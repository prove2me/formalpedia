-- Prove2me | solution 1 for ModularCurve.SW_local_old_smul_top_eq_top_of_not_hasLowerLevelTorsion_aux2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/34707ff1-11fe-5e39-b73e-fe48d95ccdfa

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SW_local_old_smul_top_eq_top_of_not_hasLowerLevelTorsion_aux2

set_option autoImplicit false

open ModularCurve

namespace SWLocalOldAux2

theorem exists_isPrimitiveRoot_residueField (p : ℕ) [Fact p.Prime] {q' : ℕ} (hq' : q'.Prime)
    (hq'p : q' ≠ p) (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField ↥A) q'] :
    ∃ ζ : (IsLocalRing.ResidueField ↥A)ˣ, IsPrimitiveRoot ζ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p

  have hmem : ζ₀ ∈ A := by
    rcases A.mem_or_inv_mem ζ₀ with h | h
    · exact h
    · have h1 : ζ₀ ^ (p - 1) * ζ₀ = 1 := by
        rw [pow_sub_one_mul (NeZero.ne p), hζ₀.pow_eq_one]
      have h2 : ζ₀⁻¹ ^ (p - 1) = ζ₀ := by
        rw [inv_pow]
        exact inv_eq_of_mul_eq_one_right h1
      rw [← h2]
      exact pow_mem h _
  set ζ₁ : ↥A := ⟨ζ₀, hmem⟩ with hζ₁_def
  have hζ₁ : IsPrimitiveRoot ζ₁ p := by
    have hinj : Function.Injective (A.subtype) := Subtype.val_injective
    exact (IsPrimitiveRoot.map_iff_of_injective (f := A.subtype) hinj).1 hζ₀
  set ζbar : IsLocalRing.ResidueField ↥A := IsLocalRing.residue ↥A ζ₁ with hζbar_def
  have hpow : ζbar ^ p = 1 := by
    rw [hζbar_def, ← map_pow, hζ₁.pow_eq_one, map_one]
  have hne : ζbar ≠ 1 := by
    intro h1
    have hsum : ∑ i ∈ Finset.range p, ζ₁ ^ i = 0 :=
      hζ₁.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
    have h' := congrArg (IsLocalRing.residue ↥A) hsum
    rw [map_sum, map_zero] at h'
    simp only [map_pow, ← hζbar_def, h1, one_pow, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one] at h'
    have hdvd : q' ∣ p := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField ↥A) q' p).1 h'
    exact hq'p ((Nat.prime_dvd_prime_iff_eq hq' Fact.out).1 hdvd)
  have hprim : IsPrimitiveRoot ζbar p := by
    have ho : orderOf ζbar = p := orderOf_eq_prime hpow hne
    rw [← ho]
    exact IsPrimitiveRoot.orderOf ζbar
  exact ⟨(hprim.isUnit (NeZero.ne p)).unit, hprim.isUnit_unit (NeZero.ne p)⟩

theorem exists_injective_zmod_hom {R : Type*} [CommRing R] [IsDomain R] {p : ℕ} [NeZero p] {ζ : Rˣ}
    (hζ : IsPrimitiveRoot ζ p) :
    ∃ Z : ZMod p →+ Additive Rˣ, Function.Injective Z := by
  refine ⟨(MonoidHom.toAdditive (Subgroup.zpowers ζ).subtype).comp hζ.zmodEquivZPowers.toAddMonoidHom, ?_⟩
  have h1 : Function.Injective (MonoidHom.toAdditive (Subgroup.zpowers ζ).subtype) := by
    rw [MonoidHom.coe_toAdditive]
    exact Additive.ofMul.injective.comp
      ((Subgroup.zpowers ζ).subtype_injective.comp Additive.toMul.injective)
  exact h1.comp hζ.zmodEquivZPowers.injective

theorem exists_character (p : ℕ) [Fact p.Prime]
    {V : Type*} [AddCommGroup V] {Xo : Type*} [AddCommGroup Xo] [Module HeckeAlg Xo]
    (𝔪 : Ideal HeckeAlg) (hp : (p : HeckeAlg) ∈ 𝔪) (good : Nat.Primes → Prop)
    (B : Nat.Primes → V →+ V) (e : V →+ Xo)
    (he : ∀ ℓ : Nat.Primes, good ℓ → ∀ v : V, heckeGen ℓ • e v = e (B ℓ v))
    (v₀ : V) (hv₀ : e v₀ ∉ 𝔪 • (⊤ : Submodule HeckeAlg Xo))
    {G : Type*} [AddCommGroup G] (Z : ZMod p →+ G) (hZ : Function.Injective Z) :
    ∃ φ : V →+ G, φ v₀ ≠ 0 ∧ p • φ = 0 ∧
      ∀ ℓ : Nat.Primes, good ℓ → ∀ b : ℤ, heckeGen ℓ - MvPolynomial.C b ∈ 𝔪 →
        ∀ x : V, φ (B ℓ x) = b • φ x := by
  classical
  set W : Submodule HeckeAlg Xo := 𝔪 • ⊤

  have hkill : ∀ m : Xo ⧸ W, p • m = 0 := by
    intro m
    obtain ⟨x, rfl⟩ := W.mkQ_surjective m
    rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← Nat.cast_smul_eq_nsmul HeckeAlg]
    exact Submodule.smul_mem_smul hp Submodule.mem_top

  haveI modp : Module (ZMod p) (Xo ⧸ W) := AddCommGroup.zmodModule hkill

  set g : V →+ Xo ⧸ W := W.mkQ.toAddMonoidHom.comp e
  have hg_apply : ∀ v, g v = W.mkQ (e v) := fun v => rfl
  have hm₀ : g v₀ ≠ 0 := by
    rw [hg_apply, Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hv₀

  have hgT : ∀ ℓ : Nat.Primes, good ℓ → ∀ b : ℤ, heckeGen ℓ - MvPolynomial.C b ∈ 𝔪 →
      ∀ x : V, g (B ℓ x) = b • g x := by
    intro ℓ hℓ b hb x
    rw [hg_apply, hg_apply, ← he ℓ hℓ x, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_smul, ← sub_eq_zero, ← Int.cast_smul_eq_zsmul HeckeAlg b,
      ← sub_smul, ← eq_intCast (MvPolynomial.C : ℤ →+* HeckeAlg) b, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hb Submodule.mem_top

  haveI hfree : Module.Free (ZMod p) (Xo ⧸ W) := Module.Free.of_divisionRing (ZMod p) (Xo ⧸ W)
  haveI hproj : Module.Projective (ZMod p) (Xo ⧸ W) := @Module.Projective.of_free (ZMod p) _ (Xo ⧸ W) _ modp hfree
  obtain ⟨lam, hlam⟩ : ∃ lam : (Xo ⧸ W) →ₗ[ZMod p] ZMod p, lam (g v₀) ≠ 0 :=
    @Module.Projective.exists_dual_ne_zero (Xo ⧸ W) _ (ZMod p) _ modp hproj _ hm₀
  refine ⟨Z.comp (lam.toAddMonoidHom.comp g), ?_, ?_, ?_⟩
  ·
    intro h0
    apply hlam
    apply hZ
    rw [map_zero]
    exact h0
  ·
    ext v
    rw [AddMonoidHom.nsmul_apply, AddMonoidHom.zero_apply]
    show p • Z (lam (g v)) = 0
    rw [← map_nsmul, ← map_nsmul, hkill, map_zero, map_zero]
  · intro ℓ hℓ b hb x
    show Z (lam (g (B ℓ x))) = b • Z (lam (g x))
    rw [hgT ℓ hℓ b hb x, map_zsmul, map_zsmul]

theorem hasLowerLevelTorsion_of_character (p : ℕ) [Fact p.Prime]
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J] (𝒯 : Submodule HeckeAlg J)
    {V G : Type*} [AddCommGroup V] [AddCommGroup G] (good : Nat.Primes → Prop)
    (ε : ↥𝒯 ≃+ (V →+ G)) (B : Nat.Primes → V →+ V)
    (hε : ∀ ℓ : Nat.Primes, good ℓ → ∀ (y : ↥𝒯) (x : V), ε (heckeGen ℓ • y) x = ε y (B ℓ x))
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪)
    (S : Finset Nat.Primes) (hS : ∀ ℓ : Nat.Primes, ℓ ∉ S → good ℓ)
    (φ : V →+ G) (v₀ : V) (hφ0 : φ v₀ ≠ 0) (hφp : p • φ = 0)
    (hφT : ∀ ℓ : Nat.Primes, good ℓ → ∀ b : ℤ, heckeGen ℓ - MvPolynomial.C b ∈ 𝔪 →
      ∀ x : V, φ (B ℓ x) = b • φ x) :
    HasLowerLevelTorsion S 𝔪 J := by
  classical
  set z : ↥𝒯 := ε.symm φ
  have hεz : ε z = φ := ε.apply_symm_apply φ
  refine ⟨(z : J), ?_, ?_, ?_⟩
  ·
    intro h0
    have hz0 : z = 0 := Subtype.ext h0
    apply hφ0
    rw [← hεz, hz0, map_zero, AddMonoidHom.zero_apply]
  ·
    intro n hn
    have hpn : p ∣ n := by
      by_contra hnd
      have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd
      obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
      apply hmax.ne_top
      rw [Ideal.eq_top_iff_one]
      have h1 : (1 : HeckeAlg) = (a : HeckeAlg) * (p : HeckeAlg) + (b : HeckeAlg) * (n : HeckeAlg) := by
        have := congrArg (Int.cast : ℤ → HeckeAlg) hab
        push_cast at this
        exact this.symm
      rw [h1]
      exact 𝔪.add_mem (𝔪.mul_mem_left _ hp) (𝔪.mul_mem_left _ hn)
    obtain ⟨c, rfl⟩ := hpn
    have hpz : p • z = 0 := by
      apply ε.injective
      rw [map_nsmul, hεz, hφp, map_zero]
    rw [Nat.cast_smul_eq_nsmul, ← AddSubmonoidClass.coe_nsmul, mul_nsmul, hpz, nsmul_zero,
      Submodule.coe_zero]
  · intro ℓ hℓ b hb
    have hℓ' : good ℓ := hS ℓ hℓ
    have hC : ∀ w : ↥𝒯, (MvPolynomial.C b : HeckeAlg) • w = b • w := fun w => by
      rw [show (MvPolynomial.C b : HeckeAlg) = (b : HeckeAlg) from eq_intCast _ b]
      exact Int.cast_smul_eq_zsmul HeckeAlg b w
    have hTz : heckeGen ℓ • z = (MvPolynomial.C b : HeckeAlg) • z := by
      apply ε.injective
      ext x
      rw [hε ℓ hℓ' z x, hεz, hφT ℓ hℓ' b hb x, hC, map_zsmul, hεz, AddMonoidHom.zsmul_apply]
    rw [← Submodule.coe_smul, sub_smul (heckeGen ℓ) (MvPolynomial.C b : HeckeAlg) z, hTz, sub_self,
      Submodule.coe_zero]

theorem coe_heckeCharacterAction_transpose {ι : Type*} [Fintype ι] (A : Matrix ι ι ℤ) {n : ℤ}
    (h : HeckeRowSums A.transpose n) (x : ↥(characterLattice ι)) :
    ((heckeCharacterAction A.transpose h x : ↥(characterLattice ι)) : ι → ℤ) = A.mulVec (x : ι → ℤ) := by
  rw [heckeCharacterAction_coe]
  funext j
  rw [heckeDivisorAction_apply]
  simp only [Matrix.transpose_apply, Matrix.mulVec, dotProduct]

theorem hasLowerLevelTorsion_of_smul_top_ne_top (p : ℕ) [Fact p.Prime] {ι : Type*} [Fintype ι]
    (A : Nat.Primes → Matrix ι ι ℤ) (ncol : Nat.Primes → ℤ)
    (hcol : ∀ ℓ : Nat.Primes, HeckeRowSums (A ℓ).transpose (ncol ℓ))
    (good : Nat.Primes → Prop) (S : Finset Nat.Primes) (hS : ∀ ℓ : Nat.Primes, ℓ ∉ S → good ℓ)
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪)
    {Xo : Type*} [AddCommGroup Xo] [Module HeckeAlg Xo]
    (eX : Xo ≃+ (↥(characterLattice ι) × ↥(characterLattice ι)))
    (hT : ∀ ℓ : Nat.Primes, good ℓ → ∀ x : Xo,
        ((eX (heckeGen ℓ • x)).1 : ι → ℤ) = (A ℓ).mulVec ((eX x).1 : ι → ℤ) ∧
        ((eX (heckeGen ℓ • x)).2 : ι → ℤ) = (A ℓ).mulVec ((eX x).2 : ι → ℤ))
    (hne : 𝔪 • (⊤ : Submodule HeckeAlg Xo) ≠ ⊤)
    {J : Type*} [AddCommGroup J] [Module HeckeAlg J] (𝒯 : Submodule HeckeAlg J)
    {R : Type*} [CommRing R] [IsDomain R] {ζ : Rˣ} (hζ : IsPrimitiveRoot ζ p)
    (ε : ↥𝒯 ≃+ (↥(characterLattice ι) →+ Additive Rˣ))
    (hε : ∀ ℓ : Nat.Primes, good ℓ → ∀ (y : ↥𝒯) (x : ↥(characterLattice ι)),
      ε (heckeGen ℓ • y) x = ε y (heckeCharacterAction (A ℓ).transpose (hcol ℓ) x)) :
    HasLowerLevelTorsion S 𝔪 J := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨B, hB⟩ : ∃ B : Nat.Primes → ↥(characterLattice ι) →+ ↥(characterLattice ι),
      ∀ ℓ x, B ℓ x = heckeCharacterAction (A ℓ).transpose (hcol ℓ) x :=
    ⟨fun ℓ => (heckeCharacterAction (A ℓ).transpose (hcol ℓ)).toAddMonoidHom, fun _ _ => rfl⟩
  have hBcoe : ∀ (ℓ : Nat.Primes) (x : ↥(characterLattice ι)),
      ((B ℓ x : ↥(characterLattice ι)) : ι → ℤ) = (A ℓ).mulVec (x : ι → ℤ) := fun ℓ x => by
    rw [hB]
    exact coe_heckeCharacterAction_transpose (A ℓ) (hcol ℓ) x
  have hε' : ∀ ℓ : Nat.Primes, good ℓ → ∀ (y : ↥𝒯) (x : ↥(characterLattice ι)),
      ε (heckeGen ℓ • y) x = ε y (B ℓ x) :=
    fun ℓ hℓ y x => by rw [hB]; exact hε ℓ hℓ y x

  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Xo, x₀ ∉ 𝔪 • (⊤ : Submodule HeckeAlg Xo) := by
    by_contra h
    push Not at h
    exact hne (Submodule.eq_top_iff'.2 h)

  obtain ⟨e₁, he₁⟩ : ∃ e₁ : ↥(characterLattice ι) →+ Xo, ∀ v, e₁ v = eX.symm (v, 0) :=
    ⟨eX.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _), fun _ => rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : ↥(characterLattice ι) →+ Xo, ∀ v, e₂ v = eX.symm (0, v) :=
    ⟨eX.symm.toAddMonoidHom.comp (AddMonoidHom.inr _ _), fun _ => rfl⟩
  have he₁T : ∀ ℓ : Nat.Primes, good ℓ → ∀ v, heckeGen ℓ • e₁ v = e₁ (B ℓ v) := by
    intro ℓ hℓ v
    obtain ⟨h1, h2⟩ := hT ℓ hℓ (e₁ v)
    rw [he₁, AddEquiv.apply_symm_apply] at h1 h2
    rw [ZeroMemClass.coe_zero, Matrix.mulVec_zero] at h2
    rw [he₁, he₁]
    apply eX.injective
    rw [AddEquiv.apply_symm_apply]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [h1, hBcoe]
    · rw [h2, ZeroMemClass.coe_zero]
  have he₂T : ∀ ℓ : Nat.Primes, good ℓ → ∀ v, heckeGen ℓ • e₂ v = e₂ (B ℓ v) := by
    intro ℓ hℓ v
    obtain ⟨h1, h2⟩ := hT ℓ hℓ (e₂ v)
    rw [he₂, AddEquiv.apply_symm_apply] at h1 h2
    rw [ZeroMemClass.coe_zero, Matrix.mulVec_zero] at h1
    rw [he₂, he₂]
    apply eX.injective
    rw [AddEquiv.apply_symm_apply]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [h1, ZeroMemClass.coe_zero]
    · rw [h2, hBcoe]

  have hsplit : x₀ = e₁ (eX x₀).1 + e₂ (eX x₀).2 := by
    rw [he₁, he₂, ← map_add, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta, AddEquiv.symm_apply_apply]
  have hcoord : (∃ v₀, e₁ v₀ ∉ 𝔪 • (⊤ : Submodule HeckeAlg Xo)) ∨
      (∃ v₀, e₂ v₀ ∉ 𝔪 • (⊤ : Submodule HeckeAlg Xo)) := by
    by_contra h
    push Not at h
    obtain ⟨h₁, h₂⟩ := h
    apply hx₀
    rw [hsplit]
    exact Submodule.add_mem _ (h₁ _) (h₂ _)

  obtain ⟨Z, hZ⟩ := exists_injective_zmod_hom hζ
  rcases hcoord with ⟨v₀, hv₀⟩ | ⟨v₀, hv₀⟩
  · obtain ⟨φ, hφ0, hφp, hφT⟩ := exists_character p 𝔪 hp good B e₁ he₁T v₀ hv₀ Z hZ
    exact hasLowerLevelTorsion_of_character p 𝒯 good ε B hε' 𝔪 hmax hp S hS φ v₀ hφ0 hφp hφT
  · obtain ⟨φ, hφ0, hφp, hφT⟩ := exists_character p 𝔪 hp good B e₂ he₂T v₀ hv₀ Z hZ
    exact hasLowerLevelTorsion_of_character p 𝒯 good ε B hε' 𝔪 hmax hp S hS φ v₀ hφ0 hφp hφT

theorem exists_finset_primes_dvd (n : ℕ) (hn : n ≠ 0) :
    ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ n) ∧ ∀ ℓ : Nat.Primes, ℓ ∉ S → ¬ ((ℓ : ℕ) ∣ n) := by
  classical
  refine ⟨Finset.subtype (fun m : ℕ => m.Prime) n.primeFactors, ?_, ?_⟩
  · intro ℓ hℓ
    have hℓ' : (ℓ : ℕ) ∈ n.primeFactors :=
      (Finset.mem_subtype (p := fun m : ℕ => m.Prime) (s := n.primeFactors) (a := ℓ)).1 hℓ
    exact Nat.dvd_of_mem_primeFactors hℓ'
  · intro ℓ hℓ hdvd
    have hℓ' : (ℓ : ℕ) ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨ℓ.2, hdvd, hn⟩
    exact hℓ ((Finset.mem_subtype (p := fun m : ℕ => m.Prime) (s := n.primeFactors) (a := ℓ)).2 hℓ')

end SWLocalOldAux2

open SWLocalOldAux2 in
theorem solution
    (p : ℕ) [Fact p.Prime] {N q q' : ℕ}
    (hq : q.Prime) (hq' : q'.Prime) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q) (hq'p : q' ≠ p)
    [NeZero (N * q')] [NeZero N] [NeZero q] [Fact q.Prime] [Fact q'.Prime]
    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hp : (p : HeckeAlg) ∈ 𝔪)
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    [DecidableEq (IsLocalRing.ResidueField ↥A₁)] [CharP (IsLocalRing.ResidueField ↥A₁) q']
    [Fintype ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [Fintype ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' (N * q) (IsLocalRing.ResidueField ↥A₁))]
    [DecidableEq ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))]
    (X₁ : SSLevelDatum q' (IsLocalRing.ResidueField ↥A₁) N q) (hX₁ : X₁.HeckeLaws)
    {Xo₁ : Type} [AddCommGroup Xo₁] [Module HeckeAlg Xo₁] [Module.Finite ℤ Xo₁]
    (eX₁ : Xo₁ ≃+ (↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))) × ↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)))))
    (hT₁ : ∀ ℓ : Nat.Primes, ¬ ((ℓ : ℕ) ∣ N * q * q') → ∀ x : Xo₁,
        ((eX₁ (heckeGen ℓ • x)).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) = (X₁.vertexHecke ℓ).mulVec ((eX₁ x).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) ∧
        ((eX₁ (heckeGen ℓ • x)).2 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) = (X₁.vertexHecke ℓ).mulVec ((eX₁ x).2 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ))
    (hU₁ : ∀ x : Xo₁,
        ((eX₁ (heckeGen ⟨q, hq⟩ • x)).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) =
            (X₁.vertexHecke ⟨q, hq⟩).mulVec ((eX₁ x).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) - ((eX₁ x).2 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) ∧
        ((eX₁ (heckeGen ⟨q, hq⟩ • x)).2 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ) = ((q : ℕ) : ℤ) • ((eX₁ x).1 : ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)) → ℤ))
    (n₂ : Nat.Primes → ℤ) (hcol₂ : ∀ ℓ : Nat.Primes, HeckeRowSums (X₁.vertexHecke ℓ).transpose (n₂ ℓ))
    (ε₂ : letI := heckeModuleBar (N * q')
      ↥(toricMonodromyPart (J := JZero (N * q')) q' (A₁.inertiaSubgroupIn ℚ)) ≃+
        (↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁))) →+ Additive (IsLocalRing.ResidueField ↥A₁)ˣ))
    (hε₂ : letI := heckeModuleBar (N * q')
      ∀ (ℓ : Nat.Primes), ¬ ((ℓ : ℕ) ∣ N * q * q') →
        ∀ (y : ↥(toricMonodromyPart (J := JZero (N * q')) q' (A₁.inertiaSubgroupIn ℚ)))
        (x : ↥(characterLattice ↥(ssPlaces q' N (IsLocalRing.ResidueField ↥A₁)))),
        ε₂ (heckeGen ℓ • y) x = ε₂ y (heckeCharacterAction (X₁.vertexHecke ℓ).transpose (hcol₂ ℓ) x))
    (hreg : letI := heckeModuleBar (N * q')
      ¬ ∃ S : Finset Nat.Primes, (∀ ℓ ∈ S, (ℓ : ℕ) ∣ N * q * q') ∧
        HasLowerLevelTorsion S 𝔪 (JZero (N * q'))) :
    𝔪 • (⊤ : Submodule HeckeAlg Xo₁) = ⊤ := by
  letI hJ : Module HeckeAlg (JZero (N * q')) := heckeModuleBar (N * q')
  by_contra hne
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_residueField p hq' hq'p A₁
  have hn0 : N * q * q' ≠ 0 := mul_ne_zero (mul_ne_zero (NeZero.ne N) (NeZero.ne q)) hq'.ne_zero
  obtain ⟨S, hSdvd, hSgood⟩ := exists_finset_primes_dvd (N * q * q') hn0
  exact hreg ⟨S, hSdvd, hasLowerLevelTorsion_of_smul_top_ne_top p X₁.vertexHecke n₂ hcol₂
    (fun ℓ : Nat.Primes => ¬ ((ℓ : ℕ) ∣ N * q * q')) S hSgood 𝔪 hmax hp eX₁ hT₁ hne _ hζ ε₂ hε₂⟩

end S_ModularCurve_SW_local_old_smul_top_eq_top_of_not_hasLowerLevelTorsion_aux2
end P2MW
export P2MW.S_ModularCurve_SW_local_old_smul_top_eq_top_of_not_hasLowerLevelTorsion_aux2 (solution)
