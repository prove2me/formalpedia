-- Prove2me | solution 1 for ModularCurve.finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7a5e15d5-bf4b-5176-8899-6321bc2a9107

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Theorems.Thm_RibetLevelLowering_finrank_span_torsion_eq_finrank_quotient_of_characterDuality
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range
set_option autoImplicit false
set_option Elab.async false
open ModularCurve

namespace ToricTorsionBound

private def muP (k : Type) [Field k] (p : ℕ) : AddSubgroup (Additive kˣ) where
  carrier := {a | p • a = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [nsmul_add, ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [ha]

private theorem mem_muP {k : Type} [Field k] {p : ℕ} (a : Additive kˣ) : a ∈ muP k p ↔ p • a = 0 := Iff.rfl

private def muPEquivRootsOfUnity (k : Type) [Field k] (p : ℕ) : muP k p ≃ rootsOfUnity p k where
  toFun a := ⟨a.1.toMul, (mem_rootsOfUnity p _).2 (by rw [← toMul_nsmul, (mem_muP _).1 a.2, toMul_zero])⟩
  invFun ζ := ⟨Additive.ofMul ζ.1, (mem_muP _).2 (by rw [← ofMul_pow, (mem_rootsOfUnity p _).1 ζ.2, ofMul_one])⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem natCard_muP (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] (hpk : (p : k) ≠ 0) :
    Nat.card (muP k p) = p := by
  haveI : NeZero (p : k) := ⟨hpk⟩
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Nat.card_congr (muPEquivRootsOfUnity k p)]
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity k p

private scoped instance finite_muP (k : Type) [Field k] (p : ℕ) [Fact p.Prime] : Finite (muP k p) :=
  Finite.of_equiv _ (muPEquivRootsOfUnity k p).symm

private theorem eq_zero_of_prime_smul_eq_zero {k : Type} [Field k] {p : ℕ} [Fact p.Prime] (hpk : (p : k) = 0)
    (a : Additive kˣ) (ha : p • a = 0) : a = 0 := by
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (R := k) (Fact.out : p.Prime)).2 hpk
  have hu : a.toMul ^ p = 1 := by rw [← toMul_nsmul, ha, toMul_zero]
  have hv : ((a.toMul : kˣ) : k) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hsub : (((a.toMul : kˣ) : k) - 1) ^ p = 0 := by rw [sub_pow_char ((a.toMul : kˣ) : k) 1, hv, one_pow, sub_self]
  have h1 : ((a.toMul : kˣ) : k) = 1 := sub_eq_zero.1 ((pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).1 hsub)
  exact Additive.toMul.injective (by rw [toMul_zero]; exact Units.val_eq_one.1 h1)

private theorem finite_addMonoidHom (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (N : Type) [AddCommGroup N]
    [Finite N] : Finite (X →+ N) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := X)
  refine Finite.of_injective (fun (g : X →+ N) (i : Fin n) => g (s i)) ?_
  intro g₁ g₂ h
  have h' : g₁.toIntLinearMap = g₂.toIntLinearMap := by
    refine LinearMap.ext_on hs ?_
    rintro _ ⟨i, rfl⟩
    exact congrFun h i
  exact AddMonoidHom.ext fun x => LinearMap.congr_fun h' x

private theorem moduleFinite_characterLattice (ι : Type) [Fintype ι] : Module.Finite ℤ ↥(characterLattice ι) := by
  haveI : IsNoetherian ℤ (ι → ℤ) := isNoetherian_of_isNoetherianRing_of_finite ℤ (ι → ℤ)
  infer_instance

@[reducible] private noncomputable def homModule (X : Type) [AddCommGroup X] [Module HeckeAlg X] (N : Type) [AddCommGroup N] :
    Module HeckeAlg (X →+ N) where
  smul t g := g.comp (DistribSMul.toAddMonoidHom X t)
  one_smul g := AddMonoidHom.ext fun x => show g ((1 : HeckeAlg) • x) = g x by rw [one_smul]
  mul_smul t s g := AddMonoidHom.ext fun x =>
    show g ((t * s) • x) = g (s • t • x) by rw [mul_comm, mul_smul]
  smul_zero t := AddMonoidHom.ext fun x => show (0 : N) = 0 from rfl
  smul_add t g h := AddMonoidHom.ext fun x => show g (t • x) + h (t • x) = g (t • x) + h (t • x) from rfl
  add_smul t s g := AddMonoidHom.ext fun x =>
    show g ((t + s) • x) = g (t • x) + g (s • x) by rw [add_smul, map_add]
  zero_smul g := AddMonoidHom.ext fun x => show g ((0 : HeckeAlg) • x) = 0 by rw [zero_smul, map_zero]

attribute [local instance] homModule

private theorem homModule_smul_apply {X : Type} [AddCommGroup X] [Module HeckeAlg X] {N : Type} [AddCommGroup N]
    (t : HeckeAlg) (g : X →+ N) (x : X) :
    (t • g) x = g (t • x) := rfl

private theorem smul_comm_of_heckeGen {W : Type} [AddCommGroup W] [Module HeckeAlg W] {V : Type} [AddCommGroup V]
    [Module HeckeAlg V] (ψ : W →+ V) (hψ : ∀ (ℓ : Nat.Primes) (w : W), ψ (heckeGen ℓ • w) = heckeGen ℓ • ψ w)
    (t : HeckeAlg) (w : W) : ψ (t • w) = t • ψ w := by
  induction t using MvPolynomial.induction_on generalizing w with
  | C a =>
    rw [eq_intCast (MvPolynomial.C : ℤ →+* HeckeAlg) a, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]
  | add s t hs ht =>
    rw [add_smul, map_add, hs, ht, add_smul]
  | mul_X s ℓ hs =>
    have h : ψ (MvPolynomial.X ℓ • w) = MvPolynomial.X ℓ • ψ w := hψ ℓ w
    rw [mul_smul, hs, h, mul_smul]

private theorem finrank_heckeTorsion_hom_eq (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] {p : ℕ} (hp : p.Prime)
    (hpm : (p : HeckeAlg) ∈ 𝔪) (X : Type) [AddCommGroup X] [Module HeckeAlg X] [Module.Finite ℤ X]
    (μ : Type) [AddCommGroup μ] (hμ : Nat.card μ = p) :
    Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (X →+ μ) 𝔪) =
      Module.finrank (HeckeAlg ⧸ 𝔪) (X ⧸ (𝔪 • (⊤ : Submodule HeckeAlg X))) := by
  have htor : ∀ g : X →+ μ, g ∈ Submodule.torsionBy HeckeAlg (X →+ μ) (p : HeckeAlg) := by
    intro g
    rw [Submodule.mem_torsionBy_iff]
    ext x
    show g ((p : HeckeAlg) • x) = 0
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← hμ]
    exact card_nsmul_eq_zero'
  have hmem : ∀ g : X →+ μ,
      g ∈ (⊤ : Submodule HeckeAlg (X →+ μ)) ⊓ Submodule.torsionBy HeckeAlg (X →+ μ) (p : HeckeAlg) :=
    fun g => ⟨Submodule.mem_top, htor g⟩
  let ε : ↥((⊤ : Submodule HeckeAlg (X →+ μ)) ⊓ Submodule.torsionBy HeckeAlg (X →+ μ) (p : HeckeAlg)) ≃+
      (X →+ μ) :=
    AddEquiv.ofBijective
      ((⊤ : Submodule HeckeAlg (X →+ μ)) ⊓ Submodule.torsionBy HeckeAlg (X →+ μ) (p : HeckeAlg)).subtype
      ⟨Subtype.val_injective, fun g => ⟨⟨g, hmem g⟩, rfl⟩⟩
  have hε : ∀ (ℓ : Nat.Primes)
      (y : ↥((⊤ : Submodule HeckeAlg (X →+ μ)) ⊓ Submodule.torsionBy HeckeAlg (X →+ μ) (p : HeckeAlg)))
      (l : X), ε (heckeGen ℓ • y) l = ε y (heckeGen ℓ • l) := fun _ _ _ => rfl
  have h := RibetLevelLowering.finrank_span_torsion_eq_finrank_quotient_of_characterDuality
    (J := X →+ μ) ⊤ 𝔪 hp hpm (L := X) (μ := μ) hμ ε hε
  rw [← h, Submodule.top_coe, Set.preimage_univ, Submodule.span_univ, finrank_top]

section Main

variable {J : Type} [AddCommGroup J] [Module HeckeAlg J] (𝒯 : Submodule HeckeAlg J)
  {k : Type} [Field k] (p : ℕ)
  {ι₁ : Type} [Fintype ι₁] (𝔪 : Ideal HeckeAlg)
  (T₁ : Nat.Primes → Matrix ι₁ ι₁ ℤ) (n₁ : Nat.Primes → ℤ)
  (hcol₁ : ∀ ℓ : Nat.Primes, HeckeRowSums (T₁ ℓ).transpose (n₁ ℓ))
  (ε₁ : ↥𝒯 ≃+ (↥(characterLattice ι₁) →+ Additive kˣ))

private def Mu (k : Type) [Field k] (p : ℕ) : Type := ↥(muP k p)

private scoped instance Mu.instAddCommGroup (k : Type) [Field k] (p : ℕ) : AddCommGroup (Mu k p) :=
  inferInstanceAs (AddCommGroup ↥(muP k p))

p2m_reactivate "P2MW.S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range.ToricTorsionBound.Mu"
private scoped instance Mu.instFinite (k : Type) [Field k] (p : ℕ) [Fact p.Prime] : Finite (Mu k p) :=
  inferInstanceAs (Finite ↥(muP k p))

p2m_reactivate "P2MW.S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range.ToricTorsionBound.Mu"
private theorem natCard_Mu (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] (hpk : (p : k) ≠ 0) :
    Nat.card (Mu k p) = p :=
  natCard_muP k p hpk

private def Mu.val {k : Type} [Field k] {p : ℕ} (m : Mu k p) : Additive kˣ := Subtype.val m

private theorem Mu.val_injective {k : Type} [Field k] {p : ℕ} : Function.Injective (Mu.val (k := k) (p := p)) :=
  Subtype.val_injective

private theorem Mu.val_add {k : Type} [Field k] {p : ℕ} (a b : Mu k p) : (a + b).val = a.val + b.val := rfl

private theorem Mu.val_zero {k : Type} [Field k] {p : ℕ} : (0 : Mu k p).val = 0 := rfl

private def Mu.mk {k : Type} [Field k] {p : ℕ} (a : Additive kˣ) (ha : p • a = 0) : Mu k p :=
  Subtype.mk a ((mem_muP a).2 ha)

private theorem Mu.val_mk {k : Type} [Field k] {p : ℕ} (a : Additive kˣ) (ha : p • a = 0) : (Mu.mk a ha).val = a :=
  rfl

private def inTor : Submodule (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion J 𝔪) where
  carrier := (Subtype.val : ↥(heckeTorsion J 𝔪) → J) ⁻¹' (𝒯 : Set J)
  add_mem' {a b} ha hb := 𝒯.add_mem ha hb
  zero_mem' := 𝒯.zero_mem
  smul_mem' c a ha := by
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact 𝒯.smul_mem t ha

private theorem span_eq_inTor :
    Submodule.span (HeckeAlg ⧸ 𝔪) ((Subtype.val : ↥(heckeTorsion J 𝔪) → J) ⁻¹' (𝒯 : Set J)) =
      inTor 𝒯 𝔪 :=
  Submodule.span_eq (inTor 𝒯 𝔪)

private def toT (s : ↥(inTor 𝒯 𝔪)) : ↥𝒯 := ⟨((s : ↥(heckeTorsion J 𝔪)) : J), s.2⟩

private theorem toT_add (s s' : ↥(inTor 𝒯 𝔪)) : toT 𝒯 𝔪 (s + s') = toT 𝒯 𝔪 s + toT 𝒯 𝔪 s' := rfl

private theorem smul_toT_eq_zero (s : ↥(inTor 𝒯 𝔪)) {t : HeckeAlg} (ht : t ∈ 𝔪) : t • toT 𝒯 𝔪 s = 0 := by
  apply Subtype.ext
  have h := (Submodule.mem_torsionBySet_iff (𝔪 : Set HeckeAlg) ((s : ↥(heckeTorsion J 𝔪)) : J)).1
    (s : ↥(heckeTorsion J 𝔪)).2 ⟨t, ht⟩
  first | exact h | simpa [toT] using h

private theorem toT_injective : Function.Injective (toT 𝒯 𝔪) := by
  intro s s' h
  have h' := congrArg (fun y : ↥𝒯 => (y : J)) h
  exact Subtype.ext (Subtype.ext h')

variable (hpm : (p : HeckeAlg) ∈ 𝔪)
include hpm

private theorem prime_smul_eps (s : ↥(inTor 𝒯 𝔪)) (x : ↥(characterLattice ι₁)) : p • ε₁ (toT 𝒯 𝔪 s) x = 0 := by
  have h1 : p • toT 𝒯 𝔪 s = 0 := by
    rw [← Nat.cast_smul_eq_nsmul HeckeAlg p (toT 𝒯 𝔪 s)]
    exact smul_toT_eq_zero 𝒯 𝔪 s hpm
  have h2 : ε₁ (p • toT 𝒯 𝔪 s) = 0 := by rw [h1, map_zero]
  rw [map_nsmul] at h2
  have h3 := congrArg (fun g : ↥(characterLattice ι₁) →+ Additive kˣ => g x) h2
  simpa using h3

private noncomputable def resMu (s : ↥(inTor 𝒯 𝔪)) : ↥(characterLattice ι₁) →+ Mu k p where
  toFun x := Mu.mk (ε₁ (toT 𝒯 𝔪 s) x) (prime_smul_eps 𝒯 p 𝔪 ε₁ hpm s x)
  map_zero' := by
    apply Mu.val_injective
    rw [Mu.val_mk, Mu.val_zero, map_zero]
  map_add' a b := by
    apply Mu.val_injective
    rw [Mu.val_mk, Mu.val_add, Mu.val_mk, Mu.val_mk, map_add]

private theorem coe_resMu_apply (s : ↥(inTor 𝒯 𝔪)) (x : ↥(characterLattice ι₁)) :
    (resMu 𝒯 p 𝔪 ε₁ hpm s x).val = ε₁ (toT 𝒯 𝔪 s) x := rfl

private theorem resMu_injective : Function.Injective (resMu 𝒯 p 𝔪 ε₁ hpm) := by
  intro s s' h
  apply toT_injective 𝒯 𝔪
  apply ε₁.injective
  refine AddMonoidHom.ext fun x => ?_
  have h' : resMu 𝒯 p 𝔪 ε₁ hpm s x = resMu 𝒯 p 𝔪 ε₁ hpm s' x := by rw [h]
  have h'' := congrArg Mu.val h'
  exact h''

omit hpm in

private theorem eps_comp_smul
    (hε₁ : ∀ (ℓ : Nat.Primes) (y : ↥𝒯) (x : ↥(characterLattice ι₁)),
      ε₁ (heckeGen ℓ • y) x = ε₁ y (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x))
    (Q : Type) [AddCommGroup Q] [Module HeckeAlg Q] (φ : Q →+ ↥(characterLattice ι₁))
    (hφT : ∀ (ℓ : Nat.Primes) (z : Q),
      φ (heckeGen ℓ • z) = heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) (φ z))
    (t : HeckeAlg) (y : ↥𝒯) :
    (ε₁ (t • y) : ↥(characterLattice ι₁) →+ Additive kˣ).comp φ =
      t • ((ε₁ y : ↥(characterLattice ι₁) →+ Additive kˣ).comp φ) := by
  let ψ : ↥𝒯 →+ (Q →+ Additive kˣ) :=
    { toFun := fun y => (ε₁ y : ↥(characterLattice ι₁) →+ Additive kˣ).comp φ
      map_zero' := by simp
      map_add' := fun a b => by simp [AddMonoidHom.add_comp] }
  have hψ : ∀ (ℓ : Nat.Primes) (w : ↥𝒯), ψ (heckeGen ℓ • w) = heckeGen ℓ • ψ w := by
    intro ℓ w
    refine AddMonoidHom.ext fun z => ?_
    rw [homModule_smul_apply]
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.comp_apply]
    rw [hε₁, hφT]
  exact smul_comm_of_heckeGen ψ hψ t y

omit hpm in

private theorem lift_smul
    (hε₁ : ∀ (ℓ : Nat.Primes) (y : ↥𝒯) (x : ↥(characterLattice ι₁)),
      ε₁ (heckeGen ℓ • y) x = ε₁ y (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x))
    (L : Type) [AddCommGroup L] [Module HeckeAlg L] (πL : ↥(characterLattice ι₁) →+ L)
    (hπsurj : Function.Surjective πL)
    (hπT : ∀ (ℓ : Nat.Primes) (x : ↥(characterLattice ι₁)),
      πL (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x) = heckeGen ℓ • πL x)
    (K : Submodule HeckeAlg ↥𝒯)
    (hkerK : ∀ w : ↥K, πL.ker ≤ (ε₁ (w : ↥𝒯) : ↥(characterLattice ι₁) →+ Additive kˣ).ker)
    (t : HeckeAlg) (w : ↥K) :
    πL.liftOfSurjective hπsurj ⟨(ε₁ ((t • w : ↥K) : ↥𝒯) : ↥(characterLattice ι₁) →+ Additive kˣ),
        hkerK (t • w)⟩ =
      t • πL.liftOfSurjective hπsurj ⟨(ε₁ (w : ↥𝒯) : ↥(characterLattice ι₁) →+ Additive kˣ), hkerK w⟩ := by
  let ψ : ↥K →+ (L →+ Additive kˣ) :=
    { toFun := fun w =>
        πL.liftOfSurjective hπsurj ⟨(ε₁ (w : ↥𝒯) : ↥(characterLattice ι₁) →+ Additive kˣ), hkerK w⟩
      map_zero' := by
        refine AddMonoidHom.ext fun l => ?_
        obtain ⟨x, rfl⟩ := hπsurj l
        rw [AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply]
        simp
      map_add' := fun a b => by
        refine AddMonoidHom.ext fun l => ?_
        obtain ⟨x, rfl⟩ := hπsurj l
        simp only [AddMonoidHom.add_apply]
        rw [AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
          AddMonoidHom.liftOfRightInverse_comp_apply, AddMonoidHom.liftOfRightInverse_comp_apply]
        simp }
  have hψ : ∀ (ℓ : Nat.Primes) (w : ↥K), ψ (heckeGen ℓ • w) = heckeGen ℓ • ψ w := by
    intro ℓ w
    refine AddMonoidHom.ext fun l => ?_
    obtain ⟨x, rfl⟩ := hπsurj l
    rw [homModule_smul_apply, ← hπT]
    simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply,
      AddMonoidHom.liftOfRightInverse_comp_apply]
    simp only [Submodule.coe_smul]
    rw [hε₁]
  exact smul_comm_of_heckeGen ψ hψ t w

private theorem main [Fact p.Prime] [𝔪.IsMaximal] [IsAlgClosed k]
    (hε₁ : ∀ (ℓ : Nat.Primes) (y : ↥𝒯) (x : ↥(characterLattice ι₁)),
      ε₁ (heckeGen ℓ • y) x = ε₁ y (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x))
    (Q : Type) [AddCommGroup Q] [Module HeckeAlg Q] [Module.Finite ℤ Q] (φ : Q →+ ↥(characterLattice ι₁))
    (hφT : ∀ (ℓ : Nat.Primes) (z : Q),
      φ (heckeGen ℓ • z) = heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) (φ z))
    (L : Type) [AddCommGroup L] [Module HeckeAlg L] [Module.Finite ℤ L] (πL : ↥(characterLattice ι₁) →+ L)
    (hπsurj : Function.Surjective πL)
    (hπT : ∀ (ℓ : Nat.Primes) (x : ↥(characterLattice ι₁)),
      πL (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x) = heckeGen ℓ • πL x)
    (hker : ∀ x : ↥(characterLattice ι₁), πL x = 0 → x ∈ AddMonoidHom.range φ) :
    Module.finrank (HeckeAlg ⧸ 𝔪)
        ↥(Submodule.span (HeckeAlg ⧸ 𝔪) ((Subtype.val : ↥(heckeTorsion J 𝔪) → J) ⁻¹' (𝒯 : Set J))) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) +
        Module.finrank (HeckeAlg ⧸ 𝔪) (Q ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Q))) := by
  rw [span_eq_inTor]
  by_cases hpk : (p : k) = 0
  ·
    have hbot : inTor 𝒯 𝔪 = ⊥ := by
      rw [eq_bot_iff]
      intro s hs
      rw [Submodule.mem_bot]
      have h0 : toT 𝒯 𝔪 ⟨s, hs⟩ = 0 := by
        apply ε₁.injective
        rw [map_zero]
        refine AddMonoidHom.ext fun x => ?_
        rw [AddMonoidHom.zero_apply]
        exact eq_zero_of_prime_smul_eq_zero hpk _ (prime_smul_eps 𝒯 p 𝔪 ε₁ hpm ⟨s, hs⟩ x)
      have h1 := congrArg (fun y : ↥𝒯 => (y : J)) h0
      exact Subtype.ext h1
    rw [hbot, finrank_bot]
    exact Nat.zero_le _

  have hp : p.Prime := Fact.out
  have hμ : Nat.card (Mu k p) = p := natCard_Mu k p hpk
  haveI : Finite (Q →+ Mu k p) := finite_addMonoidHom Q (Mu k p)
  haveI : Finite (L →+ Mu k p) := finite_addMonoidHom L (Mu k p)
  haveI : Module.Finite ℤ ↥(characterLattice ι₁) := moduleFinite_characterLattice ι₁
  haveI : Finite (↥(characterLattice ι₁) →+ Mu k p) := finite_addMonoidHom _ _
  haveI hfinQ : Module.Finite (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (Q →+ Mu k p) 𝔪) :=
    Module.Finite.of_finite
  haveI hfinL : Module.Finite (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion (L →+ Mu k p) 𝔪) :=
    Module.Finite.of_finite
  haveI : Finite ↥(inTor 𝒯 𝔪) := Finite.of_injective _ (resMu_injective 𝒯 p 𝔪 ε₁ hpm)
  haveI hfinS : Module.Finite (HeckeAlg ⧸ 𝔪) ↥(inTor 𝒯 𝔪) := Module.Finite.of_finite

  have hQ := finrank_heckeTorsion_hom_eq 𝔪 hp hpm Q (Mu k p) hμ
  have hL := finrank_heckeTorsion_hom_eq 𝔪 hp hpm L (Mu k p) hμ

  have heq : ∀ (t : HeckeAlg) (s : ↥(inTor 𝒯 𝔪)) (z : Q),
      ε₁ (t • toT 𝒯 𝔪 s) (φ z) = ε₁ (toT 𝒯 𝔪 s) (φ (t • z)) := by
    intro t s z
    have h := congrArg (fun g : Q →+ Additive kˣ => g z)
      (eps_comp_smul 𝒯 T₁ n₁ hcol₁ ε₁ hε₁ Q φ hφT t (toT 𝒯 𝔪 s))
    simp only [AddMonoidHom.comp_apply] at h
    rw [homModule_smul_apply, AddMonoidHom.comp_apply] at h
    exact h
  have hfmem : ∀ s : ↥(inTor 𝒯 𝔪),
      (resMu 𝒯 p 𝔪 ε₁ hpm s).comp φ ∈ heckeTorsion (Q →+ Mu k p) 𝔪 := by
    intro s
    rw [mem_heckeTorsion_iff]
    intro t ht
    refine AddMonoidHom.ext fun z => Mu.val_injective ?_
    rw [homModule_smul_apply, AddMonoidHom.zero_apply, AddMonoidHom.comp_apply, coe_resMu_apply, ← heq,
      smul_toT_eq_zero 𝒯 𝔪 s ht, map_zero, AddMonoidHom.zero_apply]
    exact Mu.val_zero.symm
  let f : ↥(inTor 𝒯 𝔪) →ₗ[HeckeAlg ⧸ 𝔪] ↥(heckeTorsion (Q →+ Mu k p) 𝔪) :=
    { toFun := fun s => ⟨(resMu 𝒯 p 𝔪 ε₁ hpm s).comp φ, hfmem s⟩
      map_add' := fun s s' => by
        apply Subtype.ext
        refine AddMonoidHom.ext fun z => Mu.val_injective ?_
        change ε₁ (toT 𝒯 𝔪 (s + s')) (φ z) = (resMu 𝒯 p 𝔪 ε₁ hpm s (φ z) + resMu 𝒯 p 𝔪 ε₁ hpm s' (φ z)).val
        rw [Mu.val_add, coe_resMu_apply, coe_resMu_apply, toT_add, map_add, AddMonoidHom.add_apply]
      map_smul' := fun c s => by
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
        apply Subtype.ext
        refine AddMonoidHom.ext fun z => Mu.val_injective ?_
        exact heq t s z }
  letI sKs : SMul (HeckeAlg ⧸ 𝔪) ↥(LinearMap.ker f) :=
    (LinearMap.ker f).module.toDistribMulAction.toMulAction.toSMul

  let K : Submodule HeckeAlg ↥𝒯 :=
    { carrier := {y | (ε₁ y : ↥(characterLattice ι₁) →+ Additive kˣ).comp φ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, AddMonoidHom.add_comp, ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun t y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        rw [eps_comp_smul 𝒯 T₁ n₁ hcol₁ ε₁ hε₁ Q φ hφT t y, hy]
        rfl }
  have hkerK : ∀ w : ↥K, πL.ker ≤ (ε₁ (w : ↥𝒯) : ↥(characterLattice ι₁) →+ Additive kˣ).ker := by
    intro w x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    obtain ⟨z, rfl⟩ := hker x hx
    have hw : ((ε₁ (w : ↥𝒯) : ↥(characterLattice ι₁) →+ Additive kˣ)).comp φ = 0 := w.2
    have h := congrArg (fun g : Q →+ Additive kˣ => g z) hw
    simpa using h
  have hkf : ∀ s : ↥(LinearMap.ker f), toT 𝒯 𝔪 (s : ↥(inTor 𝒯 𝔪)) ∈ K := by
    intro s
    have hs := s.2
    rw [LinearMap.mem_ker] at hs
    change (ε₁ (toT 𝒯 𝔪 (s : ↥(inTor 𝒯 𝔪))) : ↥(characterLattice ι₁) →+ Additive kˣ).comp φ = 0
    refine AddMonoidHom.ext fun z => ?_
    have h := congrArg (fun g : ↥(heckeTorsion (Q →+ Mu k p) 𝔪) => ((g : Q →+ Mu k p) z).val) hs
    beta_reduce at h
    exact h
  let toK : ↥(LinearMap.ker f) → ↥K := fun s => ⟨toT 𝒯 𝔪 (s : ↥(inTor 𝒯 𝔪)), hkf s⟩
  have toK_add : ∀ s s' : ↥(LinearMap.ker f), toK (s + s') = toK s + toK s' := fun _ _ => rfl
  have toK_mk_smul : ∀ (t : HeckeAlg) (s : ↥(LinearMap.ker f)),
      toK ((Ideal.Quotient.mk 𝔪 t : HeckeAlg ⧸ 𝔪) • s) = t • toK s := fun _ _ => rfl
  have toK_zero : toK 0 = 0 := rfl
  let lift : ↥K → (L →+ Additive kˣ) := fun w =>
    πL.liftOfSurjective hπsurj ⟨(ε₁ (w : ↥𝒯) : ↥(characterLattice ι₁) →+ Additive kˣ), hkerK w⟩
  have lift_apply : ∀ (w : ↥K) (x : ↥(characterLattice ι₁)), lift w (πL x) = ε₁ (w : ↥𝒯) x := by
    intro w x
    simp only [lift]
    rw [AddMonoidHom.liftOfSurjective, AddMonoidHom.liftOfRightInverse_comp_apply]
  have lift_smul' : ∀ (t : HeckeAlg) (w : ↥K), lift (t • w) = t • lift w :=
    lift_smul 𝒯 T₁ n₁ hcol₁ ε₁ hε₁ L πL hπsurj hπT K hkerK
  have lift_zero : lift 0 = 0 := by
    refine AddMonoidHom.ext fun l => ?_
    obtain ⟨x, rfl⟩ := hπsurj l
    rw [lift_apply, AddMonoidHom.zero_apply]
    simp
  have hlift_tors : ∀ (s : ↥(LinearMap.ker f)) (l : L), p • lift (toK s) l = 0 := by
    intro s l
    obtain ⟨x, rfl⟩ := hπsurj l
    rw [lift_apply]
    exact prime_smul_eps 𝒯 p 𝔪 ε₁ hpm _ x
  let liftMu : ↥(LinearMap.ker f) → (L →+ Mu k p) := fun s =>
    { toFun := fun l => Mu.mk (lift (toK s) l) (hlift_tors s l)
      map_zero' := by
        apply Mu.val_injective
        rw [Mu.val_mk, Mu.val_zero, map_zero]
      map_add' := fun a b => by
        apply Mu.val_injective
        rw [Mu.val_mk, Mu.val_add, Mu.val_mk, Mu.val_mk, map_add] }
  have coe_liftMu : ∀ (s : ↥(LinearMap.ker f)) (l : L), (liftMu s l).val = lift (toK s) l := fun _ _ => rfl
  have hgmem : ∀ s : ↥(LinearMap.ker f), liftMu s ∈ heckeTorsion (L →+ Mu k p) 𝔪 := by
    intro s
    rw [mem_heckeTorsion_iff]
    intro t ht
    refine AddMonoidHom.ext fun l => Mu.val_injective ?_
    rw [homModule_smul_apply, AddMonoidHom.zero_apply, coe_liftMu, ← homModule_smul_apply t (lift (toK s)) l,
      ← lift_smul', ← toK_mk_smul]
    have h0 : ((Ideal.Quotient.mk 𝔪 t : HeckeAlg ⧸ 𝔪) • s : ↥(LinearMap.ker f)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.2 ht]
      exact zero_smul (HeckeAlg ⧸ 𝔪) s
    rw [h0, toK_zero, lift_zero, AddMonoidHom.zero_apply]
    exact Mu.val_zero.symm
  let g : ↥(LinearMap.ker f) →ₗ[HeckeAlg ⧸ 𝔪] ↥(heckeTorsion (L →+ Mu k p) 𝔪) :=
    { toFun := fun s => ⟨liftMu s, hgmem s⟩
      map_add' := fun s s' => by
        apply Subtype.ext
        refine AddMonoidHom.ext fun l => Mu.val_injective ?_
        obtain ⟨x, rfl⟩ := hπsurj l
        change lift (toK (s + s')) (πL x) = (liftMu s (πL x) + liftMu s' (πL x)).val
        rw [Mu.val_add, coe_liftMu, coe_liftMu, lift_apply, lift_apply, lift_apply, toK_add, Submodule.coe_add,
          map_add, AddMonoidHom.add_apply]
      map_smul' := fun c s => by
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
        apply Subtype.ext
        refine AddMonoidHom.ext fun l => Mu.val_injective ?_
        have e1 : lift (toK ((Ideal.Quotient.mk 𝔪 t : HeckeAlg ⧸ 𝔪) • s)) l = lift (toK s) (t • l) := by
          rw [toK_mk_smul, lift_smul', homModule_smul_apply]
        exact e1 }
  have hginj : Function.Injective g := by
    intro s s' h
    have h1 : lift (toK s) = lift (toK s') := by
      refine AddMonoidHom.ext fun l => ?_
      have h2 : ((g s : ↥(heckeTorsion (L →+ Mu k p) 𝔪)) : L →+ Mu k p) l =
          ((g s' : ↥(heckeTorsion (L →+ Mu k p) 𝔪)) : L →+ Mu k p) l := by rw [h]
      have h3 := congrArg Mu.val h2
      exact h3
    have h3 : ε₁ (toT 𝒯 𝔪 (s : ↥(inTor 𝒯 𝔪))) = ε₁ (toT 𝒯 𝔪 (s' : ↥(inTor 𝒯 𝔪))) := by
      refine AddMonoidHom.ext fun x => ?_
      have h4 := congrArg (fun e : L →+ Additive kˣ => e (πL x)) h1
      beta_reduce at h4
      rw [lift_apply, lift_apply] at h4
      exact h4
    exact Subtype.ext (toT_injective 𝒯 𝔪 (ε₁.injective h3))

  have hrn : Module.finrank (HeckeAlg ⧸ 𝔪) ↥(LinearMap.range f) +
      Module.finrank (HeckeAlg ⧸ 𝔪) ↥(LinearMap.ker f) = Module.finrank (HeckeAlg ⧸ 𝔪) ↥(inTor 𝒯 𝔪) := by
    rw [← LinearEquiv.finrank_eq f.quotKerEquivRange]
    exact Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  have h1 : Module.finrank (HeckeAlg ⧸ 𝔪) ↥(LinearMap.range f) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (Q ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Q))) := by
    rw [← hQ]
    exact Submodule.finrank_le _
  have h2 : Module.finrank (HeckeAlg ⧸ 𝔪) ↥(LinearMap.ker f) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) := by
    rw [← hL]
    exact LinearMap.finrank_le_finrank_of_injective hginj
  omega

end Main
p2m_reactivate "P2MW.S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range.ToricTorsionBound.Mu"

end ToricTorsionBound
p2m_reactivate "P2MW.S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range.ToricTorsionBound.Mu P2MW.S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range.ToricTorsionBound"

theorem solution
    (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (r : ℕ) (hpr : p ≠ r)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r)
    {ι₁ : Type} [Fintype ι₁]
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] (hpm : (p : HeckeAlg) ∈ 𝔪)
    (T₁ : Nat.Primes → Matrix ι₁ ι₁ ℤ)
    (n₁ : Nat.Primes → ℤ) (hcol₁ : ∀ ℓ : Nat.Primes, HeckeRowSums (T₁ ℓ).transpose (n₁ ℓ))
    (ε₁ : letI := heckeModuleBar M;
      ↥(toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ)) ≃+
        (↥(characterLattice ι₁) →+ Additive (IsLocalRing.ResidueField A)ˣ))
    (hε₁ : letI := heckeModuleBar M;
      ∀ (ℓ : Nat.Primes) (y : ↥(toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ)))
        (x : ↥(characterLattice ι₁)),
        ε₁ (heckeGen ℓ • y) x = ε₁ y (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x))
    (Q : Type) [AddCommGroup Q] [Module HeckeAlg Q] [Module.Finite ℤ Q]
    (φ : Q →+ ↥(characterLattice ι₁))
    (hφT : ∀ (ℓ : Nat.Primes) (z : Q), φ (heckeGen ℓ • z) = heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) (φ z))
    (L : Type) [AddCommGroup L] [Module HeckeAlg L] [Module.Finite ℤ L]
    (πL : ↥(characterLattice ι₁) →+ L) (hπsurj : Function.Surjective πL)
    (hπT : ∀ (ℓ : Nat.Primes) (x : ↥(characterLattice ι₁)),
      πL (heckeCharacterAction (T₁ ℓ).transpose (hcol₁ ℓ) x) = heckeGen ℓ • πL x)
    (hker : ∀ x : ↥(characterLattice ι₁), πL x = 0 → x ∈ AddMonoidHom.range φ) :
    letI := heckeModuleBar M
    Module.finrank (HeckeAlg ⧸ 𝔪)
        ↥(Submodule.span (HeckeAlg ⧸ 𝔪)
          ((Subtype.val : ↥(heckeTorsion (JZero M) 𝔪) → JZero M) ⁻¹'
            (toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ) : Set (JZero M)))) ≤
      Module.finrank (HeckeAlg ⧸ 𝔪) (L ⧸ (𝔪 • (⊤ : Submodule HeckeAlg L))) +
        Module.finrank (HeckeAlg ⧸ 𝔪) (Q ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Q))) := by
  have _ := hpr
  have _ := hA
  letI := heckeModuleBar M
  haveI := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  exact ToricTorsionBound.main (toricMonodromyPart (J := JZero M) r (A.inertiaSubgroupIn ℚ)) p 𝔪 T₁ n₁ hcol₁ ε₁ hpm
    hε₁ Q φ hφT L πL hπsurj hπT hker

end S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range
end P2MW
export P2MW.S_ModularCurve_finrank_span_toricMonodromyPart_le_finrank_quotient_add_of_anchor_of_ker_le_range (solution)
