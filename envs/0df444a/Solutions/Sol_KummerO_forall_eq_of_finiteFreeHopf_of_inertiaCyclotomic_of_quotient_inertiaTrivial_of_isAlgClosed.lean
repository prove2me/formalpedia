-- Prove2me | solution 1 for KummerO.forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/83933cec-bc86-5d0b-a847-07b1e712836b

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
import Theorems.Thm_KummerO_exists_units_of_block_of_isAlgClosed
import Theorems.Thm_HopfAlgebra_exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed
import Theorems.Thm_KummerO_exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_KummerO_forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy WeierstrassCurve.Affine.Point.instFinite"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq"

set_option autoImplicit false

set_option maxHeartbeats 800000

section PtsFin
variable {L : Type} [Field L] [IsAlgClosed L] [CharZero L]
variable (q : ℕ) (A : ValuationSubring (L)) (O : Type) [CommRing O] [IsDomain O] [Algebra O ↥A]
  (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B]
  (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)

include hBq in
theorem S17KummerOGen.finite_points : Finite (WithConv (B →ₐ[O] ↥A)) := by
  classical
  letI : Algebra O (L) := ((algebraMap ↥A (L)).comp (algebraMap O ↥A)).toAlgebra
  let j : ↥A →ₐ[O] L :=
    { (algebraMap ↥A (L)) with commutes' := fun _ => rfl }
  have hj : Function.Injective j := Subtype.val_injective
  by_cases hB : Nontrivial B
  · haveI := hB
    have hcard : Nat.card (B →ₐ[O] L) = Module.finrank O B :=
      HopfAlgebra.natCard_algHom_eq_finrank_of_charZero O B (L)
    haveI : Finite (B →ₐ[O] L) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact Module.finrank_pos.ne')
    refine Finite.of_injective (fun f : WithConv (B →ₐ[O] ↥A) => j.comp (WithConv.ofConv f)) ?_
    intro f g hfg
    apply WithConv.ext
    apply AlgHom.ext
    intro b
    exact hj (congrArg (fun φ : B →ₐ[O] L => φ b) hfg)
  · rw [not_nontrivial_iff_subsingleton] at hB
    haveI : IsEmpty (WithConv (B →ₐ[O] ↥A)) := ⟨fun f => by
      have h := (WithConv.ofConv f).map_one
      rw [Subsingleton.elim (1 : B) 0, map_zero] at h
      exact zero_ne_one h⟩
    infer_instance

end PtsFin

namespace S17KummerOGen
namespace PointsDict

open WithConv

section Provider
variable {L : Type} [Field L]
variable (A : ValuationSubring (L)) (O : Type) [CommRing O] [Algebra O ↥A]

@[reducible] noncomputable def algebraQbar : Algebra O (L) :=
  ((algebraMap ↥A (L)).comp (algebraMap O ↥A)).toAlgebra

theorem isScalarTower_qbar : letI := algebraQbar A O; IsScalarTower O ↥A (L) :=
  letI := algebraQbar A O
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

end Provider

section Points

variable {L : Type} [Field L]
variable {A : ValuationSubring (L)} {O : Type} [CommRing O] [Algebra O ↥A]
  [Algebra O (L)] [IsScalarTower O ↥A (L)]
variable (B : Type) [CommRing B] [Bialgebra O B]

omit [Bialgebra O B] in
theorem algebraMap_mem (x : O) : algebraMap O (L) x ∈ A := by
  rw [IsScalarTower.algebraMap_apply O ↥A (L)]
  exact (algebraMap O ↥A x).2

noncomputable abbrev jA : ↥A →ₐ[O] L := IsScalarTower.toAlgHom O ↥A (L)

omit [Bialgebra O B] in
theorem jA_apply (a : ↥A) : jA (A := A) (O := O) a = (a : L) := rfl

theorem apply_mem_of_moduleFinite {B : Type} [CommRing B] [Algebra O B] [Module.Finite O B]
    (f : B →ₐ[O] L) (h : B) : f h ∈ A := by
  classical
  have hOA : ∀ x : O, algebraMap O (L) x ∈ A := algebraMap_mem (A := A) (O := O)
  have hint : IsIntegral O (f h) := (Algebra.IsIntegral.isIntegral (R := O) h).map f
  obtain ⟨p, hpm, hpev⟩ := hint
  rw [← A.valuation_le_one_iff]
  by_contra hgt
  rw [not_le] at hgt
  have hy0 : A.valuation (f h) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
  have hsum : ∑ i ∈ Finset.range (p.natDegree + 1),
      algebraMap O (L) (p.coeff i) * f h ^ i = 0 := by
    rw [← Polynomial.eval₂_eq_sum_range]
    exact hpev
  rw [Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hyd : f h ^ p.natDegree
      = -∑ i ∈ Finset.range p.natDegree,
          algebraMap O (L) (p.coeff i) * f h ^ i :=
    eq_neg_of_add_eq_zero_right hsum
  have hlt : A.valuation (∑ i ∈ Finset.range p.natDegree,
      algebraMap O (L) (p.coeff i) * f h ^ i)
        < A.valuation (f h) ^ p.natDegree := by
    apply Valuation.map_sum_lt _ (pow_ne_zero _ hy0)
    intro i hi
    have hi' : i < p.natDegree := Finset.mem_range.mp hi
    rw [Valuation.map_mul, Valuation.map_pow]
    calc A.valuation (algebraMap O (L) (p.coeff i)) * A.valuation (f h) ^ i
        ≤ 1 * A.valuation (f h) ^ i := by
          apply mul_le_mul_left
          exact (A.valuation_le_one_iff _).mpr (hOA (p.coeff i))
      _ = A.valuation (f h) ^ i := one_mul _
      _ < A.valuation (f h) ^ p.natDegree := pow_lt_pow_right₀ hgt hi'
  have hcontra : A.valuation (f h ^ p.natDegree) < A.valuation (f h) ^ p.natDegree := by
    rw [hyd, Valuation.map_neg]
    exact hlt
  rw [Valuation.map_pow] at hcontra
  exact lt_irrefl _ hcontra

noncomputable def toQ (f : WithConv (B →ₐ[O] ↥A)) : WithConv (B →ₐ[O] L) :=
  toConv ((jA (A := A) (O := O)).comp (ofConv f))

theorem toQ_apply (f : WithConv (B →ₐ[O] ↥A)) (b : B) :
    ofConv (toQ B f) b = ((ofConv f b : ↥A) : L) := rfl

theorem toQ_injective : Function.Injective (toQ (A := A) (O := O) B) := by
  intro f g hfg
  apply WithConv.ext
  apply AlgHom.ext
  intro b
  apply Subtype.ext
  have := congrArg (fun φ : WithConv (B →ₐ[O] L) => ofConv φ b) hfg
  exact this

theorem toQ_mul (f g : WithConv (B →ₐ[O] ↥A)) : toQ B (f * g) = toQ B f * toQ B g := by
  apply WithConv.ext
  show (jA (A := A) (O := O)).comp (ofConv (f * g)) = _
  rw [AlgHom.comp_convMul_distrib]
  rfl

theorem toQ_one : toQ (A := A) (O := O) B 1 = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro b
  rw [toQ_apply]
  show (((1 : WithConv (B →ₐ[O] ↥A)) b : ↥A) : L) = (1 : WithConv (B →ₐ[O] L)) b
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply, IsScalarTower.algebraMap_apply O ↥A (L)]
  rfl

theorem toQ_pow (f : WithConv (B →ₐ[O] ↥A)) (n : ℕ) : toQ B (f ^ n) = toQ B f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toQ_one]
  | succ n ih => rw [pow_succ, pow_succ, toQ_mul, ih]

noncomputable def ofQ [Module.Finite O B] (φ : WithConv (B →ₐ[O] L)) : WithConv (B →ₐ[O] ↥A) :=
  toConv
    { toFun := fun b => ⟨ofConv φ b, apply_mem_of_moduleFinite (ofConv φ) b⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      commutes' := fun r => Subtype.ext (by
        show ofConv φ (algebraMap O B r) = ((algebraMap O ↥A r : ↥A) : L)
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply O ↥A (L)]
        rfl) }

theorem ofQ_apply [Module.Finite O B] (φ : WithConv (B →ₐ[O] L)) (b : B) :
    ((ofConv (ofQ (A := A) B φ) b : ↥A) : L) = ofConv φ b := rfl

theorem toQ_ofQ [Module.Finite O B] (φ : WithConv (B →ₐ[O] L)) : toQ B (ofQ (A := A) B φ) = φ := by
  apply WithConv.ext; apply AlgHom.ext; intro b; rfl

theorem ofQ_toQ [Module.Finite O B] (f : WithConv (B →ₐ[O] ↥A)) : ofQ (A := A) B (toQ B f) = f := by
  apply WithConv.ext; apply AlgHom.ext; intro b; apply Subtype.ext; rfl

noncomputable def pointsEquiv [Module.Finite O B] : WithConv (B →ₐ[O] ↥A) ≃ WithConv (B →ₐ[O] L) :=
  { toFun := toQ B
    invFun := ofQ (A := A) B
    left_inv := ofQ_toQ B
    right_inv := toQ_ofQ B }

theorem pointsEquiv_apply [Module.Finite O B] (f : WithConv (B →ₐ[O] ↥A)) : pointsEquiv (A := A) B f = toQ B f := rfl

theorem apply_eq_one_iff (f : WithConv (B →ₐ[O] ↥A)) (e : B) : ofConv f e = 1 ↔ ofConv (toQ B f) e = 1 := by
  rw [toQ_apply]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact Subtype.ext h

theorem natCard_block_eq [Module.Finite O B] (e : B) :
    Nat.card {ψ : WithConv (B →ₐ[O] ↥A) // ofConv ψ e = 1} = Nat.card {φ : WithConv (B →ₐ[O] L) // ofConv φ e = 1} :=
  Nat.card_congr ((pointsEquiv (A := A) B).subtypeEquiv (fun f => apply_eq_one_iff B f e))

theorem forall_apply_eq_iff {K : Type} [Field K] [Algebra K L] (σ : L ≃ₐ[K] L) (f g : WithConv (B →ₐ[O] ↥A)) :
    (∀ b : B, ((ofConv g b : ↥A) : L) = σ ((ofConv f b : ↥A) : L)) ↔
      ∀ b : B, ofConv (toQ B g) b = σ (ofConv (toQ B f) b) := Iff.rfl

end Points

end S17KummerOGen.PointsDict

open S17KummerOGen.PointsDict in
theorem S17KummerOGen.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_gen
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring (L)) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : (L ≃ₐ[K] L), σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ ((ι x : ↥A) : L) = ((ι x : ↥A) : L))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn K, σ (a : L) = (a : L)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (n : (L ≃ₐ[K] L) → ℕ)
    (hn : ∀ σ (ζ : L), ζ ^ q = 1 → σ ζ = ζ ^ n σ)
    (D : Submonoid (WithConv (B →ₐ[O] ↥A)))
    (hDcyc : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ f ∈ D, ∀ g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : L) = σ ((WithConv.ofConv f b : ↥A) : L)) → g = f ^ n σ)
    (a : ℕ) (hcardD : Nat.card ↥D = q ^ a) :
    ∃ p₀ : B →ₐc[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q)),
      Function.Surjective p₀ ∧
      ∀ f : B →ₐ[O] ↥A,
        (∃ g : MonoidAlgebra O (Multiplicative (Fin a → ZMod q)) →ₐ[O] ↥A,
            g.comp (p₀ : B →ₐ[O] MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) = f) ↔
          WithConv.toConv f ∈ D := by
  classical
  have hqp : q.Prime := Fact.out
  have hq0 : q ≠ 0 := hqp.ne_zero
  have hQpos : 0 < q := hqp.pos

  letI : Algebra O (L) := algebraQbar A O
  haveI : IsScalarTower O ↥A (L) := isScalarTower_qbar A O
  haveI : FaithfulSMul O (L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply hι
    rw [← hιalg, ← hιalg]
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply O ↥A (L), IsScalarTower.algebraMap_apply O ↥A (L)] at hxy
    exact hxy
  have halg : ∀ x : O, algebraMap O (L) x = ((ι x : ↥A) : L) := by
    intro x
    rw [IsScalarTower.algebraMap_apply O ↥A (L), hιalg]
    rfl
  have hOA : ∀ x : O, algebraMap O (L) x ∈ A := fun x => algebraMap_mem (A := A) (O := O) x
  have hOfix : ∀ σ : (L ≃ₐ[K] L), σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ (algebraMap O (L) x) = algebraMap O (L) x := by
    intro σ
    rw [hιfix σ]
    simp only [halg]
  have hOmax : ∀ y ∈ A, (∀ σ ∈ A.inertiaSubgroupIn K, σ y = y) → ∃ x : O, algebraMap O (L) x = y := by
    intro y hy hfix
    obtain ⟨x, hx⟩ := hιmax ⟨y, hy⟩ (fun σ hσ => hfix σ hσ)
    exact ⟨x, by rw [halg, hx]⟩

  let toQh : WithConv (B →ₐ[O] ↥A) →* WithConv (B →ₐ[O] L) :=
    { toFun := toQ (A := A) (O := O) B, map_one' := toQ_one B, map_mul' := toQ_mul B }
  have htoQh : ∀ f, toQh f = toQ (A := A) (O := O) B f := fun _ => rfl
  let D' : Submonoid (WithConv (B →ₐ[O] L)) := D.map toQh
  have hmemD' : ∀ f : WithConv (B →ₐ[O] ↥A), toQ (A := A) (O := O) B f ∈ D' ↔ f ∈ D := by
    intro f
    constructor
    · rintro ⟨g, hg, hgf⟩
      rw [htoQh] at hgf
      rwa [← toQ_injective B hgf]
    · intro hf
      exact ⟨f, hf, rfl⟩
  have hcardD' : Nat.card ↥D' = q ^ a := by
    rw [← hcardD]
    refine (Nat.card_congr (Equiv.ofBijective (fun d : ↥D => (⟨toQh d.1, d.1, d.2, rfl⟩ : ↥D')) ⟨?_, ?_⟩)).symm
    · intro d₁ d₂ h
      exact Subtype.ext (toQ_injective (A := A) (O := O) B (congrArg Subtype.val h))
    · rintro ⟨_, f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩

  have hptq : ∀ φ : WithConv (B →ₐ[O] L), φ ^ q = 1 := by
    intro φ
    rw [← toQ_ofQ (A := A) B φ, ← toQ_pow, hBq, toQ_one]

  have hD' : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ c : ℕ,
      (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ c) →
      ∀ φ ∈ D', ∀ ψ : WithConv (B →ₐ[O] L), (∀ h : B, ψ h = σ (φ h)) → ψ = φ ^ c := by
    intro σ hσ c hc φ hφ ψ hψ
    obtain ⟨f, hf, rfl⟩ := hφ
    rw [htoQh] at hψ ⊢
    let g := ofQ (A := A) B ψ
    have hg : toQ (A := A) (O := O) B g = ψ := toQ_ofQ B ψ
    have hrel : ∀ b : B, ((WithConv.ofConv g b : ↥A) : L) = σ ((WithConv.ofConv f b : ↥A) : L) := by
      rw [forall_apply_eq_iff B σ f g, hg]
      exact hψ
    have key := hDcyc σ hσ f hf g hrel
    rw [← hg, key, toQ_pow]

    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := q)
    have h1 : ζ ^ (n σ) = ζ ^ c := by rw [← hn σ ζ hζ.pow_eq_one, hc ζ hζ.pow_eq_one]
    rw [pow_eq_pow_mod (n σ) hζ.pow_eq_one, pow_eq_pow_mod c hζ.pow_eq_one] at h1
    have hmod : n σ % q = c % q := hζ.pow_inj (Nat.mod_lt _ hQpos) (Nat.mod_lt _ hQpos) h1
    rw [pow_eq_pow_mod (n σ) (hptq _), hmod, ← pow_eq_pow_mod c (hptq _)]
  obtain ⟨p₀, hsurj, hfac⟩ :=
    HopfAlgebra.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_submonoid_of_isAlgClosed q hq2 A O hOA inferInstance hirr hOfix hOmax
      B D' a hcardD' hD'
  refine ⟨p₀, hsurj, fun f => ?_⟩
  have hQ := hfac ((jA (A := A) (O := O)).comp f)
  have hmem : WithConv.toConv ((jA (A := A) (O := O)).comp f) ∈ D' ↔ WithConv.toConv f ∈ D :=
    hmemD' (WithConv.toConv f)
  rw [hmem] at hQ
  rw [← hQ]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨(jA (A := A) (O := O)).comp g, by rw [← hg]; rfl⟩
  · rintro ⟨g', hg'⟩
    refine ⟨WithConv.ofConv (ofQ (A := A) (MonoidAlgebra O (Multiplicative (Fin a → ZMod q))) (WithConv.toConv g')), ?_⟩
    refine AlgHom.ext fun b => Subtype.ext ?_
    have := DFunLike.congr_fun hg' b
    exact this

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L] [CharZero L]
    (A : ValuationSubring L) (hA : A.LiesOverPrime q)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hirr : Irreducible (q : O))
    [Algebra O ↥A] (ι : O →+* ↥A) (hι : Function.Injective ι) (hιalg : ∀ x : O, algebraMap O ↥A x = ι x)
    (hιfix : ∀ σ : (L ≃ₐ[K] L), σ ∈ A.inertiaSubgroupIn K ↔ ∀ x : O, σ ((ι x : ↥A) : L) = ((ι x : ↥A) : L))
    (hιmax : ∀ a : ↥A, (∀ σ ∈ A.inertiaSubgroupIn K, σ (a : L) = (a : L)) → a ∈ Set.range ι)
    (B : Type) [CommRing B] [HopfAlgebra O B] [Module.Finite O B] [Module.Free O B] [Coalgebra.IsCocomm O B]
    (hBq : ∀ (T : Type) [CommRing T] [Algebra O T] (f : WithConv (B →ₐ[O] T)), f ^ q = 1)
    (n : (L ≃ₐ[K] L) → ℕ)
    (hn : ∀ σ (ζ : L), ζ ^ q = 1 → σ ζ = ζ ^ n σ)
    (D : Submonoid (WithConv (B →ₐ[O] ↥A)))
    (hDcyc : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ f ∈ D, ∀ g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : L) = σ ((WithConv.ofConv f b : ↥A) : L)) → g = f ^ n σ)
    (hquot : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ f g : WithConv (B →ₐ[O] ↥A),
      (∀ b : B, ((WithConv.ofConv g b : ↥A) : L) = σ ((WithConv.ofConv f b : ↥A) : L)) → ∃ d ∈ D, g = f * d) :
    ∃ (t : ℕ) (u β : Fin t → L),
      (∀ i, A.valuation (u i) = 1) ∧
      (∀ i, ∀ σ ∈ A.inertiaSubgroupIn K, σ (u i) = u i) ∧
      (∀ i, (β i) ^ q = u i) ∧
      (∀ σ ∈ A.inertiaSubgroupIn K,
        (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ) →
        (∀ i, σ (β i) = β i) →
        ∀ f g : WithConv (B →ₐ[O] ↥A),
          (∀ b : B, ((WithConv.ofConv g b : ↥A) : L) = σ ((WithConv.ofConv f b : ↥A) : L)) → g = f) := by
  classical
  have hqp : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩

  haveI hfinP : Finite (WithConv (B →ₐ[O] ↥A)) := S17KummerOGen.finite_points q A O B hBq
  haveI : Finite ↥D := Finite.of_injective (fun d : ↥D => (d : WithConv (B →ₐ[O] ↥A))) Subtype.val_injective
  have hDq : ∀ f : ↥D, f ^ q = 1 := fun f => Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hBq (↥A) f.1)

  letI : Group ↥D :=
    { inv := fun f => f ^ (q - 1)
      inv_mul_cancel := fun f => by
        show f ^ (q - 1) * f = 1
        rw [← pow_succ, Nat.sub_add_cancel hqp.one_lt.le, hDq] }
  have hPG : IsPGroup q ↥D := fun f => ⟨1, by rw [pow_one]; exact hDq f⟩
  obtain ⟨a, ha⟩ := hPG.exists_card_eq

  obtain ⟨p₀, hsurj, hp₀⟩ := S17KummerOGen.exists_surjective_bialgHom_monoidAlgebra_of_inertiaCyclotomic_gen q hq2 A hA O hirr ι hι hιalg hιfix hιmax B hBq n hn D hDcyc a ha
  have hΛ : Nat.card (Fin a → ZMod q) = Nat.card ↥D := by
    rw [ha, Nat.card_eq_fintype_card, Fintype.card_pi, Finset.prod_const, ZMod.card, Finset.card_univ, Fintype.card_fin]
  obtain ⟨N, ε, hidem, horth, hsum, hc0, hc, hpts, hpts0, hptsne, hcoset, hcardblk, hcardtot⟩ :=
    KummerO.exists_blockIdempotents_of_quotient_inertiaTrivial_of_isAlgClosed q hq2 A hA O hirr ι hι hιalg hιfix hιmax B hBq n hn D hDcyc hquot (Fin a → ZMod q) hΛ

  have hΛq : ∀ g : Fin a → ZMod q, q • g = 0 := fun g => by
    funext i; simp
  have hblk : ∀ i : Fin (N + 1), ∃ (U β : (Fin a → ZMod q) → L),
      (∀ g, A.valuation (U g) = 1) ∧
      (∀ g, ∀ σ ∈ A.inertiaSubgroupIn K, σ (U g) = U g) ∧
      (∀ g, (β g) ^ q = U g) ∧
      (∀ σ ∈ A.inertiaSubgroupIn K, (∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ) → (∀ g, σ (β g) = β g) →
        ∀ ψ : WithConv (B →ₐ[O] ↥A), ψ (ε i) = 1 → i ≠ 0 →
          ∀ b : B, σ ((WithConv.ofConv ψ b : ↥A) : L) = ((WithConv.ofConv ψ b : ↥A) : L)) := by
    intro i
    by_cases hi : i = 0
    · exact ⟨fun _ => 1, fun _ => 1, fun _ => by rw [Valuation.map_one], fun _ σ _ => map_one σ, fun _ => one_pow _,
        fun _ _ _ _ _ _ h => absurd hi h⟩
    · obtain ⟨U, β, h1, h2, h3, h4⟩ := KummerO.exists_units_of_block_of_isAlgClosed q hq2 A hA O hirr ι hι hιalg hιfix hιmax B hBq
        (Fin a → ZMod q) hΛq p₀ hsurj (ε i) (hidem i) (hc i hi) (hcardblk i) (hptsne i)
      exact ⟨U, β, h1, h2, h3, fun σ hσ hμ hβ ψ hψ _ => h4 σ hσ hμ hβ ψ hψ⟩
  choose U β hUval hUfix hβ hfixblk using hblk

  let eqv : Fin (N + 1) × (Fin a → ZMod q) ≃ Fin (Fintype.card (Fin (N + 1) × (Fin a → ZMod q))) := Fintype.equivFin _
  refine ⟨Fintype.card (Fin (N + 1) × (Fin a → ZMod q)), fun j => U (eqv.symm j).1 (eqv.symm j).2,
    fun j => β (eqv.symm j).1 (eqv.symm j).2, fun j => hUval _ _, fun j => hUfix _ _, fun j => hβ _ _, ?_⟩
  intro σ hσ hσμ hσβ f g hfg

  have hnσ : ∀ x : WithConv (B →ₐ[O] ↥A), x ^ n σ = x := by
    intro x
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := q)
    have h1 : ζ ^ (n σ) = ζ ^ 1 := by rw [pow_one, ← hn σ ζ hζ.pow_eq_one, hσμ ζ hζ.pow_eq_one]
    rw [pow_eq_pow_mod (n σ) hζ.pow_eq_one, pow_eq_pow_mod 1 hζ.pow_eq_one] at h1
    have hmod : n σ % q = 1 % q := hζ.pow_inj (Nat.mod_lt _ hqp.pos) (Nat.mod_lt _ hqp.pos) h1
    have hxq : x ^ q = 1 := hBq (↥A) x
    rw [← Nat.mod_add_div (n σ) q, pow_add, pow_mul, hxq, one_pow, mul_one, hmod, Nat.mod_eq_of_lt hqp.one_lt, pow_one]

  obtain ⟨i, hi, -⟩ := hpts f
  by_cases hi0 : i = 0
  ·
    subst hi0
    have hfD : f ∈ D := (hpts0 f).mpr hi
    rw [hDcyc σ hσ f hfD g hfg, hnσ]
  ·
    have hβi : ∀ g' : Fin a → ZMod q, σ (β i g') = β i g' := by
      intro g'
      have := hσβ (eqv (i, g'))
      simp only [eqv, Equiv.symm_apply_apply] at this
      exact this
    have hfix := hfixblk i σ hσ hσμ hβi f hi hi0
    apply WithConv.ext
    apply AlgHom.ext
    intro b
    apply Subtype.ext
    rw [hfg b, hfix b]

end S_KummerO_forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed
end P2MW
export P2MW.S_KummerO_forall_eq_of_finiteFreeHopf_of_inertiaCyclotomic_of_quotient_inertiaTrivial_of_isAlgClosed (solution)
