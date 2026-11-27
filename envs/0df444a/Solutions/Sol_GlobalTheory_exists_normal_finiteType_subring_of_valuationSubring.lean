-- Prove2me | solution 1 for GlobalTheory.exists_normal_finiteType_subring_of_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:14.812653+00:00
-- url     : https://prove2.me/submissions/5011a160-b010-462f-896c-13a69cb40550

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EssFiniteTypeOfFiniteDimensionalSubfieldClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormalFiniteTypeSubringInValuationSubring
import Theorems.Thm_GlobalTheory_finiteDimensional_top_subfield
import Theorems.Thm_GlobalTheory_essFiniteType_of_finiteDimensional_subfield_closure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] (φ : K →+* L) (c : ℂ →+* K), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) (hc : ∀ a, φ (c a) ∈ V) (t : Finset L), (∀ x ∈ t, x ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ R : Subring K, ∃ hcR : ∀ a, c a ∈ R, (c.codRestrict R hcR).FiniteType ∧ R ≤ (V.comap φ).toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R K ∧ (∀ x ∈ t, ∃ p : R[X], p.Monic ∧ p.eval₂ (φ.comp R.subtype) x = 0) := by
  intro K L _ _ φ c hfin V hc t ht hgen
  classical
  letI : Algebra ℂ K := c.toAlgebra
  letI : Algebra K L := φ.toAlgebra
  letI : Algebra ℂ L := (φ.comp c).toAlgebra
  haveI : IsScalarTower ℂ K L := .of_algebraMap_eq fun _ => rfl
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective
  have ht' : ∀ x : t, ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0 :=
    fun x => (ht x x.2).2
  choose p hpm hpc hpx using ht'
  let T : Set K := ⋃ x : t, ((p x).coeffs : Set K)
  have hT : T.Finite := Set.finite_iUnion fun x => (p x).coeffs.finite_toSet
  let A : Subalgebra ℂ K := Algebra.adjoin ℂ T
  haveI : Algebra.FiniteType ℂ A := .adjoin_of_finite hT
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have hcoefA : ∀ x : t, ∀ n, (p x).coeff n ∈ A := fun x n => by
    by_cases h : (p x).coeff n = 0
    · rw [h]; exact A.zero_mem
    · exact Algebra.subset_adjoin (Set.mem_iUnion.mpr ⟨x, Polynomial.coeff_mem_coeffs h⟩)
  have hAE : ∀ y ∈ A, y ∈ V.comap φ := fun y hy => by
    let E' : Subalgebra ℂ K := { (V.comap φ).toSubring with algebraMap_mem' := fun a => hc a }
    have : A ≤ E' := Algebra.adjoin_le (by
      intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hpc x i)
    exact this hy
  haveI : IsScalarTower A K L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ A L := .of_algebraMap_eq fun _ => rfl
  have hint : ∀ x : t, IsIntegral A (x : L) := fun x => by
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap A K)
      ((lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, hcoefA x n⟩, rfl⟩) (hpm x)
    refine ⟨q, hqm, ?_⟩
    rw [← hpx x, ← hq, eval₂_map]
    rfl

  have hsub : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤ (integralClosure A L).toSubring :=
    Subring.closure_le.mpr (Set.union_subset
      (by
        rintro _ ⟨a, rfl⟩
        exact isIntegral_algebraMap (R := A) (x := (⟨c a, A.algebraMap_mem a⟩ : A)))
      (fun x hx => hint ⟨x, hx⟩))
  have hall : ∀ l : L, ∃ b ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)),
      ∃ d ∈ Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)), (l = b / d ∨ l⁻¹ = b / d) := by
    intro l
    rcases V.mem_or_inv_mem l with h | h
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen l h
      exact ⟨b, hb, d, hd, Or.inl he⟩
    · obtain ⟨b, hb, d, hd, -, -, he⟩ := hgen _ h
      exact ⟨b, hb, d, hd, Or.inr he⟩
  haveI : Algebra.IsAlgebraic A L := ⟨fun l => by
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hb' : IsAlgebraic A b := (hsub hb : IsIntegral A b).isAlgebraic
    have hd' : IsAlgebraic A d := (hsub hd : IsIntegral A d).isAlgebraic
    have hbd : IsAlgebraic A (b / d) := by rw [div_eq_mul_inv]; exact hb'.mul hd'.inv
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact hbd.inv⟩
  haveI : Algebra.IsAlgebraic A K := ⟨fun k =>
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom A K L) φ.injective).mp
      (Algebra.IsAlgebraic.isAlgebraic (φ k))⟩
  have htop : Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L)) = ⊤ := by
    refine eq_top_iff.mpr fun l _ => ?_
    have hle : Subring.closure (Set.range (φ.comp c) ∪ (t : Set L)) ≤
        (Subfield.closure (Set.range (algebraMap ℂ L) ∪ (t : Set L))).toSubring :=
      Subring.closure_le.mpr Subfield.subset_closure
    obtain ⟨b, hb, d, hd, h⟩ := hall l
    have hbd := Subfield.div_mem _ (hle hb) (hle hd)
    rcases h with h | h
    · rw [h]; exact hbd
    · rw [← inv_inv l, h]; exact Subfield.inv_mem _ hbd
  haveI : Algebra.EssFiniteType ℂ L := by
    refine essFiniteType_of_finiteDimensional_subfield_closure t.finite_toSet ?_
    rw [htop]
    exact finiteDimensional_top_subfield L
  haveI : Algebra.EssFiniteType A L := .of_comp ℂ A L
  haveI := finite_integralClosure_of_essFiniteType_field ℂ A L
  let S := integralClosure A K
  let f : S →ₐ[A] integralClosure A L :=
    ((IsScalarTower.toAlgHom A K L).comp S.val).codRestrict _ fun z =>
      (z.2.map (IsScalarTower.toAlgHom A K L) : IsIntegral A _)
  haveI : Module.Finite A S := Module.Finite.of_injective f.toLinearMap fun z w h =>
    Subtype.ext (φ.injective (congrArg Subtype.val h : _))
  haveI : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℂ S
  haveI : IsFractionRing S K := integralClosure.isFractionRing_of_algebraic fun x hx => Subtype.ext hx
  haveI : IsIntegrallyClosed S := (isIntegrallyClosed_iff K).mpr fun {x} hx =>
    ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩

  have hcR : ∀ a, c a ∈ S.toSubring := fun a => S.algebraMap_mem (⟨c a, A.algebraMap_mem a⟩ : A)
  refine ⟨S.toSubring, hcR, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ S)
  · intro x hx
    obtain ⟨q, hqm, hq⟩ := (hx : IsIntegral A x)
    let ι : A →+* V.comap φ :=
      { toFun := fun a => ⟨a, hAE a a.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hE : IsIntegral (V.comap φ) x := by
      refine ⟨q.map ι, hqm.map ι, ?_⟩
      rw [eval₂_map]
      exact hq
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hE
    exact y.2
  · exact (inferInstance : IsNoetherianRing S)
  · exact (inferInstance : IsIntegrallyClosed S)
  · exact (inferInstance : IsFractionRing S K)
  · intro x hx
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := S.toSubring.subtype)
      ((lifts_iff_coeff_lifts _).mpr fun n =>
        ⟨⟨_, S.algebraMap_mem (⟨_, hcoefA ⟨x, hx⟩ n⟩ : A)⟩, rfl⟩) (hpm ⟨x, hx⟩)
    refine ⟨q, hqm, ?_⟩
    rw [← eval₂_map, hq]
    exact hpx ⟨x, hx⟩
end GlobalTheory
