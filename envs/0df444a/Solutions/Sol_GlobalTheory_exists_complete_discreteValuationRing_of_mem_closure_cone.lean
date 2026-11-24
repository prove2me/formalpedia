-- Prove2me | solution 1 for GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:22.114946+00:00
-- url     : https://prove2.me/submissions/8d2ee63e-14c6-4a3f-b772-a33514b8f214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC
import Theorems.Thm_GlobalTheory_coeff_aeval_C_mul_X
import Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_of_valuationSubring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K A J : Type) [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Fintype J], Algebra.FiniteType K A → ∀ (w : J → A) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J K) (d : ℕ), G.IsHomogeneous d → MvPolynomial.aeval w G = 0 → MvPolynomial.eval v G = 0) → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A →ₐ[K] FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro K A J _ _ _ _ _ hA w v hv hG
  let L := FractionRing (Polynomial A)
  have hinj : Function.Injective (algebraMap (Polynomial A) L) := IsFractionRing.injective _ _
  have : Algebra.EssFiniteType (Polynomial A) L := .of_isLocalization L (nonZeroDivisors _)
  have : Algebra.FiniteType K (Polynomial A) := .trans hA inferInstance
  have : Algebra.EssFiniteType K L := .comp K (Polynomial A) L
  let ψ : MvPolynomial J K →ₐ[K] Polynomial A :=
    MvPolynomial.aeval fun j => Polynomial.C (w j) * Polynomial.X
  let Φ : MvPolynomial J K →+* L := (algebraMap (Polynomial A) L).comp ψ.toRingHom
  have hker : RingHom.ker Φ ≤ RingHom.ker (MvPolynomial.eval v) := by
    intro G h
    have h1 : ψ G = 0 := hinj (h.trans (map_zero _).symm)
    rw [RingHom.mem_ker, ← MvPolynomial.sum_homogeneousComponent G, map_sum]
    refine Finset.sum_eq_zero fun d _ => hG _ d (MvPolynomial.homogeneousComponent_isHomogeneous d G) ?_
    rw [← coeff_aeval_C_mul_X]
    change (ψ G).coeff d = 0
    rw [h1, Polynomial.coeff_zero]
  have hne : (RingHom.ker (MvPolynomial.eval v)).map Φ.rangeRestrict ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, Ideal.mem_map_iff_of_surjective _ Φ.rangeRestrict_surjective]
    rintro ⟨G, h1, h2⟩
    have h3 : G - 1 ∈ RingHom.ker Φ := by
      rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      exact congrArg Subtype.val h2
    have h4 := hker h3
    rw [RingHom.mem_ker] at h1 h4
    simp [h1] at h4
  obtain ⟨U, hU, hU'⟩ := Ideal.image_subset_nonunits_valuationSubring (A := Φ.range) _ hne
  have hC : ∀ r : K, Φ (MvPolynomial.C r) = algebraMap K L r := fun r => by
    rw [IsScalarTower.algebraMap_apply K (Polynomial A) L, ← ψ.commutes]
    rfl
  let t : J → L := fun j => Φ (MvPolynomial.X j - MvPolynomial.C (v j))
  have ht : ∀ j, t j = algebraMap (Polynomial A) L
      (Polynomial.C (w j) * Polynomial.X - Polynomial.C (algebraMap K A (v j))) := fun j => by
    simp [t, Φ, ψ]
  obtain ⟨V, hV, hKV, -, htV⟩ := exists_discreteValuationSubring_of_valuationSubring (R := K) U
    (fun r => hU ⟨_, hC r⟩) Set.finite_empty (Set.finite_range t) (by simp)
    (by
      rintro _ ⟨j, rfl⟩
      exact hU' ⟨_, Ideal.mem_map_of_mem _
        (show MvPolynomial.X j - MvPolynomial.C (v j) ∈ _ by simp [RingHom.mem_ker]), rfl⟩)
    (by
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
      refine ⟨_, ⟨j, rfl⟩, fun h => hj ?_⟩
      rw [ht, map_eq_zero_iff _ hinj] at h
      simpa using congrArg (Polynomial.coeff · 0) h)
  let W := AdicCompletion (maximalIdeal V) V
  let κ : K →+* V := (algebraMap K L).codRestrict V hKV
  let ι : V →+* W := algebraMap V W
  letI : Algebra K W := (ι.comp κ).toAlgebra
  have hι : Function.Injective ((algebraMap W (FractionRing W)).comp ι) :=
    (IsFractionRing.injective W _).comp (algebraMap_adicCompletion_injective_of_dvr V)
  let g : L →+* FractionRing W := IsFractionRing.lift hι
  have hg : ∀ x : V, g x = algebraMap W (FractionRing W) (ι x) := fun x =>
    IsFractionRing.lift_algebraMap hι x
  let f : A →ₐ[K] FractionRing W :=
    { g.comp ((algebraMap (Polynomial A) L).comp Polynomial.C) with
      commutes' := fun r => by
        rw [IsScalarTower.algebraMap_apply K W (FractionRing W)]
        exact hg (κ r) }
  have htm : ∀ j, t j ∈ V := fun j => V.nonunits_subset (htV _ ⟨j, rfl⟩)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, f,
    g (algebraMap (Polynomial A) L Polynomial.X), fun j => ι (⟨t j, htm j⟩ + κ (v j)),
    inferInstance, ?_, fun j => ⟨?_, ?_⟩⟩
  · rw [map_ne_zero, map_ne_zero_iff _ hinj]
    exact Polynomial.X_ne_zero
  · rw [← hg]
    change g (t j + algebraMap (Polynomial A) L (Polynomial.C (algebraMap K A (v j)))) =
      _ * g (algebraMap (Polynomial A) L (Polynomial.C (w j)))
    rw [ht, ← map_add, sub_add_cancel, mul_comm, map_mul, map_mul]
  · change ι _ - ι (κ (v j)) ∈ _
    rw [← map_sub, add_sub_cancel_right]
    exact map_nonunit ι _
      ((ValuationSubring.coe_mem_nonunits_iff (a := ⟨t j, htm j⟩)).mp (htV _ ⟨j, rfl⟩))
end GlobalTheory
