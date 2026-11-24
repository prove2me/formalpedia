-- Prove2me | solution 1 for GlobalTheory.JR.Et.mem_OK_iff_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:48.532534+00:00
-- url     : https://prove2.me/submissions/0ba84ed1-a30f-4fe5-a9cd-7e435656001e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Theorems.Thm_GlobalTheory_JR_Et_charpoly_dvd_pow_of_aeval_zero
import Theorems.Thm_GlobalTheory_JR_Et_aeval_self_charpoly_lmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open Polynomial
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.Et
theorem _root_.solution [IsUltrametricDist F] (A : Et F E) (z : A.K) :
    z ∈ A.OK ↔ IsIntegral (NormedField.valuation (K := F)).integer z := by
  constructor
  · intro hz
    have hl : LinearMap.charpoly (Algebra.lmul F A.K z) ∈
        Polynomial.lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro i
      refine ⟨⟨_, ?_⟩, rfl⟩
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
      exact_mod_cast hz i
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic _)
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap F, hq]
    exact aeval_self_charpoly_lmul A z
  · rintro ⟨p, hpm, hp⟩ i
    have hp' : aeval z (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def]; exact hp
    have h1 : aeval (Algebra.lmul F A.K z) (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, hp', map_zero]
    let bs := Module.finBasis F A.K
    have h2 : aeval (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z))
        (p.map (algebraMap (NormedField.valuation (K := F)).integer F)) = 0 := by
      rw [aeval_algHom_apply, h1, map_zero]
    have h3 := charpoly_dvd_pow_of_aeval_zero _ _ h2
    have h4 : (LinearMap.toMatrixAlgEquiv bs (Algebra.lmul F A.K z)).charpoly =
        LinearMap.charpoly (Algebra.lmul F A.K z) := LinearMap.charpoly_toMatrix _ bs
    rw [h4, ← Polynomial.map_pow] at h3
    have h5 := Polynomial.isIntegral_coeff_of_dvd _ _ (hpm.pow _) (LinearMap.charpoly_monic _) h3 i
    have h6 := (Valuation.integer.integers (NormedField.valuation (K := F))).mem_of_integral h5
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h6
    exact_mod_cast h6
end GlobalTheory.JR.Et
