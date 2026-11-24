-- Prove2me | solution 1 for GlobalTheory.JR.Spec.isIntegral_integer_of_spectralNorm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:09:43.916458+00:00
-- url     : https://prove2.me/submissions/b16f28ac-2e9c-4a85-a0e6-9f6e1ab070b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametric

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Spec
variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
  {k : Type} [Field k] [Algebra F k]
namespace GlobalTheory.JR.Spec
theorem _root_.solution [FiniteDimensional F k] {y : k}
    (h : spectralNorm F k y ≤ 1) : IsIntegral (NormedField.valuation (K := F)).integer y := by
  have hyF : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyF)] at h
  have hl : minpoly F y ∈ lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast h n
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyF)
  refine ⟨q, hqm, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F, hq, minpoly.aeval]
end GlobalTheory.JR.Spec
