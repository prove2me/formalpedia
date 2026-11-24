-- Prove2me | solution 1 for GlobalTheory.residueField_map_adicCompletion_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:30.343387+00:00
-- url     : https://prove2.me/submissions/5050de7c-bd34-4eb3-bfb2-c29aabba3d5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueFieldMapAdicCompletionSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (W : Type*) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] :
    Function.Surjective (ResidueField.map (algebraMap W (AdicCompletion (maximalIdeal W) W))) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal W) 1 x)
  refine ⟨residue W w, ?_⟩
  rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal,
    mem_nonunits_iff]
  intro hu
  have h1 := hu.map (AdicCompletion.evalₐ (maximalIdeal W) 1)
  rw [map_sub, AlgHom.commutes, ← hw, Ideal.Quotient.algebraMap_eq, sub_self] at h1
  haveI : Nontrivial (W ⧸ maximalIdeal W ^ 1) :=
    Ideal.Quotient.nontrivial_iff.mpr (by rw [pow_one]; exact (maximalIdeal.isMaximal W).ne_top)
  exact not_isUnit_zero h1
end GlobalTheory
