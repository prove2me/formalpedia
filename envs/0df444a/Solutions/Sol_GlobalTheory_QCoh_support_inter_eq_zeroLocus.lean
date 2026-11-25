-- Prove2me | solution 1 for GlobalTheory.QCoh.support_inter_eq_zeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:52.108625+00:00
-- url     : https://prove2.me/submissions/162dbf5d-35a9-42fa-869d-19948b35d3c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_mem_support_iff_annihilator_le
import Theorems.Thm_GlobalTheory_QCoh_mem_primeCompl_primeIdealOf_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable (F)
namespace GlobalTheory.QCoh
theorem _root_.solution [IsFiniteQC F] (hU : IsAffineOpen U) :
    support F ∩ U = X.zeroLocus (U := U) (Module.annihilator Γ(X, U) Γ(F, U)) ∩ U := by
  ext x
  refine and_congr_left fun hx ↦ (mem_support_iff_annihilator_le hU ⟨x, hx⟩).trans ?_
  rw [Scheme.mem_zeroLocus_iff]
  refine forall₂_congr fun f _ ↦ ?_
  rw [← mem_primeCompl_primeIdealOf_iff hU ⟨x, hx⟩ f]
  exact not_not.symm
end GlobalTheory.QCoh
