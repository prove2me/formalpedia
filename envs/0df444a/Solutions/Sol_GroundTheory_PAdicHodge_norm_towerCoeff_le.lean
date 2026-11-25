-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_towerCoeff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:11.353063+00:00
-- url     : https://prove2.me/submissions/908a6a0d-9eb0-4250-af4b-1e0d2f24c405

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_mono
import Theorems.Thm_GroundTheory_PAdicHodge_relDeg_eq_of_le
import Theorems.Thm_GroundTheory_PAdicHodge_towerDualVec_mem
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_mul_normTrace_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {m : ℕ} (hm : stableIndex K ≤ m) {y : PadicAlgCl p}
    (hy : y ∈ cyclotomicLayer K m) (i : Fin (relDeg K (stableIndex K))) :
    ‖towerCoeff K m y i‖ ≤ ‖y * towerDualVec K i‖ := by
  let L := extendScalars (cycl_le_cyclotomicLayer K m)
  have hw : y * towerDualVec K i ∈ L :=
    mul_mem hy (cyclotomicLayer_mono K hm (towerDualVec_mem K i))
  apply norm_natCast_mul_normTrace_le
  have e := minpoly.algebraMap_eq (A := cycl p m) (algebraMap L (PadicAlgCl p)).injective
    (⟨y * towerDualVec K i, hw⟩ : L)
  change (minpoly (cycl p m) (algebraMap L (PadicAlgCl p) ⟨_, hw⟩)).natDegree ∣ _
  rw [e, ← relDeg_eq_of_le K hm]
  exact minpoly.degree_dvd (IsIntegral.of_finite _ _)
end GroundTheory.PAdicHodge
