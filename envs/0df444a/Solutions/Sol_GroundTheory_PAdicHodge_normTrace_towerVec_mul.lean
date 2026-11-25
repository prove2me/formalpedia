-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_towerVec_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:01.934239+00:00
-- url     : https://prove2.me/submissions/0a66cd14-99d9-46a5-be53-e2e65f1edac9

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
variable [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (i j : Fin (relDeg K (stableIndex K))) :
    normTrace (cycl p (stableIndex K)) (towerVec K i * towerDualVec K j) =
      if i = j then ((relDeg K (stableIndex K) : PadicAlgCl p))⁻¹ else 0 := by
  have e := normTraceF_eq_trace_div (cycl p (stableIndex K)) (Ω := PadicAlgCl p)
    (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K))) (traceBasis K i * traceDualBasis K j)
  have ht : Algebra.trace (cycl p (stableIndex K)) (extendScalars (cycl_le_cyclotomicLayer K (stableIndex K)))
      (traceBasis K i * traceDualBasis K j) = if i = j then 1 else 0 := by
    rw [mul_comm, ← Algebra.traceForm_apply, traceDualBasis,
      LinearMap.BilinForm.apply_dualBasis_left]
  rw [ht] at e
  rw [normTrace]
  change algebraMap _ _ (normTraceF _ (algebraMap (extendScalars (cycl_le_cyclotomicLayer K
    (stableIndex K))) (PadicAlgCl p) (traceBasis K i * traceDualBasis K j))) = _
  rw [e]
  split_ifs <;> simp [relDeg]
end GroundTheory.PAdicHodge
