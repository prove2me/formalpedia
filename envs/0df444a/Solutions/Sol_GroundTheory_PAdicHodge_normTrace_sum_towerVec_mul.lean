-- Prove2me | solution 1 for GroundTheory.PAdicHodge.normTrace_sum_towerVec_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:10.349558+00:00
-- url     : https://prove2.me/submissions/68444412-dd27-4d2e-800f-eb8db6e948f2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cycl_eq_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_towerVec_mem
import Theorems.Thm_GroundTheory_PAdicHodge_towerDualVec_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_towerVec_mul
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mul_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sum
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
theorem _root_.solution {m : ℕ} (hm : stableIndex K ≤ m)
    (c : Fin (relDeg K (stableIndex K)) → PadicAlgCl p) (hc : ∀ i, c i ∈ cycl p m)
    (j : Fin (relDeg K (stableIndex K))) :
    normTrace (cycl p m) ((∑ i, c i * towerVec K i) * towerDualVec K j) =
      c j / (relDeg K (stableIndex K) : PadicAlgCl p) := by
  rw [Finset.sum_mul, normTrace_sum]
  have : ∀ i ∈ (Finset.univ : Finset (Fin (relDeg K (stableIndex K)))),
      normTrace (cycl p m) (c i * towerVec K i * towerDualVec K j) =
        c i * (if i = j then ((relDeg K (stableIndex K) : PadicAlgCl p))⁻¹ else 0) := by
    intro i _
    rw [mul_assoc, normTrace_mul_of_mem _ (hc i),
      normTrace_cycl_eq_of_mem K le_rfl hm (mul_mem (towerVec_mem K i) (towerDualVec_mem K j)),
      normTrace_towerVec_mul]
  rw [Finset.sum_congr rfl this]
  simp [div_eq_mul_inv]
end GroundTheory.PAdicHodge
