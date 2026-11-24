-- Prove2me | solution 1 for GlobalTheory.OrbitAvg.avg_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:17:32.04301+00:00
-- url     : https://prove2.me/submissions/b2f614ee-0493-4521-b326-12bbd255d9a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAveragingProjection
import Theorems.Thm_GlobalTheory_OrbitAvg_cv_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitAvg
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
  (π : G →* Module.End ℂ V) (L : Subgroup G)
namespace GlobalTheory.OrbitAvg
theorem _root_.solution {x : V} (hx : (stab π L x).FiniteIndex) (l : L) :
    π (l : G) (avg π L x) = avg π L x := by
  classical
  haveI := Fintype.ofFinite (L ⧸ stab π L x)
  unfold avg avgH
  rw [finsum_eq_sum_of_fintype, map_smul, map_sum]
  congr 1
  have h : ∀ q : L ⧸ stab π L x, π (l : G) (cv π L (stab π L x) x q) =
      cv π L (stab π L x) x (l • q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [cv_mk π L le_rfl, MulAction.Quotient.smul_mk, cv_mk π L le_rfl, smul_eq_mul, Subgroup.coe_mul, map_mul,
        Module.End.mul_apply]
  simp_rw [h]
  exact Equiv.sum_comp (MulAction.toPerm l) (cv π L (stab π L x) x)
end GlobalTheory.OrbitAvg
