-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_nextCoeff_minpoly_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:32.278303+00:00
-- url     : https://prove2.me/submissions/39bfec3c-ad14-4db9-ab7f-0bb5a7f93a5e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_norm_eq_of_aeval_minpoly_eq_zero
import Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_sum_le_of_forall_le_of_nonneg

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
open Polynomial Module IntermediateField
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (F : Type*) [Field F] [Algebra ℚ_[p] F] [Algebra F (PadicAlgCl p)]
    [IsScalarTower ℚ_[p] F (PadicAlgCl p)] (y : PadicAlgCl p) :
    ‖algebraMap F (PadicAlgCl p) (minpoly F y).nextCoeff‖ ≤ ‖y‖ := by
  have hy : IsIntegral F y := (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) y).tower_top
  have hm : ((minpoly F y).map (algebraMap F (PadicAlgCl p))).Monic := (minpoly.monic hy).map _
  rw [← nextCoeff_map (algebraMap F (PadicAlgCl p)).injective,
    (IsAlgClosed.splits _).nextCoeff_eq_neg_sum_roots_of_monic hm, norm_neg]
  refine norm_multiset_sum_le_of_forall_le_of_nonneg _ (norm_nonneg y) fun r hr => le_of_eq ?_
  apply norm_eq_of_aeval_minpoly_eq_zero
  have h1 : aeval r (minpoly F y) = 0 := by
    rw [mem_roots hm.ne_zero, IsRoot, eval_map, ← aeval_def] at hr
    exact hr
  have h2 := minpoly.dvd_map_of_isScalarTower ℚ_[p] F y
  have := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero h2 h1
  rwa [aeval_map_algebraMap] at this
end GroundTheory.PAdicHodge
