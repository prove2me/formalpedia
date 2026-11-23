-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_pow_sub_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:53.633404+00:00
-- url     : https://prove2.me/submissions/3fd8d688-f9d2-4903-aa10-cb0613181770

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
omit hp
namespace GroundTheory.PAdicHodge
theorem _root_.solution {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul, norm_pow, norm_pow]
  exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ha) (pow_nonneg (norm_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) hb)
end GroundTheory.PAdicHodge
