-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_pow_pow_sub_pow_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:33.878394+00:00
-- url     : https://prove2.me/submissions/5074b784-816b-4c95-ae31-be83d3712e1b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
import Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_p_sub_pow_p_le

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
theorem _root_.solution {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hp1 : ‖(p : F)‖ ≤ 1)
    {e : ℕ} (he : 1 ≤ e) (hab : ‖a - b‖ ≤ ‖(p : F)‖ ^ e) (r : ℕ) :
    ‖a ^ p ^ r - b ^ p ^ r‖ ≤ ‖(p : F)‖ ^ (e + r) := by
  induction r with
  | zero => simpa using hab
  | succ r ih =>
    rw [pow_succ, pow_mul, pow_mul, ← add_assoc]
    exact norm_pow_p_sub_pow_p_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb) hp1 (by omega) ih
end GroundTheory.PAdicHodge
