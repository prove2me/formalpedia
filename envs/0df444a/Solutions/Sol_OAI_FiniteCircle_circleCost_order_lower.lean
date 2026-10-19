-- Prove2me | solution 1 for OAI.FiniteCircle.circleCost_order_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T14:37:45.646711+00:00
-- url     : https://prove2.me/submissions/91d3a07c-b94c-4fb8-be06-79821ceffd80

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/PhaseCost.lean:L45-L61
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.circleCost_order_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost

-- ---- from OAI.Combinatorics.FiniteCircle.PhaseCost ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem circleCost_order_lower {M q : ℕ} [NeZero M] {x : ZMod M}
    (hq : 0 < q) (hx : x ≠ 0) (hqx : q • x = 0) : 1 ≤ (q : ℝ)*circleCost x := by
  have he : (((q : ℤ)*x.valMinAbs : ℤ) : ZMod M) = 0 := by
    simpa [nsmul_eq_mul] using hqx
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
  have hd' : M ∣ q*x.valMinAbs.natAbs := by
    have hh := Int.natAbs_dvd_natAbs.mpr hd
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using hh
  have ha : 0 < x.valMinAbs.natAbs := by
    apply Nat.pos_of_ne_zero
    intro he
    exact hx ((ZMod.valMinAbs_eq_zero x).mp (Int.natAbs_eq_zero.mp he))
  have hm := Nat.le_of_dvd (Nat.mul_pos hq ha) hd'
  unfold circleCost
  rw [← mul_div_assoc, le_div_iff₀ (by exact_mod_cast NeZero.pos M)]
  simp only [one_mul]
  exact_mod_cast hm

namespace PhaseCost
variable {G H J : Type*} [AddCommGroup G] [AddCommGroup H] [Fintype H] [Fintype J]

end PhaseCost

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List


theorem solution : type_of% @_root_.OAI.FiniteCircle.circleCost_order_lower := @_root_.OAI.FiniteCircle.circleCost_order_lower
