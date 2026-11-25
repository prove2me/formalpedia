-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_norm_mem_Ioc_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:11.294507+00:00
-- url     : https://prove2.me/submissions/a2382050-b7c6-489b-94de-80ade5b43f9b

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltMap
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra

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
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
omit [IsUltrametricDist K]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (hnd : ∀ r : ℝ, r < 1 → ∃ x : K, r < ‖x‖ ∧ ‖x‖ < 1)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) : ∃ x : K, a < ‖x‖ ∧ ‖x‖ ≤ b := by
  have hb : 0 < b := ha.trans hab
  obtain ⟨z, hz1, hz2⟩ := hnd (a / b) ((div_lt_one hb).2 hab)
  have hz0 : 0 < ‖z‖ := (div_pos ha hb).trans hz1
  obtain ⟨y, hy⟩ := NormedField.exists_lt_norm K b
  have hex : ∃ m : ℕ, ‖y * z ^ m‖ ≤ b := by
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hb (hb.trans hy)) hz2
    refine ⟨m, ?_⟩
    rw [norm_mul, norm_pow]
    have hy0 : 0 < ‖y‖ := hb.trans hy
    calc ‖y‖ * ‖z‖ ^ m ≤ ‖y‖ * (b / ‖y‖) := by gcongr
      _ = b := by field_simp
  classical
  set m := Nat.find hex with hmdef
  have hm : ‖y * z ^ m‖ ≤ b := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, pow_zero, mul_one] at hm
    exact (lt_irrefl _) (hy.trans_le hm)
  have hprev : b < ‖y * z ^ (m - 1)‖ := by
    have := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
    exact not_le.1 this
  refine ⟨y * z ^ m, ?_, hm⟩
  have e : m = m - 1 + 1 := by omega
  rw [e, pow_succ, ← mul_assoc, norm_mul]
  calc a = b * (a / b) := by field_simp
    _ < ‖y * z ^ (m - 1)‖ * ‖z‖ := by
      apply mul_lt_mul hprev hz1.le (div_pos ha hb) (norm_nonneg _)
end GroundTheory.PAdicHodge
