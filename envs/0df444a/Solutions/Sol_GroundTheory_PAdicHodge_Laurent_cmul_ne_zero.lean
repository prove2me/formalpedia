-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.cmul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:57.554707+00:00
-- url     : https://prove2.me/submissions/85bfac6c-f4fb-4d4c-a242-59927be6e1ba

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_pos
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_mem
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_weight_lt_of_lt_lowIndex
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_weight_lt
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_weight_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open Filter Topology
namespace Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
section Basic
end Basic
section Product
variable [CompleteSpace K]
end Product
section Dominant
section Attained
variable (hρ : 0 < ρ) (h : ConvergesAt a ρ) (ha : a ≠ 0)
include hρ h ha
end Attained
section Multiplicative
variable [CompleteSpace K]
private theorem prod_lt_left {x y X Y : ℝ} (hx0 : 0 ≤ x) (hx : x < X) (hy : y ≤ Y) (hY : 0 < Y) :
    x * y < X * Y :=
  calc x * y ≤ x * Y := mul_le_mul_of_nonneg_left hy hx0
    _ < X * Y := mul_lt_mul_of_pos_right hx hY
private theorem prod_lt_right {x y X Y : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ X) (hX : 0 < X) (hy0 : 0 ≤ y)
    (hy : y < Y) :
    x * y < X * Y := by
  rw [mul_comm x, mul_comm X]
  calc y * x ≤ y * X := mul_le_mul_of_nonneg_left hx (by linarith [hy0])
    _ < Y * X := mul_lt_mul_of_pos_right hy hX
variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0
private theorem low_facts :
    ‖cmul a b (lowIndex a ρ + lowIndex b ρ)‖ * ρ ^ (lowIndex a ρ + lowIndex b ρ) =
      gaussNorm a ρ * gaussNorm b ρ ∧
    ∀ n < lowIndex a ρ + lowIndex b ρ, ‖cmul a b n‖ * ρ ^ n < gaussNorm a ρ * gaussNorm b ρ := by
  have hA := gaussNorm_pos hρ ha ha0
  have hB := gaussNorm_pos hρ hb hb0
  have hM := mul_pos hA hB
  set i₀ := lowIndex a ρ
  set j₀ := lowIndex b ρ
  have wa : ∀ i, 0 ≤ ‖a i‖ * ρ ^ i := fun i => by positivity
  have wb : ∀ i, 0 ≤ ‖b i‖ * ρ ^ i := fun i => by positivity
  refine ⟨cmul_weight_eq (i₀ := i₀) hρ ha hb hM ?_ fun i hi => ?_, fun n hn =>
    cmul_weight_lt hρ ha hb hM fun i => ?_⟩
  · rw [show i₀ + j₀ - i₀ = j₀ by ring,
      show ‖a i₀‖ * ρ ^ i₀ = gaussNorm a ρ from lowIndex_mem hρ ha ha0,
      show ‖b j₀‖ * ρ ^ j₀ = gaussNorm b ρ from lowIndex_mem hρ hb hb0]
  · rcases lt_or_gt_of_ne hi with hi | hi
    · exact prod_lt_left (wa _) (weight_lt_of_lt_lowIndex hρ ha ha0 hi) (hb.le_gaussNorm _) hB
    · exact prod_lt_right (wa _) (ha.le_gaussNorm _) hA (wb _)
        (weight_lt_of_lt_lowIndex hρ hb hb0 (by omega))
  · rcases lt_or_ge i i₀ with hi | hi
    · exact prod_lt_left (wa _) (weight_lt_of_lt_lowIndex hρ ha ha0 hi) (hb.le_gaussNorm _) hB
    · exact prod_lt_right (wa _) (ha.le_gaussNorm _) hA (wb _)
        (weight_lt_of_lt_lowIndex hρ hb hb0 (by omega))
end Multiplicative
end Dominant
end Laurent
end GroundTheory.PAdicHodge
end
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
variable [CompleteSpace K]
variable (hρ : 0 < ρ) (ha : ConvergesAt a ρ) (hb : ConvergesAt b ρ) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
include hρ ha hb ha0 hb0
namespace GroundTheory.PAdicHodge.Laurent
theorem _root_.solution : cmul a b ≠ 0 := by
  intro h0
  have h1 := (low_facts hρ ha hb ha0 hb0).1
  rw [h0] at h1
  have := mul_pos (gaussNorm_pos hρ ha ha0) (gaussNorm_pos hρ hb hb0)
  simp only [Pi.zero_apply, norm_zero, zero_mul] at h1
  linarith
end GroundTheory.PAdicHodge.Laurent
