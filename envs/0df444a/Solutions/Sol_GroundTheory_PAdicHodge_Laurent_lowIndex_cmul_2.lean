-- Prove2me | solution 2 for GroundTheory.PAdicHodge.Laurent.lowIndex_cmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:19.273916+00:00
-- url     : https://prove2.me/submissions/0186b357-8a18-4d21-b3f3-8d21871ffecd

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_le_gaussNorm
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_pos
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_mem
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_lowIndex_le
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_weight_lt_of_lt_lowIndex
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_weight_lt
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_weight_eq
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_cmul
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_cmul_ne_zero
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
theorem _root_.solution : lowIndex (cmul a b) ρ = lowIndex a ρ + lowIndex b ρ := by
  have hc := ha.cmul hρ hb
  have hc0 := cmul_ne_zero hρ ha hb ha0 hb0
  have hmem : lowIndex a ρ + lowIndex b ρ ∈ domSet (cmul a b) ρ := by
    simp only [domSet, Set.mem_setOf_eq, gaussNorm_cmul hρ ha hb ha0 hb0]
    exact (low_facts hρ ha hb ha0 hb0).1
  refine le_antisymm (lowIndex_le hρ hc hc0 hmem) (not_lt.1 fun hlt => ?_)
  have h1 := (low_facts hρ ha hb ha0 hb0).2 _ hlt
  have h2 := lowIndex_mem hρ hc hc0
  simp only [domSet, Set.mem_setOf_eq, gaussNorm_cmul hρ ha hb ha0 hb0] at h2
  linarith
end GroundTheory.PAdicHodge.Laurent
