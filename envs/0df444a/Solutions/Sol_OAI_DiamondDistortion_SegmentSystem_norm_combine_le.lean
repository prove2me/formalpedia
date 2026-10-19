-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.norm_combine_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:21:57.013077+00:00
-- url     : https://prove2.me/submissions/4d381cfa-1e5c-479f-b380-b600b1233466

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean:L501-L525
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.norm_combine_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_test_energy_le_allow_empty

-- ---- from OAI.Analysis.DiamondDistortion.SegmentNorm ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι : Type*} (T : SegmentSystem ι)

variable {T}

variable (T)

/-- Cauchy--Schwarz for represented disjoint segment coefficients, with empty
    pieces permitted after a projection. -/
lemma norm_combine_le {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a : κ → ℝ)
    (hS : ∀ i, (S i).Nonempty → T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ‖T.combine S a‖ ≤ Real.sqrt (∑ i, (a i) ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [combine_coe, Real.norm_eq_abs, UniformSpace.Completion.norm_coe, norm_eq_primal]
    have htest : Real.sqrt (∑ i, (∑ v ∈ S i, T.ofPrimal u v) ^ 2) ≤
        T.primalSeminorm (T.ofPrimal u) := by
      exact (Real.sqrt_le_left (apply_nonneg _ _)).mpr
        (T.test_energy_le_allow_empty S hS hd (T.ofPrimal u))
    calc
      |∑ i, a i * (∑ v ∈ S i, T.ofPrimal u v)| ≤
          ∑ i, |a i * (∑ v ∈ S i, T.ofPrimal u v)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |a i| * |∑ v ∈ S i, T.ofPrimal u v| := by simp only [abs_mul]
      _ ≤ Real.sqrt (∑ i, (a i) ^ 2) *
          Real.sqrt (∑ i, (∑ v ∈ S i, T.ofPrimal u v) ^ 2) := by
        simpa only [sq_abs] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
          (fun i => |a i|) (fun i => |∑ v ∈ S i, T.ofPrimal u v|)
      _ ≤ _ := mul_le_mul_of_nonneg_left htest (Real.sqrt_nonneg _)

variable {T}

variable (T)

end SegmentSystem

end DiamondDistortion

end

end OAI

-- ---- platform node ----
open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
open scoped BigOperators Classical Topology
open Set


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.norm_combine_le := @_root_.OAI.DiamondDistortion.SegmentSystem.norm_combine_le
