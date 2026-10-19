-- Prove2me | solution 1 for OAI.DiamondDistortion.SegmentSystem.norm_cone_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:23:21.49039+00:00
-- url     : https://prove2.me/submissions/08e49038-5eb8-4188-8cec-d50298d86ff1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean:L527-L581
-- (upload_full_project.md Phase 4): solution for node OAI.DiamondDistortion.SegmentSystem.norm_cone_mean_le. The node keeps its source
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

/-- A finite family of disjoint cones can be tested by independently maximizing
    each cone's represented segment. This is the finite dual reconstruction bound. -/
lemma norm_cone_mean_le {Ω κ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype κ]
    (S : Ω → κ → Finset ι) (a : Ω → κ → ℝ) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hS : ∀ ω g, (S ω g).Nonempty → T.IsSegment (S ω g))
    (hd : ∀ g h, g ≠ h → ∀ ω ν, Disjoint (S ω g) (S ν h)) :
    ‖∑ ω, w ω • T.combine (S ω) (a ω)‖ ≤
      Real.sqrt (∑ g, (∑ ω, w ω * |a ω g|) ^ 2) := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  induction u using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih u =>
    rw [sum_apply]
    simp only [smul_apply, smul_eq_mul, combine_coe, Real.norm_eq_abs,
      UniformSpace.Completion.norm_coe, norm_eq_primal]
    choose idx hidx hmax using fun g : κ => Finset.exists_max_image Finset.univ
      (fun ω => |∑ v ∈ S ω g, T.ofPrimal u v|) Finset.univ_nonempty
    let t : κ → ℝ := fun g => |∑ v ∈ S (idx g) g, T.ofPrimal u v|
    have ht (ω : Ω) (g : κ) : |∑ v ∈ S ω g, T.ofPrimal u v| ≤ t g :=
      hmax g ω (Finset.mem_univ _)
    have htest : Real.sqrt (∑ g, t g ^ 2) ≤ T.primalSeminorm (T.ofPrimal u) := by
      apply (Real.sqrt_le_left (apply_nonneg _ _)).2
      simpa only [t, sq_abs] using T.test_energy_le_allow_empty
        (fun g => S (idx g) g) (fun g => hS (idx g) g)
        (fun {g h} hgh => hd g h hgh (idx g) (idx h)) (T.ofPrimal u)
    calc
      |∑ ω, w ω * ∑ g, a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| ≤
          ∑ ω, |w ω * ∑ g, a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ω, w ω * |∑ g, a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| := by
        simp only [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ ω, w ω * (∑ g, |a ω g| * t g) := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_left _ (hw ω)
        calc
          _ ≤ ∑ g, |a ω g * (∑ v ∈ S ω g, T.ofPrimal u v)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro g _
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (ht ω g) (abs_nonneg _)
      _ = ∑ g, (∑ ω, w ω * |a ω g|) * t g := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro g _
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ ≤ Real.sqrt (∑ g, (∑ ω, w ω * |a ω g|) ^ 2) * Real.sqrt (∑ g, t g ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
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


theorem solution : type_of% @_root_.OAI.DiamondDistortion.SegmentSystem.norm_cone_mean_le := @_root_.OAI.DiamondDistortion.SegmentSystem.norm_cone_mean_le
