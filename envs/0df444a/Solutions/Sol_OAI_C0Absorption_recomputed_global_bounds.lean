-- Prove2me | solution 1 for OAI.C0Absorption.recomputed_global_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:38:58.222448+00:00
-- url     : https://prove2.me/submissions/581cf8d6-8244-41c1-a13b-ba4989c8c608

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Shift.lean:L290-L303
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.recomputed_global_bounds. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles
import Definitions.Def_OAI_Analysis_C0Absorption_Blocks
import Definitions.Def_OAI_Analysis_C0Absorption_Correction
import Definitions.Def_OAI_Analysis_C0Absorption_Frozen
import Definitions.Def_OAI_Analysis_C0Absorption_Tags
import Definitions.Def_OAI_Analysis_C0Absorption_Operators
import Definitions.Def_OAI_Analysis_C0Absorption_Shift
import Theorems.Thm_OAI_C0Absorption_normalization_bound

-- ---- from OAI.Analysis.C0Absorption.Blocks ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem finiteRadius_smul (I : Finset ℕ) (a : ℝ) (s : C0) :
    finiteRadius I (a • s)=|a| * finiteRadius I s := by
  simp only [finiteRadius,map_smul,norm_smul,Real.norm_eq_abs]

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Shift ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem outputScalar_bound (W : FrozenWeights) (lev : Level) (y : BlockC0) :
    |outputScalar W lev y|≤2*‖y‖ := by
  rw [outputScalar_apply]
  exact (abs_finite_dot_le _ _ (fun b => cfun_norm_apply_le y (blockLabel lev b))).trans
    (mul_le_mul_of_nonneg_right (W.row_bound lev) (norm_nonneg y))

theorem frozenInverse_bound (W : FrozenWeights) (y : BlockC0) : ‖frozenInverse W y‖≤5*‖y‖ := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg y))
  intro k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i =>
    have hb := outputScalar_bound W (i,0) y
    change |frozenInverse W y (rowIndex i)|≤_
    rw [frozenInverse_row]
    nlinarith [norm_nonneg y]
  | inr γ =>
    change |frozenInverse W y (labelIndex γ)|≤_
    rw [frozenInverse_block,inverseBlockFunction]
    apply (abs_sub _ _).trans
    have hp : |W.vector γ.level ⟨γ.band,γ.tag⟩*(outputScalar W γ.level y-outputScalar W (levelSuccessor γ.level) y)|≤4*‖y‖ := by
      rw [abs_mul]
      calc
        _ ≤ 1*(|outputScalar W γ.level y|+|outputScalar W (levelSuccessor γ.level) y|) :=
          mul_le_mul (W.vector_bound _ _) (abs_sub _ _) (abs_nonneg _) zero_le_one
        _ ≤ 4*‖y‖ := by linarith [outputScalar_bound W γ.level y,outputScalar_bound W (levelSuccessor γ.level) y]
    linarith [cfun_norm_apply_le y γ]

theorem outputScalar_frozenShift (W : FrozenWeights) (lev : Level) (x : C0) :
    outputScalar W lev (frozenShift W x)=previousScalar W lev x := by
  rw [outputScalar_apply]
  simp only [frozenShift_apply,frozenCorrection_apply,blockLabel]
  rw [finite_row_shift _ _ _ (W.pairing lev)]
  rw [rowScalar_apply W lev x]
  simp only [blockInput,blockLabel]
  ring

theorem frozenInverse_frozenShift (W : FrozenWeights) (x : C0) : frozenInverse W (frozenShift W x)=x := by
  ext k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i =>
    change frozenInverse W (frozenShift W x) (rowIndex i)=_
    rw [frozenInverse_row,outputScalar_frozenShift]
    rfl
  | inr γ =>
    change frozenInverse W (frozenShift W x) (labelIndex γ)=_
    rw [frozenInverse_block,inverseBlockFunction,frozenShift_apply,outputScalar_frozenShift,outputScalar_frozenShift,frozenCorrection_apply]
    have he : previousScalar W (levelSuccessor γ.level)=rowScalar W γ.level := by
      rcases γ.level with ⟨i,n⟩
      rfl
    rw [he]
    change x (labelIndex γ)+_ - _=x (labelIndex γ)
    ring

theorem frozenShift_lower (W : FrozenWeights) (x : C0) : ‖x‖≤5*‖frozenShift W x‖ := by
  simpa only [frozenInverse_frozenShift] using frozenInverse_bound W (frozenShift W x)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

theorem WeightError.smul {W V : FrozenWeights} {x : C0} {q : ℝ} (h : WeightError W V x q) (a : ℝ) :
    WeightError W V (a • x) (|a| *q) := by
  constructor
  · intro lev b
    change finiteRadius _ (a • x)*_≤_
    rw [finiteRadius_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.vector lev b) (abs_nonneg a)
  · intro lev
    change finiteRadius _ (a • x)*_≤_
    rw [finiteRadius_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.row lev) (abs_nonneg a)

theorem WeightError.mono {W V : FrozenWeights} {x : C0} {q r : ℝ} (h : WeightError W V x q) (hr : q≤r) :
    WeightError W V x r := ⟨fun lev b => (h.vector lev b).trans hr,fun lev => (h.row lev).trans hr⟩

theorem normalized_error_left (x y : C0) : WeightError (stateWeights (normalizedBall x))
    (mixedWeights (normalizedBall x) (normalizedBall y)) x (2*eta*dist x y) := by
  have hh := (mixed_left_error (normalizedBall x) (normalizedBall y)).smul ‖x‖
  simp only [normalizedBall,Subtype.coe_mk,norm_smul_normalize,abs_of_nonneg (norm_nonneg x)] at hh
  apply hh.mono
  calc
    _ = eta*(‖x‖ * dist (normalize x) (normalize y)) := by rw [Subtype.dist_eq]; ring
    _ ≤ eta*(2*dist x y) := mul_le_mul_of_nonneg_left (normalization_bound x y) eta_pos.le
    _ = _ := by ring

theorem normalized_error_right (x y : C0) : WeightError (stateWeights (normalizedBall y))
    (mixedWeights (normalizedBall x) (normalizedBall y)) y (2*eta*dist x y) := by
  have hh := (mixed_right_error (normalizedBall x) (normalizedBall y)).smul ‖y‖
  simp only [normalizedBall,Subtype.coe_mk,norm_smul_normalize,abs_of_nonneg (norm_nonneg y)] at hh
  apply hh.mono
  calc
    _ = eta*(‖y‖ * dist (normalize y) (normalize x)) := by rw [Subtype.dist_eq,dist_comm]; ring
    _ ≤ eta*(2*dist y x) := mul_le_mul_of_nonneg_left (normalization_bound y x) eta_pos.le
    _ = _ := by rw [dist_comm]; ring

theorem shift_weight_error {W V : FrozenWeights} {x : C0} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V x q) : ‖frozenShift W x-frozenShift V x‖≤6*q := by
  apply cfun_norm_le _ (mul_nonneg (by norm_num) hq)
  intro γ
  change |frozenShift W x γ-frozenShift V x γ|≤_
  rw [frozenShift_apply,frozenShift_apply,add_sub_add_left_eq_sub]
  exact correction_weight_error hq h γ

theorem recomputed_mixed_left (x y : C0) :
    ‖recomputedShift x-frozenShift (mixedWeights (normalizedBall x) (normalizedBall y)) x‖≤12*eta*dist x y := by
  have hh := shift_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg) (normalized_error_left x y)
  exact hh.trans (by apply le_of_eq; ring)

theorem recomputed_mixed_right (x y : C0) :
    ‖recomputedShift y-frozenShift (mixedWeights (normalizedBall x) (normalizedBall y)) y‖≤12*eta*dist x y := by
  have hh := shift_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg) (normalized_error_right x y)
  exact hh.trans (by apply le_of_eq; ring)

theorem recomputed_mixed_approx (x y : C0) :
    ‖recomputedShift x-recomputedShift y-frozenShift (mixedWeights (normalizedBall x) (normalizedBall y)) (x-y)‖≤24*eta*dist x y := by
  let W := mixedWeights (normalizedBall x) (normalizedBall y)
  have he : recomputedShift x-recomputedShift y-frozenShift W (x-y)=
      (recomputedShift x-frozenShift W x)-(recomputedShift y-frozenShift W y) := by rw [map_sub]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [recomputed_mixed_left x y,recomputed_mixed_right x y])

theorem recomputed_global_bounds (x y : C0) :
    (1/5-24*eta)*dist x y≤dist (recomputedShift x) (recomputedShift y) ∧
    dist (recomputedShift x) (recomputedShift y)≤(5+24*eta)*dist x y := by
  let W := mixedWeights (normalizedBall x) (normalizedBall y)
  let a := recomputedShift x-recomputedShift y
  let b := frozenShift W (x-y)
  have he : ‖a-b‖≤24*eta*dist x y := recomputed_mixed_approx x y
  have hU : ‖b‖≤5*dist x y := by simpa only [dist_eq_norm] using frozenShift_bound W (x-y)
  have hL : dist x y≤5*‖b‖ := by simpa only [dist_eq_norm] using frozenShift_lower W (x-y)
  have hu : ‖a‖≤‖a-b‖+‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a-b) b
  have hl : ‖b‖≤‖a-b‖+‖a‖ := by simpa only [sub_add_cancel,norm_sub_rev] using norm_add_le (b-a) a
  rw [dist_eq_norm (recomputedShift x) (recomputedShift y)]
  change (1/5-24*eta)*dist x y≤‖a‖ ∧ ‖a‖≤(5+24*eta)*dist x y
  constructor <;> nlinarith

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.recomputed_global_bounds := @_root_.OAI.C0Absorption.recomputed_global_bounds
