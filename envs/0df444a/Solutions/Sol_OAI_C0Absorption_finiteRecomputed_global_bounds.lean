-- Prove2me | solution 1 for OAI.C0Absorption.finiteRecomputed_global_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:47:20.934768+00:00
-- url     : https://prove2.me/submissions/b7858389-6d96-4926-b8e0-ef6154b7fa92

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/FiniteShift.lean:L64-L77
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.finiteRecomputed_global_bounds. The node keeps its source
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
import Definitions.Def_OAI_Analysis_C0Absorption_Space
import Definitions.Def_OAI_Analysis_C0Absorption_Finite
import Definitions.Def_OAI_Analysis_C0Absorption_FiniteShift
import Theorems.Thm_OAI_C0Absorption_finiteInverse_bound
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

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.Finite ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

section Sparse
variable {A : Type*} [Fintype A]

end Sparse

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

theorem finiteFrozen_lower (W : FrozenWeights) (x : FInput N) : ‖x‖≤5*‖finiteFrozen N W x‖ := by
  simpa only [finiteInverse_frozen] using finiteInverse_bound W (finiteFrozen N W x)

end
end C0Absorption

end OAI

-- ---- from OAI.Analysis.C0Absorption.FiniteShift ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

theorem finiteFrozen_weight_error {W V : FrozenWeights} {x : FInput N} {q : ℝ}
    (hq : 0≤q) (h : WeightError W V (finiteEmbed N x) q) :
    ‖finiteFrozen N W x-finiteFrozen N V x‖≤6*q := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hq)).mpr
  rintro (i|γ)
  · change |finiteRow W (i,Fin.last N) x-finiteRow V (i,Fin.last N) x|≤_
    rw [finiteRow_eq,finiteRow_eq]
    exact (rowScalar_weight_error W V _ _ (h.row _)).trans (by linarith)
  · change |finiteFrozenFunction W x (.inr γ)-finiteFrozenFunction V x (.inr γ)|≤_
    rw [finiteFrozen_block,finiteFrozen_block]
    exact (cfun_norm_apply_le (frozenShift W (finiteEmbed N x)-frozenShift V (finiteEmbed N x)) (fLabel γ)).trans
      (shift_weight_error hq h)

theorem finiteRecomputed_mixed_left (x y : FInput N) :
    ‖finiteRecomputed N x-finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) x‖≤12*eta*dist x y := by
  have hh := finiteFrozen_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg)
    (normalized_error_left (finiteEmbed N x) (finiteEmbed N y))
  rw [LinearIsometry.dist_map] at hh
  exact hh.trans (by apply le_of_eq; ring)

theorem finiteRecomputed_mixed_right (x y : FInput N) :
    ‖finiteRecomputed N y-finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) y‖≤12*eta*dist x y := by
  have hh := finiteFrozen_weight_error (mul_nonneg (mul_nonneg (by norm_num) eta_pos.le) dist_nonneg)
    (normalized_error_right (finiteEmbed N x) (finiteEmbed N y))
  rw [LinearIsometry.dist_map] at hh
  exact hh.trans (by apply le_of_eq; ring)

theorem finiteRecomputed_mixed_approx (x y : FInput N) :
    ‖finiteRecomputed N x-finiteRecomputed N y-
      finiteFrozen N (mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))) (x-y)‖≤24*eta*dist x y := by
  let W := mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))
  have he : finiteRecomputed N x-finiteRecomputed N y-finiteFrozen N W (x-y)=
      (finiteRecomputed N x-finiteFrozen N W x)-(finiteRecomputed N y-finiteFrozen N W y) := by rw [map_sub]; abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith [finiteRecomputed_mixed_left x y,finiteRecomputed_mixed_right x y])

theorem fiveBounds_of_error {E : Type*} [NormedAddCommGroup E] {a b : E} {d e : ℝ}
    (he : ‖a-b‖≤e*d) (hU : ‖b‖≤5*d) (hL : d≤5*‖b‖) :
    (1/5-e)*d≤‖a‖ ∧ ‖a‖≤(5+e)*d := by
  have hu : ‖a‖≤‖a-b‖+‖b‖ := by simpa only [sub_add_cancel] using norm_add_le (a-b) b
  have hl : ‖b‖≤‖a-b‖+‖a‖ := by simpa only [sub_add_cancel,norm_sub_rev] using norm_add_le (b-a) a
  constructor <;> nlinarith

theorem finiteRecomputed_global_bounds (x y : FInput N) :
    (1/5-24*eta)*dist x y≤dist (finiteRecomputed N x) (finiteRecomputed N y) ∧
    dist (finiteRecomputed N x) (finiteRecomputed N y)≤(5+24*eta)*dist x y := by
  let W := mixedWeights (normalizedBall (finiteEmbed N x)) (normalizedBall (finiteEmbed N y))
  let a := finiteRecomputed N x-finiteRecomputed N y
  let b := finiteFrozen N W (x-y)
  have he : ‖a-b‖≤24*eta*dist x y := finiteRecomputed_mixed_approx x y
  have hU : ‖b‖≤5*dist x y := by
    change ‖finiteFrozenFunction W (x-y)‖≤5*dist x y
    rw [dist_eq_norm]
    exact finiteFrozen_bound W (x-y)
  have hL : dist x y≤5*‖b‖ := by simpa only [dist_eq_norm] using finiteFrozen_lower W (x-y)
  rw [dist_eq_norm (finiteRecomputed N x) (finiteRecomputed N y)]
  exact fiveBounds_of_error he hU hL

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators

section FiniteOperators
variable {A : Type*} [Fintype A] [DecidableEq A] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end FiniteOperators

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


theorem solution : type_of% @_root_.OAI.C0Absorption.finiteRecomputed_global_bounds := @_root_.OAI.C0Absorption.finiteRecomputed_global_bounds
