-- Prove2me | solution 2 for OAI.C0Absorption.finiteInverse_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:42:16.316575+00:00
-- url     : https://prove2.me/submissions/dc752341-417e-4475-9963-47ae4d1d9409

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Finite.lean:L232-L245
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.finiteInverse_bound. The node keeps its source
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

theorem finiteNext_bound (W : FrozenWeights) (l : FLevel N) (y : FInput N) : |finiteNext W l y|≤2*‖y‖ := by
  unfold finiteNext
  split_ifs
  · exact finiteRow_bound W _ y
  · exact (norm_le_pi_norm y (.inl l.1)).trans (by nlinarith [norm_nonneg y])

theorem finiteInverse_bound (W : FrozenWeights) (y : FInput N) : ‖finiteInverseFunction W y‖≤5*‖y‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg y))).mpr
  rintro (i|⟨l,b⟩)
  · exact (finiteRow_bound W _ y).trans (by nlinarith [norm_nonneg y])
  · change |y (.inr ⟨l,b⟩)-W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y)|≤_
    apply (abs_sub _ _).trans
    have hp : |W.vector (l.1.val,l.2.val) b*(finiteRow W l y-finiteNext W l y)|≤4*‖y‖ := by
      rw [abs_mul]
      calc
        _ ≤ 1*(|finiteRow W l y|+|finiteNext W l y|) :=
          mul_le_mul (W.vector_bound _ _) (abs_sub _ _) (abs_nonneg _) zero_le_one
        _ ≤ 4*‖y‖ := by linarith [finiteRow_bound W l y,finiteNext_bound W l y]
    have hy : |y (.inr ⟨l,b⟩)|≤‖y‖ := norm_le_pi_norm y _
    linarith

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


theorem solution : type_of% @_root_.OAI.C0Absorption.finiteInverse_bound := @_root_.OAI.C0Absorption.finiteInverse_bound
