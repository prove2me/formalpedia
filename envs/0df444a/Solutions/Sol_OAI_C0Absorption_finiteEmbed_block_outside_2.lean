-- Prove2me | solution 2 for OAI.C0Absorption.finiteEmbed_block_outside
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:40:42.153999+00:00
-- url     : https://prove2.me/submissions/64672ce2-2693-4579-8c8f-b196a331e4cd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Finite.lean:L119-L132
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.finiteEmbed_block_outside. The node keeps its source
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

theorem finiteEmbed_block_outside {N : ℕ} (x : FInput N) (γ : Label)
    (hγ : N < γ.level.1 ∨ N < γ.level.2) : finiteEmbed N x (labelIndex γ)=0 := by
  apply sparseC0_outside
  rintro ⟨a,ha⟩
  cases a with
  | inl i => exact rowIndex_ne_labelIndex i.val γ ha
  | inr δ =>
    have he := congrArg Label.level (labelIndex_injective ha)
    change (δ.1.1.val,δ.1.2.val)=γ.level at he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    have := δ.1.1.isLt
    have := δ.1.2.isLt
    omega

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators ZeroAtInfty

variable {N : ℕ}

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


theorem solution : type_of% @_root_.OAI.C0Absorption.finiteEmbed_block_outside := @_root_.OAI.C0Absorption.finiteEmbed_block_outside
