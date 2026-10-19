-- Prove2me | solution 2 for OAI.C0Absorption.bounded_product_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:03:29.219187+00:00
-- url     : https://prove2.me/submissions/40053490-a88c-4d31-ac71-db936468c8cb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Tests.lean:L186-L201
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.bounded_product_lipschitz. The node keeps its source
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

-- ---- from OAI.Analysis.C0Absorption.Tests ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace CylinderOperation
variable {I : Finset ℕ}
end CylinderOperation

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

namespace TailOperation

end TailOperation

theorem bounded_product_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L A B : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfB : ∀ x, |f x| ≤ A) (hgB : ∀ x, |g x| ≤ B) :
    LipschitzWith (A*L+B*K) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have he : f x*g x-f y*g y = f x*(g x-g y)+g y*(f x-f y) := by ring
  rw [he]
  calc
    _ ≤ |f x*(g x-g y)|+|g y*(f x-f y)| := abs_add_le _ _
    _ = |f x| * |g x-g y|+|g y| * |f x-f y| := by rw [abs_mul, abs_mul]
    _ ≤ A*(L*dist x y)+B*(K*dist x y) := add_le_add
      (mul_le_mul (hfB x) (hg.dist_le_mul x y) (abs_nonneg _) A.coe_nonneg)
      (mul_le_mul (hgB y) (hf.dist_le_mul x y) (abs_nonneg _) B.coe_nonneg)
    _ = _ := by push_cast; ring

namespace GeneratedRepresentation
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}

end GeneratedRepresentation

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.bounded_product_lipschitz := @_root_.OAI.C0Absorption.bounded_product_lipschitz
