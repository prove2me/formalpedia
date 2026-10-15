-- Prove2me | solution 1 for OAI.SquareRootDegree.FiniteMoments.normalized_product_eval
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:07:41.841182+00:00
-- url     : https://prove2.me/submissions/54c8812c-9bbf-4107-a7f6-49528d2369aa

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/FiniteMoments.lean:L20-L35
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.FiniteMoments.normalized_product_eval. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection

-- ---- from OAI.Combinatorics.BooleanFunctions.Blocks ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Disjoint blocks and finite observation degree calculus -/

attribute [local instance] Classical.propDecidable

theorem average_pi_prod {κ α : Type*} [Fintype κ] [Fintype α] (f : κ → α → ℝ) :
    average (fun x : κ → α => ∏ i, f i (x i)) = ∏ i, average (f i) := by
  simp only [average, Fintype.card_fun, Nat.cast_pow, inv_pow, ← Fintype.prod_sum,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.FiniteMoments ----
namespace OAI

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

attribute [local instance] Classical.propDecidable

namespace FiniteMoments
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem normalized_product_eval (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (j : ι) (g : α → ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*g (x j)) = average (fun a => r j a*g a) := by
  have he : (fun x : ι → α => (∏ i, r i (x i))*g (x j)) =
      fun x => ∏ i, (if i = j then r i (x i)*g (x i) else r i (x i)) := by
    funext x
    have hi (i : ι) : (if i = j then r i (x i)*g (x i) else r i (x i)) =
        r i (x i)*(if i = j then g (x i) else 1) := by split_ifs <;> simp
    simp_rw [hi]
    rw [Finset.prod_mul_distrib]
    simp
  rw [he,average_pi_prod (fun i a => if i = j then r i a*g a else r i a)]
  have hf (i : ι) : average (fun a => if i = j then r i a*g a else r i a) =
      if i = j then average (fun a => r i a*g a) else 1 := by split_ifs <;> simp_all
  simp_rw [hf]
  simp

end FiniteMoments
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.FiniteMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι α : Type*} [Fintype ι] [Fintype α]

theorem solution (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (j : ι) (g : α → ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*g (x j)) = average (fun a => r j a*g a) := by
  first
    | exact OAI.SquareRootDegree.FiniteMoments.normalized_product_eval r hr j g
    | exact OAI.SquareRootDegree.FiniteMoments.normalized_product_eval
    | (apply OAI.SquareRootDegree.FiniteMoments.normalized_product_eval <;> assumption)
    | (intros; apply OAI.SquareRootDegree.FiniteMoments.normalized_product_eval <;> assumption)
