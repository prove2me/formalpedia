-- Prove2me | solution 1 for OAI.SquareRootDegree.FiniteMoments.normalized_product_shifted_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:17:54.09167+00:00
-- url     : https://prove2.me/submissions/7a8bcbec-7d88-4f58-a66c-887c7332d939

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/FiniteMoments.lean:L89-L113
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.FiniteMoments.normalized_product_shifted_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Theorems.Thm_OAI_SquareRootDegree_FiniteMoments_normalized_product_centered_sq
import Theorems.Thm_OAI_SquareRootDegree_FiniteMoments_normalized_product_eval

-- ---- from OAI.Combinatorics.BooleanFunctions.Walsh ----
namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Finite Walsh calculus -/

theorem average_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, mul_add]

theorem average_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_sum {α κ : Type*} [Fintype α] (s : Finset κ) (f : κ → α → ℝ) :
    average (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, average (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ### Degree calculus for finite observations -/

end SquareRootDegree

end

end OAI

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

theorem normalized_product_sum (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (T : ι → α → ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*(∑ i, T i (x i))) =
      ∑ i, average (fun a => r i a*T i a) := by
  simp_rw [Finset.mul_sum]
  rw [average_sum]
  exact Finset.sum_congr rfl (fun _ _ => normalized_product_eval r hr _ _)

theorem normalized_product_shifted_sq (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (T : ι → α → ℝ) (μ : ι → ℝ) (hμ : ∀ i, average (fun a => r i a*T i a) = μ i)
    (c : ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*(c+∑ i, T i (x i))^2) =
      (c+∑ i, μ i)^2 + ∑ i, (average (fun a => r i a*(T i a)^2)-(μ i)^2) := by
  have hc (i : ι) : average (fun a => r i a*(T i a-μ i)) = 0 := by
    simp only [mul_sub,average_sub,average_mul_const,hμ,hr,one_mul,sub_self]
  have hfirst := normalized_product_sum r hr (fun i a => T i a-μ i)
  simp only [hc,Finset.sum_const_zero] at hfirst
  have hsecond := normalized_product_centered_sq r hr (fun i a => T i a-μ i) hc
  have hp : average (fun x : ι → α => ∏ i, r i (x i)) = 1 := by rw [average_pi_prod]; simp [hr]
  have he : (fun x : ι → α => (∏ i, r i (x i))*(c+∑ i, T i (x i))^2) =
      fun x => (∏ i, r i (x i))*(∑ i, (T i (x i)-μ i))^2 +
        2*(c+∑ i, μ i)*((∏ i, r i (x i))*(∑ i, (T i (x i)-μ i))) +
        (c+∑ i, μ i)^2*(∏ i, r i (x i)) := by
    funext x; rw [Finset.sum_sub_distrib]; ring
  rw [he,average_add,average_add,average_const_mul,average_const_mul,hfirst,hsecond,hp]
  have hd (i : ι) : average (fun a => r i a*(T i a-μ i)^2) =
      average (fun a => r i a*(T i a)^2)-(μ i)^2 := by
    have he' : (fun a => r i a*(T i a-μ i)^2) =
        fun a => r i a*(T i a)^2-2*μ i*(r i a*T i a)+(μ i)^2*r i a := by funext a; ring
    rw [he',average_add,average_sub,average_const_mul,average_const_mul,hμ,hr]
    ring
  simp_rw [hd]
  ring

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
    (T : ι → α → ℝ) (μ : ι → ℝ) (hμ : ∀ i, average (fun a => r i a*T i a) = μ i)
    (c : ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*(c+∑ i, T i (x i))^2) =
      (c+∑ i, μ i)^2 + ∑ i, (average (fun a => r i a*(T i a)^2)-(μ i)^2) := by
  first
    | exact OAI.SquareRootDegree.FiniteMoments.normalized_product_shifted_sq r hr T μ hμ c
    | exact OAI.SquareRootDegree.FiniteMoments.normalized_product_shifted_sq
    | (apply OAI.SquareRootDegree.FiniteMoments.normalized_product_shifted_sq <;> assumption)
    | (intros; apply OAI.SquareRootDegree.FiniteMoments.normalized_product_shifted_sq <;> assumption)
