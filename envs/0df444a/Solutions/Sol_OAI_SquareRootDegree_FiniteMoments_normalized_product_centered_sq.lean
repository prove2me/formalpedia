-- Prove2me | solution 1 for OAI.SquareRootDegree.FiniteMoments.normalized_product_centered_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:08:46.584303+00:00
-- url     : https://prove2.me/submissions/312f6a83-dedf-4d41-a56b-bf60d15aac45

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/FiniteMoments.lean:L67-L87
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.FiniteMoments.normalized_product_centered_sq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
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

theorem normalized_product_two_eval (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (j k : ι) (hjk : j ≠ k) (g h : α → ℝ) :
    average (fun x : ι → α => (∏ i, r i (x i))*g (x j)*h (x k)) =
      average (fun a => r j a*g a) * average (fun a => r k a*h a) := by
  have he : (fun x : ι → α => (∏ i, r i (x i))*g (x j)*h (x k)) =
      fun x => ∏ i, r i (x i)*(if i = j then g (x i) else 1)*(if i = k then h (x i) else 1) := by
    funext x
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    simp
  rw [he,average_pi_prod (fun i a => r i a*(if i = j then g a else 1)*(if i = k then h a else 1))]
  have hf (i : ι) : average (fun a => r i a*(if i = j then g a else 1)*(if i = k then h a else 1)) =
      (if i = j then average (fun a => r j a*g a) else 1)*
        (if i = k then average (fun a => r k a*h a) else 1) := by
    by_cases hj : i = j
    · subst i; simp [hjk]
    by_cases hk : i = k
    · subst i; simp [hj]
    simp [hj,hk,hr]
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp

theorem normalized_product_centered_sq (r : ι → α → ℝ) (hr : ∀ i, average (r i) = 1)
    (T : ι → α → ℝ) (hT : ∀ i, average (fun a => r i a*T i a) = 0) :
    average (fun x : ι → α => (∏ i, r i (x i))*(∑ i, T i (x i))^2) =
      ∑ i, average (fun a => r i a*(T i a)^2) := by
  have he : (fun x : ι → α => (∏ i, r i (x i))*(∑ i, T i (x i))^2) =
      fun x => ∑ i, ∑ j, (∏ k, r k (x k))*T i (x i)*T j (x j) := by
    funext x
    simp only [sq,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [he,average_sum]
  simp_rw [average_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · have he' : (fun x : ι → α => (∏ k, r k (x k))*T i (x i)*T i (x i)) =
        fun x => (∏ k, r k (x k))*(T i (x i))^2 := by funext x; ring
    rw [he',normalized_product_eval r hr i (fun a => (T i a)^2)]
  · intro j _ hij
    rw [normalized_product_two_eval r hr i j (Ne.symm hij),hT,hT,mul_zero]
  · simp

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
    (T : ι → α → ℝ) (hT : ∀ i, average (fun a => r i a*T i a) = 0) :
    average (fun x : ι → α => (∏ i, r i (x i))*(∑ i, T i (x i))^2) =
      ∑ i, average (fun a => r i a*(T i a)^2) := by
  first
    | exact OAI.SquareRootDegree.FiniteMoments.normalized_product_centered_sq r hr T hT
    | exact OAI.SquareRootDegree.FiniteMoments.normalized_product_centered_sq
    | (apply OAI.SquareRootDegree.FiniteMoments.normalized_product_centered_sq <;> assumption)
    | (intros; apply OAI.SquareRootDegree.FiniteMoments.normalized_product_centered_sq <;> assumption)
