-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.finrank_le_splitBound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:23:37.784059+00:00
-- url     : https://prove2.me/submissions/c7664601-6c82-49b5-a458-587f96026ba4

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/Multigraded.lean:L181-L212
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.finrank_le_splitBound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Theorems.Thm_OAI_PermanentBorder_Multigraded_finrank_product_split
import Theorems.Thm_OAI_PermanentBorder_Multigraded_project_mul

-- ---- from OAI.Algebra.Determinantal.Multigraded ----
namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

lemma componentClosed_sup {I J : Ideal (MvPolynomial σ K)}
    (hI : ComponentClosed w I) (hJ : ComponentClosed w J) :
    ComponentClosed w (I ⊔ J) := by
  intro p hp d
  obtain ⟨i,hi,j,hj,rfl⟩ := Submodule.mem_sup.mp hp
  rw [map_add]
  exact Ideal.add_mem _ (Submodule.mem_sup_left (hI i hi d))
    (Submodule.mem_sup_right (hJ j hj d))

lemma componentClosed_span_single {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) :
    ComponentClosed w (Ideal.span {a}) := by
  intro p hp d
  obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton.mp hp
  rw [project_mul w ha]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton a))

lemma componentClosed_bot : ComponentClosed (K := K) w ⊥ := by
  intro p hp d
  have hp0 : p = 0 := hp
  simp [hp0]

lemma productIdeal_closed (qs : List (FactorPair (K := K) w)) :
    ComponentClosed w (productIdeal w qs) := by
  induction qs with
  | nil => exact componentClosed_bot w
  | cons q qs ih =>
    exact componentClosed_sup w
      (componentClosed_span_single w (q.left_homogeneous.mul q.right_homogeneous)) ih

theorem finrank_le_splitBound [∀ d, Module.Finite K (Piece (K := K) w d)]
    (qs : List (FactorPair (K := K) w)) (I : Ideal (MvPolynomial σ K))
    (hI : ComponentClosed w I) (d : G) :
    Module.finrank K (componentQuotient w (I ⊔ productIdeal w qs) d) ≤
      splitBound w I d qs := by
  induction qs generalizing I d with
  | nil => rw [productIdeal, sup_bot_eq, splitBound]
  | cons q qs ih =>
    have hs := finrank_product_split w (b := q.right) (I ⊔ productIdeal w qs)
      (componentClosed_sup w hI (productIdeal_closed w qs)) q.left_homogeneous d
    have h₁ := ih (I ⊔ Ideal.span {q.left})
      (componentClosed_sup w hI (componentClosed_span_single w q.left_homogeneous)) d
    have h₂ := ih (I ⊔ Ideal.span {q.right})
      (componentClosed_sup w hI (componentClosed_span_single w q.right_homogeneous))
      (d-q.leftDegree)
    calc
      _ ≤ Module.finrank K (componentQuotient w
            ((I ⊔ Ideal.span {q.left}) ⊔ productIdeal w qs) d) +
          Module.finrank K (componentQuotient w
            ((I ⊔ Ideal.span {q.right}) ⊔ productIdeal w qs) (d-q.leftDegree)) := by
        have h₀ : I ⊔ productIdeal w (q::qs) =
            (I ⊔ productIdeal w qs) ⊔ Ideal.span {q.left*q.right} := by
          dsimp only [productIdeal]
          rw [sup_comm (Ideal.span {q.left*q.right}) (productIdeal w qs), ← sup_assoc]
        have hₐ : (I ⊔ productIdeal w qs) ⊔ Ideal.span {q.left} =
            (I ⊔ Ideal.span {q.left}) ⊔ productIdeal w qs := sup_right_comm _ _ _
        have hᵦ : (I ⊔ productIdeal w qs) ⊔ Ideal.span {q.right} =
            (I ⊔ Ideal.span {q.right}) ⊔ productIdeal w qs := sup_right_comm _ _ _
        rw [hₐ,hᵦ] at hs
        rw [h₀]
        exact hs
      _ ≤ _ := Nat.add_le_add h₁ h₂

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section Blocks
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

end Blocks
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearLeaves
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

end LinearLeaves
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded
open MvPolynomial


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.finrank_le_splitBound := @_root_.OAI.PermanentBorder.Multigraded.finrank_le_splitBound
