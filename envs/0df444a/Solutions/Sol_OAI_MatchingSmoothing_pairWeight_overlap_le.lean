-- Prove2me | solution 1 for OAI.MatchingSmoothing.pairWeight_overlap_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:57:45.001072+00:00
-- url     : https://prove2.me/submissions/31ef4571-3f66-412c-9f2a-5d067c559633

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/TransitionMatrices.lean:L130-L154
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.pairWeight_overlap_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices

-- ---- from OAI.Combinatorics.MatchingPSD.ColoringCounts ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace MatchingSmoothing

variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]

variable {H : Type u_5} [Fintype H] [DecidableEq H]

lemma sum_pairConstant (F : (H × Bool → β) → ℝ) [Fintype β] :
    (∑ f, if pairConstant f then F f else 0) = ∑ k : H → β, F (duplicateColoring k) := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter]
  simp only [Finset.subtype_univ]
  exact Fintype.sum_equiv pairConstantEquiv _ _ (by
    intro f
    congr 1
    exact (congrArg Subtype.val (pairConstantEquiv.symm_apply_apply f)).symm)

end MatchingSmoothing

end OAI

-- ---- from OAI.Combinatorics.MatchingPSD.TransitionMatrices ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
private abbrev Finset.prod_le_one₀ := @Finset.prod_le_one

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix

variable {V : Type u_1} {C : Type u_2} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

omit [DecidableEq C] in
lemma tensorKernel_mul (U W : Matrix C C ℝ) :
    tensorKernel (V := V) (U * W) = tensorKernel (V := V) U * tensorKernel W := by
  classical
  ext f g
  simp only [tensorKernel, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro h _
  exact Finset.prod_mul_distrib

omit [Fintype C] [DecidableEq V] [DecidableEq C] in
lemma tensorKernel_transpose (U : Matrix C C ℝ) :
    tensorKernel (V := V) U.transpose = (tensorKernel U).transpose := rfl

omit [Fintype C] [DecidableEq V] in
lemma tensorKernel_one :
    tensorKernel (V := V) (1 : Matrix C C ℝ) = 1 := by
  classical
  ext f g
  by_cases h : f = g
  · subst g; simp [tensorKernel]
  · have he : ∃ v, f v ≠ g v := Function.ne_iff.mp h
    obtain ⟨v, hv⟩ := he
    simp only [tensorKernel, Matrix.one_apply, ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv]

lemma tensorKernel_orthogonal (U : Matrix C C ℝ)
    (hU : U.transpose * U = 1) :
    (tensorKernel (V := V) U).transpose * tensorKernel (V := V) U = 1 := by
  rw [← tensorKernel_transpose, ← tensorKernel_mul, hU, tensorKernel_one]

lemma tensorKernel_overlap (U : Matrix C C ℝ)
    (hU : U.transpose * U = 1) (x y : (V → C) → ℝ) :
    (tensorKernel U *ᵥ x) ⬝ᵥ (tensorKernel U *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, tensorKernel_orthogonal U hU,
    Matrix.vecMul_one]

omit [Fintype C] [DecidableEq V] [DecidableEq C] in
lemma tensorKernel_relabel (U : Matrix C C ℝ) (σ : Equiv.Perm V) (f g : V → C) :
    tensorKernel U (f ∘ σ) (g ∘ σ) = tensorKernel U f g := by
  exact Equiv.prod_comp σ (fun v => U (f v) (g v))

omit [DecidableEq C] in
lemma tensorKernel_mulVec_relabel (U : Matrix C C ℝ) (σ : Equiv.Perm V)
    (x : (V → C) → ℝ) (f : V → C) :
    (tensorKernel U *ᵥ (fun g => x (g ∘ σ))) f =
      (tensorKernel U *ᵥ x) (f ∘ σ) := by
  classical
  let e : (V → C) ≃ (V → C) := Equiv.arrowCongr σ (Equiv.refl C)
  change ∑ g, tensorKernel U f g * x (g ∘ σ) =
    ∑ g, tensorKernel U (f ∘ σ) g * x g
  refine Fintype.sum_equiv e.symm _ _ ?_
  intro g
  have he : e.symm g = g ∘ σ := rfl
  rw [he, tensorKernel_relabel]

variable {H : Type u_3} [Fintype H] [DecidableEq H]

lemma tensorKernel_mulVec_pairDiagonal (U : Matrix C C ℝ) (d : C → ℝ)
    (f : H × Bool → C) :
    (tensorKernel U *ᵥ pairDiagonal d) f =
      pairWeight (U * diagonal d * U.transpose) f := by
  classical
  change ∑ g, (∏ v, U (f v) (g v)) *
    (if pairConstant g then ∏ i, d (g (i, false)) else 0) = _
  simp only [mul_ite, mul_zero]
  rw [sum_pairConstant]
  simp only [duplicateColoring, Fintype.prod_prod_type, Fintype.prod_bool]
  have hm (a b : C) : (U * diagonal d * U.transpose) a b =
      ∑ c, U a c * d c * U b c := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  simp only [pairWeight, hm]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

lemma pairWeight_overlap (U : Matrix C C ℝ) (d : C → ℝ)
    (hU : U.transpose * U = 1) (σ : Equiv.Perm (H × Bool)) :
    (∑ f : H × Bool → C, pairWeight (U * diagonal d * U.transpose) f *
      pairWeight (U * diagonal d * U.transpose) (f ∘ σ)) =
    ∑ f : H × Bool → C, pairDiagonal d f * pairDiagonal d (f ∘ σ) := by
  simp_rw [← tensorKernel_mulVec_pairDiagonal,
    ← tensorKernel_mulVec_relabel U σ (pairDiagonal d)]
  exact tensorKernel_overlap U hU _ _

omit [Fintype C] [DecidableEq H] in
lemma pairDiagonal_abs_le (d : C → ℝ) (hd : ∀ c, |d c| ≤ 1) (f : H × Bool → C) :
    |pairDiagonal d f| ≤ 1 := by
  classical
  unfold pairDiagonal
  split_ifs
  · rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => hd _)
  · simp

lemma pairWeight_overlap_le (U : Matrix C C ℝ) (d : C → ℝ)
    (hU : U.transpose * U = 1) (hd : ∀ c, |d c| ≤ 1)
    (σ : Equiv.Perm (H × Bool)) :
    (∑ f : H × Bool → C, pairWeight (U * diagonal d * U.transpose) f *
      pairWeight (U * diagonal d * U.transpose) (f ∘ σ)) ≤
    (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) := by
  classical
  rw [pairWeight_overlap U d hU σ]
  have he : (Fintype.card {f : H × Bool → C // pairConstant f ∧ pairConstant (f ∘ σ)} : ℝ) =
      ∑ f : H × Bool → C, if pairConstant f ∧ pairConstant (f ∘ σ) then (1 : ℝ) else 0 := by
    simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro f _
    split_ifs <;> norm_num
  rw [he]
  apply Finset.sum_le_sum
  intro f _
  by_cases hf : pairConstant f ∧ pairConstant (f ∘ σ)
  · rw [ite_eq_left hf]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact (mul_le_mul (pairDiagonal_abs_le d hd f)
        (pairDiagonal_abs_le d hd (f ∘ σ)) (abs_nonneg _) zero_le_one).trans_eq (mul_one _))
  · rw [ite_eq_right hf]
    rcases not_and_or.mp hf with hf | hf <;> simp [pairDiagonal, hf]

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open Matrix


theorem solution : type_of% @_root_.OAI.MatchingSmoothing.pairWeight_overlap_le := @_root_.OAI.MatchingSmoothing.pairWeight_overlap_le
