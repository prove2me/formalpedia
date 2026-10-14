-- Prove2me | solution 1 for HunterPDE.Sobolev.uniform_cutoff_jet_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T21:39:05.113407+00:00
-- url     : https://prove2.me/submissions/8c62757b-8556-4933-9e78-7ab70ca806ec

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open HunterPDE.Sobolev
open scoped ContDiff

lemma partial_affine {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (i : Fin n) (a b c : ℝ) :
    partialDeriv i (fun x => a + b * f (c • x)) =
      fun x => 0 + (b * c) * partialDeriv i f (c • x) := by
  funext x
  have hf' := (hf.differentiable (by simp)).differentiableAt (x := c • x)
  have hd := hf'.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)
  have h := (hd.const_smul b).const_add a
  have h' : HasFDerivAt (fun y => a + b * f (c • y))
      (b • (fderiv ℝ f (c • x)).comp (c • ContinuousLinearMap.id ℝ _)) x := by
    simpa only [Function.comp_def, Pi.smul_apply, smul_eq_mul] using h
  unfold partialDeriv
  rw [h'.fderiv]
  simp [mul_assoc]

lemma partial_test {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : IsTestFunction Set.univ f) (i : Fin n) :
    IsTestFunction Set.univ (partialDeriv i f) := by
  refine ⟨?_, hf.2.1.fderiv_apply ℝ _, Set.subset_univ _⟩
  exact (hf.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp
    (contDiff_id.prodMk contDiff_const)

lemma word_bound {n : ℕ} (l : List (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsTestFunction Set.univ f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b c : ℝ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      ∀ x, ‖l.foldl (fun g i => partialDeriv i g) (fun y => a + b * f (c • y)) x‖ ≤ C := by
  induction l generalizing f with
  | nil =>
    obtain ⟨B, hB⟩ := hf.2.1.exists_bound_of_continuous hf.1.continuous
    have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
    refine ⟨1 + B, by positivity, ?_⟩
    intro a b c ha hb hc x
    exact (norm_add_le _ _).trans (add_le_add ha
      (by simpa only [norm_mul, one_mul] using (mul_le_mul hb (hB (c • x))
        (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))))
  | cons i l ih =>
    obtain ⟨C, hC, h⟩ := ih (partialDeriv i f) (partial_test hf i)
    refine ⟨C, hC, ?_⟩
    intro a b c ha hb hc x
    simp only [List.foldl_cons, partial_affine f hf.1 i a b c]
    exact h 0 (b * c) c (by simp)
      (by simpa only [norm_mul, one_mul] using (mul_le_mul hb hc (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))) hc x

lemma foldr_repeated {n : ℕ} (i : Fin n) (m : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (List.replicate m i).foldr partialDeriv f = (partialDeriv i)^[m] f := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, ih, Function.iterate_succ_apply']

lemma partial_word {n : ℕ} (β : Fin n → ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    iteratedPartial β f =
      (((List.finRange n).flatMap (fun i => List.replicate (β i) i)).reverse).foldl
        (fun g i => partialDeriv i g) f := by
  rw [← List.foldr_eq_foldl_reverse, List.foldr_flatMap]
  simp only [foldr_repeated, iteratedPartial]

theorem solution {n : ℕ} (k : ℕ)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : IsTestFunction Set.univ χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (β : Fin n → ℕ), ∑ i, β i ≤ k →
      ∀ x, ‖iteratedPartial β (fun y => 1 - χ (((j : ℝ) + 1)⁻¹ • y)) x‖ ≤ C := by
  classical
  have bound (β : Fin n → ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b c : ℝ,
      ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∀ x,
      ‖iteratedPartial β (fun y => a + b * χ (c • y)) x‖ ≤ C := by
    simpa only [partial_word] using word_bound
      (((List.finRange n).flatMap (fun i => List.replicate (β i) i)).reverse) χ hχ
  choose B hB using bound
  refine ⟨∑ β ∈ multiIndices n k, B β, Finset.sum_nonneg (fun β _ => (hB β).1), ?_⟩
  intro j β hβ x
  have hmem : β ∈ multiIndices n k := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hβ⟩
    apply Finset.mem_image.mpr
    have hcoord (i : Fin n) : β i < k + 1 := by
      exact Nat.lt_succ_of_le ((Finset.single_le_sum (fun i _ => Nat.zero_le (β i))
        (Finset.mem_univ i)).trans hβ)
    exact ⟨fun i => ⟨β i, hcoord i⟩, Finset.mem_univ _, rfl⟩
  have hc : ‖((j : ℝ) + 1)⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by simp)
  have hx := (hB β).2 1 (-1) (((j : ℝ) + 1)⁻¹) (by norm_num) (by norm_num) hc x
  have hx' : ‖iteratedPartial β (fun y => 1 - χ (((j : ℝ) + 1)⁻¹ • y)) x‖ ≤ B β := by
    simpa [sub_eq_add_neg] using hx
  exact hx'.trans
    (Finset.single_le_sum (fun β _ => (hB β).1) hmem)
