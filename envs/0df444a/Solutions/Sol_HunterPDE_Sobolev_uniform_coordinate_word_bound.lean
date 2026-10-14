-- Prove2me | solution 1 for HunterPDE.Sobolev.uniform_coordinate_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T21:42:32.909879+00:00
-- url     : https://prove2.me/submissions/8a475a05-cc41-4ced-9910-d6ac92df7ca7

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

theorem solution {n : ℕ} (l : List (Fin n))
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
