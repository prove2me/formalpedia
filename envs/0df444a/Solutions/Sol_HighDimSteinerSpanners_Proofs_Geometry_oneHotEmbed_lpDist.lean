-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Geometry.oneHotEmbed_lpDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:56.909689+00:00
-- url     : https://prove2.me/submissions/e7d37d34-8e5a-4cb0-bab2-1f31f47d14df

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Geometry
noncomputable section
namespace HighDimSteinerSpanners.Proofs.Geometry
theorem _root_.solution {N q : ℕ} (p : ℝ) (hp : 1 ≤ p) : ∀ x y : Fin N → Fin q,
    lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p) := by
  classical
  have hp_ne : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  intro x y
  unfold lpDist
  congr 1
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  have h_inner : ∀ v : Fin N,
      (∑ c : Fin q,
        |oneHotEmbed x (finProdFinEquiv (v, c)) - oneHotEmbed y (finProdFinEquiv (v, c))| ^ p) =
        2 * (if x v ≠ y v then (1 : ℝ) else 0) := by
    intro v
    dsimp only [oneHotEmbed]
    simp only [Equiv.symm_apply_apply]
    by_cases hne : x v = y v
    · simp [hne, Real.zero_rpow hp_ne]
    · simp only [ne_eq, hne, not_false_eq_true, ↓reduceIte, mul_one]
      rw [← Finset.sum_subset (Finset.subset_univ ({x v, y v} : Finset (Fin q)))]
      · rw [Finset.sum_pair hne]
        have hne' : y v ≠ x v := Ne.symm hne
        simp only [↓reduceIte, hne, hne', sub_zero, zero_sub, abs_one, abs_neg, Real.one_rpow]
        norm_num
      · intro c _ hc
        have h1 : x v ≠ c := fun h => hc (by simp [h])
        have h2 : y v ≠ c := fun h => hc (by simp [h])
        simp [h1, h2, Real.zero_rpow hp_ne]
  simp_rw [h_inner, ← Finset.mul_sum]
  rw [Finset.sum_boole]
  rfl
end HighDimSteinerSpanners.Proofs.Geometry
