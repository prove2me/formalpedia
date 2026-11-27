-- Prove2me | solution 1 for Kyprianou.Ch04.clippedAffineGridVariationBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:56:39.534318+00:00
-- url     : https://prove2.me/submissions/d8278343-7c9c-42e5-abc4-e5b5c9a4270c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_monotoneGridIndicatorVariationV1
import Theorems.Thm_Kyprianou_Ch04_affineGridLedgerVariationBoundV1
import Theorems.Thm_Kyprianou_Ch04_kw47_positive_monotone_grid_variation
open MeasureTheory Set
open scoped NNReal Classical
set_option autoImplicit false

/-- The total variation of a clipped finite affine step path is bounded by
the drift variation plus the absolute mark ledger. -/
theorem solution (T : NNReal) (S : Finset NNReal) (a Y : NNReal → ℝ)
    (b : ℝ) (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (hY : ∀ s ≤ T, Y s = b * (s : ℝ) + ∑ r ∈ S, if r ≤ s then a r else 0) :
    ∀ t ≤ T, (∑ k ∈ Finset.range n,
      |Y (min t (u (k+1)))-Y (min t (u k))|) ≤
      |b| * (T : ℝ) + ∑ r ∈ S,|a r| := by
  intro t ht
  let v : ℕ → NNReal := fun k => min t (u k)
  have hv (k : ℕ) : v k ≤ T := (min_le_left _ _).trans ht
  have hm : Monotone v := fun i j hij => min_le_min le_rfl (hu hij)
  let J (r : NNReal) (k : ℕ) : ℝ := if r ≤ v k then 1 else 0
  have hV : (∑ k ∈ Finset.range n, |(v (k+1) : ℝ)-(v k : ℝ)|) ≤ T :=
    Kyprianou.Ch04.kw47_positive_monotone_grid_variation (fun k => (v k : ℝ)) n T
      (Or.inl fun i j hij => by exact_mod_cast hm hij) (by positivity) (by positivity)
      (by exact_mod_cast hv 0) (by exact_mod_cast hv n)
  have hJ' (r : NNReal) : (∑ k ∈ Finset.range n, |J r (k+1)-J r k|) ≤ 1 :=
    Kyprianou.Ch04.monotoneGridIndicatorVariationV1 v hm r n
  have he (k : ℕ) : Y (v (k+1))-Y (v k) =
      b*((v (k+1):ℝ)-(v k:ℝ)) + ∑ r ∈ S,a r*(J r (k+1)-J r k) := by
    rw [hY _ (hv (k+1)),hY _ (hv k)]
    let A (k : ℕ) := ∑ r ∈ S, if r ≤ v k then a r else 0
    have hsum : A (k+1)-A k = ∑ r ∈ S,a r*(J r (k+1)-J r k) := by
      dsimp [A]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases h1 : r ≤ v (k+1) <;> by_cases h0 : r ≤ v k <;> simp [J,h1,h0]
    change b*(v (k+1):ℝ) + A (k+1) - (b*(v k:ℝ)+A k) = _
    rw [← hsum]
    ring
  exact Kyprianou.Ch04.affineGridLedgerVariationBoundV1 S a b T n
    (fun k => (v k : ℝ)) (fun k => Y (v k)) J he hV hJ'
