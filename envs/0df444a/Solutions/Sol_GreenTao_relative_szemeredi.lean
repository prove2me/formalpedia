-- Prove2me | solution 1 for GreenTao.relative_szemeredi
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @davidnet
-- created : 2026-09-06T02:16:28.81368+00:00
-- url     : https://prove2.me/submissions/dd5a7511-10c8-4b46-b0c3-0b004b75b79a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_GreenTao_varnavides_set_count
import Theorems.Thm_GreenTao_bounded_model_for_progression_counts

open scoped BigOperators Topology
open Filter GreenTao

private lemma uniform_avg_mono {α : Type} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : avg f ≤ avg g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

private lemma progression_avg_mono {m : ℕ+} (k : ℕ)
    {f g : ZMod (m : ℕ) → ℝ} (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) :
    apAvg k f ≤ apAvg k g := by
  apply uniform_avg_mono
  intro x
  apply uniform_avg_mono
  intro r
  exact Finset.prod_le_prod (fun j _ => hf _) (fun j _ => hfg _)

private lemma progression_avg_scale {m : ℕ+} (k : ℕ)
    (c : ℝ) (f : ZMod (m : ℕ) → ℝ) :
    apAvg k (fun x => c * f x) = c ^ k * apAvg k f := by
  simp only [apAvg, avg, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
  ring

/-- Thresholding at half the mean converts a set-count bound into a weighted bound. -/
private lemma bounded_weighted_szemeredi
    (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ,
      ∀ (m : ℕ+) (_ : Nat.Prime (m : ℕ)) (_ : B ≤ (m : ℕ))
        (g : ZMod (m : ℕ) → ℝ),
        (∀ x, 0 ≤ g x ∧ g x ≤ 1) → δ ≤ avg g → c ≤ apAvg k g := by
  classical
  have ht : 0 < δ / 2 := by positivity
  obtain ⟨c, hc, B, hsets⟩ := GreenTao.varnavides_set_count k hk (δ / 2) ht (by linarith)
  refine ⟨(δ / 2) ^ k * c, mul_pos (pow_pos ht _) hc, B, ?_⟩
  intro m hm hB g hg hmean
  let A : Finset (ZMod (m : ℕ)) := Finset.univ.filter fun x => δ / 2 ≤ g x
  let indicator : ZMod (m : ℕ) → ℝ := fun x => if x ∈ A then 1 else 0
  have hmem (x : ZMod (m : ℕ)) : x ∈ A ↔ δ / 2 ≤ g x := by simp [A]
  have hsum_indicator : (∑ x, indicator x) = (A.card : ℝ) := by simp [indicator]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.pos
  have hpoint (x : ZMod (m : ℕ)) : g x ≤ δ / 2 + indicator x := by
    by_cases hx : x ∈ A
    · simp only [indicator, if_pos hx]
      linarith [(hg x).2]
    · have hx' : g x < δ / 2 := lt_of_not_ge ((hmem x).not.mp hx)
      simpa [indicator, hx] using hx'.le
  have hsum_upper : (∑ x, g x) ≤ δ / 2 * (m : ℝ) + (A.card : ℝ) := by
    calc
      _ ≤ ∑ x, (δ / 2 + indicator x) := Finset.sum_le_sum fun x _ => hpoint x
      _ = _ := by rw [Finset.sum_add_distrib, hsum_indicator]; simp [ZMod.card, mul_comm]
  have havg : avg g = (∑ x, g x) / (m : ℝ) := by
    simp [avg, ZMod.card, div_eq_mul_inv, mul_comm]
  have hsum_lower : δ * (m : ℝ) ≤ ∑ x, g x := by
    rwa [havg, le_div_iff₀ hmpos] at hmean
  have hdensity : δ / 2 * (m : ℝ) ≤ (A.card : ℝ) := by linarith
  have hcount : c ≤ apAvg k indicator := hsets m hm hB A hdensity
  have hnonneg (x : ZMod (m : ℕ)) : 0 ≤ δ / 2 * indicator x := by
    dsimp [indicator]
    split_ifs <;> positivity
  have hbelow (x : ZMod (m : ℕ)) : δ / 2 * indicator x ≤ g x := by
    by_cases hx : x ∈ A
    · simpa [indicator, hx] using (hmem x).mp hx
    · simpa [indicator, hx] using (hg x).1
  calc
    (δ / 2) ^ k * c ≤ (δ / 2) ^ k * apAvg k indicator :=
      mul_le_mul_of_nonneg_left hcount (pow_nonneg ht.le _)
    _ = apAvg k (fun x => δ / 2 * indicator x) := (progression_avg_scale k _ _).symm
    _ ≤ apAvg k g := progression_avg_mono k hnonneg hbelow

theorem solution
    (k : ℕ) (hk : 3 ≤ k) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (ν f : GreenTao.Family M) (hν : GreenTao.Pseudorandom k M ν)
    (hf : ∀ n x, 0 ≤ f n x ∧ f n x ≤ ν n x)
    (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hdensity : ∀ᶠ n in atTop, δ ≤ GreenTao.avg (f n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, c ≤ GreenTao.apAvg k (f n) := by
  obtain ⟨c, hc, B, hweighted⟩ :=
    bounded_weighted_szemeredi k hk (δ / 2) (by positivity) (by linarith)
  let η := min (δ / 2) (c / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hmodel := GreenTao.bounded_model_for_progression_counts k hk M hprime hM ν f hν hf η hη
  have hlarge : ∀ᶠ n in atTop, B ≤ (M n : ℕ) := hM.eventually (eventually_ge_atTop B)
  refine ⟨c / 2, by positivity, ?_⟩
  filter_upwards [hdensity, hmodel, hlarge] with n hnmean hnmodel hnlarge
  obtain ⟨g, hg, hgmean, hgcount⟩ := hnmodel
  have hηδ : η ≤ δ / 2 := min_le_left _ _
  have hηc : η ≤ c / 2 := min_le_right _ _
  have hgdensity : δ / 2 ≤ avg g := by linarith
  have hpositive := hweighted (M n) (hprime n) hnlarge g hg hgdensity
  linarith
