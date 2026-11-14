-- Prove2me | solution 1 for LinearChoresCLS.reduction_figure_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:22:30.38925+00:00
-- url     : https://prove2.me/submissions/d2d188c4-4eda-41c2-b16a-22738903b6dd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_LinearChoresCLS_lemma_7_1
import Theorems.Thm_LinearChoresCLS_lemma_7_5
import Theorems.Thm_LinearChoresCLS_lemma_7_6
import Theorems.Thm_LinearChoresCLS_proposition_4_1
import Theorems.Thm_LinearChoresCLS_figure_1_encoded_construction

open Finset NetworkEquilibriumCLS.LinearNash LinearChoresCLS

private theorem input_price_pos {n : ℕ} {x : Fin n → ℝ} (hx : InCube x) {t : ℝ}
    (ht : 0 ≤ t) (j : Fin (n + 1)) : 0 < basicPrice t x j := by
  have he (b : Fin (n + 1)) : 0 ≤ xExt x b := by
    refine Fin.cases ?_ (fun i => ?_) b
    · simp [xExt]
    · simpa [xExt] using (hx i).1
  have hb : 0 ≤ xbar x := by
    unfold xbar
    exact div_nonneg (Finset.sum_nonneg (fun b _ => he b)) (by positivity)
  unfold basicPrice
  have hj := he j
  exact div_pos (by positivity) (by positivity)

private theorem family_pos {n : ℕ} (P : Quadratic n) (ε : ℚ) (x : Fin n → ℝ)
    (hx : InCube x) (i : Chore n (chainLength P ε)) : 0 < completedPrice P ε x i := by
  have ht : 0 < tParam P ε := by unfold tParam; positivity
  have hL : 8 ≤ chainLength P ε := by
    classical
    unfold chainLength
    split
    next h => exact (Nat.find_spec h).1
    next => exact le_rfl
  have hsmall : tParam P ε ≤ (1 / 2 : ℝ) ^ 8 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hL
  have hbase : 0 ≤ 1 / 2 - 4 * tParam P ε := by norm_num at hsmall; linarith
  have hq (k : ℕ) : 0 < qPar (tParam P ε) k := by unfold qPar; positivity
  have layers {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (k : ℕ) :
      0 < (layerOut (tParam P ε) u v k).1 ∧ 0 < (layerOut (tParam P ε) u v k).2 := by
    induction k with
    | zero => exact ⟨div_pos (lt_max_of_lt_left hu) (hq 0), mul_pos (hq 0) (lt_min hu hv)⟩
    | succ k ih => exact ⟨div_pos (lt_max_of_lt_left ih.1) (hq _), mul_pos (hq _) (lt_min ih.1 ih.2)⟩
  rcases i with j | ⟨π, k, s⟩
  · exact input_price_pos hx ht.le j
  · have h := layers (input_price_pos hx ht.le π.1.1) (input_price_pos hx ht.le π.1.2) k.val
    cases s <;> first | exact h.1 | exact h.2

/-- Each unordered pair has exactly two endpoints. -/
private theorem sum_incident {n : ℕ} (w : Pair n → ℝ) :
    ∑ j : Fin (n + 1), ∑ π ∈ incident j, w π = 2 * ∑ π, w π := by
  classical
  simp only [incident, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  have hne : π.1.1 ≠ π.1.2 := ne_of_lt π.2
  have hsplit (j : Fin (n + 1)) :
      (if π.1.1 = j ∨ π.1.2 = j then w π else 0) =
      (if j = π.1.1 then w π else 0) + (if j = π.1.2 then w π else 0) := by
    by_cases h₁ : j = π.1.1
    · subst j; simp [hne]
    · by_cases h₂ : j = π.1.2
      · subst j; simp [hne, hne.symm]
      · simp [h₁, h₂, Ne.symm h₁, Ne.symm h₂]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp [two_mul]

private theorem total_earnings {n L : ℕ} (P : Quadratic n) (t : ℝ) :
    ∑ a, (chainMarket P t L).earn a = (n : ℝ) + 1 := by
  classical
  have hlin : (∑ j : Fin (n + 1), cExt P j) = 0 := by
    rw [Fin.sum_univ_succ]; simp [cExt]
  have hinc : (∑ j : Fin (n+1), ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val)
      = 2 * ∑ k : Fin L, ∑ π, gadgetEarn P t π k.val := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => sum_incident _)
  change (∑ a : Fin (n+1) ⊕ (Pair n × Fin L × Fin 3), _) = _
  rw [Fintype.sum_sum_type]
  change (∑ j : Fin (n+1), ((1 - 3 / 2 * ∑ k : Fin L, ∑ π ∈ incident j, gadgetEarn P t π k.val) -
      alpha P t / t * cExt P j)) + (∑ a : Pair n × Fin L × Fin 3, gadgetEarn P t a.1 a.2.1.val) = _
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hinc, hlin, mul_zero, sub_zero]
  have haux : (∑ a : Pair n × Fin L × Fin 3, gadgetEarn P t a.1 a.2.1.val) =
      3 * ∑ k : Fin L, ∑ π, gadgetEarn P t π k.val := by
    rw [Fintype.sum_prod_type, Finset.sum_comm (s := (univ : Finset (Fin L))) (t := (univ : Finset (Pair n)))]
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_ofNat, Finset.mul_sum]
  rw [haux]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_one]
  ring

private theorem normalized_domain {n : ℕ} (P : Quadratic n) (ε : ℚ)
    (hv : (completedMarket P ε).Valid) (x : Fin n → ℝ) (hx : InCube x) :
    completedNormPrice P ε x ∈ (completedMarket P ε).priceDomain := by
  let t := tParam P ε
  let L := chainLength P ε
  have hpos (j : Chore n L) : 0 < priceFam t L x j := family_pos P ε x hx j
  have hT : 0 < totalPay P t L x := Finset.sum_pos
    (fun j _ => mul_pos (hv.2.2 j) (hpos j)) Finset.univ_nonempty
  refine ⟨fun j => mul_pos (div_pos (by positivity) hT) (hpos j), ?_⟩
  change (∑ j, (chainMarket P t L).supply j * (((n : ℝ) + 1) / totalPay P t L x * priceFam t L x j)) = _
  simp_rw [mul_left_comm ((chainMarket P t L).supply _) _ (priceFam t L x _)]
  change (∑ j, (((n : ℝ) + 1) / totalPay P t L x) * ((chainMarket P t L).supply j * priceFam t L x j)) = ∑ a, (chainMarket P t L).earn a
  rw [← Finset.mul_sum, total_earnings]
  change ((n : ℝ) + 1) / totalPay P t L x * totalPay P t L x = _
  exact div_mul_cancel₀ _ hT.ne'

theorem solution : SearchReduces epsQKKTSearch choresCESearch := by
  obtain ⟨f, g, hf, hg, hmaps⟩ := figure_1_encoded_construction
  refine ⟨f, g, hf, hg, ?_⟩
  rintro _ ⟨n, hn, P, ε, hε, rfl⟩
  obtain ⟨hvalid, hmarket, hdecode⟩ := hmaps n hn P ε hε
  refine ⟨hmarket, ?_⟩
  intro y hy
  obtain ⟨p, z, v, hCE, hv, hcode⟩ := hdecode y hy
  refine ⟨n, hn, P, ε, hε, rfl, v, hcode, ?_⟩
  rw [hv]
  obtain ⟨hx, hp⟩ := lemma_7_1 hn P ε hε p z hCE
  obtain ⟨C, R, hobj, hβ, hbound, hR⟩ := lemma_7_6 hn P ε hε
  have hα : 0 < alpha P (tParam P ε) := by unfold alpha lam tParam; positivity
  apply proposition_4_1 (completedMarket P ε) hvalid P (ε : ℝ) (by exact_mod_cast hε)
    (completedNormPrice P ε) (normalized_domain P ε hvalid) (lemma_7_5 hn P ε hε)
    ⟨_, C, _, R, hα, hobj, hβ, hbound, hR⟩ _ hx
  refine ⟨z, ?_⟩
  rw [← hp]
  exact hCE
