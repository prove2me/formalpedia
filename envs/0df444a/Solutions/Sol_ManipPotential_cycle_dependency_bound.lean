-- Prove2me | solution 1 for ManipPotential.cycle_dependency_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T19:41:48.29046+00:00
-- url     : https://prove2.me/submissions/ab46be4f-5f7c-4b6b-b200-aa243dd6aeaf

import Mathlib
import Definitions.Def_ManipPotential_Cmp
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec

open ManipPotential

namespace CycleDepAux

/-- In `Fin (n+3)`, `d - 1 < d` iff `d ≠ 0`. -/
lemma sub_one_lt_iff' {n : ℕ} (d : Fin (n + 3)) : d - 1 < d ↔ d ≠ 0 := by
  rw [Fin.lt_def, Fin.coe_sub_one]
  constructor
  · intro h hd
    subst hd
    simp at h
  · intro hd
    have hv : (d : ℕ) ≠ 0 := by
      intro h0; exact hd (Fin.ext (by simpa using h0))
    rw [if_neg hd]
    omega

/-- In `Fin (n+3)`, `d < d - 1` iff `d = 0`. -/
lemma lt_sub_one_iff' {n : ℕ} (d : Fin (n + 3)) : d < d - 1 ↔ d = 0 := by
  rw [Fin.lt_def, Fin.coe_sub_one]
  constructor
  · intro h
    by_contra hd
    rw [if_neg hd] at h
    omega
  · intro hd
    subst hd
    simp

lemma sub_succ {n : ℕ} (x y : Fin (n + 3)) : x - (y + 1) = x - y - 1 := by
  rw [sub_sub]

/-- A ranking realizing any proper nonempty pattern of cyclic comparisons. -/
lemma exists_ranking_pattern {n : ℕ} (p : Fin (n + 3) → Prop) [DecidablePred p]
    (hp : ∃ i, p i) (hq : ∃ k, ¬ p k) :
    ∃ r : Ranking (n + 3), ∀ i, (r i < r (i + 1) ↔ p i) := by
  classical
  obtain ⟨k, hk⟩ := hq
  obtain ⟨j0, hj0⟩ := hp
  -- distance along the path starting at `k + 1`
  let t : Fin (n + 3) → ℕ := fun c => ((c - (k + 1) : Fin (n + 3)) : ℕ)
  let N : Fin (n + 3) → ℕ := fun c =>
    (Finset.univ.filter (fun x => t x < t c ∧ p x)).card
  let key : Fin (n + 3) → Lex (ℕ × ℤ) := fun c => toLex (N c, -((t c : ℕ) : ℤ))
  have hkey_inj : Function.Injective key := by
    intro a b hab
    have h2 : t a = t b := by
      have := congrArg (fun x => (ofLex x).2) hab
      simp only [key, ofLex_toLex] at this
      omega
    have h3 : (a - (k + 1) : Fin (n + 3)) = b - (k + 1) := Fin.ext h2
    simpa using h3
  -- sort by the key
  let σ := Tuple.sort key
  have hmono : Monotone (key ∘ σ) := Tuple.monotone_sort key
  have hsm : StrictMono (key ∘ σ) :=
    hmono.strictMono_of_injective (hkey_inj.comp σ.injective)
  refine ⟨σ.symm, fun i => ?_⟩
  have hiff : ∀ a b : Fin (n + 3), σ.symm a < σ.symm b ↔ key a < key b := by
    intro a b
    have := hsm.lt_iff_lt (a := σ.symm a) (b := σ.symm b)
    simpa [Function.comp] using this.symm
  rw [hiff]
  -- the key comparison of consecutive candidates
  have ht_inj : Function.Injective t := by
    intro a b h
    have : (a - (k + 1) : Fin (n + 3)) = b - (k + 1) := Fin.ext h
    simpa using this
  by_cases hik : i = k
  · subst hik
    have ht1 : t (i + 1) = 0 := by simp [t]
    have hN1 : N (i + 1) = 0 := by simp [N, ht1]
    -- `N i ≥ 1`, witnessed by `j0`
    have hj0k : j0 ≠ i := fun h => hk (h ▸ hj0)
    have htj : t j0 < t i := by
      have hti : t i = n + 2 := by
        simp only [t]
        rw [sub_succ, sub_self, Fin.coe_sub_one]
        simp
      rw [hti]
      have hle : t j0 < n + 3 := (j0 - (i + 1)).isLt
      have hne : t j0 ≠ n + 2 := by
        intro h
        apply hj0k
        have h1 : (j0 - (i + 1) : Fin (n + 3)) = -1 := by
          apply Fin.ext
          rw [show ((j0 - (i + 1) : Fin (n + 3)) : ℕ) = t j0 from rfl, h]
          simp [Fin.coe_neg_one]
        have := congrArg (· + (i + 1)) h1
        simp only [sub_add_cancel] at this
        rw [this]; abel
      omega
    have hNi : 1 ≤ N i := by
      apply Finset.card_pos.mpr
      refine ⟨j0, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨htj, hj0⟩
    simp only [hk, iff_false, not_lt]
    apply le_of_lt
    show toLex (N (i + 1), -((t (i + 1) : ℕ) : ℤ)) < toLex (N i, -((t i : ℕ) : ℤ))
    rw [Prod.Lex.toLex_lt_toLex, hN1]
    left; omega
  · -- generic step
    have htsucc : t (i + 1) = t i + 1 := by
      simp only [t]
      rw [add_sub_add_right_eq_sub, sub_succ]
      have hd : (i - k : Fin (n + 3)) ≠ 0 := sub_ne_zero.mpr hik
      rw [Fin.coe_sub_one, if_neg hd]
      have : ((i - k : Fin (n + 3)) : ℕ) ≠ 0 := by
        intro h0; exact hd (Fin.ext (by simpa using h0))
      omega
    have hNsucc : N (i + 1) = N i + (if p i then 1 else 0) := by
      simp only [N, htsucc]
      split_ifs with hpi
      · rw [← Finset.card_insert_of_notMem
          (s := Finset.univ.filter (fun x => t x < t i ∧ p x)) (a := i) (by simp)]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
          · exact Or.inr ⟨h, h2⟩
          · exact Or.inl (ht_inj h)
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨Nat.lt_succ_self _, hpi⟩
          · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
      · rw [add_zero]
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
          · exact ⟨h, h2⟩
          · exact absurd (ht_inj h ▸ h2) hpi
        · rintro ⟨h1, h2⟩
          exact ⟨Nat.lt_succ_of_lt h1, h2⟩
    by_cases hpi : p i
    · simp only [hpi, iff_true]
      show toLex (N i, -((t i : ℕ) : ℤ)) < toLex (N (i + 1), -((t (i + 1) : ℕ) : ℤ))
      rw [Prod.Lex.toLex_lt_toLex, hNsucc, if_pos hpi]
      left; omega
    · simp only [hpi, iff_false, not_lt]
      apply le_of_lt
      show toLex (N (i + 1), -((t (i + 1) : ℕ) : ℤ)) < toLex (N i, -((t i : ℕ) : ℤ))
      rw [Prod.Lex.toLex_lt_toLex, hNsucc, if_neg hpi, htsucc]
      right
      refine ⟨by simp, ?_⟩
      push_cast; omega

/-- The reversed cyclic ranking: every `i ≠ k` is preferred to `i + 1`, and `k + 1` to `k`. -/
def rho {n : ℕ} (k : Fin (n + 3)) : Ranking (n + 3) := Equiv.subRight (k + 1)

lemma ell_self {n : ℕ} (i : Fin (n + 3)) : Ranking.Prefers (ell i) i (i + 1) := by
  unfold Ranking.Prefers ell
  simp only [Equiv.subLeft_apply]
  rw [sub_succ, sub_self, lt_sub_one_iff']

lemma ell_other {n : ℕ} (i j : Fin (n + 3)) (h : j ≠ i) :
    Ranking.Prefers (ell j) (i + 1) i := by
  unfold Ranking.Prefers ell
  simp only [Equiv.subLeft_apply]
  rw [sub_succ, sub_one_lt_iff']
  exact sub_ne_zero.mpr h

lemma rho_other {n : ℕ} (i k : Fin (n + 3)) (h : i ≠ k) :
    Ranking.Prefers (rho k) i (i + 1) := by
  unfold Ranking.Prefers rho
  simp only [Equiv.subRight_apply]
  rw [add_sub_add_right_eq_sub, sub_succ, sub_one_lt_iff']
  exact sub_ne_zero.mpr h

lemma rho_self {n : ℕ} (i : Fin (n + 3)) : Ranking.Prefers (rho i) (i + 1) i := by
  unfold Ranking.Prefers rho
  simp only [Equiv.subRight_apply]
  rw [sub_self, sub_succ, sub_self, lt_sub_one_iff']

lemma prefers_or {n : ℕ} (r : Ranking (n + 3)) (i : Fin (n + 3)) :
    Ranking.Prefers r i (i + 1) ∨ Ranking.Prefers r (i + 1) i := by
  unfold Ranking.Prefers
  have hne : r i ≠ r (i + 1) := by
    intro h
    have h' := r.injective h
    have : (1 : Fin (n + 3)) = 0 := by
      have := congrArg (· - i) h'
      simpa using this.symm
    exact absurd this (by simp)
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Mixed signs are impossible. -/
lemma no_mixed {n : ℕ} (lam : ℝ) (hlam : 1 < lam) (w : Fin (n + 3) → Ranking (n + 3) → ℝ)
    (hC1 : ∀ i r s, Ranking.Prefers r i (i + 1) → w i s ≤ lam * w i r)
    (hC2 : ∀ i r s, Ranking.Prefers r (i + 1) i → lam * w i r ≤ w i s)
    (hn : ∀ i, w i (ell i) - w i (ell (i + 1)) = 1)
    (α : Fin (n + 3) → ℝ) (hα : ∀ r, ∑ i, α i * w i r = 0)
    (i0 : Fin (n + 3)) (hi0 : 0 < α i0) (j0 : Fin (n + 3)) (hj0 : α j0 ≤ 0) : False := by
  classical
  have hpos : ∀ i r, Ranking.Prefers r i (i + 1) → 0 ≤ w i r := by
    intro i r h
    have := hC1 i r r h
    nlinarith
  have hneg : ∀ i r, Ranking.Prefers r (i + 1) i → w i r ≤ 0 := by
    intro i r h
    have := hC2 i r r h
    nlinarith
  -- first ranking: exactly the positive coefficients prefer `i` to `i + 1`
  obtain ⟨r, hr⟩ := exists_ranking_pattern (fun i => 0 < α i) ⟨i0, hi0⟩ ⟨j0, not_lt.mpr hj0⟩
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ α i * w i r := by
    intro i _
    by_cases h : 0 < α i
    · exact mul_nonneg h.le (hpos i r ((hr i).mpr h))
    · have h' : Ranking.Prefers r (i + 1) i := by
        rcases prefers_or r i with h1 | h1
        · exact absurd ((hr i).mp h1) h
        · exact h1
      exact mul_nonneg_of_nonpos_of_nonpos (not_lt.mp h) (hneg i r h')
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp (hα r) i0 (Finset.mem_univ _)
  have hw0 : w i0 r = 0 := by
    rcases mul_eq_zero.mp hz with h | h
    · linarith
    · exact h
  have hle : ∀ s, w i0 s ≤ 0 := by
    intro s
    have := hC1 i0 r s ((hr i0).mpr hi0)
    rw [hw0, mul_zero] at this
    exact this
  -- second ranking: the complementary pattern
  obtain ⟨r', hr'⟩ := exists_ranking_pattern (fun i => ¬ 0 < α i) ⟨j0, not_lt.mpr hj0⟩
    ⟨i0, not_not.mpr hi0⟩
  have hterm' : ∀ i ∈ Finset.univ, α i * w i r' ≤ 0 := by
    intro i _
    by_cases h : 0 < α i
    · have h' : Ranking.Prefers r' (i + 1) i := by
        rcases prefers_or r' i with h1 | h1
        · exact absurd h ((hr' i).mp h1)
        · exact h1
      exact mul_nonpos_of_nonneg_of_nonpos h.le (hneg i r' h')
    · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) (hpos i r' ((hr' i).mpr h))
  have hz' := (Finset.sum_eq_zero_iff_of_nonpos hterm').mp (hα r') i0 (Finset.mem_univ _)
  have hw0' : w i0 r' = 0 := by
    rcases mul_eq_zero.mp hz' with h | h
    · linarith
    · exact h
  have hge : ∀ s, 0 ≤ w i0 s := by
    intro s
    have hpr : Ranking.Prefers r' (i0 + 1) i0 := by
      rcases prefers_or r' i0 with h1 | h1
      · exact absurd hi0 ((hr' i0).mp h1)
      · exact h1
    have := hC2 i0 r' s hpr
    rw [hw0', mul_zero] at this
    exact this
  have h1 := hn i0
  have ha := le_antisymm (hle (ell i0)) (hge (ell i0))
  have hb := le_antisymm (hle (ell (i0 + 1))) (hge (ell (i0 + 1)))
  rw [ha, hb] at h1
  norm_num at h1

end CycleDepAux

open CycleDepAux in
theorem solution {m : ℕ} [NeZero m] (hm : 3 ≤ m) (lam : ℝ) (hlam : 1 < lam)
    (W : Submodule ℝ (Ranking m → ℝ)) (hW : Module.finrank ℝ W = m - 1)
    (w : Fin m → Ranking m → ℝ) (hwW : ∀ i, w i ∈ W) (hwC : ∀ i, w i ∈ Cmp lam i (i + 1))
    (hwn : ∀ i, dotProduct (w i) (unitVec (ell i) - unitVec (ell (i + 1))) = 1) :
    (m : ℝ) - 1 ≤ lam := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  -- unpack the hypotheses
  have hC1 : ∀ i r s, Ranking.Prefers r i (i + 1) → w i s ≤ lam * w i r :=
    fun i r s h => (hwC i).1 r s h
  have hC2 : ∀ i r s, Ranking.Prefers r (i + 1) i → lam * w i r ≤ w i s :=
    fun i r s h => (hwC i).2 r s h
  have hn : ∀ i, w i (ell i) - w i (ell (i + 1)) = 1 := by
    intro i
    have := hwn i
    simpa [unitVec, dotProduct_sub, dotProduct_single] using this
  -- linear dependence
  obtain ⟨α, ⟨i1, hi1⟩, hα⟩ : ∃ α : Fin (n + 3) → ℝ, (∃ i, α i ≠ 0) ∧
      ∀ r, ∑ i, α i * w i r = 0 := by
    let v : Fin (n + 3) → W := fun i => ⟨w i, hwW i⟩
    have hnot : ¬ LinearIndependent ℝ v := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [hW, Fintype.card_fin] at this
      omega
    rw [Fintype.not_linearIndependent_iff] at hnot
    obtain ⟨g, hg, i, hi⟩ := hnot
    refine ⟨g, ⟨i, hi⟩, fun r => ?_⟩
    have := congrArg (fun x : W => (x : Ranking (n + 3) → ℝ) r) hg
    simpa [v, Finset.sum_apply] using this
  -- all coefficients have one strict sign
  obtain ⟨β, hβpos, hβ⟩ : ∃ β : Fin (n + 3) → ℝ, (∀ i, 0 < β i) ∧ ∀ r, ∑ i, β i * w i r = 0 := by
    rcases lt_or_gt_of_ne hi1 with h | h
    · refine ⟨fun i => -α i, fun i => ?_, fun r => ?_⟩
      · by_contra hc
        exact no_mixed lam hlam w hC1 hC2 hn (fun i => -α i)
          (fun r => by simp [neg_mul, Finset.sum_neg_distrib, hα r]) i1 (by linarith) i
          (not_lt.mp hc)
      · simp [neg_mul, Finset.sum_neg_distrib, hα r]
    · refine ⟨α, fun i => ?_, hα⟩
      by_contra hc
      exact no_mixed lam hlam w hC1 hC2 hn α hα i1 h i (not_lt.mp hc)
  -- the cyclic and reversed-cyclic evaluations
  set A : Fin (n + 3) → ℝ := fun i => w i (ell i) with hAdef
  set R : Fin (n + 3) → ℝ := fun i => -w i (rho i) with hRdef
  have hF1 : ∀ i j, j ≠ i → R i ≤ lam * (-w i (ell j)) := by
    intro i j h
    have := hC2 i (ell j) (rho i) (ell_other i j h)
    simp only [hRdef]
    linarith
  have hF2 : ∀ i k, i ≠ k → A i ≤ lam * w i (rho k) := by
    intro i k h
    exact hC1 i (rho k) (ell i) (rho_other i k h)
  have hF3 : ∀ i, 1 ≤ A i + lam * R i := by
    intro i
    have h1 := hC2 i (rho i) (ell (i + 1)) (rho_self i)
    have h2 := hn i
    simp only [hAdef, hRdef]
    linarith
  set Asum := ∑ i, β i * A i with hAsum
  set Rsum := ∑ i, β i * R i with hRsum
  have hE1 : ∀ j, Rsum - β j * R j ≤ lam * (β j * A j) := by
    intro j
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => β i * w i (ell j))
      (Finset.mem_univ j)
    rw [hβ (ell j)] at hsplit
    have hle : ∑ i ∈ Finset.univ.erase j, β i * R i ≤
        ∑ i ∈ Finset.univ.erase j, lam * (β i * (-w i (ell j))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : j ≠ i := fun h => (Finset.mem_erase.mp hi).1 (h ▸ rfl)
      have := hF1 i j hij
      have hb := hβpos i
      nlinarith
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j), ← Finset.mul_sum] at hle
    have : ∑ i ∈ Finset.univ.erase j, β i * -w i (ell j) = β j * A j := by
      simp only [mul_neg, Finset.sum_neg_distrib, hAdef]
      linarith
    rw [this] at hle
    exact hle
  have hE2 : ∀ k, Asum - β k * A k ≤ lam * (β k * R k) := by
    intro k
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => β i * w i (rho k))
      (Finset.mem_univ k)
    rw [hβ (rho k)] at hsplit
    have hle : ∑ i ∈ Finset.univ.erase k, β i * A i ≤
        ∑ i ∈ Finset.univ.erase k, lam * (β i * w i (rho k)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≠ k := (Finset.mem_erase.mp hi).1
      have := hF2 i k hik
      have hb := hβpos i
      nlinarith
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ k), ← Finset.mul_sum] at hle
    have : ∑ i ∈ Finset.univ.erase k, β i * w i (rho k) = β k * R k := by
      simp only [hRdef, mul_neg]
      linarith
    rw [this] at hle
    exact hle
  -- sum over all indices
  have hS1 : ((n + 3 : ℕ) : ℝ) * Rsum - Rsum ≤ lam * Asum := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hE1 j)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum, nsmul_eq_mul] at this
    linarith
  have hS2 : ((n + 3 : ℕ) : ℝ) * Asum - Asum ≤ lam * Rsum := by
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hE2 j)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Finset.mul_sum, nsmul_eq_mul] at this
    linarith
  have hpos3 : 0 < Asum + lam * Rsum := by
    have : ∑ i, β i * (A i + lam * R i) ≥ ∑ i, β i * 1 :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hF3 i) (hβpos i).le)
    have hb : 0 < ∑ i, β i * 1 := by
      simp only [mul_one]
      exact Finset.sum_pos (fun i _ => hβpos i) Finset.univ_nonempty
    have : ∑ i, β i * (A i + lam * R i) = Asum + lam * Rsum := by
      rw [hAsum, hRsum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    linarith
  have hm1 : (2 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hApos : 0 < Asum := by
    by_contra hc
    push Not at hc
    have : (((n + 3 : ℕ) : ℝ) - 1) * Rsum ≤ lam * Asum := by linarith
    have hl0 : lam * Asum ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hc
    have hR : Rsum ≤ 0 := by nlinarith
    nlinarith
  -- conclude `(m-1)^2 ≤ lam^2`
  set c := ((n + 3 : ℕ) : ℝ) - 1 with hc
  have h1 : c * Rsum ≤ lam * Asum := by linarith
  have h2 : c * Asum ≤ lam * Rsum := by linarith
  have hRnn : 0 ≤ Rsum := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have key : c * c * Asum ≤ lam * lam * Asum := by
    calc c * c * Asum = c * (c * Asum) := by ring
      _ ≤ c * (lam * Rsum) := by apply mul_le_mul_of_nonneg_left h2; linarith
      _ = lam * (c * Rsum) := by ring
      _ ≤ lam * (lam * Asum) := by apply mul_le_mul_of_nonneg_left h1; linarith
      _ = lam * lam * Asum := by ring
  have hsq : c * c ≤ lam * lam := le_of_mul_le_mul_right key hApos
  push_cast at hc ⊢
  nlinarith
