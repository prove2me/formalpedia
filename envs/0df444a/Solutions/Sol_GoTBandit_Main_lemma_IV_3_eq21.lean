-- Prove2me | solution 1 for GoTBandit.Main.lemma_IV_3_eq21
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T01:21:37.798552+00:00
-- url     : https://prove2.me/submissions/651f7205-f2c0-4b8c-bd7e-9a8e2f5c4e05

import Mathlib
import Definitions.Def_GoTBandit_Main_Algorithm
import Theorems.Thm_GoTBandit_Main_lemma_IV_3_eq20

open Finset MeasureTheory ProbabilityTheory

namespace GoTIV321

/-- Geometric tail: `∑_{j ≤ ⌊k/2⌋} e^{-A (k-j)} ≤ e^{-(A/2) k} / (1 - e^{-A})`. -/
theorem geo_tail (A : ℝ) (hA : 0 < A) (k : ℕ) :
    ∑ j ∈ range (k / 2 + 1), Real.exp (-A * ((k - j : ℕ) : ℝ)) ≤
      Real.exp (-(A / 2) * k) / (1 - Real.exp (-A)) := by
  set m := k / 2 with hm
  set q := Real.exp (-A) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.2 (by linarith)
  have hmk : m ≤ k := Nat.div_le_self _ _
  have h2m : 2 * m ≤ k := by omega
  -- rewrite each term
  have hterm : ∀ j ∈ range (m + 1), Real.exp (-A * ((k - j : ℕ) : ℝ)) =
      Real.exp (-A * ((k - m : ℕ) : ℝ)) * q ^ (m - j) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rw [hq, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    rw [Nat.cast_sub (le_trans hjm hmk), Nat.cast_sub hmk, Nat.cast_sub hjm]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hrefl : ∑ j ∈ range (m + 1), q ^ (m - j) = ∑ j ∈ range (m + 1), q ^ j := by
    have := Finset.sum_range_reflect (fun j => q ^ j) (m + 1)
    simpa using this
  rw [hrefl, geom_sum_eq (ne_of_lt hq1)]
  have hgs : (q ^ (m + 1) - 1) / (q - 1) ≤ 1 / (1 - q) := by
    rw [show (q ^ (m + 1) - 1) / (q - 1) = (1 - q ^ (m + 1)) / (1 - q) by
      rw [← neg_div_neg_eq]; ring_nf]
    apply div_le_div_of_nonneg_right _ (by linarith)
    linarith [pow_nonneg hq0 (m + 1)]
  have hexp : Real.exp (-A * ((k - m : ℕ) : ℝ)) ≤ Real.exp (-(A / 2) * k) := by
    apply Real.exp_le_exp.2
    rw [Nat.cast_sub hmk]
    have : (2 * m : ℝ) ≤ k := by exact_mod_cast h2m
    nlinarith
  calc Real.exp (-A * ((k - m : ℕ) : ℝ)) * ((q ^ (m + 1) - 1) / (q - 1))
      ≤ Real.exp (-(A / 2) * k) * (1 / (1 - q)) := by
        apply mul_le_mul hexp hgs _ (Real.exp_pos _).le
        rw [show (q ^ (m + 1) - 1) / (q - 1) = (1 - q ^ (m + 1)) / (1 - q) by
          rw [← neg_div_neg_eq]; ring_nf]
        apply div_nonneg _ (by linarith)
        have : q ^ (m + 1) ≤ 1 := pow_le_one₀ hq0 hq1.le
        linarith
    _ = Real.exp (-(A / 2) * k) / (1 - Real.exp (-A)) := by rw [hq]; ring

end GoTIV321

open GoTBandit.Main GoTIV321

theorem solution {N M : ℕ} (hNM : N ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin N → Fin M → ℕ → Ω → ℝ) (μ σ2 b : Fin N → Fin M → ℝ)
    (hr : IIDRewards P r μ σ2 b) (ξ : Fin N → ℕ → Fin 4 → Ω → ℝ) (hξ : Seeds P r ξ)
    (p : GoTParams) (hc1 : 0 < p.c1) (hδ : 0 < p.δ) (hΔ : 0 < Δmin μ)
    (k : ℕ) (hk : 1 ≤ k) :
    P.real {ω | ∃ j ≤ k / 2,
        Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ (k - j) n i ω - μ n i|} ≤
      2 * N * M / (1 - Real.exp (-(wConst μ (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) (⨆ n, ⨆ i, b n i)) *
            p.c1 * ((k : ℝ) / 4) ^ p.δ)) *
          Real.exp (-(wConst μ (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) (⨆ n, ⨆ i, b n i) / 2) *
            p.c1 * ((k : ℝ) / 4) ^ p.δ * k) +
        N * M / (1 - Real.exp (-(1 / (36 * (M : ℝ) ^ 2)) * p.c1 * ((k : ℝ) / 4) ^ p.δ)) *
          Real.exp (-(1 / (72 * (M : ℝ) ^ 2)) * p.c1 * ((k : ℝ) / 4) ^ p.δ * k) := by
  set w := wConst μ (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) (⨆ n, ⨆ i, b n i) with hw
  -- N ≥ 1 and M ≥ 1
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h
      exfalso
      have : Δmin μ = 0 := by
        unfold Δmin
        have : {d : ℝ | ∃ (n : Fin 0) (a₁ a₂ : Fin 0 → Fin M),
            gUtil μ a₁ n ≠ gUtil μ a₂ n ∧ d = |gUtil μ a₁ n - gUtil μ a₂ n|} = ∅ := by
          ext d; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨n, -⟩; exact n.elim0
        rw [this, Real.sInf_empty]
      linarith
    · exact h
  have hM : 0 < M := lt_of_lt_of_le hN hNM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- w > 0
  have hbmax : 0 < ⨆ n, ⨆ i, b n i := by
    have h1 : b ⟨0, hN⟩ ⟨0, hM⟩ ≤ ⨆ i, b ⟨0, hN⟩ i := le_ciSup (Finite.bddAbove_range _) _
    have h2 : (⨆ i, b ⟨0, hN⟩ i) ≤ ⨆ n, ⨆ i, b n i :=
      le_ciSup (f := fun n => ⨆ i, b n i) (Finite.bddAbove_range _) _
    linarith [hr.b_pos ⟨0, hN⟩ ⟨0, hM⟩]
  have hwpos : 0 < w := by
    rw [hw]; unfold wConst
    apply div_pos (pow_pos hΔ 2)
    have : 0 < 4 * (⨆ n, ⨆ i, Real.sqrt (σ2 n i)) ^ 2 + (⨆ n, ⨆ i, b n i) * Δmin μ := by
      have := mul_pos hbmax hΔ
      nlinarith [sq_nonneg (⨆ n, ⨆ i, Real.sqrt (σ2 n i))]
    positivity
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk4 : 0 < ((k : ℝ) / 4) ^ p.δ := Real.rpow_pos_of_pos (by linarith) _
  have hc1r : (0 : ℝ) < p.c1 := by exact_mod_cast hc1
  set A := w * p.c1 * ((k : ℝ) / 4) ^ p.δ with hA
  set B := (1 / (36 * (M : ℝ) ^ 2)) * p.c1 * ((k : ℝ) / 4) ^ p.δ with hB
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  -- per-epoch bound
  have hper : ∀ j ∈ range (k / 2 + 1),
      P.real {ω | Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ (k - j) n i ω - μ n i|} ≤
        2 * N * M * Real.exp (-A * ((k - j : ℕ) : ℝ)) +
          N * M * Real.exp (-B * ((k - j : ℕ) : ℝ)) := by
    intro j hj
    have hjm : j ≤ k / 2 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hjk : j ≤ k := le_trans hjm (Nat.div_le_self _ _)
    have hk1 : 1 ≤ k - j := by omega
    have h20 := lemma_IV_3_eq20 hNM P r μ σ2 b hr ξ hξ p hc1 hδ (k - j) hk1
    refine le_trans h20 ?_
    have hkj : (k : ℝ) / 4 ≤ ((k - j : ℕ) : ℝ) / 2 := by
      rw [Nat.cast_sub hjk]
      have : (2 * j : ℝ) ≤ k := by exact_mod_cast (show 2 * j ≤ k by omega)
      linarith
    have hpow : ((k : ℝ) / 4) ^ p.δ ≤ (((k - j : ℕ) : ℝ) / 2) ^ p.δ :=
      Real.rpow_le_rpow (by positivity) hkj hδ.le
    have hk' : (0 : ℝ) ≤ ((k - j : ℕ) : ℝ) := Nat.cast_nonneg _
    have e1 : Real.exp (-w * p.c1 * ((((k - j : ℕ) : ℝ)) / 2) ^ p.δ * ((k - j : ℕ) : ℝ)) ≤
        Real.exp (-A * ((k - j : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.2
      have : w * p.c1 * ((k : ℝ) / 4) ^ p.δ * ((k - j : ℕ) : ℝ) ≤
          w * p.c1 * ((((k - j : ℕ) : ℝ)) / 2) ^ p.δ * ((k - j : ℕ) : ℝ) := by gcongr
      rw [hA]; linarith
    have e2 : Real.exp (-((p.c1 : ℝ) * ((((k - j : ℕ) : ℝ)) / 2) ^ p.δ / (36 * (M : ℝ) ^ 2)) *
        ((k - j : ℕ) : ℝ)) ≤ Real.exp (-B * ((k - j : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.2
      have : (1 / (36 * (M : ℝ) ^ 2)) * p.c1 * ((k : ℝ) / 4) ^ p.δ * ((k - j : ℕ) : ℝ) ≤
          (1 / (36 * (M : ℝ) ^ 2)) * p.c1 * ((((k - j : ℕ) : ℝ)) / 2) ^ p.δ *
            ((k - j : ℕ) : ℝ) := by gcongr
      rw [hB]
      have e : (p.c1 : ℝ) * ((((k - j : ℕ) : ℝ)) / 2) ^ p.δ / (36 * (M : ℝ) ^ 2) =
          (1 / (36 * (M : ℝ) ^ 2)) * p.c1 * ((((k - j : ℕ) : ℝ)) / 2) ^ p.δ := by ring
      rw [e]; linarith
    have hNM0 : (0 : ℝ) ≤ N * M := by positivity
    have := mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 2 * N * M)
    have := mul_le_mul_of_nonneg_left e2 hNM0
    linarith
  have hset : {ω | ∃ j ≤ k / 2,
        Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ (k - j) n i ω - μ n i|} =
      ⋃ j ∈ range (k / 2 + 1),
        {ω | Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ (k - j) n i ω - μ n i|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩
    · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩
  rw [hset]
  have gA := geo_tail A hApos k
  have gB := geo_tail B hBpos k
  calc P.real (⋃ j ∈ range (k / 2 + 1),
        {ω | Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ (k - j) n i ω - μ n i|})
      ≤ ∑ j ∈ range (k / 2 + 1),
        P.real {ω | Δmin μ / 4 < ⨆ n, ⨆ i, |est p hNM r ξ (k - j) n i ω - μ n i|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ range (k / 2 + 1), (2 * N * M * Real.exp (-A * ((k - j : ℕ) : ℝ)) +
          N * M * Real.exp (-B * ((k - j : ℕ) : ℝ))) := Finset.sum_le_sum hper
    _ = 2 * N * M * ∑ j ∈ range (k / 2 + 1), Real.exp (-A * ((k - j : ℕ) : ℝ)) +
          N * M * ∑ j ∈ range (k / 2 + 1), Real.exp (-B * ((k - j : ℕ) : ℝ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * N * M * (Real.exp (-(A / 2) * k) / (1 - Real.exp (-A))) +
          N * M * (Real.exp (-(B / 2) * k) / (1 - Real.exp (-B))) := by
        gcongr
    _ = _ := by
        have e1 : -(A / 2) * (k : ℝ) = -(w / 2) * p.c1 * ((k : ℝ) / 4) ^ p.δ * k := by
          rw [hA]; ring
        have e2 : -A = -w * p.c1 * ((k : ℝ) / 4) ^ p.δ := by rw [hA]; ring
        have e3 : -(B / 2) * (k : ℝ) =
            -(1 / (72 * (M : ℝ) ^ 2)) * p.c1 * ((k : ℝ) / 4) ^ p.δ * k := by
          rw [hB]; field_simp; ring
        have e4 : -B = -(1 / (36 * (M : ℝ) ^ 2)) * p.c1 * ((k : ℝ) / 4) ^ p.δ := by
          rw [hB]; ring
        rw [e1, e2, e3, e4]
        ring
