-- Prove2me | solution 1 for Komlos.spencer_random_finish
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-09T12:06:32.754581+00:00
-- url     : https://prove2.me/submissions/a6487bda-ff92-4963-98c0-25832ebeabfd

import Mathlib

open Finset Real

namespace SpencerAux

/-- The `±1` value attached to a boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> simp [sgn]

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by
  cases b <;> norm_num [sgn]

variable {n : ℕ}

/-- The exponential moment of a Rademacher sum, as a counting identity. -/
lemma sum_exp_prod (T : Finset (Fin n)) (a : Fin n → ℝ) (lam : ℝ) :
    ∑ σ : Fin n → Bool, Real.exp (lam * ∑ j ∈ T, a j * sgn (σ j))
      = ∏ j : Fin n, (if j ∈ T then Real.exp (lam * a j) + Real.exp (-(lam * a j)) else 2) := by
  classical
  have hfun : ∀ σ : Fin n → Bool,
      Real.exp (lam * ∑ j ∈ T, a j * sgn (σ j))
        = ∏ j : Fin n, (if j ∈ T then Real.exp (lam * a j * sgn (σ j)) else 1) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    rw [← Finset.prod_filter]
    congr 1
    · simp
    · funext j
      ring_nf
  calc ∑ σ : Fin n → Bool, Real.exp (lam * ∑ j ∈ T, a j * sgn (σ j))
      = ∑ σ : Fin n → Bool,
          ∏ j : Fin n, (if j ∈ T then Real.exp (lam * a j * sgn (σ j)) else 1) := by
        exact Finset.sum_congr rfl fun σ _ => hfun σ
    _ = ∏ j : Fin n, ∑ b : Bool, (if j ∈ T then Real.exp (lam * a j * sgn b) else 1) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ j : Fin n, (if j ∈ T then Real.exp (lam * a j) + Real.exp (-(lam * a j)) else 2) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j ∈ T
        · simp [hj, sgn]
        · simp [hj]

/-- The product of the one-step moments is at most `2^n exp(λ²S/2)`. -/
lemma prod_le (T : Finset (Fin n)) (a : Fin n → ℝ) (lam : ℝ) :
    ∏ j : Fin n, (if j ∈ T then Real.exp (lam * a j) + Real.exp (-(lam * a j)) else 2)
      ≤ 2 ^ n * Real.exp (lam ^ 2 / 2 * ∑ j ∈ T, (a j) ^ 2) := by
  classical
  have hterm : ∀ j : Fin n,
      (if j ∈ T then Real.exp (lam * a j) + Real.exp (-(lam * a j)) else 2)
        ≤ 2 * Real.exp (if j ∈ T then lam ^ 2 / 2 * (a j) ^ 2 else 0) := by
    intro j
    by_cases hj : j ∈ T
    · have h := Real.cosh_le_exp_half_sq (lam * a j)
      rw [Real.cosh_eq] at h
      have h2 : Real.exp (lam * a j) + Real.exp (-(lam * a j))
          ≤ 2 * Real.exp ((lam * a j) ^ 2 / 2) := by
        nlinarith [h]
      simpa [hj, mul_pow] using
        (by
          have : (lam * a j) ^ 2 / 2 = lam ^ 2 / 2 * (a j) ^ 2 := by ring
          rwa [this] at h2)
    · simp [hj]
  have hnonneg : ∀ j : Fin n,
      (0:ℝ) ≤ (if j ∈ T then Real.exp (lam * a j) + Real.exp (-(lam * a j)) else 2) := by
    intro j; by_cases hj : j ∈ T <;> simp [hj] <;> positivity
  calc ∏ j : Fin n, (if j ∈ T then Real.exp (lam * a j) + Real.exp (-(lam * a j)) else 2)
      ≤ ∏ j : Fin n, (2 * Real.exp (if j ∈ T then lam ^ 2 / 2 * (a j) ^ 2 else 0)) :=
        Finset.prod_le_prod (fun j _ => hnonneg j) (fun j _ => hterm j)
    _ = 2 ^ n * Real.exp (∑ j : Fin n, (if j ∈ T then lam ^ 2 / 2 * (a j) ^ 2 else 0)) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum]
        simp
    _ = 2 ^ n * Real.exp (lam ^ 2 / 2 * ∑ j ∈ T, (a j) ^ 2) := by
        congr 2
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

/-- One-sided counting Chernoff bound. -/
lemma card_ge_le (T : Finset (Fin n)) (a : Fin n → ℝ) (u : ℝ) (hu : 0 < u)
    (S : ℝ) (hS : 0 < S) (hSa : ∑ j ∈ T, (a j) ^ 2 ≤ S) :
    ((Finset.univ.filter
        (fun σ : Fin n → Bool => u ≤ ∑ j ∈ T, a j * sgn (σ j))).card : ℝ)
      ≤ 2 ^ n * Real.exp (-(u ^ 2) / (2 * S)) := by
  classical
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = u / S := ⟨u / S, rfl⟩
  have hlam0 : 0 < lam := by rw [hlamdef]; exact div_pos hu hS
  set B := Finset.univ.filter
      (fun σ : Fin n → Bool => u ≤ ∑ j ∈ T, a j * sgn (σ j)) with hB
  set g : (Fin n → Bool) → ℝ :=
    fun σ => Real.exp (-(lam * u)) * Real.exp (lam * ∑ j ∈ T, a j * sgn (σ j)) with hg
  have hone : ∀ σ ∈ B, (1 : ℝ) ≤ g σ := by
    intro σ hσ
    have hσ' : u ≤ ∑ j ∈ T, a j * sgn (σ j) := by
      simpa [hB] using hσ
    have : Real.exp 0 ≤ Real.exp (-(lam * u) + lam * ∑ j ∈ T, a j * sgn (σ j)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    simpa [hg, ← Real.exp_add] using this
  have h1 : (B.card : ℝ) ≤ ∑ σ ∈ B, g σ := by
    have := Finset.card_nsmul_le_sum B g 1 hone
    simpa using this
  have h2 : ∑ σ ∈ B, g σ ≤ ∑ σ : Fin n → Bool, g σ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro σ _ _
    positivity
  have h3 : ∑ σ : Fin n → Bool, g σ
      = Real.exp (-(lam * u)) *
        ∏ j : Fin n, (if j ∈ T then Real.exp (lam * a j) + Real.exp (-(lam * a j)) else 2) := by
    rw [hg, ← Finset.mul_sum, sum_exp_prod]
  have h4 : ∏ j : Fin n, (if j ∈ T then Real.exp (lam * a j) + Real.exp (-(lam * a j)) else 2)
      ≤ 2 ^ n * Real.exp (lam ^ 2 / 2 * S) := by
    refine (prod_le T a lam).trans ?_
    have : Real.exp (lam ^ 2 / 2 * ∑ j ∈ T, (a j) ^ 2) ≤ Real.exp (lam ^ 2 / 2 * S) := by
      apply Real.exp_le_exp.mpr
      have h0 : (0:ℝ) ≤ lam ^ 2 / 2 := by positivity
      exact mul_le_mul_of_nonneg_left hSa h0
    have h2n : (0:ℝ) ≤ 2 ^ n := by positivity
    exact mul_le_mul_of_nonneg_left this h2n
  have h5 : Real.exp (-(lam * u)) * (2 ^ n * Real.exp (lam ^ 2 / 2 * S))
      = 2 ^ n * Real.exp (-(u ^ 2) / (2 * S)) := by
    have hkey : -(lam * u) + lam ^ 2 / 2 * S = -(u ^ 2) / (2 * S) := by
      rw [hlamdef]
      field_simp
      ring
    rw [show Real.exp (-(lam * u)) * (2 ^ n * Real.exp (lam ^ 2 / 2 * S))
        = 2 ^ n * (Real.exp (-(lam * u)) * Real.exp (lam ^ 2 / 2 * S)) by ring,
      ← Real.exp_add, hkey]
  calc (B.card : ℝ) ≤ ∑ σ ∈ B, g σ := h1
    _ ≤ ∑ σ : Fin n → Bool, g σ := h2
    _ = Real.exp (-(lam * u)) *
        ∏ j : Fin n, (if j ∈ T then Real.exp (lam * a j) + Real.exp (-(lam * a j)) else 2) := h3
    _ ≤ Real.exp (-(lam * u)) * (2 ^ n * Real.exp (lam ^ 2 / 2 * S)) := by
        exact mul_le_mul_of_nonneg_left h4 (Real.exp_nonneg _)
    _ = 2 ^ n * Real.exp (-(u ^ 2) / (2 * S)) := h5

/-- Two-sided counting Chernoff bound. -/
lemma card_abs_ge_le (T : Finset (Fin n)) (a : Fin n → ℝ) (u : ℝ) (hu : 0 < u)
    (S : ℝ) (hS : 0 < S) (hSa : ∑ j ∈ T, (a j) ^ 2 ≤ S) :
    ((Finset.univ.filter
        (fun σ : Fin n → Bool => u ≤ |∑ j ∈ T, a j * sgn (σ j)|)).card : ℝ)
      ≤ 2 * (2 ^ n * Real.exp (-(u ^ 2) / (2 * S))) := by
  classical
  have hsub : (Finset.univ.filter
      (fun σ : Fin n → Bool => u ≤ |∑ j ∈ T, a j * sgn (σ j)|))
      ⊆ (Finset.univ.filter (fun σ : Fin n → Bool => u ≤ ∑ j ∈ T, a j * sgn (σ j)))
        ∪ (Finset.univ.filter (fun σ : Fin n → Bool => u ≤ ∑ j ∈ T, (-a j) * sgn (σ j))) := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have hneg : ∑ j ∈ T, (-a j) * sgn (σ j) = -∑ j ∈ T, a j * sgn (σ j) := by
      simp [neg_mul]
    by_cases hpos : 0 ≤ ∑ j ∈ T, a j * sgn (σ j)
    · refine Finset.mem_union_left _ ?_
      have hle : u ≤ ∑ j ∈ T, a j * sgn (σ j) := by
        rwa [abs_of_nonneg hpos] at hσ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
    · push_neg at hpos
      refine Finset.mem_union_right _ ?_
      have hle : u ≤ ∑ j ∈ T, (-a j) * sgn (σ j) := by
        rw [hneg]
        rwa [abs_of_neg hpos] at hσ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
      (Finset.univ.filter (fun σ : Fin n → Bool => u ≤ ∑ j ∈ T, a j * sgn (σ j)))
      (Finset.univ.filter (fun σ : Fin n → Bool => u ≤ ∑ j ∈ T, (-a j) * sgn (σ j)))
  have hS2 : ∑ j ∈ T, (-a j) ^ 2 ≤ S := by
    simpa using hSa
  have h1 := card_ge_le T a u hu S hS hSa
  have h2 := card_ge_le T (fun j => -a j) u hu S hS hS2
  have : ((Finset.univ.filter
      (fun σ : Fin n → Bool => u ≤ |∑ j ∈ T, a j * sgn (σ j)|)).card : ℝ)
      ≤ ((Finset.univ.filter (fun σ : Fin n → Bool => u ≤ ∑ j ∈ T, a j * sgn (σ j))).card : ℝ)
        + ((Finset.univ.filter
            (fun σ : Fin n → Bool => u ≤ ∑ j ∈ T, (-a j) * sgn (σ j))).card : ℝ) := by
    exact_mod_cast le_trans hcard hunion
  linarith

end SpencerAux

open SpencerAux in
/-- The union-bound colouring of a residual set of columns. -/
theorem solution
    (n : ℕ) (hn : 0 < n) (A : Fin n → Fin n → ℝ) (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (T : Finset (Fin n)) :
    ∃ χ : Fin n → ℝ,
      (∀ j, j ∈ T → (χ j = 1 ∨ χ j = -1)) ∧
      (∀ j, j ∉ T → χ j = 0) ∧
      (∀ i, |∑ j ∈ T, A i j * χ j|
          ≤ Real.sqrt (2 * (T.card : ℝ) * Real.log (4 * n))) := by
  classical
  by_cases ht0 : T.card = 0
  · have hTe : T = ∅ := Finset.card_eq_zero.mp ht0
    refine ⟨fun _ => 0, ?_, fun j _ => rfl, ?_⟩
    · intro j hj; rw [hTe] at hj; simp at hj
    · intro i; simp [hTe]
  · have htpos : 0 < T.card := Nat.pos_of_ne_zero ht0
    have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hlog : 0 < Real.log (4 * n) := by
      apply Real.log_pos; linarith
    have htR : (0:ℝ) < (T.card : ℝ) := by exact_mod_cast htpos
    have harg : (0:ℝ) ≤ 2 * (T.card : ℝ) * Real.log (4 * n) := by positivity
    set u : ℝ := Real.sqrt (2 * (T.card : ℝ) * Real.log (4 * n)) with hudef
    have hu2 : u ^ 2 = 2 * (T.card : ℝ) * Real.log (4 * n) := Real.sq_sqrt harg
    have hupos : 0 < u := Real.sqrt_pos.mpr (by positivity)
    set Bad : Fin n → Finset (Fin n → Bool) := fun i =>
      Finset.univ.filter (fun σ => u ≤ |∑ j ∈ T, A i j * sgn (σ j)|) with hBad
    have hexp : Real.exp (-(u ^ 2) / (2 * (T.card : ℝ))) = (4 * (n:ℝ))⁻¹ := by
      have : -(u ^ 2) / (2 * (T.card : ℝ)) = -Real.log (4 * n) := by
        rw [hu2]; field_simp
      rw [this, Real.exp_neg, Real.exp_log (by linarith)]
    have hcard_i : ∀ i, ((Bad i).card : ℝ) ≤ 2 ^ n / (2 * (n:ℝ)) := by
      intro i
      have hSle : ∑ j ∈ T, (A i j) ^ 2 ≤ (T.card : ℝ) := by
        calc ∑ j ∈ T, (A i j) ^ 2 ≤ ∑ _j ∈ T, (1:ℝ) := by
              refine Finset.sum_le_sum fun j _ => ?_
              rcases h01 i j with h | h <;> simp [h]
          _ = (T.card : ℝ) := by simp
      have hb := card_abs_ge_le T (A i) u hupos (T.card : ℝ) htR hSle
      rw [hexp] at hb
      calc ((Bad i).card : ℝ) ≤ 2 * (2 ^ n * (4 * (n:ℝ))⁻¹) := hb
        _ = 2 ^ n / (2 * (n:ℝ)) := by field_simp; ring
    have hUnion : ((Finset.univ.biUnion Bad).card : ℝ) ≤ (n:ℝ) * (2 ^ n / (2 * (n:ℝ))) := by
      have h1 : (Finset.univ.biUnion Bad).card ≤ ∑ i : Fin n, (Bad i).card :=
        Finset.card_biUnion_le
      have h2 : ((∑ i : Fin n, (Bad i).card : ℕ) : ℝ) ≤ (n:ℝ) * (2 ^ n / (2 * (n:ℝ))) := by
        push_cast
        calc ∑ i : Fin n, ((Bad i).card : ℝ) ≤ ∑ _i : Fin n, 2 ^ n / (2 * (n:ℝ)) :=
              Finset.sum_le_sum fun i _ => hcard_i i
          _ = (n:ℝ) * (2 ^ n / (2 * (n:ℝ))) := by simp [mul_comm]
      exact le_trans (by exact_mod_cast h1) h2
    have hlt : ((Finset.univ.biUnion Bad).card : ℝ) < 2 ^ n := by
      have hn0 : (n:ℝ) ≠ 0 := by linarith
      have : (n:ℝ) * (2 ^ n / (2 * (n:ℝ))) = 2 ^ n / 2 := by field_simp
      rw [this] at hUnion
      have h2n : (0:ℝ) < 2 ^ n := by positivity
      linarith
    have hex : ∃ σ : Fin n → Bool, σ ∉ Finset.univ.biUnion Bad := by
      by_contra hcon
      push_neg at hcon
      have hsub : (Finset.univ : Finset (Fin n → Bool)) ⊆ Finset.univ.biUnion Bad :=
        fun σ _ => hcon σ
      have hcard := Finset.card_le_card hsub
      have huniv : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
        simp [Finset.card_univ]
      rw [huniv] at hcard
      have : ((2:ℝ) ^ n) ≤ ((Finset.univ.biUnion Bad).card : ℝ) := by exact_mod_cast hcard
      linarith
    obtain ⟨σ, hσ⟩ := hex
    refine ⟨fun j => if j ∈ T then sgn (σ j) else 0, ?_, ?_, ?_⟩
    · intro j hj
      simp only [hj, if_true]
      cases hb : σ j <;> simp [sgn, hb]
    · intro j hj
      simp [hj]
    · intro i
      have hnb : σ ∉ Bad i := by
        intro hc
        exact hσ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hc⟩)
      have hlt' : |∑ j ∈ T, A i j * sgn (σ j)| < u := by
        by_contra hcon
        push_neg at hcon
        exact hnb (by simp [hBad, hcon])
      have hsum : ∑ j ∈ T, A i j * (if j ∈ T then sgn (σ j) else 0)
          = ∑ j ∈ T, A i j * sgn (σ j) :=
        Finset.sum_congr rfl fun j hj => by simp [hj]
      rw [hsum]
      exact le_of_lt hlt'
