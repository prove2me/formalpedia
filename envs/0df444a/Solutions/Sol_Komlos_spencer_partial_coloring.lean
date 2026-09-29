-- Prove2me | solution 1 for Komlos.spencer_partial_coloring
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-11T03:27:38.466874+00:00
-- url     : https://prove2.me/submissions/37868f06-eb25-47cc-89fc-3c1b0045ef7c

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

namespace SpencerEnt

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- The probability of the fibre of `Y` over `b`, for the uniform measure on `Ω`. -/
noncomputable def pr {β : Type} [DecidableEq β] (Y : Ω → β) (b : β) : ℝ :=
  ((Finset.univ.filter (fun ω => Y ω = b)).card : ℝ) / (Fintype.card Ω : ℝ)

/-- Shannon entropy in bits, summed over the image of `Y`. -/
noncomputable def ent {β : Type} [DecidableEq β] (Y : Ω → β) : ℝ :=
  ∑ b ∈ Finset.image Y Finset.univ, pr Y b * Real.logb 2 (1 / pr Y b)

variable {β : Type} [DecidableEq β]

lemma pr_nonneg (Y : Ω → β) (b : β) : 0 ≤ pr Y b := by
  unfold pr; positivity

lemma pr_pos_of_mem_image [Nonempty Ω] {Y : Ω → β} {b : β}
    (hb : b ∈ Finset.image Y Finset.univ) : 0 < pr Y b := by
  obtain ⟨ω, -, hω⟩ := Finset.mem_image.mp hb
  have hcard : 0 < (Finset.univ.filter (fun ω' => Y ω' = b)).card := by
    refine Finset.card_pos.mpr ⟨ω, ?_⟩
    simp [hω]
  have h1 : (0:ℝ) < ((Finset.univ.filter (fun ω' => Y ω' = b)).card : ℝ) := by
    exact_mod_cast hcard
  have h2 : (0:ℝ) < (Fintype.card Ω : ℝ) := by
    have := Fintype.card_pos (α := Ω)
    exact_mod_cast this
  unfold pr
  positivity

lemma sum_pr [Nonempty Ω] (Y : Ω → β) :
    ∑ b ∈ Finset.image Y Finset.univ, pr Y b = 1 := by
  have hcard : (Fintype.card Ω)
      = ∑ b ∈ Finset.image Y Finset.univ,
          (Finset.univ.filter (fun ω => Y ω = b)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun ω _ => Finset.mem_image_of_mem Y (Finset.mem_univ ω))
  have h2 : (0:ℝ) < (Fintype.card Ω : ℝ) := by
    have := Fintype.card_pos (α := Ω); exact_mod_cast this
  unfold pr
  rw [← Finset.sum_div]
  rw [div_eq_one_iff_eq (ne_of_gt h2)]
  exact_mod_cast hcard.symm

/-- Some fibre has probability at least `2 ^ (-H)`. -/
lemma exists_fibre_large [Nonempty Ω] (Y : Ω → β) :
    ∃ b : β, (2 : ℝ) ^ (-(ent Y)) ≤ pr Y b := by
  classical
  have hne : (Finset.image Y Finset.univ).Nonempty := by
    obtain ⟨ω⟩ := ‹Nonempty Ω›
    exact ⟨Y ω, Finset.mem_image_of_mem Y (Finset.mem_univ ω)⟩
  obtain ⟨b₀, hb₀mem, hb₀⟩ := Finset.exists_max_image (Finset.image Y Finset.univ) (pr Y) hne
  have hpos : 0 < pr Y b₀ := pr_pos_of_mem_image hb₀mem
  -- entropy is at least log₂(1/pr b₀)
  have hle : Real.logb 2 (1 / pr Y b₀) ≤ ent Y := by
    have hterm : ∀ b ∈ Finset.image Y Finset.univ,
        pr Y b * Real.logb 2 (1 / pr Y b₀) ≤ pr Y b * Real.logb 2 (1 / pr Y b) := by
      intro b hb
      have hbpos : 0 < pr Y b := pr_pos_of_mem_image hb
      have hble : pr Y b ≤ pr Y b₀ := hb₀ b hb
      have : Real.logb 2 (1 / pr Y b₀) ≤ Real.logb 2 (1 / pr Y b) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity)
          (one_div_le_one_div_of_le hbpos hble)
      exact mul_le_mul_of_nonneg_left this (le_of_lt hbpos)
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul, sum_pr Y, one_mul] at hsum
    exact hsum
  refine ⟨b₀, ?_⟩
  -- from logb 2 (1/p) ≤ H we get 2^(-H) ≤ p
  have h1 : (1 : ℝ) / pr Y b₀ ≤ (2:ℝ) ^ (ent Y) := by
    have hstep : (2:ℝ) ^ (Real.logb 2 (1 / pr Y b₀)) ≤ (2:ℝ) ^ (ent Y) :=
      (Real.rpow_le_rpow_left_iff (by norm_num)).mpr hle
    rwa [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)] at hstep
  have h2 : (2:ℝ) ^ (-(ent Y)) = ((2:ℝ) ^ (ent Y))⁻¹ := by
    rw [Real.rpow_neg (by norm_num)]
  rw [h2]
  rw [inv_le_comm₀ (by positivity) hpos]
  simpa [one_div] using h1

/-- Gibbs' inequality: the entropy is at most the cross entropy. -/
lemma gibbs {S : Finset β} (p q : β → ℝ)
    (hp0 : ∀ b ∈ S, 0 ≤ p b) (hq0 : ∀ b ∈ S, 0 < q b)
    (hp1 : ∑ b ∈ S, p b = 1) (hq1 : ∑ b ∈ S, q b ≤ 1) :
    ∑ b ∈ S, p b * Real.logb 2 (1 / p b) ≤ ∑ b ∈ S, p b * Real.logb 2 (1 / q b) := by
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∑ b ∈ S, p b * Real.log (q b / p b) ≤ 0 := by
    have hterm : ∀ b ∈ S, p b * Real.log (q b / p b) ≤ q b - p b := by
      intro b hb
      rcases eq_or_lt_of_le (hp0 b hb) with h | h
      · simp [← h, le_of_lt (hq0 b hb)]
      · have hdiv : 0 < q b / p b := div_pos (hq0 b hb) h
        have hlog := Real.log_le_sub_one_of_pos hdiv
        have := mul_le_mul_of_nonneg_left hlog (le_of_lt h)
        calc p b * Real.log (q b / p b) ≤ p b * (q b / p b - 1) := this
          _ = q b - p b := by field_simp
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, hp1] at hsum
    linarith
  have hdiff : ∀ b ∈ S, p b * Real.logb 2 (1 / p b) - p b * Real.logb 2 (1 / q b)
      = p b * Real.log (q b / p b) / Real.log 2 := by
    intro b hb
    rcases eq_or_lt_of_le (hp0 b hb) with h | h
    · simp [← h]
    · have hqb := hq0 b hb
      rw [Real.logb, Real.logb]
      rw [Real.log_div (by norm_num) (ne_of_gt h), Real.log_div (by norm_num) (ne_of_gt hqb),
        Real.log_div (ne_of_gt hqb) (ne_of_gt h)]
      simp only [Real.log_one, zero_sub]
      field_simp
      ring
  have hsplit : ∑ b ∈ S, (p b * Real.logb 2 (1 / p b) - p b * Real.logb 2 (1 / q b))
      = (∑ b ∈ S, p b * Real.log (q b / p b)) / Real.log 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl hdiff
  have : ∑ b ∈ S, (p b * Real.logb 2 (1 / p b) - p b * Real.logb 2 (1 / q b)) ≤ 0 := by
    rw [hsplit]
    exact div_nonpos_of_nonpos_of_nonneg key (le_of_lt hlog2)
  rw [Finset.sum_sub_distrib] at this
  linarith

variable {γ : Type} [DecidableEq γ]

/-- The marginal fibre probability is the sum of the joint ones. -/
lemma pr_comp [Nonempty Ω] (Y : Ω → β) (g : β → γ) (c : γ) :
    pr (fun ω => g (Y ω)) c
      = ∑ b ∈ (Finset.image Y Finset.univ).filter (fun b => g b = c), pr Y b := by
  classical
  have hcard : (Finset.univ.filter (fun ω => g (Y ω) = c)).card
      = ∑ b ∈ (Finset.image Y Finset.univ).filter (fun b => g b = c),
          (Finset.univ.filter (fun ω => Y ω = b)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun ω => Y ω)
      (t := (Finset.image Y Finset.univ).filter (fun b => g b = c))
      (s := Finset.univ.filter (fun ω => g (Y ω) = c))
      (fun ω hω => Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem Y (Finset.mem_univ ω), (Finset.mem_filter.mp hω).2⟩)]
    refine Finset.sum_congr rfl fun b hb => ?_
    congr 1
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      exact (Finset.mem_filter.mp hb).2
  unfold pr
  rw [hcard]
  push_cast
  rw [Finset.sum_div]

/-- Regrouping a `pr`-weighted sum along a map `g`. -/
lemma sum_pr_mul [Nonempty Ω] (Y : Ω → β) (g : β → γ) (f : γ → ℝ) :
    ∑ b ∈ Finset.image Y Finset.univ, pr Y b * f (g b)
      = ∑ c ∈ Finset.image (fun ω => g (Y ω)) Finset.univ,
          pr (fun ω => g (Y ω)) c * f c := by
  classical
  have hmaps : ∀ b ∈ Finset.image Y Finset.univ,
      g b ∈ Finset.image (fun ω => g (Y ω)) Finset.univ := by
    intro b hb
    obtain ⟨ω, -, hω⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, by rw [hω]⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun b => pr Y b * f (g b))]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hinner : ∀ b ∈ (Finset.image Y Finset.univ).filter (fun b => g b = c),
      pr Y b * f (g b) = pr Y b * f c := by
    intro b hb
    rw [(Finset.mem_filter.mp hb).2]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, ← pr_comp Y g c]

/-- Subadditivity of entropy: the joint entropy is at most the sum of the marginals. -/
theorem ent_le_sum [Nonempty Ω] {m : ℕ} (Y : Ω → (Fin m → β)) :
    ent Y ≤ ∑ i : Fin m, ent (fun ω => Y ω i) := by
  classical
  set S := Finset.image Y Finset.univ with hS
  set q : (Fin m → β) → ℝ := fun y => ∏ i : Fin m, pr (fun ω => Y ω i) (y i) with hq
  have hq0 : ∀ y ∈ S, 0 < q y := by
    intro y hy
    obtain ⟨ω, -, hω⟩ := Finset.mem_image.mp hy
    refine Finset.prod_pos fun i _ => ?_
    refine pr_pos_of_mem_image ?_
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, by rw [hω]⟩
  have hsubset : S ⊆ Fintype.piFinset
      (fun i : Fin m => Finset.image (fun ω => Y ω i) Finset.univ) := by
    intro y hy
    obtain ⟨ω, -, hω⟩ := Finset.mem_image.mp hy
    refine Fintype.mem_piFinset.mpr fun i => ?_
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, by rw [hω]⟩
  have hq1 : ∑ y ∈ S, q y ≤ 1 := by
    have hall : ∑ y ∈ Fintype.piFinset
        (fun i : Fin m => Finset.image (fun ω => Y ω i) Finset.univ), q y = 1 := by
      rw [hq, ← Finset.prod_univ_sum]
      simp only [sum_pr]
      simp
    calc ∑ y ∈ S, q y
        ≤ ∑ y ∈ Fintype.piFinset
            (fun i : Fin m => Finset.image (fun ω => Y ω i) Finset.univ), q y := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro y _ _
          exact Finset.prod_nonneg fun i _ => pr_nonneg _ _
      _ = 1 := hall
  have hgibbs := gibbs (S := S) (pr Y) q (fun b _ => pr_nonneg Y b) hq0 (sum_pr Y) hq1
  have hexpand : ∀ y ∈ S, pr Y y * Real.logb 2 (1 / q y)
      = ∑ i : Fin m, pr Y y * Real.logb 2 (1 / pr (fun ω => Y ω i) (y i)) := by
    intro y hy
    obtain ⟨ω, -, hω⟩ := Finset.mem_image.mp hy
    have hpos : ∀ i : Fin m, 0 < pr (fun ω' => Y ω' i) (y i) := by
      intro i
      exact pr_pos_of_mem_image (Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, by rw [hω]⟩)
    have hlogprod : Real.logb 2 (∏ i : Fin m, pr (fun ω' => Y ω' i) (y i))
        = ∑ i : Fin m, Real.logb 2 (pr (fun ω' => Y ω' i) (y i)) := by
      unfold Real.logb
      rw [Real.log_prod (fun i _ => ne_of_gt (hpos i)), Finset.sum_div]
    rw [← Finset.mul_sum]
    congr 1
    rw [hq]
    rw [one_div, Real.logb_inv, hlogprod, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div, Real.logb_inv]
  calc ent Y ≤ ∑ y ∈ S, pr Y y * Real.logb 2 (1 / q y) := hgibbs
    _ = ∑ y ∈ S, ∑ i : Fin m, pr Y y * Real.logb 2 (1 / pr (fun ω => Y ω i) (y i)) :=
        Finset.sum_congr rfl hexpand
    _ = ∑ i : Fin m, ∑ y ∈ S, pr Y y * Real.logb 2 (1 / pr (fun ω => Y ω i) (y i)) :=
        Finset.sum_comm
    _ = ∑ i : Fin m, ent (fun ω => Y ω i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact sum_pr_mul Y (fun y => y i)
          (fun c => Real.logb 2 (1 / pr (fun ω => Y ω i) c))

end SpencerEnt

namespace SpencerPCL

open SpencerAux SpencerEnt

variable {n : ℕ}

/-- The bucket index of a row sum at scale `2D`. -/
noncomputable def bucket (T : Finset (Fin n)) (a : Fin n → ℝ) (D : ℝ)
    (σ : Fin n → Bool) : ℤ :=
  round ((∑ j ∈ T, a j * sgn (σ j)) / (2 * D))

lemma card_univ_bool : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by
  simp

/-- A nonzero bucket forces the row sum to be large. -/
lemma abs_ge_of_bucket (T : Finset (Fin n)) (a : Fin n → ℝ) (D : ℝ) (hD : 0 < D)
    (σ : Fin n → Bool) (s : ℤ) (hs : s ≠ 0) (hb : bucket T a D σ = s) :
    (2 * |(s : ℝ)| - 1) * D ≤ |∑ j ∈ T, a j * sgn (σ j)| := by
  set X : ℝ := ∑ j ∈ T, a j * sgn (σ j) with hX
  have h2D : (0:ℝ) < 2 * D := by linarith
  have hround : |X / (2 * D) - (s : ℝ)| ≤ 1 / 2 := by
    rw [← hb]
    simpa [bucket] using abs_sub_round (X / (2 * D))
  obtain ⟨hlo, hhi⟩ := abs_le.mp hround
  have habs : (1:ℝ) ≤ |(s : ℝ)| := by
    have h1 : (1:ℤ) ≤ |s| := Int.one_le_abs (by exact_mod_cast hs)
    have h2 : ((1:ℤ) : ℝ) ≤ ((|s| : ℤ) : ℝ) := Int.cast_le.mpr h1
    simpa using h2
  by_cases hsp : (0:ℝ) ≤ (s : ℝ)
  · have hsabs : |(s:ℝ)| = (s:ℝ) := abs_of_nonneg hsp
    have hs1 : (1:ℝ) ≤ (s:ℝ) := by rw [hsabs] at habs; exact habs
    have hxge : (s : ℝ) - 1 / 2 ≤ X / (2 * D) := by linarith
    have hXge : ((s : ℝ) - 1 / 2) * (2 * D) ≤ X := by
      calc ((s : ℝ) - 1 / 2) * (2 * D) ≤ (X / (2 * D)) * (2 * D) :=
            mul_le_mul_of_nonneg_right hxge (le_of_lt h2D)
        _ = X := by field_simp
    have hXpos : 0 ≤ X := by nlinarith
    rw [abs_of_nonneg hXpos, hsabs]
    nlinarith
  · push_neg at hsp
    have hsabs : |(s:ℝ)| = -(s:ℝ) := abs_of_neg hsp
    have hs1 : (s:ℝ) ≤ -1 := by rw [hsabs] at habs; linarith
    have hxle : X / (2 * D) ≤ (s : ℝ) + 1 / 2 := by linarith
    have hXle : X ≤ ((s : ℝ) + 1 / 2) * (2 * D) := by
      calc X = (X / (2 * D)) * (2 * D) := by field_simp
        _ ≤ ((s : ℝ) + 1 / 2) * (2 * D) := mul_le_mul_of_nonneg_right hxle (le_of_lt h2D)
    have hXneg : X ≤ 0 := by nlinarith
    rw [abs_of_nonpos hXneg, hsabs]
    nlinarith

/-- The fibre probability of a nonzero bucket obeys the Hoeffding tail bound. -/
lemma pr_bucket_le (T : Finset (Fin n)) (a : Fin n → ℝ) (D : ℝ) (hD : 0 < D)
    (S : ℝ) (hS : 0 < S) (hSa : ∑ j ∈ T, (a j) ^ 2 ≤ S) (s : ℤ) (hs : s ≠ 0) :
    pr (bucket T a D) s
      ≤ 2 * Real.exp (-(((2 * |(s : ℝ)| - 1) * D) ^ 2) / (2 * S)) := by
  classical
  have habs : (1:ℝ) ≤ |(s : ℝ)| := by
    have h1 : (1:ℤ) ≤ |s| := Int.one_le_abs (by exact_mod_cast hs)
    have h2 : ((1:ℤ) : ℝ) ≤ ((|s| : ℤ) : ℝ) := Int.cast_le.mpr h1
    simpa using h2
  set u : ℝ := (2 * |(s : ℝ)| - 1) * D with hu
  have hupos : 0 < u := by
    have : (1:ℝ) ≤ 2 * |(s:ℝ)| - 1 := by linarith
    have : (0:ℝ) < 2 * |(s:ℝ)| - 1 := by linarith
    exact mul_pos this hD
  have hsub : (Finset.univ.filter (fun σ : Fin n → Bool => bucket T a D σ = s))
      ⊆ Finset.univ.filter (fun σ : Fin n → Bool => u ≤ |∑ j ∈ T, a j * sgn (σ j)|) := by
    intro σ hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact abs_ge_of_bucket T a D hD σ s hs (Finset.mem_filter.mp hσ).2
  have hcard : ((Finset.univ.filter
      (fun σ : Fin n → Bool => bucket T a D σ = s)).card : ℝ)
      ≤ 2 * (2 ^ n * Real.exp (-(u ^ 2) / (2 * S))) := by
    refine le_trans ?_ (card_abs_ge_le T a u hupos S hS hSa)
    exact_mod_cast Finset.card_le_card hsub
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  unfold pr
  rw [card_univ_bool]
  rw [div_le_iff₀ h2n]
  calc ((Finset.univ.filter (fun σ : Fin n → Bool => bucket T a D σ = s)).card : ℝ)
      ≤ 2 * (2 ^ n * Real.exp (-(u ^ 2) / (2 * S))) := hcard
    _ = 2 * Real.exp (-(u ^ 2) / (2 * S)) * 2 ^ n := by ring

/-! ### Analytic helpers for the entropy majorant -/

/-- `p * logb 2 (1/p)` is `negMulLog p / log 2`. -/
lemma term_eq (p : ℝ) : p * Real.logb 2 (1 / p) = Real.negMulLog p / Real.log 2 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [Real.negMulLog]
  · rw [Real.logb, Real.log_div one_ne_zero hp, Real.log_one, zero_sub, Real.negMulLog]
    ring

/-- The entropy as a sum of `negMulLog`s. -/
lemma ent_eq_sum {Ω : Type} [Fintype Ω] [DecidableEq Ω] {β : Type} [DecidableEq β]
    (Y : Ω → β) :
    ent Y = (∑ b ∈ Finset.image Y Finset.univ, Real.negMulLog (pr Y b)) / Real.log 2 := by
  rw [ent, Finset.sum_div]
  exact Finset.sum_congr rfl fun b _ => term_eq (pr Y b)

/-- `x ↦ -x log x` is nondecreasing up to `e⁻¹`. -/
lemma negMulLog_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ Real.exp (-1)) :
    Real.negMulLog x ≤ Real.negMulLog y := by
  have hy1 : y ≤ 1 := le_trans hy (by
    have : Real.exp (-1) < 1 := by
      have := Real.exp_lt_one_iff.mpr (by norm_num : (-1:ℝ) < 0)
      linarith
    linarith)
  rcases eq_or_lt_of_le hx with h0 | hxpos
  · rw [← h0]
    simpa using Real.negMulLog_nonneg (le_trans hx hxy) hy1
  · have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
    have hlogy : Real.log y ≤ -1 := by
      have := Real.log_le_log hypos hy
      simpa using this
    have hyle : y ≤ Real.negMulLog y := by
      rw [Real.negMulLog]
      nlinarith [hlogy, hypos]
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = x / y := ⟨x / y, rfl⟩
    have hl0 : 0 < l := by rw [hl]; exact div_pos hxpos hypos
    have hl1 : l ≤ 1 := by rw [hl]; exact (div_le_one hypos).mpr hxy
    have hkey : Real.negMulLog l ≤ 1 - l := Real.negMulLog_le_one_sub_self (le_of_lt hl0)
    have hxeq : l * y = x := by rw [hl]; field_simp
    have hmul : Real.negMulLog x = y * Real.negMulLog l + l * Real.negMulLog y := by
      rw [← hxeq, Real.negMulLog_mul]
    rw [hmul]
    nlinarith [mul_le_mul_of_nonneg_left hkey (le_of_lt hypos)]

/-- Two-point concavity bound. -/
lemma negMulLog_pair {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog a + Real.negMulLog b ≤ 2 * Real.negMulLog ((a + b) / 2) := by
  have h := Real.concaveOn_negMulLog.2 (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  have hmid : (1:ℝ)/2 * a + 1/2 * b = (a + b) / 2 := by ring
  rw [hmid] at h
  linarith

/-- The nonzero buckets, as a single event. -/
lemma sum_pr_ne_zero_eq (Y : (Fin n → Bool) → ℤ) :
    ∑ s ∈ (Finset.image Y Finset.univ).filter (fun s => s ≠ 0), pr Y s
      = ((Finset.univ.filter (fun σ : Fin n → Bool => Y σ ≠ 0)).card : ℝ) / 2 ^ n := by
  classical
  have hcard : (Finset.univ.filter (fun σ : Fin n → Bool => Y σ ≠ 0)).card
      = ∑ s ∈ (Finset.image Y Finset.univ).filter (fun s => s ≠ 0),
          (Finset.univ.filter (fun σ : Fin n → Bool => Y σ = s)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun σ => Y σ)
      (t := (Finset.image Y Finset.univ).filter (fun s => s ≠ 0))
      (s := Finset.univ.filter (fun σ : Fin n → Bool => Y σ ≠ 0))
      (fun σ hσ => Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem Y (Finset.mem_univ σ), (Finset.mem_filter.mp hσ).2⟩)]
    refine Finset.sum_congr rfl fun s hs => ?_
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h
      refine ⟨?_, h⟩
      rw [h]
      exact (Finset.mem_filter.mp hs).2
  unfold pr
  rw [card_univ_bool, hcard]
  push_cast
  rw [Finset.sum_div]

/-- The probability that the bucket is nonzero obeys the one-scale tail bound. -/
lemma pr_ne_zero_le (T : Finset (Fin n)) (a : Fin n → ℝ) (D : ℝ) (hD : 0 < D)
    (S : ℝ) (hS : 0 < S) (hSa : ∑ j ∈ T, (a j) ^ 2 ≤ S) :
    ((Finset.univ.filter (fun σ : Fin n → Bool => bucket T a D σ ≠ 0)).card : ℝ) / 2 ^ n
      ≤ 2 * Real.exp (-(D ^ 2) / (2 * S)) := by
  classical
  have hsub : (Finset.univ.filter (fun σ : Fin n → Bool => bucket T a D σ ≠ 0))
      ⊆ Finset.univ.filter (fun σ : Fin n → Bool => D ≤ |∑ j ∈ T, a j * sgn (σ j)|) := by
    intro σ hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hne := (Finset.mem_filter.mp hσ).2
    have hge := abs_ge_of_bucket T a D hD σ (bucket T a D σ) hne rfl
    have habs : (1:ℝ) ≤ |((bucket T a D σ : ℤ) : ℝ)| := by
      have h1 : (1:ℤ) ≤ |bucket T a D σ| := Int.one_le_abs (by exact_mod_cast hne)
      have h2 : ((1:ℤ) : ℝ) ≤ ((|bucket T a D σ| : ℤ) : ℝ) := Int.cast_le.mpr h1
      simpa using h2
    nlinarith [hge, hD]
  have hcard : ((Finset.univ.filter
      (fun σ : Fin n → Bool => bucket T a D σ ≠ 0)).card : ℝ)
      ≤ 2 * (2 ^ n * Real.exp (-(D ^ 2) / (2 * S))) := by
    refine le_trans ?_ (card_abs_ge_le T a D hD S hS hSa)
    exact_mod_cast Finset.card_le_card hsub
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ h2n]
  calc ((Finset.univ.filter (fun σ : Fin n → Bool => bucket T a D σ ≠ 0)).card : ℝ)
      ≤ 2 * (2 ^ n * Real.exp (-(D ^ 2) / (2 * S))) := hcard
    _ = 2 * Real.exp (-(D ^ 2) / (2 * S)) * 2 ^ n := by ring

/-! ### The geometric tail of the entropy majorant -/

/-- `v * exp (-v) ≤ exp (-1)`. -/
lemma mul_exp_neg_le (v : ℝ) : v * Real.exp (-v) ≤ Real.exp (-1) := by
  have hv' : v ≤ Real.exp (v - 1) := by
    have h := Real.add_one_le_exp (v - 1)
    linarith
  have hstep : v * Real.exp (-v) ≤ Real.exp (v - 1) * Real.exp (-v) :=
    mul_le_mul_of_nonneg_right hv' (le_of_lt (Real.exp_pos _))
  calc v * Real.exp (-v) ≤ Real.exp (v - 1) * Real.exp (-v) := hstep
    _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf

/-- The `negMulLog` of a Gaussian-type tail bound decays at half the rate. -/
lemma nml_tail_le (x ν : ℝ) (hx : 0 < x) (hν : 0 < ν) :
    Real.negMulLog (2 * Real.exp (-(x ^ 2 * ν ^ 2) / 2))
      ≤ 4 * Real.exp (-1) * Real.exp (-(x ^ 2 * ν ^ 2) / 4) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = x ^ 2 * ν ^ 2 / 2 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hue : -(x ^ 2 * ν ^ 2) / 2 = -u := by rw [hu]; ring
  have hue2 : -(x ^ 2 * ν ^ 2) / 4 = -(u / 2) := by rw [hu]; ring
  rw [hue, hue2]
  have hlog : Real.log (2 * Real.exp (-u)) = Real.log 2 - u := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    ring
  have hnml : Real.negMulLog (2 * Real.exp (-u)) = 2 * Real.exp (-u) * (u - Real.log 2) := by
    rw [Real.negMulLog, hlog]; ring
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.negMulLog (2 * Real.exp (-u)) ≤ 2 * (u * Real.exp (-u)) := by
    rw [hnml]
    nlinarith [Real.exp_pos (-u)]
  have hexp : Real.exp (-(u / 2)) * Real.exp (-(u / 2)) = Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  have hsplit : u * Real.exp (-u)
      = 2 * ((u / 2) * Real.exp (-(u / 2))) * Real.exp (-(u / 2)) := by
    rw [← hexp]; ring
  have hkey := mul_exp_neg_le (u / 2)
  have h2 : u * Real.exp (-u) ≤ 2 * Real.exp (-1) * Real.exp (-(u / 2)) := by
    rw [hsplit]
    have := mul_le_mul_of_nonneg_right hkey (le_of_lt (Real.exp_pos (-(u / 2))))
    nlinarith [Real.exp_pos (-(u / 2))]
  linarith

/-- A finite sum of distinct powers of `1/2` is at most `2`. -/
lemma sum_half_pow_le (K : Finset ℕ) : ∑ j ∈ K, (1/2:ℝ) ^ j ≤ 2 := by
  classical
  obtain ⟨M, hM⟩ : ∃ M, K ⊆ Finset.range M :=
    ⟨K.sup id + 1, fun k hk => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))⟩
  have hle : ∑ j ∈ K, (1/2:ℝ) ^ j ≤ ∑ j ∈ Finset.range M, (1/2:ℝ) ^ j :=
    Finset.sum_le_sum_of_subset_of_nonneg hM (fun j _ _ => by positivity)
  have heq : ∑ j ∈ Finset.range M, (1/2:ℝ) ^ j = ((1/2:ℝ) ^ M - 1) / (1/2 - 1) :=
    geom_sum_eq (by norm_num) M
  have hpow : (0:ℝ) < (1/2:ℝ) ^ M := by positivity
  rw [heq] at hle
  have : ((1/2:ℝ) ^ M - 1) / (1/2 - 1) = 2 * (1 - (1/2:ℝ) ^ M) := by
    field_simp
    ring
  rw [this] at hle
  nlinarith

/-- Summing a geometric bound over integers of absolute value at least two. -/
lemma sum_far_le (B : Finset ℤ) (hB : ∀ s ∈ B, 2 ≤ |s|) (C : ℝ) (hC : 0 ≤ C) :
    ∑ s ∈ B, C * (1/2:ℝ) ^ ((|s|).toNat - 2) ≤ 4 * C := by
  classical
  have hmaps : ∀ s ∈ B, (|s|).toNat ∈ B.image (fun s => (|s|).toNat) :=
    fun s hs => Finset.mem_image_of_mem _ hs
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun s => C * (1/2:ℝ) ^ ((|s|).toNat - 2))]
  have hfib : ∀ k ∈ B.image (fun s => (|s|).toNat),
      ∑ s ∈ B.filter (fun s => (|s|).toNat = k), C * (1/2:ℝ) ^ ((|s|).toNat - 2)
        ≤ 2 * (C * (1/2:ℝ) ^ (k - 2)) := by
    intro k hk
    have hcard : (B.filter (fun s => (|s|).toNat = k)).card ≤ 2 := by
      have hsub : B.filter (fun s => (|s|).toNat = k) ⊆ {(k:ℤ), -(k:ℤ)} := by
        intro s hs
        have hk' : (|s|).toNat = k := (Finset.mem_filter.mp hs).2
        have habs : |s| = (k:ℤ) := by
          have : ((|s|).toNat : ℤ) = |s| := Int.toNat_of_nonneg (abs_nonneg s)
          rw [← this, hk']
        rcases abs_eq (by positivity : (0:ℤ) ≤ (k:ℤ)) |>.mp habs with h | h
        · simp [h]
        · simp [h]
      calc (B.filter (fun s => (|s|).toNat = k)).card ≤ ({(k:ℤ), -(k:ℤ)} : Finset ℤ).card :=
            Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
    have hval : ∀ s ∈ B.filter (fun s => (|s|).toNat = k),
        C * (1/2:ℝ) ^ ((|s|).toNat - 2) = C * (1/2:ℝ) ^ (k - 2) := by
      intro s hs
      rw [(Finset.mem_filter.mp hs).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    have hpos : (0:ℝ) ≤ C * (1/2:ℝ) ^ (k - 2) := by positivity
    have : ((B.filter (fun s => (|s|).toNat = k)).card : ℝ) ≤ 2 := by exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right this hpos
  refine le_trans (Finset.sum_le_sum hfib) ?_
  have hshift : ∑ k ∈ B.image (fun s => (|s|).toNat), 2 * (C * (1/2:ℝ) ^ (k - 2))
      = 2 * C * ∑ k ∈ B.image (fun s => (|s|).toNat), (1/2:ℝ) ^ (k - 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hshift]
  have hsum : ∑ k ∈ B.image (fun s => (|s|).toNat), (1/2:ℝ) ^ (k - 2) ≤ 2 := by
    have hinj : ∀ k₁ ∈ B.image (fun s => (|s|).toNat), ∀ k₂ ∈ B.image (fun s => (|s|).toNat),
        k₁ - 2 = k₂ - 2 → k₁ = k₂ := by
      intro k₁ h₁ k₂ h₂ h
      obtain ⟨s₁, hs₁, rfl⟩ := Finset.mem_image.mp h₁
      obtain ⟨s₂, hs₂, rfl⟩ := Finset.mem_image.mp h₂
      have hb₁ : 2 ≤ |s₁| := hB s₁ hs₁
      have hb₂ : 2 ≤ |s₂| := hB s₂ hs₂
      have hn₁ : 2 ≤ (|s₁|).toNat := by omega
      have hn₂ : 2 ≤ (|s₂|).toNat := by omega
      omega
    calc ∑ k ∈ B.image (fun s => (|s|).toNat), (1/2:ℝ) ^ (k - 2)
        = ∑ j ∈ (B.image (fun s => (|s|).toNat)).image (fun k => k - 2), (1/2:ℝ) ^ j := by
          rw [Finset.sum_image hinj]
      _ ≤ 2 := sum_half_pow_le _
  nlinarith [hC]

/-- Fibres outside the image are empty. -/
lemma pr_eq_zero_of_notMem {Ω : Type} [Fintype Ω] [DecidableEq Ω] {β : Type} [DecidableEq β]
    (Y : Ω → β) {b : β} (hb : b ∉ Finset.image Y Finset.univ) : pr Y b = 0 := by
  classical
  have : (Finset.univ.filter (fun ω => Y ω = b)) = ∅ := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h
    exact hb (Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, h⟩)
  unfold pr
  rw [this]
  simp

/-- The exponent estimate behind the geometric tail. -/
lemma tail_exponent (k : ℕ) (hk : 2 ≤ k) (ν : ℝ) (hν : 2 ≤ ν) :
    Real.exp (-((2 * (k:ℝ) - 1) ^ 2 * ν ^ 2) / 4)
      ≤ Real.exp (-(9 * ν ^ 2) / 4) * (1/2 : ℝ) ^ (k - 2) := by
  have hkR : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hν0 : (0:ℝ) < ν := by linarith
  have hν4 : (4:ℝ) ≤ ν ^ 2 := by nlinarith
  -- (2k-1)^2 ≥ 9 + 12 (k-2)
  have hsq : (9:ℝ) + 12 * ((k:ℝ) - 2) ≤ (2 * (k:ℝ) - 1) ^ 2 := by nlinarith
  have hexp : -((2 * (k:ℝ) - 1) ^ 2 * ν ^ 2) / 4
      ≤ -(9 * ν ^ 2) / 4 - 12 * ((k:ℝ) - 2) := by nlinarith
  have hstep : Real.exp (-((2 * (k:ℝ) - 1) ^ 2 * ν ^ 2) / 4)
      ≤ Real.exp (-(9 * ν ^ 2) / 4 - 12 * ((k:ℝ) - 2)) := Real.exp_le_exp.mpr hexp
  have hsplit : Real.exp (-(9 * ν ^ 2) / 4 - 12 * ((k:ℝ) - 2))
      = Real.exp (-(9 * ν ^ 2) / 4) * Real.exp (-(12 * ((k:ℝ) - 2))) := by
    rw [← Real.exp_add]; ring_nf
  have hgeo : Real.exp (-(12 * ((k:ℝ) - 2))) ≤ (1/2 : ℝ) ^ (k - 2) := by
    have hkk : ((k - 2 : ℕ) : ℝ) = (k:ℝ) - 2 := by
      have : (2:ℕ) ≤ k := hk
      push_cast [Nat.cast_sub this]
      ring
    have hbase : Real.exp (-(12 * ((k:ℝ) - 2))) = (Real.exp (-12)) ^ ((k - 2 : ℕ)) := by
      rw [← Real.exp_nat_mul, hkk]
      congr 1
      ring
    rw [hbase]
    refine pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) ?_ _
    have h1 : Real.exp (-12) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp (-1) < 1/2 := by
      have := Real.exp_one_gt_d9
      rw [Real.exp_neg]
      rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
      linarith
    linarith
  calc Real.exp (-((2 * (k:ℝ) - 1) ^ 2 * ν ^ 2) / 4)
      ≤ Real.exp (-(9 * ν ^ 2) / 4) * Real.exp (-(12 * ((k:ℝ) - 2))) := by
        rw [← hsplit]; exact hstep
    _ ≤ Real.exp (-(9 * ν ^ 2) / 4) * (1/2 : ℝ) ^ (k - 2) :=
        mul_le_mul_of_nonneg_left hgeo (le_of_lt (Real.exp_pos _))

/-- `exp (-x) ≤ 1/c` whenever `c ≤ exp x`. -/
lemma exp_neg_le_inv (x c : ℝ) (hc : 0 < c) (h : c ≤ Real.exp x) :
    Real.exp (-x) ≤ 1 / c := by
  have hstep : Real.exp (-x) * c ≤ Real.exp (-x) * Real.exp x :=
    mul_le_mul_of_nonneg_left h (le_of_lt (Real.exp_pos _))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hstep
  rw [le_div_iff₀ hc]
  linarith

/-- A crude numeric bound: `e^7 ≥ 20`. -/
lemma exp_seven_ge : (20:ℝ) ≤ Real.exp 7 := by
  have h : (10/3:ℝ) ≤ Real.exp (7/3) := by
    have := Real.add_one_le_exp (7/3 : ℝ)
    linarith
  have h3 : Real.exp 7 = Real.exp (7/3) * (Real.exp (7/3) * Real.exp (7/3)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h3]
  nlinarith [Real.exp_pos (7/3:ℝ)]

/-- Fibre probabilities are at most one. -/
lemma pr_le_one {β : Type} [DecidableEq β] (Y : (Fin n → Bool) → β) (b : β) :
    pr Y b ≤ 1 := by
  classical
  unfold pr
  rw [card_univ_bool, div_le_one (by positivity)]
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin n → Bool)) (fun σ => Y σ = b)
  have hc : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  rw [hc] at h
  exact_mod_cast h

/-- The two extreme buckets are disjoint events inside the nonzero event. -/
lemma pr_pair_le (Y : (Fin n → Bool) → ℤ) :
    pr Y 1 + pr Y (-1)
      ≤ ((Finset.univ.filter (fun σ : Fin n → Bool => Y σ ≠ 0)).card : ℝ) / 2 ^ n := by
  classical
  have hdisj : Disjoint (Finset.univ.filter (fun σ : Fin n → Bool => Y σ = 1))
      (Finset.univ.filter (fun σ : Fin n → Bool => Y σ = -1)) := by
    rw [Finset.disjoint_filter]
    intro σ _ h1 h2
    rw [h1] at h2
    norm_num at h2
  have hsub : (Finset.univ.filter (fun σ : Fin n → Bool => Y σ = 1)) ∪
      (Finset.univ.filter (fun σ : Fin n → Bool => Y σ = -1))
      ⊆ Finset.univ.filter (fun σ : Fin n → Bool => Y σ ≠ 0) := by
    intro σ hσ
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    rcases hσ with h | h <;> rw [h] <;> norm_num
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have hcast : ((Finset.univ.filter (fun σ : Fin n → Bool => Y σ = 1)).card : ℝ)
      + ((Finset.univ.filter (fun σ : Fin n → Bool => Y σ = -1)).card : ℝ)
      ≤ ((Finset.univ.filter (fun σ : Fin n → Bool => Y σ ≠ 0)).card : ℝ) := by
    exact_mod_cast hcard
  unfold pr
  rw [card_univ_bool, ← add_div]
  gcongr

/-- The entropy majorant.  If the nonzero event has probability at most `2 e^{-ν²/2}`
and every nonzero bucket obeys the Hoeffding tail, the Shannon entropy (in bits) of the
bucket variable is at most `Ψ(ν) = 2 e^{-ν²/2} (3ν²/4 + 2)`. -/
theorem ent_le_of_tails (Y : (Fin n → Bool) → ℤ) (ν : ℝ) (hν : 2 ≤ ν)
    (h0 : ((Finset.univ.filter (fun σ : Fin n → Bool => Y σ ≠ 0)).card : ℝ) / 2 ^ n
            ≤ 2 * Real.exp (-(ν ^ 2) / 2))
    (hfar : ∀ s : ℤ, s ≠ 0 →
      pr Y s ≤ 2 * Real.exp (-((2 * |(s:ℝ)| - 1) ^ 2 * ν ^ 2) / 2)) :
    ent Y ≤ 2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2) := by
  classical
  have hν0 : (0:ℝ) < ν := by linarith
  have hν4 : (4:ℝ) ≤ ν ^ 2 := by nlinarith
  have hE : (0:ℝ) < Real.exp (-(ν ^ 2) / 2) := Real.exp_pos _
  set E : ℝ := Real.exp (-(ν ^ 2) / 2) with hEdef
  set Qv : ℝ :=
    ((Finset.univ.filter (fun σ : Fin n → Bool => Y σ ≠ 0)).card : ℝ) / 2 ^ n with hQdef
  have hQ0 : (0:ℝ) ≤ Qv := by rw [hQdef]; positivity
  rw [ent_eq_sum Y, div_le_iff₀ (Real.log_pos (by norm_num))]
  set J : Finset ℤ := Finset.image Y Finset.univ with hJdef
  -- the three-way split of the index set
  have hsplit1 := Finset.sum_filter_add_sum_filter_not J (fun s => s = 0)
      (fun b => Real.negMulLog (pr Y b))
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (J.filter (fun s => ¬ (s = 0)))
      (fun s => |s| = 1) (fun b => Real.negMulLog (pr Y b))
  -- the mass of the zero bucket
  have hall : ∑ b ∈ J, pr Y b = 1 := sum_pr Y
  have hnz : ∑ s ∈ J.filter (fun s => ¬ (s = 0)), pr Y s = Qv := sum_pr_ne_zero_eq Y
  have hsplitp := Finset.sum_filter_add_sum_filter_not J (fun s => s = 0) (fun b => pr Y b)
  have hzero : ∑ b ∈ J.filter (fun s => s = 0), pr Y b = 1 - Qv := by
    rw [hall] at hsplitp
    linarith [hnz, hsplitp]
  -- (A) the zero bucket contributes at most the nonzero mass
  have hA : ∑ b ∈ J.filter (fun s => s = 0), Real.negMulLog (pr Y b) ≤ Qv := by
    have hle : ∑ b ∈ J.filter (fun s => s = 0), Real.negMulLog (pr Y b)
        ≤ ∑ b ∈ J.filter (fun s => s = 0), (1 - pr Y b) :=
      Finset.sum_le_sum (fun b _ => Real.negMulLog_le_one_sub_self (pr_nonneg Y b))
    have heq : ∑ b ∈ J.filter (fun s => s = 0), (1 - pr Y b)
        = ((J.filter (fun s => s = 0)).card : ℝ)
          - ∑ b ∈ J.filter (fun s => s = 0), pr Y b := by
      rw [Finset.sum_sub_distrib]
      simp
    have hcard : ((J.filter (fun s => s = 0)).card : ℝ) ≤ 1 := by
      have hsub : J.filter (fun s => s = 0) ⊆ ({0} : Finset ℤ) := by
        intro b hb
        simp only [Finset.mem_filter] at hb
        simp [hb.2]
      have hc := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at hc
      exact_mod_cast hc
    rw [heq, hzero] at hle
    linarith
  -- (B) the two unit buckets, via two-point concavity
  have hB : ∑ b ∈ (J.filter (fun s => ¬ (s = 0))).filter (fun s => |s| = 1),
      Real.negMulLog (pr Y b) ≤ E * ν ^ 2 := by
    have hsub : (J.filter (fun s => ¬ (s = 0))).filter (fun s => |s| = 1)
        ⊆ ({1, -1} : Finset ℤ) := by
      intro b hb
      simp only [Finset.mem_filter] at hb
      have h1 : b = 1 ∨ b = -1 := (abs_eq (by norm_num : (0:ℤ) ≤ 1)).mp hb.2
      rcases h1 with h | h <;> simp [h]
    have hstep1 : ∑ b ∈ (J.filter (fun s => ¬ (s = 0))).filter (fun s => |s| = 1),
        Real.negMulLog (pr Y b) ≤ ∑ b ∈ ({1, -1} : Finset ℤ), Real.negMulLog (pr Y b) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun b _ _ => Real.negMulLog_nonneg (pr_nonneg Y b) (pr_le_one Y b))
    have hpair : ∑ b ∈ ({1, -1} : Finset ℤ), Real.negMulLog (pr Y b)
        = Real.negMulLog (pr Y 1) + Real.negMulLog (pr Y (-1)) :=
      Finset.sum_pair (by norm_num)
    have hconc : Real.negMulLog (pr Y 1) + Real.negMulLog (pr Y (-1))
        ≤ 2 * Real.negMulLog ((pr Y 1 + pr Y (-1)) / 2) :=
      negMulLog_pair (pr_nonneg Y 1) (pr_nonneg Y (-1))
    have hmid : (pr Y 1 + pr Y (-1)) / 2 ≤ E := by
      have := pr_pair_le Y
      rw [← hQdef] at this
      linarith
    have hEle : E ≤ Real.exp (-1) := by
      rw [hEdef]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hmono : Real.negMulLog ((pr Y 1 + pr Y (-1)) / 2) ≤ Real.negMulLog E :=
      negMulLog_mono (by linarith [pr_nonneg Y 1, pr_nonneg Y (-1)]) hmid hEle
    have hval : Real.negMulLog E = E * (ν ^ 2 / 2) := by
      rw [hEdef]
      unfold Real.negMulLog
      rw [Real.log_exp]
      ring
    have : 2 * Real.negMulLog E = E * ν ^ 2 := by rw [hval]; ring
    linarith
  -- (C) the far buckets, geometric tail
  have hC : ∑ b ∈ (J.filter (fun s => ¬ (s = 0))).filter (fun s => ¬ (|s| = 1)),
      Real.negMulLog (pr Y b) ≤ 4 * (4 * Real.exp (-1) * Real.exp (-(9 * ν ^ 2) / 4)) := by
    have hCnn : (0:ℝ) ≤ 4 * Real.exp (-1) * Real.exp (-(9 * ν ^ 2) / 4) := by positivity
    have hfarset : ∀ s ∈ (J.filter (fun s => ¬ (s = 0))).filter (fun s => ¬ (|s| = 1)),
        2 ≤ |s| := by
      intro s hs
      simp only [Finset.mem_filter] at hs
      have h0' : ¬ (s = 0) := hs.1.2
      have h1' : ¬ (|s| = 1) := hs.2
      rcases lt_trichotomy s 0 with h | h | h
      · have habs : |s| = -s := abs_of_neg h
        omega
      · exact absurd h h0'
      · have habs : |s| = s := abs_of_pos h
        omega
    have hterm : ∀ b ∈ (J.filter (fun s => ¬ (s = 0))).filter (fun s => ¬ (|s| = 1)),
        Real.negMulLog (pr Y b)
          ≤ (4 * Real.exp (-1) * Real.exp (-(9 * ν ^ 2) / 4)) * (1/2:ℝ) ^ ((|b|).toNat - 2) := by
      intro b hb
      have hb0 : b ≠ 0 := by
        simp only [Finset.mem_filter] at hb
        exact hb.1.2
      have hb2 : 2 ≤ |b| := hfarset b hb
      have hk2 : 2 ≤ (|b|).toNat := by omega
      have hkR : (((|b|).toNat : ℕ) : ℝ) = |(b:ℝ)| := by
        have h1 : (((|b|).toNat : ℕ) : ℤ) = |b| := Int.toNat_of_nonneg (abs_nonneg b)
        have h2 : (((|b|).toNat : ℕ) : ℝ) = ((|b| : ℤ) : ℝ) := by exact_mod_cast h1
        rwa [Int.cast_abs] at h2
      have hkge : (2:ℝ) ≤ (((|b|).toNat : ℕ) : ℝ) := by exact_mod_cast hk2
      have hpr := hfar b hb0
      rw [← hkR] at hpr
      have hxsq : (36:ℝ) ≤ (2 * (((|b|).toNat : ℕ) : ℝ) - 1) ^ 2 * ν ^ 2 := by nlinarith
      have hsmall : 2 * Real.exp (-((2 * (((|b|).toNat : ℕ) : ℝ) - 1) ^ 2 * ν ^ 2) / 2)
          ≤ Real.exp (-1) := by
        have hle : Real.exp (-((2 * (((|b|).toNat : ℕ) : ℝ) - 1) ^ 2 * ν ^ 2) / 2)
            ≤ Real.exp (-18) := Real.exp_le_exp.mpr (by linarith)
        have h17 : Real.exp (-17) ≤ 1/2 :=
          exp_neg_le_inv 17 2 (by norm_num) (by linarith [Real.add_one_le_exp (17:ℝ)])
        have hsp : Real.exp (-18) = Real.exp (-1) * Real.exp (-17) := by
          rw [← Real.exp_add]; congr 1; ring
        have hmul : Real.exp (-1) * Real.exp (-17) ≤ Real.exp (-1) * (1/2) :=
          mul_le_mul_of_nonneg_left h17 (le_of_lt (Real.exp_pos _))
        rw [hsp] at hle
        linarith
      have hmono := negMulLog_mono (pr_nonneg Y b) hpr hsmall
      have htail := nml_tail_le (2 * (((|b|).toNat : ℕ) : ℝ) - 1) ν (by linarith) hν0
      have hte := tail_exponent ((|b|).toNat) hk2 ν hν
      have h4 : (0:ℝ) ≤ 4 * Real.exp (-1) := by positivity
      calc Real.negMulLog (pr Y b)
          ≤ Real.negMulLog (2 * Real.exp (-((2 * (((|b|).toNat : ℕ) : ℝ) - 1) ^ 2 * ν ^ 2) / 2)) :=
            hmono
        _ ≤ 4 * Real.exp (-1)
              * Real.exp (-((2 * (((|b|).toNat : ℕ) : ℝ) - 1) ^ 2 * ν ^ 2) / 4) := htail
        _ ≤ 4 * Real.exp (-1) * (Real.exp (-(9 * ν ^ 2) / 4) * (1/2:ℝ) ^ ((|b|).toNat - 2)) :=
            mul_le_mul_of_nonneg_left hte h4
        _ = (4 * Real.exp (-1) * Real.exp (-(9 * ν ^ 2) / 4)) * (1/2:ℝ) ^ ((|b|).toNat - 2) := by
            ring
    calc ∑ b ∈ (J.filter (fun s => ¬ (s = 0))).filter (fun s => ¬ (|s| = 1)),
            Real.negMulLog (pr Y b)
        ≤ ∑ b ∈ (J.filter (fun s => ¬ (s = 0))).filter (fun s => ¬ (|s| = 1)),
            (4 * Real.exp (-1) * Real.exp (-(9 * ν ^ 2) / 4)) * (1/2:ℝ) ^ ((|b|).toNat - 2) :=
          Finset.sum_le_sum hterm
      _ ≤ 4 * (4 * Real.exp (-1) * Real.exp (-(9 * ν ^ 2) / 4)) :=
          sum_far_le _ hfarset _ hCnn
  -- the tail is a small fraction of the leading term
  have h9 : Real.exp (-(9 * ν ^ 2) / 4) ≤ E / 20 := by
    have hsp9 : Real.exp (-(9 * ν ^ 2) / 4) = E * Real.exp (-(7 * ν ^ 2) / 4) := by
      rw [hEdef, ← Real.exp_add]; congr 1; ring
    have h7 : Real.exp (-(7 * ν ^ 2) / 4) ≤ 1/20 := by
      have hstep : Real.exp (-(7 * ν ^ 2) / 4) ≤ Real.exp (-7) :=
        Real.exp_le_exp.mpr (by linarith)
      have h20 : Real.exp (-7) ≤ 1/20 := exp_neg_le_inv 7 20 (by norm_num) exp_seven_ge
      linarith
    rw [hsp9]
    nlinarith [hE]
  have he1 : Real.exp (-1) ≤ 1/2 :=
    exp_neg_le_inv 1 2 (by norm_num) (by linarith [Real.add_one_le_exp (1:ℝ)])
  have hTail : 4 * (4 * Real.exp (-1) * Real.exp (-(9 * ν ^ 2) / 4)) ≤ 2 * E / 5 := by
    have h9p : (0:ℝ) < Real.exp (-(9 * ν ^ 2) / 4) := Real.exp_pos _
    nlinarith [Real.exp_pos (-1:ℝ), h9p, he1, h9]
  -- final arithmetic
  have hL : (0.6931:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hbase : (0:ℝ) ≤ 3 * ν ^ 2 / 4 + 2 := by positivity
  have hmul : (3 * ν ^ 2 / 4 + 2) * 0.6931 ≤ (3 * ν ^ 2 / 4 + 2) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hL hbase
  have hkey : 1 + ν ^ 2 / 2 + 1/5 ≤ (3 * ν ^ 2 / 4 + 2) * Real.log 2 := by nlinarith
  have hq : 2 * E * (1 + ν ^ 2 / 2 + 1/5) ≤ 2 * E * ((3 * ν ^ 2 / 4 + 2) * Real.log 2) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have hexp1 : 2 * E * (1 + ν ^ 2 / 2 + 1/5) = 2 * E + E * ν ^ 2 + 2 * E / 5 := by ring
  have hexp2 : 2 * E * ((3 * ν ^ 2 / 4 + 2) * Real.log 2)
      = 2 * E * (3 * ν ^ 2 / 4 + 2) * Real.log 2 := by ring
  linarith [hA, hB, hC, hTail, h0, hsplit1, hsplit2, hq]

/-- The entropy of one bucket variable at scale `D = ν √S`. -/
theorem ent_bucket_le (T : Finset (Fin n)) (a : Fin n → ℝ)
    (S : ℝ) (hS : 0 < S) (hSa : ∑ j ∈ T, (a j) ^ 2 ≤ S)
    (ν : ℝ) (hν : 2 ≤ ν) :
    ent (bucket T a (ν * Real.sqrt S))
      ≤ 2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2) := by
  have hν0 : (0:ℝ) < ν := by linarith
  have hD0 : 0 < ν * Real.sqrt S := mul_pos hν0 (Real.sqrt_pos.mpr hS)
  have hDsq : (ν * Real.sqrt S) ^ 2 = ν ^ 2 * S := by
    rw [mul_pow, Real.sq_sqrt hS.le]
  have hSne : S ≠ 0 := ne_of_gt hS
  refine ent_le_of_tails _ ν hν ?_ ?_
  · have h := pr_ne_zero_le T a (ν * Real.sqrt S) hD0 S hS hSa
    have heq : -((ν * Real.sqrt S) ^ 2) / (2 * S) = -(ν ^ 2) / 2 := by
      rw [hDsq]; field_simp
    rwa [heq] at h
  · intro s hs
    have h := pr_bucket_le T a (ν * Real.sqrt S) hD0 S hS hSa s hs
    have heq : -(((2 * |(s:ℝ)| - 1) * (ν * Real.sqrt S)) ^ 2) / (2 * S)
        = -((2 * |(s:ℝ)| - 1) ^ 2 * ν ^ 2) / 2 := by
      rw [mul_pow, hDsq]; field_simp
    rwa [heq] at h

/-- Two points in the same bucket have row sums within `2D`. -/
lemma bucket_close (T : Finset (Fin n)) (a : Fin n → ℝ) (D : ℝ) (hD : 0 < D)
    (σ ρ : Fin n → Bool) (h : bucket T a D σ = bucket T a D ρ) :
    |(∑ j ∈ T, a j * sgn (σ j)) - (∑ j ∈ T, a j * sgn (ρ j))| ≤ 2 * D := by
  unfold bucket at h
  set u : ℝ := (∑ j ∈ T, a j * sgn (σ j)) / (2 * D) with hu
  set v : ℝ := (∑ j ∈ T, a j * sgn (ρ j)) / (2 * D) with hv
  have h1 := abs_sub_round u
  have h2 := abs_sub_round v
  rw [h] at h1
  have hb1 := abs_le.mp h1
  have hb2 := abs_le.mp h2
  have huv : |u - v| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2]
  have hD2 : (0:ℝ) < 2 * D := by linarith
  have hdiff : u - v
      = ((∑ j ∈ T, a j * sgn (σ j)) - (∑ j ∈ T, a j * sgn (ρ j))) / (2 * D) := by
    rw [hu, hv]; ring
  rw [hdiff, abs_div, abs_of_pos hD2, div_le_one hD2] at huv
  exact huv

end SpencerPCL

namespace SpencerMcD

variable {n : ℕ}

/-- Flipping one coordinate is an involution, so it reindexes a sum over the cube. -/
lemma sum_flip (j : Fin n) (F : (Fin n → Bool) → ℝ) :
    ∑ σ : Fin n → Bool, F σ
      = ∑ σ : Fin n → Bool, F (Function.update σ j (!σ j)) := by
  have hinv : Function.Involutive (fun σ : Fin n → Bool => Function.update σ j (!σ j)) := by
    intro σ
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  exact (Fintype.sum_equiv hinv.toPerm
    (fun σ => F (Function.update σ j (!σ j))) F (fun σ => rfl)).symm

/-- Summing over the cube is the same as averaging each coordinate pair. -/
lemma sum_pair_split (j : Fin n) (F : (Fin n → Bool) → ℝ) :
    ∑ σ : Fin n → Bool, F σ
      = ∑ σ : Fin n → Bool,
          (F (Function.update σ j false) + F (Function.update σ j true)) / 2 := by
  have h1 := sum_flip j F
  have key : ∑ σ : Fin n → Bool, (F σ + F (Function.update σ j (!σ j))) / 2
      = ∑ σ : Fin n → Bool, F σ := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← h1]
    ring
  rw [← key]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  cases hb : σ j with
  | false =>
    have e1 : Function.update σ j false = σ := by
      conv_rhs => rw [← Function.update_eq_self j σ]
      rw [hb]
    simp only [Bool.not_false, e1]
  | true =>
    have e1 : Function.update σ j true = σ := by
      conv_rhs => rw [← Function.update_eq_self j σ]
      rw [hb]
    simp only [Bool.not_true, e1]
    ring

/-- The average of `f` over the coordinates in `S`, the others held fixed at `σ`. -/
noncomputable def avgOn (S : Finset (Fin n)) (f : (Fin n → Bool) → ℝ)
    (σ : Fin n → Bool) : ℝ :=
  (∑ x : Fin n → Bool, f (fun j => if j ∈ S then x j else σ j)) / 2 ^ n

lemma cube_card : ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) = 2 ^ n := by
  simp

lemma avgOn_empty (f : (Fin n → Bool) → ℝ) (σ : Fin n → Bool) : avgOn ∅ f σ = f σ := by
  unfold avgOn
  have hx : ∀ x : Fin n → Bool,
      (fun j => if j ∈ (∅ : Finset (Fin n)) then x j else σ j) = σ := by
    intro x; funext j; simp
  simp only [hx, Finset.sum_const, nsmul_eq_mul]
  rw [cube_card]
  have h2 : (2:ℝ) ^ n ≠ 0 := by positivity
  field_simp

lemma avgOn_univ (f : (Fin n → Bool) → ℝ) (σ : Fin n → Bool) :
    avgOn Finset.univ f σ = (∑ x : Fin n → Bool, f x) / 2 ^ n := by
  unfold avgOn
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  funext j
  simp

lemma avgOn_insert (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S)
    (f : (Fin n → Bool) → ℝ) (σ : Fin n → Bool) :
    avgOn (insert j S) f σ
      = (avgOn S f (Function.update σ j false) + avgOn S f (Function.update σ j true)) / 2 := by
  have hf : ∀ (b : Bool) (x : Fin n → Bool),
      (fun k => if k ∈ insert j S then (Function.update x j b) k else σ k)
        = (fun k => if k ∈ S then x k else (Function.update σ j b) k) := by
    intro b x
    funext k
    by_cases hk : k = j
    · subst hk
      simp [hj, Function.update_self]
    · simp [Finset.mem_insert, hk, Function.update_of_ne hk]
  have hkey := sum_pair_split j (fun x : Fin n → Bool =>
      f (fun k => if k ∈ insert j S then x k else σ k))
  simp only [hf] at hkey
  unfold avgOn
  rw [hkey, ← Finset.sum_div, Finset.sum_add_distrib]
  ring

lemma avgOn_osc (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S)
    (f : (Fin n → Bool) → ℝ) (c : ℝ)
    (hosc : ∀ τ : Fin n → Bool,
      |f (Function.update τ j false) - f (Function.update τ j true)| ≤ c)
    (σ : Fin n → Bool) :
    |avgOn S f (Function.update σ j false) - avgOn S f (Function.update σ j true)| ≤ c := by
  have hmix : ∀ (b : Bool) (x : Fin n → Bool),
      (fun k => if k ∈ S then x k else (Function.update σ j b) k)
        = Function.update (fun k => if k ∈ S then x k else σ k) j b := by
    intro b x
    funext k
    by_cases hk : k = j
    · subst hk; simp [hj]
    · simp [Function.update_of_ne hk, hk]
  have h2 : (0:ℝ) < 2 ^ n := by positivity
  unfold avgOn
  simp only [hmix]
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, abs_div, abs_of_pos h2,
    div_le_iff₀ h2]
  calc |∑ x : Fin n → Bool,
          (f (Function.update (fun k => if k ∈ S then x k else σ k) j false)
            - f (Function.update (fun k => if k ∈ S then x k else σ k) j true))|
      ≤ ∑ x : Fin n → Bool,
          |f (Function.update (fun k => if k ∈ S then x k else σ k) j false)
            - f (Function.update (fun k => if k ∈ S then x k else σ k) j true)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Fin n → Bool, c := Finset.sum_le_sum (fun x _ => hosc _)
    _ = c * 2 ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul, cube_card]
        ring


/-- One averaging step: integrating out coordinate `j` costs a factor `exp(λ²c²/8)`. -/
lemma mgf_step (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S)
    (f : (Fin n → Bool) → ℝ) (c lam : ℝ)
    (hosc : ∀ τ : Fin n → Bool,
      |f (Function.update τ j false) - f (Function.update τ j true)| ≤ c) :
    ∑ σ : Fin n → Bool, Real.exp (lam * avgOn S f σ)
      ≤ Real.exp (lam ^ 2 * c ^ 2 / 8)
          * ∑ σ : Fin n → Bool, Real.exp (lam * avgOn (insert j S) f σ) := by
  rw [sum_pair_split j (fun σ => Real.exp (lam * avgOn S f σ)), Finset.mul_sum]
  refine Finset.sum_le_sum (fun σ _ => ?_)
  have hm : avgOn (insert j S) f σ
      = (avgOn S f (Function.update σ j false) + avgOn S f (Function.update σ j true)) / 2 :=
    avgOn_insert S j hj f σ
  have hd := avgOn_osc S j hj f c hosc σ
  set u := avgOn S f (Function.update σ j false) with hu
  set v := avgOn S f (Function.update σ j true) with hv
  have hd' := abs_le.mp hd
  have hsq : (u - v) ^ 2 ≤ c ^ 2 := by nlinarith [hd'.1, hd'.2]
  have e1 : Real.exp (lam * u)
      = Real.exp (lam * ((u + v) / 2)) * Real.exp (lam * (u - v) / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (lam * v)
      = Real.exp (lam * ((u + v) / 2)) * Real.exp (-(lam * (u - v) / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hcosh : (Real.exp (lam * u) + Real.exp (lam * v)) / 2
      = Real.exp (lam * ((u + v) / 2)) * Real.cosh (lam * (u - v) / 2) := by
    rw [Real.cosh_eq, e1, e2]; ring
  rw [hm, hcosh]
  have hbound : Real.cosh (lam * (u - v) / 2) ≤ Real.exp (lam ^ 2 * c ^ 2 / 8) := by
    refine (Real.cosh_le_exp_half_sq _).trans (Real.exp_le_exp.mpr ?_)
    nlinarith [sq_nonneg lam, mul_le_mul_of_nonneg_left hsq (sq_nonneg lam)]
  calc Real.exp (lam * ((u + v) / 2)) * Real.cosh (lam * (u - v) / 2)
      ≤ Real.exp (lam * ((u + v) / 2)) * Real.exp (lam ^ 2 * c ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg _)
    _ = Real.exp (lam ^ 2 * c ^ 2 / 8) * Real.exp (lam * ((u + v) / 2)) := by ring

/-- Iterating the averaging step over a set of coordinates. -/
lemma mgf_induct (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ) (lam : ℝ)
    (hosc : ∀ (j : Fin n) (τ : Fin n → Bool),
      |f (Function.update τ j false) - f (Function.update τ j true)| ≤ c j) :
    ∀ U : Finset (Fin n), ∀ S : Finset (Fin n), Disjoint U S →
      ∑ σ : Fin n → Bool, Real.exp (lam * avgOn S f σ)
        ≤ Real.exp (lam ^ 2 * (∑ j ∈ U, (c j) ^ 2) / 8)
            * ∑ σ : Fin n → Bool, Real.exp (lam * avgOn (S ∪ U) f σ) := by
  intro U
  refine Finset.induction_on U ?_ ?_
  · intro S _
    simp
  · intro j U' hjU' ih S hdisj
    have hjS : j ∉ S := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self j U')
    have hdisj' : Disjoint U' (insert j S) := by
      rw [Finset.disjoint_insert_right]
      exact ⟨hjU', (Finset.disjoint_insert_left.mp hdisj).2⟩
    have h1 := mgf_step S j hjS f (c j) lam (fun τ => hosc j τ)
    have h2 := ih (insert j S) hdisj'
    have hunion : (insert j S) ∪ U' = S ∪ insert j U' := by
      ext k
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [hunion] at h2
    rw [Finset.sum_insert hjU']
    have hexp : Real.exp (lam ^ 2 * (c j) ^ 2 / 8)
          * Real.exp (lam ^ 2 * (∑ k ∈ U', (c k) ^ 2) / 8)
        = Real.exp (lam ^ 2 * ((c j) ^ 2 + ∑ k ∈ U', (c k) ^ 2) / 8) := by
      rw [← Real.exp_add]; congr 1; ring
    calc ∑ σ : Fin n → Bool, Real.exp (lam * avgOn S f σ)
        ≤ Real.exp (lam ^ 2 * (c j) ^ 2 / 8)
            * ∑ σ : Fin n → Bool, Real.exp (lam * avgOn (insert j S) f σ) := h1
      _ ≤ Real.exp (lam ^ 2 * (c j) ^ 2 / 8)
            * (Real.exp (lam ^ 2 * (∑ k ∈ U', (c k) ^ 2) / 8)
              * ∑ σ : Fin n → Bool, Real.exp (lam * avgOn (S ∪ insert j U') f σ)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
      _ = Real.exp (lam ^ 2 * ((c j) ^ 2 + ∑ k ∈ U', (c k) ^ 2) / 8)
            * ∑ σ : Fin n → Bool, Real.exp (lam * avgOn (S ∪ insert j U') f σ) := by
          rw [← mul_assoc, hexp]

/-- The bounded-differences moment generating function bound, as a counting statement. -/
theorem mgf_bound (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ) (lam : ℝ)
    (hosc : ∀ (j : Fin n) (τ : Fin n → Bool),
      |f (Function.update τ j false) - f (Function.update τ j true)| ≤ c j) :
    ∑ σ : Fin n → Bool, Real.exp (lam * f σ)
      ≤ Real.exp (lam ^ 2 * (∑ j, (c j) ^ 2) / 8)
          * (2 ^ n * Real.exp (lam * ((∑ τ : Fin n → Bool, f τ) / 2 ^ n))) := by
  have h := mgf_induct f c lam hosc Finset.univ ∅ (by simp)
  simp only [avgOn_empty, Finset.empty_union, avgOn_univ] at h
  rw [Finset.sum_const, nsmul_eq_mul, cube_card] at h
  exact h

/-- McDiarmid's inequality, counting form: the upper tail. -/
theorem mcd_upper (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ)
    (hosc : ∀ (j : Fin n) (τ : Fin n → Bool),
      |f (Function.update τ j false) - f (Function.update τ j true)| ≤ c j)
    (V : ℝ) (hV : 0 < V) (hVc : ∑ j, (c j) ^ 2 ≤ V) (s : ℝ) (hs : 0 < s) :
    ((Finset.univ.filter (fun σ : Fin n → Bool =>
        (∑ τ : Fin n → Bool, f τ) / 2 ^ n + s ≤ f σ)).card : ℝ)
      ≤ 2 ^ n * Real.exp (-(2 * s ^ 2) / V) := by
  classical
  have hVne : V ≠ 0 := ne_of_gt hV
  set m : ℝ := (∑ τ : Fin n → Bool, f τ) / 2 ^ n with hm
  obtain ⟨lam, hlamdef⟩ : ∃ lam : ℝ, lam = 4 * s / V := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlamdef]; positivity
  set B := Finset.univ.filter (fun σ : Fin n → Bool => m + s ≤ f σ) with hB
  set g : (Fin n → Bool) → ℝ :=
    fun σ => Real.exp (-(lam * (m + s))) * Real.exp (lam * f σ) with hg
  have hone : ∀ σ ∈ B, (1:ℝ) ≤ g σ := by
    intro σ hσ
    have hσ' : m + s ≤ f σ := (Finset.mem_filter.mp hσ).2
    have hstep : Real.exp 0 ≤ Real.exp (-(lam * (m + s)) + lam * f σ) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    simpa [hg, ← Real.exp_add] using hstep
  have h1 : (B.card : ℝ) ≤ ∑ σ ∈ B, g σ := by
    have := Finset.card_nsmul_le_sum B g 1 hone
    simpa using this
  have h2 : ∑ σ ∈ B, g σ ≤ ∑ σ : Fin n → Bool, g σ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro σ _ _
    positivity
  have h3 : ∑ σ : Fin n → Bool, g σ
      = Real.exp (-(lam * (m + s))) * ∑ σ : Fin n → Bool, Real.exp (lam * f σ) := by
    rw [hg, ← Finset.mul_sum]
  have h4 := mgf_bound f c lam hosc
  rw [← hm] at h4
  have h5 : Real.exp (lam ^ 2 * (∑ j, (c j) ^ 2) / 8) ≤ Real.exp (lam ^ 2 * V / 8) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg lam]
  have h6 : ∑ σ : Fin n → Bool, Real.exp (lam * f σ)
      ≤ Real.exp (lam ^ 2 * V / 8) * (2 ^ n * Real.exp (lam * m)) := by
    refine h4.trans ?_
    exact mul_le_mul_of_nonneg_right h5 (by positivity)
  have hkey : -(lam * (m + s)) + (lam ^ 2 * V / 8 + lam * m) = -(2 * s ^ 2) / V := by
    rw [hlamdef]
    field_simp
    ring
  have hfin : Real.exp (-(lam * (m + s)))
        * (Real.exp (lam ^ 2 * V / 8) * (2 ^ n * Real.exp (lam * m)))
      = 2 ^ n * Real.exp (-(2 * s ^ 2) / V) := by
    calc Real.exp (-(lam * (m + s)))
          * (Real.exp (lam ^ 2 * V / 8) * (2 ^ n * Real.exp (lam * m)))
        = 2 ^ n * (Real.exp (-(lam * (m + s)))
            * (Real.exp (lam ^ 2 * V / 8) * Real.exp (lam * m))) := by ring
      _ = 2 ^ n * Real.exp (-(lam * (m + s)) + (lam ^ 2 * V / 8 + lam * m)) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ = 2 ^ n * Real.exp (-(2 * s ^ 2) / V) := by rw [hkey]
  calc (B.card : ℝ) ≤ ∑ σ ∈ B, g σ := h1
    _ ≤ ∑ σ : Fin n → Bool, g σ := h2
    _ = Real.exp (-(lam * (m + s))) * ∑ σ : Fin n → Bool, Real.exp (lam * f σ) := h3
    _ ≤ Real.exp (-(lam * (m + s)))
          * (Real.exp (lam ^ 2 * V / 8) * (2 ^ n * Real.exp (lam * m))) :=
        mul_le_mul_of_nonneg_left h6 (Real.exp_nonneg _)
    _ = 2 ^ n * Real.exp (-(2 * s ^ 2) / V) := hfin

/-- McDiarmid's inequality, counting form: the lower tail. -/
theorem mcd_lower (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ)
    (hosc : ∀ (j : Fin n) (τ : Fin n → Bool),
      |f (Function.update τ j false) - f (Function.update τ j true)| ≤ c j)
    (V : ℝ) (hV : 0 < V) (hVc : ∑ j, (c j) ^ 2 ≤ V) (s : ℝ) (hs : 0 < s) :
    ((Finset.univ.filter (fun σ : Fin n → Bool =>
        f σ ≤ (∑ τ : Fin n → Bool, f τ) / 2 ^ n - s)).card : ℝ)
      ≤ 2 ^ n * Real.exp (-(2 * s ^ 2) / V) := by
  classical
  have hosc' : ∀ (j : Fin n) (τ : Fin n → Bool),
      |(fun σ => -f σ) (Function.update τ j false)
        - (fun σ => -f σ) (Function.update τ j true)| ≤ c j := by
    intro j τ
    show |-f (Function.update τ j false) - -f (Function.update τ j true)| ≤ c j
    rw [show -f (Function.update τ j false) - -f (Function.update τ j true)
        = -(f (Function.update τ j false) - f (Function.update τ j true)) from by ring, abs_neg]
    exact hosc j τ
  have h := mcd_upper (fun σ => -f σ) c hosc' V hV hVc s hs
  have hsum : ∑ τ : Fin n → Bool, (fun σ => -f σ) τ = -∑ τ : Fin n → Bool, f τ := by
    simp
  rw [hsum] at h
  have hset : (Finset.univ.filter (fun σ : Fin n → Bool =>
        (-∑ τ : Fin n → Bool, f τ) / 2 ^ n + s ≤ -f σ))
      = (Finset.univ.filter (fun σ : Fin n → Bool =>
        f σ ≤ (∑ τ : Fin n → Bool, f τ) / 2 ^ n - s)) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, neg_div]
    constructor <;> intro hx <;> linarith
  rw [hset] at h
  exact h


/-- Two filters that agree away from one point have cardinalities within one. -/
lemma card_filter_le_succ (T : Finset (Fin n)) (j : Fin n) (P Q : Fin n → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ k, k ≠ j → (P k ↔ Q k)) :
    (T.filter P).card ≤ (T.filter Q).card + 1 := by
  classical
  have hsub : T.filter P ⊆ insert j (T.filter Q) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    by_cases hkj : k = j
    · subst hkj; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hk.1, (h k hkj).mp hk.2⟩)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_insert_le _ _)

/-- Hamming distance restricted to `T` is `1`-Lipschitz in each coordinate. -/
lemma dT_lip (T : Finset (Fin n)) (j : Fin n) (σ τ : Fin n → Bool) :
    |((T.filter (fun k => Function.update σ j false k ≠ τ k)).card : ℝ)
      - ((T.filter (fun k => Function.update σ j true k ≠ τ k)).card : ℝ)| ≤ 1 := by
  classical
  have hagree : ∀ (b b' : Bool) (k : Fin n), k ≠ j →
      ((Function.update σ j b k ≠ τ k) ↔ (Function.update σ j b' k ≠ τ k)) := by
    intro b b' k hk
    rw [Function.update_of_ne hk, Function.update_of_ne hk]
  have h1 := card_filter_le_succ T j _ _ (hagree false true)
  have h2 := card_filter_le_succ T j _ _ (hagree true false)
  have h1' : ((T.filter (fun k => Function.update σ j false k ≠ τ k)).card : ℝ)
      ≤ ((T.filter (fun k => Function.update σ j true k ≠ τ k)).card : ℝ) + 1 := by
    exact_mod_cast h1
  have h2' : ((T.filter (fun k => Function.update σ j true k ≠ τ k)).card : ℝ)
      ≤ ((T.filter (fun k => Function.update σ j false k ≠ τ k)).card : ℝ) + 1 := by
    exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-- Coordinates outside `T` do not affect the restricted Hamming distance. -/
lemma dT_const (T : Finset (Fin n)) (j : Fin n) (hj : j ∉ T) (σ τ : Fin n → Bool) :
    (T.filter (fun k => Function.update σ j false k ≠ τ k))
      = (T.filter (fun k => Function.update σ j true k ≠ τ k)) := by
  classical
  refine Finset.filter_congr (fun k hk => ?_)
  have hkj : k ≠ j := fun h => hj (h ▸ hk)
  rw [Function.update_of_ne hkj, Function.update_of_ne hkj]

/-- The infimum over a finite set is `c`-Lipschitz in the family. -/
lemma inf'_lip {ι : Type} (G : Finset ι) (hG : G.Nonempty) (a b : ι → ℝ) (c : ℝ)
    (h : ∀ x ∈ G, |a x - b x| ≤ c) :
    |G.inf' hG a - G.inf' hG b| ≤ c := by
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_inf' hG a
  obtain ⟨y, hy, hye⟩ := Finset.exists_mem_eq_inf' hG b
  have h1 : G.inf' hG b ≤ b x := Finset.inf'_le b hx
  have h2 : G.inf' hG a ≤ a y := Finset.inf'_le a hy
  have hax := abs_le.mp (h x hx)
  have hay := abs_le.mp (h y hy)
  rw [abs_le]
  constructor <;> linarith


/-- **Far pair.**  A subset of the cube of density at least `e^{-K}` whose parameters satisfy
`2K < θ²|T|` contains two points differing in at least `(1-θ)|T|` coordinates of `T`. -/
theorem far_pair (T : Finset (Fin n)) (F : Finset (Fin n → Bool)) (hF : F.Nonempty)
    (θ K : ℝ) (hθ0 : 0 < θ) (hK0 : 0 < K)
    (htpos : (0:ℝ) < (T.card : ℝ))
    (hcard : 2 ^ n * Real.exp (-K) ≤ (F.card : ℝ))
    (hcrit : 2 * K < θ ^ 2 * (T.card : ℝ)) :
    ∃ σ ∈ F, ∃ ρ ∈ F,
      (1 - θ) * (T.card : ℝ) ≤ ((T.filter (fun j => σ j ≠ ρ j)).card : ℝ) := by
  classical
  set t : ℝ := (T.card : ℝ) with ht
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  set G : Finset (Fin n → Bool) := F.image (fun ρ => fun j => !ρ j) with hGdef
  have hGne : G.Nonempty := hF.image _
  set f : (Fin n → Bool) → ℝ :=
    fun σ => G.inf' hGne (fun τ => ((T.filter (fun j => σ j ≠ τ j)).card : ℝ)) with hfdef
  set c : Fin n → ℝ := fun j => if j ∈ T then 1 else 0 with hcdef
  have hosc : ∀ (j : Fin n) (τ : Fin n → Bool),
      |f (Function.update τ j false) - f (Function.update τ j true)| ≤ c j := by
    intro j τ
    by_cases hjT : j ∈ T
    · have hc1 : c j = 1 := by simp [hcdef, hjT]
      rw [hc1, hfdef]
      exact inf'_lip G hGne _ _ 1 (fun x _ => dT_lip T j τ x)
    · have hc0 : c j = 0 := by simp [hcdef, hjT]
      rw [hc0, hfdef]
      have heq : (fun x : Fin n → Bool =>
            ((T.filter (fun k => Function.update τ j false k ≠ x k)).card : ℝ))
          = (fun x : Fin n → Bool =>
            ((T.filter (fun k => Function.update τ j true k ≠ x k)).card : ℝ)) := by
        funext x
        rw [dT_const T j hjT τ x]
      simp only [heq, sub_self, abs_zero]
      exact le_refl 0
  have hV : ∑ j, (c j) ^ 2 = t := by
    have hsq : ∀ j : Fin n, (c j) ^ 2 = if j ∈ T then (1:ℝ) else 0 := by
      intro j
      by_cases hj : j ∈ T <;> simp [hcdef, hj]
    have hfil : (Finset.univ.filter (fun j : Fin n => j ∈ T)) = T := by
      ext j; simp
    simp only [hsq]
    rw [← Finset.sum_filter, hfil, Finset.sum_const, nsmul_eq_mul, mul_one, ht]
  have hf0 : ∀ σ, 0 ≤ f σ := by
    intro σ
    rw [hfdef]
    exact Finset.le_inf' hGne _ (fun x _ => by positivity)
  have hfG : ∀ σ ∈ G, f σ = 0 := by
    intro σ hσ
    have hle : f σ ≤ ((T.filter (fun j => σ j ≠ σ j)).card : ℝ) := by
      rw [hfdef]; exact Finset.inf'_le _ hσ
    have hz : (T.filter (fun j => σ j ≠ σ j)) = ∅ := by ext j; simp
    rw [hz] at hle
    simp only [Finset.card_empty, Nat.cast_zero] at hle
    exact le_antisymm hle (hf0 σ)
  have hGcard : G.card = F.card := by
    rw [hGdef]
    refine Finset.card_image_of_injective F ?_
    intro x y hxy
    funext j
    have hj := congrFun hxy j
    simpa using hj
  set m : ℝ := (∑ τ : Fin n → Bool, f τ) / 2 ^ n with hmdef
  have hm0 : 0 ≤ m := by
    rw [hmdef]
    exact div_nonneg (Finset.sum_nonneg (fun σ _ => hf0 σ)) (le_of_lt h2n)
  have hmean : 2 * m ^ 2 ≤ K * t := by
    rcases eq_or_lt_of_le hm0 with hm | hm
    · have : m = 0 := hm.symm
      rw [this]
      have := mul_pos hK0 htpos
      nlinarith
    · have hlow := mcd_lower f c hosc t htpos (le_of_eq hV) m hm
      rw [← hmdef] at hlow
      have hGsub : G ⊆ Finset.univ.filter (fun σ : Fin n → Bool => f σ ≤ m - m) := by
        intro σ hσ
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hfG σ hσ, sub_self]
      have hGle : (G.card : ℝ)
          ≤ ((Finset.univ.filter (fun σ : Fin n → Bool => f σ ≤ m - m)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hGsub
      rw [hGcard] at hGle
      have hchain : 2 ^ n * Real.exp (-K) ≤ 2 ^ n * Real.exp (-(2 * m ^ 2) / t) := by
        linarith
      have hexp : Real.exp (-K) ≤ Real.exp (-(2 * m ^ 2) / t) :=
        le_of_mul_le_mul_left hchain h2n
      have hfin : -K ≤ -(2 * m ^ 2) / t := Real.exp_le_exp.mp hexp
      rw [le_div_iff₀ htpos] at hfin
      linarith
  have hmt : 2 * m < θ * t := by
    by_contra hcon
    push_neg at hcon
    have htp : (0:ℝ) ≤ θ * t := le_of_lt (mul_pos hθ0 htpos)
    have h1 : θ * t * (θ * t) ≤ 2 * m * (2 * m) :=
      mul_le_mul hcon hcon htp (by linarith)
    nlinarith [hmean, mul_lt_mul_of_pos_right hcrit htpos, h1]
  set s : ℝ := θ * t - m with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hKt : K * t < 2 * s ^ 2 := by
    have hs1 : θ * t / 2 < s := by rw [hsdef]; linarith
    have hpos : (0:ℝ) < θ * t / 2 := by
      have := mul_pos hθ0 htpos
      linarith
    have hsq : (θ * t / 2) ^ 2 < s ^ 2 := by
      nlinarith [mul_pos (sub_pos.mpr hs1) (by linarith : (0:ℝ) < s + θ * t / 2)]
    nlinarith [mul_lt_mul_of_pos_right hcrit htpos, hsq]
  have hup := mcd_upper f c hosc t htpos (le_of_eq hV) s hs0
  rw [← hmdef] at hup
  have hstrict : 2 ^ n * Real.exp (-(2 * s ^ 2) / t) < 2 ^ n * Real.exp (-K) := by
    refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr ?_) h2n
    rw [div_lt_iff₀ htpos]
    linarith
  have hex : ∃ σ ∈ F, f σ < m + s := by
    by_contra hcon
    push_neg at hcon
    have hFsub : F ⊆ Finset.univ.filter (fun σ : Fin n → Bool => m + s ≤ f σ) :=
      fun σ hσ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon σ hσ⟩
    have hFle : (F.card : ℝ)
        ≤ ((Finset.univ.filter (fun σ : Fin n → Bool => m + s ≤ f σ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hFsub
    linarith
  obtain ⟨σ, hσF, hσlt⟩ := hex
  have hms : m + s = θ * t := by rw [hsdef]; ring
  obtain ⟨τ, hτG, hτe⟩ := Finset.exists_mem_eq_inf' hGne
      (fun x : Fin n → Bool => ((T.filter (fun j => σ j ≠ x j)).card : ℝ))
  have hfσ : f σ = ((T.filter (fun j => σ j ≠ τ j)).card : ℝ) := by
    rw [hfdef]; exact hτe
  rw [hGdef] at hτG
  obtain ⟨ρ, hρF, hρe⟩ := Finset.mem_image.mp hτG
  refine ⟨σ, hσF, ρ, hρF, ?_⟩
  have hiff : ∀ j, (σ j ≠ τ j) ↔ ¬ (σ j ≠ ρ j) := by
    intro j
    have hτj : τ j = !ρ j := (congrFun hρe j).symm
    rw [hτj]
    cases hσj : σ j <;> cases hρj : ρ j <;> simp [hσj, hρj]
  have hfe : (T.filter (fun j => σ j ≠ τ j)) = T.filter (fun j => ¬ (σ j ≠ ρ j)) :=
    Finset.filter_congr (fun j _ => hiff j)
  have hcompl : (T.filter (fun j => σ j ≠ ρ j)).card
      + (T.filter (fun j => σ j ≠ τ j)).card = T.card := by
    rw [hfe]
    exact Finset.card_filter_add_card_filter_not (s := T) (fun j => σ j ≠ ρ j)
  have hcast : ((T.filter (fun j => σ j ≠ ρ j)).card : ℝ)
      + ((T.filter (fun j => σ j ≠ τ j)).card : ℝ) = t := by
    rw [ht]
    exact_mod_cast hcompl
  rw [← hfσ] at hcast
  linarith

end SpencerMcD

open SpencerAux SpencerEnt SpencerPCL SpencerMcD in
/-- **Spencer's partial colouring lemma.** -/
theorem solution (n : ℕ) (A : Fin n → Fin n → ℝ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (T : Finset (Fin n)) (hT : 0 < T.card)
    (θ ν : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2) (hν : 2 ≤ ν)
    (hbudget : (n : ℝ) * (2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2))
        ≤ (2 / 3) * θ ^ 2 * (T.card : ℝ)) :
    ∃ χ : Fin n → ℝ,
      (∀ j, χ j = 1 ∨ χ j = -1 ∨ χ j = 0) ∧
      (∀ j, j ∉ T → χ j = 0) ∧
      (1 - θ) * (T.card : ℝ) ≤ ((T.filter (fun j => χ j ≠ 0)).card : ℝ) ∧
      (∀ i, |∑ j ∈ T, A i j * χ j| ≤ ν * Real.sqrt (T.card : ℝ)) := by
  classical
  set t : ℝ := (T.card : ℝ) with ht
  have htpos : (0:ℝ) < t := by rw [ht]; exact_mod_cast hT
  have hν0 : (0:ℝ) < ν := by linarith
  set D : ℝ := ν * Real.sqrt t with hD
  have hD0 : 0 < D := by rw [hD]; exact mul_pos hν0 (Real.sqrt_pos.mpr htpos)
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  -- each row of a 0/1 matrix has square sum at most |T|
  have hrow : ∀ i : Fin n, ∑ j ∈ T, (A i j) ^ 2 ≤ t := by
    intro i
    have hle : ∑ j ∈ T, (A i j) ^ 2 ≤ ∑ _j ∈ T, (1:ℝ) := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      rcases h01 i j with h | h <;> rw [h] <;> norm_num
    have hone : ∑ _j ∈ T, (1:ℝ) = t := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, ht]
    rw [hone] at hle
    exact hle
  -- the signature map
  set Φ : (Fin n → Bool) → (Fin n → ℤ) := fun σ => fun i => bucket T (A i) D σ with hΦ
  have hentrow : ∀ i : Fin n, ent (fun σ => Φ σ i)
      ≤ 2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2) := by
    intro i
    have hfun : (fun σ : Fin n → Bool => Φ σ i) = bucket T (A i) D := by
      funext σ
      simp only [hΦ]
    rw [hfun, hD]
    exact ent_bucket_le T (A i) t htpos (hrow i) ν hν
  have hent : ent Φ ≤ (2 / 3) * θ ^ 2 * t := by
    refine le_trans (ent_le_sum Φ) ?_
    calc ∑ i : Fin n, ent (fun σ => Φ σ i)
        ≤ ∑ _i : Fin n, (2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2)) :=
          Finset.sum_le_sum (fun i _ => hentrow i)
      _ = (n : ℝ) * (2 * Real.exp (-(ν ^ 2) / 2) * (3 * ν ^ 2 / 4 + 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (2 / 3) * θ ^ 2 * t := hbudget
  -- a large fibre
  obtain ⟨b, hb⟩ := exists_fibre_large Φ
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := (2 / 3) * θ ^ 2 * t * Real.log 2 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  have hprb : Real.exp (-K) ≤ pr Φ b := by
    refine le_trans ?_ hb
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    rw [hK]
    nlinarith [mul_le_mul_of_nonneg_left hent (le_of_lt hlog2)]
  set F : Finset (Fin n → Bool) := Finset.univ.filter (fun σ => Φ σ = b) with hF
  have hFcard : 2 ^ n * Real.exp (-K) ≤ (F.card : ℝ) := by
    have hpr : pr Φ b = (F.card : ℝ) / 2 ^ n := by
      rw [hF]
      unfold pr
      rw [card_univ_bool]
    rw [hpr, le_div_iff₀ h2n] at hprb
    linarith
  have hFne : F.Nonempty := by
    rw [← Finset.card_pos]
    have hpos : (0:ℝ) < (F.card : ℝ) := lt_of_lt_of_le (by positivity) hFcard
    exact_mod_cast hpos
  have hcrit : 2 * K < θ ^ 2 * t := by
    have hθt : (0:ℝ) < θ ^ 2 * t := by positivity
    have hlt : Real.log 2 < 0.6932 := by linarith [Real.log_two_lt_d9]
    have := mul_lt_mul_of_pos_right hlt hθt
    rw [hK]
    nlinarith [this]
  obtain ⟨σ, hσF, ρ, hρF, hfar⟩ := far_pair T F hFne θ K hθ0 hK0 htpos hFcard hcrit
  have hσb : Φ σ = b := by
    rw [hF] at hσF
    exact (Finset.mem_filter.mp hσF).2
  have hρb : Φ ρ = b := by
    rw [hF] at hρF
    exact (Finset.mem_filter.mp hρF).2
  refine ⟨fun j => if j ∈ T then (sgn (σ j) - sgn (ρ j)) / 2 else 0, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ T
    · have hval : (sgn (σ j) - sgn (ρ j)) / 2 = 1 ∨ (sgn (σ j) - sgn (ρ j)) / 2 = -1
          ∨ (sgn (σ j) - sgn (ρ j)) / 2 = 0 := by
        cases hσ : σ j <;> cases hρ : ρ j <;> norm_num [sgn, hσ, hρ]
      simpa [hj] using hval
    · simp [hj]
  · intro j hj
    simp [hj]
  · have hfe : (T.filter (fun j =>
          (if j ∈ T then (sgn (σ j) - sgn (ρ j)) / 2 else 0) ≠ 0))
        = T.filter (fun j => σ j ≠ ρ j) := by
      refine Finset.filter_congr (fun j hj => ?_)
      have hiff : ((sgn (σ j) - sgn (ρ j)) / 2 ≠ 0) ↔ (σ j ≠ ρ j) := by
        cases hσ : σ j <;> cases hρ : ρ j <;> norm_num [sgn, hσ, hρ]
      simp only [hj, if_true]
      exact hiff
    rw [hfe]
    exact hfar
  · intro i
    have hbi : bucket T (A i) D σ = bucket T (A i) D ρ := by
      have hc := congrFun (hσb.trans hρb.symm) i
      simp only [hΦ] at hc
      exact hc
    have hclose := bucket_close T (A i) D hD0 σ ρ hbi
    have hsum : ∑ j ∈ T, A i j * (if j ∈ T then (sgn (σ j) - sgn (ρ j)) / 2 else 0)
        = ((∑ j ∈ T, A i j * sgn (σ j)) - (∑ j ∈ T, A i j * sgn (ρ j))) / 2 := by
      rw [← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp only [hj, if_true]
      ring
    rw [hsum, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2),
      div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith
