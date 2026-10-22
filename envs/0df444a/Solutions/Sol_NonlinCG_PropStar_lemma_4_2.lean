-- Prove2me | solution 1 for NonlinCG.PropStar.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T04:03:06.433726+00:00
-- url     : https://prove2.me/submissions/c5c881af-9188-42f6-b447-d72db885bc30

import Mathlib
import Definitions.Def_NonlinCG_PropStar_Setting



namespace NonlinCG.PropStar

lemma l42_block (s : ℕ → ℤ) (k₀ Δ : ℕ) (hΔ : 1 ≤ Δ) (hs : ∀ j, s j ≤ 1)
    (hH : ∀ k ≥ k₀, ∑ j ∈ Finset.Ico k (k + Δ), s j ≤ 0) :
    ∀ m : ℕ, ∀ k ≥ k₀, ∑ j ∈ Finset.Ico k (k + m), s j ≤ Δ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hk
    by_cases hm : m ≤ Δ
    · calc ∑ j ∈ Finset.Ico k (k + m), s j ≤ ∑ j ∈ Finset.Ico k (k + m), (1 : ℤ) :=
            Finset.sum_le_sum (fun j _ => hs j)
        _ = m := by simp
        _ ≤ Δ := by exact_mod_cast hm
    · push_neg at hm
      have hsplit := Finset.sum_Ico_consecutive s (show k ≤ k + Δ by omega) (show k + Δ ≤ k + m by omega)
      have h1 := hH k hk
      have h2 := ih (m - Δ) (by omega) (k + Δ) (by omega)
      have e : k + Δ + (m - Δ) = k + m := by omega
      rw [e] at h2
      rw [← hsplit]
      linarith

lemma l42_growth (a : ℕ → ℝ) (s : ℕ → ℤ) (R c : ℝ) (hR : 1 ≤ R) (hc : 0 ≤ c) (k₀ Δ : ℕ)
    (hΔ : 1 ≤ Δ) (hs : ∀ j, s j ≤ 1)
    (hH : ∀ k ≥ k₀, ∑ j ∈ Finset.Ico k (k + Δ), s j ≤ 0)
    (hrec : ∀ l ≥ k₀, a (l + 1) ≤ c + R ^ (s (l + 1)) * a l) (ha : 0 ≤ a k₀) :
    ∀ l ≥ k₀, a l ≤ R ^ Δ * (a k₀ + c * ((l - k₀ : ℕ) : ℝ)) := by
  have hR0 : 0 < R := by linarith
  have hblock := l42_block s k₀ Δ hΔ hs hH
  set e : ℕ → ℤ := fun l => ∑ j ∈ Finset.Ico (k₀ + 1) (l + 1), s j with he
  set W : ℕ → ℝ := fun l => R ^ (e l) with hW
  have hWpos : ∀ l, 0 < W l := fun l => zpow_pos hR0 _
  have he0 : e k₀ = 0 := by simp [he]
  have heS : ∀ l ≥ k₀, e (l + 1) = e l + s (l + 1) := by
    intro l hl
    simp only [he]
    rw [Finset.sum_Ico_succ_top (by omega)]
  have hWS : ∀ l ≥ k₀, W (l + 1) = W l * R ^ (s (l + 1)) := by
    intro l hl
    simp only [hW]
    rw [heS l hl, zpow_add₀ hR0.ne']
  have hdiff : ∀ i l, k₀ ≤ i → i ≤ l → e l - e i ≤ Δ := by
    intro i l hi hil
    have := Finset.sum_Ico_consecutive s (show k₀ + 1 ≤ i + 1 by omega) (show i + 1 ≤ l + 1 by omega)
    have h2 := hblock (l - i) (i + 1) (by omega)
    have e3 : i + 1 + (l - i) = l + 1 := by omega
    rw [e3] at h2
    simp only [he]
    linarith
  have hWle : ∀ i l, k₀ ≤ i → i ≤ l → W l * (W i)⁻¹ ≤ R ^ Δ := by
    intro i l hi hil
    have : W l * (W i)⁻¹ = R ^ (e l - e i) := by
      simp only [hW]
      rw [zpow_sub₀ hR0.ne', div_eq_mul_inv]
    rw [this]
    calc R ^ (e l - e i) ≤ R ^ ((Δ : ℕ) : ℤ) := zpow_le_zpow_right₀ hR (hdiff i l hi hil)
      _ = R ^ Δ := zpow_natCast R Δ
  have hS : ∀ l ≥ k₀, a l ≤ W l * (a k₀ + c * ∑ i ∈ Finset.Ico (k₀ + 1) (l + 1), (W i)⁻¹) := by
    intro l hl
    induction l, hl using Nat.le_induction with
    | base => simp [hW, he0]
    | succ l hl ih =>
      have h1 := hrec l hl
      have hpos : 0 ≤ R ^ (s (l + 1)) := (zpow_pos hR0 _).le
      have h2 : R ^ (s (l + 1)) * a l ≤ R ^ (s (l + 1)) * (W l * (a k₀ + c * ∑ i ∈ Finset.Ico (k₀ + 1) (l + 1), (W i)⁻¹)) :=
        mul_le_mul_of_nonneg_left ih hpos
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hWn := hWS l hl
      have hw := hWpos l
      have ht : 0 < R ^ (s (l + 1)) := zpow_pos hR0 _
      generalize (∑ i ∈ Finset.Ico (k₀ + 1) (l + 1), (W i)⁻¹) = S at *
      generalize R ^ (s (l + 1)) = t at *
      have e4 : W (l + 1) * (a k₀ + c * (S + (W (l + 1))⁻¹)) = t * (W l * (a k₀ + c * S)) + c := by
        rw [hWn]
        field_simp
        ring
      rw [e4]
      linarith
  intro l hl
  have h1 := hS l hl
  have hWk : W l ≤ R ^ Δ := by
    have := hWle k₀ l le_rfl hl
    have hk : W k₀ = 1 := by simp [hW, he0]
    rw [hk, inv_one, mul_one] at this
    exact this
  have h2 : W l * (a k₀ + c * ∑ i ∈ Finset.Ico (k₀ + 1) (l + 1), (W i)⁻¹) ≤
      R ^ Δ * (a k₀ + c * ((l - k₀ : ℕ) : ℝ)) := by
    rw [mul_add, mul_left_comm, Finset.mul_sum]
    have h3 : ∑ i ∈ Finset.Ico (k₀ + 1) (l + 1), W l * (W i)⁻¹ ≤
        ∑ i ∈ Finset.Ico (k₀ + 1) (l + 1), R ^ Δ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact hWle i l (by omega) (by omega)
    have h4 : ∑ i ∈ Finset.Ico (k₀ + 1) (l + 1), R ^ Δ = ((l - k₀ : ℕ) : ℝ) * R ^ Δ := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [h4] at h3
    have h5 : W l * a k₀ ≤ R ^ Δ * a k₀ := mul_le_mul_of_nonneg_right hWk ha
    nlinarith [mul_le_mul_of_nonneg_left h3 hc]
  linarith


lemma l42_gbound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (x : ℕ → E) (x₁ : E)
    (hb : Bornology.IsBounded (NonlinCG.FRBound.levelSet f x₁))
    (hL : ∀ k ≥ 1, x k ∈ NonlinCG.FRBound.levelSet f x₁) :
    ∃ G : ℝ, ∀ k ≥ 1, ‖NonlinCG.FRBound.g f x k‖ ≤ G := by
  have hcl : IsClosed (NonlinCG.FRBound.levelSet f x₁) :=
    isClosed_le hf.continuous continuous_const
  have hcomp : IsCompact (NonlinCG.FRBound.levelSet f x₁) :=
    Metric.isCompact_of_isClosed_isBounded hcl hb
  have hcont : Continuous (fun y : E => gradient f y) := by
    have h1 : Continuous (fun y : E => fderiv ℝ f y) := hf.continuous_fderiv one_ne_zero
    have : (fun y : E => gradient f y) = fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f y) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp h1
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨C, fun k hk => hC _ (hL k hk)⟩

theorem lemma42_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hA : NonlinCG.FRBound.Assumptions21 f (x 1)) (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hL : ∀ k ≥ 1, x k ∈ NonlinCG.FRBound.levelSet f (x 1))
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (hP : PropertyStar f β x)
    (h43 : ∃ γ > 0, ∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖) :
    ∃ lam > 0, ∀ Δ : ℕ, 1 ≤ Δ → ∀ k₀ : ℕ, ∃ k ≥ k₀, Δ < 2 * (Kset lam x k Δ).card := by
  obtain ⟨γ, hγ, hg⟩ := h43
  obtain ⟨G, hG⟩ := l42_gbound f hf x (x 1) hA.1 hL
  obtain ⟨b, hb1, lam, hlam, hbl⟩ := hP γ G hγ (fun k hk => ⟨hg k hk, hG k hk⟩)
  refine ⟨lam, hlam, ?_⟩
  intro Δ hΔ k₀
  by_contra hcon
  push_neg at hcon
  have hG0 : 0 ≤ G := le_trans (norm_nonneg _) (hG 1 le_rfl)
  have hdne : ∀ k ≥ 1, d k ≠ 0 := by
    intro k hk h0
    have h1 := hD k hk
    rw [h0, inner_zero_right] at h1
    have h2 : 0 < ‖NonlinCG.FRBound.g f x k‖ := lt_of_lt_of_le hγ (hg k hk)
    nlinarith [hσ₃.1, mul_pos hσ₃.1 (pow_pos h2 2)]
  set K₀ := max k₀ 2 with hK₀
  have hK2 : 2 ≤ K₀ := le_max_right _ _
  have hK0 : k₀ ≤ K₀ := le_max_left _ _
  let s : ℕ → ℤ := fun j => if lam < ‖x j - x (j - 1)‖ then 1 else -1
  have hs : ∀ j, s j ≤ 1 := by
    intro j; simp only [s]; split_ifs <;> norm_num
  have hH : ∀ k ≥ K₀, ∑ j ∈ Finset.Ico k (k + Δ), s j ≤ 0 := by
    intro k hk
    have hc := hcon k (by omega)
    have hset : Kset lam x k Δ = (Finset.Ico k (k + Δ)).filter (fun i => lam < ‖x i - x (i - 1)‖) := by
      ext i
      simp only [Kset, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, by omega⟩, h4⟩
      · rintro ⟨⟨h1, h2⟩, h4⟩; exact ⟨⟨h1, by omega⟩, by omega, h4⟩
    rw [hset] at hc
    simp only [s]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
    have hcard := Finset.card_filter_add_card_filter_not (s := Finset.Ico k (k + Δ))
      (fun i => lam < ‖x i - x (i - 1)‖)
    rw [Nat.card_Ico, show k + Δ - k = Δ by omega] at hcard
    have : ((Finset.filter (fun i => lam < ‖x i - x (i - 1)‖) (Finset.Ico k (k + Δ))).card : ℤ) +
        ((Finset.filter (fun i => ¬ lam < ‖x i - x (i - 1)‖) (Finset.Ico k (k + Δ))).card : ℤ) = Δ := by
      exact_mod_cast hcard
    omega
  have hb0 : 0 < b := by linarith
  have hR1 : 1 ≤ 2 * b ^ 2 := by nlinarith
  have hrec : ∀ l ≥ K₀, ‖d (l + 1)‖ ^ 2 ≤ 2 * G ^ 2 + (2 * b ^ 2) ^ (s (l + 1)) * ‖d l‖ ^ 2 := by
    intro l hl
    have hd := hrun.2.1 (l + 1) (by omega)
    have hd' : d (l + 1) = -NonlinCG.FRBound.g f x (l + 1) + β (l + 1) • d l := by
      simpa using hd
    have hnorm : ‖d (l + 1)‖ ≤ G + |β (l + 1)| * ‖d l‖ := by
      rw [hd']
      calc ‖-NonlinCG.FRBound.g f x (l + 1) + β (l + 1) • d l‖
          ≤ ‖-NonlinCG.FRBound.g f x (l + 1)‖ + ‖β (l + 1) • d l‖ := norm_add_le _ _
        _ ≤ G + |β (l + 1)| * ‖d l‖ := by
          rw [norm_neg, norm_smul, Real.norm_eq_abs]
          have := hG (l + 1) (by omega)
          linarith
    have hsq : ‖d (l + 1)‖ ^ 2 ≤ 2 * G ^ 2 + 2 * (β (l + 1)) ^ 2 * ‖d l‖ ^ 2 := by
      have h0 : 0 ≤ ‖d (l + 1)‖ := norm_nonneg _
      have h1 : ‖d (l + 1)‖ ^ 2 ≤ (G + |β (l + 1)| * ‖d l‖) ^ 2 := pow_le_pow_left₀ h0 hnorm 2
      have h2 : (|β (l + 1)| * ‖d l‖) ^ 2 = (β (l + 1)) ^ 2 * ‖d l‖ ^ 2 := by
        rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg (G - |β (l + 1)| * ‖d l‖)]
    have hbl' := hbl (l + 1) (by omega)
    have hl1 : l + 1 - 1 = l := by omega
    rw [hl1] at hbl'
    obtain ⟨hb1', hb2'⟩ := hbl'
    have hsl : s (l + 1) = if lam < ‖x (l + 1) - x l‖ then 1 else -1 := by
      simp only [s, hl1]
    by_cases hc : lam < ‖x (l + 1) - x l‖
    · rw [hsl, if_pos hc, zpow_one]
      have hb3 : (β (l + 1)) ^ 2 ≤ b ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb1' 2
      nlinarith [sq_nonneg ‖d l‖]
    · rw [hsl, if_neg hc, zpow_neg_one]
      have h5 := hb2' (not_lt.mp hc)
      rw [le_div_iff₀ (by positivity)] at h5
      have hb4 : 2 * (β (l + 1)) ^ 2 * (2 * b ^ 2) ≤ 1 := by
        have h6 : (|β (l + 1)| * (2 * b)) ^ 2 ≤ 1 := by
          exact pow_le_one₀ (by positivity) h5
        rw [mul_pow, sq_abs] at h6
        nlinarith
      have hb5 : 2 * (β (l + 1)) ^ 2 ≤ (2 * b ^ 2)⁻¹ := by
        rw [← one_div, le_div_iff₀ (by positivity)]
        exact hb4
      nlinarith [sq_nonneg ‖d l‖]
  have hgr := l42_growth (fun l => ‖d l‖ ^ 2) s (2 * b ^ 2) (2 * G ^ 2) hR1 (by positivity) K₀ Δ hΔ hs hH
    (fun l hl => hrec l hl) (by positivity)
  have hZ' := hZ
  unfold NonlinCG.FRBound.ZoutendijkCondition at hZ'
  have hS : Summable (fun k : ℕ => 1 / ‖d (k + 1)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (hZ'.mul_left (1 / (σ₃ ^ 2 * (γ ^ 2) ^ 2)))
    have hk : k + 1 ≥ 1 := by omega
    have hgk : γ ≤ ‖NonlinCG.FRBound.g f x (k + 1)‖ := hg (k + 1) hk
    have hD2 := hD (k + 1) hk
    have hsig := hσ₃.1
    have hsq : σ₃ * γ ^ 2 ≤ |inner ℝ (NonlinCG.FRBound.g f x (k + 1)) (d (k + 1))| := by
      have := neg_le_abs (inner ℝ (NonlinCG.FRBound.g f x (k + 1)) (d (k + 1)))
      have h7 : γ ^ 2 ≤ ‖NonlinCG.FRBound.g f x (k + 1)‖ ^ 2 := pow_le_pow_left₀ hγ.le hgk 2
      nlinarith
    have hsq2 : (σ₃ * γ ^ 2) ^ 2 ≤ inner ℝ (NonlinCG.FRBound.g f x (k + 1)) (d (k + 1)) ^ 2 := by
      rw [← sq_abs (inner ℝ _ _)]
      exact pow_le_pow_left₀ (by positivity) hsq 2
    have hD0 : 0 < ‖d (k + 1)‖ ^ 2 := by
      have := norm_pos_iff.mpr (hdne (k + 1) hk); positivity
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hD0.le
    rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity), one_mul]
    nlinarith
  have hS2 := (summable_nat_add_iff K₀).mpr hS
  set M : ℝ := (2 * b ^ 2) ^ Δ * (‖d K₀‖ ^ 2 + 2 * G ^ 2 + 1) with hM
  have hMpos : 0 < M := by positivity
  have hlow : ∀ n : ℕ, 1 / (M * ((n : ℝ) + 1)) ≤ 1 / ‖d (n + K₀ + 1)‖ ^ 2 := by
    intro n
    have hdpos : 0 < ‖d (n + K₀ + 1)‖ ^ 2 := by
      have := norm_pos_iff.mpr (hdne (n + K₀ + 1) (by omega)); positivity
    apply one_div_le_one_div_of_le hdpos
    have h1 := hgr (n + K₀ + 1) (by omega)
    have e1 : n + K₀ + 1 - K₀ = n + 1 := by omega
    rw [e1] at h1
    push_cast at h1
    have hRΔ : 0 ≤ (2 * b ^ 2) ^ Δ := by positivity
    have h2 : ‖d K₀‖ ^ 2 + 2 * G ^ 2 * ((n : ℝ) + 1) ≤ (‖d K₀‖ ^ 2 + 2 * G ^ 2 + 1) * ((n : ℝ) + 1) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [sq_nonneg ‖d K₀‖]
    calc ‖d (n + K₀ + 1)‖ ^ 2 ≤ _ := h1
      _ ≤ (2 * b ^ 2) ^ Δ * ((‖d K₀‖ ^ 2 + 2 * G ^ 2 + 1) * ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left h2 hRΔ
      _ = M * ((n : ℝ) + 1) := by rw [hM]; ring
  have hS3 : Summable (fun n : ℕ => 1 / (M * ((n : ℝ) + 1))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hlow hS2
  have hS4 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    have := hS3.mul_left M
    refine this.congr (fun n => ?_)
    field_simp
  have hS5 : Summable (fun n : ℕ => 1 / ((n : ℝ))) := by
    rw [← summable_nat_add_iff 1]
    simpa using hS4
  exact Real.not_summable_one_div_natCast hS5

end NonlinCG.PropStar

open NonlinCG.PropStar


theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hA : NonlinCG.FRBound.Assumptions21 f (x 1)) (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hL : ∀ k ≥ 1, x k ∈ NonlinCG.FRBound.levelSet f (x 1))
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (hP : PropertyStar f β x)
    (h43 : ∃ γ > 0, ∀ k ≥ 1, γ ≤ ‖NonlinCG.FRBound.g f x k‖) :
    ∃ lam > 0, ∀ Δ : ℕ, 1 ≤ Δ → ∀ k₀ : ℕ, ∃ k ≥ k₀, Δ < 2 * (Kset lam x k Δ).card := by
  exact lemma42_core f hf β α x d σ₃ hA hrun hL hZ hσ₃ hD hP h43
