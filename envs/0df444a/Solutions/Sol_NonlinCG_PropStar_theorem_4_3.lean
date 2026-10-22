-- Prove2me | solution 1 for NonlinCG.PropStar.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T20:59:04.99151+00:00
-- url     : https://prove2.me/submissions/0068ff0c-9590-4549-b747-74eecc3eab92

import Mathlib
import Definitions.Def_NonlinCG_PropStar_Setting

set_option autoImplicit false

namespace NCGProof

lemma finite_lower (h : ℕ → ℝ) (hpos : ∀ k ≥ 1, 0 < h k) :
    ∀ K : ℕ, ∃ γ > 0, ∀ k, 1 ≤ k → k < K → γ ≤ h k := by
  intro K
  induction K with
  | zero => exact ⟨1, one_pos, fun k _ hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ K ih =>
    obtain ⟨γ, hγ, hb⟩ := ih
    by_cases hK : 1 ≤ K
    · refine ⟨min γ (h K), lt_min hγ (hpos K hK), fun k hk1 hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact (min_le_left _ _).trans (hb k hk1 hk)
      · subst hk; exact min_le_right _ _
    · exact ⟨γ, hγ, fun k hk1 hk => hb k hk1 (by omega)⟩

lemma unit_diff_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (δ : ℝ) (hδ : 0 ≤ δ) :
    ‖a - b‖ ≤ 2 * ‖a - δ • b‖ := by
  have hsq : ‖δ • a - b‖ ^ 2 = ‖a - δ • b‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
      real_inner_smul_right, Real.norm_eq_abs, abs_of_nonneg hδ, ha, hb]
    ring
  have h1 := norm_nonneg (δ • a - b)
  have h2 := norm_nonneg (a - δ • b)
  have heq : ‖δ • a - b‖ = ‖a - δ • b‖ := by
    apply le_antisymm
    · nlinarith [sq_nonneg (‖δ • a - b‖ - ‖a - δ • b‖)]
    · nlinarith [sq_nonneg (‖δ • a - b‖ - ‖a - δ • b‖)]
  have hcomb : (1 + δ) • (a - b) = (a - δ • b) + (δ • a - b) := by
    simp only [add_smul, one_smul, smul_sub]; abel
  have h3 : (1 + δ) * ‖a - b‖ ≤ 2 * ‖a - δ • b‖ := by
    have := norm_add_le (a - δ • b) (δ • a - b)
    rw [← hcomb, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at this
    linarith [heq]
  nlinarith [norm_nonneg (a - b)]

lemma unroll (D a : ℕ → ℝ) (c A : ℝ) (p : ℕ) (hc : 0 ≤ c) (hA : 1 ≤ A)
    (hD : ∀ j, 0 ≤ D j) (ha0 : ∀ t, 0 ≤ a (p + t + 1)) (haA : ∀ t, a (p + t + 1) ≤ A)
    (hrec : ∀ t, D (p + t + 1) ≤ c + a (p + t + 1) * D (p + t)) :
    ∀ m : ℕ, D (p + m) ≤ (∏ t ∈ Finset.range m, a (p + t + 1)) * D p + c * m * A ^ m := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have h1 := hrec m
    have hP : 0 ≤ ∏ t ∈ Finset.range m, a (p + t + 1) :=
      Finset.prod_nonneg (fun t _ => ha0 t)
    have hAm : 1 ≤ A ^ m := one_le_pow₀ hA
    have hAm1 : A ^ (m + 1) = A ^ m * A := pow_succ A m
    have e : p + (m + 1) = p + m + 1 := by ring
    rw [e, hAm1]
    push_cast
    have key : a (p + m + 1) * D (p + m) ≤ a (p + m + 1) *
        ((∏ t ∈ Finset.range m, a (p + t + 1)) * D p + c * m * A ^ m) :=
      mul_le_mul_of_nonneg_left ih (ha0 m)
    have hcm : 0 ≤ c * (m : ℝ) * A ^ m := by
      have : (0 : ℝ) ≤ A ^ m := by linarith
      positivity
    have key2 : a (p + m + 1) * (c * m * A ^ m) ≤ A * (c * m * A ^ m) :=
      mul_le_mul_of_nonneg_right (haA m) hcm
    have hAA : 1 ≤ A ^ m * A := by nlinarith
    have hc1 : c ≤ c * (A ^ m * A) := by nlinarith
    nlinarith

lemma prod_le_one (a : ℕ → ℝ) (A : ℝ) (hA : 1 ≤ A) (Δ : ℕ) (big : ℕ → Prop) [DecidablePred big]
    (h0 : ∀ t, 0 ≤ a t) (hbig : ∀ t, a t ≤ A) (hsmall : ∀ t, ¬ big t → a t ≤ A⁻¹)
    (hcard : 2 * ((Finset.range Δ).filter big).card ≤ Δ) :
    ∏ t ∈ Finset.range Δ, a t ≤ 1 := by
  calc ∏ t ∈ Finset.range Δ, a t ≤ ∏ t ∈ Finset.range Δ, (if big t then A else A⁻¹) :=
        Finset.prod_le_prod (fun t _ => h0 t) (fun t _ => by
          split_ifs with h
          · exact hbig t
          · exact hsmall t h)
    _ = A ^ ((Finset.range Δ).filter big).card *
          A⁻¹ ^ ((Finset.range Δ).filter (fun t => ¬ big t)).card := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    _ ≤ 1 := by
        have hsum := Finset.card_filter_add_card_filter_not (s := Finset.range Δ) big
        rw [Finset.card_range] at hsum
        have hle : ((Finset.range Δ).filter big).card ≤
            ((Finset.range Δ).filter (fun t => ¬ big t)).card := by omega
        have hA0 : 0 < A := by linarith
        rw [inv_pow, ← div_eq_mul_inv, div_le_one (pow_pos hA0 _)]
        exact pow_le_pow_right₀ hA hle

lemma not_summable_lin (D0 M : ℝ) (hD0 : 0 < D0) (hM : 0 ≤ M) :
    ¬ Summable (fun n : ℕ => 1 / (D0 + n * M)) := by
  intro hs
  have hC : 0 < D0 + M := by linarith
  have h2 : Summable (fun n : ℕ => (D0 + M)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    have hpos : 0 < D0 + n * M := by positivity
    rw [inv_mul_eq_div, div_div]
    apply one_div_le_one_div_of_le hpos
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h3 : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    have := h2.mul_left (D0 + M)
    simpa [← mul_assoc, mul_inv_cancel₀ hC.ne'] using this
  exact Real.not_summable_one_div_natCast
    ((_root_.summable_nat_add_iff (f := fun m : ℕ => 1 / (m : ℝ)) 1).mp h3)

end NCGProof

set_option maxHeartbeats 1600000 in
open NonlinCG.FRBound NonlinCG.PropStar in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E) (σ₃ : ℝ)
    (hA : NonlinCG.FRBound.Assumptions21 f (x 1)) (hrun : NonlinCG.FRBound.IsCGRun f β α x d)
    (hg : ∀ k ≥ 1, NonlinCG.FRBound.g f x k ≠ 0)
    (hβ : ∀ k ≥ 2, 0 ≤ β k)
    (hL : ∀ k ≥ 1, x k ∈ NonlinCG.FRBound.levelSet f (x 1))
    (hZ : NonlinCG.FRBound.ZoutendijkCondition f x d)
    (hσ₃ : 0 < σ₃ ∧ σ₃ ≤ 1) (hD : SufficientDescent f σ₃ x d)
    (hP : PropertyStar f β x) :
    NonlinCG.FRBound.LiminfGradZero f x := by
  obtain ⟨hd1, hdk, hαx⟩ := hrun
  obtain ⟨hbdd, N, hNo, hLN, hfN, L, hLpos, hLip⟩ := hA
  obtain ⟨hσpos, hσle⟩ := hσ₃
  -- bounded iterates
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbdd
  have hx1 : x 1 ∈ levelSet f (x 1) := by show f (x 1) ≤ f (x 1); exact le_rfl
  have hxC : ∀ k ≥ 1, ‖x k‖ ≤ C := fun k hk => hC _ (hL k hk)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hxC 1 le_rfl)
  have hxB : ∀ i ≥ 1, ∀ j ≥ 1, ‖x i - x j‖ ≤ 2 * C := fun i hi j hj =>
    (norm_sub_le _ _).trans (by linarith [hxC i hi, hxC j hj])
  -- gradient upper bound
  have hgup : ∀ k ≥ 1, ‖g f x k‖ ≤ ‖g f x 1‖ + L * (2 * C) := by
    intro k hk
    have h1 : dist (g f x k) (g f x 1) ≤ L * dist (x k) (x 1) :=
      hLip.dist_le_mul (x k) (hLN (hL k hk)) (x 1) (hLN hx1)
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h3 := norm_sub_norm_le (g f x k) (g f x 1)
    have h2 : (L : ℝ) * ‖x k - x 1‖ ≤ L * (2 * C) :=
      mul_le_mul_of_nonneg_left (hxB k hk 1 le_rfl) L.coe_nonneg
    linarith
  set γbar := ‖g f x 1‖ + L * (2 * C) with hγbar
  -- descent facts
  have hgpos : ∀ k ≥ 1, 0 < ‖g f x k‖ := fun k hk => norm_pos_iff.mpr (hg k hk)
  have hgd : ∀ k ≥ 1, inner ℝ (g f x k) (d k) < 0 := fun k hk => by
    have h1 := hD k hk
    have h2 : 0 < σ₃ * ‖g f x k‖ ^ 2 := by have := hgpos k hk; positivity
    linarith
  have hdne : ∀ k ≥ 1, d k ≠ 0 := fun k hk h => by
    have := hgd k hk
    rw [h, inner_zero_right] at this
    exact lt_irrefl _ this
  have hdpos : ∀ k ≥ 1, 0 < ‖d k‖ := fun k hk => norm_pos_iff.mpr (hdne k hk)
  have hsq : ∀ k ≥ 1, σ₃ ^ 2 * ‖g f x k‖ ^ 4 ≤ inner ℝ (g f x k) (d k) ^ 2 := by
    intro k hk
    have h1 := hD k hk
    have h2 : 0 ≤ σ₃ * ‖g f x k‖ ^ 2 := by positivity
    have h3 : σ₃ * ‖g f x k‖ ^ 2 ≤ -inner ℝ (g f x k) (d k) := by linarith
    calc σ₃ ^ 2 * ‖g f x k‖ ^ 4 = (σ₃ * ‖g f x k‖ ^ 2) * (σ₃ * ‖g f x k‖ ^ 2) := by ring
      _ ≤ (-inner ℝ (g f x k) (d k)) * (-inner ℝ (g f x k) (d k)) :=
          mul_le_mul h3 h3 h2 (h2.trans h3)
      _ = inner ℝ (g f x k) (d k) ^ 2 := by ring
  -- contradiction setup
  by_contra H
  unfold LiminfGradZero at H
  push Not at H
  obtain ⟨ε, hε, K, hK⟩ := H
  obtain ⟨γ0, hγ0, hγ0b⟩ := NCGProof.finite_lower (fun k => ‖g f x k‖) (fun k hk => hgpos k hk) K
  have hγ : 0 < min ε γ0 := lt_min hε hγ0
  set γ := min ε γ0 with hγdef
  have hglow : ∀ k ≥ 1, γ ≤ ‖g f x k‖ := by
    intro k hk
    by_cases hkK : K ≤ k
    · exact (min_le_left _ _).trans (hK k hkK)
    · exact (min_le_right _ _).trans (hγ0b k hk (by omega))
  obtain ⟨b, hb1, lam, hlam, hPk⟩ := hP γ γbar hγ (fun k hk => ⟨hglow k hk, hgup k hk⟩)
  -- Lemma 4.1
  have hu1 : ∀ k ≥ 1, ‖u d k‖ = 1 := by
    intro k hk
    simp only [u, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hdpos k hk).ne'
  have hukey : ∀ k ≥ 2, ‖u d k - u d (k - 1)‖ ≤ 2 * (‖g f x k‖ / ‖d k‖) := by
    intro k hk
    have hk1 : k - 1 ≥ 1 := by omega
    have hne : ‖d (k - 1)‖ ≠ 0 := (hdpos (k - 1) hk1).ne'
    have hδ : 0 ≤ ‖d k‖⁻¹ * β k * ‖d (k - 1)‖ := by
      have := hβ k hk; positivity
    have h1 := NCGProof.unit_diff_le (u d k) (u d (k - 1)) (hu1 k (by omega)) (hu1 (k - 1) hk1) _ hδ
    have hc : (‖d k‖⁻¹ * β k * ‖d (k - 1)‖) * ‖d (k - 1)‖⁻¹ = ‖d k‖⁻¹ * β k := by
      rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
    have e : ‖d k‖⁻¹ • d k = ‖d k‖⁻¹ • (-g f x k + β k • d (k - 1)) := by
      rw [← hdk k hk]
    have h2 : u d k - (‖d k‖⁻¹ * β k * ‖d (k - 1)‖) • u d (k - 1) = -(‖d k‖⁻¹ • g f x k) := by
      show ‖d k‖⁻¹ • d k - (‖d k‖⁻¹ * β k * ‖d (k - 1)‖) • (‖d (k - 1)‖⁻¹ • d (k - 1)) = _
      rw [e, smul_smul, hc, smul_add, smul_neg, smul_smul]
      abel
    rw [h2, norm_neg, norm_smul, norm_inv, norm_norm] at h1
    rw [div_eq_inv_mul]
    exact h1
  have hZ2 : Summable (fun k : ℕ =>
      inner ℝ (g f x (k + 1 + 1)) (d (k + 1 + 1)) ^ 2 / ‖d (k + 1 + 1)‖ ^ 2) :=
    (_root_.summable_nat_add_iff 1).mpr hZ
  have hU : Summable (fun k : ℕ => ‖u d (k + 1 + 1) - u d (k + 1)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (hZ2.mul_left (4 / (σ₃ ^ 2 * γ ^ 2)))
    have h1 := hukey (k + 1 + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h1
    have hgk := hglow (k + 1 + 1) (by omega)
    have hsq' := hsq (k + 1 + 1) (by omega)
    have hdk' := hdpos (k + 1 + 1) (by omega)
    have h0 : 0 ≤ ‖u d (k + 1 + 1) - u d (k + 1)‖ := norm_nonneg _
    have h2 : ‖u d (k + 1 + 1) - u d (k + 1)‖ ^ 2 ≤
        4 * (‖g f x (k + 1 + 1)‖ ^ 2 / ‖d (k + 1 + 1)‖ ^ 2) := by
      have := pow_le_pow_left₀ h0 h1 2
      rw [mul_pow, div_pow] at this
      linarith
    have hG2 : γ ^ 2 ≤ ‖g f x (k + 1 + 1)‖ ^ 2 := pow_le_pow_left₀ hγ.le hgk 2
    have h4 : ‖g f x (k + 1 + 1)‖ ^ 2 * (σ₃ ^ 2 * γ ^ 2) ≤
        inner ℝ (g f x (k + 1 + 1)) (d (k + 1 + 1)) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hG2
        (by positivity : 0 ≤ σ₃ ^ 2 * ‖g f x (k + 1 + 1)‖ ^ 2)
      nlinarith
    have h3 : ‖g f x (k + 1 + 1)‖ ^ 2 / ‖d (k + 1 + 1)‖ ^ 2 ≤
        (inner ℝ (g f x (k + 1 + 1)) (d (k + 1 + 1)) ^ 2 / ‖d (k + 1 + 1)‖ ^ 2) /
          (σ₃ ^ 2 * γ ^ 2) := by
      rw [le_div_iff₀ (by positivity), div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right h4 (by positivity)
    calc ‖u d (k + 1 + 1) - u d (k + 1)‖ ^ 2
        ≤ 4 * (‖g f x (k + 1 + 1)‖ ^ 2 / ‖d (k + 1 + 1)‖ ^ 2) := h2
      _ ≤ 4 * ((inner ℝ (g f x (k + 1 + 1)) (d (k + 1 + 1)) ^ 2 / ‖d (k + 1 + 1)‖ ^ 2) /
          (σ₃ ^ 2 * γ ^ 2)) := by linarith
      _ = 4 / (σ₃ ^ 2 * γ ^ 2) *
          (inner ℝ (g f x (k + 1 + 1)) (d (k + 1 + 1)) ^ 2 / ‖d (k + 1 + 1)‖ ^ 2) := by ring
  -- choose Δ
  set Δ : ℕ := ⌈4 * (2 * C) / lam⌉₊ + 1 with hΔdef
  have hΔ1 : 1 ≤ Δ := by omega
  have hΔlam : 4 * (2 * C) ≤ lam * Δ := by
    have h1 := Nat.le_ceil (4 * (2 * C) / lam)
    have h2 : (⌈4 * (2 * C) / lam⌉₊ : ℝ) ≤ Δ := by
      rw [hΔdef]; push_cast; linarith
    rw [div_le_iff₀ hlam] at h1
    nlinarith
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast hΔ1
  -- tail of Lemma 4.1 sum
  have hT := _root_.tendsto_sum_nat_add (fun k : ℕ => ‖u d (k + 1 + 1) - u d (k + 1)‖ ^ 2)
  obtain ⟨q0, hq0⟩ := Filter.eventually_atTop.mp
    (hT.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (4 * Δ))))
  have hwin : ∀ q ≥ q0, ∑ r ∈ Finset.range Δ, ‖u d (q + 1 + r + 1) - u d (q + 1 + r)‖ ≤ 1 / 2 := by
    intro q hq
    have htail := hq0 q hq
    have hsumm := (_root_.summable_nat_add_iff q).mpr hU
    have hle : ∑ r ∈ Finset.range Δ, ‖u d (r + q + 1 + 1) - u d (r + q + 1)‖ ^ 2 ≤
        ∑' r, ‖u d (r + q + 1 + 1) - u d (r + q + 1)‖ ^ 2 :=
      hsumm.sum_le_tsum _ (fun r _ => by positivity)
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range Δ)
      (f := fun r => ‖u d (q + 1 + r + 1) - u d (q + 1 + r)‖)
    rw [Finset.card_range] at hcs
    have heq : ∑ r ∈ Finset.range Δ, ‖u d (q + 1 + r + 1) - u d (q + 1 + r)‖ ^ 2 =
        ∑ r ∈ Finset.range Δ, ‖u d (r + q + 1 + 1) - u d (r + q + 1)‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [show q + 1 + r = r + q + 1 by omega]
    have hS0 : 0 ≤ ∑ r ∈ Finset.range Δ, ‖u d (q + 1 + r + 1) - u d (q + 1 + r)‖ :=
      Finset.sum_nonneg (fun r _ => norm_nonneg _)
    have hsq2 : (∑ r ∈ Finset.range Δ, ‖u d (q + 1 + r + 1) - u d (q + 1 + r)‖) ^ 2 ≤ 1 / 4 := by
      have h5 : (Δ : ℝ) * (1 / (4 * Δ)) = 1 / 4 := by field_simp
      have h6 : (Δ : ℝ) * ∑' r, ‖u d (r + q + 1 + 1) - u d (r + q + 1)‖ ^ 2 ≤
          Δ * (1 / (4 * Δ)) := mul_le_mul_of_nonneg_left htail.le hΔpos.le
      calc _ ≤ (Δ : ℝ) * ∑ r ∈ Finset.range Δ, ‖u d (q + 1 + r + 1) - u d (q + 1 + r)‖ ^ 2 := hcs
        _ ≤ (Δ : ℝ) * ∑' r, ‖u d (r + q + 1 + 1) - u d (r + q + 1)‖ ^ 2 := by
            rw [heq]; exact mul_le_mul_of_nonneg_left hle hΔpos.le
        _ ≤ 1 / 4 := by linarith
    nlinarith
  -- Lemma 4.2: a window with many big steps
  have hbigwin : ∃ p ≥ q0 + 1, Δ <
      2 * ((Finset.range Δ).filter (fun t => lam < ‖x (p + t + 1) - x (p + t)‖)).card := by
    by_contra Hc
    push Not at Hc
    have hb0 : 0 < b := by linarith
    have hA1 : 1 ≤ 2 * b ^ 2 := by nlinarith
    have hrecD : ∀ j ≥ 2, ‖d j‖ ^ 2 ≤ 2 * γbar ^ 2 + 2 * β j ^ 2 * ‖d (j - 1)‖ ^ 2 := by
      intro j hj
      have h1 : ‖d j‖ ≤ γbar + |β j| * ‖d (j - 1)‖ := by
        rw [hdk j hj]
        calc ‖-g f x j + β j • d (j - 1)‖ ≤ ‖-g f x j‖ + ‖β j • d (j - 1)‖ := norm_add_le _ _
          _ = ‖g f x j‖ + |β j| * ‖d (j - 1)‖ := by rw [norm_neg, norm_smul, Real.norm_eq_abs]
          _ ≤ _ := by linarith [hgup j (by omega)]
      have h0 : 0 ≤ ‖d j‖ := norm_nonneg _
      have h2 := pow_le_pow_left₀ h0 h1 2
      have e : (|β j| * ‖d (j - 1)‖) ^ 2 = β j ^ 2 * ‖d (j - 1)‖ ^ 2 := by
        rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg (γbar - |β j| * ‖d (j - 1)‖)]
    have haA : ∀ j ≥ 2, 2 * β j ^ 2 ≤ 2 * b ^ 2 := by
      intro j hj
      have h1 := (hPk j hj).1
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at this
      linarith
    have hstep : ∀ p ≥ q0 + 1, ‖d (p + Δ)‖ ^ 2 ≤
        ‖d p‖ ^ 2 + 2 * γbar ^ 2 * Δ * (2 * b ^ 2) ^ Δ := by
      intro p hp
      have hU2 := NCGProof.unroll (fun j => ‖d j‖ ^ 2) (fun j => 2 * β j ^ 2) (2 * γbar ^ 2) (2 * b ^ 2) p
        (by positivity) hA1 (fun j => by positivity) (fun t => by positivity)
        (fun t => haA (p + t + 1) (by omega))
        (fun t => by
          have := hrecD (p + t + 1) (by omega)
          simpa only [Nat.add_sub_cancel] using this) Δ
      have hprod : ∏ t ∈ Finset.range Δ, 2 * β (p + t + 1) ^ 2 ≤ 1 :=
        NCGProof.prod_le_one (fun t => 2 * β (p + t + 1) ^ 2) (2 * b ^ 2) hA1 Δ
          (fun t => lam < ‖x (p + t + 1) - x (p + t)‖) (fun t => by positivity)
          (fun t => haA (p + t + 1) (by omega))
          (fun t ht => by
            push Not at ht
            have h1 := (hPk (p + t + 1) (by omega)).2
            simp only [Nat.add_sub_cancel] at h1
            have h2 := h1 ht
            have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 2
            rw [sq_abs] at h3
            have e : 2 * (1 / (2 * b)) ^ 2 = (2 * b ^ 2)⁻¹ := by field_simp
            show 2 * β (p + t + 1) ^ 2 ≤ (2 * b ^ 2)⁻¹
            rw [← e]; linarith)
          (Hc p hp)
      have hDp : 0 ≤ ‖d p‖ ^ 2 := by positivity
      have := mul_le_mul_of_nonneg_right hprod hDp
      linarith
    set M := 2 * γbar ^ 2 * Δ * (2 * b ^ 2) ^ Δ with hM
    have hM0 : 0 ≤ M := by positivity
    have hind : ∀ n : ℕ, ‖d (q0 + n * Δ + 1)‖ ^ 2 ≤ ‖d (q0 + 1)‖ ^ 2 + n * M := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : q0 + (n + 1) * Δ + 1 = (q0 + n * Δ + 1) + Δ := by ring
        rw [e]
        have := hstep (q0 + n * Δ + 1) (by omega)
        push_cast
        linarith
    -- summability of 1/‖d‖²
    have hinv : Summable (fun k : ℕ => 1 / ‖d (k + 1)‖ ^ 2) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
        (hZ.mul_left (1 / (σ₃ ^ 2 * γ ^ 4)))
      have hgk := hglow (k + 1) (by omega)
      have hsq' := hsq (k + 1) (by omega)
      have hdk' := hdpos (k + 1) (by omega)
      have hG4 : γ ^ 4 ≤ ‖g f x (k + 1)‖ ^ 4 := pow_le_pow_left₀ hγ.le hgk 4
      have h4 : σ₃ ^ 2 * γ ^ 4 ≤ inner ℝ (g f x (k + 1)) (d (k + 1)) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hG4 (by positivity : 0 ≤ σ₃ ^ 2)
        linarith
      have hσ0 : σ₃ ≠ 0 := hσpos.ne'
      have hγ0' : γ ≠ 0 := hγ.ne'
      have hD0 : ‖d (k + 1)‖ ≠ 0 := hdk'.ne'
      calc 1 / ‖d (k + 1)‖ ^ 2 = (σ₃ ^ 2 * γ ^ 4 / ‖d (k + 1)‖ ^ 2) / (σ₃ ^ 2 * γ ^ 4) := by
            field_simp
        _ ≤ (inner ℝ (g f x (k + 1)) (d (k + 1)) ^ 2 / ‖d (k + 1)‖ ^ 2) / (σ₃ ^ 2 * γ ^ 4) := by
            gcongr
        _ = 1 / (σ₃ ^ 2 * γ ^ 4) * (inner ℝ (g f x (k + 1)) (d (k + 1)) ^ 2 / ‖d (k + 1)‖ ^ 2) := by
            ring
    have hinj : Function.Injective (fun n : ℕ => q0 + n * Δ) := by
      intro m n h
      have h' : m * Δ = n * Δ := by simpa using h
      exact Nat.eq_of_mul_eq_mul_right (by omega) h'
    have hsub := hinv.comp_injective hinj
    have hlin : Summable (fun n : ℕ => 1 / (‖d (q0 + 1)‖ ^ 2 + n * M)) := by
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsub
      · have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        positivity
      · show 1 / (‖d (q0 + 1)‖ ^ 2 + n * M) ≤ 1 / ‖d (q0 + n * Δ + 1)‖ ^ 2
        have hpos : 0 < ‖d (q0 + n * Δ + 1)‖ ^ 2 := by
          have := hdpos (q0 + n * Δ + 1) (by omega); positivity
        exact one_div_le_one_div_of_le hpos (hind n)
    have hD0 : 0 < ‖d (q0 + 1)‖ ^ 2 := by have := hdpos (q0 + 1) (by omega); positivity
    exact NCGProof.not_summable_lin _ M hD0 hM0 hlin
  -- Theorem 4.3: the window argument
  obtain ⟨p, hp, hcard⟩ := hbigwin
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hq : q ≥ q0 := by omega
  have hw := hwin q hq
  have hs : ∀ j ≥ 1, x (j + 1) - x j = ‖x (j + 1) - x j‖ • u d j := by
    intro j hj
    obtain ⟨hα, hx⟩ := hαx j hj
    rw [hx, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hα]
    show α j • d j = (α j * ‖d j‖) • (‖d j‖⁻¹ • d j)
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ (hdpos j hj).ne', mul_one]
  set P := q + 1 with hPdef
  have hP1 : P ≥ 1 := by omega
  set S := ∑ t ∈ Finset.range Δ, ‖x (P + t + 1) - x (P + t)‖ with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun t _ => norm_nonneg _)
  -- each unit direction stays near u_P
  have hnear : ∀ t < Δ, ‖u d (P + t) - u d P‖ ≤ 1 / 2 := by
    intro t ht
    have htel : u d (P + t) - u d P = ∑ r ∈ Finset.range t, (u d (P + r + 1) - u d (P + r)) := by
      have := Finset.sum_range_sub (fun r => u d (P + r)) t
      simpa only [add_zero, ← add_assoc] using this.symm
    rw [htel]
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ hw
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro r hr; simp only [Finset.mem_range] at hr ⊢; omega)
      (fun r _ _ => norm_nonneg _)
  have htel2 : ∑ t ∈ Finset.range Δ, (x (P + t + 1) - x (P + t)) = x (P + Δ) - x P := by
    have := Finset.sum_range_sub (fun t => x (P + t)) Δ
    simpa only [add_zero, ← add_assoc] using this
  have hdecomp : S • u d P = (x (P + Δ) - x P) -
      ∑ t ∈ Finset.range Δ, ‖x (P + t + 1) - x (P + t)‖ • (u d (P + t) - u d P) := by
    rw [← htel2, hSdef, Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [hs (P + t) (by omega), smul_sub, norm_smul, norm_norm, hu1 (P + t) (by omega), mul_one]
    abel
  have hupper : S ≤ 2 * C + (1 / 2) * S := by
    have h1 : ‖S • u d P‖ = S := by
      rw [norm_smul, hu1 P hP1, mul_one, Real.norm_eq_abs, abs_of_nonneg hS0]
    have h2 := norm_sub_le (x (P + Δ) - x P)
      (∑ t ∈ Finset.range Δ, ‖x (P + t + 1) - x (P + t)‖ • (u d (P + t) - u d P))
    rw [← hdecomp, h1] at h2
    have h3 := hxB (P + Δ) (by omega) P hP1
    have h4 : ‖∑ t ∈ Finset.range Δ, ‖x (P + t + 1) - x (P + t)‖ • (u d (P + t) - u d P)‖ ≤
        (1 / 2) * S := by
      refine (norm_sum_le _ _).trans ?_
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_le_sum (fun t ht => ?_)
      rw [norm_smul, norm_norm, mul_comm]
      exact mul_le_mul_of_nonneg_right (hnear t (Finset.mem_range.mp ht)) (norm_nonneg _)
    linarith
  have hlower : (((Finset.range Δ).filter
      (fun t => lam < ‖x (P + t + 1) - x (P + t)‖)).card : ℝ) * lam ≤ S := by
    have h1 := Finset.card_nsmul_le_sum
      ((Finset.range Δ).filter (fun t => lam < ‖x (P + t + 1) - x (P + t)‖))
      (fun t => ‖x (P + t + 1) - x (P + t)‖) lam
      (fun t ht => (Finset.mem_filter.mp ht).2.le)
    rw [nsmul_eq_mul] at h1
    refine h1.trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun t _ _ => norm_nonneg _)
  have hcardR : (Δ : ℝ) + 1 ≤ 2 * (((Finset.range Δ).filter
      (fun t => lam < ‖x (P + t + 1) - x (P + t)‖)).card : ℝ) := by
    exact_mod_cast hcard
  nlinarith
