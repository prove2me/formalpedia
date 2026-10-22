-- Prove2me | solution 1 for NonlinCG.FRBound.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T02:24:56.088979+00:00
-- url     : https://prove2.me/submissions/0ebd3333-4925-412d-a3b1-c073498d481d

import Mathlib
import Definitions.Def_NonlinCG_FRBound_Setting

set_option autoImplicit false

namespace NCGFRProof

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

/-- `D ≤ c G + β² D0` and `β² G0² ≤ G²` give `D/G² ≤ c/G + D0/G0²`. -/
lemma ratio_step (D D0 G G0 β c : ℝ) (hG : 0 < G) (hG0 : 0 < G0) (hD0 : 0 ≤ D0)
    (hD : D ≤ c * G + β ^ 2 * D0) (hβ : β ^ 2 * G0 ^ 2 ≤ G ^ 2) :
    D / G ^ 2 ≤ c / G + D0 / G0 ^ 2 := by
  have hG2 : 0 < G ^ 2 := by positivity
  have hG02 : 0 < G0 ^ 2 := by positivity
  have h1 : D / G ^ 2 ≤ (c * G + β ^ 2 * D0) / G ^ 2 := div_le_div_of_nonneg_right hD hG2.le
  have h2 : (c * G + β ^ 2 * D0) / G ^ 2 = c / G + β ^ 2 * D0 / G ^ 2 := by
    field_simp
  have h3 : β ^ 2 * D0 / G ^ 2 ≤ D0 / G0 ^ 2 := by
    rw [div_le_div_iff₀ hG2 hG02]
    have := mul_le_mul_of_nonneg_left hβ hD0
    nlinarith
  linarith

end NCGFRProof

set_option maxHeartbeats 1600000 in
open NonlinCG.FRBound in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (hf : ContDiff ℝ 1 f) (β α : ℕ → ℝ) (x d : ℕ → E)
    (σ₁ σ₂ : ℝ) (hA : Assumptions21 f (x 1)) (hrun : IsCGRun f β α x d)
    (hβ : ∀ k ≥ 2, |β k| ≤ betaFR f x k)
    (hσ : 0 < σ₁ ∧ σ₁ < σ₂ ∧ σ₂ < 1 / 2)
    (hls : ∀ k ≥ 1, StrongWolfeStep f σ₁ σ₂ (x k) (d k) (α k)) :
    LiminfGradZero f x := by
  obtain ⟨hd1, hdk, hαx⟩ := hrun
  obtain ⟨hbdd, N, hNo, hLN, hfN, L, hLpos, hLip⟩ := hA
  obtain ⟨hσ1, hσ12, hσ2⟩ := hσ
  have hs1 : 0 < 1 - σ₂ := by linarith
  have hs2 : 0 < 1 - 2 * σ₂ := by linarith
  have hσ2p : 0 < σ₂ := by linarith
  -- the step facts in terms of g
  have hstep : ∀ k ≥ 1, f (x (k + 1)) ≤ f (x k) + σ₁ * α k * inner ℝ (g f x k) (d k) ∧
      |inner ℝ (g f x (k + 1)) (d k)| ≤ -σ₂ * inner ℝ (g f x k) (d k) := by
    intro k hk
    have h := hls k hk
    unfold StrongWolfeStep at h
    simp only [g]
    rw [(hαx k hk).2]
    exact h
  -- recursion for d
  have hdrec : ∀ k ≥ 1, d (k + 1) = -g f x (k + 1) + β (k + 1) • d k := by
    intro k hk
    have := hdk (k + 1) (by omega)
    simpa using this
  -- |β_k| ‖g_{k-1}‖² ≤ ‖g_k‖²
  have hβG : ∀ k ≥ 1, |β (k + 1)| * ‖g f x k‖ ^ 2 ≤ ‖g f x (k + 1)‖ ^ 2 := by
    intro k hk
    have h := hβ (k + 1) (by omega)
    unfold betaFR at h
    simp only [Nat.add_sub_cancel] at h
    by_cases h0 : ‖g f x k‖ ^ 2 = 0
    · rw [h0, mul_zero]; positivity
    · have hpos : 0 < ‖g f x k‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
      rwa [le_div_iff₀ hpos] at h
  -- inner product of g_{k+1} with d_{k+1}
  have hinner : ∀ k ≥ 1, inner ℝ (g f x (k + 1)) (d (k + 1)) =
      -‖g f x (k + 1)‖ ^ 2 + β (k + 1) * inner ℝ (g f x (k + 1)) (d k) := by
    intro k hk
    rw [hdrec k hk, inner_add_right, inner_neg_right, real_inner_self_eq_norm_sq,
      real_inner_smul_right]
  -- Lemma 3.1 (Al-Baali) invariant
  have hinv : ∀ k ≥ 1, -‖g f x k‖ ^ 2 ≤ (1 - σ₂) * inner ℝ (g f x k) (d k) ∧
      (1 - σ₂) * inner ℝ (g f x k) (d k) ≤ -(1 - 2 * σ₂) * ‖g f x k‖ ^ 2 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      rw [hd1, inner_neg_right, real_inner_self_eq_norm_sq]
      have := sq_nonneg ‖g f x 1‖
      constructor <;> nlinarith
    | succ k hk ih =>
      rw [hinner k hk]
      obtain ⟨ih1, ih2⟩ := ih
      have hs := (hstep k hk).2
      have hb := hβG k hk
      set a := inner ℝ (g f x k) (d k)
      set s := inner ℝ (g f x (k + 1)) (d k)
      set G := ‖g f x (k + 1)‖ ^ 2
      set G0 := ‖g f x k‖ ^ 2
      have hsa : (1 - σ₂) * |s| ≤ σ₂ * G0 := by
        have := mul_le_mul_of_nonneg_left hs hs1.le
        nlinarith
      have hP : (1 - σ₂) * (|β (k + 1)| * |s|) ≤ σ₂ * G := by
        have h1 := mul_le_mul_of_nonneg_left hsa (abs_nonneg (β (k + 1)))
        have h2 := mul_le_mul_of_nonneg_left hb hσ2p.le
        nlinarith
      have hab := abs_le.mp (le_of_eq (abs_mul (β (k + 1)) s))
      have hl : -((1 - σ₂) * (|β (k + 1)| * |s|)) ≤ (1 - σ₂) * (β (k + 1) * s) := by
        have := mul_le_mul_of_nonneg_left hab.1 hs1.le
        linarith
      have hr : (1 - σ₂) * (β (k + 1) * s) ≤ (1 - σ₂) * (|β (k + 1)| * |s|) :=
        mul_le_mul_of_nonneg_left hab.2 hs1.le
      constructor <;> nlinarith
  -- descent
  have hneg : ∀ k ≥ 1, inner ℝ (g f x k) (d k) ≤ 0 := by
    intro k hk
    have := (hinv k hk).2
    have : 0 ≤ (1 - 2 * σ₂) * ‖g f x k‖ ^ 2 := by positivity
    nlinarith
  have hdec : ∀ k ≥ 1, f (x (k + 1)) ≤ f (x k) := by
    intro k hk
    have h1 := (hstep k hk).1
    have h2 : 0 ≤ σ₁ * α k := mul_nonneg hσ1.le (hαx k hk).1.le
    have := mul_nonpos_of_nonneg_of_nonpos h2 (hneg k hk)
    linarith
  have hlev : ∀ k ≥ 1, x k ∈ levelSet f (x 1) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => show f (x 1) ≤ f (x 1); exact le_rfl
    | succ k hk ih =>
      show f (x (k + 1)) ≤ f (x 1)
      exact (hdec k hk).trans ih
  -- lower bound for f on the level set
  obtain ⟨m, hm⟩ := hbdd.isCompact_closure.bddBelow_image hf.continuous.continuousOn
  have hfm : ∀ k ≥ 1, m ≤ f (x k) := fun k hk =>
    hm ⟨x k, subset_closure (hlev k hk), rfl⟩
  -- Zoutendijk step
  have hzk : ∀ k ≥ 1, σ₁ * (1 - σ₂) * inner ℝ (g f x k) (d k) ^ 2 ≤
      L * ‖d k‖ ^ 2 * (f (x k) - f (x (k + 1))) := by
    intro k hk
    obtain ⟨hαk, hx⟩ := hαx k hk
    obtain ⟨h1, hs⟩ := hstep k hk
    have hlip : dist (gradient f (x (k + 1))) (gradient f (x k)) ≤ L * dist (x (k + 1)) (x k) :=
      hLip.dist_le_mul _ (hLN (hlev (k + 1) (by omega))) _ (hLN (hlev k hk))
    rw [dist_eq_norm, dist_eq_norm] at hlip
    have hdiff : x (k + 1) - x k = α k • d k := by rw [hx]; simp
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hαk] at hlip
    have hcs := real_inner_le_norm (gradient f (x (k + 1)) - gradient f (x k)) (d k)
    have hsub : inner ℝ (gradient f (x (k + 1)) - gradient f (x k)) (d k) =
        inner ℝ (g f x (k + 1)) (d k) - inner ℝ (g f x k) (d k) := by
      rw [inner_sub_left]; rfl
    rw [hsub] at hcs
    set a := inner ℝ (g f x k) (d k)
    set s := inner ℝ (g f x (k + 1)) (d k)
    set D := ‖d k‖
    have hD0 : 0 ≤ D := norm_nonneg _
    have hsl : σ₂ * a ≤ s := by
      have := neg_abs_le s
      linarith
    have hmul := mul_le_mul_of_nonneg_right hlip hD0
    have key : (1 - σ₂) * (-a) ≤ L * α k * D ^ 2 := by nlinarith
    have ha := hneg k hk
    have hfd : σ₁ * α k * (-a) ≤ f (x k) - f (x (k + 1)) := by linarith
    have hna : 0 ≤ -a := by linarith
    calc σ₁ * (1 - σ₂) * a ^ 2 = (σ₁ * (-a)) * ((1 - σ₂) * (-a)) := by ring
      _ ≤ (σ₁ * (-a)) * (L * α k * D ^ 2) :=
          mul_le_mul_of_nonneg_left key (mul_nonneg hσ1.le hna)
      _ = (L * D ^ 2) * (σ₁ * α k * (-a)) := by ring
      _ ≤ (L * D ^ 2) * (f (x k) - f (x (k + 1))) :=
          mul_le_mul_of_nonneg_left hfd (by positivity)
  -- contradiction
  by_contra H
  unfold LiminfGradZero at H
  push Not at H
  obtain ⟨ε, hε, K, hK⟩ := H
  -- gradients never vanish
  have hprop : ∀ j ≥ 1, g f x j = 0 → g f x (j + 1) = 0 := by
    intro j hj h0
    have hdj : d j = 0 := by
      rcases Nat.eq_or_lt_of_le hj with h | h
      · subst h; rw [hd1, h0, neg_zero]
      · have hb := hβ j (by omega)
        unfold betaFR at hb
        rw [h0, norm_zero] at hb
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div] at hb
        have hb0 : β j = 0 := abs_nonpos_iff.mp hb
        rw [hdk j (by omega), h0, hb0, neg_zero, zero_smul, add_zero]
    show gradient f (x (j + 1)) = 0
    rw [(hαx j hj).2, hdj, smul_zero, add_zero]
    exact h0
  have hgne : ∀ k ≥ 1, g f x k ≠ 0 := by
    intro j hj h0
    have hall : ∀ t : ℕ, g f x (j + t) = 0 := by
      intro t
      induction t with
      | zero => simpa using h0
      | succ t ih => exact hprop (j + t) (by omega) ih
    have := hK (j + K) (by omega)
    rw [hall K, norm_zero] at this
    linarith
  have hgpos : ∀ k ≥ 1, 0 < ‖g f x k‖ := fun k hk => norm_pos_iff.mpr (hgne k hk)
  obtain ⟨γ0, hγ0, hγ0b⟩ := NCGFRProof.finite_lower (fun k => ‖g f x k‖) hgpos K
  have hγ : 0 < min ε γ0 := lt_min hε hγ0
  set γ := min ε γ0 with hγdef
  have hglow : ∀ k ≥ 1, γ ≤ ‖g f x k‖ := by
    intro k hk
    by_cases hkK : K ≤ k
    · exact (min_le_left _ _).trans (hK k hkK)
    · exact (min_le_right _ _).trans (hγ0b k hk (by omega))
  have hG2 : ∀ k ≥ 1, γ ^ 2 ≤ ‖g f x k‖ ^ 2 := fun k hk =>
    pow_le_pow_left₀ hγ.le (hglow k hk) 2
  -- strict descent and d ≠ 0
  have hgdlt : ∀ k ≥ 1, (1 - 2 * σ₂) * ‖g f x k‖ ^ 2 ≤ (1 - σ₂) * (-inner ℝ (g f x k) (d k)) := by
    intro k hk
    have := (hinv k hk).2
    linarith
  have hdpos : ∀ k ≥ 1, 0 < ‖d k‖ := by
    intro k hk
    apply norm_pos_iff.mpr
    intro h
    have h1 := hgdlt k hk
    rw [h, inner_zero_right, neg_zero, mul_zero] at h1
    have : 0 < (1 - 2 * σ₂) * ‖g f x k‖ ^ 2 := by have := hgpos k hk; positivity
    linarith
  -- norm recursion
  set c3 := (1 + σ₂) / (1 - σ₂) with hc3
  have hdnorm : ∀ k ≥ 1, ‖d (k + 1)‖ ^ 2 ≤ c3 * ‖g f x (k + 1)‖ ^ 2 + β (k + 1) ^ 2 * ‖d k‖ ^ 2 := by
    intro k hk
    have hexp : ‖d (k + 1)‖ ^ 2 = ‖g f x (k + 1)‖ ^ 2 -
        2 * (β (k + 1) * inner ℝ (g f x (k + 1)) (d k)) + β (k + 1) ^ 2 * ‖d k‖ ^ 2 := by
      rw [hdrec k hk, norm_add_sq_real, norm_neg, inner_neg_left, real_inner_smul_right,
        norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [hexp]
    have hs := (hstep k hk).2
    have hb := hβG k hk
    have ih1 := (hinv k hk).1
    set a := inner ℝ (g f x k) (d k)
    set s := inner ℝ (g f x (k + 1)) (d k)
    set G := ‖g f x (k + 1)‖ ^ 2
    set G0 := ‖g f x k‖ ^ 2
    have hsa : (1 - σ₂) * |s| ≤ σ₂ * G0 := by
      have := mul_le_mul_of_nonneg_left hs hs1.le
      nlinarith
    have hP : (1 - σ₂) * (|β (k + 1)| * |s|) ≤ σ₂ * G := by
      have h1 := mul_le_mul_of_nonneg_left hsa (abs_nonneg (β (k + 1)))
      have h2 := mul_le_mul_of_nonneg_left hb hσ2p.le
      nlinarith
    have hab := abs_le.mp (le_of_eq (abs_mul (β (k + 1)) s))
    have hl : -((1 - σ₂) * (|β (k + 1)| * |s|)) ≤ (1 - σ₂) * (β (k + 1) * s) := by
      have := mul_le_mul_of_nonneg_left hab.1 hs1.le
      linarith
    have hc3e : c3 * G = G + 2 * σ₂ * G / (1 - σ₂) := by
      rw [hc3]; field_simp; ring
    have hq : -(β (k + 1) * s) ≤ σ₂ * G / (1 - σ₂) := by
      rw [le_div_iff₀ hs1]
      linarith
    rw [hc3e]
    have : 2 * σ₂ * G / (1 - σ₂) = 2 * (σ₂ * G / (1 - σ₂)) := by ring
    linarith
  -- u_k := ‖d_k‖² / (‖g_k‖²)²
  set M := c3 / γ ^ 2 with hM
  have hc3p : 0 ≤ c3 := by rw [hc3]; apply div_nonneg <;> linarith
  have hMp : 0 ≤ M := by positivity
  have hu : ∀ k ≥ 1, ‖d (k + 1)‖ ^ 2 / (‖g f x (k + 1)‖ ^ 2) ^ 2 ≤
      M + ‖d k‖ ^ 2 / (‖g f x k‖ ^ 2) ^ 2 := by
    intro k hk
    have hGp : 0 < ‖g f x (k + 1)‖ ^ 2 := by have := hgpos (k + 1) (by omega); positivity
    have hG0p : 0 < ‖g f x k‖ ^ 2 := by have := hgpos k hk; positivity
    have hb := hβG k hk
    have hb2 : β (k + 1) ^ 2 * (‖g f x k‖ ^ 2) ^ 2 ≤ (‖g f x (k + 1)‖ ^ 2) ^ 2 := by
      have h0 : 0 ≤ |β (k + 1)| * ‖g f x k‖ ^ 2 := by positivity
      have := mul_le_mul hb hb h0 (h0.trans hb)
      have e : β (k + 1) ^ 2 * (‖g f x k‖ ^ 2) ^ 2 =
          (|β (k + 1)| * ‖g f x k‖ ^ 2) * (|β (k + 1)| * ‖g f x k‖ ^ 2) := by
        rw [← sq_abs (β (k + 1))]; ring
      rw [e]; nlinarith
    have h1 := NCGFRProof.ratio_step _ _ _ _ _ _ hGp hG0p (by positivity) (hdnorm k hk) hb2
    have h2 : c3 / ‖g f x (k + 1)‖ ^ 2 ≤ M := by
      rw [hM]
      exact div_le_div_of_nonneg_left hc3p (by positivity) (hG2 (k + 1) (by omega))
    linarith
  set u1 := ‖d 1‖ ^ 2 / (‖g f x 1‖ ^ 2) ^ 2 with hu1
  have hu1p : 0 < u1 := by
    have := hdpos 1 le_rfl
    have := hgpos 1 le_rfl
    positivity
  have hun : ∀ n : ℕ, ‖d (n + 1)‖ ^ 2 / (‖g f x (n + 1)‖ ^ 2) ^ 2 ≤ u1 + n * M := by
    intro n
    induction n with
    | zero => simp [hu1]
    | succ n ih =>
      have := hu (n + 1) (by omega)
      push_cast
      linarith
  -- the summable telescoping sequence
  set h : ℕ → ℝ := fun n => f (x (n + 1)) - f (x (n + 1 + 1)) with hh
  have hh0 : ∀ n, 0 ≤ h n := fun n => by
    simp only [hh]; linarith [hdec (n + 1) (by omega)]
  have hsum : Summable h := by
    apply summable_of_sum_range_le hh0 (c := f (x 1) - m)
    intro n
    have := Finset.sum_range_sub' (fun i => f (x (i + 1))) n
    simp only [hh]
    rw [this]
    simp only [zero_add]
    linarith [hfm (n + 1) (by omega)]
  set κ := σ₁ * (1 - σ₂) * (1 - 2 * σ₂) ^ 2 with hκ
  have hκp : 0 < κ := by positivity
  set Λ := (1 - σ₂) ^ 2 * (L : ℝ) with hΛ
  have hbound : ∀ n : ℕ, 1 / (u1 + n * M) ≤ (Λ / κ) * h n := by
    intro n
    have hk : n + 1 ≥ 1 := by omega
    have hD := hdpos (n + 1) hk
    have hGp : 0 < ‖g f x (n + 1)‖ ^ 2 := by have := hgpos (n + 1) hk; positivity
    have hupos : 0 < ‖d (n + 1)‖ ^ 2 / (‖g f x (n + 1)‖ ^ 2) ^ 2 := by positivity
    have h1 : 1 / (u1 + n * M) ≤ 1 / (‖d (n + 1)‖ ^ 2 / (‖g f x (n + 1)‖ ^ 2) ^ 2) :=
      one_div_le_one_div_of_le hupos (hun n)
    have hz := hzk (n + 1) hk
    have hg := hgdlt (n + 1) hk
    set a := inner ℝ (g f x (n + 1)) (d (n + 1))
    set G := ‖g f x (n + 1)‖ ^ 2
    set D := ‖d (n + 1)‖ ^ 2
    have hDp : 0 < D := by positivity
    have hga : (1 - 2 * σ₂) ^ 2 * G ^ 2 ≤ (1 - σ₂) ^ 2 * a ^ 2 := by
      have h0 : 0 ≤ (1 - 2 * σ₂) * G := by positivity
      have := mul_le_mul hg hg h0 (h0.trans hg)
      nlinarith
    have hmain : κ * G ^ 2 ≤ Λ * D * h n := by
      have e : h n = f (x (n + 1)) - f (x (n + 1 + 1)) := rfl
      rw [e]
      have h2 := mul_le_mul_of_nonneg_left hga (mul_nonneg hσ1.le hs1.le)
      have h3 := mul_le_mul_of_nonneg_left hz (sq_nonneg (1 - σ₂))
      rw [hκ, hΛ]
      nlinarith
    have e1 : 1 / (D / G ^ 2) = G ^ 2 / D := by
      rw [one_div_div]
    rw [e1] at h1
    have h4 : G ^ 2 / D ≤ (Λ / κ) * h n := by
      rw [div_le_iff₀ hDp, div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hκp]
      nlinarith
    linarith
  have hs2' : Summable (fun n : ℕ => 1 / (u1 + n * M)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hbound (hsum.mul_left (Λ / κ))
  exact NCGFRProof.not_summable_lin u1 M hu1p hMp hs2'
