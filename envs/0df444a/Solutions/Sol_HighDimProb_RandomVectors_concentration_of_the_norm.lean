-- Prove2me | solution 1 for HighDimProb.RandomVectors.concentration_of_the_norm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T20:03:47.676199+00:00
-- url     : https://prove2.me/submissions/8050e4ce-6d8e-41f1-a560-8bf0bc89bde0

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real

lemma cn_exp_le (x : ℝ) : exp x ≤ 1 + x + x ^ 2 + x ^ 2 * exp x := by
  have hex := exp_pos x
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hx)).2
    have h2 : 0 ≤ x ^ 2 * exp x := by positivity
    linarith
  · rcases le_or_gt 0 x with h0 | h0
    · have hx1 : 1 < x := by rwa [abs_of_nonneg h0] at hx
      have h4 : 1 ≤ x ^ 2 := by nlinarith
      nlinarith
    · have hx1 : x < -1 := by
        rw [abs_of_neg h0] at hx; linarith
      have h4 : exp x ≤ 1 := Real.exp_le_one_iff.2 h0.le
      nlinarith

lemma cn_exp_half_le_two : exp (1 / 2 : ℝ) ≤ 2 := by
  have h1 : exp (1 / 2 : ℝ) * exp (1 / 2) = exp 1 := by rw [← exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := exp_pos (1 / 2 : ℝ)
  nlinarith

/-- pointwise domination: `exp (s (y²-1)) ≤ 2 exp (y²/σ²)`. -/
lemma cn_ptB (y s σ : ℝ) (hσ : 1 ≤ σ) (hs : |s| ≤ 1 / (2 * σ ^ 2)) :
    exp (s * (y ^ 2 - 1)) ≤ 2 * exp (y ^ 2 / σ ^ 2) := by
  have hσ2 : 1 ≤ σ ^ 2 := by nlinarith
  have hσpos : 0 < σ ^ 2 := by positivity
  have hs2 : |s| ≤ 1 / 2 := by
    refine hs.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hx : s * (y ^ 2 - 1) ≤ y ^ 2 / σ ^ 2 / 2 + 1 / 2 := by
    have h1 : s * (y ^ 2 - 1) ≤ |s| * y ^ 2 + |s| := by
      have := neg_abs_le s
      have := le_abs_self s
      nlinarith
    have h2 : |s| * y ^ 2 ≤ y ^ 2 / σ ^ 2 / 2 := by
      have : |s| * y ^ 2 ≤ 1 / (2 * σ ^ 2) * y ^ 2 := mul_le_mul_of_nonneg_right hs hy2
      calc |s| * y ^ 2 ≤ 1 / (2 * σ ^ 2) * y ^ 2 := this
        _ = y ^ 2 / σ ^ 2 / 2 := by field_simp
    linarith
  have hu : 0 ≤ y ^ 2 / σ ^ 2 := by positivity
  calc exp (s * (y ^ 2 - 1)) ≤ exp (y ^ 2 / σ ^ 2 / 2 + 1 / 2) := exp_le_exp.2 hx
    _ = exp (y ^ 2 / σ ^ 2 / 2) * exp (1 / 2) := exp_add _ _
    _ ≤ exp (y ^ 2 / σ ^ 2) * 2 := by
        apply mul_le_mul (exp_le_exp.2 (by linarith)) cn_exp_half_le_two (exp_pos _).le
          (exp_pos _).le
    _ = 2 * exp (y ^ 2 / σ ^ 2) := by ring

lemma cn_ptW (y s σ : ℝ) (hσ : 1 ≤ σ) (hs : |s| ≤ 1 / (2 * σ ^ 2)) :
    exp (s * (y ^ 2 - 1)) ≤ (1 - s) + s * y ^ 2 + 27 * s ^ 2 * σ ^ 4 * exp (y ^ 2 / σ ^ 2) := by
  have hσ2 : 1 ≤ σ ^ 2 := by nlinarith
  have hσ4 : 1 ≤ σ ^ 4 := by nlinarith
  have hσpos : 0 < σ ^ 2 := by positivity
  set u := y ^ 2 / σ ^ 2 with hu_def
  have hu : 0 ≤ u := by positivity
  have hyu : y ^ 2 = u * σ ^ 2 := by rw [hu_def]; field_simp
  set h := exp (u / 2) with hh
  have hE : exp u = h * h := by rw [hh, ← exp_add]; ring_nf
  have hh1 : 1 ≤ h := one_le_exp (by linarith)
  have hF1 : u ^ 2 ≤ 8 * h := by
    have := Real.quadratic_le_exp_of_nonneg (x := u / 2) (by linarith)
    nlinarith
  have hy4 : (y ^ 2) ^ 2 ≤ 8 * σ ^ 4 * h := by
    rw [hyu]
    have : (u * σ ^ 2) ^ 2 = u ^ 2 * σ ^ 4 := by ring
    rw [this]; nlinarith
  set x := s * (y ^ 2 - 1) with hx
  have hx2 : x ^ 2 ≤ s ^ 2 * (8 * σ ^ 4 * h + 1) := by
    have h1 : x ^ 2 = s ^ 2 * (y ^ 2 - 1) ^ 2 := by rw [hx]; ring
    have h2 : (y ^ 2 - 1) ^ 2 ≤ 8 * σ ^ 4 * h + 1 := by nlinarith [sq_nonneg y]
    rw [h1]; exact mul_le_mul_of_nonneg_left h2 (sq_nonneg s)
  have hB : exp x ≤ 2 * h := by
    have hs2 : |s| ≤ 1 / 2 := by
      refine hs.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    have h1 : x ≤ |s| * y ^ 2 + |s| := by
      have := neg_abs_le s
      have := le_abs_self s
      rw [hx]; nlinarith
    have h2 : |s| * y ^ 2 ≤ u / 2 := by
      have : |s| * y ^ 2 ≤ 1 / (2 * σ ^ 2) * y ^ 2 := mul_le_mul_of_nonneg_right hs hy2
      calc |s| * y ^ 2 ≤ 1 / (2 * σ ^ 2) * y ^ 2 := this
        _ = u / 2 := by rw [hu_def]; field_simp
    calc exp x ≤ exp (u / 2 + 1 / 2) := exp_le_exp.2 (by linarith)
      _ = h * exp (1 / 2) := by rw [exp_add]
      _ ≤ h * 2 := mul_le_mul_of_nonneg_left cn_exp_half_le_two (by linarith)
      _ = 2 * h := by ring
  have hx2e : x ^ 2 * exp x ≤ s ^ 2 * (8 * σ ^ 4 * h + 1) * (2 * h) :=
    mul_le_mul hx2 hB (exp_pos _).le (by positivity)
  have hmain := cn_exp_le x
  have hs0 : 0 ≤ s ^ 2 := sq_nonneg s
  have key : x ^ 2 + x ^ 2 * exp x ≤ 27 * s ^ 2 * σ ^ 4 * (h * h) := by
    have e1 : s ^ 2 * (8 * σ ^ 4 * h + 1) + s ^ 2 * (8 * σ ^ 4 * h + 1) * (2 * h)
        ≤ 27 * s ^ 2 * σ ^ 4 * (h * h) := by
      have hhh : h ≤ h * h := by nlinarith
      have hq : 8 * σ ^ 4 * h + 1 + (8 * σ ^ 4 * h + 1) * (2 * h) ≤ 27 * σ ^ 4 * (h * h) := by
        nlinarith [mul_le_mul_of_nonneg_left hhh (by positivity : (0:ℝ) ≤ σ ^ 4)]
      nlinarith [mul_le_mul_of_nonneg_left hq hs0]
    linarith
  rw [hE]
  have : 1 + x = (1 - s) + s * y ^ 2 := by rw [hx]; ring
  linarith

lemma cn_mgfW {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (h2 : ∫ ω, Y ω ^ 2 ∂P = 1) (σ : ℝ) (hσ : 1 ≤ σ)
    (hint : Integrable (fun ω => exp (Y ω ^ 2 / σ ^ 2)) P)
    (hle : ∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P ≤ 2) (s : ℝ) (hs : |s| ≤ 1 / (2 * σ ^ 2)) :
    Integrable (fun ω => exp (s * (Y ω ^ 2 - 1))) P ∧
      ∫ ω, exp (s * (Y ω ^ 2 - 1)) ∂P ≤ exp (54 * s ^ 2 * σ ^ 4) := by
  have hσpos : 0 < σ ^ 2 := by positivity
  have hmeasE : Measurable (fun ω => exp (s * (Y ω ^ 2 - 1))) := by fun_prop
  have hI : Integrable (fun ω => exp (s * (Y ω ^ 2 - 1))) P := by
    refine Integrable.mono' (hint.const_mul 2) hmeasE.aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact cn_ptB (Y ω) s σ hσ hs
  have hY2 : Integrable (fun ω => Y ω ^ 2) P := by
    refine Integrable.mono' (hint.const_mul (σ ^ 2)) (hY.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := Real.add_one_le_exp (Y ω ^ 2 / σ ^ 2)
    have h3 : Y ω ^ 2 = σ ^ 2 * (Y ω ^ 2 / σ ^ 2) := by field_simp
    have h4 : 0 ≤ Y ω ^ 2 / σ ^ 2 := by positivity
    nlinarith
  refine ⟨hI, ?_⟩
  have hI1 : Integrable (fun ω => (1 - s) + s * Y ω ^ 2) P :=
    (integrable_const _).add (hY2.const_mul s)
  have hI2 : Integrable (fun ω => 27 * s ^ 2 * σ ^ 4 * exp (Y ω ^ 2 / σ ^ 2)) P :=
    hint.const_mul _
  calc ∫ ω, exp (s * (Y ω ^ 2 - 1)) ∂P
      ≤ ∫ ω, ((1 - s) + s * Y ω ^ 2 + 27 * s ^ 2 * σ ^ 4 * exp (Y ω ^ 2 / σ ^ 2)) ∂P :=
        integral_mono hI (hI1.add hI2) (fun ω => cn_ptW (Y ω) s σ hσ hs)
    _ = (1 - s) + s * ∫ ω, Y ω ^ 2 ∂P +
          27 * s ^ 2 * σ ^ 4 * ∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P := by
        rw [integral_add hI1 hI2, integral_add (integrable_const _) (hY2.const_mul s),
          integral_const_mul, integral_const_mul, integral_const]
        simp
    _ ≤ 1 + 54 * s ^ 2 * σ ^ 4 := by
        rw [h2]
        have : 0 ≤ 27 * s ^ 2 * σ ^ 4 := by positivity
        nlinarith
    _ ≤ exp (54 * s ^ 2 * σ ^ 4) := by linarith [add_one_le_exp (54 * s ^ 2 * σ ^ 4)]

lemma cn_one_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (h2 : ∫ ω, Y ω ^ 2 ∂P = 1) (s : ℝ) (hs : 0 < s)
    (hint : Integrable (fun ω => exp (Y ω ^ 2 / s ^ 2)) P)
    (hle : ∫ ω, exp (Y ω ^ 2 / s ^ 2) ∂P ≤ 2) : 1 ≤ s := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hpt : ∀ ω, Y ω ^ 2 / s ^ 2 ≤ exp (Y ω ^ 2 / s ^ 2) - 1 := fun ω => by
    linarith [Real.add_one_le_exp (Y ω ^ 2 / s ^ 2)]
  have hI : Integrable (fun ω => Y ω ^ 2 / s ^ 2) P := by
    refine Integrable.mono' (hint.sub (integrable_const 1))
      ((hY.pow_const 2).div_const _).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt ω
  have h3 : ∫ ω, Y ω ^ 2 / s ^ 2 ∂P ≤ ∫ ω, (exp (Y ω ^ 2 / s ^ 2) - 1) ∂P :=
    integral_mono hI (hint.sub (integrable_const 1)) hpt
  rw [integral_div, h2, integral_sub hint (integrable_const 1), integral_const] at h3
  simp at h3
  have h4 : 1 / s ^ 2 ≤ 1 := by rw [one_div]; linarith
  rw [div_le_one hs2] at h4
  nlinarith

lemma cn_choose (a b N v M κ : ℝ) (ha : 0 < a) (hb : 0 < b) (hN : 0 < N) (hv : 0 < v)
    (hMv : v ≤ M) (hMN : N * v ≤ M ^ 2) (hκa : 4 * a * κ ≤ 1) (hκb : 2 * κ ≤ b) :
    ∃ s, 0 ≤ s ∧ s ≤ b ∧ -s * M + a * N * s ^ 2 ≤ -κ * v := by
  have hM : 0 < M := lt_of_lt_of_le hv hMv
  have haN : 0 < 2 * a * N := by positivity
  rcases le_or_gt M (2 * a * N * b) with h | h
  · refine ⟨M / (2 * a * N), by positivity, ?_, ?_⟩
    · rw [div_le_iff₀ haN]; linarith
    · set s := M / (2 * a * N) with hs
      have hs2 : s * (2 * a * N) = M := by rw [hs]; field_simp
      have e1 : -s * M + a * N * s ^ 2 = -(s * M) / 2 := by
        have : a * N * s ^ 2 = s * (s * (2 * a * N)) / 2 := by ring
        rw [this, hs2]; ring
      rw [e1]
      -- s * M * (2 a N) = M^2 ≥ N v ≥ N v (4 a κ)
      have e2 : s * M * (2 * a * N) = M ^ 2 := by rw [← hs2]; ring
      have hκ0 : κ ≤ 1 / (4 * a) := by rw [le_div_iff₀ (by positivity)]; linarith
      have e3 : 2 * κ * v * (2 * a * N) ≤ s * M * (2 * a * N) := by
        rw [e2]
        have : 2 * κ * v * (2 * a * N) = (4 * a * κ) * (N * v) := by ring
        rw [this]
        have hNv : 0 ≤ N * v := by positivity
        rcases le_or_gt 0 κ with hk | hk
        · nlinarith
        · nlinarith
      have e4 : 2 * κ * v ≤ s * M := le_of_mul_le_mul_right e3 haN
      linarith
  · refine ⟨b, hb.le, le_rfl, ?_⟩
    have e1 : a * N * b ^ 2 ≤ b * M / 2 := by
      have : a * N * b ^ 2 = b * (2 * a * N * b) / 2 := by ring
      rw [this]; nlinarith
    have e2 : κ * v ≤ b * v / 2 := by nlinarith
    have e3 : b * v ≤ b * M := mul_le_mul_of_nonneg_left hMv hb.le
    nlinarith

lemma cn_geom (Q N v : ℝ) (hQ : 0 ≤ Q) (hN : 1 ≤ N) (hv : v < (sqrt Q - sqrt N) ^ 2) :
    max v (sqrt (N * v)) ≤ |Q - N| := by
  set R := sqrt Q with hR
  set r := sqrt N with hr
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.2 hN
  have hRQ : R ^ 2 = Q := sq_sqrt hQ
  have hrN : r ^ 2 = N := sq_sqrt (by linarith)
  have hfac : Q - N = (R - r) * (R + r) := by rw [← hRQ, ← hrN]; ring
  have habs : |Q - N| = |R - r| * (R + r) := by
    rw [hfac, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ R + r)]
  have hZ : |R - r| ≤ R + r := abs_le.2 ⟨by linarith, by linarith⟩
  have hZ2 : (R - r) ^ 2 = |R - r| ^ 2 := (sq_abs _).symm
  apply max_le
  · rw [habs]
    have h0 : 0 ≤ |R - r| := abs_nonneg _
    nlinarith
  · have hsq : (Q - N) ^ 2 = (R - r) ^ 2 * (R + r) ^ 2 := by rw [hfac]; ring
    have h1 : N * v ≤ (Q - N) ^ 2 := by
      rw [hsq, ← hrN]
      have h3 : r ^ 2 ≤ (R + r) ^ 2 := by nlinarith
      have h4 : 0 ≤ (R - r) ^ 2 := sq_nonneg _
      have h5 : 0 ≤ r ^ 2 := sq_nonneg _
      nlinarith
    calc sqrt (N * v) ≤ sqrt ((Q - N) ^ 2) := Real.sqrt_le_sqrt h1
      _ = |Q - N| := Real.sqrt_sq_eq_abs _

lemma cn_layer {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω) (κ l : ℝ) (hl : 0 < l)
    (hκ : 3 * l ≤ κ) (htail : ∀ v : ℝ, 0 < v → P.real {ω | v < f ω} ≤ 2 * exp (-κ * v)) :
    Integrable (fun ω => exp (l * f ω)) P ∧ ∫ ω, exp (l * f ω) ∂P ≤ 2 := by
  have hG : ∀ x : ℝ, ∫ u in (0:ℝ)..x, l * exp (l * u) = exp (l * x) - 1 := by
    intro x
    have hd : ∀ u ∈ Set.uIcc 0 x, HasDerivAt (fun u => exp (l * u)) (l * exp (l * u)) u := by
      intro u _
      have h := ((hasDerivAt_id u).const_mul l).exp
      simp only [id, mul_one] at h
      convert h using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun u => l * exp (l * u)).intervalIntegrable _ _)]
    simp
  have hlc := lintegral_comp_eq_lintegral_meas_lt_mul P (f := f) (g := fun u => l * exp (l * u))
    (ae_of_all _ hf0) hf.aemeasurable
    (fun t _ => (by fun_prop : Continuous fun u => l * exp (l * u)).intervalIntegrable _ _)
    (ae_of_all _ fun u => by positivity)
  simp_rw [hG] at hlc
  have hκl : l - κ < 0 := by linarith
  have hIexp : IntegrableOn (fun u => 2 * l * exp ((l - κ) * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi hκl 0).const_mul _
  have hbound : ∫⁻ t in Set.Ioi 0, P {a | t < f a} * ENNReal.ofReal (l * exp (l * t)) ≤
      ENNReal.ofReal (∫ u in Set.Ioi 0, 2 * l * exp ((l - κ) * u)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hIexp (ae_of_all _ fun u => by positivity)]
    refine setLIntegral_mono (by fun_prop) (fun t ht => ?_)
    have ht0 : 0 < t := ht
    have h1 : P {a | t < f a} ≤ ENNReal.ofReal (2 * exp (-κ * t)) := by
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal (htail t ht0)
    calc P {a | t < f a} * ENNReal.ofReal (l * exp (l * t))
        ≤ ENNReal.ofReal (2 * exp (-κ * t)) * ENNReal.ofReal (l * exp (l * t)) :=
          by gcongr
      _ = ENNReal.ofReal (2 * l * exp ((l - κ) * t)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : exp ((l - κ) * t) = exp (-κ * t) * exp (l * t) := by
            rw [← exp_add]; ring_nf
          rw [this]; ring
  have hval : ∫ u in Set.Ioi 0, 2 * l * exp ((l - κ) * u) ≤ 1 := by
    rw [integral_const_mul, integral_exp_mul_Ioi hκl 0]
    simp only [mul_zero, exp_zero]
    rw [show l - κ = -(κ - l) by ring, div_neg, neg_div, neg_neg, mul_one_div,
      div_le_one (by linarith)]
    linarith
  have hL : ∫⁻ ω, ENNReal.ofReal (exp (l * f ω) - 1) ∂P ≤ ENNReal.ofReal 1 :=
    hlc ▸ hbound.trans (ENNReal.ofReal_le_ofReal hval)
  have hnn : ∀ ω, 0 ≤ exp (l * f ω) - 1 := fun ω => by
    have := one_le_exp (mul_nonneg hl.le (hf0 ω)); linarith
  have hmeas : Measurable (fun ω => exp (l * f ω) - 1) := by fun_prop
  have hIG : Integrable (fun ω => exp (l * f ω) - 1) P := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)]
    exact lt_of_le_of_lt hL ENNReal.ofReal_lt_top
  have hintG : ∫ ω, (exp (l * f ω) - 1) ∂P ≤ 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one hL
  have hI : Integrable (fun ω => exp (l * f ω)) P := by
    exact (hIG.add (integrable_const (1:ℝ))).congr
      (ae_of_all _ fun ω => by simp only [Pi.add_apply]; ring)
  refine ⟨hI, ?_⟩
  rw [integral_sub hI (integrable_const 1), integral_const] at hintG
  simp at hintG
  linarith

open MeasureTheory ProbabilityTheory Real HighDimProb.Concentration in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {n : ℕ} (X : Fin n → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X P →
        (∀ i, ∫ ω, (X i ω) ^ 2 ∂P = 1) →
        (∀ i, ∃ t > 0, Integrable (fun ω => Real.exp ((X i ω) ^ 2 / t ^ 2)) P ∧
                       ∫ ω, Real.exp ((X i ω) ^ 2 / t ^ 2) ∂P ≤ 2) →
        HighDimProb.Concentration.subgaussianNorm P
            (fun ω => Real.sqrt (∑ i, (X i ω) ^ 2) - Real.sqrt n) ≤
          C * (⨆ i, HighDimProb.Concentration.subgaussianNorm P (X i)) ^ 2 := by
  refine ⟨104, by norm_num, ?_⟩
  intro Ω _ P _ n X hXm hind h2 hsg
  set K := ⨆ i, subgaussianNorm P (X i) with hK
  have hnorm_le : ∀ (Z : Ω → ℝ) (t : ℝ), 0 < t →
      Integrable (fun ω => exp (Z ω ^ 2 / t ^ 2)) P →
      ∫ ω, exp (Z ω ^ 2 / t ^ 2) ∂P ≤ 2 → subgaussianNorm P Z ≤ t :=
    fun Z t ht hI hle => by
      unfold subgaussianNorm
      refine csInf_le ?_ ⟨ht, hI, hle⟩
      exact ⟨0, fun x hx => hx.1.le⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hR : 0 ≤ 104 * K ^ 2 := by positivity
    refine le_trans ?_ hR
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    apply hnorm_le _ ε hε
    · norm_num
    · norm_num
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnorm_ge : ∀ i, 1 ≤ subgaussianNorm P (X i) := by
    intro i
    obtain ⟨s0, hs0, hint0, hle0⟩ := hsg i
    unfold subgaussianNorm
    refine le_csInf ⟨s0, hs0, hint0, hle0⟩ ?_
    rintro s ⟨hs, hints, hles⟩
    exact cn_one_le P (X i) (hXm i) (h2 i) s hs hints hles
  have hbdd : BddAbove (Set.range fun i => subgaussianNorm P (X i)) :=
    (Set.finite_range _).bddAbove
  have hleK : ∀ i, subgaussianNorm P (X i) ≤ K := fun i => le_ciSup hbdd i
  have hK1 : 1 ≤ K := (hnorm_ge ⟨0, hn⟩).trans (hleK _)
  set σ := 2 * K with hσdef
  have hσ1 : 1 ≤ σ := by linarith
  have hσ : ∀ i, Integrable (fun ω => exp (X i ω ^ 2 / σ ^ 2)) P ∧
      ∫ ω, exp (X i ω ^ 2 / σ ^ 2) ∂P ≤ 2 := by
    intro i
    obtain ⟨s0, hs0, hint0, hle0⟩ := hsg i
    have hne : ({s : ℝ | 0 < s ∧ Integrable (fun ω => Real.exp ((X i ω) ^ 2 / s ^ 2)) P ∧
        ∫ ω, Real.exp ((X i ω) ^ 2 / s ^ 2) ∂P ≤ 2}).Nonempty := ⟨s0, hs0, hint0, hle0⟩
    have hlt : subgaussianNorm P (X i) < σ := by linarith [hleK i]
    unfold subgaussianNorm at hlt
    obtain ⟨s, ⟨hs, hints, hles⟩, hs2⟩ := exists_lt_of_csInf_lt hne hlt
    have hmono : ∀ ω, exp (X i ω ^ 2 / σ ^ 2) ≤ exp (X i ω ^ 2 / s ^ 2) := fun ω =>
      exp_le_exp.2 (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (pow_le_pow_left₀ hs.le hs2.le 2))
    have hint2 : Integrable (fun ω => exp (X i ω ^ 2 / σ ^ 2)) P :=
      hints.mono' (((hXm i).pow_const 2).div_const _).exp.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hmono ω)
    exact ⟨hint2, (integral_mono hint2 hints hmono).trans hles⟩
  set W : Fin n → Ω → ℝ := fun i ω => X i ω ^ 2 - 1 with hW
  have hWm : ∀ i, Measurable (W i) := fun i => ((hXm i).pow_const 2).sub_const 1
  have hindW : iIndepFun W P := hind.comp (fun i x => x ^ 2 - 1) (fun i => by fun_prop)
  set S : Ω → ℝ := ∑ i, W i with hS
  have hSapp : ∀ ω, S ω = (∑ i, X i ω ^ 2) - n := by
    intro ω
    rw [hS, Finset.sum_apply]
    simp only [hW]
    rw [Finset.sum_sub_distrib]
    simp
  set b := 1 / (2 * σ ^ 2) with hb
  set a := 54 * σ ^ 4 with ha
  have hmgf : ∀ s, |s| ≤ b →
      Integrable (fun ω => exp (s * S ω)) P ∧ mgf S P s ≤ exp (a * n * s ^ 2) := by
    intro s hs
    have hc := fun i => cn_mgfW P (X i) (hXm i) (h2 i) σ hσ1 (hσ i).1 (hσ i).2 s hs
    refine ⟨?_, ?_⟩
    · exact hindW.integrable_exp_mul_sum hWm (fun i _ => (hc i).1)
    · rw [hS, hindW.mgf_sum hWm]
      calc ∏ i, mgf (W i) P s ≤ ∏ i : Fin n, exp (54 * s ^ 2 * σ ^ 4) :=
            Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => (hc i).2)
        _ = exp (a * n * s ^ 2) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
            congr 1
            rw [ha]; ring
  have hapos : 0 < a := by positivity
  have hbpos : 0 < b := by positivity
  set κ := 1 / (4 * a) with hκ
  have hκa : 4 * a * κ ≤ 1 := by
    have : 4 * a * κ = 1 := by rw [hκ]; field_simp
    exact this.le
  have hκb : 2 * κ ≤ b := by
    have e : 2 * κ = 1 / (108 * σ ^ 4) := by rw [hκ, ha]; field_simp; ring
    rw [e, hb]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_le_pow_left₀ zero_le_one hσ1 2]
  set Z : Ω → ℝ := fun ω => Real.sqrt (∑ i, (X i ω) ^ 2) - Real.sqrt n with hZ
  have htail : ∀ v : ℝ, 0 < v → P.real {ω | v < Z ω ^ 2} ≤ 2 * exp (-κ * v) := by
    intro v hv
    set M := max v (Real.sqrt (n * v)) with hM
    have hMN : (n:ℝ) * v ≤ M ^ 2 := by
      have h1 : Real.sqrt (n * v) ≤ M := le_max_right _ _
      have h2 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ n * v)
      have h3 : 0 ≤ Real.sqrt (n * v) := Real.sqrt_nonneg _
      nlinarith
    obtain ⟨s, hs0, hsb, hsv⟩ :=
      cn_choose a b n v M κ hapos hbpos (by linarith) hv (le_max_left _ _) hMN hκa hκb
    have habs_s : |s| ≤ b := by rw [abs_of_nonneg hs0]; exact hsb
    have habs_ns : |-s| ≤ b := by rw [abs_neg]; exact habs_s
    obtain ⟨hI1, hm1⟩ := hmgf s habs_s
    obtain ⟨hI2, hm2⟩ := hmgf (-s) habs_ns
    have hup : P.real {ω | M ≤ S ω} ≤ exp (-κ * v) := by
      calc P.real {ω | M ≤ S ω} ≤ exp (-s * M) * mgf S P s :=
            measure_ge_le_exp_mul_mgf M hs0 hI1
        _ ≤ exp (-s * M) * exp (a * n * s ^ 2) := mul_le_mul_of_nonneg_left hm1 (exp_pos _).le
        _ = exp (-s * M + a * n * s ^ 2) := (exp_add _ _).symm
        _ ≤ exp (-κ * v) := exp_le_exp.2 hsv
    have hlo : P.real {ω | M ≤ -S ω} ≤ exp (-κ * v) := by
      have hI1' : Integrable (fun ω => exp (s * (-S ω))) P := by
        refine hI2.congr (ae_of_all _ fun ω => ?_)
        simp only
        ring_nf
      have hmg : mgf (fun ω => -S ω) P s = mgf S P (-s) := by
        simp only [mgf]
        congr 1
        funext ω
        ring_nf
      calc P.real {ω | M ≤ -S ω} ≤ exp (-s * M) * mgf (fun ω => -S ω) P s :=
            measure_ge_le_exp_mul_mgf (X := fun ω => -S ω) M hs0 hI1'
        _ = exp (-s * M) * mgf S P (-s) := by rw [hmg]
        _ ≤ exp (-s * M) * exp (a * n * (-s) ^ 2) :=
            mul_le_mul_of_nonneg_left hm2 (exp_pos _).le
        _ = exp (-s * M + a * n * s ^ 2) := by rw [← exp_add]; ring_nf
        _ ≤ exp (-κ * v) := exp_le_exp.2 hsv
    have hsub : {ω | v < Z ω ^ 2} ⊆ {ω | M ≤ S ω} ∪ {ω | M ≤ -S ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
      have hg := cn_geom (∑ i, X i ω ^ 2) n v (Finset.sum_nonneg fun i _ => sq_nonneg _) hn1 hω
      rw [← hSapp ω] at hg
      exact le_abs.1 hg
    calc P.real {ω | v < Z ω ^ 2}
        ≤ P.real ({ω | M ≤ S ω} ∪ {ω | M ≤ -S ω}) := measureReal_mono hsub
      _ ≤ P.real {ω | M ≤ S ω} + P.real {ω | M ≤ -S ω} := measureReal_union_le _ _
      _ ≤ 2 * exp (-κ * v) := by linarith
  have hZm : Measurable (fun ω => Z ω ^ 2) := by
    have : Measurable fun ω => ∑ i, X i ω ^ 2 :=
      Finset.measurable_sum _ (fun i _ => (hXm i).pow_const 2)
    exact (this.sqrt.sub_const _).pow_const 2
  set l := 1 / (26 * σ ^ 2) ^ 2 with hl_def
  have hl : 0 < l := by positivity
  have h3l : 3 * l ≤ κ := by
    have e1 : 3 * l = 1 / ((676 / 3) * σ ^ 4) := by rw [hl_def]; field_simp; ring
    have e2 : κ = 1 / (216 * σ ^ 4) := by rw [hκ, ha]; ring
    rw [e1, e2]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_le_pow_left₀ zero_le_one hσ1 4]
  obtain ⟨hIl, hle⟩ := cn_layer P (fun ω => Z ω ^ 2) hZm (fun ω => sq_nonneg _) κ l hl h3l htail
  have hconv : ∀ ω, Z ω ^ 2 / (26 * σ ^ 2) ^ 2 = l * Z ω ^ 2 := by
    intro ω; rw [hl_def]; ring
  have hfin := hnorm_le Z (26 * σ ^ 2) (by positivity) (by simp_rw [hconv]; exact hIl)
    (by simp_rw [hconv]; exact hle)
  calc subgaussianNorm P Z ≤ 26 * σ ^ 2 := hfin
    _ = 104 * K ^ 2 := by rw [hσdef]; ring
