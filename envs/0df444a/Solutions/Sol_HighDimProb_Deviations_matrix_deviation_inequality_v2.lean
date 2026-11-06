-- Prove2me | solution 1 for HighDimProb.Deviations.matrix_deviation_inequality_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T01:20:51.108035+00:00
-- url     : https://prove2.me/submissions/5e84bdc9-5e7c-416a-a418-b6dda8807780

import Mathlib
import Definitions.Def_HighDimProb_Deviations_ExpSup
import Definitions.Def_HighDimProb_Deviations_IsIsotropic
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm_v2
import Definitions.Def_HighDimProb_Deviations_GaussianComplexity
import Theorems.Thm_HighDimProb_RandomProcesses_sudakov_minoration_finite_separated
import Theorems.Thm_GaussianMatrix_gaussian_concentration_vector

set_option autoImplicit false

section SecC1


open MeasureTheory ProbabilityTheory Real

lemma cn_exp_le (x : ℝ) : exp x ≤ 1 + x + x ^ 2 + x ^ 2 * exp x := by
  have hex := exp_pos x
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hx)).2
    have h2 : 0 ≤ x ^ 2 * exp x := by positivity
    linarith
  · rcases le_or_gt 0 x with h0 | h0
    · have hx1 : 1 < x := by rwa [abs_of_nonneg h0] at hx
      have h4 : 1 ≤ x ^ 2 := one_le_pow₀ hx1.le
      have h5 := mul_le_mul_of_nonneg_right h4 hex.le
      linarith
    · have hx1 : x < -1 := by
        rw [abs_of_neg h0] at hx; linarith
      have h4 : exp x ≤ 1 := Real.exp_le_one_iff.2 h0.le
      have h5 : 0 < x * (x + 1) := mul_pos_of_neg_of_neg h0 (by linarith)
      have h6 : 0 ≤ x ^ 2 * exp x := by positivity
      linarith

lemma cn_exp_half_le_two : exp (1 / 2 : ℝ) ≤ 2 := by
  have h1 : exp (1 / 2 : ℝ) * exp (1 / 2) = exp 1 := by rw [← exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := exp_pos (1 / 2 : ℝ)
  by_contra hc
  have hc' := not_le.mp hc
  have := mul_lt_mul'' hc' hc' (by norm_num) (by norm_num)
  linarith

/-- pointwise domination: `exp (s (y²-1)) ≤ 2 exp (y²/σ²)`. -/
lemma cn_ptB (y s σ : ℝ) (hσ : 1 ≤ σ) (hs : |s| ≤ 1 / (2 * σ ^ 2)) :
    exp (s * (y ^ 2 - 1)) ≤ 2 * exp (y ^ 2 / σ ^ 2) := by
  have hσ2 : 1 ≤ σ ^ 2 := one_le_pow₀ hσ
  have hσpos : 0 < σ ^ 2 := by positivity
  have hs2 : |s| ≤ 1 / 2 := by
    refine hs.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  have hx : s * (y ^ 2 - 1) ≤ y ^ 2 / σ ^ 2 / 2 + 1 / 2 := by
    have h1 : s * (y ^ 2 - 1) ≤ |s| * y ^ 2 + |s| := by
      have := neg_abs_le s
      have := mul_le_mul_of_nonneg_right (le_abs_self s) hy2
      linarith
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
  have hσ2 : 1 ≤ σ ^ 2 := one_le_pow₀ hσ
  have hσ4 : 1 ≤ σ ^ 4 := one_le_pow₀ hσ
  have hσpos : 0 < σ ^ 2 := by positivity
  set u := y ^ 2 / σ ^ 2 with hu_def
  have hu : 0 ≤ u := by positivity
  have hyu : y ^ 2 = u * σ ^ 2 := by rw [hu_def]; field_simp
  set h := exp (u / 2) with hh
  have hE : exp u = h * h := by rw [hh, ← exp_add]; ring_nf
  have hh1 : 1 ≤ h := one_le_exp (by linarith)
  have hF1 : u ^ 2 ≤ 8 * h := by
    have := Real.quadratic_le_exp_of_nonneg (x := u / 2) (by linarith)
    linarith
  have hy4 : (y ^ 2) ^ 2 ≤ 8 * σ ^ 4 * h := by
    rw [hyu]
    have : (u * σ ^ 2) ^ 2 = u ^ 2 * σ ^ 4 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_right hF1 (by positivity : (0:ℝ) ≤ σ ^ 4)
    linarith
  set x := s * (y ^ 2 - 1) with hx
  have hx2 : x ^ 2 ≤ s ^ 2 * (8 * σ ^ 4 * h + 1) := by
    have h1 : x ^ 2 = s ^ 2 * (y ^ 2 - 1) ^ 2 := by rw [hx]; ring
    have h2 : (y ^ 2 - 1) ^ 2 ≤ 8 * σ ^ 4 * h + 1 := by linarith [sq_nonneg y]
    rw [h1]; exact mul_le_mul_of_nonneg_left h2 (sq_nonneg s)
  have hB : exp x ≤ 2 * h := by
    have hs2 : |s| ≤ 1 / 2 := by
      refine hs.trans ?_
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
    have h1 : x ≤ |s| * y ^ 2 + |s| := by
      have := neg_abs_le s
      have := mul_le_mul_of_nonneg_right (le_abs_self s) hy2
      rw [hx]; linarith
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
      have hhh : h ≤ h * h := le_mul_of_one_le_right (by linarith) hh1
      have hq : 8 * σ ^ 4 * h + 1 + (8 * σ ^ 4 * h + 1) * (2 * h) ≤ 27 * σ ^ 4 * (h * h) := by
        linarith [mul_le_mul_of_nonneg_left hhh (by positivity : (0:ℝ) ≤ σ ^ 4),
          mul_le_mul_of_nonneg_right hσ4 (by positivity : (0:ℝ) ≤ h * h)]
      linarith [mul_le_mul_of_nonneg_left hq hs0]
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
    have h5 := mul_le_mul_of_nonneg_left
      (show Y ω ^ 2 / σ ^ 2 ≤ exp (Y ω ^ 2 / σ ^ 2) by linarith) hσpos.le
    show Y ω ^ 2 ≤ σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2)
    linarith
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
        have h6 := mul_le_mul_of_nonneg_left hle this
        linarith
    _ ≤ exp (54 * s ^ 2 * σ ^ 4) := by linarith [add_one_le_exp (54 * s ^ 2 * σ ^ 4)]

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
        have := mul_le_mul_of_nonneg_right hκa hNv
        linarith
      have e4 : 2 * κ * v ≤ s * M := le_of_mul_le_mul_right e3 haN
      linarith
  · refine ⟨b, hb.le, le_rfl, ?_⟩
    have e1 : a * N * b ^ 2 ≤ b * M / 2 := by
      have : a * N * b ^ 2 = b * (2 * a * N * b) / 2 := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left h.le hb.le
      linarith
    have e2 : κ * v ≤ b * v / 2 := by
      have := mul_le_mul_of_nonneg_right hκb hv.le
      linarith
    have e3 : b * v ≤ b * M := mul_le_mul_of_nonneg_left hMv hb.le
    linarith

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
    have := mul_le_mul_of_nonneg_left hZ h0
    linarith
  · have hsq : (Q - N) ^ 2 = (R - r) ^ 2 * (R + r) ^ 2 := by rw [hfac]; ring
    have h1 : N * v ≤ (Q - N) ^ 2 := by
      rw [hsq, ← hrN]
      have h3 : r ^ 2 ≤ (R + r) ^ 2 := by
        have := mul_nonneg hR0 (by linarith : (0:ℝ) ≤ r)
        linarith [sq_nonneg R]
      have h4 : 0 ≤ (R - r) ^ 2 := sq_nonneg _
      have h5 : 0 ≤ r ^ 2 := sq_nonneg _
      linarith [mul_le_mul_of_nonneg_left hv.le h5, mul_le_mul_of_nonneg_right h3 h4]
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

open scoped ENNReal NNReal

namespace C1

/-! ### Concentration core for measurable families (from the norm-concentration proof) -/

lemma nc_core {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (hm : 1 ≤ m) (X : Fin m → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (h2 : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = 1) (σ : ℝ) (hσ1 : 1 ≤ σ)
    (hσ : ∀ i, Integrable (fun ω => exp (X i ω ^ 2 / σ ^ 2)) P ∧
      ∫ ω, exp (X i ω ^ 2 / σ ^ 2) ∂P ≤ 2) :
    (∀ v : ℝ, 0 < v → P.real {ω | v < (Real.sqrt (∑ i, (X i ω) ^ 2) - Real.sqrt m) ^ 2} ≤
        2 * exp (-(v / (216 * σ ^ 4)))) ∧
    (∀ M : ℝ, 0 ≤ M → P.real {ω | M ≤ |∑ i, ((X i ω) ^ 2 - 1)|} ≤
        2 * exp (-min (M ^ 2 / (216 * σ ^ 4 * m)) (M / (4 * σ ^ 2)))) := by
  have hn1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0:ℝ) < m := by linarith
  set W : Fin m → Ω → ℝ := fun i ω => X i ω ^ 2 - 1 with hW
  have hWm : ∀ i, Measurable (W i) := fun i => ((hXm i).pow_const 2).sub_const 1
  have hindW : iIndepFun W P := hind.comp (fun i x => x ^ 2 - 1) (fun i => by fun_prop)
  set S : Ω → ℝ := ∑ i, W i with hS
  have hSapp : ∀ ω, S ω = ∑ i, ((X i ω) ^ 2 - 1) := by
    intro ω
    rw [hS, Finset.sum_apply]
  have hSapp' : ∀ ω, S ω = (∑ i, X i ω ^ 2) - m := by
    intro ω
    rw [hSapp, Finset.sum_sub_distrib]
    simp
  set b := 1 / (2 * σ ^ 2) with hb
  set a := 54 * σ ^ 4 with ha
  have hapos : 0 < a := by positivity
  have hbpos : 0 < b := by positivity
  have hmgf : ∀ s, |s| ≤ b →
      Integrable (fun ω => exp (s * S ω)) P ∧ mgf S P s ≤ exp (a * m * s ^ 2) := by
    intro s hs
    have hc := fun i => cn_mgfW P (X i) (hXm i) (h2 i) σ hσ1 (hσ i).1 (hσ i).2 s hs
    refine ⟨?_, ?_⟩
    · exact hindW.integrable_exp_mul_sum hWm (fun i _ => (hc i).1)
    · rw [hS, hindW.mgf_sum hWm]
      calc ∏ i, mgf (W i) P s ≤ ∏ i : Fin m, exp (54 * s ^ 2 * σ ^ 4) :=
            Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => (hc i).2)
        _ = exp (a * m * s ^ 2) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
            congr 1
            rw [ha]; ring
  have htwo : ∀ s M : ℝ, 0 ≤ s → s ≤ b →
      P.real {ω | M ≤ |S ω|} ≤ 2 * exp (-s * M + a * m * s ^ 2) := by
    intro s M hs0 hsb
    have habs_s : |s| ≤ b := by rw [abs_of_nonneg hs0]; exact hsb
    have habs_ns : |-s| ≤ b := by rw [abs_neg]; exact habs_s
    obtain ⟨hI1, hm1⟩ := hmgf s habs_s
    obtain ⟨hI2, hm2⟩ := hmgf (-s) habs_ns
    have hup : P.real {ω | M ≤ S ω} ≤ exp (-s * M + a * m * s ^ 2) := by
      calc P.real {ω | M ≤ S ω} ≤ exp (-s * M) * mgf S P s :=
            measure_ge_le_exp_mul_mgf M hs0 hI1
        _ ≤ exp (-s * M) * exp (a * m * s ^ 2) := mul_le_mul_of_nonneg_left hm1 (exp_pos _).le
        _ = exp (-s * M + a * m * s ^ 2) := (exp_add _ _).symm
    have hlo : P.real {ω | M ≤ -S ω} ≤ exp (-s * M + a * m * s ^ 2) := by
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
        _ ≤ exp (-s * M) * exp (a * m * (-s) ^ 2) :=
            mul_le_mul_of_nonneg_left hm2 (exp_pos _).le
        _ = exp (-s * M + a * m * s ^ 2) := by rw [← exp_add]; ring_nf
    have hsub : {ω | M ≤ |S ω|} ⊆ {ω | M ≤ S ω} ∪ {ω | M ≤ -S ω} := by
      intro ω hω
      have h : M ≤ |S ω| := hω
      exact le_abs.1 h
    calc P.real {ω | M ≤ |S ω|}
        ≤ P.real ({ω | M ≤ S ω} ∪ {ω | M ≤ -S ω}) := measureReal_mono hsub
      _ ≤ P.real {ω | M ≤ S ω} + P.real {ω | M ≤ -S ω} := measureReal_union_le _ _
      _ ≤ 2 * exp (-s * M + a * m * s ^ 2) := by linarith
  refine ⟨fun v hv => ?_, fun M hM => ?_⟩
  · set M := max v (Real.sqrt (m * v)) with hM
    have hMN : (m:ℝ) * v ≤ M ^ 2 := by
      have h1 : Real.sqrt (m * v) ≤ M := le_max_right _ _
      have h2 := Real.sq_sqrt (by positivity : (0:ℝ) ≤ m * v)
      have h3 : 0 ≤ Real.sqrt (m * v) := Real.sqrt_nonneg _
      nlinarith
    set κ := 1 / (4 * a) with hκ
    have hκa : 4 * a * κ ≤ 1 := by
      have : 4 * a * κ = 1 := by rw [hκ]; field_simp
      exact this.le
    have hκb : 2 * κ ≤ b := by
      have e : 2 * κ = 1 / (108 * σ ^ 4) := by rw [hκ, ha]; field_simp; ring
      rw [e, hb]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [pow_le_pow_left₀ zero_le_one hσ1 2]
    obtain ⟨s, hs0, hsb, hsv⟩ :=
      cn_choose a b m v M κ hapos hbpos hmpos hv (le_max_left _ _) hMN hκa hκb
    have hsub : {ω | v < (Real.sqrt (∑ i, (X i ω) ^ 2) - Real.sqrt m) ^ 2} ⊆
        {ω | M ≤ |S ω|} := by
      intro ω hω
      have hω' : v < (Real.sqrt (∑ i, (X i ω) ^ 2) - Real.sqrt m) ^ 2 := hω
      have hg := cn_geom (∑ i, X i ω ^ 2) m v (Finset.sum_nonneg fun i _ => sq_nonneg _) hn1 hω'
      show M ≤ |S ω|
      rw [hSapp' ω]
      exact hg
    have hκv : -κ * v = -(v / (216 * σ ^ 4)) := by rw [hκ, ha]; ring
    calc _ ≤ P.real {ω | M ≤ |S ω|} := measureReal_mono hsub
      _ ≤ 2 * exp (-s * M + a * m * s ^ 2) := htwo s M hs0 hsb
      _ ≤ 2 * exp (-κ * v) := by gcongr
      _ = _ := by rw [hκv]
  · obtain ⟨s, hsdef⟩ : ∃ s, s = min (M / (2 * a * m)) b := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := by rw [hsdef]; exact le_min (by positivity) hbpos.le
    have hsb : s ≤ b := by rw [hsdef]; exact min_le_right _ _
    have hs1 : a * m * s ≤ M / 2 := by
      have h' : s ≤ M / (2 * a * m) := by rw [hsdef]; exact min_le_left _ _
      have hamp : 0 ≤ a * m := by positivity
      calc a * m * s ≤ a * m * (M / (2 * a * m)) := mul_le_mul_of_nonneg_left h' hamp
        _ = M / 2 := by field_simp
    have hkey : -s * M + a * m * s ^ 2 ≤ -(s * M / 2) := by
      linarith [mul_le_mul_of_nonneg_left hs1 hs0]
    have hmin : min (M ^ 2 / (216 * σ ^ 4 * m)) (M / (4 * σ ^ 2)) ≤ s * M / 2 := by
      rcases min_choice (M / (2 * a * m)) b with h | h <;> rw [h] at hsdef
      · refine (min_le_left _ _).trans (le_of_eq ?_)
        rw [hsdef, ha]; field_simp; ring
      · refine (min_le_right _ _).trans (le_of_eq ?_)
        rw [hsdef, hb]; field_simp; ring
    have hE : P.real {ω | M ≤ |∑ i, ((X i ω) ^ 2 - 1)|} = P.real {ω | M ≤ |S ω|} := by
      congr 1; ext ω; simp only [Set.mem_ofPred_eq, hSapp ω]
    rw [hE]
    calc _ ≤ 2 * exp (-s * M + a * m * s ^ 2) := htwo s M hs0 hsb
      _ ≤ _ := by gcongr; linarith

/-! ### ψ₂ helpers (ENNReal-valued norm) -/

lemma tail_congr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (h : f =ᵐ[P] g) (p : ℝ → Prop) : P.real {ω | p (f ω)} = P.real {ω | p (g ω)} := by
  have hs : {ω | p (f ω)} =ᵐ[P] {ω | p (g ω)} := by
    filter_upwards [h] with ω hω
    show p (f ω) = p (g ω)
    rw [hω]
  simp only [Measure.real, measure_congr hs]

lemma valid_of_lt {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Z : Ω → ℝ) (s : ℝ)
    (hs : 0 < s) (h : HighDimProb.Concentration.subgaussianNorm P Z < ENNReal.ofReal s)
    (hZ2 : AEStronglyMeasurable (fun ω => Z ω ^ 2) P) :
    Integrable (fun ω => exp (Z ω ^ 2 / s ^ 2)) P ∧ ∫ ω, exp (Z ω ^ 2 / s ^ 2) ∂P ≤ 2 := by
  unfold HighDimProb.Concentration.subgaussianNorm at h
  simp only [iInf_lt_iff] at h
  obtain ⟨t, ht, hi, hle, hlt⟩ := h
  have hts : t < s := (ENNReal.ofReal_lt_ofReal_iff hs).1 hlt
  have hmono : ∀ ω, exp (Z ω ^ 2 / s ^ 2) ≤ exp (Z ω ^ 2 / t ^ 2) := fun ω =>
    exp_le_exp.2 (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (pow_le_pow_left₀ ht.le hts.le 2))
  have hm : AEStronglyMeasurable (fun ω => exp (Z ω ^ 2 / s ^ 2)) P :=
    (Real.continuous_exp.measurable.comp_aemeasurable
      (hZ2.aemeasurable.div_const _)).aestronglyMeasurable
  have hI : Integrable (fun ω => exp (Z ω ^ 2 / s ^ 2)) P :=
    hi.mono' hm (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hmono ω)
  exact ⟨hI, (integral_mono hI hi hmono).trans hle⟩

lemma one_le_of_valid {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Integrable (fun ω => Z ω ^ 2) P) (h2 : ∫ ω, Z ω ^ 2 ∂P = 1)
    (s : ℝ) (hs : 0 < s)
    (hI : Integrable (fun ω => exp (Z ω ^ 2 / s ^ 2)) P)
    (hle : ∫ ω, exp (Z ω ^ 2 / s ^ 2) ∂P ≤ 2) : 1 ≤ s := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hJ : Integrable (fun ω => 1 + Z ω ^ 2 / s ^ 2) P :=
    (integrable_const 1).add (hZ.div_const _)
  have hmono : ∫ ω, (1 + Z ω ^ 2 / s ^ 2) ∂P ≤ ∫ ω, exp (Z ω ^ 2 / s ^ 2) ∂P :=
    integral_mono hJ hI (fun ω => by
      have := Real.add_one_le_exp (Z ω ^ 2 / s ^ 2)
      simp only
      linarith)
  have e : ∫ ω, (1 + Z ω ^ 2 / s ^ 2) ∂P = 1 + 1 / s ^ 2 := by
    rw [integral_add (integrable_const 1) (hZ.div_const _), integral_div, h2]
    simp
  rw [e] at hmono
  have h1 : 1 / s ^ 2 ≤ 1 := by linarith
  rw [div_le_one hs2] at h1
  nlinarith

lemma psi_zero {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → ℝ) (h : ∀ ω, D ω = 0) (r : ℝ≥0∞) :
    HighDimProb.Concentration.subgaussianNorm P D ≤ r := by
  have hD : D = fun _ => 0 := funext h
  subst hD
  refine le_trans ?_ (show (0:ℝ≥0∞) ≤ r from zero_le)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [zero_add]
  have hε' : (0:ℝ) < ε := hε
  unfold HighDimProb.Concentration.subgaussianNorm
  refine iInf_le_of_le (ε:ℝ) (iInf_le_of_le hε' (iInf_le_of_le ?_ (iInf_le_of_le ?_ ?_)))
  · simp
  · norm_num
  · simp

lemma tail_8_to_2 (p x : ℝ) (hx : 0 ≤ x) (h1 : p ≤ 1) (h8 : p ≤ 8 * exp (-x)) :
    p ≤ 2 * exp (-(x / 4)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases le_or_gt x (4 * Real.log 2) with hx4 | hx4
  · have h := exp_le_exp.2 (show -Real.log 2 ≤ -(x / 4) by linarith)
    rw [Real.exp_neg, Real.exp_log (by norm_num)] at h
    linarith
  · have h3 : exp (-(3 * x / 4)) ≤ exp (-(3 * Real.log 2)) := exp_le_exp.2 (by linarith)
    have h8' : exp (-(3 * Real.log 2)) = 1 / 8 := by
      have hl8 : 3 * Real.log 2 = Real.log 8 := by
        rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
      rw [Real.exp_neg, hl8, Real.exp_log (by norm_num)]
      norm_num
    have hsplit : exp (-x) = exp (-(x / 4)) * exp (-(3 * x / 4)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpos : 0 < exp (-(x / 4)) := exp_pos _
    rw [hsplit] at h8
    rw [h8'] at h3
    linarith [mul_le_mul_of_nonneg_left h3 hpos.le]

lemma psi_of_tail {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → ℝ) (hD : AEMeasurable D P) (c : ℝ) (hc : 0 < c)
    (htail : ∀ τ : ℝ, 0 < τ → P.real {ω | τ < |D ω|} ≤ 8 * exp (-(τ ^ 2 / c))) :
    HighDimProb.Concentration.subgaussianNorm P D ≤ ENNReal.ofReal (Real.sqrt (12 * c)) := by
  obtain ⟨D', hD'm, hDe⟩ : ∃ D' : Ω → ℝ, Measurable D' ∧ D =ᵐ[P] D' :=
    ⟨hD.mk _, hD.measurable_mk, hD.ae_eq_mk⟩
  have hsq : (fun ω => D ω ^ 2) =ᵐ[P] fun ω => D' ω ^ 2 := by
    filter_upwards [hDe] with ω h
    rw [h]
  have htail' : ∀ v : ℝ, 0 < v → P.real {ω | v < D' ω ^ 2} ≤ 2 * exp (-(c⁻¹ / 4) * v) := by
    intro v hv
    have hset : {ω | v < D ω ^ 2} = {ω | Real.sqrt v < |D ω|} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [← Real.sqrt_sq_eq_abs, Real.sqrt_lt_sqrt_iff hv.le]
    have h1 : P.real {ω | v < D' ω ^ 2} = P.real {ω | v < D ω ^ 2} :=
      (tail_congr hsq (fun z => v < z)).symm
    have h8 : P.real {ω | v < D' ω ^ 2} ≤ 8 * exp (-(v / c)) := by
      rw [h1, hset]
      have := htail (Real.sqrt v) (Real.sqrt_pos.2 hv)
      rwa [Real.sq_sqrt hv.le] at this
    have h1' : P.real {ω | v < D' ω ^ 2} ≤ 1 := measureReal_le_one
    refine (tail_8_to_2 _ (v / c) (by positivity) h1' h8).trans_eq ?_
    rw [show -(v / c / 4) = -(c⁻¹ / 4) * v by ring]
  obtain ⟨hIl, hle⟩ := cn_layer P (fun ω => D' ω ^ 2) (hD'm.pow_const 2) (fun ω => sq_nonneg _)
    (c⁻¹ / 4) (c⁻¹ / 12) (by positivity) (le_of_eq (by ring)) htail'
  have hT : 0 < Real.sqrt (12 * c) := Real.sqrt_pos.2 (by positivity)
  have hT2 : Real.sqrt (12 * c) ^ 2 = 12 * c := Real.sq_sqrt (by positivity)
  have hfe : (fun ω => exp ((c⁻¹ / 12) * D' ω ^ 2)) =ᵐ[P]
      fun ω => exp (D ω ^ 2 / Real.sqrt (12 * c) ^ 2) := by
    filter_upwards [hDe] with ω h
    rw [hT2, h]
    congr 1
    field_simp
  have hI : Integrable (fun ω => exp (D ω ^ 2 / Real.sqrt (12 * c) ^ 2)) P := hIl.congr hfe
  have hle' : ∫ ω, exp (D ω ^ 2 / Real.sqrt (12 * c) ^ 2) ∂P ≤ 2 := by
    rw [← integral_congr_ae hfe]; exact hle
  unfold HighDimProb.Concentration.subgaussianNorm
  exact iInf_le_of_le _ (iInf_le_of_le hT (iInf_le_of_le hI (iInf_le_of_le hle' le_rfl)))

lemma qexp_le (q c1 c2 : ℝ) (hq : 0 ≤ q) (h1 : 0 < c1) (h12 : c1 ≤ c2) :
    exp (-(q / c1)) ≤ exp (-(q / c2)) :=
  exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_left hq h1 h12))

/-! ### The norms `‖A w‖` -/

noncomputable def Nw {Ω : Type} {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) w) ^ 2)

noncomputable def Xp {Ω : Type} {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n)) (ω : Ω) : ℝ :=
  Nw A w ω - Real.sqrt m * ‖w‖

section Nw
variable {Ω : Type} {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n))

lemma Nw_sq (w : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    (Nw A w ω) ^ 2 = ∑ i, (inner (𝕜 := ℝ) (A i ω) w) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma Nw_nonneg (w : EuclideanSpace ℝ (Fin n)) (ω : Ω) : 0 ≤ Nw A w ω := Real.sqrt_nonneg _

lemma Nw_zero (ω : Ω) : Nw A 0 ω = 0 := by simp [Nw]

lemma Nw_smul (c : ℝ) (w : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    Nw A (c • w) ω = |c| * Nw A w ω := by
  unfold Nw
  simp_rw [inner_smul_right, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma Nw_eq_norm (w : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    Nw A w ω = ‖(WithLp.toLp 2 (fun i => inner (𝕜 := ℝ) (A i ω) w) : EuclideanSpace ℝ (Fin m))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold Nw
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

lemma Nw_sub_le (x y : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    |Nw A x ω - Nw A y ω| ≤ Nw A (x - y) ω := by
  rw [Nw_eq_norm, Nw_eq_norm, Nw_eq_norm]
  have : (WithLp.toLp 2 (fun i => inner (𝕜 := ℝ) (A i ω) (x - y)) : EuclideanSpace ℝ (Fin m)) =
      WithLp.toLp 2 (fun i => inner (𝕜 := ℝ) (A i ω) x) -
        WithLp.toLp 2 (fun i => inner (𝕜 := ℝ) (A i ω) y) := by
    rw [← WithLp.toLp_sub]
    congr 1
    funext i
    simp [inner_sub_right]
  rw [this]
  exact abs_norm_sub_norm_le _ _

lemma Xp_smul (c : ℝ) (hc : 0 ≤ c) (w : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    Xp A (c • w) ω = c * Xp A w ω := by
  unfold Xp
  rw [Nw_smul, abs_of_nonneg hc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  ring

end Nw

end C1

namespace C1

/-! ### Measurable families along a direction -/

lemma dir_family {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (hind : iIndepFun A P)
    (hiso : ∀ i, HighDimProb.Deviations.IsIsotropic P (A i))
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) (σ : ℝ)
    (hσ : ∀ i, Integrable (fun ω => exp ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 / σ ^ 2)) P ∧
      ∫ ω, exp ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 / σ ^ 2) ∂P ≤ 2) :
    ∃ Y : Fin m → Ω → ℝ, (∀ i, Measurable (Y i)) ∧ iIndepFun Y P ∧
      (∀ i, (fun ω => (Y i ω) ^ 2) =ᵐ[P] fun ω => (inner (𝕜 := ℝ) (A i ω) w) ^ 2) ∧
      (∀ i, ∫ ω, (Y i ω) ^ 2 ∂P = 1) ∧
      (∀ i, Integrable (fun ω => exp (Y i ω ^ 2 / σ ^ 2)) P ∧
        ∫ ω, exp (Y i ω ^ 2 / σ ^ 2) ∂P ≤ 2) := by
  have hf : ∀ i, AEMeasurable (fun ω => |inner (𝕜 := ℝ) (A i ω) w|) P := by
    intro i
    have h1 : AEMeasurable (fun ω => (inner (𝕜 := ℝ) (A i ω) w) ^ 2) P :=
      (hiso i w).1.aemeasurable
    exact h1.sqrt.congr (ae_of_all _ fun ω => Real.sqrt_sq_eq_abs _)
  have hcont : Continuous fun v : EuclideanSpace ℝ (Fin n) => |inner (𝕜 := ℝ) v w| :=
    continuous_abs.comp (continuous_id.inner continuous_const)
  have hindf : iIndepFun (fun i ω => |inner (𝕜 := ℝ) (A i ω) w|) P :=
    hind.comp (fun _ v => |inner (𝕜 := ℝ) v w|) (fun _ => hcont.measurable)
  choose Y hYm hYe using fun i => (⟨(hf i).mk _, (hf i).measurable_mk, (hf i).ae_eq_mk⟩ :
    ∃ g : Ω → ℝ, Measurable g ∧ (fun ω => |inner (𝕜 := ℝ) (A i ω) w|) =ᵐ[P] g)
  have hsq : ∀ i, (fun ω => (Y i ω) ^ 2) =ᵐ[P] fun ω => (inner (𝕜 := ℝ) (A i ω) w) ^ 2 := by
    intro i
    filter_upwards [hYe i] with ω h
    rw [← h, sq_abs]
  refine ⟨Y, hYm, hindf.congr hYe, hsq, fun i => ?_, fun i => ?_⟩
  · rw [integral_congr_ae (hsq i), (hiso i w).2, hw]; norm_num
  · have hc : (fun ω => exp ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 / σ ^ 2)) =ᵐ[P]
        fun ω => exp (Y i ω ^ 2 / σ ^ 2) := by
      filter_upwards [hsq i] with ω h
      rw [← h]
    exact ⟨(hσ i).1.congr hc, (integral_congr_ae hc).symm.le.trans (hσ i).2⟩

lemma N_tails {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m n : ℕ} (hm : 1 ≤ m) (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (hind : iIndepFun A P)
    (hiso : ∀ i, HighDimProb.Deviations.IsIsotropic P (A i)) (σ : ℝ) (hσ1 : 1 ≤ σ)
    (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1)
    (hσ : ∀ i, Integrable (fun ω => exp ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 / σ ^ 2)) P ∧
      ∫ ω, exp ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 / σ ^ 2) ∂P ≤ 2) :
    (∀ v : ℝ, 0 < v → P.real {ω | v < (Nw A w ω - Real.sqrt m) ^ 2} ≤
        2 * exp (-(v / (216 * σ ^ 4)))) ∧
    (∀ M : ℝ, 0 ≤ M → P.real {ω | M ≤ |∑ i, ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 - 1)|} ≤
        2 * exp (-min (M ^ 2 / (216 * σ ^ 4 * m)) (M / (4 * σ ^ 2)))) := by
  obtain ⟨Y, hYm, hYi, hsq, h2, hYσ⟩ := dir_family P A hind hiso w hw σ hσ
  obtain ⟨h1, h2'⟩ := nc_core P hm Y hYm hYi h2 σ hσ1 hYσ
  have hall : ∀ᵐ ω ∂P, ∀ i, (Y i ω) ^ 2 = (inner (𝕜 := ℝ) (A i ω) w) ^ 2 :=
    ae_all_iff.2 fun i => hsq i
  refine ⟨fun v hv => ?_, fun M hM => ?_⟩
  · have hc : (fun ω => (Real.sqrt (∑ i, (Y i ω) ^ 2) - Real.sqrt m) ^ 2) =ᵐ[P]
        fun ω => (Nw A w ω - Real.sqrt m) ^ 2 := by
      filter_upwards [hall] with ω hω
      simp only [Nw, hω]
    calc P.real {ω | v < (Nw A w ω - Real.sqrt m) ^ 2}
        = P.real {ω | v < (Real.sqrt (∑ i, (Y i ω) ^ 2) - Real.sqrt m) ^ 2} :=
          (tail_congr hc (fun z => v < z)).symm
      _ ≤ _ := h1 v hv
  · have hc : (fun ω => |∑ i, ((Y i ω) ^ 2 - 1)|) =ᵐ[P]
        fun ω => |∑ i, ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 - 1)| := by
      filter_upwards [hall] with ω hω
      simp only [hω]
    calc P.real {ω | M ≤ |∑ i, ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 - 1)|}
        = P.real {ω | M ≤ |∑ i, ((Y i ω) ^ 2 - 1)|} :=
          (tail_congr hc (fun z => M ≤ z)).symm
      _ ≤ _ := h2' M hM

/-! ### Step 2: unit vectors -/

lemma pol_alg (p q δ ρ : ℝ) (hδ : δ ≠ 0) (hρ : ρ ≠ 0) :
    p ^ 2 - q ^ 2 = δ * ρ ^ 2 / 4 *
      (((ρ⁻¹ * (δ⁻¹ * (p - q) + (p + q))) ^ 2 - 1) - ((ρ⁻¹ * (δ⁻¹ * (p - q) - (p + q))) ^ 2 - 1)) := by
  field_simp
  ring

lemma step2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m n : ℕ} (hm : 1 ≤ m) (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (σ : ℝ) (hσ1 : 1 ≤ σ)
    (hT1 : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ v : ℝ, 0 < v →
      P.real {ω | v < (Nw A w ω - Real.sqrt m) ^ 2} ≤ 2 * exp (-(v / (216 * σ ^ 4))))
    (hT2 : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ M : ℝ, 0 ≤ M →
      P.real {ω | M ≤ |∑ i, ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 - 1)|} ≤
        2 * exp (-min (M ^ 2 / (216 * σ ^ 4 * m)) (M / (4 * σ ^ 2))))
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t * ‖x - y‖ < |Nw A x ω - Nw A y ω|} ≤
      6 * exp (-(t ^ 2 / (5400 * σ ^ 4))) := by
  have hE0 : 0 ≤ exp (-(t ^ 2 / (5400 * σ ^ 4))) := (exp_pos _).le
  have hσ4 : 1 ≤ σ ^ 4 := one_le_pow₀ hσ1
  have hσ2 : 1 ≤ σ ^ 2 := one_le_pow₀ hσ1
  have hσ42 : σ ^ 2 ≤ σ ^ 4 := by
    linarith [mul_le_mul_of_nonneg_left hσ2 (by positivity : (0:ℝ) ≤ σ ^ 2)]
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 (by linarith)
  have hsm2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt (by linarith)
  by_cases hxy : x = y
  · subst hxy
    have : {ω | t * ‖x - x‖ < |Nw A x ω - Nw A x ω|} = ∅ := by
      ext ω; simp
    rw [this, measureReal_empty]; positivity
  have hδ : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  obtain ⟨u, hu⟩ : ∃ u, u = ‖x - y‖⁻¹ • (x - y) := ⟨_, rfl⟩
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hδ.ne']
  have hxyu : x - y = ‖x - y‖ • u := by
    rw [hu, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
  by_cases htm : 2 * Real.sqrt m < t
  · have htpos : 0 < t := by linarith
    have hsub : {ω | t * ‖x - y‖ < |Nw A x ω - Nw A y ω|} ⊆
        {ω | t ^ 2 / 4 < (Nw A u ω - Real.sqrt m) ^ 2} := by
      intro ω hω
      have hω' : t * ‖x - y‖ < |Nw A x ω - Nw A y ω| := hω
      have h1 := Nw_sub_le A x y ω
      have h2 : Nw A (x - y) ω = ‖x - y‖ * Nw A u ω := by
        rw [show Nw A (x - y) ω = Nw A (‖x - y‖ • u) ω by rw [← hxyu], Nw_smul, abs_of_pos hδ]
      have h3 : t < Nw A u ω :=
        lt_of_mul_lt_mul_left (by linarith : ‖x - y‖ * t < ‖x - y‖ * Nw A u ω) hδ.le
      have h4 : t / 2 < Nw A u ω - Real.sqrt m := by linarith
      show t ^ 2 / 4 < (Nw A u ω - Real.sqrt m) ^ 2
      linarith [mul_pos (by linarith : (0:ℝ) < Nw A u ω - Real.sqrt m - t / 2)
        (by linarith : (0:ℝ) < Nw A u ω - Real.sqrt m + t / 2)]
    calc _ ≤ P.real {ω | t ^ 2 / 4 < (Nw A u ω - Real.sqrt m) ^ 2} := measureReal_mono hsub
      _ ≤ 2 * exp (-(t ^ 2 / 4 / (216 * σ ^ 4))) := hT1 u hu1 _ (by positivity)
      _ = 2 * exp (-(t ^ 2 / (864 * σ ^ 4))) := by
          rw [show t ^ 2 / 4 / (216 * σ ^ 4) = t ^ 2 / (864 * σ ^ 4) by ring]
      _ ≤ 6 * exp (-(t ^ 2 / (5400 * σ ^ 4))) := by
          have := qexp_le (t ^ 2) (864 * σ ^ 4) (5400 * σ ^ 4) (sq_nonneg _) (by positivity)
            (by linarith)
          linarith
  push_neg at htm
  -- polarization data
  obtain ⟨v, hv⟩ : ∃ v, v = x + y := ⟨_, rfl⟩
  have huv : inner (𝕜 := ℝ) u v = 0 := by
    rw [hu, hv, inner_smul_left, inner_sub_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm x y, hx, hy]
    simp
    right
    ring
  have hv2 : ‖v‖ ≤ 2 := by
    rw [hv]
    calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
      _ = 2 := by rw [hx, hy]; norm_num
  obtain ⟨ρ2, hρ2⟩ : ∃ ρ2 : ℝ, ρ2 = 1 + ‖v‖ ^ 2 := ⟨_, rfl⟩
  have hρ2le : ρ2 ≤ 5 := by rw [hρ2]; nlinarith [norm_nonneg v]
  have hρ2ge : 1 ≤ ρ2 := by rw [hρ2]; linarith [sq_nonneg ‖v‖]
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = Real.sqrt ρ2 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; exact Real.sqrt_pos.2 (by linarith)
  have hρsq : ρ ^ 2 = ρ2 := by rw [hρdef]; exact Real.sq_sqrt (by linarith)
  have hupv : ‖u + v‖ ^ 2 = ρ2 := by
    rw [norm_add_sq_real, huv, hu1, hρ2]; ring
  have humv : ‖u - v‖ ^ 2 = ρ2 := by
    rw [norm_sub_sq_real, huv, hu1, hρ2]; ring
  obtain ⟨w1, hw1d⟩ : ∃ w, w = ρ⁻¹ • (u + v) := ⟨_, rfl⟩
  obtain ⟨w2, hw2d⟩ : ∃ w, w = ρ⁻¹ • (u - v) := ⟨_, rfl⟩
  have hw1 : ‖w1‖ = 1 := by
    have : ‖u + v‖ = ρ := by
      rw [← Real.sqrt_sq (norm_nonneg (u + v)), hupv, hρdef]
    rw [hw1d, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hρ, this, inv_mul_cancel₀ hρ.ne']
  have hw2 : ‖w2‖ = 1 := by
    have : ‖u - v‖ = ρ := by
      rw [← Real.sqrt_sq (norm_nonneg (u - v)), humv, hρdef]
    rw [hw2d, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hρ, this, inv_mul_cancel₀ hρ.ne']
  have hpol : ∀ ω, (Nw A x ω) ^ 2 - (Nw A y ω) ^ 2 = ‖x - y‖ * ρ2 / 4 *
      ((∑ i, ((inner (𝕜 := ℝ) (A i ω) w1) ^ 2 - 1)) -
        ∑ i, ((inner (𝕜 := ℝ) (A i ω) w2) ^ 2 - 1)) := by
    intro ω
    rw [Nw_sq, Nw_sq, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw1d, hw2d, hu, hv, ← hρsq]
    simp only [inner_smul_right, inner_add_right, inner_sub_right]
    exact pol_alg _ _ _ _ hδ.ne' hρ.ne'
  obtain ⟨M, hMd⟩ : ∃ M : ℝ, M = t * Real.sqrt m / 5 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMd]; positivity
  have hsub : {ω | t * ‖x - y‖ < |Nw A x ω - Nw A y ω|} ⊆
      {ω | (m:ℝ) / 4 < (Nw A x ω - Real.sqrt m) ^ 2} ∪
        ({ω | M ≤ |∑ i, ((inner (𝕜 := ℝ) (A i ω) w1) ^ 2 - 1)|} ∪
          {ω | M ≤ |∑ i, ((inner (𝕜 := ℝ) (A i ω) w2) ^ 2 - 1)|}) := by
    intro ω hω
    have hω' : t * ‖x - y‖ < |Nw A x ω - Nw A y ω| := hω
    by_cases hA : (m:ℝ) / 4 < (Nw A x ω - Real.sqrt m) ^ 2
    · exact Or.inl hA
    right
    push_neg at hA
    have hNx : Real.sqrt m / 2 ≤ Nw A x ω := by
      by_contra hc
      push_neg at hc
      linarith [hsm2, mul_pos (by linarith : (0:ℝ) < -(Nw A x ω - Real.sqrt m) - Real.sqrt m / 2)
        (by linarith : (0:ℝ) < -(Nw A x ω - Real.sqrt m) + Real.sqrt m / 2)]
    have hNy := Nw_nonneg A y ω
    have hprod : t * ‖x - y‖ * (Real.sqrt m / 2) ≤ |(Nw A x ω) ^ 2 - (Nw A y ω) ^ 2| := by
      have e : (Nw A x ω) ^ 2 - (Nw A y ω) ^ 2 = (Nw A x ω - Nw A y ω) * (Nw A x ω + Nw A y ω) := by
        ring
      rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Nw A x ω + Nw A y ω)]
      exact mul_le_mul hω'.le (by linarith) (by positivity) (abs_nonneg _)
    rw [hpol ω, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖x - y‖ * ρ2 / 4)] at hprod
    set S1 := ∑ i, ((inner (𝕜 := ℝ) (A i ω) w1) ^ 2 - 1)
    set S2 := ∑ i, ((inner (𝕜 := ℝ) (A i ω) w2) ^ 2 - 1)
    have h5 : 2 * t * Real.sqrt m ≤ ρ2 * |S1 - S2| := by
      have : ‖x - y‖ * (2 * t * Real.sqrt m) ≤ ‖x - y‖ * (ρ2 * |S1 - S2|) := by linarith [hprod]
      exact le_of_mul_le_mul_left this hδ
    have h6 : 2 * M ≤ |S1 - S2| := by
      rw [hMd]
      have : ρ2 * |S1 - S2| ≤ 5 * |S1 - S2| :=
        mul_le_mul_of_nonneg_right hρ2le (abs_nonneg _)
      linarith
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hc
    have := abs_sub S1 S2
    linarith [hc.1, hc.2]
  have hB1 : P.real {ω | (m:ℝ) / 4 < (Nw A x ω - Real.sqrt m) ^ 2} ≤
      2 * exp (-(t ^ 2 / (5400 * σ ^ 4))) := by
    refine (hT1 x hx _ (by positivity)).trans ?_
    have ht2 : t ^ 2 ≤ 4 * m := by
      have h := pow_le_pow_left₀ ht htm 2
      rw [mul_pow, hsm2] at h
      linarith
    have hq : t ^ 2 / (5400 * σ ^ 4) ≤ (m:ℝ) / 4 / (216 * σ ^ 4) := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [mul_le_mul_of_nonneg_right ht2 (by positivity : (0:ℝ) ≤ 864 * σ ^ 4),
        mul_nonneg (by positivity : (0:ℝ) ≤ m) (by positivity : (0:ℝ) ≤ σ ^ 4)]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (neg_le_neg hq)) (by norm_num)
  have hmin : t ^ 2 / (5400 * σ ^ 4) ≤ min (M ^ 2 / (216 * σ ^ 4 * m)) (M / (4 * σ ^ 2)) := by
    refine le_min (le_of_eq ?_) ?_
    · rw [hMd, div_pow, mul_pow, hsm2]
      field_simp
      ring
    · have ht2 : t ^ 2 ≤ 2 * t * Real.sqrt m := by
        have h := mul_le_mul_of_nonneg_left htm ht
        linarith
      rw [hMd, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith [mul_le_mul_of_nonneg_right ht2 (by positivity : (0:ℝ) ≤ 4 * σ ^ 2),
        mul_le_mul_of_nonneg_left hσ42 (by positivity : (0:ℝ) ≤ t * Real.sqrt m),
        mul_nonneg (by positivity : (0:ℝ) ≤ t * Real.sqrt m) (by positivity : (0:ℝ) ≤ σ ^ 4)]
  have hB2 : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
      P.real {ω | M ≤ |∑ i, ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 - 1)|} ≤
        2 * exp (-(t ^ 2 / (5400 * σ ^ 4))) := by
    intro w hw
    refine (hT2 w hw M hM0).trans ?_
    exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (neg_le_neg hmin)) (by norm_num)
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (measureReal_union_le _ _)
    _ ≤ 2 * exp (-(t ^ 2 / (5400 * σ ^ 4))) +
        (2 * exp (-(t ^ 2 / (5400 * σ ^ 4))) + 2 * exp (-(t ^ 2 / (5400 * σ ^ 4)))) :=
        add_le_add hB1 (add_le_add (hB2 w1 hw1) (hB2 w2 hw2))
    _ = _ := by ring

end C1

namespace C1

/-! ### Step 3: general vectors -/

lemma step3u {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m n : ℕ} (hm : 1 ≤ m) (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (σ : ℝ) (hσ1 : 1 ≤ σ)
    (hT1 : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ v : ℝ, 0 < v →
      P.real {ω | v < (Nw A w ω - Real.sqrt m) ^ 2} ≤ 2 * exp (-(v / (216 * σ ^ 4))))
    (hT2 : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ M : ℝ, 0 ≤ M →
      P.real {ω | M ≤ |∑ i, ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 - 1)|} ≤
        2 * exp (-min (M ^ 2 / (216 * σ ^ 4 * m)) (M / (4 * σ ^ 2))))
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) (hy : ‖y‖ ≤ 1) (hxy : x ≠ y)
    (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | τ < |Xp A x ω - Xp A y ω|} ≤
      8 * exp (-(τ ^ 2 / (48600 * σ ^ 4 * ‖x - y‖ ^ 2))) := by
  have hδ : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hσ4 : 1 ≤ σ ^ 4 := one_le_pow₀ hσ1
  by_cases hy0 : y = 0
  · subst hy0
    have hxn : ‖x - 0‖ = 1 := by rw [sub_zero, hx]
    rw [hxn]
    have hsub : {ω | τ < |Xp A x ω - Xp A 0 ω|} ⊆
        {ω | τ ^ 2 < (Nw A x ω - Real.sqrt m) ^ 2} := by
      intro ω hω
      have hω' : τ < |Xp A x ω - Xp A 0 ω| := hω
      have e : Xp A x ω - Xp A 0 ω = Nw A x ω - Real.sqrt m := by
        simp only [Xp, Nw_zero, hx, norm_zero]; ring
      rw [e] at hω'
      show τ ^ 2 < (Nw A x ω - Real.sqrt m) ^ 2
      rw [← sq_abs (Nw A x ω - Real.sqrt m)]
      exact pow_lt_pow_left₀ hω' hτ.le two_ne_zero
    calc _ ≤ _ := measureReal_mono hsub
      _ ≤ 2 * exp (-(τ ^ 2 / (216 * σ ^ 4))) := hT1 x hx _ (by positivity)
      _ ≤ 8 * exp (-(τ ^ 2 / (48600 * σ ^ 4 * 1 ^ 2))) := by
          have := qexp_le (τ ^ 2) (216 * σ ^ 4) (48600 * σ ^ 4 * 1 ^ 2) (sq_nonneg _)
            (by positivity) (by linarith)
          have := exp_pos (-(τ ^ 2 / (48600 * σ ^ 4 * 1 ^ 2)))
          linarith
  have hs : 0 < ‖y‖ := norm_pos_iff.2 hy0
  obtain ⟨yb, hyb⟩ : ∃ yb, yb = ‖y‖⁻¹ • y := ⟨_, rfl⟩
  have hyb1 : ‖yb‖ = 1 := by
    rw [hyb, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
  have hy_eq : y = ‖y‖ • yb := by rw [hyb, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hXy : ∀ ω, Xp A y ω = ‖y‖ * Xp A yb ω := by
    intro ω
    calc Xp A y ω = Xp A (‖y‖ • yb) ω := by rw [← hy_eq]
      _ = ‖y‖ * Xp A yb ω := Xp_smul A ‖y‖ (norm_nonneg _) yb ω
  have hβ0 : 0 ≤ 1 - ‖y‖ := by linarith
  have hβδ : 1 - ‖y‖ ≤ ‖x - y‖ := by
    have := norm_sub_norm_le x y
    rw [hx] at this
    linarith
  have hyyb : ‖y - yb‖ = 1 - ‖y‖ := by
    have : y - yb = (‖y‖ - 1) • yb := by
      rw [sub_smul, one_smul, ← hy_eq]
    rw [this, norm_smul, hyb1, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hα : ‖x - yb‖ ≤ ‖x - y‖ + (1 - ‖y‖) := by
    have := norm_sub_le_norm_sub_add_norm_sub x y yb
    linarith
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = τ / (3 * ‖x - y‖) := ⟨_, rfl⟩
  have htpos : 0 < t := by rw [ht]; positivity
  have ht3 : t * (3 * ‖x - y‖) = τ := by rw [ht]; field_simp
  have hsub : {ω | τ < |Xp A x ω - Xp A y ω|} ⊆
      {ω | t * ‖x - yb‖ < |Nw A x ω - Nw A yb ω|} ∪
        {ω | t ^ 2 < (Nw A yb ω - Real.sqrt m) ^ 2} := by
    intro ω hω
    have hω' : τ < |Xp A x ω - Xp A y ω| := hω
    have e : Xp A x ω - Xp A y ω =
        (Nw A x ω - Nw A yb ω) + (1 - ‖y‖) * (Nw A yb ω - Real.sqrt m) := by
      rw [hXy]
      simp only [Xp, hx, hyb1]
      ring
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h2' : |Nw A yb ω - Real.sqrt m| ≤ t := by
      by_contra hc
      push_neg at hc
      have := pow_lt_pow_left₀ hc htpos.le two_ne_zero
      rw [sq_abs] at this
      linarith
    have h3 : |Xp A x ω - Xp A y ω| ≤ t * ‖x - yb‖ + (1 - ‖y‖) * t := by
      rw [e]
      calc _ ≤ |Nw A x ω - Nw A yb ω| + |(1 - ‖y‖) * (Nw A yb ω - Real.sqrt m)| :=
            abs_add_le _ _
        _ = |Nw A x ω - Nw A yb ω| + (1 - ‖y‖) * |Nw A yb ω - Real.sqrt m| := by
            rw [abs_mul, abs_of_nonneg hβ0]
        _ ≤ _ := add_le_add h1 (mul_le_mul_of_nonneg_left h2' hβ0)
    have h4 : t * ‖x - yb‖ + (1 - ‖y‖) * t ≤ τ := by
      linarith [mul_le_mul_of_nonneg_left hα htpos.le, mul_le_mul_of_nonneg_left hβδ htpos.le]
    linarith
  have e : t ^ 2 / (5400 * σ ^ 4) = τ ^ 2 / (48600 * σ ^ 4 * ‖x - y‖ ^ 2) := by
    rw [ht]; field_simp; ring
  have hq := qexp_le (t ^ 2) (216 * σ ^ 4) (5400 * σ ^ 4) (sq_nonneg _) (by positivity)
    (by linarith)
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 6 * exp (-(t ^ 2 / (5400 * σ ^ 4))) + 2 * exp (-(t ^ 2 / (216 * σ ^ 4))) :=
        add_le_add (step2 P hm A σ hσ1 hT1 hT2 x yb hx hyb1 t htpos.le)
          (hT1 yb hyb1 _ (by positivity))
    _ ≤ 8 * exp (-(t ^ 2 / (5400 * σ ^ 4))) := by linarith
    _ = _ := by rw [e]

lemma step3 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m n : ℕ} (hm : 1 ≤ m) (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)) (σ : ℝ) (hσ1 : 1 ≤ σ)
    (hT1 : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ v : ℝ, 0 < v →
      P.real {ω | v < (Nw A w ω - Real.sqrt m) ^ 2} ≤ 2 * exp (-(v / (216 * σ ^ 4))))
    (hT2 : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ M : ℝ, 0 ≤ M →
      P.real {ω | M ≤ |∑ i, ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 - 1)|} ≤
        2 * exp (-min (M ^ 2 / (216 * σ ^ 4 * m)) (M / (4 * σ ^ 2))))
    (x y : EuclideanSpace ℝ (Fin n)) (hxy : x ≠ y) (τ : ℝ) (hτ : 0 < τ) :
    P.real {ω | τ < |Xp A x ω - Xp A y ω|} ≤
      8 * exp (-(τ ^ 2 / (48600 * σ ^ 4 * ‖x - y‖ ^ 2))) := by
  have key : ∀ x y : EuclideanSpace ℝ (Fin n), x ≠ y → ‖y‖ ≤ ‖x‖ →
      P.real {ω | τ < |Xp A x ω - Xp A y ω|} ≤
        8 * exp (-(τ ^ 2 / (48600 * σ ^ 4 * ‖x - y‖ ^ 2))) := by
    intro x y hxy hyx
    have hr : 0 < ‖x‖ := by
      rcases (norm_nonneg x).lt_or_eq with h | h
      · exact h
      · exfalso
        have hx0 : x = 0 := norm_eq_zero.1 h.symm
        have hy0 : y = 0 := norm_eq_zero.1 (le_antisymm (h ▸ hyx) (norm_nonneg _))
        exact hxy (hx0.trans hy0.symm)
    obtain ⟨x', hx'd⟩ : ∃ z, z = ‖x‖⁻¹ • x := ⟨_, rfl⟩
    obtain ⟨y', hy'd⟩ : ∃ z, z = ‖x‖⁻¹ • y := ⟨_, rfl⟩
    have hx' : ‖x'‖ = 1 := by
      rw [hx'd, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
    have hy' : ‖y'‖ ≤ 1 := by
      rw [hy'd, norm_smul, norm_inv, norm_norm]
      rw [inv_mul_le_iff₀ hr]
      linarith
    have hxy' : x' ≠ y' := by
      rw [hx'd, hy'd]
      exact (smul_right_injective _ (inv_ne_zero hr.ne')).ne hxy
    have hxe : x = ‖x‖ • x' := by rw [hx'd, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hye : y = ‖x‖ • y' := by rw [hy'd, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hD : ∀ ω, Xp A x ω - Xp A y ω = ‖x‖ * (Xp A x' ω - Xp A y' ω) := by
      intro ω
      have h1 : Xp A x ω = ‖x‖ * Xp A x' ω := by
        calc Xp A x ω = Xp A (‖x‖ • x') ω := by rw [← hxe]
          _ = _ := Xp_smul A _ (norm_nonneg _) x' ω
      have h2 : Xp A y ω = ‖x‖ * Xp A y' ω := by
        calc Xp A y ω = Xp A (‖x‖ • y') ω := by rw [← hye]
          _ = _ := Xp_smul A _ (norm_nonneg _) y' ω
      rw [h1, h2]
      ring
    have hdist : ‖x' - y'‖ = ‖x‖⁻¹ * ‖x - y‖ := by
      rw [hx'd, hy'd, ← smul_sub, norm_smul, norm_inv, norm_norm]
    have hset : {ω | τ < |Xp A x ω - Xp A y ω|} = {ω | τ / ‖x‖ < |Xp A x' ω - Xp A y' ω|} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [hD, abs_mul, abs_of_pos hr, div_lt_iff₀ hr, mul_comm]
    rw [hset]
    have hδ : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have e : (τ / ‖x‖) ^ 2 / (48600 * σ ^ 4 * ‖x' - y'‖ ^ 2) =
        τ ^ 2 / (48600 * σ ^ 4 * ‖x - y‖ ^ 2) := by
      rw [hdist]
      field_simp
    rw [← e]
    exact step3u P hm A σ hσ1 hT1 hT2 x' y' hx' hy' hxy' (τ / ‖x‖) (by positivity)
  rcases le_total ‖y‖ ‖x‖ with h | h
  · exact key x y hxy h
  · have := key y x (Ne.symm hxy) h
    rw [norm_sub_rev] at this
    have e : {ω | τ < |Xp A x ω - Xp A y ω|} = {ω | τ < |Xp A y ω - Xp A x ω|} := by
      ext ω
      simp only [Set.mem_ofPred_eq, abs_sub_comm]
    rw [e]
    exact this

end C1

open MeasureTheory ProbabilityTheory in
theorem C1.increments :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P → (∀ i, HighDimProb.Deviations.IsIsotropic P (A i)) →
        ∀ (K : NNReal), (∀ i, HighDimProb.Deviations.subgaussianVectorNorm P (A i) ≤ K) →
        ∀ x y : EuclideanSpace ℝ (Fin n),
          HighDimProb.Concentration.subgaussianNorm P (fun ω =>
            (Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x) ^ 2) - Real.sqrt m * ‖x‖) -
            (Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) y) ^ 2) - Real.sqrt m * ‖y‖)) ≤
          ENNReal.ofReal (C * (K : ℝ) ^ 2 * ‖x - y‖) := by
  refine ⟨3100, by norm_num, ?_⟩
  intro Ω _ P _ m n A hind hiso K hK x y
  by_cases hxy : x = y
  · subst hxy
    exact C1.psi_zero P _ (fun ω => sub_self _) _
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · subst hm0
    exact C1.psi_zero P _ (fun ω => by simp) _
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      exact hxy (Subsingleton.elim _ _)
    · exact h
  obtain ⟨e, he⟩ : ∃ e : EuclideanSpace ℝ (Fin n), ‖e‖ = 1 := by
    have hv : (EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1:ℝ)) ≠ 0 := by simp
    refine ⟨‖EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1:ℝ)‖⁻¹ •
      EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1:ℝ), ?_⟩
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  have hψle : ∀ i (w : EuclideanSpace ℝ (Fin n)), ‖w‖ = 1 →
      HighDimProb.Concentration.subgaussianNorm P (fun ω => inner (𝕜 := ℝ) (A i ω) w) ≤
        ENNReal.ofReal K := by
    intro i w hw
    refine le_trans ?_ ((hK i).trans_eq ENNReal.ofReal_coe_nnreal.symm)
    exact le_iSup (fun z : {v : EuclideanSpace ℝ (Fin n) // ‖v‖ = 1} =>
      HighDimProb.Concentration.subgaussianNorm P (fun ω => inner (𝕜 := ℝ) (A i ω) z.1)) ⟨w, hw⟩
  have hK0 : (0:ℝ) ≤ K := K.coe_nonneg
  have hK1 : (1:ℝ) ≤ K := by
    by_contra hlt
    push_neg at hlt
    have hs : 0 < ((K:ℝ) + 1) / 2 := by positivity
    have hlt2 : HighDimProb.Concentration.subgaussianNorm P
        (fun ω => inner (𝕜 := ℝ) (A ⟨0, hm⟩ ω) e) < ENNReal.ofReal (((K:ℝ) + 1) / 2) :=
      (hψle _ e he).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hs).2 (by linarith))
    obtain ⟨hI, hle⟩ := C1.valid_of_lt P _ _ hs hlt2 (hiso _ e).1.aestronglyMeasurable
    have := C1.one_le_of_valid P _ (hiso _ e).1 (by rw [(hiso _ e).2, he]; norm_num) _ hs hI hle
    linarith
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = 2 * K := ⟨_, rfl⟩
  have hσ1 : 1 ≤ σ := by rw [hσdef]; linarith
  have hσv : ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ i,
      Integrable (fun ω => Real.exp ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 / σ ^ 2)) P ∧
      ∫ ω, Real.exp ((inner (𝕜 := ℝ) (A i ω) w) ^ 2 / σ ^ 2) ∂P ≤ 2 := fun w hw i =>
    C1.valid_of_lt P _ σ (by linarith)
      ((hψle i w hw).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)))
      (hiso i w).1.aestronglyMeasurable
  have hT := fun (w : EuclideanSpace ℝ (Fin n)) (hw : ‖w‖ = 1) =>
    C1.N_tails P hm A hind hiso σ hσ1 w hw (hσv w hw)
  have htail := C1.step3 P hm A σ hσ1 (fun w hw => (hT w hw).1) (fun w hw => (hT w hw).2)
    x y hxy
  have hδ : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hNm : ∀ w : EuclideanSpace ℝ (Fin n), AEMeasurable (C1.Nw A w) P := by
    intro w
    have h := Finset.aemeasurable_sum (μ := P) Finset.univ fun i _ => (hiso i w).1.aemeasurable
    have h2 : AEMeasurable (fun ω => ∑ i, (inner (𝕜 := ℝ) (A i ω) w) ^ 2) P :=
      h.congr (ae_of_all _ fun ω => by simp [Finset.sum_apply])
    exact h2.sqrt
  have hmeas : AEMeasurable (fun ω => C1.Xp A x ω - C1.Xp A y ω) P :=
    ((hNm x).sub_const _).sub ((hNm y).sub_const _)
  have hpsi := C1.psi_of_tail P _ hmeas (48600 * σ ^ 4 * ‖x - y‖ ^ 2) (by positivity) htail
  refine hpsi.trans (ENNReal.ofReal_le_ofReal ?_)
  have hC : 12 * (48600 * σ ^ 4 * ‖x - y‖ ^ 2) ≤ (3100 * (K:ℝ) ^ 2 * ‖x - y‖) ^ 2 := by
    rw [hσdef]
    ring_nf
    nlinarith [mul_nonneg (pow_nonneg hK0 4) (sq_nonneg ‖x - y‖)]
  calc Real.sqrt (12 * (48600 * σ ^ 4 * ‖x - y‖ ^ 2))
      ≤ Real.sqrt ((3100 * (K:ℝ) ^ 2 * ‖x - y‖) ^ 2) := Real.sqrt_le_sqrt hC
    _ = 3100 * (K:ℝ) ^ 2 * ‖x - y‖ := Real.sqrt_sq (by positivity)

end SecC1

section SecC2


open MeasureTheory
open scoped ENNReal NNReal

namespace MDI

lemma pw (x L : ℝ) (hx : 0 ≤ x) (hL : 0 ≤ L) :
    x ≤ Real.sqrt L + 1 + Real.exp (x ^ 2 - L) := by
  by_cases h : x ≤ Real.sqrt L + 1
  · linarith [Real.exp_pos (x ^ 2 - L)]
  · push Not at h
    have hs := Real.sq_sqrt hL
    have hs0 := Real.sqrt_nonneg L
    have hm : 0 ≤ (x - Real.sqrt L) * (x + Real.sqrt L - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have h1 : x - Real.sqrt L ≤ x ^ 2 - L := by linarith
    have h2 := Real.add_one_le_exp (x ^ 2 - L)
    linarith

/-- admissibility at any level above the ψ₂ norm (no integrability of `Y` needed). -/
lemma adm2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℝ) (u : ℝ)
    (h : HighDimProb.Concentration.subgaussianNorm P Y < ENNReal.ofReal u) :
    Integrable (fun ω => Real.exp ((Y ω) ^ 2 / u ^ 2)) P ∧
      ∫ ω, Real.exp ((Y ω) ^ 2 / u ^ 2) ∂P ≤ 2 := by
  unfold HighDimProb.Concentration.subgaussianNorm at h
  simp only [iInf_lt_iff] at h
  obtain ⟨t, ht, hi, hle, hlt⟩ := h
  have htu : t < u := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).1 hlt
  have ht0 : t ≠ 0 := ht.ne'
  have hpt : ∀ ω, Real.exp ((Y ω) ^ 2 / u ^ 2) ≤ Real.exp ((Y ω) ^ 2 / t ^ 2) := by
    intro ω
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact pow_le_pow_left₀ ht.le htu.le 2
  have heq : (fun ω => Real.exp ((Y ω) ^ 2 / u ^ 2)) =
      (fun x => Real.exp (t ^ 2 * Real.log x / u ^ 2)) ∘
        (fun ω => Real.exp ((Y ω) ^ 2 / t ^ 2)) := by
    funext ω
    simp only [Function.comp, Real.log_exp]
    congr 1
    field_simp
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp ((Y ω) ^ 2 / u ^ 2)) P := by
    rw [heq]
    exact ((Real.measurable_exp.comp ((measurable_const.mul Real.measurable_log).div_const _)).comp_aemeasurable
      hi.aemeasurable).aestronglyMeasurable
  have hI : Integrable (fun ω => Real.exp ((Y ω) ^ 2 / u ^ 2)) P := by
    refine hi.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpt ω
  exact ⟨hI, (integral_mono hI hi hpt).trans hle⟩

lemma pair_bound (y d u S L : ℝ) (hu : 0 < u) (hd : 0 ≤ d) (hdS : d ≤ S) (hL : 0 ≤ L)
    (hy : d = 0 → y = 0) :
    |y| ≤ u * (Real.sqrt L + 1) * d + u * S * (Real.exp (-L) * Real.exp (y ^ 2 / (u * d) ^ 2)) := by
  rcases hd.eq_or_lt with h0 | hpos
  · have hS : 0 ≤ S := h0 ▸ hdS
    rw [hy h0.symm, abs_zero, ← h0]
    exact add_nonneg (by simp) (mul_nonneg (mul_nonneg hu.le hS) (by positivity))
  · have hud : 0 < u * d := mul_pos hu hpos
    have hx := pw (|y| / (u * d)) L (by positivity) hL
    have hsq : (|y| / (u * d)) ^ 2 = y ^ 2 / (u * d) ^ 2 := by rw [div_pow, sq_abs]
    have hE : Real.exp (y ^ 2 / (u * d) ^ 2 - L) =
        Real.exp (-L) * Real.exp (y ^ 2 / (u * d) ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsq, hE] at hx
    have hEnn : 0 ≤ Real.exp (-L) * Real.exp (y ^ 2 / (u * d) ^ 2) := by positivity
    have h1 : |y| = u * d * (|y| / (u * d)) := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hx hud.le
    have h3 := mul_le_mul_of_nonneg_left hdS (mul_nonneg hu.le hEnn)
    nlinarith

lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

/-- C2: chaining along maps `π n` with `card (range π n) ≤ 2^(2^n)` (generic chaining, upper bound). -/
theorem chaining_maps {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : Type} [MetricSpace T] [Fintype T] [DecidableEq T] (X : T → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hX : ∀ s t, HighDimProb.Concentration.subgaussianNorm P (fun ω => X s ω - X t ω) ≤
        ENNReal.ofReal (K * dist s t))
    (t0 : T) (π : ℕ → T → T) (hπ0 : ∀ t, π 0 t = t0)
    (hcard : ∀ n, (Finset.univ.image (π n)).card ≤ 2 ^ 2 ^ n)
    (hstab : ∀ t, ∃ N, ∀ k, N ≤ k → π k t = t) (S : ℝ)
    (hS : ∀ t N, ∑ k ∈ Finset.range N, Real.sqrt (2 ^ k) * dist (π k t) (π (k + 1) t) ≤ S) :
    ∫ ω, Finset.univ.sup' ⟨t0, Finset.mem_univ _⟩ (fun t => |X t ω - X t0 ω|) ∂P ≤ 5 * K * S := by
  have hS0 : 0 ≤ S := by simpa using hS t0 0
  have hsq1 : ∀ k : ℕ, 1 ≤ Real.sqrt ((2 : ℝ) ^ k) := fun k => by
    rw [Real.one_le_sqrt]; exact one_le_pow₀ (by norm_num)
  have hdS : ∀ t k, dist (π k t) (π (k + 1) t) ≤ S := by
    intro t k
    have h := hS t (k + 1)
    rw [Finset.sum_range_succ] at h
    have h0 : 0 ≤ ∑ j ∈ Finset.range k, Real.sqrt (2 ^ j) * dist (π j t) (π (j + 1) t) :=
      Finset.sum_nonneg (fun j _ => by positivity)
    have h1 := hsq1 k
    have h2 := dist_nonneg (x := π k t) (y := π (k + 1) t)
    linarith [mul_le_mul_of_nonneg_right h1 h2]
  have hs3 : Real.sqrt 3 ≤ 2 := by
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]; exact Real.sqrt_le_sqrt (by norm_num)
  have hs30 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hlin : ∀ t N, ∑ k ∈ Finset.range N,
      (Real.sqrt 3 * Real.sqrt (2 ^ k) + 1) * dist (π k t) (π (k + 1) t) ≤ (Real.sqrt 3 + 1) * S := by
    intro t N
    have h1 := hS t N
    have h2 : ∑ k ∈ Finset.range N, dist (π k t) (π (k + 1) t) ≤
        ∑ k ∈ Finset.range N, Real.sqrt (2 ^ k) * dist (π k t) (π (k + 1) t) :=
      Finset.sum_le_sum (fun k _ => le_mul_of_one_le_left dist_nonneg (hsq1 k))
    have h3 : ∑ k ∈ Finset.range N,
        (Real.sqrt 3 * Real.sqrt (2 ^ k) + 1) * dist (π k t) (π (k + 1) t) =
        Real.sqrt 3 * ∑ k ∈ Finset.range N, Real.sqrt (2 ^ k) * dist (π k t) (π (k + 1) t) +
          ∑ k ∈ Finset.range N, dist (π k t) (π (k + 1) t) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _; ring
    rw [h3]; nlinarith
  choose Nf hNf using hstab
  set N0 := Finset.univ.sup Nf with hN0
  have hπN : ∀ t, π N0 t = t := fun t => hNf t N0 (Finset.le_sup (Finset.mem_univ t))
  have hw : ∀ k : ℕ, Real.exp (-(3 * (2 : ℝ) ^ k)) * (2 : ℝ) ^ (3 * 2 ^ k) ≤ (1 / 2) ^ (k + 1) := by
    intro k
    have h1 : Real.exp (-(3 * (2 : ℝ) ^ k)) = Real.exp (-3) ^ (2 ^ k) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h2 : (2 : ℝ) ^ (3 * 2 ^ k) = 8 ^ (2 ^ k) := by rw [pow_mul]; norm_num
    rw [h1, h2, ← mul_pow]
    have h16 : (16 : ℝ) ≤ Real.exp 3 := by
      have h := Real.exp_one_gt_d9
      have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      have he : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
      have h3 := pow_le_pow_left₀ (by norm_num) he 3
      norm_num at h3 ⊢; linarith
    have h8 : Real.exp (-3) * 8 ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos 3)]; linarith
    calc (Real.exp (-3) * 8) ^ (2 ^ k) ≤ (1 / 2 : ℝ) ^ (2 ^ k) :=
          pow_le_pow_left₀ (by positivity) h8 _
      _ ≤ (1 / 2 : ℝ) ^ (k + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (succ_le_two_pow k)
  have hgeo : ∀ N, ∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ (k + 1) ≤ 1 := by
    have h : ∀ N, ∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ (k + 1) + (1 / 2) ^ N = 1 := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ]
        have : ((1 : ℝ) / 2) ^ (N + 1) + (1 / 2) ^ (N + 1) = (1 / 2) ^ N := by ring
        linarith
    intro N; have := h N; have : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
    linarith
  have key : ∀ u, K < u →
      ∫ ω, Finset.univ.sup' ⟨t0, Finset.mem_univ _⟩ (fun t => |X t ω - X t0 ω|) ∂P ≤ 5 * u * S := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt hK hu
    let g : T × T → Ω → ℝ := fun p ω =>
      Real.exp ((X p.2 ω - X p.1 ω) ^ 2 / (u * dist p.1 p.2) ^ 2)
    have hg : ∀ p, Integrable (g p) P ∧ ∫ ω, g p ω ∂P ≤ 2 := by
      intro p
      by_cases hd : dist p.1 p.2 = 0
      · have he : p.1 = p.2 := dist_eq_zero.mp hd
        have : g p = fun _ => 1 := by funext ω; simp [g, he]
        rw [this]; refine ⟨integrable_const _, ?_⟩; simp
      · have hdp : 0 < dist p.1 p.2 := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
        have hlt : HighDimProb.Concentration.subgaussianNorm P (fun ω => X p.2 ω - X p.1 ω) <
            ENNReal.ofReal (u * dist p.1 p.2) := by
          refine lt_of_le_of_lt (hX p.2 p.1) ?_
          rw [ENNReal.ofReal_lt_ofReal_iff (mul_pos hu0 hdp), dist_comm]
          exact mul_lt_mul_of_pos_right hu hdp
        exact adm2 P _ _ hlt
    let Pk : ℕ → Finset (T × T) := fun k => Finset.univ.image (fun t => (π k t, π (k + 1) t))
    let G : ℕ → Ω → ℝ := fun k ω => ∑ p ∈ Pk k, g p ω
    let w : ℕ → ℝ := fun k => Real.exp (-(3 * (2 : ℝ) ^ k))
    have hGi : ∀ k, Integrable (G k) P := fun k => integrable_finsetSum _ (fun p _ => (hg p).1)
    have hGint : ∀ k, ∫ ω, G k ω ∂P ≤ 2 * (2 : ℝ) ^ (3 * 2 ^ k) := by
      intro k
      have hc : ((Pk k).card : ℝ) ≤ (2 : ℝ) ^ (3 * 2 ^ k) := by
        have h1 : Pk k ⊆ (Finset.univ.image (π k)) ×ˢ (Finset.univ.image (π (k + 1))) := by
          intro x hx
          obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ t),
            Finset.mem_image_of_mem _ (Finset.mem_univ t)⟩
        have h2 : (Pk k).card ≤ 2 ^ (3 * 2 ^ k) := by
          calc (Pk k).card ≤ _ := Finset.card_le_card h1
            _ = _ := Finset.card_product _ _
            _ ≤ 2 ^ 2 ^ k * 2 ^ 2 ^ (k + 1) := Nat.mul_le_mul (hcard k) (hcard (k + 1))
            _ = 2 ^ (3 * 2 ^ k) := by rw [← pow_add]; congr 1; rw [pow_succ]; ring
        exact_mod_cast h2
      calc ∫ ω, G k ω ∂P = ∑ p ∈ Pk k, ∫ ω, g p ω ∂P :=
            integral_finsetSum _ (fun p _ => (hg p).1)
        _ ≤ ∑ p ∈ Pk k, (2 : ℝ) := Finset.sum_le_sum (fun p _ => (hg p).2)
        _ = 2 * (Pk k).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ 2 * (2 : ℝ) ^ (3 * 2 ^ k) := by linarith
    have hsi : Integrable (fun ω => ∑ k ∈ Finset.range N0, w k * G k ω) P :=
      integrable_finsetSum _ (fun k _ => (hGi k).const_mul (w k))
    let R : Ω → ℝ := fun ω =>
      u * ((Real.sqrt 3 + 1) * S) + u * S * ∑ k ∈ Finset.range N0, w k * G k ω
    have hRi : Integrable R P := (integrable_const _).add (hsi.const_mul (u * S))
    have hpt : ∀ ω, Finset.univ.sup' ⟨t0, Finset.mem_univ _⟩ (fun t => |X t ω - X t0 ω|) ≤ R ω := by
      intro ω
      apply Finset.sup'_le
      intro t _
      have htel := Finset.sum_range_sub (fun k => X (π k t) ω) N0
      simp only [hπN, hπ0] at htel
      have hterm : ∀ k ∈ Finset.range N0, |X (π (k + 1) t) ω - X (π k t) ω| ≤
          u * (Real.sqrt 3 * Real.sqrt (2 ^ k) + 1) * dist (π k t) (π (k + 1) t) +
            u * S * (w k * G k ω) := by
        intro k _
        have hb := pair_bound (X (π (k + 1) t) ω - X (π k t) ω) (dist (π k t) (π (k + 1) t)) u S
          (3 * 2 ^ k) hu0 dist_nonneg (hdS t k) (by positivity)
          (fun h => by rw [dist_eq_zero.mp h, sub_self])
        have hL : Real.sqrt (3 * 2 ^ k) = Real.sqrt 3 * Real.sqrt (2 ^ k) :=
          Real.sqrt_mul (by norm_num) _
        rw [hL] at hb
        have hgle : Real.exp ((X (π (k + 1) t) ω - X (π k t) ω) ^ 2 /
            (u * dist (π k t) (π (k + 1) t)) ^ 2) ≤ G k ω :=
          Finset.single_le_sum (f := fun p => g p ω) (fun p _ => (Real.exp_pos _).le)
            (Finset.mem_image_of_mem (fun t => (π k t, π (k + 1) t)) (Finset.mem_univ t))
        have hw0 : 0 ≤ w k := (Real.exp_pos _).le
        have h4 : u * S * (Real.exp (-(3 * 2 ^ k)) * Real.exp ((X (π (k + 1) t) ω - X (π k t) ω) ^ 2 /
            (u * dist (π k t) (π (k + 1) t)) ^ 2)) ≤ u * S * (w k * G k ω) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgle hw0) (mul_nonneg hu0.le hS0)
        linarith
      calc |X t ω - X t0 ω| = |∑ k ∈ Finset.range N0, (X (π (k + 1) t) ω - X (π k t) ω)| := by
            rw [htel]
        _ ≤ ∑ k ∈ Finset.range N0, |X (π (k + 1) t) ω - X (π k t) ω| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range N0, (u * (Real.sqrt 3 * Real.sqrt (2 ^ k) + 1) *
              dist (π k t) (π (k + 1) t) + u * S * (w k * G k ω)) := Finset.sum_le_sum hterm
        _ = u * ∑ k ∈ Finset.range N0, (Real.sqrt 3 * Real.sqrt (2 ^ k) + 1) *
              dist (π k t) (π (k + 1) t) + u * S * ∑ k ∈ Finset.range N0, w k * G k ω := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
            congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring
        _ ≤ R ω := by
            have h2 := mul_le_mul_of_nonneg_left (hlin t N0) hu0.le
            simp only [R]; linarith
    have hIR : ∫ ω, R ω ∂P = u * ((Real.sqrt 3 + 1) * S) +
        u * S * ∑ k ∈ Finset.range N0, w k * ∫ ω, G k ω ∂P := by
      simp only [R]
      rw [integral_add (integrable_const _) (hsi.const_mul _), integral_const, integral_const_mul,
        integral_finsetSum _ (fun k _ => (hGi k).const_mul (w k))]
      simp [integral_const_mul]
    have hsumw : ∑ k ∈ Finset.range N0, w k * ∫ ω, G k ω ∂P ≤ 2 := by
      calc _ ≤ ∑ k ∈ Finset.range N0, 2 * ((1 : ℝ) / 2) ^ (k + 1) :=
            Finset.sum_le_sum (fun k _ => by
              have h1 := mul_le_mul_of_nonneg_left (hGint k) (Real.exp_pos (-(3 * (2 : ℝ) ^ k))).le
              have h2 := hw k
              simp only [w]; nlinarith)
        _ = 2 * ∑ k ∈ Finset.range N0, ((1 : ℝ) / 2) ^ (k + 1) := by rw [Finset.mul_sum]
        _ ≤ 2 := by linarith [hgeo N0]
    have hnn : ∀ ω, 0 ≤ Finset.univ.sup' ⟨t0, Finset.mem_univ _⟩ (fun t => |X t ω - X t0 ω|) :=
      fun ω => le_trans (abs_nonneg _) (Finset.le_sup' (fun t => |X t ω - X t0 ω|) (Finset.mem_univ t0))
    calc _ ≤ ∫ ω, R ω ∂P := integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hRi
          (Filter.Eventually.of_forall hpt)
      _ ≤ 5 * u * S := by
          rw [hIR]
          have h1 := mul_le_mul_of_nonneg_left hsumw (mul_nonneg hu0.le hS0)
          have h2 : u * ((Real.sqrt 3 + 1) * S) ≤ u * (3 * S) :=
            mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_right hs3 hS0]) hu0.le
          linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have h5 : (0 : ℝ) < 5 * S + 1 := by linarith
  have hδ : 0 < ε / (5 * S + 1) := div_pos hε h5
  have hk := key (K + ε / (5 * S + 1)) (by linarith)
  have h2 : 5 * S * (ε / (5 * S + 1)) ≤ ε := by
    rw [mul_div_assoc', div_le_iff₀ h5]; linarith
  linarith

end MDI

end SecC2

section SecC4


namespace MDI

/-- Abstract bookkeeping for the partitioning scheme: a three-stage pipeline `F ≥ Lp ≥ L ≥ 0` with
ball steps (`τ` shrinks by `q ≤ 1/2`, `F → Lp → L` shift) and stay steps (`τ` grows by `√2`, `L`
drops to `F - e τ`).  Potential `V = D (F + Lp - min (F - L) (κ τ)) + 2 τ`, `κ = e/√2`, `D = 5/κ`. -/
theorem chain_sum_le (F Lp L τ : ℕ → ℝ) (q e : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (he : 0 < e)
    (hL0 : ∀ k, 0 ≤ L k) (hLLp : ∀ k, L k ≤ Lp k) (hLpF : ∀ k, Lp k ≤ F k) (hτ : ∀ k, 0 < τ k)
    (hstep : ∀ k, (τ (k + 1) = q * τ k ∧ F (k + 1) ≤ Lp k ∧ Lp (k + 1) ≤ L k) ∨
      (τ (k + 1) = Real.sqrt 2 * τ k ∧ F (k + 1) ≤ F k ∧ Lp (k + 1) ≤ Lp k ∧
        L (k + 1) ≤ F k - e * τ k)) :
    ∀ N, ∑ k ∈ Finset.range N, τ k ≤ (10 * Real.sqrt 2 / e) * F 0 + 2 * τ 0 := by
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs43 : 4 / 3 ≤ Real.sqrt 2 := by
    by_contra hc
    have hc' := not_le.mp hc
    have := mul_lt_mul'' hc' hc' hs0.le hs0.le
    linarith
  set κ : ℝ := e / Real.sqrt 2 with hκ
  have hκ0 : 0 < κ := div_pos he hs0
  have hκe : κ * Real.sqrt 2 = e := by rw [hκ]; field_simp
  set D : ℝ := 5 / κ with hD
  have hD0 : 0 < D := div_pos (by norm_num) hκ0
  have hDκ : D * κ = 5 := by rw [hD]; field_simp
  let W : ℕ → ℝ := fun k => F k + Lp k - min (F k - L k) (κ * τ k)
  let V : ℕ → ℝ := fun k => D * W k + 2 * τ k
  have hW0 : ∀ k, 0 ≤ W k := by
    intro k
    have := min_le_left (F k - L k) (κ * τ k)
    have := hL0 k; have := hLLp k
    simp only [W]; linarith
  have hstepV : ∀ k, V (k + 1) + τ k ≤ V k := by
    intro k
    have hτk := hτ k
    rcases hstep k with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩
    · -- ball step
      have hm1 : 0 ≤ min (F (k + 1) - L (k + 1)) (κ * τ (k + 1)) := by
        apply le_min
        · linarith [hLLp (k + 1), hLpF (k + 1)]
        · rw [h1]; positivity
      have hm2 := min_le_left (F k - L k) (κ * τ k)
      have hWW : W (k + 1) ≤ W k := by
        simp only [W]; linarith [hLLp k]
      have hDW : D * W (k + 1) ≤ D * W k := mul_le_mul_of_nonneg_left hWW hD0.le
      have hqτ : 2 * (q * τ k) ≤ τ k := by
        have := mul_le_mul_of_nonneg_right hq hτk.le
        linarith
      simp only [V]; rw [h1]; linarith
    · -- stay step
      have hLk1 : L (k + 1) ≤ F k - κ * Real.sqrt 2 * τ k := by rw [hκe]; exact h4
      have hm1 : κ * τ k * Real.sqrt 2 + (F k - F (k + 1)) ≤
          min (F (k + 1) - L (k + 1)) (κ * τ (k + 1)) + (F k - F (k + 1)) +
            (F k - F (k + 1)) := by
        rw [h1]
        rcases le_total (F (k + 1) - L (k + 1)) (κ * (Real.sqrt 2 * τ k)) with hc | hc
        · rw [min_eq_left hc]; linarith
        · rw [min_eq_right hc]; linarith
      have hm2 := min_le_right (F k - L k) (κ * τ k)
      have hWW : κ * τ k * (Real.sqrt 2 - 1) ≤ W k - W (k + 1) := by
        simp only [W]; linarith
      have hDW : D * (κ * τ k * (Real.sqrt 2 - 1)) ≤ D * (W k - W (k + 1)) :=
        mul_le_mul_of_nonneg_left hWW hD0.le
      have hDW' : D * (κ * τ k * (Real.sqrt 2 - 1)) = 5 * τ k * (Real.sqrt 2 - 1) := by
        rw [← hDκ]; ring
      have hfin : 2 * (Real.sqrt 2 * τ k) + τ k ≤ 2 * τ k + 5 * τ k * (Real.sqrt 2 - 1) := by
        linarith [mul_le_mul_of_nonneg_right hs43 hτk.le]
      simp only [V] at *; rw [h1]; linarith
  have hsum : ∀ N, ∑ k ∈ Finset.range N, τ k + V N ≤ V 0 := by
    intro N
    induction N with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; linarith [hstepV n]
  intro N
  have hVN : 0 ≤ V N := by
    have := hW0 N; have := hτ N
    simp only [V]; positivity
  have hV0 : V 0 ≤ (10 * Real.sqrt 2 / e) * F 0 + 2 * τ 0 := by
    have hm : 0 ≤ min (F 0 - L 0) (κ * τ 0) := le_min (by linarith [hLLp 0, hLpF 0])
      (by have := hτ 0; positivity)
    have hW : W 0 ≤ 2 * F 0 := by simp only [W]; linarith [hLpF 0]
    have hDW : D * W 0 ≤ D * (2 * F 0) := mul_le_mul_of_nonneg_left hW hD0.le
    have hDe : D * 2 = 10 * Real.sqrt 2 / e := by
      rw [hD, hκ]; field_simp; ring
    have hDF : D * (2 * F 0) = 10 * Real.sqrt 2 / e * F 0 := by rw [← hDe]; ring
    simp only [V]
    linarith
  linarith [hsum N]

section Greedy

variable {T : Type} [MetricSpace T] [Fintype T] [DecidableEq T] [Nonempty T]

/-- `X ∩ closedBall(u, ρ)` as a finset. -/
noncomputable def cb (X : Finset T) (u : T) (ρ : ℝ) : Finset T := X.filter (fun s => dist s u ≤ ρ)

lemma cb_sub (X : Finset T) (u : T) (ρ : ℝ) : cb X u ρ ⊆ X := Finset.filter_subset _ _

lemma mem_cb {X : Finset T} {u s : T} {ρ : ℝ} : s ∈ cb X u ρ ↔ s ∈ X ∧ dist s u ≤ ρ :=
  Finset.mem_filter

lemma cb_mono {X Y : Finset T} (h : X ⊆ Y) (u : T) {ρ ρ' : ℝ} (hρ : ρ ≤ ρ') : cb X u ρ ⊆ cb Y u ρ' := by
  intro s hs; rw [mem_cb] at hs ⊢; exact ⟨h hs.1, hs.2.trans hρ⟩

lemma self_mem_cb {X : Finset T} {u : T} {ρ : ℝ} (hu : u ∈ X) (hρ : 0 ≤ ρ) : u ∈ cb X u ρ := by
  rw [mem_cb]; exact ⟨hu, by simpa using hρ⟩

/-- greedy center: maximiser of `u ↦ F (X ∩ B(u, ρ))` over `X`. -/
noncomputable def ctr0 (F : Finset T → ℝ) (ρ : ℝ) (X : Finset T) : T :=
  if h : X.Nonempty then Classical.choose (Finset.exists_max_image X (fun u => F (cb X u ρ)) h)
  else Classical.arbitrary T

lemma ctr0_spec (F : Finset T → ℝ) (ρ : ℝ) {X : Finset T} (h : X.Nonempty) :
    ctr0 F ρ X ∈ X ∧ ∀ u ∈ X, F (cb X u ρ) ≤ F (cb X (ctr0 F ρ X) ρ) := by
  have := Classical.choose_spec (Finset.exists_max_image X (fun u => F (cb X u ρ)) h)
  simp only [ctr0, dif_pos h]; exact this

/-- one greedy removal. -/
noncomputable def gstep (F : Finset T → ℝ) (R r : ℝ) (X : Finset T) : Finset T :=
  X \ cb X (ctr0 F (R / r / r) X) (R / r)

noncomputable def rem (F : Finset T → ℝ) (R r : ℝ) (C : Finset T) (l : ℕ) : Finset T :=
  (gstep F R r)^[l] C

noncomputable def ctr (F : Finset T → ℝ) (R r : ℝ) (C : Finset T) (l : ℕ) : T :=
  ctr0 F (R / r / r) (rem F R r C l)

noncomputable def piece (F : Finset T → ℝ) (R r : ℝ) (C : Finset T) (l : ℕ) : Finset T :=
  cb (rem F R r C l) (ctr F R r C l) (R / r)

variable (F : Finset T → ℝ) (R r : ℝ) (C : Finset T)

lemma rem_zero : rem F R r C 0 = C := rfl

lemma rem_succ (l : ℕ) : rem F R r C (l + 1) = rem F R r C l \ piece F R r C l := by
  simp only [rem, piece, ctr, Function.iterate_succ_apply', gstep]

lemma rem_succ_sub (l : ℕ) : rem F R r C (l + 1) ⊆ rem F R r C l := by
  rw [rem_succ]; exact Finset.sdiff_subset

lemma rem_anti {l l' : ℕ} (h : l ≤ l') : rem F R r C l' ⊆ rem F R r C l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (rem_succ_sub F R r C _).trans ih

lemma rem_sub (l : ℕ) : rem F R r C l ⊆ C := rem_anti F R r C (Nat.zero_le l)

lemma piece_sub (l : ℕ) : piece F R r C l ⊆ rem F R r C l := cb_sub _ _ _

lemma not_mem_piece_of_mem_rem {l l' : ℕ} (h : l < l') {s : T} (hs : s ∈ rem F R r C l') :
    s ∉ piece F R r C l := by
  have h1 := rem_anti F R r C (Nat.succ_le_of_lt h) hs
  rw [rem_succ, Finset.mem_sdiff] at h1; exact h1.2

lemma piece_unique {l l' : ℕ} {s : T} (h : s ∈ piece F R r C l) (h' : s ∈ piece F R r C l') :
    l = l' := by
  rcases lt_trichotomy l l' with hl | hl | hl
  · exact absurd h (not_mem_piece_of_mem_rem F R r C hl (piece_sub F R r C l' h'))
  · exact hl
  · exact absurd h' (not_mem_piece_of_mem_rem F R r C hl (piece_sub F R r C l h))

lemma mem_piece_or_rem {s : T} (hs : s ∈ C) (M : ℕ) :
    (∃ l < M, s ∈ piece F R r C l) ∨ s ∈ rem F R r C M := by
  induction M with
  | zero => right; exact hs
  | succ M ih =>
    rcases ih with ⟨l, hl, h⟩ | h
    · left; exact ⟨l, Nat.lt_succ_of_lt hl, h⟩
    · by_cases hp : s ∈ piece F R r C M
      · left; exact ⟨M, Nat.lt_succ_self M, hp⟩
      · right; rw [rem_succ, Finset.mem_sdiff]; exact ⟨h, hp⟩

end Greedy

section Scheme

variable {T : Type} [MetricSpace T] [Fintype T] [DecidableEq T] [Nonempty T]

open Classical in
/-- split the cell `σ.1` (radius `σ.2`) with `M` greedy balls; the point `t` goes to its piece. -/
noncomputable def nxt (F : Finset T → ℝ) (r : ℝ) (M : ℕ) (σ : Finset T × ℝ) (t : T) :
    Finset T × ℝ :=
  if h : ∃ l, l < M ∧ t ∈ piece F σ.2 r σ.1 l then (piece F σ.2 r σ.1 (Nat.find h), σ.2 / r)
  else (rem F σ.2 r σ.1 M, σ.2)

/-- the state (cell of `t`, radius) at level `k`. -/
noncomputable def st (F : Finset T → ℝ) (r R0 : ℝ) : ℕ → T → Finset T × ℝ
  | 0 => fun _ => (Finset.univ, R0)
  | k + 1 => fun t => nxt F r (2 ^ 2 ^ k - 1) (st F r R0 k t) t

variable (F : Finset T → ℝ) (r : ℝ)

lemma nxt_cases (M : ℕ) (σ : Finset T × ℝ) {t : T} (ht : t ∈ σ.1) :
    (∃ l < M, nxt F r M σ t = (piece F σ.2 r σ.1 l, σ.2 / r) ∧ t ∈ piece F σ.2 r σ.1 l) ∨
    (nxt F r M σ t = (rem F σ.2 r σ.1 M, σ.2) ∧ t ∈ rem F σ.2 r σ.1 M ∧
      ∀ l < M, t ∉ piece F σ.2 r σ.1 l) := by
  classical
  by_cases h : ∃ l, l < M ∧ t ∈ piece F σ.2 r σ.1 l
  · left
    refine ⟨Nat.find h, (Nat.find_spec h).1, ?_, (Nat.find_spec h).2⟩
    simp only [nxt, dif_pos h]
  · right
    have h' : ∀ l < M, t ∉ piece F σ.2 r σ.1 l := fun l hl hm => h ⟨l, hl, hm⟩
    refine ⟨by simp only [nxt, dif_neg h], ?_, h'⟩
    rcases mem_piece_or_rem F σ.2 r σ.1 ht M with ⟨l, hl, hm⟩ | hm
    · exact absurd hm (h' l hl)
    · exact hm

lemma nxt_sub (M : ℕ) (σ : Finset T × ℝ) {t : T} (ht : t ∈ σ.1) : (nxt F r M σ t).1 ⊆ σ.1 := by
  rcases nxt_cases F r M σ ht with ⟨l, -, he, -⟩ | ⟨he, -, -⟩ <;> rw [he]
  · exact (piece_sub F σ.2 r σ.1 l).trans (rem_sub F σ.2 r σ.1 l)
  · exact rem_sub F σ.2 r σ.1 M

lemma nxt_mem (M : ℕ) (σ : Finset T × ℝ) {t : T} (ht : t ∈ σ.1) : t ∈ (nxt F r M σ t).1 := by
  rcases nxt_cases F r M σ ht with ⟨l, -, he, hm⟩ | ⟨he, hm, -⟩ <;> rw [he] <;> exact hm

lemma nxt_cons (M : ℕ) (σ : Finset T × ℝ) {t s : T} (ht : t ∈ σ.1) (hs : s ∈ (nxt F r M σ t).1) :
    nxt F r M σ s = nxt F r M σ t := by
  have hs1 := nxt_sub F r M σ ht hs
  rcases nxt_cases F r M σ ht with ⟨l, hl, he, -⟩ | ⟨he, -, -⟩
  · rw [he] at hs
    rcases nxt_cases F r M σ hs1 with ⟨l', -, he', hm'⟩ | ⟨-, -, hn⟩
    · rw [he', he, piece_unique F σ.2 r σ.1 hm' hs]
    · exact absurd hs (hn l hl)
  · rw [he] at hs
    rcases nxt_cases F r M σ hs1 with ⟨l', hl', -, hm'⟩ | ⟨he', -, -⟩
    · exact absurd hm' (not_mem_piece_of_mem_rem F σ.2 r σ.1 hl' hs)
    · rw [he', he]

lemma nxt_range (M : ℕ) (σ : Finset T × ℝ) (t : T) :
    nxt F r M σ t ∈ (Finset.range M).image (fun l => (piece F σ.2 r σ.1 l, σ.2 / r)) ∪
      {(rem F σ.2 r σ.1 M, σ.2)} := by
  classical
  unfold nxt
  split_ifs with h
  · apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨Nat.find h, Finset.mem_range.mpr (Nat.find_spec h).1, rfl⟩
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

variable (R0 : ℝ)

lemma st_succ (k : ℕ) (t : T) : st F r R0 (k + 1) t = nxt F r (2 ^ 2 ^ k - 1) (st F r R0 k t) t := rfl

lemma st_mem (k : ℕ) (t : T) : t ∈ (st F r R0 k t).1 := by
  induction k with
  | zero => exact Finset.mem_univ t
  | succ k ih => rw [st_succ]; exact nxt_mem F r _ _ ih

lemma st_sub (k : ℕ) (t : T) : (st F r R0 (k + 1) t).1 ⊆ (st F r R0 k t).1 := by
  rw [st_succ]; exact nxt_sub F r _ _ (st_mem F r R0 k t)

lemma st_cons (k : ℕ) : ∀ t s, s ∈ (st F r R0 k t).1 → st F r R0 k s = st F r R0 k t := by
  induction k with
  | zero => intro t s _; rfl
  | succ k ih =>
    intro t s hs
    have h1 : st F r R0 k s = st F r R0 k t := ih t s (st_sub F r R0 k t hs)
    rw [st_succ, st_succ, h1]
    rw [st_succ] at hs
    exact nxt_cons F r _ _ (st_mem F r R0 k t) hs

lemma st_card (k : ℕ) : (Finset.univ.image (st F r R0 k)).card ≤ 2 ^ 2 ^ k := by
  induction k with
  | zero =>
    have : Finset.univ.image (st F r R0 0) ⊆ {((Finset.univ : Finset T), R0)} := by
      intro x hx; obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx; exact Finset.mem_singleton_self _
    exact (Finset.card_le_card this).trans (by simp)
  | succ k ih =>
    set M := 2 ^ 2 ^ k - 1
    have hM : M + 1 = 2 ^ 2 ^ k := Nat.sub_add_cancel Nat.one_le_two_pow
    have hsub : Finset.univ.image (st F r R0 (k + 1)) ⊆ (Finset.univ.image (st F r R0 k)).biUnion
        (fun σ => (Finset.range M).image (fun l => (piece F σ.2 r σ.1 l, σ.2 / r)) ∪
          {(rem F σ.2 r σ.1 M, σ.2)}) := by
      intro x hx
      obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_biUnion.mpr ⟨st F r R0 k t, Finset.mem_image_of_mem _ (Finset.mem_univ t),
        nxt_range F r M _ t⟩
    have hc : ∀ σ : Finset T × ℝ, ((Finset.range M).image (fun l => (piece F σ.2 r σ.1 l, σ.2 / r)) ∪
          {(rem F σ.2 r σ.1 M, σ.2)}).card ≤ 2 ^ 2 ^ k := by
      intro σ
      refine (Finset.card_union_le _ _).trans ?_
      rw [Finset.card_singleton, ← hM]
      exact Nat.add_le_add_right ((Finset.card_image_le).trans (Finset.card_range M).le) 1
    calc (Finset.univ.image (st F r R0 (k + 1))).card
        ≤ _ := Finset.card_le_card hsub
      _ ≤ (Finset.univ.image (st F r R0 k)).card * 2 ^ 2 ^ k :=
          Finset.card_biUnion_le_card_mul _ _ _ (fun σ _ => hc σ)
      _ ≤ 2 ^ 2 ^ k * 2 ^ 2 ^ k := Nat.mul_le_mul_right _ ih
      _ = 2 ^ 2 ^ (k + 1) := by rw [← pow_add, pow_succ, mul_two]

lemma st_ctr (hR0 : ∀ s z : T, dist s z ≤ R0) (k : ℕ) (t : T) :
    ∃ z, ∀ s ∈ (st F r R0 k t).1, dist s z ≤ (st F r R0 k t).2 := by
  induction k with
  | zero => exact ⟨t, fun s _ => hR0 s t⟩
  | succ k ih =>
    obtain ⟨z, hz⟩ := ih
    rw [st_succ]
    rcases nxt_cases F r (2 ^ 2 ^ k - 1) (st F r R0 k t) (st_mem F r R0 k t) with
      ⟨l, -, he, -⟩ | ⟨he, -, -⟩ <;> rw [he]
    · exact ⟨_, fun s hs => (mem_cb.mp hs).2⟩
    · exact ⟨z, fun s hs => hz s (rem_sub F _ r _ _ hs)⟩

end Scheme

section Gain

variable {T : Type} [MetricSpace T] [Fintype T] [DecidableEq T] [Nonempty T]

/-- Talagrand's growth condition for a functional on finite subsets. -/
def Growth (F : Finset T → ℝ) (r c : ℝ) : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ (a : ℝ), 0 < a → ∀ (t : Fin m → T) (H : Fin m → Finset T),
    (∀ l l', l ≠ l' → a ≤ dist (t l) (t l')) →
    (∀ l, ∀ s ∈ H l, dist s (t l) ≤ a / r) → (∀ l, (H l).Nonempty) →
    ∃ l, c * a * Real.sqrt (Real.log m) + F (H l) ≤ F (Finset.univ.biUnion H)

variable (F : Finset T → ℝ) (r c : ℝ)

lemma ctr_sep (R : ℝ) (C : Finset T) {l l' M : ℕ} (hl : l < l') (hl' : l' ≤ M) {t : T}
    (ht : t ∈ rem F R r C M) : R / r < dist (ctr F R r C l') (ctr F R r C l) := by
  have hne : (rem F R r C l').Nonempty := ⟨t, rem_anti F R r C hl' ht⟩
  have hmem := (ctr0_spec F (R / r / r) hne).1
  have hn := not_mem_piece_of_mem_rem F R r C hl hmem
  have hin := rem_anti F R r C hl.le hmem
  by_contra hcon
  exact hn (mem_cb.mpr ⟨hin, not_lt.mp hcon⟩)

/-- The stay gain: after `M ≥ 2` greedy balls, every small ball of the remainder has `F` at least
`c (R/r) √(log M)` below `F` of the whole cell. -/
lemma stay_gain (hr : 1 ≤ r) (hmono : ∀ A B : Finset T, A ⊆ B → F A ≤ F B) (hG : Growth F r c)
    (R : ℝ) (hR : 0 < R) (C : Finset T) (M : ℕ) (hM : 2 ≤ M) {t : T}
    (ht : t ∈ rem F R r C M) :
    ∀ u ∈ rem F R r C M,
      c * (R / r) * Real.sqrt (Real.log M) + F (cb (rem F R r C M) u (R / r / r)) ≤ F C := by
  have hr0 : 0 < r := by linarith
  have ha : 0 < R / r := div_pos hR hr0
  have hne : ∀ l, l ≤ M → (rem F R r C l).Nonempty := fun l hl => ⟨t, rem_anti F R r C hl ht⟩
  let tt : Fin M → T := fun l => ctr F R r C l
  let H : Fin M → Finset T := fun l => cb (rem F R r C l) (ctr F R r C l) (R / r / r)
  have hsep : ∀ l l' : Fin M, l ≠ l' → R / r ≤ dist (tt l) (tt l') := by
    intro l l' hll
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hll) with h | h
    · rw [dist_comm]; exact (ctr_sep F r R C h l'.2.le ht).le
    · exact (ctr_sep F r R C h l.2.le ht).le
  have hball : ∀ l, ∀ s ∈ H l, dist s (tt l) ≤ R / r / r := fun l s hs => (mem_cb.mp hs).2
  have hHne : ∀ l, (H l).Nonempty := fun l =>
    ⟨_, self_mem_cb (ctr0_spec F (R / r / r) (hne l l.2.le)).1 (by positivity)⟩
  obtain ⟨l0, hl0⟩ := hG M hM (R / r) ha tt H hsep hball hHne
  have hU : F (Finset.univ.biUnion H) ≤ F C := by
    apply hmono
    intro s hs
    obtain ⟨l, -, hl⟩ := Finset.mem_biUnion.mp hs
    exact rem_sub F R r C l (cb_sub _ _ _ hl)
  intro u hu
  have hu0 : u ∈ rem F R r C l0 := rem_anti F R r C l0.2.le hu
  have h1 : F (cb (rem F R r C M) u (R / r / r)) ≤ F (cb (rem F R r C l0) u (R / r / r)) :=
    hmono _ _ (cb_mono (rem_anti F R r C l0.2.le) u le_rfl)
  have h2 := (ctr0_spec F (R / r / r) (hne l0 l0.2.le)).2 u hu0
  have h3 : F (cb (rem F R r C l0) (ctr0 F (R / r / r) (rem F R r C l0)) (R / r / r)) = F (H l0) := rfl
  linarith

end Gain

lemma sqrt_log_bound (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt (2 ^ k) / 2 ≤ Real.sqrt (Real.log ((2 ^ 2 ^ k - 1 : ℕ) : ℝ)) := by
  set n : ℕ := 2 ^ k with hn
  have hn2 : 2 ≤ n := by
    rw [hn]; calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hnat : 2 ^ (n - 1) ≤ 2 ^ n - 1 := by
    have h1 := Nat.one_le_two_pow (n := n - 1)
    have h2 : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    omega
  have hreal : (2 : ℝ) ^ (n - 1) ≤ ((2 ^ 2 ^ k - 1 : ℕ) : ℝ) := by
    rw [← hn]; exact_mod_cast hnat
  have hlog : ((n - 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log ((2 ^ 2 ^ k - 1 : ℕ) : ℝ) := by
    rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hreal
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hnk : (n : ℝ) = (2 : ℝ) ^ k := by rw [hn]; push_cast; ring
  have hl2 := Real.log_two_gt_d9
  have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hq : (2 : ℝ) ^ k / 4 ≤ Real.log ((2 ^ 2 ^ k - 1 : ℕ) : ℝ) := by
    rw [hcast] at hlog; rw [← hnk]
    linarith [mul_le_mul_of_nonneg_left hl2.le (by linarith : (0:ℝ) ≤ (n : ℝ) - 1)]
  have he : Real.sqrt (2 ^ k) / 2 = Real.sqrt ((2 : ℝ) ^ k / 4) := by
    rw [Real.sqrt_div (by positivity), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [he]; exact Real.sqrt_le_sqrt hq

section Chain

variable {T : Type} [MetricSpace T] [Fintype T] [DecidableEq T] [Nonempty T]
variable (F : Finset T → ℝ) (r c R0 : ℝ)

lemma st_R_pos (hr : 0 < r) (hR0 : 0 < R0) (k : ℕ) (t : T) : 0 < (st F r R0 k t).2 := by
  induction k with
  | zero => exact hR0
  | succ k ih =>
    rw [st_succ]
    rcases nxt_cases F r (2 ^ 2 ^ k - 1) (st F r R0 k t) (st_mem F r R0 k t) with
      ⟨l, -, he, -⟩ | ⟨he, -, -⟩ <;> rw [he]
    · exact div_pos ih hr
    · exact ih

/-- local functional at radius ρ: max over centres in the cell. -/
noncomputable def locF (X : Finset T) (hX : X.Nonempty) (ρ : ℝ) : ℝ :=
  X.sup' hX (fun u => F (cb X u ρ))

lemma locF_le_of_sub {X Y : Finset T} (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : X ⊆ Y)
    (hmono : ∀ A B : Finset T, A ⊆ B → F A ≤ F B) {ρ ρ' : ℝ} (hρ : ρ ≤ ρ') :
    locF F X hX ρ ≤ locF F Y hY ρ' := by
  unfold locF
  apply Finset.sup'_le
  intro u hu
  exact (hmono _ _ (cb_mono hXY u hρ)).trans (Finset.le_sup' (fun u => F (cb Y u ρ')) (hXY hu))

lemma locF_le_F {X : Finset T} (hX : X.Nonempty) (hmono : ∀ A B : Finset T, A ⊆ B → F A ≤ F B)
    (ρ : ℝ) : locF F X hX ρ ≤ F X :=
  Finset.sup'_le _ _ (fun u _ => hmono _ _ (cb_sub X u ρ))

lemma locF_nonneg {X : Finset T} (hX : X.Nonempty) (hnn : ∀ A : Finset T, A.Nonempty → 0 ≤ F A)
    {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ locF F X hX ρ := by
  obtain ⟨u, hu⟩ := hX
  exact (hnn _ ⟨u, self_mem_cb hu hρ⟩).trans (Finset.le_sup' (fun u => F (cb X u ρ)) hu)

lemma cellNe (k : ℕ) (t : T) : (st F r R0 k t).1.Nonempty := ⟨t, st_mem F r R0 k t⟩

lemma sqrt_two_pow_succ (k : ℕ) : Real.sqrt (2 ^ (k + 1)) = Real.sqrt 2 * Real.sqrt (2 ^ k) := by
  rw [pow_succ, Real.sqrt_mul (by positivity), mul_comm]

/-- One step of the chain of `t` is a ball step or a stay step (with gain), as `chain_sum_le` needs. -/
lemma chain_step (hr : 4 ≤ r) (hc : 0 < c) (hR0 : 0 < R0)
    (hmono : ∀ A B : Finset T, A ⊆ B → F A ≤ F B) (hG : Growth F r c) (t : T) (k : ℕ) (hk : 1 ≤ k) :
    (Real.sqrt (2 ^ (k + 1)) * (st F r R0 (k + 1) t).2 =
        Real.sqrt 2 / r * (Real.sqrt (2 ^ k) * (st F r R0 k t).2) ∧
      F (st F r R0 (k + 1) t).1 ≤ locF F _ (cellNe F r R0 k t) ((st F r R0 k t).2 / r) ∧
      locF F _ (cellNe F r R0 (k + 1) t) ((st F r R0 (k + 1) t).2 / r) ≤
        locF F _ (cellNe F r R0 k t) ((st F r R0 k t).2 / r / r)) ∨
    (Real.sqrt (2 ^ (k + 1)) * (st F r R0 (k + 1) t).2 =
        Real.sqrt 2 * (Real.sqrt (2 ^ k) * (st F r R0 k t).2) ∧
      F (st F r R0 (k + 1) t).1 ≤ F (st F r R0 k t).1 ∧
      locF F _ (cellNe F r R0 (k + 1) t) ((st F r R0 (k + 1) t).2 / r) ≤
        locF F _ (cellNe F r R0 k t) ((st F r R0 k t).2 / r) ∧
      locF F _ (cellNe F r R0 (k + 1) t) ((st F r R0 (k + 1) t).2 / r / r) ≤
        F (st F r R0 k t).1 - c / (2 * r) * (Real.sqrt (2 ^ k) * (st F r R0 k t).2)) := by
  have hr0 : 0 < r := by linarith
  have hRk := st_R_pos F r R0 hr0 hR0 k t
  have hsub := st_sub F r R0 k t
  set X := (st F r R0 k t).1 with hXdef
  set R := (st F r R0 k t).2 with hRdef
  have hs := st_succ F r R0 k t
  rcases nxt_cases F r (2 ^ 2 ^ k - 1) (st F r R0 k t) (st_mem F r R0 k t) with
    ⟨l, -, he, hm⟩ | ⟨he, hm, -⟩
  · left
    rw [he] at hs
    have h1 : (st F r R0 (k + 1) t).1 = piece F R r X l := by rw [hs]
    have h2 : (st F r R0 (k + 1) t).2 = R / r := by rw [hs]
    have hrem : (rem F R r X l).Nonempty := ⟨t, piece_sub F R r X l hm⟩
    have hctr : ctr F R r X l ∈ X := rem_sub F R r X l (ctr0_spec F (R / r / r) hrem).1
    refine ⟨?_, ?_, ?_⟩
    · rw [h2, sqrt_two_pow_succ]; field_simp
    · rw [h1]
      exact (hmono _ _ (cb_mono (rem_sub F R r X l) _ le_rfl)).trans
        (Finset.le_sup' (fun u => F (cb X u (R / r))) hctr)
    · exact locF_le_of_sub F _ _ hsub hmono (by rw [h2])
  · right
    rw [he] at hs
    have h1 : (st F r R0 (k + 1) t).1 = rem F R r X (2 ^ 2 ^ k - 1) := by rw [hs]
    have h2 : (st F r R0 (k + 1) t).2 = R := by rw [hs]
    have hM : 2 ≤ 2 ^ 2 ^ k - 1 := by
      have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have : 2 ^ 2 ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
      omega
    refine ⟨?_, hmono _ _ hsub, locF_le_of_sub F _ _ hsub hmono (by rw [h2]), ?_⟩
    · rw [h2, sqrt_two_pow_succ]; ring
    · unfold locF
      apply Finset.sup'_le
      intro u hu
      rw [h1] at hu
      rw [h1, h2]
      have hg := stay_gain F r c (by linarith) hmono hG R hRk X _ hM hm u hu
      have hb := sqrt_log_bound k hk
      have hcR : 0 ≤ c * (R / r) := by positivity
      have hm2 := mul_le_mul_of_nonneg_left hb hcR
      have heq : c / (2 * r) * (Real.sqrt (2 ^ k) * R) = c * (R / r) * (Real.sqrt (2 ^ k) / 2) := by
        field_simp
      linarith

end Chain


section Assembly

variable {T : Type} [MetricSpace T] [Fintype T] [DecidableEq T] [Nonempty T]

lemma st_R_succ_le (F : Finset T → ℝ) (r R0 : ℝ) (hr : 1 ≤ r) (hR0 : 0 < R0) (k : ℕ) (t : T) :
    (st F r R0 (k + 1) t).2 ≤ (st F r R0 k t).2 := by
  have hRk := st_R_pos F r R0 (by linarith) hR0 k t
  rw [st_succ]
  rcases nxt_cases F r (2 ^ 2 ^ k - 1) (st F r R0 k t) (st_mem F r R0 k t) with
    ⟨l, -, he, -⟩ | ⟨he, -, -⟩
  · rw [he]; exact div_le_self hRk.le hr
  · rw [he]

lemma st_R_anti (F : Finset T → ℝ) (r R0 : ℝ) (hr : 1 ≤ r) (hR0 : 0 < R0) (t : T) {k k' : ℕ}
    (h : k ≤ k') : (st F r R0 k' t).2 ≤ (st F r R0 k t).2 :=
  (antitone_nat_of_succ_le (f := fun k => (st F r R0 k t).2)
    (fun k => st_R_succ_le F r R0 hr hR0 k t)) h

/-- representative point of a finset. -/
noncomputable def rep (X : Finset T) : T := if h : X.Nonempty then h.choose else Classical.arbitrary T

lemma rep_mem {X : Finset T} (h : X.Nonempty) : rep X ∈ X := by
  simp only [rep, dif_pos h]; exact h.choose_spec

theorem partition_scheme (F : Finset T → ℝ) (r c : ℝ) (hr : 4 ≤ r) (hc : 0 < c)
    (hmono : ∀ A B : Finset T, A ⊆ B → F A ≤ F B)
    (hnn : ∀ A : Finset T, A.Nonempty → 0 ≤ F A) (hG : Growth F r c) :
    ∃ (t0 : T) (π : ℕ → T → T), (∀ t, π 0 t = t0) ∧
      (∀ n, (Finset.univ.image (π n)).card ≤ 2 ^ 2 ^ n) ∧
      (∀ t, ∃ N, ∀ k, N ≤ k → π k t = t) ∧
      ∀ t N, ∑ k ∈ Finset.range N, Real.sqrt (2 ^ k) * dist (π k t) (π (k + 1) t) ≤
        200 * r * (F Finset.univ / c + Metric.diam (Set.univ : Set T)) := by
  have hr0 : 0 < r := by linarith
  have hFu : 0 ≤ F Finset.univ := hnn _ Finset.univ_nonempty
  have hFc : 0 ≤ F Finset.univ / c := div_nonneg hFu hc.le
  have hbdd : Bornology.IsBounded (Set.univ : Set T) := (Set.toFinite _).isBounded
  set R0 := Metric.diam (Set.univ : Set T) with hR0def
  have hdist : ∀ s z : T, dist s z ≤ R0 := fun s z =>
    Metric.dist_le_diam_of_mem hbdd (Set.mem_univ _) (Set.mem_univ _)
  have hR0nn : 0 ≤ R0 := Metric.diam_nonneg
  rcases hR0nn.eq_or_lt with h0 | hpos
  · obtain ⟨t0⟩ := (inferInstance : Nonempty T)
    have hall : ∀ s : T, s = t0 := fun s => by
      have := hdist s t0; rw [← h0] at this; exact dist_le_zero.mp this
    refine ⟨t0, fun _ _ => t0, fun _ => rfl, ?_, ?_, ?_⟩
    · intro n
      calc _ ≤ 1 := by
            apply Finset.card_le_one.mpr; intro a _ b _
            rw [hall a, hall b]
        _ ≤ 2 ^ 2 ^ n := Nat.one_le_two_pow
    · intro t; exact ⟨0, fun k _ => (hall t).symm⟩
    · intro t N
      simp only [dist_self, mul_zero, Finset.sum_const_zero]
      exact mul_nonneg (by positivity) (by linarith)
  · have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hs15 : Real.sqrt 2 ≤ 3 / 2 := by
      by_contra hc
      have hc' := not_le.mp hc
      have := mul_lt_mul'' hc' hc' (by norm_num) (by norm_num)
      linarith
    have hq : Real.sqrt 2 / r ≤ 1 / 2 := by rw [div_le_iff₀ hr0]; linarith
    have hchain : ∀ t N, ∑ i ∈ Finset.range N, Real.sqrt (2 ^ (i + 1)) * (st F r R0 (i + 1) t).2 ≤
        (10 * Real.sqrt 2 / (c / (2 * r))) * F (st F r R0 (0 + 1) t).1 +
          2 * (Real.sqrt (2 ^ (0 + 1)) * (st F r R0 (0 + 1) t).2) := by
      intro t
      have h := chain_sum_le (fun i => F (st F r R0 (i + 1) t).1)
        (fun i => locF F _ (cellNe F r R0 (i + 1) t) ((st F r R0 (i + 1) t).2 / r))
        (fun i => locF F _ (cellNe F r R0 (i + 1) t) ((st F r R0 (i + 1) t).2 / r / r))
        (fun i => Real.sqrt (2 ^ (i + 1)) * (st F r R0 (i + 1) t).2)
        (Real.sqrt 2 / r) (c / (2 * r)) (by positivity) hq (by positivity)
        (fun i => locF_nonneg F _ hnn (by have := st_R_pos F r R0 hr0 hpos (i + 1) t; positivity))
        (fun i => locF_le_of_sub F _ _ (Finset.Subset.refl _) hmono
          (div_le_self (by have := st_R_pos F r R0 hr0 hpos (i + 1) t; positivity) (by linarith)))
        (fun i => locF_le_F F _ hmono _)
        (fun i => mul_pos (Real.sqrt_pos.mpr (by positivity)) (st_R_pos F r R0 hr0 hpos (i + 1) t))
        (fun i => chain_step F r c R0 hr hc hpos hmono hG t (i + 1) (by omega))
      exact h
    let π : ℕ → T → T := fun k t => rep (st F r R0 k t).1
    refine ⟨rep (Finset.univ : Finset T), π, fun t => rfl, ?_, ?_, ?_⟩
    · intro n
      have : Finset.univ.image (π n) =
          (Finset.univ.image (st F r R0 n)).image (fun σ => rep σ.1) := by
        rw [Finset.image_image]; rfl
      rw [this]; exact Finset.card_image_le.trans (st_card F r R0 n)
    · intro t
      have hε : ∃ ε > 0, ∀ s, s ≠ t → 2 * ε ≤ dist s t := by
        by_cases hS : (Finset.univ.filter (fun s => s ≠ t)).Nonempty
        · refine ⟨(Finset.univ.filter (fun s => s ≠ t)).inf' hS (fun s => dist s t) / 2, ?_, ?_⟩
          · apply half_pos; rw [Finset.lt_inf'_iff]; intro s hs
            exact dist_pos.mpr (Finset.mem_filter.mp hs).2
          · intro s hs
            have := Finset.inf'_le (s := Finset.univ.filter (fun s => s ≠ t)) (fun s => dist s t)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩)
            linarith
        · exact ⟨1, one_pos, fun s hs =>
            absurd (⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩⟩ :
              (Finset.univ.filter (fun s => s ≠ t)).Nonempty) hS⟩
      obtain ⟨ε, hε0, hεs⟩ := hε
      set B := (10 * Real.sqrt 2 / (c / (2 * r))) * F (st F r R0 (0 + 1) t).1 +
          2 * (Real.sqrt (2 ^ (0 + 1)) * (st F r R0 (0 + 1) t).2) with hB
      have hsmall : ∃ i, (st F r R0 (i + 1) t).2 < ε := by
        by_contra hcon
        simp only [not_exists, not_lt] at hcon
        obtain ⟨N, hN⟩ := exists_nat_gt (B / ε)
        have hlow : (N : ℝ) * ε ≤ ∑ i ∈ Finset.range N, Real.sqrt (2 ^ (i + 1)) * (st F r R0 (i + 1) t).2 := by
          have : ∑ i ∈ Finset.range N, ε ≤
              ∑ i ∈ Finset.range N, Real.sqrt (2 ^ (i + 1)) * (st F r R0 (i + 1) t).2 := by
            apply Finset.sum_le_sum; intro i _
            have h1 : 1 ≤ Real.sqrt (2 ^ (i + 1)) := by
              rw [Real.one_le_sqrt]; exact one_le_pow₀ (by norm_num)
            have h2 := hcon i
            have h3 : 0 < (st F r R0 (i + 1) t).2 := st_R_pos F r R0 hr0 hpos (i + 1) t
            linarith [mul_le_mul_of_nonneg_right h1 h3.le]
          simpa using this
        have := hchain t N
        rw [div_lt_iff₀ hε0] at hN
        linarith
      obtain ⟨i, hi⟩ := hsmall
      refine ⟨i + 1, fun k hk => ?_⟩
      have hRk : (st F r R0 k t).2 < ε := lt_of_le_of_lt (st_R_anti F r R0 (by linarith) hpos t hk) hi
      obtain ⟨z, hz⟩ := st_ctr F r R0 hdist k t
      have hall : ∀ s ∈ (st F r R0 k t).1, s = t := by
        intro s hs
        by_contra hne
        have h1 := hz s hs
        have h2 := hz t (st_mem F r R0 k t)
        have h3 := hεs s hne
        have h4 := dist_triangle_right s t z
        linarith
      exact hall _ (rep_mem (cellNe F r R0 k t))
    · intro t N
      have hterm : ∀ k, Real.sqrt (2 ^ k) * dist (π k t) (π (k + 1) t) ≤
          2 * (Real.sqrt (2 ^ k) * (st F r R0 k t).2) := by
        intro k
        obtain ⟨z, hz⟩ := st_ctr F r R0 hdist k t
        have h1 := hz _ (rep_mem (cellNe F r R0 k t))
        have h2 := hz _ (st_sub F r R0 k t (rep_mem (cellNe F r R0 (k + 1) t)))
        have h3 := dist_triangle_right (π k t) (π (k + 1) t) z
        have h4 : dist (π k t) (π (k + 1) t) ≤ 2 * (st F r R0 k t).2 := by
          simp only [π] at h3 ⊢; linarith
        have h5 : 0 ≤ Real.sqrt (2 ^ k) := Real.sqrt_nonneg _
        linarith [mul_le_mul_of_nonneg_left h4 h5]
      have hsum1 : ∑ k ∈ Finset.range N, Real.sqrt (2 ^ k) * dist (π k t) (π (k + 1) t) ≤
          2 * ∑ k ∈ Finset.range (N + 1), Real.sqrt (2 ^ k) * (st F r R0 k t).2 := by
        rw [Finset.mul_sum]
        calc _ ≤ ∑ k ∈ Finset.range N, 2 * (Real.sqrt (2 ^ k) * (st F r R0 k t).2) :=
              Finset.sum_le_sum (fun k _ => hterm k)
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
              (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
              (fun k _ _ => by have := st_R_pos F r R0 hr0 hpos k t; positivity)
      rw [Finset.sum_range_succ'] at hsum1
      have hc1 := hchain t N
      have hR1 : (st F r R0 (0 + 1) t).2 ≤ R0 := st_R_anti F r R0 (by linarith) hpos t (Nat.zero_le _)
      have hF1 : F (st F r R0 (0 + 1) t).1 ≤ F Finset.univ := hmono _ _ (Finset.subset_univ _)
      have hF1nn : 0 ≤ F (st F r R0 (0 + 1) t).1 := hnn _ (cellNe F r R0 _ t)
      have hcoef : 0 ≤ 10 * Real.sqrt 2 / (c / (2 * r)) := by positivity
      have hA : (10 * Real.sqrt 2 / (c / (2 * r))) * F (st F r R0 (0 + 1) t).1 ≤
          (10 * Real.sqrt 2 / (c / (2 * r))) * F Finset.univ := mul_le_mul_of_nonneg_left hF1 hcoef
      have hA' : (10 * Real.sqrt 2 / (c / (2 * r))) * F Finset.univ =
          20 * Real.sqrt 2 * (r * (F Finset.univ / c)) := by
        field_simp; ring
      have hx : 0 ≤ r * (F Finset.univ / c) := by positivity
      have hA'' : 20 * Real.sqrt 2 * (r * (F Finset.univ / c)) ≤ 30 * (r * (F Finset.univ / c)) :=
        mul_le_mul_of_nonneg_right (by linarith) hx
      have hs1 : Real.sqrt (2 ^ (0 + 1)) = Real.sqrt 2 := by norm_num
      have h00 : (st F r R0 0 t).2 = R0 := rfl
      have hτ0 : Real.sqrt (2 ^ 0) * (st F r R0 0 t).2 = R0 := by rw [h00]; simp
      have hB2 : Real.sqrt (2 ^ (0 + 1)) * (st F r R0 (0 + 1) t).2 ≤ 3 / 2 * R0 := by
        rw [hs1]
        linarith [mul_le_mul hs15 hR1 (st_R_pos F r R0 hr0 hpos (0 + 1) t).le (by norm_num : (0:ℝ) ≤ 3 / 2)]
      have hfin : 200 * r * (F Finset.univ / c + R0) = 200 * (r * (F Finset.univ / c)) + 200 * r * R0 := by
        ring
      rw [hfin]
      linarith [mul_le_mul_of_nonneg_right hr hpos.le]

end Assembly

end MDI

end SecC4

section SecR


open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MDI3

/-- the (specialised) Gaussian Lipschitz concentration hypothesis (statement of e92f914b at `Type`). -/
def ConcHyp : Prop :=
  ∀ {ι : Type} [Fintype ι] (f : (ι → ℝ) → ℝ) (L : ℝ),
    0 < L → (∀ x y, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)) → ∀ (t : ℝ), 0 ≤ t →
    Integrable f (Measure.pi fun _ : ι => gaussianReal 0 1) ∧
    (Measure.pi fun _ : ι => gaussianReal 0 1)
        {x | (∫ y, f y ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) + L * t ≤ f x}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / 2))

section Conc

variable {n : ℕ}


lemma conc_E (hC : ConcHyp) (f : (EuclideanSpace ℝ (Fin n)) → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hf : ∀ x y, |f x - f y| ≤ σ * ‖x - y‖) (τ : ℝ) (hτ : 0 ≤ τ) :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin n))) ∧
      stdGaussian (EuclideanSpace ℝ (Fin n)) {x | (∫ y, f y ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) + σ * τ ≤ f x} ≤
        ENNReal.ofReal (Real.exp (-τ ^ 2 / 2)) := by
  set b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n)) with hb
  let φ : (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ) → (EuclideanSpace ℝ (Fin n)) := fun x => ∑ i, x i • b i
  have hφm : Measurable φ := by fun_prop
  have hμ : stdGaussian (EuclideanSpace ℝ (Fin n)) = (Measure.pi fun _ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) => gaussianReal 0 1).map φ := rfl
  have hφn : ∀ x y, ‖φ x - φ y‖ = Real.sqrt (∑ i, (x i - y i) ^ 2) := by
    intro x y
    have h1 : φ x - φ y = b.repr.symm (WithLp.toLp 2 (x - y)) := by
      rw [← OrthonormalBasis.sum_repr_symm]
      simp only [φ, ← Finset.sum_sub_distrib, ← sub_smul]
      rfl
    rw [h1, LinearIsometryEquiv.norm_map, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp [Real.norm_eq_abs, sq_abs]
  have hfc : Continuous f := by
    have : LipschitzWith (Real.toNNReal σ) f := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hσ.le]
      exact hf x y
    exact this.continuous
  have hg := hC (f ∘ φ) σ hσ (fun x y => by
    simp only [Function.comp]; rw [← hφn]; exact hf _ _) τ hτ
  have hint : ∫ y, f y ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
      ∫ y, (f ∘ φ) y ∂(Measure.pi fun _ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) => gaussianReal 0 1) := by
    rw [hμ, integral_map hφm.aemeasurable hfc.aestronglyMeasurable]; rfl
  refine ⟨?_, ?_⟩
  · rw [hμ]
    exact (integrable_map_measure hfc.aestronglyMeasurable hφm.aemeasurable).mpr hg.1
  · rw [hint, hμ, Measure.map_apply hφm (measurableSet_le measurable_const hfc.measurable)]
    exact hg.2

end Conc

/-- tail bound ⟹ expectation bound (layer cake). -/
lemma integral_le_of_tail {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (hD0 : ∀ ω, 0 ≤ D ω) (hDm : AEMeasurable D μ) (σ k : ℝ) (hσ : 0 < σ)
    (hk : 2 ≤ k)
    (htail : ∀ τ, 0 ≤ τ → μ {ω | σ * τ < D ω} ≤ ENNReal.ofReal (k * Real.exp (-τ ^ 2 / 2))) :
    ∫ ω, D ω ∂μ ≤ σ * (Real.sqrt (2 * Real.log k) + 1 / Real.sqrt (2 * Real.log k)) := by
  set T := Real.sqrt (2 * Real.log k) with hT
  have hlogk : 0 < Real.log k := Real.log_pos (by linarith)
  have hT0 : 0 < T := Real.sqrt_pos.mpr (by linarith)
  have hT2 : T ^ 2 = 2 * Real.log k := Real.sq_sqrt (by linarith)
  have hkT : k = Real.exp (T ^ 2 / 2) := by
    rw [hT2, show 2 * Real.log k / 2 = Real.log k by ring, Real.exp_log (by linarith)]
  set a : ℝ := -T / σ with ha
  have ha0 : a < 0 := div_neg_of_neg_of_pos (by linarith) hσ
  -- pointwise tail bound on the layer variable
  have hpt : ∀ t, σ * T < t →
      μ {ω | t < D ω} ≤ ENNReal.ofReal (Real.exp (T ^ 2) * Real.exp (a * t)) := by
    intro t ht
    have hτ : 0 ≤ t / σ := div_nonneg (by nlinarith) hσ.le
    have h1 := htail (t / σ) hτ
    rw [show σ * (t / σ) = t by field_simp] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hkT, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : a * t = -T * (t / σ) := by rw [ha]; ring
    rw [this]
    nlinarith [sq_nonneg (t / σ - T)]
  have hlay := lintegral_eq_lintegral_meas_lt μ (Filter.Eventually.of_forall hD0) hDm
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 (σ * T) ∪ Set.Ioi (σ * T) :=
    (Set.Ioc_union_Ioi_eq_Ioi (by positivity)).symm
  have hI1 : ∫⁻ t in Set.Ioc 0 (σ * T), μ {ω | t < D ω} ≤ ENNReal.ofReal (σ * T) := by
    calc ∫⁻ t in Set.Ioc 0 (σ * T), μ {ω | t < D ω} ≤ ∫⁻ t in Set.Ioc 0 (σ * T), 1 :=
          lintegral_mono (fun t => prob_le_one)
      _ = ENNReal.ofReal (σ * T) := by simp [Real.volume_Ioc]
  have hint2 : IntegrableOn (fun t => Real.exp (T ^ 2) * Real.exp (a * t)) (Set.Ioi (σ * T)) :=
    (integrableOn_exp_mul_Ioi ha0 (σ * T)).const_mul _
  have hval : ∫ t in Set.Ioi (σ * T), Real.exp (T ^ 2) * Real.exp (a * t) = σ / T := by
    rw [integral_const_mul, integral_exp_mul_Ioi ha0]
    have : a * (σ * T) = -T ^ 2 := by rw [ha]; field_simp
    rw [this, ha]
    have he : Real.exp (T ^ 2) * Real.exp (-T ^ 2) = 1 := by rw [← Real.exp_add]; simp
    field_simp
    exact he
  have hI2 : ∫⁻ t in Set.Ioi (σ * T), μ {ω | t < D ω} ≤ ENNReal.ofReal (σ / T) := by
    calc ∫⁻ t in Set.Ioi (σ * T), μ {ω | t < D ω}
        ≤ ∫⁻ t in Set.Ioi (σ * T), ENNReal.ofReal (Real.exp (T ^ 2) * Real.exp (a * t)) :=
          setLIntegral_mono' measurableSet_Ioi (fun t ht => hpt t ht)
      _ = ENNReal.ofReal (σ / T) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint2
            (Filter.Eventually.of_forall (fun t => by positivity)), hval]
  have hL : ∫⁻ ω, ENNReal.ofReal (D ω) ∂μ ≤ ENNReal.ofReal (σ * T + σ / T) := by
    rw [hlay, hsplit]
    calc _ ≤ (∫⁻ t in Set.Ioc 0 (σ * T), μ {ω | t < D ω}) + (∫⁻ t in Set.Ioi (σ * T), μ {ω | t < D ω}) :=
          lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal (σ * T) + ENNReal.ofReal (σ / T) := add_le_add hI1 hI2
      _ = ENNReal.ofReal (σ * T + σ / T) := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hD0) hDm.aestronglyMeasurable]
  have := ENNReal.toReal_le_of_le_ofReal (by positivity) hL
  calc _ ≤ σ * T + σ / T := this
    _ = σ * (T + 1 / T) := by ring


lemma integrable_sup' {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type}
    (s : Finset ι) (hs : s.Nonempty) (Y : ι → Ω → ℝ) (hY : ∀ i ∈ s, Integrable (Y i) P) :
    Integrable (fun ω => s.sup' hs (fun i => Y i ω)) P := by
  have : (fun ω => s.sup' hs (fun i => Y i ω)) = s.sup' hs Y := by
    funext ω; rw [Finset.sup'_apply]
  rw [this]
  exact Finset.sup'_induction (p := fun f => Integrable f P) hs Y
    (fun a ha b hb => Integrable.sup ha hb) hY

lemma sup'_sub_const {ι : Type} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ) :
    s.sup' hs f - c = s.sup' hs (fun i => f i - c) := by
  apply le_antisymm
  · have : s.sup' hs f ≤ s.sup' hs (fun i => f i - c) + c := Finset.sup'_le _ _ (fun i hi => by
      have := Finset.le_sup' (fun i => f i - c) hi; linarith)
    linarith
  · exact Finset.sup'_le _ _ (fun i hi => by
      have := Finset.le_sup' f hi; linarith)

lemma sup'_sub_abs_le {ι : Type} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) :
    |s.sup' hs f - s.sup' hs g| ≤ s.sup' hs (fun i => |f i - g i|) := by
  have hM : ∀ i ∈ s, |f i - g i| ≤ s.sup' hs (fun i => |f i - g i|) :=
    fun i hi => Finset.le_sup' (fun i => |f i - g i|) hi
  rw [abs_sub_le_iff]; constructor
  · have : s.sup' hs f ≤ s.sup' hs g + s.sup' hs (fun i => |f i - g i|) :=
      Finset.sup'_le _ _ (fun i hi => by
        have := hM i hi; have := Finset.le_sup' g hi; have := le_abs_self (f i - g i); linarith)
    linarith
  · have : s.sup' hs g ≤ s.sup' hs f + s.sup' hs (fun i => |f i - g i|) :=
      Finset.sup'_le _ _ (fun i hi => by
        have := hM i hi; have := Finset.le_sup' f hi; have := neg_abs_le (f i - g i); linarith)
    linarith

section Growth

variable {n : ℕ}


/-- `E_g max_{t ∈ H} ⟨g, t⟩` (0 if empty); identical to `MDI.gF`. -/
noncomputable def gF (H : Finset (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ∫ g, (if h : H.Nonempty then H.sup' h (fun s => inner (𝕜 := ℝ) g s) else 0)
    ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))

lemma inner_eq_SL (s g : (EuclideanSpace ℝ (Fin n))) : inner (𝕜 := ℝ) g s = innerSL ℝ s g := by
  rw [innerSL_apply_apply]; exact real_inner_comm s g

lemma integrable_inner (s : (EuclideanSpace ℝ (Fin n))) : Integrable (fun g : (EuclideanSpace ℝ (Fin n)) => inner (𝕜 := ℝ) g s) (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have := IsGaussian.integrable_dual (stdGaussian (EuclideanSpace ℝ (Fin n))) (innerSL ℝ s)
  refine this.congr (Filter.Eventually.of_forall fun g => ?_)
  exact (inner_eq_SL s g).symm

lemma integral_inner_zero (s : (EuclideanSpace ℝ (Fin n))) : ∫ g, inner (𝕜 := ℝ) g s ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
  have h1 : ∫ g, inner (𝕜 := ℝ) g s ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = ∫ g, innerSL ℝ s (id g) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    integral_congr_ae (Filter.Eventually.of_forall fun g => inner_eq_SL s g)
  rw [h1, (innerSL ℝ s).integral_comp_comm IsGaussian.integrable_id]
  simp [integral_id_stdGaussian]

lemma second_moment (v : (EuclideanSpace ℝ (Fin n))) : ∫ g, (inner (𝕜 := ℝ) g v) ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = ‖v‖ ^ 2 := by
  have h1 := variance_dual_stdGaussian (innerSL ℝ v)
  rw [innerSL_apply_norm] at h1
  have h0 : ∫ g, innerSL ℝ v g ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0 := by
    rw [← integral_inner_zero v]
    exact integral_congr_ae (Filter.Eventually.of_forall fun g => (inner_eq_SL v g).symm)
  rw [variance_of_integral_eq_zero (innerSL ℝ v).continuous.aemeasurable h0] at h1
  rw [← h1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => by
    simp only [Pi.pow_apply]; rw [inner_eq_SL])

lemma lip_cont (f : (EuclideanSpace ℝ (Fin n)) → ℝ) (σ : ℝ) (hσ : 0 < σ) (hf : ∀ x y, |f x - f y| ≤ σ * ‖x - y‖) :
    Continuous f := by
  have : LipschitzWith (Real.toNNReal σ) f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hσ.le]
    exact hf x y
  exact this.continuous

theorem gaussian_growth (hC : ConcHyp)
    (hSud : ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {ι : Type} [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ)
        (hXG : IsGaussianProcess X P) (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0)
        (ε : ℝ), 0 ≤ ε →
        (∀ i j, i ≠ j → ε ^ 2 ≤ ∫ ω, (X i ω - X j ω) ^ 2 ∂P) →
        c * ε * Real.sqrt (Real.log (Fintype.card ι)) ≤
          ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P) :
    ∃ r c : ℝ, 4 ≤ r ∧ 0 < c ∧
      ∀ {n : ℕ} (m : ℕ), 2 ≤ m → ∀ (a : ℝ), 0 < a →
        ∀ (t : Fin m → EuclideanSpace ℝ (Fin n)) (H : Fin m → Finset (EuclideanSpace ℝ (Fin n))),
        (∀ l l', l ≠ l' → a ≤ dist (t l) (t l')) →
        (∀ l, ∀ s ∈ H l, dist s (t l) ≤ a / r) → (∀ l, (H l).Nonempty) →
        ∃ l, c * a * Real.sqrt (Real.log m) + gF (H l) ≤ gF (Finset.univ.biUnion H) := by
  obtain ⟨c0, hc0, hS⟩ := hSud
  refine ⟨max 4 (8 / c0), c0 / 2, le_max_left _ _, by positivity, ?_⟩
  intro n m hm a ha t H hsep hball hne
  set r := max 4 (8 / c0) with hr
  have hr4 : 4 ≤ r := le_max_left _ _
  have hr8 : 8 / c0 ≤ r := le_max_right _ _
  have hr0 : 0 < r := by linarith
  set σ := a / r with hσdef
  have hσ : 0 < σ := div_pos ha hr0
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  let S : Fin m → EuclideanSpace ℝ (Fin n) → ℝ := fun l g =>
    (H l).sup' (hne l) (fun s => inner (𝕜 := ℝ) g s)
  let Z : Fin m → EuclideanSpace ℝ (Fin n) → ℝ := fun l g => S l g - inner (𝕜 := ℝ) g (t l)
  have hSi : ∀ l, Integrable (S l) (stdGaussian _) := fun l =>
    integrable_sup' _ (H l) (hne l) (fun s g => inner (𝕜 := ℝ) g s) (fun s _ => integrable_inner s)
  have hZi : ∀ l, Integrable (Z l) (stdGaussian _) := fun l => (hSi l).sub (integrable_inner (t l))
  set f : Fin m → ℝ := fun l => ∫ g, Z l g ∂(stdGaussian _) with hf
  have hfS : ∀ l, gF (H l) = f l := by
    intro l
    simp only [gF, dif_pos (hne l)]
    change ∫ g, S l g ∂(stdGaussian _) = ∫ g, Z l g ∂(stdGaussian _)
    simp only [Z]
    rw [integral_sub (hSi l) (integrable_inner (t l)), integral_inner_zero, sub_zero]
  have hZlip : ∀ l g h, |Z l g - Z l h| ≤ σ * ‖g - h‖ := by
    intro l g h
    simp only [Z, S]
    rw [sup'_sub_const (H l) (hne l) (fun s => inner (𝕜 := ℝ) g s),
      sup'_sub_const (H l) (hne l) (fun s => inner (𝕜 := ℝ) h s)]
    refine (sup'_sub_abs_le _ _ _ _).trans (Finset.sup'_le _ _ (fun s hs => ?_))
    have h1 : inner (𝕜 := ℝ) g s - inner (𝕜 := ℝ) g (t l) - (inner (𝕜 := ℝ) h s - inner (𝕜 := ℝ) h (t l)) =
        inner (𝕜 := ℝ) (g - h) (s - t l) := by
      simp only [inner_sub_left, inner_sub_right]; ring
    rw [h1]
    have h2 := abs_real_inner_le_norm (g - h) (s - t l)
    have h3 : ‖s - t l‖ ≤ σ := by rw [← dist_eq_norm]; exact hball l s hs
    have h4 := norm_nonneg (g - h)
    nlinarith
  have hZc : ∀ l, Continuous (Z l) := fun l => lip_cont (Z l) σ hσ (hZlip l)
  have hcZ : ∀ l τ, 0 ≤ τ → stdGaussian _ {g | f l + σ * τ ≤ Z l g} ≤
      ENNReal.ofReal (Real.exp (-τ ^ 2 / 2)) := fun l τ hτ => (conc_E hC (Z l) σ hσ (hZlip l) τ hτ).2
  have hcZn : ∀ l τ, 0 ≤ τ → stdGaussian _ {g | -f l + σ * τ ≤ -Z l g} ≤
      ENNReal.ofReal (Real.exp (-τ ^ 2 / 2)) := by
    intro l τ hτ
    have := (conc_E hC (fun g => -Z l g) σ hσ (fun g h => by
      have := hZlip l g h; rwa [neg_sub_neg, abs_sub_comm]) τ hτ).2
    rw [integral_neg] at this
    exact this
  let D : EuclideanSpace ℝ (Fin n) → ℝ := fun g =>
    Finset.univ.sup' Finset.univ_nonempty (fun l => |Z l g - f l|)
  have hD0 : ∀ g, 0 ≤ D g := fun g => le_trans (abs_nonneg _)
    (Finset.le_sup' (fun l => |Z l g - f l|) (Finset.mem_univ (Classical.arbitrary (Fin m))))
  have hDm : Measurable D := by
    have : D = Finset.univ.sup' Finset.univ_nonempty (fun l g => |Z l g - f l|) := by
      funext g; simp only [D]; rw [Finset.sup'_apply]
    rw [this]
    exact Finset.measurable_sup' _ (fun l _ => ((hZc l).sub continuous_const).abs.measurable)
  have hDi : Integrable D (stdGaussian _) :=
    integrable_sup' _ _ _ (fun l g => |Z l g - f l|) (fun l _ => ((hZi l).sub (integrable_const _)).abs)
  have htail : ∀ τ, 0 ≤ τ → stdGaussian _ {g | σ * τ < D g} ≤
      ENNReal.ofReal (((2 * m : ℕ) : ℝ) * Real.exp (-τ ^ 2 / 2)) := by
    intro τ hτ
    have hsub : {g | σ * τ < D g} ⊆ ⋃ l ∈ (Finset.univ : Finset (Fin m)),
        ({g | f l + σ * τ ≤ Z l g} ∪ {g | -f l + σ * τ ≤ -Z l g}) := by
      intro g hg
      simp only [Set.mem_setOf_eq, D, Finset.lt_sup'_iff] at hg
      obtain ⟨l, -, hl⟩ := hg
      simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq]
      refine ⟨l, Finset.mem_univ l, ?_⟩
      rcases lt_abs.mp hl with h | h
      · left; linarith
      · right; linarith
    calc stdGaussian _ {g | σ * τ < D g}
        ≤ stdGaussian _ (⋃ l ∈ (Finset.univ : Finset (Fin m)),
            ({g | f l + σ * τ ≤ Z l g} ∪ {g | -f l + σ * τ ≤ -Z l g})) := measure_mono hsub
      _ ≤ ∑ l ∈ (Finset.univ : Finset (Fin m)),
            stdGaussian _ ({g | f l + σ * τ ≤ Z l g} ∪ {g | -f l + σ * τ ≤ -Z l g}) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ l ∈ (Finset.univ : Finset (Fin m)), ENNReal.ofReal (2 * Real.exp (-τ ^ 2 / 2)) := by
          apply Finset.sum_le_sum
          intro l _
          calc _ ≤ stdGaussian _ {g | f l + σ * τ ≤ Z l g} + stdGaussian _ {g | -f l + σ * τ ≤ -Z l g} :=
                measure_union_le _ _
            _ ≤ ENNReal.ofReal (Real.exp (-τ ^ 2 / 2)) + ENNReal.ofReal (Real.exp (-τ ^ 2 / 2)) :=
                add_le_add (hcZ l τ hτ) (hcZn l τ hτ)
            _ = ENNReal.ofReal (2 * Real.exp (-τ ^ 2 / 2)) := by
                rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
      _ = ENNReal.ofReal (((2 * m : ℕ) : ℝ) * Real.exp (-τ ^ 2 / 2)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; push_cast; ring
  have hk2 : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    push_cast; linarith
  have hED := integral_le_of_tail (stdGaussian _) D hD0 hDm.aemeasurable σ _ hσ hk2 htail
  -- numerics: (EuclideanSpace ℝ (Fin n)) D ≤ 4 σ √(log m)
  set L := Real.log m with hL
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog2 := Real.log_two_gt_d9
  have hLge : Real.log 2 ≤ L := Real.log_le_log (by norm_num) hm2
  have hL0 : 0 < L := by linarith
  have hsL : (4 / 5 : ℝ) ≤ Real.sqrt L := by
    rw [show (4 / 5 : ℝ) = Real.sqrt ((4 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hlog2m : Real.log (((2 * m : ℕ) : ℝ)) ≤ 2 * L := by
    have : (((2 * m : ℕ) : ℝ)) = 2 * m := by push_cast; ring
    rw [this, Real.log_mul (by norm_num) (by linarith)]
    linarith
  have hT1 : Real.sqrt (2 * Real.log (((2 * m : ℕ) : ℝ))) ≤ 2 * Real.sqrt L := by
    have h4 : Real.sqrt (4 * L) = 2 * Real.sqrt L := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h4]; exact Real.sqrt_le_sqrt (by linarith)
  have hT2 : 1 ≤ Real.sqrt (2 * Real.log (((2 * m : ℕ) : ℝ))) := by
    rw [Real.one_le_sqrt]
    have : Real.log 2 ≤ Real.log (((2 * m : ℕ) : ℝ)) := Real.log_le_log (by norm_num) hk2
    linarith
  have hinv : 1 / Real.sqrt (2 * Real.log (((2 * m : ℕ) : ℝ))) ≤ 1 := by
    rw [div_le_one (by linarith)]; exact hT2
  have hED' : ∫ g, D g ∂(stdGaussian _) ≤ 4 * σ * Real.sqrt L := by
    have : Real.sqrt (2 * Real.log (((2 * m : ℕ) : ℝ))) +
        1 / Real.sqrt (2 * Real.log (((2 * m : ℕ) : ℝ))) ≤ 4 * Real.sqrt L := by linarith
    have := mul_le_mul_of_nonneg_left this hσ.le
    linarith
  -- Sudakov on the centres
  let X : Fin m → EuclideanSpace ℝ (Fin n) → ℝ := fun l g => inner (𝕜 := ℝ) g (t l)
  have hXG : IsGaussianProcess X (stdGaussian _) := by
    constructor
    intro I
    let Lm : EuclideanSpace ℝ (Fin n) →L[ℝ] (I → ℝ) :=
      ContinuousLinearMap.pi (fun i : I => innerSL ℝ (t i))
    have hfun : (fun g => I.restrict (fun l => X l g)) = ⇑Lm := by
      funext g; funext i
      simp only [Finset.restrict, Lm, ContinuousLinearMap.pi_apply, X]
      exact inner_eq_SL (t i) g
    rw [hfun]
    exact IsGaussian.hasGaussianLaw
  have hXmean : ∀ l, ∫ g, X l g ∂(stdGaussian _) = 0 := fun l => integral_inner_zero (t l)
  have hXsep : ∀ i j, i ≠ j → a ^ 2 ≤ ∫ g, (X i g - X j g) ^ 2 ∂(stdGaussian _) := by
    intro i j hij
    have h1 : ∫ g, (X i g - X j g) ^ 2 ∂(stdGaussian _) = ‖t i - t j‖ ^ 2 := by
      rw [← second_moment (t i - t j)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp only [X, inner_sub_right])
    rw [h1, ← dist_eq_norm]
    exact pow_le_pow_left₀ ha.le (hsep i j hij) 2
  have hSud := hS (stdGaussian _) X hXG hXmean a ha.le hXsep
  rw [Fintype.card_fin] at hSud
  -- assembly
  obtain ⟨l0, -, hl0⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have hU : (Finset.univ.biUnion H).Nonempty := by
    obtain ⟨s, hs⟩ := hne (Classical.arbitrary (Fin m))
    exact ⟨s, Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, hs⟩⟩
  let Φ : EuclideanSpace ℝ (Fin n) → ℝ := fun g =>
    (Finset.univ.biUnion H).sup' hU (fun s => inner (𝕜 := ℝ) g s)
  have hΦ : gF (Finset.univ.biUnion H) = ∫ g, Φ g ∂(stdGaussian _) := by
    have hq : ∀ g, (if h : (Finset.univ.biUnion H).Nonempty then
        (Finset.univ.biUnion H).sup' h (fun s => inner (𝕜 := ℝ) g s) else 0) = Φ g :=
      fun g => dif_pos hU
    unfold gF
    exact integral_congr_ae (Filter.Eventually.of_forall hq)
  have hΦi : Integrable Φ (stdGaussian _) :=
    integrable_sup' _ _ hU (fun s g => inner (𝕜 := ℝ) g s) (fun s _ => integrable_inner s)
  let MX : EuclideanSpace ℝ (Fin n) → ℝ := fun g => Finset.univ.sup' Finset.univ_nonempty (fun l => X l g)
  have hMXi : Integrable MX (stdGaussian _) :=
    integrable_sup' _ _ _ X (fun l _ => integrable_inner (t l))
  have hpt : ∀ g, MX g + f l0 - D g ≤ Φ g := by
    intro g
    have : MX g ≤ Φ g - f l0 + D g := by
      apply Finset.sup'_le
      intro l _
      have hSΦ : S l g ≤ Φ g := Finset.sup'_le _ _ (fun s hs =>
        Finset.le_sup' (fun s => inner (𝕜 := ℝ) g s) (Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hs⟩))
      have hDl : |Z l g - f l| ≤ D g := Finset.le_sup' (fun l => |Z l g - f l|) (Finset.mem_univ l)
      have hfl := hl0 l (Finset.mem_univ l)
      have := neg_abs_le (Z l g - f l)
      simp only [Z] at this hDl
      simp only [X]
      linarith
    linarith
  have hint : ∫ g, (MX g + f l0 - D g) ∂(stdGaussian _) =
      ∫ g, MX g ∂(stdGaussian _) + f l0 - ∫ g, D g ∂(stdGaussian _) := by
    have hA : Integrable (fun g => MX g + f l0) (stdGaussian _) := hMXi.add (integrable_const _)
    rw [integral_sub hA hDi, integral_add hMXi (integrable_const _)]
    simp
  have hmono : ∫ g, (MX g + f l0 - D g) ∂(stdGaussian _) ≤ ∫ g, Φ g ∂(stdGaussian _) :=
    integral_mono ((hMXi.add (integrable_const _)).sub hDi) hΦi hpt
  refine ⟨l0, ?_⟩
  rw [hfS l0, hΦ]
  have h8 : 8 ≤ r * c0 := by rw [div_le_iff₀ hc0] at hr8; linarith
  have hsq0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
  have hkey : 4 * σ * Real.sqrt L ≤ c0 / 2 * a * Real.sqrt L := by
    apply mul_le_mul_of_nonneg_right _ hsq0
    rw [hσdef, mul_div_assoc']
    rw [div_le_iff₀ hr0]
    nlinarith
  have hSud' : c0 * a * Real.sqrt L ≤ ∫ g, MX g ∂(stdGaussian _) := hSud
  linarith

end Growth


end MDI3

namespace MDI

/-- C1: sub-gaussian increments (Vershynin 9.1). -/
def SubgaussianIncrements : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
      iIndepFun A P → (∀ i, HighDimProb.Deviations.IsIsotropic P (A i)) →
      ∀ (K : ℝ≥0), (∀ i, HighDimProb.Deviations.subgaussianVectorNorm P (A i) ≤ K) →
      ∀ x y : EuclideanSpace ℝ (Fin n),
        HighDimProb.Concentration.subgaussianNorm P (fun ω =>
          (Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x) ^ 2) - Real.sqrt m * ‖x‖) -
          (Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) y) ^ 2) - Real.sqrt m * ‖y‖)) ≤
        ENNReal.ofReal (C * (K : ℝ) ^ 2 * ‖x - y‖)

/-- C2: chaining along maps π n with card ≤ 2^(2^n). -/
def ChainingMapsBound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {T : Type} [MetricSpace T] [Fintype T] [DecidableEq T] (X : T → Ω → ℝ) (K : ℝ), 0 ≤ K →
      (∀ s t, HighDimProb.Concentration.subgaussianNorm P (fun ω => X s ω - X t ω) ≤
        ENNReal.ofReal (K * dist s t)) →
      ∀ (t0 : T) (π : ℕ → T → T), (∀ t, π 0 t = t0) →
      (∀ n, (Finset.univ.image (π n)).card ≤ 2 ^ 2 ^ n) →
      (∀ t, ∃ N, ∀ k, N ≤ k → π k t = t) → ∀ S : ℝ,
      (∀ t N, ∑ k ∈ Finset.range N, Real.sqrt (2 ^ k) * dist (π k t) (π (k + 1) t) ≤ S) →
      ∫ ω, Finset.univ.sup' ⟨t0, Finset.mem_univ _⟩ (fun t => |X t ω - X t0 ω|) ∂P ≤ C * K * S

/-- C3: growth condition for the Gaussian functional. -/
def GaussianGrowth : Prop :=
  ∃ r c : ℝ, 4 ≤ r ∧ 0 < c ∧
    ∀ {n : ℕ} (m : ℕ), 2 ≤ m → ∀ (a : ℝ), 0 < a →
      ∀ (t : Fin m → EuclideanSpace ℝ (Fin n)) (H : Fin m → Finset (EuclideanSpace ℝ (Fin n))),
      (∀ l l', l ≠ l' → a ≤ dist (t l) (t l')) →
      (∀ l, ∀ s ∈ H l, dist s (t l) ≤ a / r) → (∀ l, (H l).Nonempty) →
      ∃ l, c * a * Real.sqrt (Real.log m) + MDI3.gF (H l) ≤ MDI3.gF (Finset.univ.biUnion H)

/-- C4: Talagrand's partitioning scheme, abstract finite metric space. -/
def PartitionScheme : Prop :=
  ∀ {T : Type} [MetricSpace T] [Fintype T] [DecidableEq T] [Nonempty T] (F : Finset T → ℝ) (r c : ℝ),
    4 ≤ r → 0 < c →
    (∀ A B : Finset T, A ⊆ B → F A ≤ F B) →
    (∀ A : Finset T, A.Nonempty → 0 ≤ F A) →
    (∀ (m : ℕ), 2 ≤ m → ∀ (a : ℝ), 0 < a → ∀ (t : Fin m → T) (H : Fin m → Finset T),
        (∀ l l', l ≠ l' → a ≤ dist (t l) (t l')) →
        (∀ l, ∀ s ∈ H l, dist s (t l) ≤ a / r) → (∀ l, (H l).Nonempty) →
        ∃ l, c * a * Real.sqrt (Real.log m) + F (H l) ≤ F (Finset.univ.biUnion H)) →
    ∃ (t0 : T) (π : ℕ → T → T), (∀ t, π 0 t = t0) ∧
      (∀ n, (Finset.univ.image (π n)).card ≤ 2 ^ 2 ^ n) ∧
      (∀ t, ∃ N, ∀ k, N ≤ k → π k t = t) ∧
      ∀ t N, ∑ k ∈ Finset.range N, Real.sqrt (2 ^ k) * dist (π k t) (π (k + 1) t) ≤
        200 * r * (F Finset.univ / c + Metric.diam (Set.univ : Set T))

end MDI

namespace MDI3

section Assembly

lemma isGP_inner {n : ℕ} {ι : Type} (v : ι → EuclideanSpace ℝ (Fin n)) :
    IsGaussianProcess (fun i (g : EuclideanSpace ℝ (Fin n)) => inner (𝕜 := ℝ) g (v i))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  constructor
  intro I
  let Lm : EuclideanSpace ℝ (Fin n) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi (fun i : I => innerSL ℝ (v i))
  have hfun : (fun g => I.restrict (fun i => inner (𝕜 := ℝ) g (v i))) = ⇑Lm := by
    funext g; funext i
    simp only [Finset.restrict, Lm, ContinuousLinearMap.pi_apply]
    exact inner_eq_SL (v i) g
  rw [hfun]
  exact IsGaussian.hasGaussianLaw

lemma gF_eq {n : ℕ} {H : Finset (EuclideanSpace ℝ (Fin n))} (h : H.Nonempty) :
    gF H = ∫ g, H.sup' h (fun s => inner (𝕜 := ℝ) g s) ∂(stdGaussian _) := by
  unfold gF
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => dif_pos h)

lemma gF_empty {n : ℕ} : gF (∅ : Finset (EuclideanSpace ℝ (Fin n))) = 0 := by
  unfold gF; simp

lemma gF_nonneg {n : ℕ} {H : Finset (EuclideanSpace ℝ (Fin n))} (h : H.Nonempty) : 0 ≤ gF H := by
  obtain ⟨s, hs⟩ := h
  rw [gF_eq ⟨s, hs⟩]
  calc (0 : ℝ) = ∫ g, inner (𝕜 := ℝ) g s ∂(stdGaussian _) := (integral_inner_zero s).symm
    _ ≤ _ := integral_mono (integrable_inner s)
          (integrable_sup' _ H ⟨s, hs⟩ (fun s g => inner (𝕜 := ℝ) g s) (fun s _ => integrable_inner s))
          (fun g => Finset.le_sup' (fun s => inner (𝕜 := ℝ) g s) hs)

lemma gF_mono {n : ℕ} {H H' : Finset (EuclideanSpace ℝ (Fin n))} (hsub : H ⊆ H') : gF H ≤ gF H' := by
  rcases H.eq_empty_or_nonempty with h | h
  · rw [h, gF_empty]
    rcases H'.eq_empty_or_nonempty with h' | h'
    · rw [h', gF_empty]
    · exact gF_nonneg h'
  · rw [gF_eq h, gF_eq (h.mono hsub)]
    exact integral_mono
      (integrable_sup' _ H h (fun s g => inner (𝕜 := ℝ) g s) (fun s _ => integrable_inner s))
      (integrable_sup' _ H' (h.mono hsub) (fun s g => inner (𝕜 := ℝ) g s) (fun s _ => integrable_inner s))
      (fun g => Finset.sup'_mono _ hsub h)

lemma abs_integrable_of_psi {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (h : HighDimProb.Concentration.subgaussianNorm P Z < ⊤) : Integrable (fun ω => |Z ω|) P := by
  unfold HighDimProb.Concentration.subgaussianNorm at h
  simp only [iInf_lt_iff] at h
  obtain ⟨t, ht, hi, -, -⟩ := h
  have heq : (fun ω => |Z ω|) =
      (fun x => t * Real.sqrt (Real.log x)) ∘ (fun ω => Real.exp ((Z ω) ^ 2 / t ^ 2)) := by
    funext ω
    simp only [Function.comp, Real.log_exp]
    rw [Real.sqrt_div (sq_nonneg (Z ω)), Real.sqrt_sq_eq_abs, Real.sqrt_sq ht.le]
    field_simp
  have hmeas : AEStronglyMeasurable (fun ω => |Z ω|) P := by
    rw [heq]
    exact ((measurable_const.mul Real.measurable_log.sqrt).comp_aemeasurable
      hi.aemeasurable).aestronglyMeasurable
  refine (hi.const_mul t).mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  have h2 : (|Z ω| / t) ^ 2 = (Z ω) ^ 2 / t ^ 2 := by rw [div_pow, sq_abs]
  have hx : |Z ω| / t ≤ Real.exp ((Z ω) ^ 2 / t ^ 2) := by
    have h1 := Real.add_one_le_exp ((Z ω) ^ 2 / t ^ 2)
    nlinarith [sq_nonneg (|Z ω| / t - 1 / 2)]
  calc |Z ω| = t * (|Z ω| / t) := by field_simp
    _ ≤ t * Real.exp ((Z ω) ^ 2 / t ^ 2) := mul_le_mul_of_nonneg_left hx ht.le

set_option maxHeartbeats 1000000 in
open HighDimProb.Deviations in
theorem mdi_assembly (hC1 : MDI.SubgaussianIncrements) (hC2 : MDI.ChainingMapsBound)
    (hC4 : MDI.PartitionScheme) (hG : MDI.GaussianGrowth)
    (hSud : ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {ι : Type} [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ)
        (hXG : IsGaussianProcess X P) (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0)
        (ε : ℝ), 0 ≤ ε →
        (∀ i j, i ≠ j → ε ^ 2 ≤ ∫ ω, (X i ω - X j ω) ^ 2 ∂P) →
        c * ε * Real.sqrt (Real.log (Fintype.card ι)) ≤
          ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P →
        (∀ i, IsIsotropic P (A i)) →
        ∀ (K : ℝ≥0), (∀ i, subgaussianVectorNorm P (A i) ≤ K) →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))) (γ : ℝ),
          gaussianComplexity T = (γ : EReal) →
          expSup P (fun x : T => fun ω =>
              |Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x.1) ^ 2) -
                Real.sqrt m * ‖x.1‖|) ≤
            ((C * K ^ 2 * γ : ℝ) : EReal) := by
  obtain ⟨C1, hC1p, hC1⟩ := hC1
  obtain ⟨C2, hC2p, hC2⟩ := hC2
  obtain ⟨r, c, hr, hc, hG⟩ := hG
  obtain ⟨cS, hcSp, hS⟩ := hSud
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsl2 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hl2
  have hr0 : 0 < r := by linarith
  set Cst := 400 * C2 * C1 * r * (1 / c + 2 / (cS * Real.sqrt (Real.log 2))) with hCst
  refine ⟨Cst, by positivity, ?_⟩
  intro Ω _ P _ m n A hind hiso K hK T γ hγ
  have hJ : ∀ S : {s : Finset T // s.Nonempty},
      ∫ g, S.1.sup' S.2 (fun x => |inner (𝕜 := ℝ) g x.1|) ∂(stdGaussian _) ≤ γ := by
    intro S
    have h1 : ((∫ g, S.1.sup' S.2 (fun x => |inner (𝕜 := ℝ) g x.1|) ∂(stdGaussian _) : ℝ) : EReal) ≤
        gaussianComplexity T := by
      unfold gaussianComplexity expSup
      exact le_iSup (fun S : {s : Finset T // s.Nonempty} =>
        ((∫ g, S.1.sup' S.2 (fun x => |inner (𝕜 := ℝ) g x.1|) ∂(stdGaussian _) : ℝ) : EReal)) S
    rw [hγ] at h1; exact_mod_cast h1
  unfold expSup
  apply iSup_le
  intro S
  rw [EReal.coe_le_coe_iff]
  classical
  have hγ0 : 0 ≤ γ := by
    refine le_trans (integral_nonneg (fun g => ?_)) (hJ S)
    obtain ⟨x, hx⟩ := S.2
    exact le_trans (abs_nonneg _) (Finset.le_sup' (fun x : T => |inner (𝕜 := ℝ) g x.1|) hx)
  set P' : Finset (EuclideanSpace ℝ (Fin n)) := insert 0 (S.1.image Subtype.val) with hP'
  have h0P : (0 : EuclideanSpace ℝ (Fin n)) ∈ P' := Finset.mem_insert_self _ _
  haveI : Nonempty P' := ⟨⟨0, h0P⟩⟩
  let Y : P' → Ω → ℝ := fun p ω =>
    Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) p.1) ^ 2) - Real.sqrt m * ‖p.1‖
  have hinc : ∀ p q : P', HighDimProb.Concentration.subgaussianNorm P (fun ω => Y p ω - Y q ω) ≤
      ENNReal.ofReal ((C1 * (K : ℝ) ^ 2) * dist p q) := by
    intro p q
    have := hC1 P A hind hiso K hK p.1 q.1
    rw [Subtype.dist_eq, dist_eq_norm]
    exact this
  let F : Finset P' → ℝ := fun B => gF (B.image Subtype.val)
  have hFm : ∀ B B' : Finset P', B ⊆ B' → F B ≤ F B' := fun B B' h =>
    gF_mono (Finset.image_subset_image h)
  have hFn : ∀ B : Finset P', B.Nonempty → 0 ≤ F B := fun B h => gF_nonneg (h.image _)
  have hFG : ∀ (m' : ℕ), 2 ≤ m' → ∀ (a : ℝ), 0 < a → ∀ (t : Fin m' → P') (H : Fin m' → Finset P'),
      (∀ l l', l ≠ l' → a ≤ dist (t l) (t l')) → (∀ l, ∀ s ∈ H l, dist s (t l) ≤ a / r) →
      (∀ l, (H l).Nonempty) →
      ∃ l, c * a * Real.sqrt (Real.log m') + F (H l) ≤ F (Finset.univ.biUnion H) := by
    intro m' hm' a ha t H hsep hball hne
    obtain ⟨l, hl⟩ := hG m' hm' a ha (fun l => (t l).1) (fun l => (H l).image Subtype.val)
      (fun l l' h => by have := hsep l l' h; rwa [Subtype.dist_eq] at this)
      (fun l s hs => by
        obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
        have := hball l s' hs'; rwa [Subtype.dist_eq] at this)
      (fun l => (hne l).image _)
    refine ⟨l, ?_⟩
    have he : (Finset.univ.biUnion H).image Subtype.val =
        Finset.univ.biUnion (fun l => (H l).image Subtype.val) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, ⟨l, hl⟩, rfl⟩; exact ⟨l, x, hl, rfl⟩
      · rintro ⟨l, x, hl, rfl⟩; exact ⟨x, ⟨l, hl⟩, rfl⟩
    show _ ≤ gF ((Finset.univ.biUnion H).image Subtype.val)
    rw [he]; exact hl
  obtain ⟨t0, π, hπ0, hcard, hstab, hsum⟩ := hC4 F r c hr hc hFm hFn hFG
  set S0 := 200 * r * (F Finset.univ / c + Metric.diam (Set.univ : Set P')) with hS0
  have hchain := hC2 P Y (C1 * (K : ℝ) ^ 2) (by positivity) hinc t0 π hπ0 hcard hstab S0 hsum
  let M : Ω → ℝ := fun ω => Finset.univ.sup' ⟨t0, Finset.mem_univ _⟩ (fun t => |Y t ω - Y t0 ω|)
  have hMi : Integrable M P := integrable_sup' P _ _ (fun t ω => |Y t ω - Y t0 ω|)
    (fun t _ => abs_integrable_of_psi (lt_of_le_of_lt (hinc t t0) ENNReal.ofReal_lt_top))
  have hY0 : ∀ ω, Y ⟨0, h0P⟩ ω = 0 := fun ω => by simp [Y]
  have hpt : ∀ ω, S.1.sup' S.2 (fun x => |Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x.1) ^ 2) -
      Real.sqrt m * ‖x.1‖|) ≤ 2 * M ω := by
    intro ω
    apply Finset.sup'_le
    intro x hx
    have hxP : x.1 ∈ P' := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
    have h1 : |Y ⟨x.1, hxP⟩ ω - Y t0 ω| ≤ M ω :=
      Finset.le_sup' (fun t => |Y t ω - Y t0 ω|) (Finset.mem_univ _)
    have h2 : |Y ⟨0, h0P⟩ ω - Y t0 ω| ≤ M ω :=
      Finset.le_sup' (fun t => |Y t ω - Y t0 ω|) (Finset.mem_univ _)
    rw [hY0, zero_sub, abs_neg] at h2
    have h3 : |Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x.1) ^ 2) - Real.sqrt m * ‖x.1‖| =
        |Y ⟨x.1, hxP⟩ ω| := rfl
    rw [h3]
    have h4 := abs_sub_le (Y ⟨x.1, hxP⟩ ω) (Y t0 ω) 0
    simp only [sub_zero] at h4
    linarith
  have hint : ∫ ω, S.1.sup' S.2 (fun x => |Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x.1) ^ 2) -
      Real.sqrt m * ‖x.1‖|) ∂P ≤ 2 * (C2 * (C1 * (K : ℝ) ^ 2) * S0) := by
    calc _ ≤ ∫ ω, 2 * M ω ∂P := integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun ω => by
            obtain ⟨x, hx⟩ := S.2
            exact le_trans (abs_nonneg _) (Finset.le_sup' (fun x : T =>
              |Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x.1) ^ 2) - Real.sqrt m * ‖x.1‖|) hx))
          (hMi.const_mul 2) (Filter.Eventually.of_forall hpt)
      _ = 2 * ∫ ω, M ω ∂P := integral_const_mul _ _
      _ ≤ 2 * (C2 * (C1 * (K : ℝ) ^ 2) * S0) := mul_le_mul_of_nonneg_left hchain (by norm_num)
  have hUimg : (Finset.univ : Finset P').image Subtype.val = P' := by ext y; simp
  have hFγ : F Finset.univ ≤ γ := by
    simp only [F]; rw [hUimg, gF_eq ⟨0, h0P⟩]
    refine le_trans (integral_mono
      (integrable_sup' _ P' ⟨0, h0P⟩ (fun s g => inner (𝕜 := ℝ) g s) (fun s _ => integrable_inner s))
      (integrable_sup' _ S.1 S.2 (fun x g => |inner (𝕜 := ℝ) g x.1|) (fun x _ => (integrable_inner x.1).abs))
      ?_) (hJ S)
    intro g
    apply Finset.sup'_le
    intro s hs
    rcases Finset.mem_insert.mp hs with hs0 | hs'
    · rw [hs0, inner_zero_right]
      obtain ⟨x, hx⟩ := S.2
      exact le_trans (abs_nonneg _) (Finset.le_sup' (fun x : T => |inner (𝕜 := ℝ) g x.1|) hx)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs'
      exact le_trans (le_abs_self _) (Finset.le_sup' (fun x : T => |inner (𝕜 := ℝ) g x.1|) hx)
  have hnorm : ∀ x ∈ S.1, ‖x.1‖ ≤ γ / (cS * Real.sqrt (Real.log 2)) := by
    intro x hx
    let v : Fin 2 → EuclideanSpace ℝ (Fin n) := fun i => if i = 0 then x.1 else 0
    have h01 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by decide
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hv0 : v 0 = x.1 := if_pos rfl
    have hv1 : v 1 = 0 := if_neg h10
    have hsep : ∀ i j : Fin 2, i ≠ j → ‖x.1‖ ^ 2 ≤ ∫ g,
        (inner (𝕜 := ℝ) g (v i) - inner (𝕜 := ℝ) g (v j)) ^ 2 ∂(stdGaussian _) := by
      intro i j hij
      have h1 : ∫ g, (inner (𝕜 := ℝ) g (v i) - inner (𝕜 := ℝ) g (v j)) ^ 2 ∂(stdGaussian _) =
          ‖v i - v j‖ ^ 2 := by
        rw [← second_moment]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => by simp only [inner_sub_right])
      rw [h1]
      rcases h01 i with rfl | rfl <;> rcases h01 j with rfl | rfl
      · exact absurd rfl hij
      · rw [hv0, hv1, sub_zero]
      · rw [hv0, hv1, zero_sub, norm_neg]
      · exact absurd rfl hij
    have hsud := hS (stdGaussian (EuclideanSpace ℝ (Fin n)))
      (fun (i : Fin 2) (g : EuclideanSpace ℝ (Fin n)) => inner (𝕜 := ℝ) g (v i))
      (isGP_inner v) (fun i => integral_inner_zero _) ‖x.1‖ (norm_nonneg _) hsep
    rw [Fintype.card_fin] at hsud
    have hle : ∫ g, Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin 2 => inner (𝕜 := ℝ) g (v i)) ∂(stdGaussian _) ≤ γ := by
      refine le_trans (integral_mono
        (integrable_sup' _ _ _ (fun (i : Fin 2) g => inner (𝕜 := ℝ) g (v i))
          (fun i _ => integrable_inner _))
        (integrable_sup' _ S.1 S.2 (fun x g => |inner (𝕜 := ℝ) g x.1|)
          (fun x _ => (integrable_inner x.1).abs)) ?_) (hJ S)
      intro g
      apply Finset.sup'_le
      intro i _
      have hb : |inner (𝕜 := ℝ) g x.1| ≤ S.1.sup' S.2 (fun x => |inner (𝕜 := ℝ) g x.1|) :=
        Finset.le_sup' (fun x : T => |inner (𝕜 := ℝ) g x.1|) hx
      rcases h01 i with rfl | rfl
      · show inner (𝕜 := ℝ) g (v 0) ≤ _
        rw [hv0]; exact le_trans (le_abs_self _) hb
      · show inner (𝕜 := ℝ) g (v 1) ≤ _
        rw [hv1, inner_zero_right]; exact le_trans (abs_nonneg _) hb
    rw [le_div_iff₀ (by positivity)]
    have hfin : cS * ‖x.1‖ * Real.sqrt (Real.log ((2 : ℕ) : ℝ)) ≤ γ := hsud.trans hle
    rw [Nat.cast_ofNat] at hfin
    calc ‖x.1‖ * (cS * Real.sqrt (Real.log 2)) = cS * ‖x.1‖ * Real.sqrt (Real.log 2) := by ring
      _ ≤ γ := hfin
  have hbd0 : 0 ≤ γ / (cS * Real.sqrt (Real.log 2)) := div_nonneg hγ0 (by positivity)
  have hdiam : Metric.diam (Set.univ : Set P') ≤ 2 * (γ / (cS * Real.sqrt (Real.log 2))) := by
    apply Metric.diam_le_of_forall_dist_le (by linarith)
    intro p _ q _
    rw [Subtype.dist_eq, dist_eq_norm]
    have hp : ∀ p : P', ‖p.1‖ ≤ γ / (cS * Real.sqrt (Real.log 2)) := by
      intro p
      rcases Finset.mem_insert.mp p.2 with h | h
      · rw [h, norm_zero]; exact hbd0
      · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h
        rw [← hxe]; exact hnorm x hx
    have := norm_sub_le p.1 q.1
    linarith [hp p, hp q]
  have hS0b : S0 ≤ 200 * r * (γ / c + 2 * (γ / (cS * Real.sqrt (Real.log 2)))) := by
    have : F Finset.univ / c ≤ γ / c := div_le_div_of_nonneg_right hFγ hc.le
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hK0 : 0 ≤ C2 * (C1 * (K : ℝ) ^ 2) := by positivity
  calc _ ≤ 2 * (C2 * (C1 * (K : ℝ) ^ 2) * S0) := hint
    _ ≤ 2 * (C2 * (C1 * (K : ℝ) ^ 2) *
          (200 * r * (γ / c + 2 * (γ / (cS * Real.sqrt (Real.log 2)))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS0b hK0) (by norm_num)
    _ = Cst * (K : ℝ) ^ 2 * γ := by rw [hCst]; ring

end Assembly

end MDI3

end SecR


open MeasureTheory ProbabilityTheory HighDimProb.Deviations in
open scoped ENNReal NNReal in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P →
        (∀ i, IsIsotropic P (A i)) →
        ∀ (K : ℝ≥0), (∀ i, subgaussianVectorNorm P (A i) ≤ K) →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))) (γ : ℝ),
          gaussianComplexity T = (γ : EReal) →
          expSup P (fun x : T => fun ω =>
              |Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x.1) ^ 2) -
                Real.sqrt m * ‖x.1‖|) ≤
            ((C * K ^ 2 * γ : ℝ) : EReal) := by
  have hC2 : MDI.ChainingMapsBound := by
    refine ⟨5, by norm_num, ?_⟩
    intro Ω _ P _ T _ _ _ X K hK hX t0 π hπ0 hcard hstab S hS
    exact MDI.chaining_maps P X K hK hX t0 π hπ0 hcard hstab S hS
  have hC4 : MDI.PartitionScheme := by
    intro T _ _ _ _ F r c hr hc hmono hnn hG
    exact MDI.partition_scheme F r c hr hc hmono hnn hG
  have hconc : MDI3.ConcHyp := by
    intro ι _ f L hL hLip t ht
    exact GaussianMatrix.gaussian_concentration_vector f L hL hLip t ht
  have hsud := HighDimProb.RandomProcesses.sudakov_minoration_finite_separated
  exact MDI3.mdi_assembly C1.increments hC2 hC4 (MDI3.gaussian_growth hconc hsud) hsud
