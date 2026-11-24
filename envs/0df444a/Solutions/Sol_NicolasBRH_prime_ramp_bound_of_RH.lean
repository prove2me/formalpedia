-- Prove2me | solution 1 for NicolasBRH.prime_ramp_bound_of_RH
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-24T04:22:47.762924+00:00
-- url     : https://prove2.me/submissions/9c9daae6-c848-4927-a5b1-8df65f9b0c8a

import Theorems.Thm_LandauCriterion_sum_multiplicity_div_normSq_zeros_le
import Theorems.Thm_MasulloRH_prime_ramp_integrated_explicit_formula
import Theorems.Thm_LandauCriterion_psi_error_of_riemannHypothesis
import Mathlib

set_option autoImplicit false
open Finset ArithmeticFunction MeasureTheory Filter Topology

namespace NicZ

noncomputable def Mfun (x : ℝ) : ℝ :=
  ((∑ n ∈ range (⌊x⌋₊+1), vonMangoldt n * max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)) / x

noncomputable def βc : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

noncomputable def Kt (x : ℝ) (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) : ℂ :=
  (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (x:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1))

lemma re_half (hRH : RiemannHypothesis) (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) :
    ρ.val.re = 1/2 := by
  obtain ⟨hz, h0, h1, -⟩ := ρ.property
  apply hRH ρ.val hz
  · rintro ⟨n, hn⟩
    have : ρ.val.re = -2 * ((n:ℝ) + 1) := by rw [hn]; simp
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · intro h; rw [h] at h1; simp at h1

lemma norm_Kt (hRH : RiemannHypothesis) (x : ℝ) (hx : 0 < x)
    (ρ : MasulloRH.ZetaZerosInTraceStrip (1/2)) :
    ‖Kt x ρ‖ = x ^ (-(1/2:ℝ)) * ((analyticOrderNatAt riemannZeta ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  have hre := re_half hRH ρ
  have hne : ρ.val ≠ 0 := by
    intro h; rw [h] at hre; simp at hre
  have hn1 : ‖ρ.val - 1‖ = ‖ρ.val‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply, hre]
    ring
  rw [Kt, norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, hn1]
  have : (ρ.val - 1).re = -(1/2) := by simp [hre]; norm_num
  rw [this]
  simp only [Complex.norm_natCast]
  have hp : 0 < ‖ρ.val‖ := norm_pos_iff.mpr hne
  field_simp

lemma summable_Kt (x : ℝ) (hx : 1 ≤ x) : Summable (fun ρ => ‖Kt x ρ‖) := by
  have h := @MasulloRH.prime_ramp_integrated_explicit_formula
  dsimp only at h
  exact h.1 x hx

lemma tsum_norm_Kt_le (hRH : RiemannHypothesis) (x : ℝ) (hx : 1 ≤ x) :
    ∑' ρ, ‖Kt x ρ‖ ≤ βc * x ^ (-(1/2:ℝ)) := by
  have hx0 : 0 < x := by linarith
  apply (summable_Kt x hx).tsum_le_of_sum_le
  intro s
  simp_rw [norm_Kt hRH x hx0]
  rw [← Finset.mul_sum, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hL := LandauCriterion.sum_multiplicity_div_normSq_zeros_le hRH
    (s.map ⟨Subtype.val, Subtype.val_injective⟩) (by
      intro ρ hρ
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hρ
      obtain ⟨r, -, rfl⟩ := hρ
      exact ⟨r.property.1, r.property.2.1⟩)
  rw [Finset.sum_map] at hL
  simpa [βc] using hL

lemma abs_re_tsum_Kt_le (hRH : RiemannHypothesis) (x : ℝ) (hx : 1 ≤ x) :
    |(∑' ρ, Kt x ρ).re| ≤ βc * x ^ (-(1/2:ℝ)) :=
  (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm (summable_Kt x hx)).trans
    (tsum_norm_Kt_le hRH x hx))

noncomputable def cfun (t : ℝ) : ℝ := Real.log (2*Real.pi) + (1/2) * Real.log (1 - t^(-2:ℝ))

lemma cfun_bounds (t : ℝ) (ht : 2 ≤ t) : 0 ≤ cfun t ∧ cfun t ≤ Real.log (2*Real.pi) := by
  have ht0 : 0 < t := by linarith
  have h1 : t^(-2:ℝ) ≤ 1/4 := by
    rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : 0 < t^(-2:ℝ) := Real.rpow_pos_of_pos ht0 _
  have h3 : Real.log (3/4) ≤ Real.log (1 - t^(-2:ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h3' : Real.log (1 - t^(-2:ℝ)) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h4 : Real.log 6 ≤ Real.log (2*Real.pi) :=
    Real.log_le_log (by norm_num) (by linarith [Real.pi_gt_three])
  have h5 : Real.log (3/4) = Real.log 3 - Real.log 4 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h7 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have h8 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h9 := Real.log_two_gt_d9
  unfold cfun
  constructor <;> nlinarith

lemma cfun_cont (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    ContinuousOn (fun t => cfun t / t^2) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have h1 : t^(-2:ℝ) < 1 := by
    rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_lt_one_iff₀]; right; nlinarith [ht.1]
  apply ContinuousAt.continuousWithinAt
  unfold cfun
  apply ContinuousAt.div _ (continuousAt_id.pow 2) (pow_ne_zero 2 ht0.ne')
  apply ContinuousAt.add continuousAt_const
  apply ContinuousAt.mul continuousAt_const
  apply ContinuousAt.log _ (by linarith)
  apply ContinuousAt.sub continuousAt_const
  exact Real.continuousAt_rpow_const _ _ (Or.inl ht0.ne')

/-- Masullo's identity, real form. -/
theorem M_identity (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    Mfun b - Mfun a = -((∑' ρ, Kt b ρ).re - (∑' ρ, Kt a ρ).re) - ∫ t in a..b, cfun t / t^2 := by
  have h := @MasulloRH.prime_ramp_integrated_explicit_formula
  dsimp only at h
  have hE := h.2 a b ha hab
  have hsa : Summable (fun ρ => Kt a ρ) := (summable_Kt a (by linarith)).of_norm
  have hsb : Summable (fun ρ => Kt b ρ) := (summable_Kt b (by linarith)).of_norm
  have hsplit : (∑' ρ : MasulloRH.ZetaZerosInTraceStrip (1/2),
      ((analyticOrderNatAt riemannZeta ρ.val : ℂ) * (b:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)) -
        (analyticOrderNatAt riemannZeta ρ.val : ℂ) * (a:ℂ)^(ρ.val-1)/(ρ.val*(ρ.val-1)))) =
      (∑' ρ, Kt b ρ) - ∑' ρ, Kt a ρ := (hsb.tsum_sub hsa)
  rw [hsplit] at hE
  have hint : (∫ t in a..b, ((Real.log (2*Real.pi)+(1/2)*Real.log (1-t^(-2:ℝ)):ℝ):ℂ)/(t:ℂ)^2) =
      ((∫ t in a..b, cfun t / t^2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext t; unfold cfun; push_cast; ring
  rw [hint] at hE
  have hre := congrArg Complex.re hE
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
  have hMb : Mfun b = ((∑ n ∈ range (⌊b⌋₊+1), vonMangoldt n * max (b/(n:ℝ)-1) 0) -
      b*(Real.log b-1-Real.eulerMascheroniConstant)) / b := rfl
  have hMa : Mfun a = ((∑ n ∈ range (⌊a⌋₊+1), vonMangoldt n * max (a/(n:ℝ)-1) 0) -
      a*(Real.log a-1-Real.eulerMascheroniConstant)) / a := rfl
  rw [hMb, hMa]
  linarith

lemma int_c_bounds (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, cfun t / t^2 ∧
      ∫ t in a..b, cfun t / t^2 ≤ Real.log (2*Real.pi) * (1/a - 1/b) := by
  have ha0 : 0 < a := by linarith
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact div_nonneg (cfun_bounds t (by linarith [ht.1])).1 (by positivity)
  · have hm : ∫ t in a..b, cfun t / t^2 ≤ ∫ t in a..b, Real.log (2*Real.pi) / t^2 := by
      apply intervalIntegral.integral_mono_on hab
      · exact (cfun_cont a b ha hab).intervalIntegrable
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        intro t ht; rw [Set.uIcc_of_le hab] at ht
        exact pow_ne_zero 2 (by linarith [ht.1])
      · intro t ht
        exact div_le_div_of_nonneg_right (cfun_bounds t (by linarith [ht.1])).2 (by positivity)
    have he : ∫ t in a..b, Real.log (2*Real.pi) / t^2 = Real.log (2*Real.pi) * (1/a - 1/b) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => -Real.log (2*Real.pi) / t)]
      · field_simp; ring
      · intro t ht; rw [Set.uIcc_of_le hab] at ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        have := (hasDerivAt_inv ht0).const_mul (-Real.log (2*Real.pi))
        have e1 : (fun t : ℝ => -Real.log (2*Real.pi) / t) = (fun y => -Real.log (2 * Real.pi) * y⁻¹) := by
          funext s; rw [div_eq_mul_inv]
        rw [e1]
        exact this.congr_deriv (by rw [neg_mul_neg, div_eq_mul_inv])
      · apply ContinuousOn.intervalIntegrable
        apply ContinuousOn.div continuousOn_const (continuousOn_pow 2)
        intro t ht; rw [Set.uIcc_of_le hab] at ht
        exact pow_ne_zero 2 (by linarith [ht.1])
    linarith

theorem M_diff_abs (hRH : RiemannHypothesis) (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    |Mfun b - Mfun a| ≤ βc * (a ^ (-(1/2:ℝ)) + b ^ (-(1/2:ℝ))) + Real.log (2*Real.pi) / a := by
  have hI := M_identity a b ha hab
  have hc := int_c_bounds a b ha hab
  have h1 := abs_re_tsum_Kt_le hRH a (by linarith)
  have h2 := abs_re_tsum_Kt_le hRH b (by linarith)
  have hb0 : 0 < b := by linarith
  have hl : 0 < Real.log (2*Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have h3 : Real.log (2*Real.pi) * (1/a - 1/b) ≤ Real.log (2*Real.pi) / a := by
    have : 0 < Real.log (2*Real.pi) / b := by positivity
    have e : Real.log (2*Real.pi) * (1/a - 1/b) = Real.log (2*Real.pi) / a - Real.log (2*Real.pi) / b := by ring
    linarith
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith

lemma rpow_neg_half_tendsto : Tendsto (fun b : ℝ => b ^ (-(1/2:ℝ))) atTop (𝓝 0) :=
  tendsto_rpow_neg_atTop (by norm_num)

/-- Under RH, `M` has a limit `M∞` with `|M(a) - M∞| ≤ β a^{-1/2} + log(2π)/a`. -/
theorem M_limit (hRH : RiemannHypothesis) :
    ∃ C : ℝ, Tendsto Mfun atTop (𝓝 C) ∧
      ∀ a : ℝ, 2 ≤ a → |Mfun a - C| ≤ βc * a ^ (-(1/2:ℝ)) + Real.log (2*Real.pi) / a := by
  have hβ : 0 ≤ βc := by
    have := LandauCriterion.sum_multiplicity_div_normSq_zeros_le hRH ∅ (by simp)
    simpa [βc] using this
  have hcauchy : CauchySeq Mfun := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    -- choose N with 2 β N^{-1/2} + log(2π)/N < ε
    have h1 : Tendsto (fun N : ℝ => 2 * βc * N ^ (-(1/2:ℝ)) + Real.log (2*Real.pi) / N) atTop (𝓝 0) := by
      have := ((rpow_neg_half_tendsto).const_mul (2*βc)).add
        ((tendsto_const_nhds (x := Real.log (2*Real.pi))).div_atTop tendsto_id)
      simpa using this
    obtain ⟨N, hN⟩ := (h1.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop (2:ℝ))
      |>.exists
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have h := M_diff_abs hRH N n hN.2 hn
    have hn0 : 0 < N := by linarith [hN.2]
    have hmono : n ^ (-(1/2:ℝ)) ≤ N ^ (-(1/2:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hn0 hn (by norm_num)
    nlinarith [hN.1]
  obtain ⟨C, hC⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨C, hC, fun a ha => ?_⟩
  have hlim : Tendsto (fun b => |Mfun b - Mfun a|) atTop (𝓝 (|C - Mfun a|)) :=
    ((hC.sub tendsto_const_nhds).abs)
  have hlim2 : Tendsto (fun b : ℝ => βc * (a ^ (-(1/2:ℝ)) + b ^ (-(1/2:ℝ))) + Real.log (2*Real.pi) / a)
      atTop (𝓝 (βc * (a ^ (-(1/2:ℝ)) + 0) + Real.log (2*Real.pi) / a)) :=
    ((tendsto_const_nhds.add rpow_neg_half_tendsto).const_mul βc).add tendsto_const_nhds
  have := le_of_tendsto_of_tendsto hlim hlim2 (by
    filter_upwards [eventually_ge_atTop a] with b hb
    exact M_diff_abs hRH a b ha hb)
  rw [abs_sub_comm]; simpa using this

end NicZ

namespace NicZ

lemma int_rpow_Ioi (σ : ℝ) (hσ : 0 < σ) : σ * ∫ t in Set.Ioi (1:ℝ), t ^ (-σ - 1) = 1 := by
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
  have : -σ - 1 + 1 = -σ := by ring
  rw [this]
  field_simp

lemma integrableOn_rpow (σ : ℝ) (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Set.Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one

/-- An Abelian lemma: if `S` is bounded, measurable and `S t → L`, then
`σ ∫_1^∞ S(t) t^{-σ-1} dt → L` as `σ → 0⁺`. -/
theorem abel_lim (S : ℝ → ℂ) (hm : AEStronglyMeasurable S (volume.restrict (Set.Ioi 1)))
    (B : ℝ) (hB : ∀ t, ‖S t‖ ≤ B) (L : ℂ) (hS : Tendsto S atTop (𝓝 L)) :
    Tendsto (fun σ : ℝ => (σ:ℂ) * ∫ t in Set.Ioi (1:ℝ), S t * ((t ^ (-σ - 1) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- tail: |S t - L| ≤ ε/2 for t ≥ T
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp hS) (ε/2) (by linarith)
  set T' := max T 2 with hT'
  have hT'1 : (1:ℝ) < T' := by rw [hT']; exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set K := B + ‖L‖ with hK
  have hK0 : 0 ≤ K := by positivity
  -- choose σ small
  have hσev : ∀ᶠ σ : ℝ in 𝓝[>] 0, 0 < σ ∧ σ * (K * (T' - 1)) < ε/2 := by
    have h1 : ∀ᶠ σ : ℝ in 𝓝[>] 0, 0 < σ := self_mem_nhdsWithin
    have h2 : Tendsto (fun σ : ℝ => σ * (K * (T' - 1))) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun σ : ℝ => σ * (K * (T' - 1))) := by fun_prop
      have := (hc.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      simpa using this
    exact h1.and (h2.eventually (gt_mem_nhds (by linarith)))
  filter_upwards [hσev] with σ ⟨hσ, hσs⟩
  rw [dist_eq_norm]
  have hint := integrableOn_rpow σ hσ
  have hSi : IntegrableOn (fun t => S t * ((t ^ (-σ - 1) : ℝ) : ℂ)) (Set.Ioi 1) := by
    have : Integrable (fun t : ℝ => ((t ^ (-σ - 1) : ℝ) : ℂ)) (volume.restrict (Set.Ioi 1)) :=
      hint.ofReal
    exact this.bdd_mul hm (Filter.Eventually.of_forall hB)
  have hLi : IntegrableOn (fun t : ℝ => L * ((t ^ (-σ - 1) : ℝ) : ℂ)) (Set.Ioi 1) :=
    hint.ofReal.const_mul L
  -- σ ∫ L t^{-σ-1} = L
  have hL1 : (σ:ℂ) * ∫ t in Set.Ioi (1:ℝ), L * ((t ^ (-σ - 1) : ℝ) : ℂ) = L := by
    rw [integral_const_mul, integral_complex_ofReal]
    have := int_rpow_Ioi σ hσ
    calc (σ:ℂ) * (L * ((∫ t in Set.Ioi (1:ℝ), t ^ (-σ - 1) : ℝ) : ℂ))
        = L * (((σ * ∫ t in Set.Ioi (1:ℝ), t ^ (-σ - 1)) : ℝ) : ℂ) := by push_cast; ring
      _ = L := by rw [this]; simp
  have hdiff : (σ:ℂ) * (∫ t in Set.Ioi (1:ℝ), S t * ((t ^ (-σ - 1) : ℝ) : ℂ)) - L =
      (σ:ℂ) * ∫ t in Set.Ioi (1:ℝ), (S t - L) * ((t ^ (-σ - 1) : ℝ) : ℂ) := by
    conv_lhs => rw [← hL1]
    rw [← mul_sub, ← integral_sub hSi hLi]
    congr 2; funext t; ring
  rw [hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ.le]
  -- bound the integral of the norm
  have hDi : IntegrableOn (fun t => (S t - L) * ((t ^ (-σ - 1) : ℝ) : ℂ)) (Set.Ioi 1) := by
    refine (hSi.sub hLi).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]; ring
  have hnorm := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi (1:ℝ)))
    (fun t => (S t - L) * ((t ^ (-σ - 1) : ℝ) : ℂ))
  -- pointwise bound: ‖(S t - L) t^{-σ-1}‖ ≤ g t
  set g : ℝ → ℝ := fun t => Set.indicator (Set.Ioc 1 T') (fun t => K * t ^ (-σ - 1)) t +
      ε/2 * t ^ (-σ - 1)
  have hind : IntegrableOn (fun t => Set.indicator (Set.Ioc 1 T') (fun t => K * t ^ (-σ - 1)) t)
      (Set.Ioi 1) := (hint.const_mul K).indicator measurableSet_Ioc
  have hgi : IntegrableOn g (Set.Ioi 1) := hind.add (hint.const_mul _)
  have hpt : ∀ t ∈ Set.Ioi (1:ℝ), ‖(S t - L) * ((t ^ (-σ - 1) : ℝ) : ℂ)‖ ≤ g t := by
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    have hp : 0 ≤ t ^ (-σ - 1) := Real.rpow_nonneg ht0.le _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp]
    simp only [g]
    by_cases hc : t ≤ T'
    · have hmem : t ∈ Set.Ioc 1 T' := ⟨ht, hc⟩
      simp only [Set.indicator_of_mem hmem]
      have : ‖S t - L‖ ≤ K := (norm_sub_le _ _).trans (by rw [hK]; linarith [hB t])
      nlinarith
    · have hmem : t ∉ Set.Ioc 1 T' := fun h => hc h.2
      simp only [Set.indicator_of_notMem hmem, zero_add]
      have htT : T ≤ t := le_trans (le_max_left _ _) (le_of_lt (not_le.mp hc))
      have := hT t htT
      rw [dist_eq_norm] at this
      nlinarith
  have hint_le : ∫ t in Set.Ioi (1:ℝ), ‖(S t - L) * ((t ^ (-σ - 1) : ℝ) : ℂ)‖ ≤
      ∫ t in Set.Ioi (1:ℝ), g t :=
    setIntegral_mono_on hDi.norm hgi measurableSet_Ioi hpt
  have hg_eq : ∫ t in Set.Ioi (1:ℝ), g t =
      (∫ t in Set.Ioc (1:ℝ) T', K * t ^ (-σ - 1)) + ε/2 * ∫ t in Set.Ioi (1:ℝ), t ^ (-σ - 1) := by
    simp only [g]
    rw [integral_add hind (hint.const_mul _), integral_const_mul, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self]
  have hIoc : ∫ t in Set.Ioc (1:ℝ) T', K * t ^ (-σ - 1) ≤ K * (T' - 1) := by
    have hle : ∫ t in Set.Ioc (1:ℝ) T', K * t ^ (-σ - 1) ≤ ∫ t in Set.Ioc (1:ℝ) T', K := by
      apply setIntegral_mono_on
      · exact (hint.mono_set Set.Ioc_subset_Ioi_self).const_mul K
      · exact integrableOn_const (by simp) (by simp)
      · exact measurableSet_Ioc
      · intro t ht
        have ht1 : 1 ≤ t := le_of_lt ht.1
        have : t ^ (-σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
        nlinarith
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hT'1.le, smul_eq_mul] at hle
    linarith [mul_comm (T' - 1) K]
  have hI1 := int_rpow_Ioi σ hσ
  calc σ * ‖∫ t in Set.Ioi (1:ℝ), (S t - L) * ((t ^ (-σ - 1) : ℝ) : ℂ)‖
      ≤ σ * ∫ t in Set.Ioi (1:ℝ), g t :=
        mul_le_mul_of_nonneg_left (hnorm.trans hint_le) hσ.le
    _ = σ * (∫ t in Set.Ioc (1:ℝ) T', K * t ^ (-σ - 1)) + ε/2 * (σ * ∫ t in Set.Ioi (1:ℝ), t ^ (-σ - 1)) := by
        rw [hg_eq]; ring
    _ ≤ σ * (K * (T' - 1)) + ε/2 * 1 := by
        rw [hI1]; gcongr
    _ < ε := by nlinarith

end NicZ
namespace NicZ
lemma Mfun_eq (t : ℝ) (ht : 1 ≤ t) :
    Mfun t = (∑ k ∈ Icc 1 ⌊t⌋₊, (vonMangoldt k : ℝ) / k) - Chebyshev.psi t / t - Real.log t + 1 +
      Real.eulerMascheroniConstant := by
  have ht0 : 0 < t := by linarith
  have h1 : ∑ n ∈ range (⌊t⌋₊+1), vonMangoldt n * max (t/(n:ℝ)-1) 0 =
      ∑ k ∈ Icc 1 ⌊t⌋₊, (vonMangoldt k : ℝ) * (t / k - 1) := by
    have hs : range (⌊t⌋₊+1) = insert 0 (Icc 1 ⌊t⌋₊) := by
      ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [hs, Finset.sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    · intro k hk
      simp only [mem_Icc] at hk
      have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk.1
      have hkt : (k:ℝ) ≤ t := le_trans (by exact_mod_cast hk.2) (Nat.floor_le ht0.le)
      rw [max_eq_left]
      rw [sub_nonneg, le_div_iff₀ (by linarith)]; linarith
  have h2 : ∑ k ∈ Icc 1 ⌊t⌋₊, (vonMangoldt k : ℝ) * (t / k - 1) =
      t * (∑ k ∈ Icc 1 ⌊t⌋₊, (vonMangoldt k : ℝ) / k) - Chebyshev.psi t := by
    rw [Chebyshev.psi, Finset.mul_sum]
    have : Finset.Ioc 0 ⌊t⌋₊ = Icc 1 ⌊t⌋₊ := by ext k; simp; omega
    rw [this, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  unfold Mfun; rw [h1, h2]
  field_simp
  ring
end NicZ

open scoped LSeries.notation
namespace NicZ

noncomputable def fco (k : ℕ) : ℂ := (((vonMangoldt k : ℝ) - 1) / k : ℝ)

lemma fco_sum (n : ℕ) : ∑ k ∈ Icc 1 n, fco k =
    (((∑ k ∈ Icc 1 n, (vonMangoldt k : ℝ) / k) - harmonic n : ℝ) : ℂ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [fco]; push_cast; ring

lemma psi_div_tendsto (hRH : RiemannHypothesis) :
    Tendsto (fun t : ℝ => Chebyshev.psi t / t) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := LandauCriterion.psi_error_of_riemannHypothesis hRH
  have hlog : Tendsto (fun t : ℝ => Real.log t ^ 2 / Real.sqrt t) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
      (Real.tendsto_sqrt_atTop)
    have h4 := h.const_mul 4
    rw [mul_zero] at h4
    apply h4.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    simp only [Function.comp, one_mul, add_zero]
    rw [Real.log_sqrt ht.le]; ring
  have h2 : Tendsto (fun t : ℝ => C * (Real.log t ^ 2 / Real.sqrt t)) atTop (𝓝 0) := by
    simpa using hlog.const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun t => norm_nonneg _)) _ h2
  filter_upwards [eventually_ge_atTop (2:ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  rw [Real.norm_eq_abs, show Chebyshev.psi t / t - 1 = (Chebyshev.psi t - t) / t by field_simp,
    abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  have := hC t ht
  calc |Chebyshev.psi t - t| ≤ C * Real.sqrt t * Real.log t ^ 2 := this
    _ = C * (Real.log t ^ 2 / Real.sqrt t) * t := by
      rw [show C * (Real.log t ^ 2 / Real.sqrt t) * t =
        C * (Real.log t ^ 2 / Real.sqrt t) * (Real.sqrt t * Real.sqrt t) by rw [hss]]
      field_simp

theorem M_limit_zero (hRH : RiemannHypothesis) (C : ℝ) (hC : Tendsto Mfun atTop (𝓝 C)) : C = 0 := by
  set γ := Real.eulerMascheroniConstant
  -- S(t) := ∑_{k ≤ ⌊t⌋} fco k
  set S : ℝ → ℂ := fun t => ∑ k ∈ Icc 1 ⌊t⌋₊, fco k with hSdef
  have hSre : ∀ t : ℝ, 1 ≤ t → S t = ((Mfun t + Chebyshev.psi t / t - 1 - γ +
      (Real.log t - Real.log ⌊t⌋₊) - (harmonic ⌊t⌋₊ - Real.log ⌊t⌋₊) : ℝ) : ℂ) := by
    intro t ht
    simp only [hSdef, fco_sum, Mfun_eq t ht]
    congr 1; ring
  have hlim : Tendsto S atTop (𝓝 ((C + 1 - 1 - γ + 0 - γ : ℝ) : ℂ)) := by
    have hfl : Tendsto (fun t : ℝ => Real.log t - Real.log ⌊t⌋₊) atTop (𝓝 0) := by
      have h := (tendsto_nat_floor_div_atTop (R := ℝ)).log one_ne_zero
      rw [Real.log_one] at h
      have h2 := h.neg
      rw [neg_zero] at h2
      apply h2.congr'
      filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
      have hf : (0:ℝ) < ⌊t⌋₊ := by exact_mod_cast Nat.floor_pos.mpr ht
      rw [Real.log_div hf.ne' (by linarith)]; ring
    have hh : Tendsto (fun t : ℝ => (harmonic ⌊t⌋₊ : ℝ) - Real.log ⌊t⌋₊) atTop (𝓝 γ) :=
      Real.tendsto_harmonic_sub_log.comp tendsto_nat_floor_atTop
    have hall := ((((hC.add (psi_div_tendsto hRH)).sub (tendsto_const_nhds (x := (1:ℝ)))).sub
      (tendsto_const_nhds (x := γ))).add hfl).sub hh
    have hall' := (Complex.continuous_ofReal.tendsto _).comp hall
    apply hall'.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    rw [hSre t ht]; rfl
  -- boundedness and measurability
  have hbdd : ∃ B, ∀ t, ‖S t‖ ≤ B := by
    have hn : Tendsto (fun n : ℕ => ∑ k ∈ Icc 1 n, fco k) atTop
        (𝓝 ((C + 1 - 1 - γ + 0 - γ : ℝ) : ℂ)) := by
      have := hlim.comp tendsto_natCast_atTop_atTop
      apply this.congr
      intro n; simp [hSdef, Nat.floor_natCast]
    obtain ⟨B, hB⟩ := hn.norm.bddAbove_range
    refine ⟨B, fun t => ?_⟩
    exact hB ⟨⌊t⌋₊, rfl⟩
  obtain ⟨B, hB⟩ := hbdd
  have hmeas : Measurable S := by
    have : S = (fun n : ℕ => ∑ k ∈ Icc 1 n, fco k) ∘ (fun t : ℝ => ⌊t⌋₊) := rfl
    rw [this]
    exact measurable_from_nat.comp Nat.measurable_floor
  have habel := abel_lim S hmeas.aestronglyMeasurable B hB _ hlim
  -- L-series side
  have hLs : ∀ σ : ℝ, 0 < σ → LSeries fco σ =
      (σ:ℂ) * ∫ t in Set.Ioi (1:ℝ), S t * ((t ^ (-σ - 1) : ℝ) : ℂ) := by
    intro σ hσ
    have hsum : LSeriesSummable fco σ := by
      have h1 : LSeriesSummable (↗vonMangoldt - 1) ((σ:ℂ) + 1) :=
        (LSeriesSummable_vonMangoldt (by simp; linarith)).sub
          (LSeriesSummable_one_iff.mpr (by simp; linarith))
      unfold LSeriesSummable at h1 ⊢
      apply h1.congr
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
      rw [Complex.cpow_add _ _ hn', Complex.cpow_one]
      simp only [fco, Pi.sub_apply, Pi.one_apply]
      push_cast
      field_simp
    have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, fco k) =O[atTop] fun n : ℕ => (n:ℝ) ^ (0:ℝ) := by
      simp only [Real.rpow_zero]
      apply Asymptotics.isBigO_of_le' (c := B)
      intro n
      have := hB n
      simp only [hSdef, Nat.floor_natCast] at this
      simpa using this
    rw [LSeries_eq_mul_integral fco le_rfl (by simpa using hσ) hsum hO]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [hSdef]
    congr 1
    rw [Complex.ofReal_cpow (by linarith [ht.out] : (0:ℝ) ≤ t)]
    congr 1; push_cast; ring
  have hL1 : Tendsto (fun σ : ℝ => LSeries fco σ) (𝓝[>] 0) (𝓝 ((C + 1 - 1 - γ + 0 - γ : ℝ) : ℂ)) := by
    apply habel.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hLs σ hσ).symm
  -- zeta side
  have hz : ∀ σ : ℝ, 0 < σ → LSeries fco σ =
      -(deriv riemannZeta (1 + σ) / riemannZeta (1 + σ)) - riemannZeta (1 + σ) := by
    intro σ hσ
    have hre : 1 < ((1:ℂ) + σ).re := by simp; linarith
    rw [← neg_div, ← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre, ← LSeries_one_eq_riemannZeta hre]
    rw [← LSeries_sub (LSeriesSummable_vonMangoldt hre) (LSeriesSummable_one_iff.mpr hre)]
    unfold LSeries
    apply tsum_congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hn' : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    rw [add_comm (1:ℂ), Complex.cpow_add _ _ hn', Complex.cpow_one]
    simp only [fco, Pi.sub_apply, Pi.one_apply]
    push_cast
    field_simp
  have hmap : Tendsto (fun σ : ℝ => (1:ℂ) + σ) (𝓝[>] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have : Tendsto (fun σ : ℝ => (1:ℂ) + σ) (𝓝 0) (𝓝 1) := by
        have hc : Continuous (fun σ : ℝ => (1:ℂ) + σ) := by fun_prop
        have := hc.tendsto (0:ℝ)
        simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left, Complex.ofReal_eq_zero]
      exact ne_of_gt hσ
  have hA := (Asymptotics.isLittleO_one_iff (F := ℂ)).mp log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
  have hB2 := tendsto_riemannZeta_sub_one_div
  have hcomb : Tendsto (fun s : ℂ => -(deriv riemannZeta s / riemannZeta s) - riemannZeta s)
      (𝓝[≠] 1) (𝓝 (-(0:ℂ) - γ - γ)) := by
    have := (hA.neg.sub (tendsto_const_nhds (x := (γ:ℂ)))).sub hB2
    apply this.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [one_div]
    ring
  have hL2 : Tendsto (fun σ : ℝ => LSeries fco σ) (𝓝[>] 0) (𝓝 (-(0:ℂ) - γ - γ)) := by
    apply (hcomb.comp hmap).congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (hz σ hσ).symm
  have heq := tendsto_nhds_unique hL1 hL2
  have := congrArg Complex.re heq
  simp at this
  linarith

/-- Under RH: `|M(a)| ≤ β a^{-1/2} + log(2π)/a` for `a ≥ 2`. -/
theorem M_bound (hRH : RiemannHypothesis) (a : ℝ) (ha : 2 ≤ a) :
    |Mfun a| ≤ βc * a ^ (-(1/2:ℝ)) + Real.log (2*Real.pi) / a := by
  obtain ⟨C, hC, hb⟩ := M_limit hRH
  have := M_limit_zero hRH C hC
  subst this
  simpa using hb a ha

end NicZ

theorem solution (hRH : RiemannHypothesis) (x : ℝ) (hx : 2 ≤ x) :
    |((∑ n ∈ Finset.range (⌊x⌋₊+1), ArithmeticFunction.vonMangoldt n * max (x/(n:ℝ)-1) 0) -
        x*(Real.log x-1-Real.eulerMascheroniConstant)) / x| ≤
      (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) * x ^ (-(1/2:ℝ)) +
        Real.log (2 * Real.pi) / x :=
  NicZ.M_bound hRH x hx
