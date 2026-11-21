-- Prove2me | solution 1 for MasulloAudit.real_log_fourier_exact_finite_part
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:12:02.922365+00:00
-- url     : https://prove2.me/submissions/069a44d3-9614-4923-ae90-caaed209bb1d

import Mathlib
import Theorems.Thm_MasulloAudit_real_log_fourier_eq_neg_half_integral_of_zero_at_zero

open Filter MeasureTheory Set FourierTransform Real
open scoped SchwartzMap FourierTransform Topology ContDiff Interval

namespace MasulloAudit

private noncomputable def unitGaussian (x : ℝ) : ℝ := exp (-π*x^2)

private lemma unitGaussian_hasDerivAt (x : ℝ) :
    HasDerivAt unitGaussian ((-2*π*x) * unitGaussian x) x := by
  have h := ((hasDerivAt_id x).pow 2).const_mul (-π)
  have he := (Real.hasDerivAt_exp (-π*x^2)).comp x h
  have hEq : rexp (-π*x^2) * (-π * ((2:ℝ) * id x ^ (2 - 1 : ℕ) * 1)) =
      (-2*π*x)*unitGaussian x := by
    simp only [unitGaussian, id_eq, Nat.add_one_sub_one, pow_one, mul_one]
    ring
  have he' : HasDerivAt unitGaussian
      (rexp (-π*x^2) * (-π * ((2:ℝ) * id x ^ (2 - 1 : ℕ) * 1))) x := he
  exact hEq ▸ he' 

private lemma iteratedDeriv_unitGaussian (n : ℕ) :
    ∃ p : Polynomial ℝ, iteratedDeriv n unitGaussian = fun x ↦ p.eval x * unitGaussian x := by
  induction n with
  | zero => exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨p.derivative + Polynomial.C (-2*π) * Polynomial.X * p, ?_⟩
    rw [iteratedDeriv_succ, hp]
    funext x
    have h : deriv (fun y ↦ p.eval y * unitGaussian y) x =
        p.derivative.eval x * unitGaussian x + p.eval x * ((-2*π*x) * unitGaussian x) :=
      ((p.hasDerivAt x).mul (unitGaussian_hasDerivAt x)).deriv
    rw [h]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring

private lemma unitGaussian_pow_mul_bounded (k : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * unitGaussian x ≤ C := by
  let g (x : ℝ) := |x| ^ k * unitGaussian x
  have hLimit : Tendsto g (cocompact ℝ) (𝓝 0) := by
    simpa only [g, unitGaussian, Real.rpow_natCast] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact Real.pi_pos (k:ℝ)
  have hC : Continuous g := by unfold g unitGaussian; fun_prop
  obtain ⟨K, hK, hSub⟩ := Filter.mem_cocompact.mp (hLimit.eventually (gt_mem_nhds zero_lt_one))
  obtain ⟨M, hM⟩ := (hK.image hC).bddAbove
  refine ⟨max 1 M, fun x ↦ ?_⟩
  by_cases hx : x ∈ K
  · exact (hM (show g x ∈ g '' K from ⟨x,hx,rfl⟩)).trans (le_max_right _ _)
  · exact (hSub hx).le.trans (le_max_left _ _)

private lemma unitGaussian_poly_mul_bounded (k : ℕ) (p : Polynomial ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, |x| ^ k * |p.eval x| * unitGaussian x ≤ C := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hq
    refine ⟨P+Q, fun x ↦ ?_⟩
    rw [Polynomial.eval_add]
    calc
      _ ≤ |x|^k * (|p.eval x| + |q.eval x|) * unitGaussian x :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity))
          (by unfold unitGaussian; positivity)
      _ = |x|^k * |p.eval x| * unitGaussian x + |x|^k * |q.eval x| * unitGaussian x := by ring
      _ ≤ _ := add_le_add (hP x) (hQ x)
  | monomial n a =>
    obtain ⟨C, hC⟩ := unitGaussian_pow_mul_bounded (k+n)
    refine ⟨|a| * C, fun x ↦ ?_⟩
    rw [Polynomial.eval_monomial, abs_mul, abs_pow]
    rw [show |x|^k*(|a| *|x|^n)*unitGaussian x = |a| *(|x|^(k+n)*unitGaussian x) by rw [pow_add]; ring]
    exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

private noncomputable def realGaussianSchwartz : 𝓢(ℝ, ℝ) where
  toFun := unitGaussian
  smooth' := by unfold unitGaussian; fun_prop
  decay' k n := by
    obtain ⟨p, hp⟩ := iteratedDeriv_unitGaussian n
    obtain ⟨C,hC⟩ := unitGaussian_poly_mul_bounded k p
    refine ⟨C, fun x ↦ ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hp, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (show 0 ≤ unitGaussian x by unfold unitGaussian; positivity)]
    rw [← mul_assoc]
    exact hC x

private noncomputable def unitGaussianSchwartz : 𝓢(ℝ, ℂ) :=
  realGaussianSchwartz.postcompCLM Complex.ofRealCLM

private lemma unitGaussianSchwartz_apply (x : ℝ) :
    unitGaussianSchwartz x = (unitGaussian x : ℂ) := rfl

private lemma unitGaussianSchwartz_zero : unitGaussianSchwartz 0 = 1 := by
  rw [unitGaussianSchwartz_apply]
  simp [unitGaussian]

private lemma fourier_unitGaussianSchwartz :
    𝓕 (unitGaussianSchwartz : ℝ → ℂ) = unitGaussianSchwartz := by
  have h := fourier_gaussian_pi (b := (1 : ℂ)) (by simp)
  have hg : (unitGaussianSchwartz : ℝ → ℂ) =
      fun x : ℝ ↦ Complex.exp (-↑π * (x : ℂ)^2) := by
    funext x
    rw [unitGaussianSchwartz_apply, unitGaussian, Complex.ofReal_exp]
    push_cast
    rfl
  rw [hg]
  simpa only [mul_one, div_one, Complex.one_cpow, one_mul] using h


private noncomputable def gammaLogMoment (s t : ℝ) : ℝ :=
  t^(s-1) * (log t * rexp (-t))

private lemma gammaLogMoment_properties {s : ℝ} (hs : 0 < s) :
    IntegrableOn (gammaLogMoment s) (Ioi 0) ∧
      (∫ t in Ioi (0:ℝ), gammaLogMoment s t) = deriv Real.Gamma s := by
  let g (t : ℝ) : ℂ := rexp (-t)
  have hg : Continuous g := Complex.continuous_ofReal.comp (continuous_exp.comp continuous_neg)
  have hTop : Asymptotics.IsBigO atTop g (fun t : ℝ ↦ t ^ (-(s+1))) := by
    rw [← Asymptotics.isBigO_norm_left]
    simpa only [g, Complex.norm_of_nonneg (exp_pos _).le, neg_one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-(s+1))).isBigO
  have hBot : Asymptotics.IsBigO (𝓝[>] 0) g (fun t : ℝ ↦ t ^ (-(0:ℝ))) := by
    simp only [neg_zero, rpow_zero]
    apply Asymptotics.isBigO_const_of_tendsto (y := (1:ℂ)) _ (by norm_num)
    have h := hg.continuousWithinAt (s := Ioi (0:ℝ)) (x := 0)
    change Tendsto g (𝓝[>] (0:ℝ)) (𝓝 (g 0)) at h
    simpa [g] using h
  have hM := mellin_hasDerivAt_of_isBigO_rpow (s := (s : ℂ))
    (hg.continuousOn.locallyIntegrableOn measurableSet_Ioi) hTop
    (by simp) hBot (by simpa using hs)
  have hEq : EqOn
      (fun t : ℝ ↦ (t : ℂ) ^ ((s : ℂ)-1) • (log t • g t))
      (fun t : ℝ ↦ (gammaLogMoment s t : ℂ)) (Ioi 0) := by
    intro t ht
    change (t : ℂ) ^ ((s : ℂ)-1) • (log t • g t) = _
    rw [show (s : ℂ)-1 = ((s-1 : ℝ):ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow (show 0 ≤ t from le_of_lt ht)]
    simp [gammaLogMoment, g, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  have hIntC : IntegrableOn (fun t : ℝ ↦ (gammaLogMoment s t : ℂ)) (Ioi 0) :=
    hM.1.congr_fun hEq measurableSet_Ioi
  have hInt : IntegrableOn (gammaLogMoment s) (Ioi 0) := by
    have h := hIntC.re
    change IntegrableOn (fun t : ℝ ↦ (gammaLogMoment s t : ℂ).re) (Ioi 0) at h
    simpa only [IntegrableOn, Complex.ofReal_re] using h
  refine ⟨hInt, ?_⟩
  have he : Complex.Gamma =ᶠ[𝓝 (s : ℂ)] Complex.GammaIntegral := by
    have hOpen : IsOpen {z : ℂ | 0 < z.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    filter_upwards [hOpen.mem_nhds (show 0 < (s : ℂ).re by simpa using hs)] with z hz
    exact Complex.Gamma_eq_integral hz
  have hD : HasDerivAt Complex.Gamma
      (mellin (fun t ↦ log t • g t) (s : ℂ)) (s : ℂ) :=
    (Complex.GammaIntegral_eq_mellin ▸ hM.2).congr_of_eventuallyEq he
  have hDreal := hD.real_of_complex
  change HasDerivAt Real.Gamma _ s at hDreal
  rw [hDreal.deriv, mellin, setIntegral_congr_fun measurableSet_Ioi hEq]
  rw [show (∫ t in Ioi (0:ℝ), (gammaLogMoment s t : ℂ)) =
    (↑(∫ t in Ioi (0:ℝ), gammaLogMoment s t) : ℂ) from integral_ofReal (𝕜 := ℂ),
    Complex.ofReal_re]

private lemma integrableOn_log_exp_neg :
    IntegrableOn (fun t : ℝ ↦ log t * exp (-t)) (Ioi 0) := by
  refine (gammaLogMoment_properties (s := 1) zero_lt_one).1.congr_fun
    (fun t _ ↦ ?_) measurableSet_Ioi
  simp [gammaLogMoment]

private lemma integral_log_exp_neg :
    (∫ t in Ioi (0:ℝ), log t * exp (-t)) = -eulerMascheroniConstant := by
  rw [← Real.hasDerivAt_Gamma_one.deriv]
  simpa only [gammaLogMoment, sub_self, rpow_zero, one_mul] using
    (gammaLogMoment_properties (s := 1) zero_lt_one).2


private lemma integrableOn_exp_neg_div_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ rexp (-t)/t) (Ioi a) := by
  have hMeas : Measurable (fun t : ℝ ↦ rexp (-t)/t) :=
    (continuous_exp.comp continuous_neg).measurable.div measurable_id
  refine ((integrableOn_exp_neg_Ioi a).const_mul a⁻¹).mono' hMeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : 0 < t := ha.trans ht
  rw [Real.norm_of_nonneg (div_nonneg (exp_pos _).le ht'.le), div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ ha ht.le) (exp_pos _).le

private lemma integral_exp_neg_div_add_log {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi a, rexp (-t)/t) + log a =
      (∫ t in Ioi a, log t * rexp (-t)) + (1 - rexp (-a))*log a := by
  let F (t : ℝ) := rexp (-t) * log t
  let f (t : ℝ) := rexp (-t)/t - log t * rexp (-t)
  have hDer (t : ℝ) (ht : t ∈ Ici a) : HasDerivAt F (f t) t := by
    have ht' : 0 < t := ha.trans_le ht
    have hExp : HasDerivAt (fun x : ℝ ↦ rexp (-x)) (-rexp (-t)) t := by
      simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using!
        (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
    have h := hExp.mul (Real.hasDerivAt_log ht'.ne')
    convert! h using 1
    unfold f
    ring
  have hF : Tendsto F atTop (𝓝 0) := by
    have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht' : 0 < t := zero_lt_one.trans_le ht
    unfold F
    rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le,
      Real.norm_of_nonneg (Real.log_nonneg ht), pow_one, mul_comm t]
    exact mul_le_mul_of_nonneg_left ((Real.log_le_sub_one_of_pos ht').trans (by linarith))
      (exp_pos _).le
  have hInt := integrableOn_log_exp_neg.mono_set (Ioi_subset_Ioi ha.le)
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hDer
    ((integrableOn_exp_neg_div_Ioi ha).sub hInt) hF
  change (∫ t in Ioi a, rexp (-t)/t - log t * rexp (-t)) = _ at he
  rw [integral_sub (integrableOn_exp_neg_div_Ioi ha) hInt, zero_sub] at he
  dsimp only [F] at he
  linarith [he]

private lemma tendsto_exp_neg_div_add_log :
    Tendsto (fun a : ℝ ↦ (∫ t in Ioi a, rexp (-t)/t) + log a)
      (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant)) := by
  have h1 := integrableOn_log_exp_neg.continuousWithinAt_Ici_primitive_Ioi.mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  change Tendsto (fun a : ℝ ↦ ∫ t in Ioi a, log t * rexp (-t))
    (𝓝[>] 0) (𝓝 (∫ t in Ioi (0:ℝ), log t * rexp (-t))) at h1
  rw [integral_log_exp_neg] at h1
  have h2 : Tendsto (fun a : ℝ ↦ (1-rexp (-a))*log a) (𝓝[>] 0) (𝓝 0) := by
    have hLog := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
    simp only [Real.rpow_one] at hLog
    have hN : Tendsto (fun a : ℝ ↦ ‖log a * a‖) (𝓝[>] 0) (𝓝 0) := by
      simpa using hLog.norm
    refine squeeze_zero_norm' ?_ hN
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha' : 0 < a := ha
    have hNonneg : 0 ≤ 1-rexp (-a) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    rw [norm_mul, norm_mul, Real.norm_of_nonneg hNonneg, Real.norm_of_nonneg ha'.le, mul_comm _ a]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    linarith [Real.add_one_le_exp (-a)]
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (integral_exp_neg_div_add_log ha).symm


private lemma integral_comp_pi_sq_Ioi (g : ℝ → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (∫ x in Ioi a, (2*π*x)*g (π*x^2)) = ∫ t in Ioi (π*a^2), g t := by
  let u (x : ℝ) := π*x^2
  have hu (x : ℝ) (hx : x ∈ Ioi a) : HasDerivWithinAt u (2*π*x) (Ioi a) x := by
    apply HasDerivAt.hasDerivWithinAt
    have h := ((hasDerivAt_id x).pow 2).const_mul π
    convert! h using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]
    ring
  have hStrict : StrictMonoOn u (Ioi a) := by
    intro x hx y hy hxy
    apply mul_lt_mul_of_pos_left _ Real.pi_pos
    exact sq_lt_sq' (by linarith [show a < x from hx, show a < y from hy]) hxy
  have hImage : u '' Ioi a = Ioi (π*a^2) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact mul_lt_mul_of_pos_left
        (sq_lt_sq' (by linarith [show a < x from hx]) hx) Real.pi_pos
    · intro hy
      have hy' : 0 < y := (mul_nonneg Real.pi_pos.le (sq_nonneg a)).trans_lt hy
      have hsq : (Real.sqrt (y/π))^2 = y/π := Real.sq_sqrt (div_nonneg hy'.le Real.pi_pos.le)
      have hxa : a < Real.sqrt (y/π) := by
        apply lt_of_not_ge
        intro h
        have h' := pow_le_pow_left₀ (Real.sqrt_nonneg (y/π)) h 2
        rw [hsq, div_le_iff₀ Real.pi_pos] at h'
        have hy'' : π*a^2 < y := hy
        linarith
      refine ⟨Real.sqrt (y/π), hxa, ?_⟩
      dsimp [u]
      rw [hsq]
      field_simp [Real.pi_ne_zero]
  rw [← hImage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hu hStrict.injOn]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx' : 0 < x := ha.trans_lt hx
  rw [smul_eq_mul, abs_of_nonneg (by positivity : 0 ≤ 2*π*x)]

private lemma integral_outside_eq_twice_of_even {f : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (he : Function.Even f) (hf : IntegrableOn f {x : ℝ | a < |x|}) :
    (∫ x in {x : ℝ | a < |x|}, f x) = 2 * ∫ x in Ioi a, f x := by
  have hSet : {x : ℝ | a < |x|} = Iio (-a) ∪ Ioi a := by
    ext x
    change (a < |x|) ↔ x < -a ∨ a < x
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · linarith
        · exact h
    · rw [abs_of_neg hx]
      constructor <;> intro h
      · exact Or.inl (by linarith)
      · rcases h with h | h <;> linarith
  have hDisj : Disjoint (Iio (-a)) (Ioi a) := by
    rw [Set.disjoint_left]
    intro x hx hy
    change x < -a at hx
    change a < x at hy
    linarith
  rw [hSet] at hf ⊢
  rw [setIntegral_union hDisj measurableSet_Ioi (hf.mono_set subset_union_left)
    (hf.mono_set subset_union_right)]
  have heq : (∫ x in Iio (-a), f x) = ∫ x in Ioi a, f x := by
    rw [setIntegral_congr_set Iio_ae_eq_Iic, ← integral_comp_neg_Ioi a f]
    exact setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ he x
  rw [heq]
  ring

private lemma integral_unitGaussian_pole_cutoff {δ : ℝ} (hδ : 0 < δ) :
    (∫ x in {x : ℝ | δ < |x|}, unitGaussian x / |x|) =
      ∫ t in Ioi (π*δ^2), rexp (-t)/t := by
  have hMeas : Measurable (fun x : ℝ ↦ unitGaussian x / |x|) :=
    (by unfold unitGaussian; fun_prop : Measurable unitGaussian).div measurable_abs
  have hInt : IntegrableOn (fun x : ℝ ↦ unitGaussian x / |x|) {x | δ < |x|} := by
    have hg : IntegrableOn (fun x ↦ δ⁻¹ * unitGaussian x) {x : ℝ | δ < |x|} :=
      ((integrable_exp_neg_mul_sq Real.pi_pos).const_mul _).integrableOn
    refine hg.mono' hMeas.aestronglyMeasurable ?_
    have hS : MeasurableSet {x : ℝ | δ < |x|} := measurableSet_lt measurable_const measurable_abs
    filter_upwards [ae_restrict_mem hS] with x hx
    have hx' : δ < |x| := hx
    have hPos : 0 ≤ unitGaussian x := (exp_pos _).le
    rw [Real.norm_of_nonneg (div_nonneg hPos (abs_nonneg _)), div_eq_mul_inv, mul_comm (unitGaussian x)]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ hx'.le) hPos
  rw [integral_outside_eq_twice_of_even hδ.le (by intro x; simp [unitGaussian]) hInt,
    ← integral_const_mul, ← integral_comp_pi_sq_Ioi _ hδ.le]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  have hx' : 0 < x := hδ.trans hx
  rw [abs_of_pos hx', unitGaussian]
  field_simp [hx'.ne', Real.pi_ne_zero]

private lemma tendsto_unitGaussian_pole_cutoff :
    Tendsto (fun δ : ℝ ↦ (∫ x in {x : ℝ | δ < |x|}, unitGaussian x / |x|) + 2*log δ)
      (𝓝[>] 0) (𝓝 (-eulerMascheroniConstant - log π)) := by
  have ht : Tendsto (fun δ : ℝ ↦ π*δ^2) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hC : Continuous fun δ : ℝ ↦ π*δ^2 := by fun_prop
      simpa using (hC.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (mul_pos Real.pi_pos (sq_pos_of_pos hδ) : 0 < π*δ^2)
  have h := (tendsto_exp_neg_div_add_log.comp ht).sub tendsto_const_nhds (b := log π)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : 0 < δ := hδ
  dsimp only [Function.comp_def]
  rw [integral_unitGaussian_pole_cutoff hδ',
    Real.log_mul Real.pi_ne_zero (pow_ne_zero _ hδ'.ne'), Real.log_pow]
  norm_num
  ring


private lemma integrable_log_mul_schwartz (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ ↦ (Real.log |x| : ℂ) * g x) := by
  let K := Icc (-1 : ℝ) 1
  let f (x : ℝ) := (Real.log |x| : ℂ) * g x
  have hf : Measurable f := by
    unfold f
    exact (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_abs)).mul
      g.continuous.measurable
  have hLog : IntegrableOn (fun x : ℝ ↦ Real.log |x|) K := by
    simp only [Real.log_abs, K]
    have h : IntegrableOn (fun x : ℝ ↦ Real.log x) (Ioc (-1 : ℝ) 1) :=
      (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).1
    simpa only [IntegrableOn, Measure.restrict_congr_set Ioc_ae_eq_Icc] using h
  let C := SchwartzMap.seminorm ℝ 0 0 g
  have hNear : IntegrableOn f K := by
    refine (hLog.norm.const_mul C).mono' hf.aestronglyMeasurable ?_
    filter_upwards [] with x
    dsimp only [f]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ g x) (abs_nonneg _)
  have hFar : IntegrableOn f Kᶜ := by
    have hI := (g.integrable_pow_mul volume 1).integrableOn (s := Kᶜ)
    refine hI.mono' hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    have hx' : 1 < |x| := lt_of_not_ge fun he ↦ hx (abs_le.mp he)
    have hx'' : 0 < |x| := zero_lt_one.trans hx'
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx'.le), pow_one]
    exact mul_le_mul_of_nonneg_right
      ((Real.log_le_sub_one_of_pos hx'').trans (sub_le_self _ zero_le_one)) (norm_nonneg _)
  have h := hNear.union hFar
  simpa only [union_compl_self, integrableOn_univ, f] using h

private lemma ae_ne_zero_real : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]

private lemma integrable_div_abs_of_zero_at_zero (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) :
    Integrable (fun x : ℝ ↦ f x / (|x| : ℝ)) := by
  let E := Icc (-1 : ℝ) 1
  let g (x : ℝ) : ℂ := f x / (|x| : ℝ)
  have hMeas : Measurable g := by
    unfold g
    exact f.continuous.measurable.div (Complex.continuous_ofReal.measurable.comp measurable_abs)
  let C := SchwartzMap.seminorm ℝ 0 1 f
  have hBound (x : ℝ) : ‖f x‖ ≤ C * |x| := by
    have hLe := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := (f : ℝ → ℂ)) (s := univ) (C := C) (x := 0) (y := x)
      (fun y _ ↦ f.differentiable y) (fun y _ ↦ ?_) (convex_univ) (mem_univ _) (mem_univ _)
    · simpa only [hf, sub_zero, Real.norm_eq_abs] using hLe
    · rw [norm_deriv_eq_norm_fderiv, ← norm_iteratedFDeriv_one]
      exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f 1 y
  have hNear : IntegrableOn g E := by
    refine (integrableOn_const (C := C) (by simp [E])).mono' hMeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae ae_ne_zero_real] with x hx
    rw [show ‖g x‖ = ‖f x‖ / |x| by simp only [g, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_abs ] ]
    exact (div_le_iff₀ (abs_pos.mpr hx)).mpr (hBound x)
  have hFar : IntegrableOn g Eᶜ := by
    have hfFar : IntegrableOn (f : ℝ → ℂ) Eᶜ := f.integrable.integrableOn
    change Integrable g (volume.restrict Eᶜ)
    refine Integrable.mono' (f := g) hfFar.norm hMeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    dsimp [g]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    have hx' : 1 < |x| := lt_of_not_ge fun he ↦ hx (abs_le.mp he)
    exact div_le_self (norm_nonneg _) hx'.le
  simpa only [union_compl_self, integrableOn_univ, g] using hNear.union hFar

private lemma integrable_log_mul_unitGaussian :
    Integrable (fun x : ℝ ↦ log |x| * unitGaussian x) := by
  have h := (integrable_log_mul_schwartz unitGaussianSchwartz).re
  change Integrable (fun x : ℝ ↦ ((log |x| : ℂ) * unitGaussianSchwartz x).re) at h
  have he : (fun x : ℝ ↦ ((log |x| : ℂ) * unitGaussianSchwartz x).re) =
      fun x : ℝ ↦ log |x| * unitGaussian x := by
    funext x
    rw [unitGaussianSchwartz_apply, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [he] at h
  exact h

private lemma integral_log_mul_unitGaussian :
    (∫ x : ℝ, log |x| * unitGaussian x) =
      -(eulerMascheroniConstant + 2*log 2 + log π)/2 := by
  let m := gammaLogMoment (1/2)
  let h (t : ℝ) := t ^ ((1/2:ℝ)-1) * rexp (-t)
  let b := fun t : ℝ ↦ (2*Real.sqrt π)⁻¹ * (m t - log π * h t)
  have hM : IntegrableOn m (Ioi 0) := (gammaLogMoment_properties (by norm_num)).1
  have hH : IntegrableOn h (Ioi 0) :=
    (Real.GammaIntegral_convergent (by norm_num : 0 < (1/2:ℝ))).congr_fun
      (fun t _ ↦ mul_comm _ _) measurableSet_Ioi
  have hIm : (∫ t in Ioi (0:ℝ), m t) = -Real.sqrt π * (eulerMascheroniConstant+2*log 2) :=
    (gammaLogMoment_properties (by norm_num)).2.trans Real.hasDerivAt_Gamma_one_half.deriv
  have hIh : (∫ t in Ioi (0:ℝ), h t) = Real.sqrt π := by
    have hGamma := (Real.Gamma_eq_integral (s := (1/2:ℝ)) (by norm_num)).symm.trans
      Real.Gamma_one_half_eq
    simpa only [h, mul_comm] using hGamma
  have hae : {x : ℝ | 0 < |x|} =ᵐ[volume] (univ : Set ℝ) := by
    have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]
    filter_upwards [hn] with x hx
    change (0 < |x|) = (x ∈ (univ : Set ℝ))
    exact propext ⟨fun _ ↦ mem_univ x, fun _ ↦ abs_pos.mpr hx⟩
  rw [← setIntegral_univ (f := fun x : ℝ ↦ log |x| * unitGaussian x),
    ← setIntegral_congr_set hae,
    integral_outside_eq_twice_of_even (by norm_num : (0:ℝ) ≤ 0)
      (by intro x; simp [unitGaussian])
      integrable_log_mul_unitGaussian.integrableOn, ← integral_const_mul]
  have hChange := integral_comp_pi_sq_Ioi b (a := 0) le_rfl
  rw [show π*(0:ℝ)^2 = 0 by ring] at hChange
  have hEq :
      (∫ x in Ioi (0:ℝ), 2*(log |x| * unitGaussian x)) =
        ∫ x in Ioi (0:ℝ), (2*π*x)*b (π*x^2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    have hx' : 0 < x := hx
    have hS : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    have hRpow : (π*x^2) ^ ((1/2:ℝ)-1) = (Real.sqrt π*x)⁻¹ := by
      rw [show (1/2:ℝ)-1 = -(1/2) by ring, Real.rpow_neg (by positivity),
        ← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq_eq_abs, abs_of_pos hx']
    dsimp only [b, m, h, gammaLogMoment]
    rw [abs_of_pos hx', unitGaussian, hRpow, log_mul Real.pi_ne_zero (pow_ne_zero _ hx'.ne'), log_pow]
    push_cast
    field_simp [Real.pi_ne_zero, hx'.ne', hS.ne']
    ring_nf
    rw [Real.sq_sqrt Real.pi_pos.le]
  rw [hEq, hChange]
  unfold b
  rw [integral_const_mul, integral_sub hM (hH.const_mul _),
    integral_const_mul, hIm, hIh]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  ring


private noncomputable def logPairing (f : 𝓢(ℝ, ℂ)) : ℂ :=
  ∫ x : ℝ, (log |x| : ℂ) * 𝓕 (f : ℝ → ℂ) x

private noncomputable def printedRealCutoff (f : 𝓢(ℝ, ℂ)) (δ : ℝ) : ℂ :=
  (∫ x in {x : ℝ | δ ≤ |x|}, f x / (|x| : ℝ)) + 2 * f 0 * (log δ : ℂ)

private lemma logPairing_unitGaussian :
    logPairing unitGaussianSchwartz = (-(eulerMascheroniConstant+2*log 2+log π)/2 : ℝ) := by
  unfold logPairing
  rw [fourier_unitGaussianSchwartz]
  simp only [unitGaussianSchwartz_apply, ← Complex.ofReal_mul]
  have he : (∫ x : ℝ, ((log |x| * unitGaussian x : ℝ) : ℂ)) =
      (↑(∫ x : ℝ, log |x| * unitGaussian x) : ℂ) := integral_ofReal (𝕜 := ℂ)
  rw [he, integral_log_mul_unitGaussian]

private lemma logPairing_add_smul (f g : 𝓢(ℝ, ℂ)) (c : ℂ) :
    logPairing (f + c • g) = logPairing f + c * logPairing g := by
  let F (x : ℝ) := (log |x| : ℂ) * (𝓕 f) x
  let G (x : ℝ) := (log |x| : ℂ) * (𝓕 g) x
  have hI : Integrable F := integrable_log_mul_schwartz (𝓕 f)
  have hJ : Integrable G := integrable_log_mul_schwartz (𝓕 g)
  have hFourier : (𝓕 (f + c • g) : 𝓢(ℝ, ℂ)) = (𝓕 f) + c • (𝓕 g) := by
    change (SchwartzMap.fourierTransformCLM ℂ) (f + c • g) =
      (SchwartzMap.fourierTransformCLM ℂ) f + c • (SchwartzMap.fourierTransformCLM ℂ) g
    rw [map_add, map_smul]
  have he : (fun x : ℝ ↦ (log |x| : ℂ) * (𝓕 (f + c • g)) x) =
      fun x : ℝ ↦ F x + c * G x := by
    funext x
    rw [hFourier]
    simp only [add_apply, smul_apply, smul_eq_mul, F, G]
    ring
  simp_rw [logPairing, ← SchwartzMap.fourier_coe]
  rw [he, integral_add hI (hJ.const_mul _), integral_const_mul]

private def outsidePole (δ : ℝ) : Set ℝ := {x | δ < |x|}

private lemma measurableSet_outsidePole (δ : ℝ) : MeasurableSet (outsidePole δ) :=
  measurableSet_lt measurable_const measurable_abs

private lemma closedCutoff_ae_eq (δ : ℝ) :
    {x : ℝ | δ ≤ |x|} =ᵐ[volume] outsidePole δ := by
  have h1 : ∀ᵐ x : ℝ ∂volume, x ≠ δ := by simp [ae_iff]
  have h2 : ∀ᵐ x : ℝ ∂volume, x ≠ -δ := by simp [ae_iff]
  filter_upwards [h1,h2] with x hx hy
  change (δ ≤ |x|) = (δ < |x|)
  have hne : δ ≠ |x| := by
    intro he
    rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h] at he
      exact hx he.symm
    · rw [abs_of_neg h] at he
      exact hy (by linarith)
  exact propext ⟨fun h ↦ lt_of_le_of_ne h hne, le_of_lt⟩

private lemma integrable_cutoff_pole (f : 𝓢(ℝ, ℂ)) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun x : ℝ ↦ f x / (|x| : ℝ)) (outsidePole δ) := by
  have hG : IntegrableOn (fun x : ℝ ↦ δ⁻¹ * ‖f x‖) (outsidePole δ) :=
    ((f.integrable (μ := volume)).norm.const_mul _).integrableOn
  have hMeas : Measurable (fun x : ℝ ↦ f x / (|x| : ℝ)) :=
    f.continuous.measurable.div (Complex.continuous_ofReal.measurable.comp measurable_abs)
  refine hG.mono' hMeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_outsidePole δ)] with x hx
  change δ < |x| at hx
  rw [norm_div, Complex.norm_of_nonneg (abs_nonneg _), div_eq_mul_inv, mul_comm ‖f x‖]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hδ hx.le) (norm_nonneg _)

private lemma tendsto_integral_outsidePole {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto (fun δ : ℝ ↦ ∫ x in outsidePole δ, f x) (𝓝[>] 0) (𝓝 (∫ x, f x)) := by
  simp_rw [← integral_indicator (measurableSet_outsidePole _)]
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
  · exact Eventually.of_forall (fun δ ↦ hf.aestronglyMeasurable.indicator (measurableSet_outsidePole δ))
  · exact Eventually.of_forall (fun δ ↦ Eventually.of_forall (fun x ↦ by
      by_cases hx : x ∈ outsidePole δ
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, norm_zero]; exact norm_nonneg _))
  · exact hf.norm
  · filter_upwards [ae_ne_zero_real] with x hx
    have he : ∀ᶠ δ : ℝ in 𝓝[>] (0:ℝ), δ < |x| :=
      (gt_mem_nhds (abs_pos.mpr hx)).filter_mono nhdsWithin_le_nhds
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [he] with δ hδ
    exact (indicator_of_mem (show x ∈ outsidePole δ from hδ) _).symm

private lemma tendsto_cutoff_gaussian_complex :
    Tendsto (printedRealCutoff unitGaussianSchwartz) (𝓝[>] 0)
      (𝓝 ((-eulerMascheroniConstant-log π : ℝ) : ℂ)) := by
  apply (Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_unitGaussian_pole_cutoff).congr'
  filter_upwards [] with δ
  have he : (∫ x in outsidePole δ, ((unitGaussian x / |x| : ℝ) : ℂ)) =
      (↑(∫ x in outsidePole δ, unitGaussian x / |x|) : ℂ) := integral_ofReal (𝕜 := ℂ)
  change (↑((∫ x in outsidePole δ, unitGaussian x / |x|) + 2*log δ) : ℂ) =
    printedRealCutoff unitGaussianSchwartz δ
  rw [printedRealCutoff, unitGaussianSchwartz_zero, mul_one,
    setIntegral_congr_set (closedCutoff_ae_eq δ), Complex.ofReal_add, ← he]
  simp only [unitGaussianSchwartz_apply, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]

private lemma printedRealCutoff_add_smul (f g : 𝓢(ℝ, ℂ)) (c : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    printedRealCutoff (f + c • g) δ = printedRealCutoff f δ + c * printedRealCutoff g δ := by
  have hF := integrable_cutoff_pole f hδ
  have hG := (integrable_cutoff_pole g hδ).const_mul c
  unfold printedRealCutoff
  simp_rw [setIntegral_congr_set (closedCutoff_ae_eq δ)]
  simp only [add_apply, smul_apply, smul_eq_mul, add_div, mul_div_assoc]
  rw [integral_add hF hG, integral_const_mul]
  ring

/-- The additive Fourier distribution in real dimension one, with the full
finite-part normalization and the constant at the pole. -/
theorem real_log_fourier_exact_finite_part_aux (f : 𝓢(ℝ, ℂ)) :
    Tendsto (printedRealCutoff f) (𝓝[>] 0)
      (𝓝 (-2 * (logPairing f + (eulerMascheroniConstant + log (2*π) : ℝ) * f 0))) := by
  let c := f 0
  let g := f - c • unitGaussianSchwartz
  have hg : g 0 = 0 := by
    simp [g, c, unitGaussianSchwartz_zero]
  have hfg : g + c • unitGaussianSchwartz = f := sub_add_cancel _ _
  let I : ℂ := ∫ x : ℝ, g x / (|x| : ℝ)
  have hI : Tendsto (printedRealCutoff g) (𝓝[>] 0) (𝓝 I) := by
    apply (tendsto_integral_outsidePole (integrable_div_abs_of_zero_at_zero g hg)).congr'
    filter_upwards [] with δ
    simp only [printedRealCutoff, hg, mul_zero, zero_mul, add_zero]
    exact (setIntegral_congr_set (closedCutoff_ae_eq δ)).symm
  have hV := hI.add (tendsto_cutoff_gaussian_complex.const_mul c)
  have hVC : Tendsto (printedRealCutoff f) (𝓝[>] 0)
      (𝓝 (I + c * ((-eulerMascheroniConstant-log π : ℝ) : ℂ))) := by
    apply hV.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    rw [← printedRealCutoff_add_smul g unitGaussianSchwartz c hδ, hfg]
  have hT : logPairing g = -(2:ℂ)⁻¹ * I :=
    real_log_fourier_eq_neg_half_integral_of_zero_at_zero g hg
  have hTf : logPairing f = -(2:ℂ)⁻¹ * I + c * (-(eulerMascheroniConstant+2*log 2+log π)/2 : ℝ) := by
    rw [← hfg, logPairing_add_smul, hT, logPairing_unitGaussian]
  rw [hTf, show f 0 = c from rfl, log_mul (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero]
  convert hVC using 2
  push_cast
  ring

end MasulloAudit

open MeasureTheory

theorem solution (f : SchwartzMap ℝ ℂ) :
    Filter.Tendsto
      (fun δ : ℝ ↦ (∫ x in {x : ℝ | δ ≤ |x|}, f x / (|x| : ℝ)) +
        2 * f 0 * (Real.log δ : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-2 * ((∫ ξ : ℝ, (Real.log |ξ| : ℂ) * FourierTransform.fourier (f : ℝ → ℂ) ξ) +
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) : ℝ) * f 0))) := by
  exact MasulloAudit.real_log_fourier_exact_finite_part_aux f
