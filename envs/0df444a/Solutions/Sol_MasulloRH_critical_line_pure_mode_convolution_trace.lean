-- Prove2me | solution 1 for MasulloRH.critical_line_pure_mode_convolution_trace
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:50:38.336846+00:00
-- url     : https://prove2.me/submissions/419b4f93-de62-486f-91a4-a8baaee7164f

import Mathlib
import Theorems.Thm_MasulloRH_spectral_trace_of_polynomial_translation
import Theorems.Thm_MasulloRH_weighted_zero_summability
open MeasureTheory Filter MasulloGRH
open scoped Topology FourierTransform SchwartzMap InnerProductSpace

set_option autoImplicit false
open scoped ENNReal

namespace MasulloRH
noncomputable section

abbrev LogL2 := Lp ℂ 2 (volume : Measure ℝ)

def logWeight (p x : ℝ) : ℝ := (1 + |x|) ^ (-p)

lemma logWeight_pos (p x : ℝ) : 0 < logWeight p x := Real.rpow_pos_of_pos (by positivity) _

lemma continuous_logWeight (p : ℝ) : Continuous (logWeight p) := by
  apply Continuous.rpow_const (continuous_const.add continuous_abs)
  exact fun x => Or.inl (show (1 + |x| : ℝ) ≠ 0 by positivity)

lemma logWeight_ratio_le {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    logWeight p x / logWeight p (x+y) ≤ (1 + |y|)^p := by
  have hx : 0 < 1 + |x| := by positivity
  have hxy : 0 < 1 + |x+y| := by positivity
  have hab : 1 + |x+y| ≤ (1 + |x|) * (1 + |y|) := by
    nlinarith [abs_add_le x y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]
  rw [logWeight, logWeight, Real.rpow_neg hx.le, Real.rpow_neg hxy.le, inv_div_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hx p)).2
  rw [mul_comm, ← Real.mul_rpow hx.le (show 0 ≤ 1 + |y| by positivity)]
  exact Real.rpow_le_rpow hxy.le hab hp

private def ratio (p y x : ℝ) : ℂ := (logWeight p x / logWeight p (x+y) : ℝ)

private lemma ratio_norm (p y x : ℝ) : ‖ratio p y x‖ = logWeight p x / logWeight p (x+y) := by
  exact Complex.norm_of_nonneg (div_nonneg (logWeight_pos _ _).le (logWeight_pos _ _).le)

private lemma ratio_mem (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : MemLp (ratio p y) ⊤ volume := by
  apply memLp_top_of_bound _ ((1+|y|)^p) (ae_of_all _ fun x => (ratio_norm p y x).le.trans (logWeight_ratio_le hp x y))
  apply Continuous.aestronglyMeasurable
  exact Complex.continuous_ofReal.comp <| (continuous_logWeight p).div
    ((continuous_logWeight p).comp (continuous_id.add_const y)) (fun x => (logWeight_pos _ _).ne')

private def shift (y : ℝ) : LogL2 →ₗᵢ[ℂ] LogL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x+y) (measurePreserving_add_right volume y)

def weightedTranslation (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : LogL2 →L[ℂ] LogL2 :=
  (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2) ((ratio_mem p hp y).toLp (ratio p y))).comp
    (shift y).toContinuousLinearMap

lemma weightedTranslation_apply_ae (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : LogL2) :
    (weightedTranslation p hp y f : ℝ → ℂ) =ᵐ[volume] fun x =>
      ((logWeight p x / logWeight p (x+y) : ℝ) : ℂ) * f (x+y) := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((ratio_mem p hp y).toLp (ratio p y)) (shift y f)
  have hs := Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)
  refine h.trans ?_
  filter_upwards [(ratio_mem p hp y).coeFn_toLp, hs] with x hx hsx
  change ((ratio_mem p hp y).toLp (ratio p y)) x * (shift y f) x = _
  change (shift y f) x = f (x+y) at hsx
  rw [hx, hsx]; rfl

lemma norm_weightedTranslation_le (p : ℝ) (hp : 0 ≤ p) (y : ℝ) :
    ‖weightedTranslation p hp y‖ ≤ (1+|y|)^p := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [← (shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedTranslation_apply_ae p hp y f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hs
  change (shift y f) x = f (x+y) at hs
  rw [hx, hs, norm_mul]
  exact mul_le_mul_of_nonneg_right ((ratio_norm p y x).le.trans (logWeight_ratio_le hp x y)) (norm_nonneg _)

lemma weightedTranslation_zero (p : ℝ) (hp : 0 ≤ p) : weightedTranslation p hp 0 = .id ℂ LogL2 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [weightedTranslation_apply_ae p hp 0 f] with x h
  change (weightedTranslation p hp 0 f) x = f x
  simpa only [add_zero, div_self (logWeight_pos p x).ne', Complex.ofReal_one, one_mul] using h

lemma weightedTranslation_add (p : ℝ) (hp : 0 ≤ p) (y z : ℝ) :
    weightedTranslation p hp (y+z) = (weightedTranslation p hp y).comp (weightedTranslation p hp z) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hz := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp
    (weightedTranslation_apply_ae p hp z f)
  filter_upwards [weightedTranslation_apply_ae p hp (y+z) f,
    weightedTranslation_apply_ae p hp y ((weightedTranslation p hp z) f), hz] with x hall hy hz
  change (weightedTranslation p hp z f) (x+y) = _ at hz
  change (weightedTranslation p hp (y+z) f) x = (weightedTranslation p hp y ((weightedTranslation p hp z) f)) x
  rw [hall, hy, hz]
  simp only [Function.comp_apply, ← add_assoc, ← mul_assoc, ← Complex.ofReal_mul]
  field_simp [ne_of_gt (logWeight_pos p (x+y)), ne_of_gt (logWeight_pos p (x+y+z))]

def angularCharacter (ξ x : ℝ) : ℂ := Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)

lemma angularCharacter_add (ξ x y : ℝ) :
    angularCharacter ξ (x+y) = angularCharacter ξ x * angularCharacter ξ y := by
  simp [angularCharacter, mul_add, add_mul, Complex.exp_add]

lemma norm_angularCharacter (ξ x : ℝ) : ‖angularCharacter ξ x‖ = 1 := by
  simp [angularCharacter, Complex.norm_exp]

lemma weightedExponential_memLp (p ξ : ℝ) (hp : 1/2 < p) :
    MemLp (fun x : ℝ => (logWeight p x : ℂ) * angularCharacter ξ x) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm _).2
  · have hdeg : (Module.finrank ℝ ℝ : ℝ) < 2*p := by simp; linarith
    have hint := integrable_one_add_norm (E := ℝ) (μ := volume) hdeg
    apply hint.congr
    apply Filter.Eventually.of_forall
    intro x
    change (1 + ‖x‖)^(-(2*p)) = ‖(logWeight p x : ℂ) * angularCharacter ξ x‖^2
    rw [norm_mul, norm_angularCharacter, mul_one, Complex.norm_of_nonneg (logWeight_pos _ _).le,
      logWeight, ← Real.rpow_mul_natCast (by positivity)]
    simp [Real.norm_eq_abs, mul_comm]
  · apply Continuous.aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp (continuous_logWeight p)).mul
      (show Continuous (angularCharacter ξ) by unfold angularCharacter; fun_prop)

def weightedExponential (p ξ : ℝ) (hp : 1/2 < p) : LogL2 := (weightedExponential_memLp p ξ hp).toLp _

lemma weightedTranslation_exponential (p ξ : ℝ) (hp : 1/2 < p) (y : ℝ) :
    weightedTranslation p (by linarith) y (weightedExponential p ξ hp) =
      angularCharacter ξ y • weightedExponential p ξ hp := by
  have he := (weightedExponential_memLp p ξ hp).coeFn_toLp
  have hesh := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp he
  apply Lp.ext
  filter_upwards [weightedTranslation_apply_ae p (by linarith) y (weightedExponential p ξ hp), he,
    hesh, Lp.coeFn_smul (angularCharacter ξ y) (weightedExponential p ξ hp)] with x hU hx hxy hsm
  change weightedExponential p ξ hp x = (logWeight p x : ℂ) * angularCharacter ξ x at hx
  change weightedExponential p ξ hp (x+y) = (logWeight p (x+y) : ℂ) * angularCharacter ξ (x+y) at hxy
  rw [hU, hsm, Pi.smul_apply, smul_eq_mul, hx, hxy, angularCharacter_add, Complex.ofReal_div]
  field_simp [ne_of_gt (logWeight_pos p (x+y))]

private lemma ratio_sub_one_bound {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    |logWeight p x / logWeight p (x+y) - 1| ≤ (1+|y|)^p - 1 := by
  let a := logWeight p x / logWeight p (x+y)
  let D := (1+|y|)^p
  have hD : 1 ≤ D := Real.one_le_rpow (by linarith [abs_nonneg y]) hp
  have ha : a ≤ D := logWeight_ratio_le hp x y
  have hinv := logWeight_ratio_le hp (x+y) (-y)
  simp only [add_neg_cancel_right, abs_neg] at hinv
  have hDa : 1 ≤ D*a := by
    change 1 ≤ D * (logWeight p x / logWeight p (x+y))
    rw [← mul_div_assoc, le_div_iff₀ (logWeight_pos p (x+y)), one_mul]
    exact (div_le_iff₀ (logWeight_pos p x)).mp hinv
  change |a-1| ≤ D-1
  apply abs_le.mpr
  refine ⟨?_, by linarith⟩
  by_cases h : a ≤ 1
  · have h' := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hD)
    nlinarith
  · linarith

private lemma shift_continuous (f : LogL2) : Continuous (fun y : ℝ => shift y f) := by
  let g : C(ℝ × ℝ, ℝ) := ⟨fun z => z.2 + z.1, continuous_snd.add continuous_fst⟩
  exact continuous_const.compMeasurePreservingLp (g := g.curry) g.curry.continuous
    (fun y => measurePreserving_add_right volume y) (by norm_num)

private lemma diff_shift_bound (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : LogL2) :
    ‖weightedTranslation p hp y f - shift y f‖ ≤ ((1+|y|)^p-1) * ‖f‖ := by
  rw [← (shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [weightedTranslation_apply_ae p hp y f,
    Lp.coeFn_sub (weightedTranslation p hp y f) (shift y f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hsub hs
  change (shift y f) x = f (x+y) at hs
  rw [hsub, Pi.sub_apply, hx, hs, ← sub_one_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact ratio_sub_one_bound hp x y

lemma continuous_weightedTranslation_orbit (p : ℝ) (hp : 0 ≤ p) (f : LogL2) :
    Continuous (fun y : ℝ => weightedTranslation p hp y f) := by
  have hlim : Tendsto (fun y : ℝ => weightedTranslation p hp y f) (𝓝 0) (𝓝 f) := by
    have hg : Continuous (fun y : ℝ => ((1+|y|)^p-1) * ‖f‖) := by
      apply Continuous.mul_const
      apply Continuous.sub _ continuous_const
      apply Continuous.rpow_const (continuous_const.add continuous_abs)
      exact fun x => Or.inl (show (1 + |x| : ℝ) ≠ 0 by positivity)
    have hbound : Tendsto (fun y : ℝ => ((1+|y|)^p-1) * ‖f‖) (𝓝 0) (𝓝 0) := by
      simpa using hg.tendsto 0
    have hdiff : Tendsto (fun y : ℝ => weightedTranslation p hp y f - shift y f) (𝓝 0) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => norm_nonneg _) (fun y => diff_shift_bound p hp y f) hbound
    have hs0 : shift 0 f = f := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume (0:ℝ))] with x hx
      change (shift 0 f) x = f (x+0) at hx
      simpa only [add_zero] using hx
    have hs := (shift_continuous f).tendsto 0
    rw [hs0] at hs
    simpa only [sub_add_cancel, zero_add] using hdiff.add hs
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : Tendsto (fun z : ℝ => z-y) (𝓝 y) (𝓝 0) := by simpa using (show Continuous (fun z : ℝ => z-y) from continuous_id.sub continuous_const).tendsto y
  have h := (weightedTranslation p hp y).continuous.continuousAt.tendsto.comp (hlim.comp hd)
  refine h.congr fun z => ?_
  change (weightedTranslation p hp y) ((weightedTranslation p hp (z-y)) f) = _
  rw [← ContinuousLinearMap.comp_apply, ← weightedTranslation_add]
  simp

end
end MasulloRH

namespace MasulloRH
noncomputable section

private def angularHom (ξ : ℝ) : Multiplicative ℝ →* ℂ where
  toFun t := angularCharacter ξ t.toAdd
  map_one' := by simp [angularCharacter]
  map_mul' u v := angularCharacter_add _ _ _

private lemma angularHom_injective : Function.Injective angularHom := by
  intro ξ η h
  by_contra hne
  let t := Real.pi / (ξ - η)
  have hd : (ξ-η)*t = Real.pi := mul_div_cancel₀ _ (sub_ne_zero.mpr hne)
  have ha := DFunLike.congr_fun h (Multiplicative.ofAdd t)
  change Complex.exp ((ξ : ℂ) * (t : ℂ) * Complex.I) = Complex.exp ((η : ℂ) * (t : ℂ) * Complex.I) at ha
  have hb : Complex.exp (((ξ : ℂ) * (t : ℂ) * Complex.I) - ((η : ℂ) * (t : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_sub, ha, div_self (Complex.exp_ne_zero _)]
  have hc : (ξ : ℂ) * (t : ℂ) * Complex.I - (η : ℂ) * (t : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I := by
    rw [← sub_mul, ← sub_mul, ← Complex.ofReal_sub, ← Complex.ofReal_mul, hd]
  rw [hc, Complex.exp_pi_mul_I] at hb
  norm_num at hb

private lemma sum_exponential_ae (p : ℝ) (hp : 1/2 < p) (s : Finset ℝ) (c : ℝ → ℂ) :
    ((∑ ξ ∈ s, c ξ • weightedExponential p ξ hp : LogL2) : ℝ → ℂ) =ᵐ[volume]
      fun x => (logWeight p x : ℂ) * ∑ ξ ∈ s, c ξ * angularCharacter ξ x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, mul_zero]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    exact hx
  | insert ξ s hs ih =>
    simp only [Finset.sum_insert hs]
    filter_upwards [Lp.coeFn_add (c ξ • weightedExponential p ξ hp) (∑ η ∈ s, c η • weightedExponential p η hp),
      Lp.coeFn_smul (c ξ) (weightedExponential p ξ hp), (weightedExponential_memLp p ξ hp).coeFn_toLp, ih]
      with x ha hm he ht
    change weightedExponential p ξ hp x = _ at he
    rw [ha, Pi.add_apply, hm, Pi.smul_apply, smul_eq_mul, he, ht]
    ring

/-- Exponentials of every distinct angular frequency form a linearly independent family
in the polynomially weighted shift model, for every weight exponent greater than one half. -/
theorem linearIndependent_weightedExponential (p : ℝ) (hp : 1/2 < p) :
    LinearIndependent ℂ (fun ξ : ℝ => weightedExponential p ξ hp) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc
  have hzero : (fun x : ℝ => ∑ ξ ∈ s, c ξ * angularCharacter ξ x) =ᵐ[volume] fun _ => 0 := by
    have he := sum_exponential_ae p hp s c
    rw [hc] at he
    filter_upwards [he, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x h hx
    rw [hx] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Complex.ofReal_ne_zero.mpr (logWeight_pos p x).ne')
  have hall := Measure.eq_of_ae_eq hzero (by unfold angularCharacter; fun_prop) continuous_const
  have hl := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp angularHom angularHom_injective
  apply (linearIndependent_iff'.mp hl) s c
  funext x
  simpa [angularHom] using congrFun hall x.toAdd

end
end MasulloRH

namespace MasulloRH
noncomputable section

variable {ι : Type*}

private def spectralMode (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (i : ι) : LogL2 :=
  weightedExponential p (-2*Real.pi*ν i) hp

private lemma spectralMode_ae (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (i : ι) :
    (spectralMode p hp ν i : ℝ → ℂ) =ᵐ[volume] fun x =>
      (logWeight p x : ℂ) * Complex.exp ((-2*Real.pi*(ν i)*x : ℝ) * Complex.I) := by
  exact (weightedExponential_memLp p (-2*Real.pi*ν i) hp).coeFn_toLp.trans
    (ae_of_all _ fun x => by simp [angularCharacter])

def weightedSpectralSpan (p : ℝ) (ν : ι → ℝ) : Submodule ℂ LogL2 :=
  (Submodule.span ℂ {f : LogL2 | ∃ i, (f : ℝ → ℂ) =ᵐ[volume] fun x =>
    (logWeight p x : ℂ) * Complex.exp ((-2*Real.pi*(ν i)*x : ℝ) * Complex.I)}).topologicalClosure

private lemma set_spectralMode (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) :
    {f : LogL2 | ∃ i, (f : ℝ → ℂ) =ᵐ[volume] fun x =>
      (logWeight p x : ℂ) * Complex.exp ((-2*Real.pi*(ν i)*x : ℝ) * Complex.I)} = Set.range (spectralMode p hp ν) := by
  ext f
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Lp.ext ((spectralMode_ae p hp ν i).trans hi.symm)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, spectralMode_ae p hp ν i⟩

private lemma span_spectralMode (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) :
    weightedSpectralSpan p ν = (Submodule.span ℂ (Set.range (spectralMode p hp ν))).topologicalClosure := by
  rw [weightedSpectralSpan, set_spectralMode p hp ν]

instance (p : ℝ) (ν : ι → ℝ) : CompleteSpace (weightedSpectralSpan p ν) :=
  inferInstanceAs (CompleteSpace (Submodule.topologicalClosure _))

private def includedMode (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (i : ι) : weightedSpectralSpan p ν :=
  ⟨spectralMode p hp ν i, by rw [span_spectralMode p hp ν]; exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i,rfl⟩)⟩

private theorem includedMode_independent (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (hν : Function.Injective ν) :
    LinearIndependent ℂ (includedMode p hp ν) := by
  apply LinearIndependent.of_comp (weightedSpectralSpan p ν).subtype
  apply (linearIndependent_weightedExponential p hp).comp (fun i => -2*Real.pi*ν i)
  intro i j he
  exact hν (mul_left_cancel₀ (by positivity : (-2:ℝ)*Real.pi ≠ 0) he)

private theorem includedMode_dense (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) :
    Dense (Submodule.span ℂ (Set.range (includedMode p hp ν)) : Set (weightedSpectralSpan p ν)) := by
  rw [Subtype.dense_iff]
  have h : ((weightedSpectralSpan p ν).subtype '' (Submodule.span ℂ (Set.range (includedMode p hp ν)) : Set (weightedSpectralSpan p ν))) =
      (Submodule.span ℂ (Set.range (spectralMode p hp ν)) : Set LogL2) := by
    rw [← Submodule.map_coe, Submodule.map_span, ← Set.range_comp]
    rfl
  change (weightedSpectralSpan p ν : Set LogL2) ⊆ closure ((weightedSpectralSpan p ν).subtype '' _)
  rw [h, span_spectralMode p hp ν, Submodule.topologicalClosure_coe]

private lemma span_invariant (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (y : ℝ) :
    ∀ u ∈ weightedSpectralSpan p ν, weightedTranslation p (by linarith) y u ∈ weightedSpectralSpan p ν := by
  rw [span_spectralMode p hp ν]
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
  apply Submodule.topologicalClosure_mem_invtSubmodule
  rw [Module.End.mem_invtSubmodule_iff_map_le, Submodule.map_span, Submodule.span_le, ← Set.range_comp]
  rintro _ ⟨i,rfl⟩
  change weightedTranslation p (by linarith) y (weightedExponential p (-2*Real.pi*ν i) hp) ∈ _
  rw [weightedTranslation_exponential]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

def weightedSpectralShift (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (y : ℝ) :
    weightedSpectralSpan p ν →L[ℂ] weightedSpectralSpan p ν :=
  (weightedTranslation p (by linarith) y).restrict (span_invariant p hp ν y)

private lemma continuous_spectral_orbit (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (u : weightedSpectralSpan p ν) :
    Continuous fun y => weightedSpectralShift p hp ν y u := by
  apply Continuous.subtype_mk
  exact continuous_weightedTranslation_orbit p (by linarith) (u : LogL2)

private lemma shift_bound (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (y : ℝ) :
    ‖weightedSpectralShift p hp ν y‖ ≤ (1+|y|)^⌈p⌉₊ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖weightedTranslation p (by linarith) y (u : LogL2)‖ ≤ _ * ‖(u : LogL2)‖
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (norm_weightedTranslation_le p (by linarith) y).trans
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (Nat.le_ceil p)

private lemma spectralShift_acts (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (i : ι) (y : ℝ) :
    weightedSpectralShift p hp ν y (includedMode p hp ν i) =
      Complex.exp ((-2*Real.pi*y*ν i : ℝ) * Complex.I) • includedMode p hp ν i := by
  apply Subtype.ext
  change weightedTranslation p (by linarith) y (weightedExponential p (-2*Real.pi*ν i) hp) = _ • weightedExponential p (-2*Real.pi*ν i) hp
  rw [weightedTranslation_exponential]
  congr 1
  unfold angularCharacter
  push_cast
  ring_nf

theorem spectral_trace_on_weighted_span (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (hν : Function.Injective ν)
    (hw : Summable fun i => 1/(1+(ν i)^2)) (m : 𝓢(ℝ,ℂ)) :
    ∃ T : weightedSpectralSpan p ν →L[ℂ] weightedSpectralSpan p ν,
      (∀ u, ((T u : weightedSpectralSpan p ν) : LogL2) =
        ∫ y : ℝ, (𝓕⁻ (⇑m)) y • weightedTranslation p (by linarith) y (u : LogL2)) ∧
      IsNuclearOperator T ∧ HasSum (fun i => m (ν i)) (operatorTrace T) := by
  obtain ⟨T,hT,hN,htr⟩ := spectral_trace_of_polynomial_translation (weightedSpectralShift p hp ν) ⌈p⌉₊ 1
    (by norm_num) (continuous_spectral_orbit p hp ν) (fun y => by simpa only [one_mul] using shift_bound p hp ν y)
    (includedMode p hp ν) ν (includedMode_independent p hp ν hν) (includedMode_dense p hp ν) (spectralShift_acts p hp ν) hw m
  refine ⟨T, fun u => ?_, hN, htr⟩
  rw [hT]
  exact ((weightedSpectralSpan p ν).subtypeₗᵢ.integral_comp_comm (fun y : ℝ => (𝓕⁻ (⇑m)) y • weightedSpectralShift p hp ν y u)).symm

private lemma multiplier_integrable (p : ℝ) (hp : 1/2 < p) (u : LogL2) (m : 𝓢(ℝ,ℂ)) :
    Integrable (fun y : ℝ => (𝓕⁻ (⇑m)) y • weightedTranslation p (by linarith) y u) := by
  let k := Nat.ceil p
  let g := (𝓕⁻ m : 𝓢(ℝ,ℂ))
  have hg : (g : ℝ → ℂ) = 𝓕⁻ (⇑m) := SchwartzMap.fourierInv_coe m
  rw [← hg]
  have hw : Integrable (fun y : ℝ => (1+|y|)^k * ‖g y‖) := by
    have h := (g.integrable.norm.add (g.integrable_pow_mul volume k)).const_mul ((2:ℝ)^(k-1))
    apply h.mono' (by fun_prop)
    refine Eventually.of_forall fun y => ?_
    change ‖(1+|y|)^k * ‖g y‖‖ ≤ 2^(k-1) * (‖g y‖ + ‖y‖ ^ k * ‖g y‖)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, ← one_add_mul, ← mul_assoc]
    gcongr
    simpa using add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg y) k
  apply (hw.mul_const ‖u‖).mono' (g.continuous.aestronglyMeasurable.smul (continuous_weightedTranslation_orbit p (by linarith) u).aestronglyMeasurable)
  refine ae_of_all _ fun y => ?_
  change ‖g y • (weightedTranslation p (by linarith) y u)‖ ≤ _
  rw [norm_smul]
  have hb : ‖weightedTranslation p (by linarith) y‖ ≤ (1+|y|)^k := by
    apply (norm_weightedTranslation_le _ _ _).trans
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (Nat.le_ceil p)
  calc
    _ ≤ ‖g y‖ * ((1+|y|)^k * ‖u‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact ((weightedTranslation p (by linarith) y).le_opNorm u).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    _ = _ := by ring

private lemma convolution_pairing (p : ℝ) (hp : 1/2 < p) (m : 𝓢(ℝ,ℂ)) (u g : LogL2) :
    ⟪g, ∫ y : ℝ, (𝓕⁻ (⇑m)) y • weightedTranslation p (by linarith) y u⟫_ℂ =
      ∫ y : ℝ, (𝓕⁻ (⇑m)) y * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
        (((logWeight p x / logWeight p (x+y) : ℝ) : ℂ) * u (x+y)) := by
  rw [← integral_inner (multiplier_integrable p hp u m) g]
  apply integral_congr_ae (ae_of_all _ fun y => ?_)
  rw [inner_smul_right, MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [weightedTranslation_apply_ae p (by linarith) y u] with x hx
  rw [RCLike.inner_apply', hx]


end
end MasulloRH

open MasulloRH

theorem MasulloRH.weighted_spectral_convolution_trace {ι : Type*} (p : ℝ) (hp : 1/2 < p) (ν : ι → ℝ) (hν : Function.Injective ν)
    (hw : Summable fun i => 1/(1+(ν i)^2)) (m : 𝓢(ℝ,ℂ)) :
    let H := Lp ℂ 2 (volume : Measure ℝ)
    let S := (Submodule.span ℂ {f : H | ∃ i, (f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      (((1+|x|)^(-p) : ℝ) : ℂ) * Complex.exp ((-2*Real.pi*(ν i)*x : ℝ) * Complex.I)}).topologicalClosure
    ∃! T : S →L[ℂ] S,
      (∀ (u : S) (g : H), ⟪g, (T u : H)⟫_ℂ =
        ∫ y : ℝ, (𝓕⁻ (⇑m)) y * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
          ((((1+|x|)^(-p) / (1+|x+y|)^(-p) : ℝ) : ℂ) * (u : H) (x+y))) ∧
      IsNuclearOperator T ∧ HasSum (fun i => m (ν i)) (operatorTrace T) := by
  dsimp only
  obtain ⟨T, hT, hN, htrace⟩ := spectral_trace_on_weighted_span p hp ν hν hw m
  have hpair (u : weightedSpectralSpan p ν) (g : LogL2) :=
    (congrArg (inner ℂ g) (hT u)).trans (convolution_pairing p hp m (u : LogL2) g)
  refine ⟨T, ⟨hpair, hN, htrace⟩, fun T' h' => ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply ext_inner_left ℂ
  exact fun g => (h'.1 u g).trans (hpair u g).symm


open Set Filter MeasureTheory
open scoped FourierTransform SchwartzMap Topology

namespace MasulloRH

abbrev CriticalLineZero := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1 / 2}

theorem criticalLineOrder_pos (ρ : CriticalLineZero) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    linarith [ρ.prop.2, Complex.one_re]
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfinite := analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  have hnonzero := (analyticOn_riemannZeta _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1
  exact Nat.pos_of_ne_zero (fun h => (ENat.toNat_eq_zero.mp h).elim hnonzero hfinite)

theorem criticalLineZero_scaled_multiplicity_summable :
    Summable (fun ρ : CriticalLineZero => (analyticOrderNatAt riemannZeta ρ.val : ℝ) /
        (1 + (-ρ.val.im / (2 * Real.pi)) ^ 2)) := by
  let e (ρ : CriticalLineZero) : ZetaZerosInTraceStrip 1 :=
    ⟨ρ.val, ρ.prop.1, by rw [ρ.prop.2]; norm_num, by rw [ρ.prop.2]; norm_num,
      by rw [ρ.prop.2]; norm_num⟩
  have he : Function.Injective e := fun _ _ h => Subtype.ext (congrArg (fun s : ZetaZerosInTraceStrip 1 => s.val) h)
  have hs := ((weighted_zero_summability 1 one_pos).comp_injective he).mul_left ((2 * Real.pi)^2)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro ρ
  let y := ρ.val.im
  let c := 2 * Real.pi
  have hc : 1 ≤ c := by dsimp [c]; linarith [Real.pi_gt_three]
  have hc0 : 0 < c := by linarith
  have hsc : 1 + y^2 ≤ c^2 * (1 + (-y/c)^2) := calc
    _ ≤ c^2 + y^2 := by nlinarith [sq_nonneg (c-1)]
    _ = _ := by field_simp
  have hrecip : 1 / (1 + (-y / c)^2) ≤ c^2 / (1+y^2) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa only [one_mul] using hsc)
  let m : ℝ := analyticOrderNatAt riemannZeta ρ.val
  have hm : 0 ≤ m := Nat.cast_nonneg _
  change m / (1 + (-y / c)^2) ≤ c^2 * (m / (1+y^2))
  calc
    _ = m * (1 / (1 + (-y / c)^2)) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hrecip hm).trans_eq (by ring)

theorem criticalLineZero_scaled_weight_summable :
    Summable (fun ρ : CriticalLineZero => 1 / (1 + (-ρ.val.im / (2 * Real.pi)) ^ 2)) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ criticalLineZero_scaled_multiplicity_summable
  intro ρ
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast criticalLineOrder_pos ρ

theorem exists_logTraceTest_schwartz (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ f : 𝓢(ℝ, ℂ), ∀ y, f y = φ (Real.exp y) := by
  have hk : IsCompact (Real.log '' tsupport φ) := hφ.2.1.image_of_continuousOn
    (Real.continuousOn_log.mono (fun x hx => ne_of_gt (hφ.2.2.1 hx)))
  have hc : HasCompactSupport (fun y => φ (Real.exp y)) :=
    HasCompactSupport.of_support_subset_isCompact hk (by
      intro y hy
      exact ⟨Real.exp y, subset_tsupport _ hy, Real.log_exp y⟩)
  exact ⟨hc.toSchwartzMap (hφ.1.comp Real.contDiff_exp), fun _ => rfl⟩

theorem fourier_logTraceTest_eq_mellin (φ : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun y : ℝ => φ (Real.exp y)) (-t / (2 * Real.pi)) = mellin φ (Complex.I * t) := by
  rw [mellin_eq_fourier]
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
    Complex.ofReal_im, mul_zero, sub_zero, neg_zero, Real.exp_zero, one_smul,
    Complex.mul_im, one_mul, zero_add]
  rw [← Real.fourierInv_eq_fourier_comp_neg (fun y : ℝ => φ (Real.exp y))]
  rw [Real.fourierInv_eq_fourier_neg, neg_div]


end MasulloRH

open MasulloRH MasulloGRH MeasureTheory Filter
open scoped SchwartzMap FourierTransform InnerProductSpace

/-- On the closed span of the pure critical-line zeta modes, weighted convolution with a
rational trace test has the sum of its Mellin values at the distinct zeros as its trace. -/
theorem solution (p : ℝ) (hp : 1 / 2 < p) (φ : ℝ → ℂ) (hφ : MasulloRH.IsRationalTraceTest φ) :
    let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}
    let H := Lp ℂ 2 (volume : Measure ℝ)
    let S := (Submodule.span ℂ {f : H | ∃ ρ : Z, (f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      (((1+|x|)^(-p) : ℝ) : ℂ) * Complex.exp (((ρ.val.im*x : ℝ) : ℂ) * Complex.I)}).topologicalClosure
    ∃! T : S →L[ℂ] S,
      (∀ (u : S) (g : H), ⟪g, (T u : H)⟫_ℂ =
        ∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
          ((((1+|x|)^(-p) / (1+|x+y|)^(-p) : ℝ) : ℂ) * (u : H) (x+y))) ∧
      IsNuclearOperator T ∧ HasSum (fun ρ : Z => mellin φ (ρ.val - 1/2)) (operatorTrace T) := by
  let ν (ρ : CriticalLineZero) := -ρ.val.im/(2*Real.pi)
  have hν : Function.Injective ν := by
    intro i j hij
    apply Subtype.ext
    apply Complex.ext
    · rw [i.prop.2, j.prop.2]
    · change -i.val.im / (2*Real.pi) = -j.val.im / (2*Real.pi) at hij
      apply neg_injective
      exact (div_left_inj' (by positivity : (2:ℝ)*Real.pi ≠ 0)).mp hij
  have hmode (ρ : CriticalLineZero) (x : ℝ) : -2*Real.pi*ν ρ*x = ρ.val.im*x := by
    dsimp [ν]
    field_simp [Real.pi_ne_zero]
  obtain ⟨f,hf⟩ := exists_logTraceTest_schwartz φ hφ
  let m := (𝓕 f : 𝓢(ℝ,ℂ))
  have hF : (𝓕⁻ (⇑m)) = fun y : ℝ => φ (Real.exp y) := by
    rw [← SchwartzMap.fourierInv_coe]
    change (⇑(𝓕⁻ (𝓕 f) : 𝓢(ℝ,ℂ))) = _
    simpa using (funext hf)
  have hm (ρ : CriticalLineZero) : m (ν ρ) = mellin φ (ρ.val - 1/2) := by
    have hr : ρ.val - 1/2 = Complex.I * (ρ.val.im : ℂ) := by
      apply Complex.ext <;> simp [ρ.prop.2, Complex.mul_re, Complex.mul_im]
    rw [hr, ← fourier_logTraceTest_eq_mellin]
    change (𝓕 (f : ℝ → ℂ)) (ν ρ) = _
    rw [funext hf]
  have h := weighted_spectral_convolution_trace p hp ν hν criticalLineZero_scaled_weight_summable m
  dsimp only at h ⊢
  have hset :
      {f : LogL2 | ∃ i : CriticalLineZero, (f : ℝ → ℂ) =ᵐ[volume] fun x =>
        (((1+|x|)^(-p) : ℝ) : ℂ) * Complex.exp ((-2*Real.pi*ν i*x : ℝ) * Complex.I)} =
      {f : LogL2 | ∃ i : CriticalLineZero, (f : ℝ → ℂ) =ᵐ[volume] fun x =>
        (((1+|x|)^(-p) : ℝ) : ℂ) * Complex.exp (((i.val.im*x : ℝ) : ℂ) * Complex.I)} := by
    simp only [hmode]
  rw [hset] at h
  simpa only [hF, hm] using h
