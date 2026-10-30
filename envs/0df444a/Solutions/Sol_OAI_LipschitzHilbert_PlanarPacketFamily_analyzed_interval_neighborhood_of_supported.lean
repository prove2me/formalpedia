-- Prove2me | solution 1 for OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:05:36.169405+00:00
-- url     : https://prove2.me/submissions/8ce21b37-e431-4c8c-940e-5f1f1d7695f2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ090A002

section
-- module Solutions.OAIQ090_LH.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_IntervalPoincare
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The interval energy estimate needed for the low-frequency part of
the smooth-convolution versus cell-average comparison. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem integral_square_le_mass_mul_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (g : Ω → ℝ)
    (hg : MemLp g 2 μ) (hgn : 0 ≤ᵐ[μ] g) :
    (∫ x, g x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, g x ^ 2 ∂μ := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ)) (g := g) (by filter_upwards; norm_num) hgn
    (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
    (by simpa using hg)
  simp only [one_mul, integral_const, smul_eq_mul, mul_one, Real.rpow_two,
    one_pow] at h
  have hsq := pow_le_pow_left₀ (integral_nonneg_of_ae hgn) h 2
  have heq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  rwa [mul_pow, heq _ measureReal_nonneg, heq _ (integral_nonneg fun _ => sq_nonneg _)] at hsq

theorem interval_pair_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖f x - f y‖ ^ 2 ≤ (b - a) * ∫ t in Icc a b, ‖deriv f t‖ ^ 2 := by
  have hd1 : IntegrableOn (fun t => ‖deriv f t‖) (Icc a b) := hd.norm.integrable (by norm_num)
  have htotal : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u ≤ v →
      ‖f v - f u‖ ≤ ∫ t in Icc a b, ‖deriv f t‖ := by
    intro u hu v hv huv
    have hsub : Icc u v ⊆ Icc a b := fun t ht => ⟨hu.1.trans ht.1, ht.2.trans hv.2⟩
    have hraw := norm_sub_le_integral_of_norm_deriv_le_of_le huv
      (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => (hf t (hsub ⟨ht.1.le,ht.2.le⟩)).differentiableWithinAt)
      (B := fun t => ‖deriv f t‖) (by filter_upwards; intros; rfl)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr (hd1.mono_set hsub))
    refine hraw.trans ?_
    rw [intervalIntegral.integral_of_le huv]
    exact setIntegral_mono_set hd1 (by filter_upwards with t; exact norm_nonneg _)
      (Filter.Eventually.of_forall fun t ht => hsub ⟨ht.1.le,ht.2⟩)
  have hnorm : ‖f x - f y‖ ≤ ∫ t in Icc a b, ‖deriv f t‖ := by
    rcases le_total x y with hxy | hyx
    · rw [norm_sub_rev]
      exact htotal x hx y hy hxy
    · exact htotal y hy x hx hyx
  have hcauchy := integral_square_le_mass_mul_square (volume.restrict (Icc a b))
    (fun t => ‖deriv f t‖) hd.norm (by filter_upwards with t; exact norm_nonneg _)
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hmass] at hcauchy
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcauchy

theorem norm_sub_mean_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (hf : Integrable f μ)
    (hm : 0 < μ.real univ) (v : E) (B : ℝ)
    (hbound : ∀ᵐ y ∂μ, ‖v - f y‖ ≤ B) :
    ‖v - (μ.real univ)⁻¹ • ∫ y, f y ∂μ‖ ≤ B := by
  have heq : v - (μ.real univ)⁻¹ • ∫ y, f y ∂μ =
      (μ.real univ)⁻¹ • ∫ y, (v - f y) ∂μ := by
    rw [integral_sub (integrable_const v) hf, integral_const,
      smul_sub, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  calc
    _ ≤ (μ.real univ)⁻¹ * (B * μ.real univ) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hbound) (inv_nonneg.mpr hm.le)
    _ = B := by rw [mul_comm B, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]

/-- Pointwise Poincaré on one interval, with the actual integral mean. -/
theorem interval_mean_energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x - (b - a)⁻¹ • ∫ y in Icc a b, f y‖ ^ 2 ≤
      (b - a) * ∫ y in Icc a b, ‖deriv f y‖ ^ 2 := by
  let energy := (b - a) * ∫ y in Icc a b, ‖deriv f y‖ ^ 2
  have he : 0 ≤ energy := mul_nonneg (sub_nonneg.mpr hab.le)
    (integral_nonneg fun _ => sq_nonneg _)
  have hmass : (volume.restrict (Icc a b)).real univ = b - a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hcont : ContinuousOn f (Icc a b) := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hbound : ∀ᵐ y ∂volume.restrict (Icc a b), ‖f x - f y‖ ≤ Real.sqrt energy := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt he]
    exact interval_pair_energy f hab.le hf hd hx hy
  have h := norm_sub_mean_le (volume.restrict (Icc a b)) f hcont.integrableOn_Icc
    (by rw [hmass]; exact sub_pos.mpr hab) (f x) (Real.sqrt energy) hbound
  rw [hmass] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [Real.sq_sqrt he] at hsq

/-- Integrated Poincaré with the interval length squared, independent
of the dimension of the Hilbert packet space. -/
theorem interval_poincare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    (∫ x in Icc a b, ‖f x - (b - a)⁻¹ • ∫ y in Icc a b, f y‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Icc a b, ‖deriv f x‖ ^ 2 := by
  have hcont : ContinuousOn f (Icc a b) := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have herr : IntegrableOn
      (fun x => ‖f x - (b - a)⁻¹ • ∫ y in Icc a b, f y‖ ^ 2) (Icc a b) volume :=
    ((hcont.sub continuousOn_const).norm.pow 2).integrableOn_Icc
  have h := integral_mono_ae herr (integrable_const
    ((b - a) * ∫ x in Icc a b, ‖deriv f x‖ ^ 2))
    ((ae_restrict_mem measurableSet_Icc).mono fun x hx => interval_mean_energy f hab hf hd hx)
  rw [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)] at h
  simpa only [pow_two, mul_assoc] using h

theorem interval_poincare_Ico {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) :
    (∫ x in Ico a b, ‖f x - (b - a)⁻¹ • ∫ y in Ico a b, f y‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ x in Ico a b, ‖deriv f x‖ ^ 2 := by
  simpa only [integral_Icc_eq_integral_Ico] using interval_poincare f hab hf hd

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalNeighborhood
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent vertical neighborhood control from the actual
function and its vertical derivative. The moment application only needs
this fixed interval Sobolev estimate. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem interval_pointwise_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b))) {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖^2 ≤ (2/(b-a)) * (∫ t in Icc a b, ‖f t‖^2) +
      2*(b-a)*(∫ t in Icc a b, ‖deriv f t‖^2) := by
  have hm : 0 < b-a := sub_pos.mpr hab
  have hcont : ContinuousOn f (Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun t => ‖f t‖^2) (Icc a b) volume :=
    (hcont.norm.pow 2).integrableOn_Icc
  let D := (b-a) * ∫ t in Icc a b, ‖deriv f t‖^2
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) : ‖f x‖^2 ≤ 2*‖f t‖^2+2*D := by
    have hp := interval_pair_energy f hab.le hf hd hx ht
    have hn : ‖f x‖ ≤ ‖f t‖ + ‖f x-f t‖ := by
      simpa only [add_sub_cancel] using norm_add_le (f t) (f x-f t)
    have hs := pow_le_pow_left₀ (norm_nonneg (f x)) hn 2
    dsimp [D]
    nlinarith [sq_nonneg (‖f t‖-‖f x-f t‖)]
  have hint := integral_mono_ae
    (integrable_const (‖f x‖^2) : Integrable (fun _ : ℝ => ‖f x‖^2) (volume.restrict (Icc a b)))
    ((hi.const_mul 2).add (integrable_const (2*D)))
    ((ae_restrict_mem measurableSet_Icc).mono (fun t ht => hpoint t ht))
  have hmass : (volume.restrict (Icc a b)).real univ = b-a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hm.le]
  dsimp only [Pi.add_apply] at hint
  rw [integral_add (hi.const_mul 2) (integrable_const (2*D)), integral_const_mul,
    integral_const, integral_const, hmass] at hint
  simp only [smul_eq_mul] at hint
  have heq : (2/(b-a)) * (∫ t in Icc a b, ‖f t‖^2) * (b-a) =
      2 * ∫ t in Icc a b, ‖f t‖^2 := by field_simp [hm.ne']
  dsimp [D] at hint
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_AveragedSquareMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Even moments of the vertical Sobolev majorant. The constants are
independent of the number of packet sums and of their Hilbert dimension. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem average_natPow_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] (f : Ω → ℝ) (n : ℕ)
    (hf : Integrable f μ) (hfn : Integrable (fun t => f t ^ n) μ)
    (hf0 : ∀ᵐ t ∂μ, 0 ≤ f t) :
    (⨍ t, f t ∂μ)^n ≤ ⨍ t, f t^n ∂μ := by
  exact (convexOn_pow n).map_average_le (continuous_id.pow n).continuousOn
    isClosed_Ici hf0 hf hfn

theorem averaged_square_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] [NeZero μ] (V D : Ω → ℝ) (n : ℕ)
    (hV : Integrable (fun t => V t^2) μ) (hD : Integrable (fun t => D t^2) μ)
    (hn : Integrable (fun t => (V t^2 + D t^2)^n) μ)
    (hVn : Integrable (fun t => V t^(2*n)) μ)
    (hDn : Integrable (fun t => D t^(2*n)) μ) :
    (2 * ⨍ t, V t^2 + D t^2 ∂μ)^n ≤
      4^n * ⨍ t, V t^(2*n) + D t^(2*n) ∂μ := by
  have hj := average_natPow_le μ (fun t => V t^2 + D t^2) n (hV.add hD) hn
    (Filter.Eventually.of_forall fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hp (t : Ω) : (V t^2 + D t^2)^n ≤
      2^n * (V t^(2*n) + D t^(2*n)) := by
    calc
      _ ≤ 2^(n-1) * ((V t^2)^n + (D t^2)^n) := add_pow_le (sq_nonneg _) (sq_nonneg _) n
      _ ≤ 2^n * ((V t^2)^n + (D t^2)^n) := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)) (by positivity)
      _ = _ := by simp only [pow_mul]
  have ha := integral_mono_ae hn ((hVn.add hDn).const_mul (2^n))
    (Filter.Eventually.of_forall hp)
  dsimp only [Pi.add_apply] at ha
  rw [integral_const_mul] at ha
  have hav : (⨍ t, (V t^2 + D t^2)^n ∂μ) ≤
      2^n * ⨍ t, V t^(2*n) + D t^(2*n) ∂μ := by
    simp only [average_eq, smul_eq_mul]
    calc
      _ ≤ (μ.real univ)⁻¹ * (2^n * ∫ t, V t^(2*n) + D t^(2*n) ∂μ) :=
        mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr measureReal_nonneg)
      _ = _ := by ring
  calc
    _ = 2^n * (⨍ t, V t^2 + D t^2 ∂μ)^n := mul_pow _ _ _
    _ ≤ 2^n * (2^n * ⨍ t, V t^(2*n) + D t^(2*n) ∂μ) := by
      exact mul_le_mul_of_nonneg_left (hj.trans hav) (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzBandEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two band-energy inequalities used by the actual cell-average
comparison, proved from Mathlib's Schwartz Plancherel theorem. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem schwartz_fourier_deriv (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ f) ξ =
      (2 * Real.pi * Complex.I * ξ) • 𝓕 f ξ := by
  exact congrFun (Real.fourier_deriv f.integrable f.differentiable
    (SchwartzMap.derivCLM ℂ ℂ f).integrable) ξ

theorem norm_fourier_deriv_coefficient (ξ : ℝ) :
    ‖(2 * Real.pi * Complex.I * ξ : ℂ)‖ = 2 * Real.pi * |ξ| := by
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]

theorem schwartz_band_derivative_upper (f : SchwartzMap ℝ ℂ) {R : ℝ} (_hR : 0 ≤ R)
    (hband : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0) :
    (∫ x, ‖deriv f x‖ ^ 2) ≤ (2 * Real.pi * R) ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  let df := SchwartzMap.derivCLM ℂ ℂ f
  have hpoint (ξ : ℝ) : ‖𝓕 df ξ‖ ^ 2 ≤ (2 * Real.pi * R) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
    by_cases hξ : |ξ| ≤ R
    · rw [schwartz_fourier_deriv, norm_smul, norm_fourier_deriv_coefficient, mul_pow]
      gcongr
    · rw [schwartz_fourier_deriv, hband ξ (lt_of_not_ge hξ)]
      simp
  calc
    _ = ∫ ξ, ‖𝓕 df ξ‖ ^ 2 := by
      simpa only [df, SchwartzMap.derivCLM_apply] using
        (SchwartzMap.integral_norm_sq_fourier df).symm
    _ ≤ ∫ ξ, (2 * Real.pi * R) ^ 2 * ‖𝓕 f ξ‖ ^ 2 :=
      integral_mono (((𝓕 df).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0))
        ((((𝓕 f).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul _) hpoint
    _ = _ := by rw [integral_const_mul, SchwartzMap.integral_norm_sq_fourier]

theorem schwartz_band_derivative_lower (f : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 0 < r)
    (hband : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0) :
    (2 * Real.pi * r) ^ 2 * (∫ x, ‖f x‖ ^ 2) ≤ ∫ x, ‖deriv f x‖ ^ 2 := by
  let df := SchwartzMap.derivCLM ℂ ℂ f
  have hpoint (ξ : ℝ) : (2 * Real.pi * r) ^ 2 * ‖𝓕 f ξ‖ ^ 2 ≤ ‖𝓕 df ξ‖ ^ 2 := by
    by_cases hξ : r ≤ |ξ|
    · rw [schwartz_fourier_deriv, norm_smul, norm_fourier_deriv_coefficient, mul_pow]
      simp only [mul_pow]
      gcongr
    · rw [schwartz_fourier_deriv, hband ξ (lt_of_not_ge hξ)]
      simp
  calc
    _ = ∫ ξ, (2 * Real.pi * r) ^ 2 * ‖𝓕 f ξ‖ ^ 2 := by
      rw [integral_const_mul, SchwartzMap.integral_norm_sq_fourier]
    _ ≤ ∫ ξ, ‖𝓕 df ξ‖ ^ 2 :=
      integral_mono ((((𝓕 f).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul _)
        (((𝓕 df).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)) hpoint
    _ = _ := by
      simpa only [df, SchwartzMap.derivCLM_apply] using SchwartzMap.integral_norm_sq_fourier df

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_CoordinateFourierSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Multiplication by the line coordinate preserves Fourier support for
Schwartz functions. This is the first step in polynomial localization of
the annular packet variation estimate. -/

noncomputable section

open MeasureTheory Function FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem coordinateProduct_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    coordinateProduct f x = (x : ℂ) * f x := by
  simpa only [coordinateProduct, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply Function.Complex.hasTemperateGrowth_ofReal f x

theorem fourier_coordinate_derivative (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (𝓕 f) =
      (-2 * Real.pi * Complex.I : ℂ) • 𝓕 (coordinateProduct f) := by
  have hxf : Integrable (fun x : ℝ => x • f x) := by
    have hcp : Integrable (coordinateProduct f : ℝ → ℂ) volume := (coordinateProduct f).integrable
    convert hcp using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    rw [coordinateProduct_apply, Complex.real_smul]
  have h := Real.deriv_fourier f.integrable hxf
  have hprod : (fun x : ℝ => (-2 * Real.pi * Complex.I * x : ℂ) • f x) =
      ((-2 * Real.pi * Complex.I : ℂ) • coordinateProduct f : SchwartzMap ℝ ℂ) := by
    funext x
    simp only [smul_apply, coordinateProduct_apply, smul_eq_mul]
    ring
  ext x
  change deriv (𝓕 (f : ℝ → ℂ)) x = _
  rw [h, hprod]
  simp only [← SchwartzMap.fourier_coe, fourier_smul, smul_apply]

theorem coordinateProduct_fourier_support (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (coordinateProduct f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hout
  have hz : deriv (𝓕 f : SchwartzMap ℝ ℂ) x = 0 := deriv_of_notMem_tsupport hout
  have hd := congrArg (fun g : SchwartzMap ℝ ℂ => g x) (fourier_coordinate_derivative f)
  simp only [SchwartzMap.derivCLM_apply, smul_apply, smul_eq_mul, hz] at hd
  have hc : (-2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  have hf0 : 𝓕 (coordinateProduct f) x = 0 := (mul_eq_zero.mp hd.symm).resolve_left hc
  exact hx hf0

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive polynomial weights used to localize annular packets on a
reference line. Their construction and Fourier support preservation are
proved here for the actual Schwartz functions. -/

noncomputable section

open Function FourierTransform
open scoped FourierTransform

namespace LipschitzHilbert

theorem fourier_support_add_subset (f g : SchwartzMap ℝ ℂ) {S : Set ℝ}
    (hS : IsClosed S)
    (hf : tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ S)
    (hg : tsupport ((𝓕 g : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ S) :
    tsupport ((𝓕 (f + g) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ S := by
  apply closure_minimal _ hS
  intro x hx
  by_contra hout
  have hf0 : 𝓕 f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hout (hf h))
  have hg0 : 𝓕 g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hout (hg h))
  apply hx
  have heq : (𝓕 (f + g) : SchwartzMap ℝ ℂ) = 𝓕 f + 𝓕 g := fourier_add f g
  rw [heq]
  change 𝓕 f x + 𝓕 g x = 0
  rw [hf0, hg0, add_zero]

theorem fourier_support_smul_subset (c : ℂ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (c • f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  rw [fourier_smul]
  exact tsupport_smul_subset_right (fun _ => c) _

theorem centeredCoordinateProduct_apply (a : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    centeredCoordinateProduct a f x = ((x - a : ℝ) : ℂ) * f x := by
  simp only [centeredCoordinateProduct, add_apply, smul_apply, coordinateProduct_apply,
    smul_eq_mul, Complex.ofReal_sub]
  ring

theorem centeredCoordinateProduct_fourier_support (a : ℝ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (centeredCoordinateProduct a f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
  fourier_support_add_subset _ _ isClosed_closure
    (coordinateProduct_fourier_support f) (fourier_support_smul_subset _ f)

theorem quadraticLocalization_apply (a r : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    quadraticLocalization a r f x = ((1 + (x - a) ^ 2 / r ^ 2 : ℝ) : ℂ) * f x := by
  simp only [quadraticLocalization, add_apply, smul_apply, smul_eq_mul,
    centeredCoordinateProduct_apply, Complex.ofReal_add, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_inv]
  ring

theorem quadraticLocalization_fourier_support (a r : ℝ) (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (quadraticLocalization a r f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  apply fourier_support_add_subset _ _ isClosed_closure (Set.Subset.refl _)
  exact (fourier_support_smul_subset _ _).trans
    ((centeredCoordinateProduct_fourier_support a _).trans
      (centeredCoordinateProduct_fourier_support a f))

theorem polynomialLocalization_apply (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    polynomialLocalization a r q f x = (polynomialWeight a r q x : ℂ) * f x := by
  induction q with
  | zero => simp [polynomialLocalization, polynomialWeight]
  | succ q ih =>
    rw [polynomialLocalization, quadraticLocalization_apply, ih]
    simp only [polynomialWeight, pow_succ, Complex.ofReal_mul]
    ring

theorem polynomialWeight_one_le (a r : ℝ) (q : ℕ) (x : ℝ) :
    1 ≤ polynomialWeight a r q x := by
  have hbase : 1 ≤ 1 + (x - a) ^ 2 / r ^ 2 := by
    have h := div_nonneg (sq_nonneg (x - a)) (sq_nonneg r)
    linarith
  exact one_le_pow₀ hbase

theorem polynomialLocalization_fourier_support (a r : ℝ) (q : ℕ)
    (f : SchwartzMap ℝ ℂ) :
    tsupport ((𝓕 (polynomialLocalization a r q f) : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  induction q with
  | zero => exact Set.Subset.refl _
  | succ q ih => exact (quadraticLocalization_fourier_support a r _).trans ih

theorem fourier_support_annulus (f : SchwartzMap ℝ ℂ) (lo hi : ℝ)
    (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) :
    tsupport ((𝓕 f : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆
      {ξ | lo ≤ |ξ| ∧ |ξ| ≤ hi} := by
  apply closure_minimal
  · intro ξ hξ
    exact ⟨le_of_not_gt (fun h => hξ (hlow ξ h)),
      le_of_not_gt (fun h => hξ (hhigh ξ h))⟩
  · exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)

theorem polynomialLocalization_low (a r : ℝ) (q : ℕ) (f : SchwartzMap ℝ ℂ)
    (lo hi : ℝ) (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : |ξ| < lo) :
    𝓕 (polynomialLocalization a r q f) ξ = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact (not_le_of_gt hξ) ((fourier_support_annulus f lo hi hlow hhigh)
    (polynomialLocalization_fourier_support a r q f hmem)).1

theorem polynomialLocalization_high (a r : ℝ) (q : ℕ) (f : SchwartzMap ℝ ℂ)
    (lo hi : ℝ) (hlow : ∀ ξ, |ξ| < lo → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, hi < |ξ| → 𝓕 f ξ = 0) (ξ : ℝ) (hξ : hi < |ξ|) :
    𝓕 (polynomialLocalization a r q f) ξ = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  exact (not_le_of_gt hξ) ((fourier_support_annulus f lo hi hlow hhigh)
    (polynomialLocalization_fourier_support a r q f hmem)).2

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SequenceNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Monotonicity of finite sequence norms and the small-remainder estimate. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι : Type*} [Fintype ι]

theorem sum_rpow_le_rpow_sum (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {p : ℝ} (hp : 1 ≤ p) : (∑ i, x i ^ p) ≤ (∑ i, x i) ^ p := by
  have hp0 : 0 < p := by linarith
  have h (s : Finset ι) : (∑ i ∈ s, x i ^ p) ≤ (∑ i ∈ s, x i) ^ p := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow hp0.ne']
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      calc
        x i ^ p + ∑ j ∈ s, x j ^ p ≤ x i ^ p + (∑ j ∈ s, x j) ^ p :=
          add_le_add le_rfl ih
        _ ≤ (x i + ∑ j ∈ s, x j) ^ p :=
          Real.add_rpow_le_rpow_add (hx i) (Finset.sum_nonneg (fun j _ => hx j)) hp
  exact h Finset.univ

theorem sum_powers_exponent_comparison (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    (∑ i, x i ^ q) ≤ (∑ i, x i ^ p) ^ (q / p) := by
  have h := sum_rpow_le_rpow_sum (fun i => x i ^ p)
    (fun i => Real.rpow_nonneg (hx i) p) ((le_div_iff₀ hp).2 (by simpa using hpq))
  have heq (i : ι) : (x i ^ p) ^ (q / p) = x i ^ q := by
    rw [← Real.rpow_mul (hx i)]
    congr 1
    field_simp
  simpa only [heq] using h

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MixedNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mixed-norm comparisons for the diagonal Hilbert-valued extension. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.PhaseCombinatorics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem finite_minkowski (x : ι → κ → ℝ) (hx : ∀ i j, 0 ≤ x i j)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ j, (∑ i, x i j) ^ p) ^ (1 / p) ≤
      ∑ i, (∑ j, x i j ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h (s : Finset ι) : (∑ j, (∑ i ∈ s, x i j) ^ p) ^ (1 / p) ≤
      ∑ i ∈ s, (∑ j, x i j ^ p) ^ (1 / p) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')]
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      have hm := Real.Lp_add_le_of_nonneg (Finset.univ : Finset κ)
        (f := fun j => x i j) (g := fun j => ∑ k ∈ s, x k j) hp
        (fun j _ => hx i j) (fun j _ => Finset.sum_nonneg (fun k _ => hx k j))
      exact hm.trans (add_le_add le_rfl ih)
  exact h Finset.univ

end LipschitzHilbert.PhaseCombinatorics

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic variation and its dimension-free Euclidean comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem finiteCubicVariation_nonneg {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) : 0 ≤ finiteCubicVariation F N := by
  classical
  apply Finset.le_sup'_of_le (f := fun p : Fin (N + 1) → Fin (N + 1) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
    (Finset.mem_univ (fun _ => 0))
  simp

theorem partition_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ≤
      finiteCubicVariation F N := by
  classical
  simpa only [finiteCubicVariation, ite_eq_left hp] using
    (Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
      (Finset.mem_univ p))

theorem scalar_finiteCubicVariation {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) :
    ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) = variationCube F N x := by
  classical
  have heq (p : Fin (N + 1) → Fin (N + 1)) :
      ENNReal.ofReal (if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) =
      if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0 := by
    split_ifs
    · rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    · exact ENNReal.ofReal_zero
  apply le_antisymm
  · obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0)
    change ENNReal.ofReal (Finset.univ.sup' _ _) ≤ _
    rw [hp, heq]
    change (if Monotone p then ∑ i : Fin N,
      ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0) ≤
      Finset.univ.sup _
    exact Finset.le_sup (f := fun q : Fin (N + 1) → Fin (N + 1) =>
      if Monotone q then ∑ i : Fin N,
        ‖F (q i.succ) x - F (q i.castSucc) x‖ₑ ^ 3 else 0) (Finset.mem_univ p)
  · apply Finset.sup_le
    intro p _
    rw [← heq]
    apply ENNReal.ofReal_le_ofReal
    exact Finset.le_sup' (fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then ∑ i : Fin N,
        ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0) (Finset.mem_univ p)

/-- Minkowski in `ℓ^(3/2)` moves the Euclidean coordinates outside the
variation. The constant does not depend on the number of coordinates. -/
theorem euclidean_partition_variation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℝ κ) (N : ℕ)
    (p : Fin (N + 1) → Fin (N + 1)) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ^ (2 / 3 : ℝ) ≤
      ∑ k, (∑ i : Fin N,
        ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 3) ^ (2 / 3 : ℝ) := by
  have hpow (a : ℝ) (ha : 0 ≤ a) : (a ^ 2) ^ (3 / 2 : ℝ) = a ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have h := PhaseCombinatorics.finite_minkowski
    (fun k (i : Fin N) => ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2)
    (fun _ _ => sq_nonneg _) (by norm_num : (1 : ℝ) ≤ 3 / 2)
  norm_num only [one_div_div, div_one] at h
  have hsum (i : Fin N) :
      (∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2) ^ (3 / 2 : ℝ) =
      ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 := by
    have heq : ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2 =
        ∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    rw [← heq]
    exact hpow _ (norm_nonneg _)
  simpa only [hsum, hpow _ (norm_nonneg _)] using h

theorem euclidean_finiteCubicVariation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℝ κ) (N : ℕ) :
    (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      ∑ k, (finiteCubicVariation (fun n => F n k) N) ^ (2 / 3 : ℝ) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (2 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    apply (euclidean_partition_variation_le F N p).trans
    apply Finset.sum_le_sum
    intro k _
    exact Real.rpow_le_rpow (by positivity)
      (partition_le_finiteCubicVariation (fun n => F n k) N p hmono) (by norm_num)
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    exact Finset.sum_nonneg fun k _ =>
      Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationPerturbation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-summable error in the smooth/dyadic comparison controls
its entire cubic variation, uniformly in the number of scales. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem cubic_sum_rpow_le_square_sum {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ 3) ^ (2 / 3 : ℝ) ≤ ∑ i, a i ^ 2 := by
  have h := PhaseCombinatorics.sum_powers_exponent_comparison a ha
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
  norm_num only [Real.rpow_ofNat] at h
  have hpow := Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => pow_nonneg (ha i) 3)
    h (by norm_num : (0 : ℝ) ≤ 2 / 3)
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ => sq_nonneg (a i))] at hpow
  norm_num at hpow ⊢
  exact hpow

theorem monotone_partition_square_sum {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2) ≤
      4 * ∑ k : Fin (N + 1), ‖F k‖ ^ 2 := by
  classical
  let s := Finset.univ.filter (fun i : Fin N => p i.castSucc < p i.succ)
  have hstep (i j : Fin N) (hij : i < j) : p i.succ ≤ p j.castSucc :=
    hp (by simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
      (show i.val + 1 ≤ j.val by omega))
  have hleft : Set.InjOn (fun i : Fin N => p i.castSucc) s := by
    intro i hi j hj heq
    change p i.castSucc = p j.castSucc at heq
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((not_lt_of_ge (hstep i j hij)) (by simpa only [heq] using hi'))
    · exact hij
    · exact False.elim ((not_lt_of_ge (hstep j i hij)) (by simpa only [heq] using hj'))
  have hright : Set.InjOn (fun i : Fin N => p i.succ) s := by
    intro i hi j hj heq
    change p i.succ = p j.succ at heq
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((not_lt_of_ge (hstep i j hij)) (by simpa only [heq] using hj'))
    · exact hij
    · exact False.elim ((not_lt_of_ge (hstep j i hij)) (by simpa only [heq] using hi'))
  have hsumleft : (∑ i ∈ s, ‖F (p i.castSucc)‖ ^ 2) ≤
      ∑ k : Fin (N + 1), ‖F k‖ ^ 2 :=
    OAI.sum_le_sum_of_injOn (fun i : Fin N => p i.castSucc) hleft
      (Finset.subset_univ _) (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)
  have hsumright : (∑ i ∈ s, ‖F (p i.succ)‖ ^ 2) ≤
      ∑ k : Fin (N + 1), ‖F k‖ ^ 2 :=
    OAI.sum_le_sum_of_injOn (fun i : Fin N => p i.succ) hright
      (Finset.subset_univ _) (fun _ _ => le_rfl) (fun _ _ _ => sq_nonneg _)
  have hrestrict : (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2) =
      ∑ i ∈ s, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hle : p i.castSucc ≤ p i.succ := hp (Fin.castSucc_le_succ i)
    have heq : p i.castSucc = p i.succ := le_antisymm hle
      (le_of_not_gt (by simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hi))
    simp [heq]
  rw [hrestrict]
  calc
    _ ≤ ∑ i ∈ s, 2 * (‖F (p i.succ)‖ ^ 2 + ‖F (p i.castSucc)‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      have hnorm := norm_sub_le (F (p i.succ)) (F (p i.castSucc))
      have hsquare := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hnorm
      nlinarith [sq_nonneg (‖F (p i.succ)‖ - ‖F (p i.castSucc)‖)]
    _ = 2 * ((∑ i ∈ s, ‖F (p i.succ)‖ ^ 2) +
        ∑ i ∈ s, ‖F (p i.castSucc)‖ ^ 2) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 4 * ∑ k : Fin (N + 1), ‖F k‖ ^ 2 := by linarith

theorem finiteCubicVariation_le_square_energy {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) :
    (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      4 * ∑ k : Fin (N + 1), ‖F k‖ ^ 2 := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (2 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    exact (cubic_sum_rpow_le_square_sum _ (fun _ => norm_nonneg _)).trans
      (monotone_partition_square_sum F N p hmono)
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    positivity

theorem finiteCubicVariation_add_rpow {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) :
    (finiteCubicVariation (fun n => F n + G n) N) ^ (1 / 3 : ℝ) ≤
      (finiteCubicVariation F N) ^ (1 / 3 : ℝ) +
        (finiteCubicVariation G N) ^ (1 / 3 : ℝ) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖(F (p i.succ) + G (p i.succ)) -
        (F (p i.castSucc) + G (p i.castSucc))‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (1 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    calc
      _ ≤ (∑ i : Fin N, (‖F (p i.succ) - F (p i.castSucc)‖ +
          ‖G (p i.succ) - G (p i.castSucc)‖) ^ 3) ^ (1 / 3 : ℝ) := by
        apply Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => by positivity) _ (by norm_num)
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [add_sub_add_comm]
        exact norm_add_le _ _
      _ ≤ (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ^ (1 / 3 : ℝ) +
          (∑ i : Fin N, ‖G (p i.succ) - G (p i.castSucc)‖ ^ 3) ^ (1 / 3 : ℝ) := by
        simpa only [Real.rpow_ofNat] using Real.Lp_add_le_of_nonneg
          (Finset.univ : Finset (Fin N)) (by norm_num : (1 : ℝ) ≤ 3)
          (f := fun i => ‖F (p i.succ) - F (p i.castSucc)‖)
          (g := fun i => ‖G (p i.succ) - G (p i.castSucc)‖)
          (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      _ ≤ _ := add_le_add
        (Real.rpow_le_rpow (by positivity) (partition_le_finiteCubicVariation F N p hmono)
          (by norm_num))
        (Real.rpow_le_rpow (by positivity) (partition_le_finiteCubicVariation G N p hmono)
          (by norm_num))
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (1 / 3 : ℝ) ≠ 0)]
    exact add_nonneg (Real.rpow_nonneg (finiteCubicVariation_nonneg F N) _)
      (Real.rpow_nonneg (finiteCubicVariation_nonneg G N) _)

theorem finiteCubicVariation_add_square {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) :
    (finiteCubicVariation (fun n => F n + G n) N) ^ (2 / 3 : ℝ) ≤
      2 * (finiteCubicVariation F N) ^ (2 / 3 : ℝ) +
        2 * (finiteCubicVariation G N) ^ (2 / 3 : ℝ) := by
  have h := finiteCubicVariation_add_rpow F G N
  have hsq := pow_le_pow_left₀ (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _) h 2
  have heq (a : ℝ) (ha : 0 ≤ a) : (a ^ (1 / 3 : ℝ)) ^ 2 = a ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hcross := sq_nonneg ((finiteCubicVariation F N) ^ (1 / 3 : ℝ) -
    (finiteCubicVariation G N) ^ (1 / 3 : ℝ))
  rw [sub_sq, heq _ (finiteCubicVariation_nonneg F N),
    heq _ (finiteCubicVariation_nonneg G N)] at hcross
  rw [heq _ (finiteCubicVariation_nonneg _ _)] at hsq
  rw [add_sq, heq _ (finiteCubicVariation_nonneg F N),
    heq _ (finiteCubicVariation_nonneg G N)] at hsq
  linarith

/-- The manuscript's smooth partial sums are a dyadic martingale plus
the square-summable comparison error. No scale-count factor occurs. -/
theorem finiteCubicVariation_comparison {E : Type*} [NormedAddCommGroup E]
    (P M : ℕ → E) (N : ℕ) :
    (finiteCubicVariation P N) ^ (2 / 3 : ℝ) ≤
      2 * (finiteCubicVariation M N) ^ (2 / 3 : ℝ) +
        8 * ∑ k : Fin (N + 1), ‖P k - M k‖ ^ 2 := by
  have heq : (fun n => M n + (P n - M n)) = P := by funext n; abel
  have h := finiteCubicVariation_add_square M (fun n => P n - M n) N
  rw [heq] at h
  exact h.trans (add_le_add le_rfl
    (by linarith [finiteCubicVariation_le_square_energy (fun n => P n - M n) N]))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact behavior of finite interval-sum variation under a common scalar.
This keeps polynomial localization independent of the number of scales. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem finiteCubicVariation_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (F : ℕ → E) (N : ℕ) :
    finiteCubicVariation (fun i => c • F i) N = |c| ^ 3 * finiteCubicVariation F N := by
  classical
  unfold finiteCubicVariation
  rw [Finset.mul₀_sup' (pow_nonneg (abs_nonneg c) 3)]
  congr 1
  funext p
  split_ifs with hp
  · simp only [← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, Finset.mul_sum]
  · exact (mul_zero _).symm

theorem finiteCubicVariation_smul_square {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (F : ℕ → E) (N : ℕ) :
    (finiteCubicVariation (fun i => c • F i) N) ^ (2 / 3 : ℝ) =
      c ^ 2 * (finiteCubicVariation F N) ^ (2 / 3 : ℝ) := by
  rw [finiteCubicVariation_smul, Real.mul_rpow (pow_nonneg (abs_nonneg c) 3)
    (finiteCubicVariation_nonneg F N)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg c)]
  norm_num [sq_abs]

theorem ennreal_finiteCubicVariation_smul_square {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : ℝ) (F : ℕ → E) (N : ℕ) :
    ENNReal.ofReal (finiteCubicVariation (fun i => c • F i) N) ^ (2 / 3 : ℝ) =
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (finiteCubicVariation F N) ^ (2 / 3 : ℝ) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num),
    finiteCubicVariation_smul_square, ENNReal.ofReal_mul (sq_nonneg c),
    ← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationSubsequence
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sampling partial sums at increasing times cannot increase variation. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem finiteCubicVariation_comp_le {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (q : ℕ → ℕ) (hq : Monotone q) (hN : q N ≤ N) :
    finiteCubicVariation (fun n => F (q n)) N ≤ finiteCubicVariation F N := by
  classical
  unfold finiteCubicVariation
  apply Finset.sup'_le
  intro p _
  by_cases hp : Monotone p
  · rw [ite_eq_left hp]
    let r : Fin (N + 1) → Fin (N + 1) := fun k =>
      ⟨q (p k).val, by have := (hq (show (p k).val ≤ N by omega)).trans hN; omega⟩
    have hr : Monotone r := by
      intro i j hij
      exact hq (hp hij)
    exact partition_le_finiteCubicVariation F N r hr
  · rw [ite_eq_right hp]
    exact finiteCubicVariation_nonneg F N

theorem finiteCubicVariation_congr {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) (h : ∀ i, i ≤ N → F i = G i) :
    finiteCubicVariation F N = finiteCubicVariation G N := by
  classical
  unfold finiteCubicVariation
  congr 1
  funext p
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [h (p i.succ) (by have := (p i.succ).isLt; omega),
    h (p i.castSucc) (by have := (p i.castSucc).isLt; omega)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteEnergySchur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite weighted energy summation for the smooth/dyadic comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_sum_norm_square {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (v : ι → E) (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    ‖∑ j, v j‖ ^ 2 ≤ (∑ j, w j) * ∑ j, ‖v j‖ ^ 2 / w j := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := w) (g := fun j => ‖v j‖ ^ 2 / w j) (r := fun j => ‖v j‖)
    (fun j _ => (hw j).le) (fun j _ => div_nonneg (sq_nonneg _) (hw j).le)
    (fun j _ => by rw [mul_div_cancel₀ _ (hw j).ne'])
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hcs

theorem weighted_integral_sum_square {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] (μ : Measure Ω)
    (F : ι → Ω → E) (hF : ∀ j, MemLp (F j) 2 μ)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    (∫ x, ‖∑ j, F j x‖ ^ 2 ∂μ) ≤
      (∑ j, w j) * ∑ j, (∫ x, ‖F j x‖ ^ 2 ∂μ) / w j := by
  have hsum : MemLp (fun x => ∑ j, F j x) 2 μ := by
    simpa only [Finset.sum_apply] using memLp_finsetSum Finset.univ (fun j _ => hF j)
  have hint (j : ι) : Integrable (fun x => ‖F j x‖ ^ 2 / w j) μ :=
    ((hF j).integrable_norm_pow (by decide : 2 ≠ 0)).div_const _
  calc
    _ ≤ ∫ x, (∑ j, w j) * ∑ j, ‖F j x‖ ^ 2 / w j ∂μ :=
      integral_mono (hsum.integrable_norm_pow (by decide : 2 ≠ 0))
        ((integrable_finsetSum _ (fun j _ => hint j)).const_mul _)
        (fun x => weighted_sum_norm_square (fun j => F j x) w hw)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ => hint j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact integral_div _ _

theorem finite_energy_schur {Ω ι κ E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] [NormedAddCommGroup E]
    (μ : Measure Ω) (F : ι → κ → Ω → E)
    (hF : ∀ i j, MemLp (F i j) 2 μ) (a : ι → κ → ℝ)
    (ha : ∀ i j, 0 < a i j) (b : κ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {R C : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, a i j ≤ R) (hcol : ∀ j, ∑ i, a i j ≤ C)
    (hbound : ∀ i j, (∫ x, ‖F i j x‖ ^ 2 ∂μ) ≤ a i j ^ 2 * b j) :
    (∑ i, ∫ x, ‖∑ j, F i j x‖ ^ 2 ∂μ) ≤ R * C * ∑ j, b j := by
  have hcell (i : ι) (j : κ) :
      (∫ x, ‖F i j x‖ ^ 2 ∂μ) / a i j ≤ a i j * b j := by
    apply (div_le_iff₀ (ha i j)).mpr
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hbound i j
  have hrowbound (i : ι) : (∫ x, ‖∑ j, F i j x‖ ^ 2 ∂μ) ≤
      R * ∑ j, a i j * b j := by
    calc
      _ ≤ (∑ j, a i j) * ∑ j, (∫ x, ‖F i j x‖ ^ 2 ∂μ) / a i j :=
        weighted_integral_sum_square μ (F i) (hF i) (a i) (ha i)
      _ ≤ (∑ j, a i j) * ∑ j, a i j * b j :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hcell i j))
          (Finset.sum_nonneg (fun j _ => (ha i j).le))
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg (fun j _ => mul_nonneg (ha i j).le (hb j)))
  calc
    _ ≤ ∑ i, R * ∑ j, a i j * b j := Finset.sum_le_sum (fun i _ => hrowbound i)
    _ = R * ∑ j, (∑ i, a i j) * b j := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ R * ∑ j, C * b j := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (hb j))) hR
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricScaleWeights
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform row and column bounds for the actual geometric scale kernel. -/

open scoped BigOperators

noncomputable section

namespace LipschitzHilbert

theorem sum_half_powers_le_two (N : ℕ) :
    (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
  have heq : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) =
      2 * (1 - (1 / 2 : ℝ) ^ N) := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [heq]
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N]

theorem sum_half_distance_le_four (N i : ℕ) :
    (∑ j : Fin N, (1 / 2 : ℝ) ^ Nat.dist i j.val) ≤ 4 := by
  classical
  let s := Finset.univ.filter (fun j : Fin N => j.val ≤ i)
  let t := Finset.univ.filter (fun j : Fin N => ¬j.val ≤ i)
  have hs : (∑ j ∈ s, (1 / 2 : ℝ) ^ Nat.dist i j.val) ≤ 2 := by
    have hinj : Set.InjOn (fun j : Fin N => i - j.val) s := by
      intro j hj k hk heq
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      change i - j.val = i - k.val at heq
      apply Fin.ext
      omega
    have hmap : s.image (fun j : Fin N => i - j.val) ⊆
        Finset.range (i + N + 1) := by
      intro n hn
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
      simp only [Finset.mem_range]
      omega
    have h := OAI.sum_le_sum_of_injOn (fun j : Fin N => i - j.val) hinj hmap
      (s := s) (t := Finset.range (i + N + 1))
      (f := fun j => (1 / 2 : ℝ) ^ Nat.dist i j.val)
      (g := fun n => (1 / 2 : ℝ) ^ n)
      (fun j hj => by rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hj).2])
      (fun n _ _ => pow_nonneg (by norm_num) n)
    exact h.trans (sum_half_powers_le_two _)
  have ht : (∑ j ∈ t, (1 / 2 : ℝ) ^ Nat.dist i j.val) ≤ 2 := by
    have hinj : Set.InjOn (fun j : Fin N => j.val - i) t := by
      intro j hj k hk heq
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      change j.val - i = k.val - i at heq
      apply Fin.ext
      omega
    have hmap : t.image (fun j : Fin N => j.val - i) ⊆
        Finset.range (i + N + 1) := by
      intro n hn
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
      simp only [Finset.mem_range]
      have := j.isLt
      omega
    have h := OAI.sum_le_sum_of_injOn (fun j : Fin N => j.val - i) hinj hmap
      (s := t) (t := Finset.range (i + N + 1))
      (f := fun j => (1 / 2 : ℝ) ^ Nat.dist i j.val)
      (g := fun n => (1 / 2 : ℝ) ^ n)
      (fun j hj => by
        rw [Nat.dist_eq_sub_of_le (by have := (Finset.mem_filter.mp hj).2; omega)])
      (fun n _ _ => pow_nonneg (by norm_num) n)
    exact h.trans (sum_half_powers_le_two _)
  have heq := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin N => j.val ≤ i) (fun j => (1 / 2 : ℝ) ^ Nat.dist i j.val)
  change (∑ j ∈ s, (1 / 2 : ℝ) ^ Nat.dist i j.val) +
    (∑ j ∈ t, (1 / 2 : ℝ) ^ Nat.dist i j.val) = _ at heq
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_HilbertVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional Hilbert consequence of the published scalar input. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

theorem measurable_variationCube {Ω : Type*} [MeasurableSpace Ω]
    (F : ℕ → Ω → ℝ) (hF : ∀ n, Measurable (F n)) (N : ℕ) :
    Measurable (variationCube F N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : Ω) =>
    if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Measurable (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact Finset.measurable_sum _ fun i _ => ((hF _).sub (hF _)).enorm.pow_const _
    · simpa only [g, ite_eq_right hp] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ≥0∞)))
  have hs (s : Finset (Fin (N + 1) → Fin (N + 1))) :
      Measurable (fun x => s.sup (fun p => g p x)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      simpa only [Finset.sup_insert] using (hg p).max ih
  exact hs Finset.univ

/-- No extra Hilbert-valued input is assumed: coordinatewise scalar
martingales and finite Minkowski give the same squared Lépingle constant. -/
theorem lepingle_euclidean_bound (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℝ κ),
          (∀ k, Martingale (fun n x => F n x k) ℱ μ) →
          (∀ k n, MemLp (fun x => F n x k) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^
              (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C, hC, hbound⟩ := hL
  refine ⟨C, hC, ?_⟩
  intro Ω m μ hμ κ inst ℱ F hF hF2 N
  have hmeas (k : κ) (n : ℕ) : Measurable (fun x => F n x k) :=
    ((hF k).stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have hpoint (x : Ω) :
      ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^ (2 / 3 : ℝ) ≤
        ∑ k, variationCube (fun n x => F n x k) N x ^ (2 / 3 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]
    have h := ENNReal.ofReal_le_ofReal (euclidean_finiteCubicVariation_le (fun n => F n x) N)
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg
      (finiteCubicVariation_nonneg _ _) _)] at h
    refine h.trans_eq (Finset.sum_congr rfl fun k _ => ?_)
    rw [← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _)
      (by norm_num : (0 : ℝ) ≤ 2 / 3)]
    rw [scalar_finiteCubicVariation (fun n x => F n x k) N x]
  calc
    _ ≤ ∫⁻ x, ∑ k, variationCube (fun n x => F n x k) N x ^ (2 / 3 : ℝ) ∂μ :=
      lintegral_mono hpoint
    _ = ∑ k, ∫⁻ x, variationCube (fun n x => F n x k) N x ^ (2 / 3 : ℝ) ∂μ := by
      apply lintegral_finsetSum
      intro k _
      exact (measurable_variationCube _ (hmeas k) N).pow_const _
    _ ≤ ∑ k, (C : ℝ≥0∞) ^ 2 * squareIntegral μ (fun x => F N x k) :=
      Finset.sum_le_sum fun k _ => hbound Ω m μ hμ ℱ _ (hF k) (hF2 k) N
    _ = (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
      rw [← Finset.mul_sum]
      congr 1
      unfold squareIntegral
      rw [← lintegral_finsetSum]
      · apply lintegral_congr
        intro x
        rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          EuclideanSpace.norm_sq_eq, ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
        simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      · intro k _
        exact (hmeas k N).enorm.pow_const _

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComplexVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realification preserves the cubic variation and the terminal L² norm
of the complex Hilbert-valued packet sums. -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace LipschitzHilbert

theorem complexRealify_sub {κ : Type*} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    complexRealify (v - w) = complexRealify v - complexRealify w := by
  ext ⟨k,j⟩
  fin_cases j <;> simp [complexRealify]

theorem norm_complexRealify {κ : Type*} [Fintype κ] (v : EuclideanSpace ℂ κ) :
    ‖complexRealify v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  simpa [complexRealify, Fin.sum_univ_two, Complex.normSq_apply, pow_two] using
    Complex.normSq_eq_norm_sq (v k)

theorem finiteCubicVariation_complexRealify {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ) :
    finiteCubicVariation (fun n => complexRealify (F n)) N = finiteCubicVariation F N := by
  have hnorm (i j : ℕ) : ‖complexRealify (F i) - complexRealify (F j)‖ = ‖F i - F j‖ := by
    rw [← complexRealify_sub, norm_complexRealify]
  unfold finiteCubicVariation
  simp_rw [hnorm]

/-- Apply the scalar published input to real and imaginary coordinates.
Realification preserves both norms exactly, so there is no dimension loss. -/
theorem lepingle_complex_bound (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℂ κ),
          (∀ k, Martingale (fun n x => (F n x k).re) ℱ μ) →
          (∀ k, Martingale (fun n x => (F n x k).im) ℱ μ) →
          (∀ k n, MemLp (fun x => (F n x k).re) 2 μ) →
          (∀ k n, MemLp (fun x => (F n x k).im) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^
              (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C,hC,hbound⟩ := lepingle_euclidean_bound hL
  refine ⟨C,hC,?_⟩
  intro Ω m μ hμ κ inst ℱ F hFre hFim hF2re hF2im N
  let H := fun n x => complexRealify (F n x)
  have hH (i : κ × Fin 2) : Martingale (fun n x => H n x i) ℱ μ := by
    rcases i with ⟨k,j⟩
    fin_cases j
    · simpa [H, complexRealify] using hFre k
    · simpa [H, complexRealify] using hFim k
  have hH2 (i : κ × Fin 2) (n : ℕ) : MemLp (fun x => H n x i) 2 μ := by
    rcases i with ⟨k,j⟩
    fin_cases j
    · simpa [H, complexRealify] using hF2re k n
    · simpa [H, complexRealify] using hF2im k n
  have h := hbound Ω m μ hμ (κ × Fin 2) ℱ H hH hH2 N
  simpa only [H, finiteCubicVariation_complexRealify, ← ofReal_norm, norm_complexRealify] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FiniteMeasureLepingle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a finite line cell, apply the published probability-space
inequality, then restore its unnormalized measure without loss. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

theorem martingale_smul_measure {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ m}
    {F : ℕ → Ω → ℝ} (hF : Martingale F ℱ μ) (c : ℝ≥0∞) (hc : c ≠ ∞) :
    Martingale F ℱ (c • μ) := by
  have : IsFiniteMeasure (c • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top _ _)⟩
  apply martingale_of_setIntegral_eq_succ hF.stronglyAdapted
    (fun n => (hF.integrable n).smul_measure hc)
  intro n s hs
  simp only [Measure.restrict_smul, integral_smul_measure]
  rw [hF.setIntegral_eq (Nat.le_succ n) hs]

/-- The scalar probability-space theorem gives the same constant on
every finite measure. This is the normalization used on coarsest line cells. -/
theorem lepingle_complex_finite_measure (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsFiniteMeasure μ → ∀ (κ : Type) [Fintype κ]
          (ℱ : Filtration ℕ m) (F : ℕ → Ω → EuclideanSpace ℂ κ),
          (∀ k, Martingale (fun n x => (F n x k).re) ℱ μ) →
          (∀ k, Martingale (fun n x => (F n x k).im) ℱ μ) →
          (∀ k n, MemLp (fun x => (F n x k).re) 2 μ) →
          (∀ k n, MemLp (fun x => (F n x k).im) 2 μ) → ∀ N : ℕ,
            (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F N x‖ₑ ^ 2 ∂μ := by
  obtain ⟨C,hC,hbound⟩ := lepingle_complex_bound hL
  refine ⟨C,hC,?_⟩
  intro Ω m μ hμ κ inst ℱ F hRe hIm hRe2 hIm2 N
  let : IsFiniteMeasure μ := hμ
  by_cases hzero : μ = 0
  · simp [hzero]
  have hmass : μ Set.univ ≠ 0 := fun hz => hzero (Measure.measure_univ_eq_zero.mp hz)
  have htop : μ Set.univ ≠ ∞ := (measure_lt_top μ Set.univ).ne
  let c := (μ Set.univ)⁻¹
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.mpr htop
  have hctop : c ≠ ∞ := ENNReal.inv_ne_top.mpr hmass
  have hprob : IsProbabilityMeasure (c • μ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass htop⟩
  have h := hbound Ω m (c • μ) hprob κ ℱ F
    (fun k => martingale_smul_measure (hRe k) c hctop)
    (fun k => martingale_smul_measure (hIm k) c hctop)
    (fun k n => (hRe2 k n).smul_measure hctop)
    (fun k n => (hIm2 k n).smul_measure hctop) N
  simp only [lintegral_smul_measure, smul_eq_mul] at h
  rw [← mul_assoc, mul_comm ((C : ℝ≥0∞) ^ 2) c, mul_assoc] at h
  have hcancel := mul_le_mul_right h c⁻¹
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul] using hcancel

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationMeasurable
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable common exceptional set for all selected scale intervals. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem measurable_finiteCubicVariation {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (F : ℕ → Ω → E) (hF : ∀ n, Measurable (F n)) (N : ℕ) :
    Measurable (fun x => finiteCubicVariation (fun n => F n x) N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : Ω) =>
    if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Measurable (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact Finset.measurable_sum _ fun i _ => ((hF _).sub (hF _)).norm.pow_const _
    · simpa only [g, ite_eq_right hp] using
        (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  have hs := Finset.measurable_sup' Finset.univ_nonempty (fun p _ => hg p)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [finiteCubicVariation, g, Finset.sup'_apply]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PerturbedLepingle
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Lépingle plus the actual square-summable smooth/dyadic error. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

theorem lintegral_finiteCubicVariation_comparison {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) (P M : ℕ → Ω → E)
    (hP : ∀ n, Measurable (P n)) (hM : ∀ n, Measurable (M n)) (N : ℕ) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => P n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
      2 * (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => M n x) N) ^ (2 / 3 : ℝ) ∂μ) +
        8 * ∑ k : Fin (N + 1), ∫⁻ x, ‖P k x - M k x‖ₑ ^ 2 ∂μ := by
  have hpoint (x : Ω) :
      ENNReal.ofReal (finiteCubicVariation (fun n => P n x) N) ^ (2 / 3 : ℝ) ≤
        2 * ENNReal.ofReal (finiteCubicVariation (fun n => M n x) N) ^ (2 / 3 : ℝ) +
          8 * ∑ k : Fin (N + 1), ‖P k x - M k x‖ₑ ^ 2 := by
    have h := ENNReal.ofReal_le_ofReal
      (finiteCubicVariation_comparison (fun n => P n x) (fun n => M n x) N)
    rw [ENNReal.ofReal_add (mul_nonneg (by norm_num)
      (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _)) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
      ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)] at h
    simpa only [← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _)
      (by norm_num : (0 : ℝ) ≤ 2 / 3), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] using h
  calc
    _ ≤ ∫⁻ x, 2 * ENNReal.ofReal (finiteCubicVariation (fun n => M n x) N) ^ (2 / 3 : ℝ) +
        8 * ∑ k : Fin (N + 1), ‖P k x - M k x‖ₑ ^ 2 ∂μ := lintegral_mono hpoint
    _ = _ := by
      rw [lintegral_add_left]
      · rw [lintegral_const_mul, lintegral_const_mul, lintegral_finsetSum]
        · intro k _
          exact ((hP _).sub (hM _)).enorm.pow_const _
        · exact Finset.measurable_sum _ fun k _ => ((hP _).sub (hM _)).enorm.pow_const _
        · exact (measurable_finiteCubicVariation M hM N).ennreal_ofReal.pow_const _
      · exact measurable_const.mul
          ((measurable_finiteCubicVariation M hM N).ennreal_ofReal.pow_const _)

theorem measurable_complex_martingale {Ω κ : Type*} [m : MeasurableSpace Ω] [Fintype κ]
    {μ : Measure Ω} {ℱ : Filtration ℕ m} {M : ℕ → Ω → EuclideanSpace ℂ κ}
    (hRe : ∀ k, Martingale (fun n x => (M n x k).re) ℱ μ)
    (hIm : ∀ k, Martingale (fun n x => (M n x k).im) ℱ μ) (n : ℕ) :
    Measurable (M n) := by
  have hre (k : κ) : Measurable (fun x => (M n x k).re) :=
    ((hRe k).stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have him (k : κ) : Measurable (fun x => (M n x k).im) :=
    ((hIm k).stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl
  have hc (k : κ) : Measurable (fun x => M n x k) := by
    have h := (Complex.continuous_ofReal.measurable.comp (hre k)).add
      ((Complex.continuous_ofReal.measurable.comp (him k)).mul_const Complex.I)
    change Measurable (fun x => ((M n x k).re : ℂ) + (M n x k).im * Complex.I) at h
    simpa only [Complex.re_add_im] using h
  exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr hc)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FiniteLineGrid
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite line partitions, nested at an integer branching ratio. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

namespace FiniteLineGrid

attribute [local instance] Classical.propDecidable

/-- Two points of one finer cell differ by at most its mesh width. -/
theorem same_index_distance (g : FiniteLineGrid) {level : ℕ} (hlevel : level ≤ g.depth)
    {x y : ℝ} (hx : x ∈ g.root) (hy : y ∈ g.root)
    (hxy : g.index level x = g.index level y) :
    |x - y| ≤ g.width / (g.branching : ℝ) ^ level := by
  have hG : 0 < (g.branching : ℝ) := by exact_mod_cast g.branching_pos
  have hp : 0 < (g.branching : ℝ) ^ level := pow_pos hG _
  have hxn : 0 ≤ ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hx.1) g.width_pos.le) hp.le
  have hyn : 0 ≤ ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hy.1) g.width_pos.le) hp.le
  have hf : ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ =
      ⌊((y - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ := by
    have h := congrArg Fin.val hxy
    simpa only [index, Nat.min_eq_left hlevel, rawIndex, ite_eq_left hx, ite_eq_left hy] using h
  have hxlo := Nat.floor_le hxn
  have hylo := Nat.floor_le hyn
  have hxhi := Nat.lt_floor_add_one (((x - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  have hyhi := Nat.lt_floor_add_one (((y - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  rw [hf] at hxlo hxhi
  have hnorm : |((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have heq : ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level =
      (x - y) * ((g.branching : ℝ) ^ level / g.width) := by ring
  rw [heq, abs_mul, abs_of_pos (div_pos hp g.width_pos)] at hnorm
  apply (le_div_iff₀ hp).mpr
  have h := mul_le_mul_of_nonneg_right hnorm g.width_pos.le
  calc
    |x - y| * (g.branching : ℝ) ^ level =
        (|x - y| * ((g.branching : ℝ) ^ level / g.width)) * g.width := by
          field_simp [g.width_pos.ne']
    _ ≤ 1 * g.width := h
    _ = g.width := one_mul _

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteLineCells
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact intervals underlying the finite line-mesh index maps. -/

noncomputable section

open Set

namespace LipschitzHilbert.FiniteLineGrid

theorem index_eq_iff_mem_cell (g : FiniteLineGrid) {level : ℕ}
    (hl : level ≤ g.depth) {x : ℝ} (hx : x ∈ g.root) (i : ℕ) :
    (g.index level x).val = i ↔ x ∈ g.cell level i := by
  have hG : (0 : ℝ) < g.branching := by exact_mod_cast g.branching_pos
  have hrep : (x - g.origin) / g.width * (g.branching : ℝ) ^ level =
      (x - g.origin) / g.meshWidth level := by
    unfold meshWidth
    field_simp
  have hn : 0 ≤ (x - g.origin) / g.meshWidth level :=
    div_nonneg (sub_nonneg.mpr hx.1) (g.meshWidth_pos level).le
  simp only [index, rawIndex, Nat.min_eq_left hl, ite_eq_left hx, hrep]
  rw [Nat.floor_eq_iff hn]
  change (i : ℝ) ≤ (x - g.origin) / g.meshWidth level ∧
      (x - g.origin) / g.meshWidth level < i + 1 ↔
    g.origin + g.meshWidth level * i ≤ x ∧ x < g.origin + g.meshWidth level * (i + 1)
  rw [le_div_iff₀ (g.meshWidth_pos level), div_lt_iff₀ (g.meshWidth_pos level)]
  constructor <;> rintro ⟨hleft, hright⟩ <;> constructor <;> nlinarith

theorem cell_subset_root (g : FiniteLineGrid) (level : ℕ) {i : ℕ}
    (hi : i < g.branching ^ level) : g.cell level i ⊆ g.root := by
  have hwidth := g.meshWidth_pos level
  have hG : (0 : ℝ) < g.branching := by exact_mod_cast g.branching_pos
  have hupper : (i : ℝ) + 1 ≤ (g.branching : ℝ) ^ level := by
    exact_mod_cast (show i + 1 ≤ g.branching ^ level by omega)
  have hmul := mul_le_mul_of_nonneg_left hupper hwidth.le
  have hrestore : g.meshWidth level * (g.branching : ℝ) ^ level = g.width := by
    exact div_mul_cancel₀ _ (pow_pos hG _).ne'
  rw [hrestore] at hmul
  intro x hx
  change g.origin + g.meshWidth level * i ≤ x ∧
    x < g.origin + g.meshWidth level * (i + 1) at hx
  change g.origin ≤ x ∧ x < g.origin + g.width
  have hzero : 0 ≤ g.meshWidth level * i := mul_nonneg hwidth.le (Nat.cast_nonneg _)
  constructor <;> linarith [hx.1, hx.2]

/-- Restricting the coarse-index fiber to the root gives exactly its
half-open mesh interval. -/
theorem index_fiber_inter_root (g : FiniteLineGrid) {level : ℕ}
    (hl : level ≤ g.depth) {i : ℕ} (hi : i < g.branching ^ level) :
    {x ∈ g.root | (g.index level x).val = i} = g.cell level i := by
  ext x
  constructor
  · intro hx
    exact (g.index_eq_iff_mem_cell hl hx.1 i).mp hx.2
  · intro hx
    have hr := g.cell_subset_root level hi hx
    exact ⟨hr, (g.index_eq_iff_mem_cell hl hr i).mpr hx⟩

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridMartingale
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The martingale of actual nested line-cell averages. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem average_martingale (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) : Martingale (g.average μ f) g.filtration μ :=
  martingale_condExp f g.filtration μ

theorem average_memLp (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 μ) (n : ℕ) : MemLp (g.average μ f n) 2 μ :=
  hf.condExp (by norm_num)

theorem average_constant (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℝ)
    (n : ℕ) {x y : ℝ} (hxy : g.index n x = g.index n y) :
    g.average μ f n x = g.average μ f n y := by
  exact (show StronglyMeasurable[g.filtration n] (g.average μ f n) from
    stronglyMeasurable_condExp).factorsThrough hxy

/-- Conditional expectation is the actual integral average on every
positive-measure index fiber, pointwise for its canonical representative. -/
theorem average_eq_fiber_mean (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (n : ℕ) (x : ℝ)
    (hpos : μ.real {y | g.index n y = g.index n x} ≠ 0) :
    g.average μ f n x =
      (∫ y in {y | g.index n y = g.index n x}, f y ∂μ) /
        μ.real {y | g.index n y = g.index n x} := by
  let s := {y | g.index n y = g.index n x}
  have hs : MeasurableSet[g.filtration n] s :=
    (comap_measurable (g.index n)) (measurableSet_singleton _)
  have hsambient : MeasurableSet s := (g.filtration.le n) _ hs
  apply (eq_div_iff hpos).mpr
  calc
    g.average μ f n x * μ.real s = ∫ y in s, g.average μ f n x ∂μ := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ = ∫ y in s, g.average μ f n y ∂μ := by
      apply setIntegral_congr_fun hsambient
      intro y hy
      exact g.average_constant μ f n hy.symm
    _ = ∫ y in s, f y ∂μ := setIntegral_condExp (g.filtration.le n) hf hs

theorem lineMeasure_fiber (g : FiniteLineGrid) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    g.lineMeasure {x | (g.index level x).val = i} = ENNReal.ofReal (g.meshWidth level) := by
  rw [lineMeasure, Measure.restrict_apply]
  · have heq : {x | (g.index level x).val = i} ∩ g.root = g.cell level i := by
      rw [inter_comm]
      exact g.index_fiber_inter_root hl hi
    rw [heq, cell, Real.volume_Ico]
    congr 1
    ring
  · exact ((measurable_of_countable (fun j : Fin (g.branching ^ g.depth) => j.val)).comp
      (g.measurable_index level)) (measurableSet_singleton i)

/-- On a nonempty mesh interval, the canonical dyadic conditional
expectation is exactly the usual Lebesgue average over that interval. -/
theorem average_eq_cell_mean (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure f level x =
      (∫ y in g.cell level i, f y) / g.meshWidth level := by
  have hix : (g.index level x).val = i :=
    (g.index_eq_iff_mem_cell hl (g.cell_subset_root level hi hx) i).mpr hx
  have hfiber : {y | g.index level y = g.index level x} =
      {y | (g.index level y).val = i} := by
    ext y
    simp only [Fin.ext_iff, hix, Set.mem_ofPred_eq]
  have hmass : g.lineMeasure.real {y | g.index level y = g.index level x} =
      g.meshWidth level := by
    rw [measureReal_def, hfiber, g.lineMeasure_fiber hl hi,
      ENNReal.toReal_ofReal (g.meshWidth_pos level).le]
  rw [g.average_eq_fiber_mean g.lineMeasure f hf level x
    (by rw [hmass]; exact (g.meshWidth_pos level).ne'), hmass]
  congr 1
  rw [lineMeasure, Measure.restrict_restrict (g.measurable_index_fiber level _)]
  congr 1
  rw [hfiber, inter_comm]
  congr 1
  exact g.index_fiber_inter_root hl hi

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ComplexLineAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex Hilbert-valued averages on the actual finite line grid. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

theorem lintegral_square_condExp_le {Ω : Type*} [m : MeasurableSpace Ω]
    (μ : Measure Ω) (m' : MeasurableSpace Ω) (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    (∫⁻ x, ‖μ[f | m'] x‖ₑ ^ 2 ∂μ) ≤ ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have h := ENNReal.rpow_le_rpow
    (eLpNorm_condExp_le_eLpNorm (m := m') (m0 := m) (μ := μ) f
      (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    (by norm_num : (0 : ℝ) ≤ 2)
  have hleft := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (f := μ[f | m']) (μ := μ)
  have hright := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
    (f := f) (μ := μ)
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at h hleft hright
  rwa [hleft, hright] at h

theorem enorm_complex_sq (z : ℂ) : ‖z‖ₑ ^ 2 = ‖z.re‖ₑ ^ 2 + ‖z.im‖ₑ ^ 2 := by
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  congr 1
  have h : ‖z‖ * ‖z‖ = z.re * z.re + z.im * z.im := by
    simpa only [pow_two, Complex.normSq_apply] using (Complex.normSq_eq_norm_sq z).symm
  simp only [Real.norm_eq_abs, pow_two]
  nlinarith only [h, sq_abs z.re, sq_abs z.im]

theorem lintegral_complex_euclidean_sq {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (μ : Measure Ω) (F : Ω → EuclideanSpace ℂ κ) (hF : Measurable F) :
    (∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ) = ∑ k,
      ((∫⁻ x, ‖(F x k).re‖ₑ ^ 2 ∂μ) + (∫⁻ x, ‖(F x k).im‖ₑ ^ 2 ∂μ)) := by
  have hpoint (x : Ω) : ‖F x‖ₑ ^ 2 = ∑ k, (‖(F x k).re‖ₑ ^ 2 + ‖(F x k).im‖ₑ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _)]
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, enorm_complex_sq]
  simp_rw [hpoint]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [lintegral_add_left]
    exact ((Complex.continuous_re.comp ((PiLp.continuous_apply 2 _ k))).measurable.comp hF).enorm.pow_const _
  · intro k _
    exact (((Complex.continuous_re.comp (PiLp.continuous_apply 2 _ k)).measurable.comp hF).enorm.pow_const _).add
      (((Complex.continuous_im.comp (PiLp.continuous_apply 2 _ k)).measurable.comp hF).enorm.pow_const _)

namespace FiniteLineGrid

theorem complexAverage_re {κ : Type*} [Fintype κ] (g : FiniteLineGrid) (μ : Measure ℝ)
    (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) (x : ℝ) (k : κ) :
    (g.complexAverage μ F n x k).re = g.average μ (fun y => (F y k).re) n x := by
  simp [complexAverage]

theorem complexAverage_im {κ : Type*} [Fintype κ] (g : FiniteLineGrid) (μ : Measure ℝ)
    (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) (x : ℝ) (k : κ) :
    (g.complexAverage μ F n x k).im = g.average μ (fun y => (F y k).im) n x := by
  simp [complexAverage]

theorem complexAverage_measurable {κ : Type*} [Fintype κ] (g : FiniteLineGrid)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (F : ℝ → EuclideanSpace ℂ κ) (n : ℕ) :
    Measurable (g.complexAverage μ F n) := by
  apply measurable_complex_martingale
  · intro k
    simpa only [complexAverage_re] using g.average_martingale μ (fun y => (F y k).re)
  · intro k
    simpa only [complexAverage_im] using g.average_martingale μ (fun y => (F y k).im)

theorem complexAverage_energy {κ : Type*} [Fintype κ] (g : FiniteLineGrid)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (F : ℝ → EuclideanSpace ℂ κ) (hF : Measurable F)
    (hRe : ∀ k, MemLp (fun y => (F y k).re) 2 μ)
    (hIm : ∀ k, MemLp (fun y => (F y k).im) 2 μ) (n : ℕ) :
    (∫⁻ x, ‖g.complexAverage μ F n x‖ₑ ^ 2 ∂μ) ≤ ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ := by
  rw [lintegral_complex_euclidean_sq μ _ (g.complexAverage_measurable μ F n),
    lintegral_complex_euclidean_sq μ F hF]
  apply Finset.sum_le_sum
  intro k _
  simp only [complexAverage_re, complexAverage_im, average]
  exact add_le_add (lintegral_square_condExp_le μ _ _ (hRe k))
    (lintegral_square_condExp_le μ _ _ (hIm k))

end FiniteLineGrid

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SeparatedSampling
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sampling estimate needed for a band primitive: use disjoint
intervals at the band scale, independently of the larger mesh spacing. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem sample_interval_energy (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    (a : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    δ * A a ^ 2 ≤ 2 * (∫ x in Ico a (a + δ), A x ^ 2) +
      2 * δ ^ 2 * ∫ x in Ico a (a + δ), deriv A x ^ 2 := by
  have hab : a < a + δ := lt_add_of_pos_right a hδ
  let energy := ∫ x in Icc a (a + δ), deriv A x ^ 2
  have hpoint : ∀ᵐ y ∂volume.restrict (Icc a (a + δ)),
      A a ^ 2 ≤ 2 * A y ^ 2 + 2 * δ * energy := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hp := interval_pair_energy A hab.le (fun x _ => hA x)
      (hd2.restrict _) (show a ∈ Icc a (a + δ) from ⟨le_rfl, hab.le⟩) hy
    simp only [Real.norm_eq_abs, sq_abs, add_sub_cancel_left] at hp
    nlinarith [sq_nonneg (A a - 2 * A y)]
  have h := integral_mono_ae (integrable_const (A a ^ 2))
    (((hA2.restrict (Icc a (a + δ))).integrable_sq.const_mul 2).add
      (integrable_const (2 * δ * energy))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add ((hA2.restrict (Icc a (a + δ))).integrable_sq.const_mul 2)
      (integrable_const _), integral_const_mul, integral_const, integral_const] at h
  have hmass : (volume.restrict (Icc a (a + δ))).real univ = δ := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, add_sub_cancel_left,
      ENNReal.toReal_ofReal hδ.le]
  simp only [smul_eq_mul, hmass, energy, integral_Icc_eq_integral_Ico] at h
  nlinarith only [h]

theorem separated_sample_sum (A : ℝ → ℝ) (hA : Differentiable ℝ A)
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    (N : ℕ) (sample : Fin N → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hseparated : ∀ i j, i < j → sample i + δ ≤ sample j) :
    (∑ i, A (sample i) ^ 2) ≤
      (2 / δ) * (∫ x, A x ^ 2) + 2 * δ * ∫ x, deriv A x ^ 2 := by
  let cell := fun i => Ico (sample i) (sample i + δ)
  have hdisj : Pairwise (fun i j => Disjoint (cell i) (cell j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · exact (not_lt_of_ge (hseparated i j h)) (hxj.1.trans_lt hxi.2)
    · exact (not_lt_of_ge (hseparated j i h)) (hxi.1.trans_lt hxj.2)
  have hsumA : (∑ i, ∫ x in cell i, A x ^ 2) ≤ ∫ x, A x ^ 2 := by
    rw [← integral_iUnion_fintype (fun _ => measurableSet_Ico) hdisj
      (fun _ => hA2.integrable_sq.integrableOn)]
    exact setIntegral_le_integral hA2.integrable_sq (by filter_upwards with x; exact sq_nonneg _)
  have hsumd : (∑ i, ∫ x in cell i, deriv A x ^ 2) ≤ ∫ x, deriv A x ^ 2 := by
    rw [← integral_iUnion_fintype (fun _ => measurableSet_Ico) hdisj
      (fun _ => hd2.integrable_sq.integrableOn)]
    exact setIntegral_le_integral hd2.integrable_sq (by filter_upwards with x; exact sq_nonneg _)
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => sample_interval_energy A hA hA2 hd2 (sample i) hδ)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at h
  have htotal : δ * (∑ i, A (sample i) ^ 2) ≤
      2 * (∫ x, A x ^ 2) + 2 * δ ^ 2 * ∫ x, deriv A x ^ 2 := by
    dsimp only [cell] at hsumA hsumd
    nlinarith [mul_le_mul_of_nonneg_left hsumd (sq_nonneg δ)]
  calc
    _ ≤ (2 * (∫ x, A x ^ 2) + 2 * δ ^ 2 * ∫ x, deriv A x ^ 2) / δ :=
      (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using htotal)
    _ = _ := by field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridPoincare
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-frequency averaging errors on the actual nested line grid. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem index_lt_level (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) (x : ℝ) :
    (g.index level x).val < g.branching ^ level := by
  let h : FiniteLineGrid := { g with depth := level }
  have ht := h.rawIndex_lt (le_refl level) x
  change g.rawIndex level x < g.branching ^ level at ht
  simpa only [index, Nat.min_eq_left hl] using ht

theorem cells_cover_root (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) :
    (⋃ i : Fin (g.branching ^ level), g.cell level i.val) = g.root := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact g.cell_subset_root level i.isLt hi
  · intro hx
    let i : Fin (g.branching ^ level) := ⟨(g.index level x).val, g.index_lt_level hl x⟩
    exact mem_iUnion.mpr ⟨i, (g.index_eq_iff_mem_cell hl hx i.val).mp rfl⟩

theorem cells_disjoint (g : FiniteLineGrid) {level : ℕ} (hl : level ≤ g.depth) :
    Pairwise (fun i j : Fin (g.branching ^ level) => Disjoint (g.cell level i.val) (g.cell level j.val)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hri := g.cell_subset_root level i.isLt hxi
  have hix := (g.index_eq_iff_mem_cell hl hri i.val).mpr hxi
  have hjx := (g.index_eq_iff_mem_cell hl hri j.val).mpr hxj
  exact hij (Fin.ext (hix.symm.trans hjx))

theorem cell_poincare (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) (hdf : Differentiable ℝ f)
    (hd : MemLp (deriv f) 2 volume) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    (∫ x in g.cell level i, |f x - g.average g.lineMeasure f level x| ^ 2) ≤
      g.meshWidth level ^ 2 * ∫ x in g.cell level i, |deriv f x| ^ 2 := by
  let a := g.origin + g.meshWidth level * i
  let b := g.origin + g.meshWidth level * (i + 1)
  have hlength : b - a = g.meshWidth level := by dsimp [a,b]; ring
  have hab : a < b := sub_pos.mp (hlength ▸ g.meshWidth_pos level)
  have h := interval_poincare_Ico f hab (fun x _ => hdf x) (hd.restrict (Icc a b))
  rw [hlength] at h
  calc
    _ = ∫ x in Ico a b, |f x - (g.meshWidth level)⁻¹ * ∫ y in Ico a b, f y| ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      dsimp only
      rw [g.average_eq_cell_mean f hf hl hi hx, div_eq_mul_inv, mul_comm]
      rfl
    _ ≤ _ := by simpa only [Real.norm_eq_abs, smul_eq_mul, cell, a, b] using h

/-- Summing the actual disjoint cells gives the low-frequency part of
the smooth/dyadic comparison, with no loss from their number. -/
theorem poincare (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : MemLp f 2 g.lineMeasure) (hdf : Differentiable ℝ f)
    (hd : MemLp (deriv f) 2 volume) {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, |f x - g.average g.lineMeasure f level x| ^ 2 ∂g.lineMeasure) ≤
      g.meshWidth level ^ 2 * ∫ x in g.root, |deriv f x| ^ 2 := by
  have herr : Integrable (fun x => |f x - g.average g.lineMeasure f level x| ^ 2)
      g.lineMeasure := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (hf.sub (g.average_memLp g.lineMeasure f hf level)).integrable_norm_pow (by decide : 2 ≠ 0)
  have hder : Integrable (fun x => |deriv f x| ^ 2) volume := by
    simpa only [Real.norm_eq_abs] using hd.integrable_norm_pow (by decide : 2 ≠ 0)
  have hc (i : Fin (g.branching ^ level)) :
      IntegrableOn (fun x => |f x - g.average g.lineMeasure f level x| ^ 2)
        (g.cell level i.val) volume :=
    herr.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root level i.isLt))
  change (∫ x in g.root, |f x - g.average g.lineMeasure f level x| ^ 2) ≤ _
  have hpartf := integral_iUnion_fintype
    (s := fun i : Fin (g.branching ^ level) => g.cell level i.val)
    (fun _ => measurableSet_Ico) (g.cells_disjoint hl) hc
  have hpartd := integral_iUnion_fintype
    (s := fun i : Fin (g.branching ^ level) => g.cell level i.val)
    (fun _ => measurableSet_Ico) (g.cells_disjoint hl) (fun _ => hder.integrableOn)
  rw [g.cells_cover_root hl] at hpartf hpartd
  rw [hpartf]
  calc
    _ ≤ ∑ i : Fin (g.branching ^ level), g.meshWidth level ^ 2 *
        ∫ x in g.cell level i.val, |deriv f x| ^ 2 :=
      Finset.sum_le_sum fun i _ => g.cell_poincare f (hf.integrable (by norm_num)) hdf hd hl i.isLt
    _ = _ := by
      rw [← Finset.mul_sum, ← hpartd]

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridPrimitive
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cell averages of a derivative are boundary differences. This is the
high-frequency half of the manuscript's dyadic comparison. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem average_deriv_eq (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A)) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure (deriv A) level x =
      (A (g.origin + g.meshWidth level * (i + 1)) -
        A (g.origin + g.meshWidth level * i)) / g.meshWidth level := by
  have hint : Integrable (deriv A) g.lineMeasure :=
    (hd.continuousOn.integrableOn_Icc :
      IntegrableOn (deriv A) (Icc g.origin (g.origin + g.width)) volume).mono_set Ico_subset_Icc_self
  rw [g.average_eq_cell_mean (deriv A) hint hl hi hx]
  congr 1
  let a := g.origin + g.meshWidth level * i
  let b := g.origin + g.meshWidth level * (i + 1)
  have hab : a ≤ b := by dsimp [a,b]; nlinarith [g.meshWidth_pos level]
  change (∫ y in Ico a b, deriv A y) = A b - A a
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_deriv_eq_sub (fun y _ => hA y) (hd.intervalIntegrable a b)

theorem average_deriv_cell_energy (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A)) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    (∫ x in g.cell level i, |g.average g.lineMeasure (deriv A) level x| ^ 2) =
      (g.meshWidth level)⁻¹ *
        (A (g.origin + g.meshWidth level * (i + 1)) -
          A (g.origin + g.meshWidth level * i)) ^ 2 := by
  have heq := setIntegral_congr_fun (μ := volume) (s := g.cell level i) measurableSet_Ico
    (fun x hx => congrArg (fun t : ℝ => |t| ^ 2) (g.average_deriv_eq A hA hd hl hi hx))
  rw [heq, setIntegral_const, smul_eq_mul]
  have hmass : volume.real (g.cell level i) = g.meshWidth level := by
    rw [measureReal_def, cell, Real.volume_Ico]
    have he : g.origin + g.meshWidth level * (i + 1) -
        (g.origin + g.meshWidth level * i) = g.meshWidth level := by ring
    rw [he, ENNReal.toReal_ofReal (g.meshWidth_pos level).le]
  rw [hmass, sq_abs]
  field_simp [(g.meshWidth_pos level).ne']

/-- Each sample is charged by at most two adjacent cells, giving the
exact boundary-sampling reduction used for high-frequency bands. -/
theorem average_deriv_energy (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A))
    {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, |g.average g.lineMeasure (deriv A) level x| ^ 2 ∂g.lineMeasure) ≤
      4 * (g.meshWidth level)⁻¹ * ∑ i : Fin (g.branching ^ level + 1),
        |A (g.origin + g.meshWidth level * i.val)| ^ 2 := by
  let boundary := fun i : ℕ => A (g.origin + g.meshWidth level * i)
  have hcellint (i : Fin (g.branching ^ level)) :
      IntegrableOn (fun x => |g.average g.lineMeasure (deriv A) level x| ^ 2)
        (g.cell level i.val) volume := by
    apply (integrableOn_const (C := |(boundary (i.val + 1) - boundary i.val) /
      g.meshWidth level| ^ 2) (by simp [Real.volume_Ico])).congr_fun _ measurableSet_Ico
    intro x hx
    dsimp only
    rw [g.average_deriv_eq A hA hd hl i.isLt hx]
    simp only [boundary, Nat.cast_add, Nat.cast_one]
  have hpart := integral_iUnion_fintype
    (s := fun i : Fin (g.branching ^ level) => g.cell level i.val)
    (fun _ => measurableSet_Ico) (g.cells_disjoint hl) hcellint
  rw [g.cells_cover_root hl] at hpart
  change (∫ x in g.root, |g.average g.lineMeasure (deriv A) level x| ^ 2) ≤ _
  rw [hpart]
  simp_rw [g.average_deriv_cell_energy A hA hd hl (Fin.isLt _)]
  rw [← Finset.mul_sum]
  have hsum := monotone_partition_square_sum boundary (g.branching ^ level) id monotone_id
  simp only [id_eq, Fin.val_succ, Fin.val_castSucc, Real.norm_eq_abs] at hsum
  have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (g.meshWidth_pos level).le)
  simpa only [boundary, sq_abs, Nat.cast_add, Nat.cast_one,
    mul_left_comm (g.meshWidth level)⁻¹ 4, mul_assoc] using hmul

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HighFrequencyAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The high-frequency cell-average bound from a band-scale primitive. -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.FiniteLineGrid

theorem primitive_average_energy (g : FiniteLineGrid) (A : ℝ → ℝ)
    (hA : Differentiable ℝ A) (hd : Continuous (deriv A))
    (hA2 : MemLp A 2 volume) (hd2 : MemLp (deriv A) 2 volume)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ} (hδ : 0 < δ)
    (hδmesh : δ ≤ g.meshWidth level) :
    (∫ x, |g.average g.lineMeasure (deriv A) level x| ^ 2 ∂g.lineMeasure) ≤
      (8 / (g.meshWidth level * δ)) * (∫ x, A x ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, deriv A x ^ 2 := by
  simp only [sq_abs]
  let sample := fun i : Fin (g.branching ^ level + 1) =>
    g.origin + g.meshWidth level * i.val
  have hsep (i j : Fin (g.branching ^ level + 1)) (hij : i < j) :
      sample i + δ ≤ sample j := by
    have hn : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (show i.val + 1 ≤ j.val by omega)
    have hm := mul_le_mul_of_nonneg_left hn (g.meshWidth_pos level).le
    dsimp [sample]
    nlinarith
  have hs := separated_sample_sum A hA hA2 hd2 (g.branching ^ level + 1) sample hδ hsep
  have hav := g.average_deriv_energy A hA hd hl
  simp only [sq_abs] at hav
  calc
    _ ≤ 4 * (g.meshWidth level)⁻¹ * ∑ i, A (sample i) ^ 2 := hav
    _ ≤ 4 * (g.meshWidth level)⁻¹ *
        ((2 / δ) * (∫ x, A x ^ 2) + 2 * δ * ∫ x, deriv A x ^ 2) :=
      mul_le_mul_of_nonneg_left hs
        (mul_nonneg (by norm_num) (inv_nonneg.mpr (g.meshWidth_pos level).le))
    _ = _ := by field_simp; ring

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_SchwartzBandPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual primitive of an annular Schwartz packet. The
Fourier quotient is smooth because the packet vanishes near frequency zero. -/

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped FourierTransform Topology

namespace LipschitzHilbert

private theorem derivative_coefficient_ne_zero {ξ : ℝ} (hξ : ξ ≠ 0) :
    (2 * Real.pi * Complex.I * ξ : ℂ) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hξ)

theorem exists_schwartz_band_primitive (f : SchwartzMap ℝ ℂ) {r R : ℝ}
    (hr : 0 < r) (hlow : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0) :
    ∃ A : SchwartzMap ℝ ℂ,
      (∀ x, deriv A x = f x) ∧
      (∀ ξ, |ξ| < r → 𝓕 A ξ = 0) ∧
      (∀ ξ, R < |ξ| → 𝓕 A ξ = 0) := by
  let q := fun ξ : ℝ => (2 * Real.pi * Complex.I * ξ : ℂ)⁻¹ * 𝓕 f ξ
  have hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q := by
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ξ = 0
    · subst ξ
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hr) hr] with t ht
      dsimp only [q]
      rw [hlow t (abs_lt.mpr ht), mul_zero]
    · have hc : ContDiffAt ℝ (↑(⊤ : ℕ∞))
          (fun t : ℝ => (2 * Real.pi * Complex.I * t : ℂ)) ξ :=
        contDiffAt_const.mul Complex.ofRealCLM.contDiff.contDiffAt
      exact (hc.inv (derivative_coefficient_ne_zero hξ)).mul
        ((𝓕 f).smooth ⊤).contDiffAt
  have hcompact : HasCompactSupport q := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-R) R))
    intro ξ hξ
    have hRξ : R < |ξ| := by
      by_contra h
      exact hξ (abs_le.mp (le_of_not_gt h))
    dsimp only [q]
    rw [hhigh ξ hRξ, mul_zero]
  let Q : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hq
  let A : SchwartzMap ℝ ℂ := 𝓕⁻ Q
  have hAQ : 𝓕 A = Q := fourier_fourierInv_eq Q
  have hderiv : SchwartzMap.derivCLM ℂ ℂ A = f := by
    apply (FourierTransform.fourierEquiv ℂ (SchwartzMap ℝ ℂ)).injective
    ext ξ
    change 𝓕 (SchwartzMap.derivCLM ℂ ℂ A) ξ = 𝓕 f ξ
    rw [schwartz_fourier_deriv, hAQ]
    change (2 * Real.pi * Complex.I * ξ : ℂ) *
      ((2 * Real.pi * Complex.I * ξ : ℂ)⁻¹ * 𝓕 f ξ) = 𝓕 f ξ
    by_cases hξ : ξ = 0
    · subst ξ
      rw [hlow 0 (by simpa using hr)]
      simp
    · rw [← mul_assoc, mul_inv_cancel₀ (derivative_coefficient_ne_zero hξ), one_mul]
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x
    exact congrArg (fun F : SchwartzMap ℝ ℂ => F x) hderiv
  · intro ξ hξ
    rw [hAQ]
    change q ξ = 0
    simp only [q, hlow ξ hξ, mul_zero]
  · intro ξ hξ
    rw [hAQ]
    change q ξ = 0
    simp only [q, hhigh ξ hξ, mul_zero]

theorem schwartz_primitive_energy (A f : SchwartzMap ℝ ℂ) {r : ℝ} (hr : 0 < r)
    (hderiv : ∀ x, deriv A x = f x)
    (hband : ∀ ξ, |ξ| < r → 𝓕 A ξ = 0) :
    (∫ x, ‖A x‖ ^ 2) ≤ (2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  have h := schwartz_band_derivative_lower A hr hband
  simp only [hderiv] at h
  have hc : 0 < (2 * Real.pi * r) ^ 2 := sq_pos_of_pos (by positivity)
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    (2 * Real.pi * r) ^ 2 * (∫ x, ‖A x‖ ^ 2) ≤ ∫ x, ‖f x‖ ^ 2 := h
    _ = (2 * Real.pi * r) ^ 2 *
        ((2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2) := by
      field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ComplexBandAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar complex packet averages on the actual line grid. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem integral_complex_square (μ : Measure ℝ) (f : ℝ → ℂ)
    (hre : MemLp (fun x => (f x).re) 2 μ)
    (him : MemLp (fun x => (f x).im) 2 μ) :
    (∫ x, ‖f x‖ ^ 2 ∂μ) =
      (∫ x, (f x).re ^ 2 ∂μ) + ∫ x, (f x).im ^ 2 ∂μ := by
  have h (x : ℝ) : ‖f x‖ ^ 2 = (f x).re ^ 2 + (f x).im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using (Complex.normSq_eq_norm_sq (f x)).symm
  simp_rw [h]
  exact integral_add hre.integrable_sq him.integrable_sq

theorem schwartz_projection_deriv (f : SchwartzMap ℝ ℂ) (L : ℂ →L[ℝ] ℝ) :
    deriv (f.postcompCLM L) = fun x => L (deriv f x) := by
  funext x
  exact (L.hasFDerivAt.comp_hasDerivAt x (f.differentiable x).hasDerivAt).deriv

theorem schwartz_projection_coe (f : SchwartzMap ℝ ℂ) (L : ℂ →L[ℝ] ℝ) :
    (f.postcompCLM L : ℝ → ℝ) = fun x => L (f x) := by
  funext x
  rfl

theorem schwartz_re_memLp (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => (f x).re) 2 volume := by
  simpa only [schwartz_projection_coe, Complex.reCLM_apply] using
    (f.postcompCLM Complex.reCLM).memLp 2 volume

theorem schwartz_im_memLp (f : SchwartzMap ℝ ℂ) :
    MemLp (fun x => (f x).im) 2 volume := by
  simpa only [schwartz_projection_coe, Complex.imCLM_apply] using
    (f.postcompCLM Complex.imCLM).memLp 2 volume

namespace FiniteLineGrid

theorem schwartz_projection_average_energy (g : FiniteLineGrid)
    (A f : SchwartzMap ℝ ℂ) (hderiv : ∀ x, deriv A x = f x)
    (L : ℂ →L[ℝ] ℝ) {level : ℕ} (hl : level ≤ g.depth)
    {δ : ℝ} (hδ : 0 < δ) (hδmesh : δ ≤ g.meshWidth level) :
    (∫ x, |g.average g.lineMeasure (fun y => L (f y)) level x| ^ 2 ∂g.lineMeasure) ≤
      (8 / (g.meshWidth level * δ)) * (∫ x, L (A x) ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, L (f x) ^ 2 := by
  let B := A.postcompCLM L
  have hd : deriv B = fun x => L (f x) := by
    rw [schwartz_projection_deriv]
    simp only [hderiv]
  have hc : Continuous (deriv B) := by rw [hd]; exact L.continuous.comp f.continuous
  have hm : MemLp (deriv B) 2 volume := by
    rw [hd]
    exact (f.postcompCLM L).memLp 2
  have h := g.primitive_average_energy B B.differentiable hc (B.memLp 2) hm hl hδ hδmesh
  simpa only [hd, B, SchwartzMap.postcompCLM_apply] using h

theorem schwartz_primitive_average_energy (g : FiniteLineGrid)
    (A f : SchwartzMap ℝ ℂ) (hderiv : ∀ x, deriv A x = f x)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ}
    (hδ : 0 < δ) (hδmesh : δ ≤ g.meshWidth level) :
    (∫ x, ‖g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      (8 / (g.meshWidth level * δ)) * (∫ x, ‖A x‖ ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 := by
  have hRe := g.schwartz_projection_average_energy A f hderiv Complex.reCLM hl hδ hδmesh
  have hIm := g.schwartz_projection_average_energy A f hderiv Complex.imCLM hl hδ hδmesh
  have hre : MemLp (fun x => (f x).re) 2 g.lineMeasure :=
    (schwartz_re_memLp f).restrict g.root
  have him : MemLp (fun x => (f x).im) 2 g.lineMeasure :=
    (schwartz_im_memLp f).restrict g.root
  rw [integral_complex_square g.lineMeasure _
    (by simpa only [scalarAverage_re] using g.average_memLp g.lineMeasure _ hre level)
    (by simpa only [scalarAverage_im] using g.average_memLp g.lineMeasure _ him level)]
  simp only [scalarAverage_re, scalarAverage_im]
  rw [integral_complex_square volume A (schwartz_re_memLp A) (schwartz_im_memLp A),
    integral_complex_square volume f (schwartz_re_memLp f) (schwartz_im_memLp f)]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, sq_abs] at hRe hIm
  nlinarith only [hRe, hIm]

theorem schwartz_poincare (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, ‖f x - g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      g.meshWidth level ^ 2 * ∫ x, ‖deriv f x‖ ^ 2 := by
  let df := SchwartzMap.derivCLM ℂ ℂ f
  have hre : MemLp (fun x => (f x).re) 2 g.lineMeasure :=
    (schwartz_re_memLp f).restrict g.root
  have him : MemLp (fun x => (f x).im) 2 g.lineMeasure :=
    (schwartz_im_memLp f).restrict g.root
  have hRe := g.poincare (f.postcompCLM Complex.reCLM) hre
    (f.postcompCLM Complex.reCLM).differentiable
    (by simpa only [schwartz_projection_deriv, df, SchwartzMap.derivCLM_apply,
      Complex.reCLM_apply] using schwartz_re_memLp df) hl
  have hIm := g.poincare (f.postcompCLM Complex.imCLM) him
    (f.postcompCLM Complex.imCLM).differentiable
    (by simpa only [schwartz_projection_deriv, df, SchwartzMap.derivCLM_apply,
      Complex.imCLM_apply] using schwartz_im_memLp df) hl
  have hRe' : (∫ x in g.root, (deriv f x).re ^ 2) ≤ ∫ x, (deriv f x).re ^ 2 := by
    apply setIntegral_le_integral
    · simpa only [df, SchwartzMap.derivCLM_apply] using (schwartz_re_memLp df).integrable_sq
    · filter_upwards with x
      exact sq_nonneg _
  have hIm' : (∫ x in g.root, (deriv f x).im ^ 2) ≤ ∫ x, (deriv f x).im ^ 2 := by
    apply setIntegral_le_integral
    · simpa only [df, SchwartzMap.derivCLM_apply] using (schwartz_im_memLp df).integrable_sq
    · filter_upwards with x
      exact sq_nonneg _
  have her : MemLp (fun x => (f x - g.scalarAverage g.lineMeasure f level x).re)
      2 g.lineMeasure := by
    convert hre.sub (g.average_memLp g.lineMeasure _ hre level) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.sub_apply, Complex.sub_re, scalarAverage_re]
  have hei : MemLp (fun x => (f x - g.scalarAverage g.lineMeasure f level x).im)
      2 g.lineMeasure := by
    convert him.sub (g.average_memLp g.lineMeasure _ him level) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.sub_apply, Complex.sub_im, scalarAverage_im]
  rw [integral_complex_square g.lineMeasure _ her hei]
  have hdecomp := integral_complex_square volume df (schwartz_re_memLp df) (schwartz_im_memLp df)
  simp only [df, SchwartzMap.derivCLM_apply] at hdecomp
  rw [hdecomp]
  rw [schwartz_projection_deriv] at hRe hIm
  simp only [schwartz_projection_coe, SchwartzMap.postcompCLM_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, sq_abs] at hRe hIm
  simp only [Complex.sub_re, Complex.sub_im, scalarAverage_re, scalarAverage_im]
  exact (add_le_add hRe hIm).trans (by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_left hRe' (sq_nonneg _))
      (mul_le_mul_of_nonneg_left hIm' (sq_nonneg _)))

theorem schwartz_low_frequency_error (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hband : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0)
    {level : ℕ} (hl : level ≤ g.depth) :
    (∫ x, ‖f x - g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      (g.meshWidth level * (2 * Real.pi * R)) ^ 2 * ∫ x, ‖f x‖ ^ 2 := by
  calc
    _ ≤ g.meshWidth level ^ 2 * ∫ x, ‖deriv f x‖ ^ 2 := g.schwartz_poincare f hl
    _ ≤ g.meshWidth level ^ 2 * ((2 * Real.pi * R) ^ 2 * ∫ x, ‖f x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (schwartz_band_derivative_upper f hR hband) (sq_nonneg _)
    _ = _ := by ring

end FiniteLineGrid
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_FourGridBandErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual radix-four meshes and the geometric error bound for each band. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem four_pow_ratio {i j : ℕ} (h : j ≤ i) :
    ((4 : ℝ) ^ i)⁻¹ * (4 : ℝ) ^ j = (1 / 4 : ℝ) ^ (i - j) := by
  have heq : i = j + (i - j) := by omega
  rw [heq, pow_add]
  simp only [Nat.add_sub_cancel_left, one_div, inv_pow]
  field_simp

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_BandAverageComparison
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual annular packet errors without a scale-count loss. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

namespace FiniteLineGrid

theorem scalarAverage_memLp (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 μ) (i : ℕ) : MemLp (g.scalarAverage μ f i) 2 μ := by
  apply memLp_re_im_iff.mp
  constructor
  · convert g.average_memLp μ (fun x => (f x).re) hf.re i using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact scalarAverage_re g μ f i x
  · convert g.average_memLp μ (fun x => (f x).im) hf.im i using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact scalarAverage_im g μ f i x

theorem scalarAverage_fullBandSum {N : ℕ} (g : FiniteLineGrid)
    (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    g.scalarAverage g.lineMeasure (fullBandSum f) i =ᵐ[g.lineMeasure]
      fun x => ∑ j, g.scalarAverage g.lineMeasure (f j) i x := by
  have hr : (fun x => (fullBandSum f x).re) = ∑ j, (fun x => (f j x).re) := by
    funext x
    simp only [fullBandSum, Complex.re_sum, Finset.sum_apply]
  have hi : (fun x => (fullBandSum f x).im) = ∑ j, (fun x => (f j x).im) := by
    funext x
    simp only [fullBandSum, Complex.im_sum, Finset.sum_apply]
  have hR := condExp_finsetSum (μ := g.lineMeasure) (s := Finset.univ)
    (fun j _ => (show MemLp (fun x => (f j x).re) 2 g.lineMeasure from
      (schwartz_re_memLp (f j)).restrict g.root).integrable (by norm_num))
    (g.filtration i)
  have hI := condExp_finsetSum (μ := g.lineMeasure) (s := Finset.univ)
    (fun j _ => (show MemLp (fun x => (f j x).im) 2 g.lineMeasure from
      (schwartz_im_memLp (f j)).restrict g.root).integrable (by norm_num))
    (g.filtration i)
  filter_upwards [hR,hI] with x hxR hxI
  apply Complex.ext
  · simp only [Complex.re_sum, scalarAverage_re, average, hr]
    simpa only [Finset.sum_apply] using hxR
  · simp only [Complex.im_sum, scalarAverage_im, average, hi]
    simpa only [Finset.sum_apply] using hxI

end FiniteLineGrid

theorem bandErrorAt_memLp (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ) (level i j : ℕ) :
    MemLp (bandErrorAt g f level i j) 2 g.lineMeasure := by
  have hf : MemLp (f : ℝ → ℂ) 2 g.lineMeasure := (f.memLp 2 volume).restrict g.root
  have hav := g.scalarAverage_memLp g.lineMeasure f hf level
  by_cases hji : j < i
  · convert hf.sub hav using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [bandErrorAt, ite_eq_left hji, Pi.sub_apply]
  · convert hav.neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [bandErrorAt, ite_eq_right hji, zero_sub, Pi.neg_apply]

theorem bandErrorAt_sum {N : ℕ} (g : FiniteLineGrid)
    (f : Fin N → SchwartzMap ℝ ℂ) (level i : ℕ) :
    (fun x => ∑ j, bandErrorAt g (f j) level i j.val x) =ᵐ[g.lineMeasure]
      fun x => partialBandSum f i x - g.scalarAverage g.lineMeasure (fullBandSum f) level x := by
  filter_upwards [g.scalarAverage_fullBandSum f level] with x hx
  simp only [bandErrorAt, Finset.sum_sub_distrib, partialBandSum, hx]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ParityPartialSums
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact even/odd decomposition of the dyadic partial sums. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem sum_range_parity {E : Type*} [AddCommGroup E] (u : ℕ → E) (n : ℕ) :
    (∑ j ∈ Finset.range n, u j) =
      (∑ j ∈ Finset.range ((n + 1) / 2), u (2 * j)) +
        ∑ j ∈ Finset.range (n / 2), u (2 * j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmod := Nat.mod_lt n (by omega : 0 < 2)
    by_cases hn : n % 2 = 0
    · have h1 : (n + 1) / 2 = n / 2 := by omega
      have h2 : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
      have h3 : 2 * (n / 2) = n := by omega
      simp only [h1, h2, Finset.sum_range_succ, h3] at ih ⊢
      rw [ih]
      abel
    · have h1 : (n + 1) / 2 = n / 2 + 1 := by omega
      have h2 : (n + 1 + 1) / 2 = n / 2 + 1 := by omega
      have h3 : 2 * (n / 2) + 1 = n := by omega
      simp only [h1, h2, Finset.sum_range_succ, h3] at ih ⊢
      rw [ih]
      abel

theorem partialBandSum_eq_sum_range {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {i : ℕ} (hi : i ≤ N) (x : ℝ) :
    partialBandSum f i x = ∑ j ∈ Finset.range i, paddedPacket f j x := by
  classical
  have hfin : partialBandSum f i x =
      ∑ j : Fin N, if j.val < i then paddedPacket f j.val x else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [paddedPacket, dite_eq_left j.isLt]
  rw [hfin]
  have heq := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j < i then paddedPacket f j x else 0) N
  rw [heq]
  rw [← Finset.sum_filter]
  have hs : (Finset.range N).filter (fun j => j < i) = Finset.range i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hs]

theorem partialBandSum_parity {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {i : ℕ} (hi : i ≤ N) (x : ℝ) :
    partialBandSum f i x =
      partialBandSum (parityPacket f 0) ((i + 1) / 2) x +
        partialBandSum (parityPacket f 1) (i / 2) x := by
  rw [partialBandSum_eq_sum_range f hi, sum_range_parity]
  rw [partialBandSum_eq_sum_range _ (by omega : (i + 1) / 2 ≤ N),
    partialBandSum_eq_sum_range _ (by omega : i / 2 ≤ N)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N := by have := Finset.mem_range.mp hj; omega
    simp only [paddedPacket, dite_eq_left hjN, parityPacket, Nat.add_zero]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjN : j < N := by have := Finset.mem_range.mp hj; omega
    simp only [paddedPacket, dite_eq_left hjN, parityPacket]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GeneralAnnularErrors
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The averaging error with arbitrary fixed annular constants. -/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert

theorem complex_band_average_energy (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {r R : ℝ} (hr : 0 < r)
    (hlow : ∀ ξ, |ξ| < r → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, R < |ξ| → 𝓕 f ξ = 0)
    {level : ℕ} (hl : level ≤ g.depth) {δ : ℝ} (hδ : 0 < δ)
    (hmesh : δ ≤ g.meshWidth level) :
    (∫ x, ‖g.scalarAverage g.lineMeasure f level x‖ ^ 2 ∂g.lineMeasure) ≤
      ((8 / (g.meshWidth level * δ)) * (2 * Real.pi * r)⁻¹ ^ 2 +
        8 * δ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 := by
  obtain ⟨A,hd,hlo,_⟩ := exists_schwartz_band_primitive f hr hlow hhigh
  have hav := g.schwartz_primitive_average_energy A f hd hl hδ hmesh
  have hp := schwartz_primitive_energy A f hr hd hlo
  have hc : 0 ≤ 8 / (g.meshWidth level * δ) :=
    div_nonneg (by norm_num) (mul_pos (g.meshWidth_pos level) hδ).le
  calc
    _ ≤ (8 / (g.meshWidth level * δ)) *
        ((2 * Real.pi * r)⁻¹ ^ 2 * ∫ x, ‖f x‖ ^ 2) +
        (8 * δ / g.meshWidth level) * ∫ x, ‖f x‖ ^ 2 :=
      hav.trans (add_le_add (mul_le_mul_of_nonneg_left hp hc) le_rfl)
    _ = _ := by ring

theorem general_annular_error (g : FiniteLineGrid) (f : SchwartzMap ℝ ℂ)
    {a b D : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hDlow : (2 * Real.pi * b) ^ 2 ≤ D ^ 2)
    (hDhigh : 8 * (1 + (2 * Real.pi * a)⁻¹ ^ 2) ≤ D ^ 2)
    (j : ℕ) (hlow : ∀ ξ, |ξ| < a * (4 : ℝ) ^ j → 𝓕 f ξ = 0)
    (hhigh : ∀ ξ, b * (4 : ℝ) ^ j < |ξ| → 𝓕 f ξ = 0)
    {level i : ℕ} (hl : level ≤ g.depth)
    (hmesh : g.meshWidth level = ((4 : ℝ) ^ i)⁻¹) :
    (∫ x, ‖bandErrorAt g f level i j x‖ ^ 2 ∂g.lineMeasure) ≤
      D ^ 2 * (1 / 4 : ℝ) ^ Nat.dist i j * ∫ x, ‖f x‖ ^ 2 := by
  have he : 0 ≤ ∫ x, ‖f x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  by_cases hji : j < i
  · have h := g.schwartz_low_frequency_error f (mul_nonneg hb (by positivity)) hhigh hl
    simp only [bandErrorAt, ite_eq_left hji]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ he)
    rw [hmesh, Nat.dist_eq_sub_of_le_right hji.le]
    have hr := four_pow_ratio hji.le
    have hq : 0 ≤ (1 / 4 : ℝ) ^ (i - j) := by positivity
    have hq1 : (1 / 4 : ℝ) ^ (i - j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have heq : ((4 : ℝ) ^ i)⁻¹ * (2 * Real.pi * (b * 4 ^ j)) =
        (2 * Real.pi * b) * (1 / 4 : ℝ) ^ (i - j) := by rw [← hr]; ring
    rw [heq, mul_pow]
    have hqq : ((1 / 4 : ℝ) ^ (i - j)) ^ 2 ≤ (1 / 4 : ℝ) ^ (i - j) := by nlinarith
    exact (mul_le_mul_of_nonneg_left hqq (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hDlow hq)
  · have hij : i ≤ j := by omega
    have hδ : 0 < ((4 : ℝ) ^ j)⁻¹ := by positivity
    have hm : ((4 : ℝ) ^ j)⁻¹ ≤ g.meshWidth level := by
      rw [hmesh]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hij)
    have h := complex_band_average_energy g f (mul_pos ha (by positivity)) hlow hhigh hl hδ hm
    simp only [bandErrorAt, ite_eq_right hji, zero_sub, norm_neg]
    refine h.trans (mul_le_mul_of_nonneg_right ?_ he)
    rw [hmesh, Nat.dist_eq_sub_of_le hij]
    have hr := four_pow_ratio hij
    have heq : (8 / (((4 : ℝ) ^ i)⁻¹ * ((4 : ℝ) ^ j)⁻¹)) *
        (2 * Real.pi * (a * 4 ^ j))⁻¹ ^ 2 +
        8 * ((4 : ℝ) ^ j)⁻¹ / ((4 : ℝ) ^ i)⁻¹ =
        8 * (1 + (2 * Real.pi * a)⁻¹ ^ 2) * (1 / 4 : ℝ) ^ (j - i) := by
      rw [← hr]
      field_simp
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hDhigh (by positivity)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GeneralAnnularComparison
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Square comparison for arbitrary fixed positive annular endpoints. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem annularErrorConstant_pos {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 < annularErrorConstant a b := by unfold annularErrorConstant; positivity

theorem annularErrorConstant_low {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (2 * Real.pi * b) ^ 2 ≤ annularErrorConstant a b ^ 2 := by
  apply pow_le_pow_left₀ (by positivity)
  unfold annularErrorConstant
  have hc : 0 ≤ (2 * Real.pi * a)⁻¹ := by positivity
  linarith

theorem annularErrorConstant_high {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    8 * (1 + (2 * Real.pi * a)⁻¹ ^ 2) ≤ annularErrorConstant a b ^ 2 := by
  have hc : 0 ≤ (2 * Real.pi * a)⁻¹ := by positivity
  have hd : 4 + 4 * (2 * Real.pi * a)⁻¹ ≤ annularErrorConstant a b := by
    unfold annularErrorConstant
    have : 0 ≤ 2 * Real.pi * b := by positivity
    linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 4 + 4 * (2 * Real.pi * a)⁻¹) hd 2
  nlinarith [sq_nonneg ((2 * Real.pi * a)⁻¹)]

theorem general_annular_square_comparison {N : ℕ} (g : FiniteLineGrid) (offset : ℕ)
    (f : Fin N → SchwartzMap ℝ ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hlow : ∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0)
    (hdepth : offset + N ≤ g.depth)
    (hmesh : ∀ i, g.meshWidth (offset + i) = ((4 : ℝ) ^ i)⁻¹) :
    (∑ i : Fin (N + 1), ∫ x, ‖partialBandSum f i.val x -
      g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖ ^ 2 ∂g.lineMeasure) ≤
      (4 * annularErrorConstant a b) ^ 2 * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  let D := annularErrorConstant a b
  have hD : 0 < D := annularErrorConstant_pos ha hb
  have h := finite_energy_schur g.lineMeasure
    (fun (i : Fin (N + 1)) (j : Fin N) => bandErrorAt g (f j) (offset + i.val) i.val j.val)
    (fun i j => bandErrorAt_memLp g (f j) (offset + i.val) i.val j.val)
    (fun i j => D * (1 / 2 : ℝ) ^ Nat.dist i.val j.val)
    (fun _ _ => mul_pos hD (by positivity))
    (fun j => ∫ x, ‖f j x‖ ^ 2) (fun j => integral_nonneg (fun _ => sq_nonneg _))
    (R := 4 * D) (C := 4 * D) (by positivity)
    (fun i => by
      rw [← Finset.mul_sum, mul_comm 4 D]
      exact mul_le_mul_of_nonneg_left (sum_half_distance_le_four N i.val) hD.le)
    (fun j => by
      simp only [Nat.dist_comm]
      rw [← Finset.mul_sum, mul_comm 4 D]
      exact mul_le_mul_of_nonneg_left (sum_half_distance_le_four (N + 1) j.val) hD.le)
    (fun i j => by
      have he := general_annular_error g (f j) ha hb
        (annularErrorConstant_low ha hb) (annularErrorConstant_high ha hb) j.val
        (hlow j) (hhigh j) (by have := i.isLt; omega) (hmesh i.val)
      have hsq : ((1 / 2 : ℝ) ^ Nat.dist i.val j.val) ^ 2 =
          (1 / 4 : ℝ) ^ Nat.dist i.val j.val := by
        rw [← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      simpa only [mul_pow, hsq, mul_assoc] using he)
  have heq : (∑ i : Fin (N + 1), ∫ x,
      ‖∑ j, bandErrorAt g (f j) (offset + i.val) i.val j.val x‖ ^ 2 ∂g.lineMeasure) =
      ∑ i : Fin (N + 1), ∫ x, ‖partialBandSum f i.val x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖ ^ 2 ∂g.lineMeasure := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [bandErrorAt_sum g f (offset + i.val) i.val] with x hx
    rw [hx]
  rw [heq] at h
  simpa only [pow_two] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ComplexVariationCoordinates
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-independent variation comparison for complex coordinates. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem complex_partition_variation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ)
    (p : Fin (N + 1) → Fin (N + 1)) :
    (∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3) ^ (2 / 3 : ℝ) ≤
      ∑ k, (∑ i : Fin N,
        ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 3) ^ (2 / 3 : ℝ) := by
  have hpow (a : ℝ) (ha : 0 ≤ a) : (a ^ 2) ^ (3 / 2 : ℝ) = a ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have h := PhaseCombinatorics.finite_minkowski
    (fun k (i : Fin N) => ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2)
    (fun _ _ => sq_nonneg _) (by norm_num : (1 : ℝ) ≤ 3 / 2)
  norm_num only [one_div_div, div_one] at h
  have hsum (i : Fin N) :
      (∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2) ^ (3 / 2 : ℝ) =
      ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 := by
    have heq : ‖F (p i.succ) - F (p i.castSucc)‖ ^ 2 =
        ∑ k, ‖F (p i.succ) k - F (p i.castSucc) k‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    rw [← heq]
    exact hpow _ (norm_nonneg _)
  simpa only [hsum, hpow _ (norm_nonneg _)] using h

theorem complex_finiteCubicVariation_le {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ) :
    (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      ∑ k, (finiteCubicVariation (fun n => F n k) N) ^ (2 / 3 : ℝ) := by
  classical
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun p : Fin (N + 1) → Fin (N + 1) => if Monotone p then
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖ ^ 3 else 0)
  change (Finset.univ.sup' _ _) ^ (2 / 3 : ℝ) ≤ _
  rw [hp]
  by_cases hmono : Monotone p
  · rw [ite_eq_left hmono]
    apply (complex_partition_variation_le F N p).trans
    apply Finset.sum_le_sum
    intro k _
    exact Real.rpow_le_rpow (by positivity)
      (partition_le_finiteCubicVariation (fun n => F n k) N p hmono) (by norm_num)
  · rw [ite_eq_right hmono, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    exact Finset.sum_nonneg fun k _ =>
      Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _


end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ScalarLineVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar complex form of the actual-grid variation comparison. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LipschitzHilbert

theorem scalarVector_sub (z w : ℂ) : scalarVector (z - w) = scalarVector z - scalarVector w := by
  ext u
  rfl

theorem norm_scalarVector (z : ℂ) : ‖scalarVector z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [scalarVector, Real.sqrt_sq (norm_nonneg z)]

theorem scalarVector_measurable : Measurable scalarVector := by
  exact (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr (fun _ => measurable_id))

theorem finiteCubicVariation_scalarVector (F : ℕ → ℂ) (N : ℕ) :
    finiteCubicVariation (fun i => scalarVector (F i)) N = finiteCubicVariation F N := by
  unfold finiteCubicVariation
  simp_rw [← scalarVector_sub, norm_scalarVector]

theorem scalarVector_average (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℂ)
    (i : ℕ) (x : ℝ) :
    g.complexAverage μ (fun y => scalarVector (f y)) i x =
      scalarVector (g.scalarAverage μ f i x) := by
  ext u
  rfl

theorem lintegral_enorm_square (μ : Measure ℝ) (f : ℝ → ℂ) (hf : MemLp f 2 μ) :
    (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (hf.integrable_norm_pow (by decide : 2 ≠ 0))
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShiftedLineAverage
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Start the actual mesh martingale at a prescribed finer level. This
allows the surrounding finite root interval to grow without changing
the packet scales used in the comparison. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert
namespace FiniteLineGrid

theorem shifted_average_martingale (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (offset : ℕ) :
    Martingale (fun i => g.average μ f (offset + i)) (g.shiftedFiltration offset) μ :=
  martingale_condExp f (g.shiftedFiltration offset) μ

end FiniteLineGrid

theorem lineGrid_shifted_lepingle (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (g : FiniteLineGrid) (offset : ℕ) (κ : Type) [Fintype κ]
      (F : ℝ → EuclideanSpace ℂ κ), Measurable F →
      (∀ k, MemLp (fun x => (F x k).re) 2 g.lineMeasure) →
      (∀ k, MemLp (fun x => (F x k).im) 2 g.lineMeasure) → ∀ N : ℕ,
        (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
          (fun i => g.complexAverage g.lineMeasure F (offset + i) x) N) ^ (2 / 3 : ℝ) ∂g.lineMeasure) ≤
          (C : ℝ≥0∞) ^ 2 * ∫⁻ x, ‖F x‖ₑ ^ 2 ∂g.lineMeasure := by
  obtain ⟨C,hC,hbound⟩ := lepingle_complex_finite_measure hL
  refine ⟨C,hC,?_⟩
  intro g offset κ inst F hF hRe hIm N
  have h := hbound ℝ inferInstance g.lineMeasure inferInstance κ (g.shiftedFiltration offset)
    (fun i => g.complexAverage g.lineMeasure F (offset + i))
    (fun k => by simpa only [FiniteLineGrid.complexAverage_re] using
      g.shifted_average_martingale g.lineMeasure (fun x => (F x k).re) offset)
    (fun k => by simpa only [FiniteLineGrid.complexAverage_im] using
      g.shifted_average_martingale g.lineMeasure (fun x => (F x k).im) offset)
    (fun k i => by simpa only [FiniteLineGrid.complexAverage_re] using
      g.average_memLp g.lineMeasure _ (hRe k) (offset + i))
    (fun k i => by simpa only [FiniteLineGrid.complexAverage_im] using
      g.average_memLp g.lineMeasure _ (hIm k) (offset + i)) N
  exact h.trans (mul_le_mul_right (g.complexAverage_energy g.lineMeasure F hF hRe hIm (offset + N)) _)

theorem scalar_shifted_line_comparison (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (g : FiniteLineGrid) (offset : ℕ)
      (f : ℝ → ℂ) (P : ℕ → ℝ → ℂ), Measurable f →
      (∀ i, Measurable (P i)) → MemLp f 2 g.lineMeasure → ∀ N : ℕ,
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => P i x) N) ^ (2 / 3 : ℝ)
        ∂g.lineMeasure) ≤
      2 * (C : ℝ≥0∞) ^ 2 * (∫⁻ x, ‖f x‖ₑ ^ 2 ∂g.lineMeasure) +
        8 * ∑ i : Fin (N + 1), ∫⁻ x,
          ‖P i.val x - g.scalarAverage g.lineMeasure f (offset + i.val) x‖ₑ ^ 2 ∂g.lineMeasure := by
  obtain ⟨C,hC,hbound⟩ := lineGrid_shifted_lepingle hL
  refine ⟨C,hC,?_⟩
  intro g offset f P hf hP hf2 N
  let F := fun x => scalarVector (f x)
  let Q := fun i x => scalarVector (P i x)
  let M := fun i => g.complexAverage g.lineMeasure F (offset + i)
  have h := lintegral_finiteCubicVariation_comparison g.lineMeasure Q M
    (fun i => scalarVector_measurable.comp (hP i))
    (fun i => g.complexAverage_measurable g.lineMeasure F (offset + i)) N
  have hm := hbound g offset Unit F (scalarVector_measurable.comp hf)
    (fun _ => hf2.re) (fun _ => hf2.im) N
  have ht := h.trans (add_le_add (by
    simpa only [mul_assoc] using mul_le_mul_right hm 2) le_rfl)
  simpa only [Q, M, F, finiteCubicVariation_scalarVector, scalarVector_average,
    ← scalarVector_sub, ← ofReal_norm, norm_scalarVector, mul_assoc] using ht

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local annular variation from Lépingle's inequality,
with the smooth/dyadic comparison supplied by packet estimates. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem fullBandSum_coe {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) :
    fullBandSum f = (∑ j, f j : SchwartzMap ℝ ℂ) := by
  funext x
  simp [fullBandSum]

theorem fullBandSum_memLp {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) :
    MemLp (fullBandSum f) 2 volume := by
  rw [fullBandSum_coe]
  exact (∑ j, f j : SchwartzMap ℝ ℂ).memLp 2 volume

theorem partialBandSum_memLp {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    MemLp (partialBandSum f i) 2 volume := by
  have h (j : Fin N) : MemLp (fun x => if j.val < i then f j x else 0) 2 volume := by
    by_cases hj : j.val < i
    · simpa only [ite_eq_left hj] using (f j).memLp 2 volume
    · simp only [ite_eq_right hj]
      exact MemLp.zero
  convert memLp_finsetSum Finset.univ (fun j _ => h j) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [partialBandSum]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GlobalAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exhaust the line by growing roots while keeping the comparison mesh
fixed. The annular variation constant is independent of the root size. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem expandingGrid_root (N M : ℕ) :
    (expandingGrid N M).root = Ico (-((4 : ℝ) ^ M) / 2) ((4 : ℝ) ^ M / 2) := by
  unfold FiniteLineGrid.root expandingGrid
  congr 1
  ring

theorem expandingGrid_mesh (N M i : ℕ) :
    (expandingGrid N M).meshWidth (M + i) = ((4 : ℝ) ^ i)⁻¹ := by
  simp only [FiniteLineGrid.meshWidth, expandingGrid, Nat.cast_ofNat, pow_add]
  field_simp

theorem expandingGrid_mono (N : ℕ) : Monotone (fun M => (expandingGrid N M).root) := by
  intro M K hMK
  change (expandingGrid N M).root ⊆ (expandingGrid N K).root
  rw [expandingGrid_root, expandingGrid_root]
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hMK
  exact Ico_subset_Ico (by linarith) (by linarith)

theorem expandingGrid_cover (N : ℕ) : (⋃ M, (expandingGrid N M).root) = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt (2 * |x|) (by norm_num : (1 : ℝ) < 4)
  refine ⟨M,?_⟩
  rw [expandingGrid_root]
  constructor <;> linarith [neg_abs_le x, le_abs_self x]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_HilbertAnnularVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional complex annular variation estimate, with no
dependence of the constant on the number of coordinates. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem ennreal_complex_variation_coordinates {κ : Type*} [Fintype κ]
    (F : ℕ → EuclideanSpace ℂ κ) (N : ℕ) :
    ENNReal.ofReal (finiteCubicVariation F N) ^ (2 / 3 : ℝ) ≤
      ∑ k, ENNReal.ofReal (finiteCubicVariation (fun i => F i k) N) ^ (2 / 3 : ℝ) := by
  have h := ENNReal.ofReal_le_ofReal (complex_finiteCubicVariation_le F N)
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Real.rpow_nonneg
    (finiteCubicVariation_nonneg _ _) _)] at h
  simpa only [ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _)
    (by norm_num : (0 : ℝ) ≤ 2 / 3)] using h

theorem partialBandSum_measurable {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (i : ℕ) :
    Measurable (partialBandSum f i) := by
  apply Finset.measurable_sum
  intro j _
  by_cases hj : j.val < i
  · simpa only [ite_eq_left hj] using (f j).continuous.measurable
  · simpa only [ite_eq_right hj] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℂ)))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_FiniteSpectralOverlap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Energy of a packet sum with finite spectral overlap. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem norm_sum_square_le_of_overlap {ι : Type*} [Fintype ι]
    (v : ι → ℂ) (M : ℕ)
    (hM : (Finset.univ.filter (fun j => v j ≠ 0)).card ≤ M) :
    ‖∑ j, v j‖ ^ 2 ≤ M * ∑ j, ‖v j‖ ^ 2 := by
  classical
  let s := Finset.univ.filter (fun j => v j ≠ 0)
  have hv : (∑ j ∈ s, v j) = ∑ j, v j := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hj
  have he : (∑ j ∈ s, ‖v j‖ ^ 2) = ∑ j, ‖v j‖ ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hz : v j = 0 := by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hj
    simp [hz]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun j => ‖v j‖) (f := fun _ => (1 : ℝ)) (g := fun j => ‖v j‖ ^ 2)
    (fun _ _ => by norm_num) (fun _ _ => sq_nonneg _) (fun _ _ => by simp)
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s v) 2
  rw [hv] at hn
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [he] at hcs
  exact (hn.trans hcs).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hM)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem finite_spectral_overlap_energy {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap ℝ ℂ) (M : ℕ)
    (hM : ∀ ξ, (Finset.univ.filter (fun j => 𝓕 (f j) ξ ≠ 0)).card ≤ M) :
    (∫ x, ‖∑ j, f j x‖ ^ 2) ≤ M * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  let F : SchwartzMap ℝ ℂ := ∑ j, f j
  have hsum (x : ℝ) : F x = ∑ j, f j x := by simp [F]
  have hf (ξ : ℝ) : 𝓕 F ξ = ∑ j, 𝓕 (f j) ξ := by
    change (SchwartzMap.fourierTransformCLM ℂ (∑ j, f j)) ξ = _
    rw [map_sum]
    simp
  have hi : Integrable (fun ξ => ∑ j, ‖𝓕 (f j) ξ‖ ^ 2) volume :=
    integrable_finsetSum _ (fun j _ => ((𝓕 (f j)).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0))
  calc
    _ = ∫ ξ, ‖𝓕 F ξ‖ ^ 2 := by
      rw [SchwartzMap.integral_norm_sq_fourier]
      simp only [hsum]
    _ ≤ ∫ ξ, (M : ℝ) * ∑ j, ‖𝓕 (f j) ξ‖ ^ 2 := by
      apply integral_mono (((𝓕 F).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)) (hi.const_mul M)
      intro ξ
      dsimp only
      rw [hf]
      exact norm_sum_square_le_of_overlap _ M (hM ξ)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum]
      · simp only [SchwartzMap.integral_norm_sq_fourier]
      · intro j _
        exact ((𝓕 (f j)).memLp 2).integrable_norm_pow (by decide : 2 ≠ 0)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_GeometricSpectralOverlap
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The spectral overlap count for fixed-width annuli at radix-four scales. -/

noncomputable section

open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem geometric_spectral_overlap {N M : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {a b : ℝ} (ha : 0 < a) (hsep : b < a * (4 : ℝ) ^ M)
    (hlow : ∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0)
    (ξ : ℝ) : (Finset.univ.filter (fun j => 𝓕 (f j) ξ ≠ 0)).card ≤ M := by
  classical
  let s := Finset.univ.filter (fun j : Fin N => 𝓕 (f j) ξ ≠ 0)
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    have hm : m ∈ s := Finset.min'_mem s hs
    have hm0 : 𝓕 (f m) ξ ≠ 0 := (Finset.mem_filter.mp hm).2
    have hmupper : |ξ| ≤ b * (4 : ℝ) ^ m.val := by
      by_contra h
      exact hm0 (hhigh m ξ (lt_of_not_ge h))
    have hinterval (j : Fin N) (hj : j ∈ s) : j.val ∈ Finset.Ico m.val (m.val + M) := by
      have hlo : m ≤ j := Finset.min'_le s j hj
      have hj0 : 𝓕 (f j) ξ ≠ 0 := (Finset.mem_filter.mp hj).2
      have hjlower : a * (4 : ℝ) ^ j.val ≤ |ξ| := by
        by_contra h
        exact hj0 (hlow j ξ (lt_of_not_ge h))
      have hhi : j.val < m.val + M := by
        by_contra h
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (le_of_not_gt h)
        have hprod := mul_le_mul_of_nonneg_left hp ha.le
        rw [pow_add] at hprod
        have hsep' := mul_lt_mul_of_pos_right hsep
          (pow_pos (by norm_num : (0 : ℝ) < 4) m.val)
        nlinarith [hprod]
      exact Finset.mem_Ico.mpr ⟨hlo,hhi⟩
    have hsubset : s.image (fun j : Fin N => j.val) ⊆ Finset.Ico m.val (m.val + M) := by
      intro k hk
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
      exact hinterval j hj
    have hcard := Finset.card_le_card hsubset
    rw [Finset.card_image_of_injective s Fin.val_injective, Nat.card_Ico] at hcard
    simpa only [Nat.add_sub_cancel_left] using hcard
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change s.card ≤ M
    simp [he]

theorem geometric_annular_energy {N M : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    {a b : ℝ} (ha : 0 < a) (hsep : b < a * (4 : ℝ) ^ M)
    (hlow : ∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0)
    (hhigh : ∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0) :
    (∫ x, ‖∑ j, f j x‖ ^ 2) ≤ M * ∑ j, ∫ x, ‖f j x‖ ^ 2 :=
  finite_spectral_overlap_energy f M (geometric_spectral_overlap f ha hsep hlow hhigh)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_GeneralAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Whole-line annular variation with arbitrary fixed inner and outer
frequency constants. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem general_scalar_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < a * (4 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, b * (4 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ)) ≤ (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
  obtain ⟨C,hC,hbound⟩ := scalar_shifted_line_comparison hL
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt (b / a) (by norm_num : (1 : ℝ) < 4)
  have hsep : b < a * (4 : ℝ) ^ M := by
    have h := (div_lt_iff₀ ha).mp hM
    simpa only [mul_comm] using h
  let D : ℝ≥0 := ⟨annularErrorConstant a b, (annularErrorConstant_pos ha hb).le⟩
  let K : ℝ≥0 := 2 * C ^ 2 * M + 8 * (4 * D) ^ 2 + 1
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro N f hlow hhigh
  have hlocal (g : FiniteLineGrid) (offset : ℕ) (hdepth : offset + N ≤ g.depth)
      (hmesh : ∀ i, g.meshWidth (offset + i) = ((4 : ℝ) ^ i)⁻¹) :
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ) ∂g.lineMeasure) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
    have hf : Measurable (fullBandSum f) := by
      rw [fullBandSum_coe]
      exact (∑ j, f j : SchwartzMap ℝ ℂ).continuous.measurable
    have hf2 : MemLp (fullBandSum f) 2 g.lineMeasure := (fullBandSum_memLp f).restrict g.root
    have hp2 (i : ℕ) : MemLp (partialBandSum f i) 2 g.lineMeasure :=
      (partialBandSum_memLp f i).restrict g.root
    have he2 (i : ℕ) : MemLp (fun x => partialBandSum f i x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i) x) 2 g.lineMeasure := by
      convert (hp2 i).sub (g.scalarAverage_memLp g.lineMeasure _ hf2 (offset + i)) using 1
      all_goals try with_reducible_and_instances rfl
    have h := hbound g offset (fullBandSum f) (partialBandSum f) hf
      (partialBandSum_measurable f) hf2 N
    rw [lintegral_enorm_square _ _ hf2] at h
    simp_rw [lintegral_enorm_square _ _ (he2 _)] at h
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      integral_nonneg (fun x => sq_nonneg (‖partialBandSum f i.val x -
        g.scalarAverage g.lineMeasure (fullBandSum f) (offset + i.val) x‖)))] at h
    have htotal : (∫ x, ‖fullBandSum f x‖ ^ 2 ∂g.lineMeasure) ≤
        M * ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
      apply le_trans _ (geometric_annular_energy f ha hsep hlow hhigh)
      exact setIntegral_le_integral
        ((fullBandSum_memLp f).integrable_norm_pow (by decide : 2 ≠ 0))
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    have hsquare := general_annular_square_comparison g offset f ha hb hlow hhigh hdepth hmesh
    have ht := ENNReal.ofReal_le_ofReal htotal
    have hs := ENNReal.ofReal_le_ofReal hsquare
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg M), ENNReal.ofReal_natCast] at ht
    rw [ENNReal.ofReal_mul (sq_nonneg _)] at hs
    have hc : ENNReal.ofReal ((4 * annularErrorConstant a b) ^ 2) = (4 * (D : ℝ≥0∞)) ^ 2 := by
      change ENNReal.ofReal ((4 * (D : ℝ)) ^ 2) = _
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      simp only [ENNReal.ofReal_coe_nnreal]
    rw [hc] at hs
    calc
      _ ≤ 2 * (C : ℝ≥0∞) ^ 2 * (M * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) +
          8 * ((4 * (D : ℝ≥0∞)) ^ 2 * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) :=
        h.trans (add_le_add (mul_le_mul_right ht _) (mul_le_mul_right hs _))
      _ ≤ _ := by
        have hk : 2 * (C : ℝ≥0∞) ^ 2 * M + 8 * (4 * (D : ℝ≥0∞)) ^ 2 ≤ (K : ℝ≥0∞) := by
          dsimp [K]
          exact le_add_of_nonneg_right (by positivity)
        first | (convert mul_le_mul_right hk (ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) using 1 <;> ring) | exact (le_of_eq (by ring)).trans ((mul_le_mul_right hk (ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2))).trans (le_of_eq (by ring)))
  let V := fun x => ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
    (2 / 3 : ℝ)
  change (∫⁻ x, V x) ≤ _
  rw [← setLIntegral_univ, ← expandingGrid_cover N,
    setLIntegral_iUnion_of_directed V (expandingGrid_mono N).directed_le]
  apply iSup_le
  intro m
  exact hlocal (expandingGrid N m) m (by simp [expandingGrid]) (expandingGrid_mesh N m)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ParityPackets
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral support and energy of the even/odd packet subfamilies. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert

theorem two_pow_parity (j r : ℕ) :
    (2 : ℝ) ^ (2 * j + r) = 2 ^ r * (4 : ℝ) ^ j := by
  rw [pow_add, pow_mul]
  norm_num
  ring

theorem parityPacket_low {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (a : ℝ) (r : ℕ)
    (hlow : ∀ k ξ, |ξ| < a * (2 : ℝ) ^ k.val → 𝓕 (f k) ξ = 0)
    (j : Fin N) (ξ : ℝ) (hξ : |ξ| < (a * (2 : ℝ) ^ r) * (4 : ℝ) ^ j.val) :
    𝓕 (parityPacket f r j) ξ = 0 := by
  by_cases h : 2 * j.val + r < N
  · simp only [parityPacket, paddedPacket, dite_eq_left h]
    apply hlow ⟨2 * j.val + r,h⟩ ξ
    simpa only [two_pow_parity, mul_assoc] using hξ
  · simp [parityPacket, paddedPacket, h]

theorem parityPacket_high {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (b : ℝ) (r : ℕ)
    (hhigh : ∀ k ξ, b * (2 : ℝ) ^ k.val < |ξ| → 𝓕 (f k) ξ = 0)
    (j : Fin N) (ξ : ℝ) (hξ : (b * (2 : ℝ) ^ r) * (4 : ℝ) ^ j.val < |ξ|) :
    𝓕 (parityPacket f r j) ξ = 0 := by
  by_cases h : 2 * j.val + r < N
  · simp only [parityPacket, paddedPacket, dite_eq_left h]
    apply hhigh ⟨2 * j.val + r,h⟩ ξ
    simpa only [two_pow_parity, mul_assoc] using hξ
  · simp [parityPacket, paddedPacket, h]

theorem sum_parity_le (u : ℕ → ℝ) (N r : ℕ) (hu : ∀ j, 0 ≤ u j)
    (hzero : ∀ j, N ≤ j → u j = 0) :
    (∑ j : Fin N, u (2 * j.val + r)) ≤ ∑ j : Fin N, u j.val := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => 2 * j + r) (Finset.range N) := by
    intro i _ j _ h
    change 2 * i + r = 2 * j + r at h
    omega
  have hmap : (Finset.range N).image (fun j => 2 * j + r) ⊆ Finset.range (2 * N + r + 1) := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have hj' := Finset.mem_range.mp hj
    apply Finset.mem_range.mpr
    omega
  have h := OAI.sum_le_sum_of_injOn (fun j : ℕ => 2 * j + r) hinj hmap
    (f := fun j => u (2 * j + r)) (g := u) (fun _ _ => le_rfl) (fun j _ _ => hu j)
  have ht : (∑ j ∈ Finset.range N, u j) = ∑ j ∈ Finset.range (2 * N + r + 1), u j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j _ hj
    exact hzero j (by simpa only [Finset.mem_range, not_lt] using hj)
  rw [← ht] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => u (2 * j + r)) N,
    Fin.sum_univ_eq_sum_range u N]
  exact h

theorem parityPacket_energy {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (r : ℕ) :
    (∑ j, ∫ x, ‖parityPacket f r j x‖ ^ 2) ≤ ∑ j, ∫ x, ‖f j x‖ ^ 2 := by
  have h := sum_parity_le (fun j => ∫ x, ‖paddedPacket f j x‖ ^ 2) N r
    (fun j => integral_nonneg (fun x => sq_nonneg _)) (fun j hj => by
      simp [paddedPacket, Nat.not_lt.mpr hj])
  simpa only [parityPacket, paddedPacket, dite_eq_left (Fin.isLt _)] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DyadicAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The manuscript's dyadic annular variation estimate, obtained from
the two radix-four subfamilies with exact partial-sum indexing. -/

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem finiteCubicVariation_parity {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (x : ℝ) :
    (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2 / 3 : ℝ) ≤
      2 * (finiteCubicVariation (fun i => partialBandSum (parityPacket f 0) i x) N) ^ (2 / 3 : ℝ) +
      2 * (finiteCubicVariation (fun i => partialBandSum (parityPacket f 1) i x) N) ^ (2 / 3 : ℝ) := by
  let E := fun i => partialBandSum (parityPacket f 0) i x
  let O := fun i => partialBandSum (parityPacket f 1) i x
  have heq := finiteCubicVariation_congr (fun i => partialBandSum f i x)
    (fun i => E ((i + 1) / 2) + O (i / 2)) N (fun i hi => partialBandSum_parity f hi x)
  rw [heq]
  have hE := finiteCubicVariation_comp_le E N (fun i => (i + 1) / 2)
    (fun i j hij => Nat.div_le_div_right (Nat.add_le_add_right hij 1)) (by omega)
  have hO := finiteCubicVariation_comp_le O N (fun i => i / 2)
    (fun _ _ hij => Nat.div_le_div_right hij) (by omega)
  have hsum := finiteCubicVariation_add_square (fun i => E ((i + 1) / 2)) (fun i => O (i / 2)) N
  exact hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (finiteCubicVariation_nonneg _ _) hE (by norm_num)) (by norm_num))
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (finiteCubicVariation_nonneg _ _) hO (by norm_num)) (by norm_num)))

theorem lintegral_variation_parity {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
      2 * (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (parityPacket f 0) i x) N) ^ (2 / 3 : ℝ)) +
      2 * (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (parityPacket f 1) i x) N) ^ (2 / 3 : ℝ)) := by
  have hpoint (x : ℝ) := ENNReal.ofReal_le_ofReal (finiteCubicVariation_parity f x)
  have hpos (g : Fin N → SchwartzMap ℝ ℂ) (x : ℝ) :
      0 ≤ 2 * (finiteCubicVariation (fun i => partialBandSum g i x) N) ^ (2 / 3 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _)
  simp only [ENNReal.ofReal_add (hpos _ _) (hpos _ _),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num : (0 : ℝ) ≤ 2 / 3)] at hpoint
  have h := lintegral_mono (μ := volume) hpoint
  have hm (r : ℕ) : Measurable (fun x => ENNReal.ofReal (finiteCubicVariation
      (fun i => partialBandSum (parityPacket f r) i x) N) ^ (2 / 3 : ℝ)) :=
    (measurable_finiteCubicVariation _
      (partialBandSum_measurable (parityPacket f r)) N).ennreal_ofReal.pow_const _
  rw [lintegral_add_left ((hm 0).const_mul (2 : ℝ≥0∞)),
    lintegral_const_mul _ (hm 0), lintegral_const_mul _ (hm 1)] at h
  exact h

theorem dyadic_scalar_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (f : Fin N → SchwartzMap ℝ ℂ),
      (∀ j ξ, |ξ| < a * (2 : ℝ) ^ j.val → 𝓕 (f j) ξ = 0) →
      (∀ j ξ, b * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun i => partialBandSum f i x) N) ^
        (2 / 3 : ℝ)) ≤ (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2) := by
  obtain ⟨K0,hK0,h0⟩ := general_scalar_annular_variation hL ha hb
  obtain ⟨K1,hK1,h1⟩ := general_scalar_annular_variation hL
    (mul_pos ha (by norm_num : (0 : ℝ) < 2)) (mul_nonneg hb (by norm_num : (0 : ℝ) ≤ 2))
  refine ⟨2 * K0 + 2 * K1, by positivity, ?_⟩
  intro N f hlow hhigh
  have he := h0 N (parityPacket f 0)
    (by simpa using parityPacket_low f a 0 hlow)
    (by simpa using parityPacket_high f b 0 hhigh)
  have ho := h1 N (parityPacket f 1)
    (by simpa using parityPacket_low f a 1 hlow)
    (by simpa using parityPacket_high f b 1 hhigh)
  have heE := ENNReal.ofReal_le_ofReal (parityPacket_energy f 0)
  have hoE := ENNReal.ofReal_le_ofReal (parityPacket_energy f 1)
  calc
    _ ≤ 2 * ((K0 : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) +
        2 * ((K1 : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j x‖ ^ 2)) :=
      (lintegral_variation_parity f).trans (add_le_add
        (mul_le_mul_right (he.trans (mul_le_mul_right heE _)) _)
        (mul_le_mul_right (ho.trans (mul_le_mul_right hoE _)) _))
    _ = _ := by push_cast; ring

theorem dyadic_hilbert_annular_variation (hL : LepingleInput) {a b : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (f : Fin N → κ → SchwartzMap ℝ ℂ),
      (∀ j k ξ, |ξ| < a * (2 : ℝ) ^ j.val → 𝓕 (f j k) ξ = 0) →
      (∀ j k ξ, b * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j k) ξ = 0) →
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∑ k, ∫ x, ‖f j k x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := dyadic_scalar_annular_variation hL ha hb
  refine ⟨K,hK,?_⟩
  intro N κ inst f hlow hhigh
  calc
    _ ≤ ∫⁻ x, ∑ k, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_mono
      intro x
      exact ennreal_complex_variation_coordinates (fun i => hilbertPartialBandSum f i x) N
    _ = ∑ k, ∫⁻ x, ENNReal.ofReal (finiteCubicVariation
        (fun i => partialBandSum (fun j => f j k) i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_finsetSum
      intro k _
      exact (measurable_finiteCubicVariation _ (partialBandSum_measurable (fun j => f j k)) N).ennreal_ofReal.pow_const _
    _ ≤ ∑ k, (K : ℝ≥0∞) * ENNReal.ofReal (∑ j, ∫ x, ‖f j k x‖ ^ 2) :=
      Finset.sum_le_sum (fun k _ => hbound N (fun j => f j k)
        (fun j => hlow j k) (fun j => hhigh j k))
    _ = _ := by
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg]
      · congr 2
        exact Finset.sum_comm
      · intro k _
        exact Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LocalizedAnnularVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localizing the dyadic annular variation estimate by the manuscript's
polynomial weights. The constant is uniform in the number of scales,
coordinates, and the location and length of the interval. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem partialBandSum_polynomialLocalization {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ)
    (a r : ℝ) (q i : ℕ) (x : ℝ) :
    partialBandSum (fun j => polynomialLocalization a r q (f j)) i x =
      (polynomialWeight a r q x : ℂ) * partialBandSum f i x := by
  unfold partialBandSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [polynomialLocalization_apply, mul_zero]

theorem hilbertPartialBandSum_polynomialLocalization {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (a r : ℝ) (q i : ℕ) (x : ℝ) :
    hilbertPartialBandSum (fun j k => polynomialLocalization a r q (f j k)) i x =
      polynomialWeight a r q x • hilbertPartialBandSum f i x := by
  ext k
  change partialBandSum (fun j => polynomialLocalization a r q (f j k)) i x =
    polynomialWeight a r q x • partialBandSum (fun j => f j k) i x
  rw [partialBandSum_polynomialLocalization, Complex.real_smul]

theorem localized_dyadic_hilbert_variation (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) [Fintype κ]
      (f : Fin N → κ → SchwartzMap ℝ ℂ) (a r : ℝ) (q : ℕ)
      (J : Set ℝ) (c : ℝ),
      (∀ j k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (f j k) ξ = 0) →
      (∀ j k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j k) ξ = 0) →
      MeasurableSet J → 0 ≤ c → (∀ x ∈ J, c ≤ polynomialWeight a r q x) →
      ENNReal.ofReal (c ^ 2) *
          (∫⁻ x in J, ENNReal.ofReal (finiteCubicVariation
            (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ)) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal
          (∑ j, ∑ k, ∫ x, ‖polynomialLocalization a r q (f j k) x‖ ^ 2) := by
  obtain ⟨K,hK,hbound⟩ := dyadic_hilbert_annular_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ inst f a r q J c hlow hhigh hJ hc hweight
  let F := fun j k => polynomialLocalization a r q (f j k)
  have hF := hbound N κ F
    (fun j k => polynomialLocalization_low a r q (f j k) _ _ (hlow j k) (hhigh j k))
    (fun j k => polynomialLocalization_high a r q (f j k) _ _ (hlow j k) (hhigh j k))
  have hpoint (x : ℝ) (hx : x ∈ J) :
      ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ) ≤
        ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum F i x) N) ^ (2 / 3 : ℝ) := by
    have heq : (fun i => hilbertPartialBandSum F i x) =
        (fun i => polynomialWeight a r q x • hilbertPartialBandSum f i x) := by
      funext i
      exact hilbertPartialBandSum_polynomialLocalization f a r q i x
    rw [heq, ennreal_finiteCubicVariation_smul_square]
    gcongr
    exact hweight x hx
  calc
    _ = ∫⁻ x in J, ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum f i x) N) ^ (2 / 3 : ℝ) :=
      (lintegral_const_mul' _ _ (by simp)).symm
    _ ≤ ∫⁻ x in J, ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum F i x) N) ^ (2 / 3 : ℝ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hJ] with x hx
      exact hpoint x hx
    _ ≤ ∫⁻ x, ENNReal.ofReal (finiteCubicVariation
          (fun i => hilbertPartialBandSum F i x) N) ^ (2 / 3 : ℝ) :=
      lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ ≤ _ := hF

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxPolynomialWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial localization lower bound on a reference interval, with
the horizontal box offset retained explicitly. -/

noncomputable section
open Set

namespace LipschitzHilbert

theorem box_polynomial_base (u r k x : ℝ) (hr : 0 < r) (hx : |x - u| ≤ r) :
    (1 + |k|) ^ 2 / 8 ≤ 1 + (x - (u + r * k)) ^ 2 / r ^ 2 := by
  let v := (x - (u + r * k)) / r
  have hunit : |(x - u) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hx
  have heq : k = (x - u) / r - v := by
    dsimp [v]
    field_simp
    ring
  have hk : |k| ≤ 1 + |v| := by
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add hunit le_rfl)
  have hk2 := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |k|)
    (add_le_add (le_rfl : (1 : ℝ) ≤ 1) hk) 2
  have habs : |v| ^ 2 = v ^ 2 := sq_abs v
  have hs := sq_nonneg (|v| - 2)
  have hv : 1 + (x - (u + r * k)) ^ 2 / r ^ 2 = 1 + v ^ 2 := by
    dsimp [v]
    rw [div_pow]
  rw [hv]
  nlinarith

theorem box_polynomial_weight (u r k x : ℝ) (q : ℕ)
    (hr : 0 < r) (hx : |x - u| ≤ r) :
    ((1 + |k|) ^ 2 / 8) ^ q ≤ polynomialWeight (u + r * k) r q x := by
  exact pow_le_pow_left₀ (by positivity) (box_polynomial_base u r k x hr hx) q

theorem box_polynomial_weight_pos (k : ℝ) (q : ℕ) :
    0 < ((1 + |k|) ^ 2 / 8) ^ q := by positivity

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth about a box is absorbed by a slower packet envelope.
The integrated envelope has the packet length as its only scale factor. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert

theorem polynomial_base_le (x s a l r : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    1 + (x - a) ^ 2 / r ^ 2 ≤ 4 * (1 + ((x - s) / l) ^ 2) := by
  have hu : |(x - s) / r| ≤ |(x - s) / l| := by
    rw [abs_div, abs_div, abs_of_pos hr, abs_of_pos hl]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hl hlr
  have hv : |(s - a) / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    exact hsa
  have hu2 := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hu
  have hv2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr hv
  simp only [sq_abs, one_pow] at hu2 hv2
  have heq : (x - a) / r = (x - s) / r + (s - a) / r := by ring
  rw [← div_pow, heq]
  nlinarith [sq_nonneg ((x - s) / r - (s - a) / r), sq_nonneg ((x - s) / l)]

theorem polynomialWeight_sq_mul_envelope (x s a l r : ℝ) (q n : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hsa : |s - a| ≤ r) :
    polynomialWeight a r q x ^ 2 * lineEnvelope s l (n + 2 * q) x ≤
      16 ^ q * lineEnvelope s l n x := by
  let B := 1 + ((x - s) / l) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hbase := polynomial_base_le x s a l r hl hr hlr hsa
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + (x - a) ^ 2 / r ^ 2)
    hbase (2 * q)
  have hweight : polynomialWeight a r q x ^ 2 = (1 + (x - a) ^ 2 / r ^ 2) ^ (2 * q) := by
    simp only [polynomialWeight, ← pow_mul, Nat.mul_comm q 2]
  rw [hweight]
  calc
    _ ≤ (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 16 ^ q * lineEnvelope s l n x := by
      change (4 * B) ^ (2 * q) * (B ^ (n + 2 * q))⁻¹ = 16 ^ q * (B ^ n)⁻¹
      rw [mul_pow, pow_add, mul_inv_rev, ← mul_assoc]
      have hz : B ^ (2 * q) ≠ 0 := pow_ne_zero _ hB.ne'
      have hc : (4 : ℝ) ^ (2 * q) = 16 ^ q := by rw [pow_mul]; norm_num
      rw [mul_assoc ((4 : ℝ) ^ (2 * q)), mul_inv_cancel₀ hz, mul_one, hc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_EnvelopeSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted Cauchy--Schwarz for actual packet synthesis, followed by
polynomially weighted whole-line energy bounds. -/

noncomputable section
open MeasureTheory
open FourierTransform
open scoped BigOperators
open scoped FourierTransform

namespace LipschitzHilbert

theorem envelope_synthesis_square {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ι → ℂ) (f : ι → E) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    {C D : ℝ} (hD : 0 ≤ D) (hover : ∑ i, w i ≤ D)
    (henv : ∀ i, ‖f i‖ ≤ C * w i) :
    ‖∑ i, c i • f i‖ ^ 2 ≤ D * C ^ 2 * ∑ i, ‖c i‖ ^ 2 * w i := by
  have hterm (i : ι) : ‖c i • f i‖ ^ 2 / w i ≤ C ^ 2 * (‖c i‖ ^ 2 * w i) := by
    rw [norm_smul, mul_pow]
    apply (div_le_iff₀ (hw i)).mpr
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (henv i) 2
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg ‖c i‖)
    nlinarith
  calc
    _ ≤ (∑ i, w i) * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      weighted_sum_norm_square _ w hw
    _ ≤ D * ∑ i, ‖c i • f i‖ ^ 2 / w i :=
      mul_le_mul_of_nonneg_right hover (Finset.sum_nonneg (fun i _ =>
        div_nonneg (sq_nonneg _) (hw i).le))
    _ ≤ D * ∑ i, C ^ 2 * (‖c i‖ ^ 2 * w i) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) hD
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

theorem packetSynthesis_apply {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (x : ℝ) :
    packetSynthesis c f x = ∑ i, c i * f i x := by
  simp only [packetSynthesis, sum_apply, smul_apply, smul_eq_mul]

theorem polynomial_packetSynthesis_energy {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (s rho : ι → ℝ)
    (a l r C D : ℝ) (q : ℕ)
    (hl : 0 < l) (hr : 0 < r) (hlr : l ≤ r) (hrho : ∀ i, 0 < rho i)
    (hcenter : ∀ i, |s i - a| ≤ r) (hD : 0 ≤ D)
    (hover : ∀ x, ∑ i, rho i * lineEnvelope (s i) l (1 + 2 * q) x ≤ D)
    (henv : ∀ i x, ‖f i x‖ ≤ C * (rho i * lineEnvelope (s i) l (1 + 2 * q) x)) :
    (∫ x, ‖polynomialLocalization a r q (packetSynthesis c f) x‖ ^ 2) ≤
      D * C ^ 2 * 16 ^ q * (Real.pi * l) * ∑ i, ‖c i‖ ^ 2 * rho i := by
  have hE (i : ι) (x : ℝ) : 0 < rho i * lineEnvelope (s i) l (1 + 2 * q) x := by
    unfold lineEnvelope
    exact mul_pos (hrho i) (inv_pos.mpr (pow_pos (by positivity) _))
  have hpoint (x : ℝ) : ‖polynomialLocalization a r q (packetSynthesis c f) x‖ ^ 2 ≤
      D * C ^ 2 * ∑ i, (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x := by
    have hsyn := envelope_synthesis_square c (fun i => f i x)
      (fun i => rho i * lineEnvelope (s i) l (1 + 2 * q) x)
      (fun i => hE i x) hD (hover x) (fun i => henv i x)
    have hn : ‖polynomialLocalization a r q (packetSynthesis c f) x‖ ^ 2 =
        polynomialWeight a r q x ^ 2 * ‖∑ i, c i • f i x‖ ^ 2 := by
      rw [polynomialLocalization_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (le_trans zero_le_one (polynomialWeight_one_le a r q x)),
        mul_pow, packetSynthesis_apply]
      simp only [smul_eq_mul]
    rw [hn]
    calc
      _ ≤ polynomialWeight a r q x ^ 2 * (D * C ^ 2 *
          ∑ i, ‖c i‖ ^ 2 * (rho i * lineEnvelope (s i) l (1 + 2 * q) x)) :=
        mul_le_mul_of_nonneg_left hsyn (sq_nonneg _)
      _ = D * C ^ 2 * ∑ i, (‖c i‖ ^ 2 * rho i) *
          (polynomialWeight a r q x ^ 2 * lineEnvelope (s i) l (1 + 2 * q) x) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ D * C ^ 2 * ∑ i, (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD (sq_nonneg C))
        apply Finset.sum_le_sum
        intro i _
        have h := mul_le_mul_of_nonneg_left
          (polynomialWeight_sq_mul_envelope x (s i) a l r q 1 hl hr hlr (hcenter i))
          (mul_nonneg (sq_nonneg ‖c i‖) (hrho i).le)
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        ring
  have hi (i : ι) : Integrable
      (fun x => (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x) :=
    (integrable_lineEnvelope_one (s i) l hl).const_mul _
  calc
    _ ≤ ∫ x, D * C ^ 2 * ∑ i, (16 ^ q * (‖c i‖ ^ 2 * rho i)) * lineEnvelope (s i) l 1 x :=
      integral_mono (((polynomialLocalization a r q (packetSynthesis c f)).memLp 2 volume).integrable_norm_pow
        (by decide : 2 ≠ 0))
        ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
      simp_rw [integral_const_mul, integral_lineEnvelope_one _ l hl]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring

theorem packetSynthesis_fourier {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (packetSynthesis c f) ξ = ∑ i, c i * 𝓕 (f i) ξ := by
  have heq : (𝓕 (packetSynthesis c f) : SchwartzMap ℝ ℂ) = ∑ i, c i • 𝓕 (f i) := by
    rw [packetSynthesis, fourier_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact fourier_smul (c i) (f i)
  rw [heq]
  simp only [sum_apply, smul_apply, smul_eq_mul]

theorem packetSynthesis_fourier_zero {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ) (ξ : ℝ)
    (hf : ∀ i, 𝓕 (f i) ξ = 0) : 𝓕 (packetSynthesis c f) ξ = 0 := by
  rw [packetSynthesis_fourier]
  simp only [hf, mul_zero, Finset.sum_const_zero]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxSynthesisEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-box energy step in the reference-line concentration proof.
The assumed coefficient budget is the finite local Carleson sum appearing
in equation (src-10); the synthesis estimate is derived from envelopes. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem box_synthesis_energy {σ : Type*} {ι : σ → Type*} [Fintype σ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → ℂ) (f : ∀ j, ι j → SchwartzMap ℝ ℂ)
    (s rho : ∀ j, ι j → ℝ) (len : σ → ℝ) (a r C D T B : ℝ) (q : ℕ)
    (hlen : ∀ j, 0 < len j) (hr : 0 < r) (hlenr : ∀ j, ∀ _ : ι j, len j ≤ r)
    (hrho : ∀ j i, 0 < rho j i) (hrhoT : ∀ j i, rho j i ≤ T)
    (hcenter : ∀ j i, |s j i - a| ≤ r) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hover : ∀ j x, ∑ i, rho j i * lineEnvelope (s j i) (len j) (1 + 2 * q) x ≤ D)
    (henv : ∀ j i x, ‖f j i x‖ ≤ C * (rho j i * lineEnvelope (s j i) (len j) (1 + 2 * q) x))
    (hbudget : ∑ j, len j * ∑ i, ‖c j i‖ ^ 2 ≤ B * r) :
    (∑ j, ∫ x, ‖polynomialLocalization a r q (packetSynthesis (c j) (f j)) x‖ ^ 2) ≤
      D * C ^ 2 * 16 ^ q * Real.pi * T * (B * r) := by
  let A := D * C ^ 2 * 16 ^ q * Real.pi
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmass (j : σ) : ∑ i, ‖c j i‖ ^ 2 * rho j i ≤ T * ∑ i, ‖c j i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrhoT j i) (sq_nonneg ‖c j i‖)
  have hbound (j : σ) :
      (∫ x, ‖polynomialLocalization a r q (packetSynthesis (c j) (f j)) x‖ ^ 2) ≤
        (A * T) * (len j * ∑ i, ‖c j i‖ ^ 2) := by
    classical
    by_cases hnonempty : Nonempty (ι j)
    swap
    · let : IsEmpty (ι j) := ⟨fun i => hnonempty ⟨i⟩⟩
      simp [packetSynthesis, polynomialLocalization_apply]
    have h := polynomial_packetSynthesis_energy (c j) (f j) (s j) (rho j)
      a (len j) r C D q (hlen j) hr (hlenr j (Classical.choice hnonempty))
      (hrho j) (hcenter j) hD (hover j) (henv j)
    calc
      _ ≤ A * len j * ∑ i, ‖c j i‖ ^ 2 * rho j i := by
        convert h using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [A]
        ring
      _ ≤ A * len j * (T * ∑ i, ‖c j i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hmass j) (mul_nonneg hA (hlen j).le)
      _ = _ := by ring
  calc
    _ ≤ ∑ j, (A * T) * (len j * ∑ i, ‖c j i‖ ^ 2) := Finset.sum_le_sum (fun j _ => hbound j)
    _ = (A * T) * (∑ j, len j * ∑ i, ‖c j i‖ ^ 2) := (Finset.mul_sum _ _ _).symm
    _ ≤ (A * T) * (B * r) := mul_le_mul_of_nonneg_left hbudget (mul_nonneg hA hT)
    _ = _ := by rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineTiling
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite _root_.OAI.LipschitzHilbert.FiniteLineGrid.lineMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Countably many actual finite line meshes cover a reference line. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

theorem tiledLineGrid_root (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G)
    (k : ℤ) :
    (tiledLineGrid origin H hH G N hG k).root =
      Ico (origin + k * H) (origin + (k + 1 : ℤ) * H) := by
  unfold FiniteLineGrid.root tiledLineGrid
  congr 1
  push_cast
  ring

theorem tiledLineGrid_pairwise_disjoint (origin H : ℝ) (hH : 0 < H) (G N : ℕ)
    (hG : 0 < G) :
    Pairwise fun i j => Disjoint (tiledLineGrid origin H hH G N hG i).root
      (tiledLineGrid origin H hH G N hG j).root := by
  intro i j hij
  simp only [tiledLineGrid_root]
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hi.2, hj.1]
  · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hj.2, hi.1]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LineLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform finite lattice overlap bound from the actual line integral of
the rational envelope. No cardinality factor or implicit lattice assumption
is used. -/

noncomputable section

open Set MeasureTheory Function
open scoped BigOperators

namespace LipschitzHilbert

theorem lineEnvelope_cell_comparison (x k y : ℝ) (hy : y ∈ Ico k (k + 1)) :
    lineEnvelope x 1 1 k ≤ 4 * lineEnvelope x 1 1 y := by
  have hdelta : (y - k) ^ 2 ≤ 1 := by
    have ha : |y - k| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr ha
    simpa only [sq_abs, one_pow] using hs
  have hb : 1 + (y - x) ^ 2 ≤ 4 * (1 + (k - x) ^ 2) := by
    nlinarith [sq_nonneg ((k - x) - (y - k)), sq_nonneg (k - x)]
  simp only [lineEnvelope, div_one, pow_one]
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hb)

theorem lineEnvelope_le_cell_integral (x k : ℝ) :
    lineEnvelope x 1 1 k ≤ 4 * ∫ y in Ico k (k + 1), lineEnvelope x 1 1 y := by
  have hint : IntegrableOn (lineEnvelope x 1 1) (Ico k (k + 1)) :=
    (integrable_lineEnvelope_one x 1 (by norm_num)).integrableOn
  have hfinite : volume (Ico k (k + 1)) ≠ ⊤ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  have h := setIntegral_mono_on (integrableOn_const hfinite : IntegrableOn
      (fun _ : ℝ => lineEnvelope x 1 1 k) (Ico k (k + 1)) volume)
    (hint.const_mul 4) measurableSet_Ico (fun y hy => lineEnvelope_cell_comparison x k y hy)
  rw [integral_const_mul] at h
  simpa [setIntegral_const, Real.volume_Ico, measureReal_def] using h

theorem finite_line_lattice_overlap (x : ℝ) (s : Finset ℤ) :
    (∑ k ∈ s, lineEnvelope x 1 1 k) ≤ 4 * Real.pi := by
  classical
  have hint := integrable_lineEnvelope_one x 1 (by norm_num)
  have hd : (s : Set ℤ).Pairwise (Disjoint on fun k : ℤ => Ico (k : ℝ) (k + 1)) := by
    intro i _ j _ hij
    have h := tiledLineGrid_pairwise_disjoint 0 1 (by norm_num) 2 0 (by norm_num) hij
    simpa only [tiledLineGrid_root, Int.cast_add, Int.cast_one, mul_one, zero_add] using h
  have hsum := integral_biUnion_finset s (fun _ _ => measurableSet_Ico) hd
    (fun _ _ => hint.integrableOn)
  calc
    _ ≤ ∑ k ∈ s, 4 * ∫ y in Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y :=
      Finset.sum_le_sum (fun k _ => lineEnvelope_le_cell_integral x k)
    _ = 4 * ∫ y in ⋃ k ∈ s, Ico (k : ℝ) (k + 1), lineEnvelope x 1 1 y := by
      rw [← Finset.mul_sum, hsum]
    _ ≤ 4 * ∫ y, lineEnvelope x 1 1 y := by
      exact mul_le_mul_of_nonneg_left (setIntegral_le_integral hint
        (Filter.Eventually.of_forall (lineEnvelope_nonneg x 1 1))) (by norm_num)
    _ = 4 * Real.pi := by rw [integral_lineEnvelope_one x 1 (by norm_num), mul_one]

theorem lineEnvelope_lattice_rescale (a l x : ℝ) (hl : l ≠ 0) (k : ℤ) (n : ℕ) :
    lineEnvelope (a + l * k) l n x = lineEnvelope ((x - a) / l) 1 n k := by
  unfold lineEnvelope
  congr 3
  simp only [div_one]
  have h : (x - (a + l * k)) / l = -((k : ℝ) - (x - a) / l) := by
    field_simp
    ring
  rw [h, neg_sq]

theorem finite_plane_lattice_overlap (x y : ℝ) (s : Finset (ℤ × ℤ)) :
    (∑ p ∈ s, lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2) ≤
      (4 * Real.pi) ^ 2 := by
  classical
  have hsub : s ⊆ (s.image Prod.fst) ×ˢ (s.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  calc
    _ ≤ ∑ p ∈ (s.image Prod.fst) ×ˢ (s.image Prod.snd),
        lineEnvelope x 1 1 p.1 * lineEnvelope y 1 1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
        mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
    _ = (∑ i ∈ s.image Prod.fst, lineEnvelope x 1 1 i) *
        ∑ j ∈ s.image Prod.snd, lineEnvelope y 1 1 j := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ (4 * Real.pi) * (4 * Real.pi) :=
      mul_le_mul (finite_line_lattice_overlap x _) (finite_line_lattice_overlap y _)
        (Finset.sum_nonneg (fun j _ => lineEnvelope_nonneg _ _ _ _)) (by positivity)
    _ = _ := (pow_two _).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TileLatticeEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform overlap for actual rectangular tile-center lattices, allowing
arbitrary horizontal and vertical scales and finite subfamilies. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem finite_scaled_plane_lattice_overlap (a b l W x y : ℝ)
    (hl : l ≠ 0) (hW : W ≠ 0) (s : Finset (ℤ × ℤ)) {m n : ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ p ∈ s, lineEnvelope (a + l * p.1) l m x *
      lineEnvelope (b + W * p.2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  calc
    _ ≤ ∑ p ∈ s, lineEnvelope ((x - a) / l) 1 1 p.1 *
        lineEnvelope ((y - b) / W) 1 1 p.2 := by
      apply Finset.sum_le_sum
      intro p _
      rw [lineEnvelope_lattice_rescale a l x hl p.1 m,
        lineEnvelope_lattice_rescale b W y hW p.2 n]
      exact mul_le_mul (lineEnvelope_antitone _ _ _ hm) (lineEnvelope_antitone _ _ _ hn)
        (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
    _ ≤ _ := finite_plane_lattice_overlap _ _ s

theorem injective_tile_lattice_overlap {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y : ℝ) (hl : l ≠ 0) (hW : W ≠ 0)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∑ i, lineEnvelope (a + l * (index i).1) l m x *
      lineEnvelope (b + W * (index i).2) W n y) ≤ (4 * Real.pi) ^ 2 := by
  classical
  have h := finite_scaled_plane_lattice_overlap a b l W x y hl hW
    (Finset.univ.image index) hm hn
  rw [Finset.sum_image (fun _ _ _ _ heq => hinj heq)] at h
  exact h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing localized packet variations with summable box weights. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem cubicVariation_nonneg {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) :
    0 ≤ cubicVariation F N := Real.rpow_nonneg (finiteCubicVariation_nonneg F N) _

theorem cubicVariation_sq {E : Type*} [NormedAddCommGroup E] (F : ℕ → E) (N : ℕ) :
    cubicVariation F N ^ 2 = (finiteCubicVariation F N) ^ (2 / 3 : ℝ) := by
  unfold cubicVariation
  rw [← Real.rpow_natCast, ← Real.rpow_mul (finiteCubicVariation_nonneg F N)]
  norm_num

theorem cubicVariation_finset_sum {ι E : Type*} [NormedAddCommGroup E]
    (F : ι → ℕ → E) (s : Finset ι) (N : ℕ) :
    cubicVariation (fun n => ∑ i ∈ s, F i n) N ≤ ∑ i ∈ s, cubicVariation (F i) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cubicVariation, finiteCubicVariation]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (finiteCubicVariation_add_rpow (F i) (fun n => ∑ j ∈ s, F j n) N).trans
      (add_le_add le_rfl ih)

theorem weighted_cubicVariation_sum {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (F : ι → ℕ → E) (N : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    (finiteCubicVariation (fun n => ∑ i, F i n) N) ^ (2 / 3 : ℝ) ≤
      (∑ i, w i) * ∑ i, (finiteCubicVariation (F i) N) ^ (2 / 3 : ℝ) / w i := by
  have hs := pow_le_pow_left₀ (cubicVariation_nonneg _ _)
    (cubicVariation_finset_sum F Finset.univ N) 2
  have hcs := weighted_sum_norm_square (fun i => cubicVariation (F i) N) w hw
  simp only [Real.norm_eq_abs, abs_of_nonneg (cubicVariation_nonneg _ _), cubicVariation_sq] at hcs hs
  rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => cubicVariation_nonneg (F i) N))] at hcs
  exact hs.trans hcs

theorem lintegral_weighted_cubicVariation_sum {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) (F : ι → ℕ → Ω → E)
    (hF : ∀ i n, Measurable (F i n)) (N : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => ∑ i, F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
      ENNReal.ofReal (∑ i, w i) * ∑ i, ENNReal.ofReal ((w i)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ := by
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hterm (i : ι) (x : Ω) :
      ENNReal.ofReal ((finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) / w i) =
        ENNReal.ofReal ((w i)⁻¹) *
          ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul
      (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _),
      ← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)]
    exact mul_comm _ _
  have hm (i : ι) : Measurable (fun x => ENNReal.ofReal ((w i)⁻¹) *
      ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ)) :=
    ((measurable_finiteCubicVariation _ (hF i) N).ennreal_ofReal.pow_const _).const_mul _
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (∑ i, w i) * ∑ i, ENNReal.ofReal ((w i)⁻¹) *
        ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ := by
      apply lintegral_mono
      intro x
      have hpoint := ENNReal.ofReal_le_ofReal
        (weighted_cubicVariation_sum (fun i n => F i n x) N w hw)
      rw [ENNReal.ofReal_mul hsum, ENNReal.ofReal_sum_of_nonneg
        (fun i _ => div_nonneg (Real.rpow_nonneg (finiteCubicVariation_nonneg _ _) _) (hw i).le)] at hpoint
      simp_rw [hterm] at hpoint
      rw [← ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)] at hpoint
      exact hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ (fun i _ => hm i)]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact lintegral_const_mul _ ((measurable_finiteCubicVariation _ (hF i) N).ennreal_ofReal.pow_const _)

theorem lintegral_cubicVariation_sum_of_weighted_energy {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) (F : ι → ℕ → Ω → E)
    (hF : ∀ i n, Measurable (F i n)) (N : ℕ) (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (A : ℝ≥0∞) {W : ℝ} (hweights : ∑ i, w i ≤ W)
    (henergy : ∀ i, (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
      (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤ A * ENNReal.ofReal (w i ^ 2)) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => ∑ i, F i n x) N) ^
      (2 / 3 : ℝ) ∂μ) ≤ ENNReal.ofReal (W ^ 2) * A := by
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  have hinv (i : ι) : ENNReal.ofReal ((w i)⁻¹) * ENNReal.ofReal (w i ^ 2) =
      ENNReal.ofReal (w i) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hw i).le)]
    congr 1
    field_simp
  calc
    _ ≤ ENNReal.ofReal (∑ i, w i) * ∑ i, ENNReal.ofReal ((w i)⁻¹) *
        ∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ :=
      lintegral_weighted_cubicVariation_sum μ F hF N w hw
    _ ≤ ENNReal.ofReal (∑ i, w i) * ∑ i, ENNReal.ofReal ((w i)⁻¹) *
        (A * ENNReal.ofReal (w i ^ 2)) := by
      gcongr with i
      exact henergy i
    _ = ENNReal.ofReal (∑ i, w i) * (A * ENNReal.ofReal (∑ i, w i)) := by
      congr 1
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => (hw i).le), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_left_comm, hinv]
    _ = ENNReal.ofReal ((∑ i, w i) ^ 2) * A := by
      rw [pow_two, ENNReal.ofReal_mul hsum]
      ac_rfl
    _ ≤ _ := by
      gcongr

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Geometry_TransverseBoxDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transverse decay of the reference-line envelope for centers in an
actual offset box. -/

noncomputable section

namespace LipschitzHilbert

theorem transverse_box_envelope (s y W b : ℝ) (n : ℕ) (hW : 0 < W)
    (hbox : |s - (y + W * b)| ≤ W) :
    lineEnvelope s W n y ≤ (((1 + |b|) ^ 2 / 8) ^ n)⁻¹ := by
  have hx : |(2 * y + W * b - s) - y| ≤ W := by
    have heq : (2 * y + W * b - s) - y = -(s - (y + W * b)) := by ring
    rw [heq, abs_neg]
    exact hbox
  have hb := box_polynomial_base y W b (2 * y + W * b - s) hW hx
  have heq : (2 * y + W * b - s) - (y + W * b) = y - s := by ring
  rw [heq, ← div_pow] at hb
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + |b|) ^ 2 / 8) hb n
  exact inv_anti₀ (by positivity) hp

theorem box_decay_le_line_envelope (b : ℝ) :
    (((1 + |b|) ^ 2 / 8) ^ 2)⁻¹ ≤ 64 * lineEnvelope 0 1 1 b ^ 2 := by
  have hbase : 1 + b ^ 2 ≤ (1 + |b|) ^ 2 := by nlinarith [abs_nonneg b, sq_abs b]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + b ^ 2) hbase 2
  have hinv := inv_anti₀ (by positivity : 0 < (1 + b ^ 2) ^ 2) hp
  have heq : (((1 + |b|) ^ 2 / 8) ^ 2)⁻¹ = 64 * (((1 + |b|) ^ 2) ^ 2)⁻¹ := by
    rw [div_pow, inv_div]
    norm_num
    ring
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 64)
  simpa only [lineEnvelope, sub_zero, div_one, pow_one, inv_pow] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_BoxVariationWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summable weights for the fixed-box variation estimates. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert

theorem boxVariationWeight_pos (p : ℤ × ℤ) : 0 < boxVariationWeight p := by
  unfold boxVariationWeight lineEnvelope
  positivity

theorem boxVariationWeight_sum {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index) :
    (∑ i, boxVariationWeight (index i)) ≤ (4 * Real.pi) ^ 2 := by
  have h := injective_tile_lattice_overlap index hinj 0 0 1 1 0 0 (by norm_num)
    (by norm_num) (by norm_num : 1 ≤ (1 : ℕ)) (by norm_num : 1 ≤ (1 : ℕ))
  have heq (k : ℤ) : lineEnvelope (0 + 1 * k) 1 1 0 = lineEnvelope 0 1 1 k := by
    simp [lineEnvelope]
  simpa only [heq, boxVariationWeight] using h

theorem ennreal_le_of_positive_real_weight {X : ℝ≥0∞} {c B : ℝ} (hc : 0 < c)
    (h : ENNReal.ofReal c * X ≤ ENNReal.ofReal B) : X ≤ ENNReal.ofReal (B / c) := by
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hcancel : (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal c = 1 := by
    rw [mul_comm, ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top]
  calc
    X = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * X) := by rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal B := mul_le_mul_right h _
    _ = ENNReal.ofReal (B / c) := by rw [ENNReal.ofReal_div_of_pos hc, div_eq_mul_inv, mul_comm]

theorem box_variation_decay_bound (p : ℤ × ℤ) {X : ℝ≥0∞} {M : ℝ} (hM : 0 ≤ M)
    (h : ENNReal.ofReal (((1 + |(p.1 : ℝ)|) ^ 2 / 8) ^ 2) * X ≤
      ENNReal.ofReal (M * (((1 + |(p.2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹)) :
    X ≤ ENNReal.ofReal (4096 * M * boxVariationWeight p ^ 2) := by
  apply (ennreal_le_of_positive_real_weight (by positivity) h).trans
  apply ENNReal.ofReal_le_ofReal
  have h1 := box_decay_le_line_envelope (p.1 : ℝ)
  have h2 := box_decay_le_line_envelope (p.2 : ℝ)
  have hprod := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hm := mul_le_mul_of_nonneg_left hprod hM
  convert hm using 1
  all_goals try (with_reducible_and_instances rfl)
  · ring
  · dsimp [boxVariationWeight]
    ring

theorem lintegral_sum_box_variation {Ω ι E : Type*} [MeasurableSpace Ω]
    [Fintype ι] [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) (F : ι → ℕ → Ω → E)
    (hF : ∀ i n, Measurable (F i n)) (N : ℕ)
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index) {M : ℝ} (hM : 0 ≤ M)
    (hbox : ∀ i, ENNReal.ofReal (((1 + |((index i).1 : ℝ)|) ^ 2 / 8) ^ 2) *
      (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
      ENNReal.ofReal (M * (((1 + |((index i).2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹)) :
    (∫⁻ x, ENNReal.ofReal (finiteCubicVariation (fun n => ∑ i, F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
      ENNReal.ofReal ((4 * Real.pi) ^ 4 * (4096 * M)) := by
  have henergy (i : ι) : (∫⁻ x, ENNReal.ofReal (finiteCubicVariation
      (fun n => F i n x) N) ^ (2 / 3 : ℝ) ∂μ) ≤
        ENNReal.ofReal (4096 * M) * ENNReal.ofReal (boxVariationWeight (index i) ^ 2) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hM)]
    exact box_variation_decay_bound _ hM (hbox i)
  have h := lintegral_cubicVariation_sum_of_weighted_energy μ F hF N
    (fun i => boxVariationWeight (index i)) (fun i => boxVariationWeight_pos (index i))
    (ENNReal.ofReal (4096 * M)) (boxVariationWeight_sum index hinj) henergy
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  congr 1
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TailLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict tail bounds pass to almost-everywhere limits. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LipschitzHilbert

theorem strict_tail_bound_of_ae_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : ℕ → X → ℝ) (g : X → ℝ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (t C : ℝ) (hC : 0 ≤ C) (hbound : ∀ n, μ.real {x | t < f n x} ≤ C) :
    μ.real {x | t < g x} ≤ C := by
  let S := fun m : ℕ => {x | ∀ n ≥ m, t < f n x}
  have hmono : Monotone S := by
    intro m n hmn x hx i hi
    exact hx i (hmn.trans hi)
  have hsub : ∀ᵐ x ∂μ, x ∈ {x | t < g x} → x ∈ ⋃ m, S m := by
    filter_upwards [hlim] with x hx ht
    have h := (tendsto_order.mp hx).1 t ht
    obtain ⟨m,hm⟩ := eventually_atTop.mp h
    exact mem_iUnion.mpr ⟨m,hm⟩
  have hmass : μ {x | t < g x} ≤ ENNReal.ofReal C := by
    calc
      _ ≤ μ (⋃ m, S m) := measure_mono_ae hsub
      _ = ⨆ m, μ (S m) := hmono.directed_le.measure_iUnion
      _ ≤ ENNReal.ofReal C := by
        apply iSup_le
        intro m
        have hle := ENNReal.ofReal_le_ofReal (hbound m)
        rw [ofReal_measureReal] at hle
        exact (measure_mono (show S m ⊆ {x | t < f m x} from fun _ hx => hx m le_rfl)).trans hle
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  simpa only [measureReal_def, ENNReal.toReal_ofReal hC] using hreal

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_FirstExceed
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Disjoint first-crossing events for a finite scalar process. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem firstExceed_disjoint {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) :
    Pairwise (fun i j => Disjoint (firstExceed U lambda i) (firstExceed U lambda j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (not_lt_of_ge (hxj.2 i h)) hxi.1
  · exact (not_lt_of_ge (hxi.2 j h)) hxj.1

theorem firstExceed_union {X : Type*} (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ) :
    (⋃ i : Fin (N + 1), firstExceed U lambda i.val) = finiteMaxEvent U lambda N := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact ⟨i, by omega, hi.1⟩
  · rintro ⟨i, hi, hUi⟩
    have hex : ∃ n, lambda < U n x := ⟨i,hUi⟩
    let n := Nat.find hex
    have hn : n ≤ i := Nat.find_min' hex hUi
    apply mem_iUnion.mpr
    refine ⟨⟨n,by omega⟩, Nat.find_spec hex, ?_⟩
    intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)

theorem measurableSet_firstExceed {X : Type*} [MeasurableSpace X]
    (U : ℕ → X → ℝ) (lambda : ℝ) (n : ℕ) (hU : ∀ i ≤ n, Measurable (U i)) :
    MeasurableSet (firstExceed U lambda n) := by
  unfold firstExceed
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_lt measurable_const (hU n le_rfl)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun hi =>
      measurableSet_le (hU i hi.le) measurable_const)

theorem firstExceed_measure_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (U : ℕ → X → ℝ) (lambda : ℝ) (N : ℕ)
    (hU : ∀ i ≤ N, Measurable (U i)) :
    (∑ i : Fin (N + 1), μ.real (firstExceed U lambda i.val)) =
      μ.real (finiteMaxEvent U lambda N) := by
  rw [← firstExceed_union]
  symm
  apply measureReal_iUnion_fintype
  · intro i j hij
    exact firstExceed_disjoint U lambda (fun h => hij (Fin.ext h))
  · intro i
    exact measurableSet_firstExceed U lambda i (fun j hj => hU j (by omega))
  · intro i
    exact measure_ne_top μ _

theorem firstExceed_norm_overshoot {X E : Type*} [NormedAddCommGroup E]
    (F : ℕ → X → E) (x : X) {lambda D : ℝ} (hlambda : 0 ≤ lambda)
    (n : ℕ) (hjump : ∀ i < n, ‖F (i + 1) x - F i x‖ ≤ D)
    (hx : x ∈ firstExceed (fun i y => ‖F i y - F 0 y‖) lambda n) :
    ‖F n x - F 0 x‖ ≤ lambda + D := by
  have hn : n ≠ 0 := by
    intro hn
    have hh := hx.1
    simp only [hn, sub_self, norm_zero] at hh
    linarith
  have hp := hx.2 (n - 1) (by omega)
  have hj := hjump (n - 1) (by omega)
  rw [show n - 1 + 1 = n by omega] at hj
  exact (norm_sub_le_norm_sub_add_norm_sub (F n x) (F (n - 1) x) (F 0 x)).trans
    (by linarith)

theorem firstExceed_large_subset {X E : Type*} [NormedAddCommGroup E]
    (F : ℕ → X → E) (N n : ℕ) (hn : n ≤ N) {lambda D δ : ℝ}
    (hlambda : 0 ≤ lambda) (hD : 0 ≤ D) (hδ : 0 ≤ δ)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) :
    finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) (lambda + D + δ) N ∩
        firstExceed (fun i x => ‖F i x - F 0 x‖) lambda n ⊆
      {x | ∃ i ≤ N - n, δ ≤ ‖F (n + i) x - F n x‖} ∩
        firstExceed (fun i x => ‖F i x - F 0 x‖) lambda n := by
  rintro x ⟨⟨k,hk,hlarge⟩,hx⟩
  refine ⟨?_,hx⟩
  have hkn : n ≤ k := by
    by_contra h
    have hb := hx.2 k (lt_of_not_ge h)
    linarith
  have hstop := firstExceed_norm_overshoot F x hlambda n
    (fun i hi => hjump i (hi.trans_le hn) x) hx
  refine ⟨k - n, by omega, ?_⟩
  rw [show n + (k - n) = k by omega]
  have htri := norm_sub_le_norm_sub_add_norm_sub (F k x) (F n x) (F 0 x)
  linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleLocalMaximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and time shift for a martingale, and the local weak-L1
maximal estimate used in the dyadic John--Nirenberg stopping argument. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

omit [IsFiniteMeasure μ] in
theorem martingale_timeShift (hF : Martingale F ℱ μ) (n : ℕ) :
    Martingale (fun i => F (n + i)) (timeShiftFiltration ℱ n) μ :=
  ⟨fun i => hF.stronglyMeasurable (n + i),
    fun _i _j hij => hF.condExp_ae_eq (Nat.add_le_add_left hij n)⟩

theorem martingale_restrict_initial (hF : Martingale F ℱ μ)
    {s : Set X} (hs : MeasurableSet[ℱ 0] s) : Martingale F ℱ (μ.restrict s) := by
  apply martingale_of_setIntegral_eq_succ hF.stronglyAdapted
    (fun i => (hF.integrable i).integrableOn)
  intro i t ht
  rw [Measure.restrict_restrict (ℱ.le i t ht)]
  exact hF.setIntegral_eq (Nat.le_succ i) (ht.inter (ℱ.mono (Nat.zero_le i) _ hs))

omit [IsFiniteMeasure μ] in
theorem martingale_abs (hF : Martingale F ℱ μ) :
    Submartingale (fun i x => |F i x|) ℱ μ := by
  have heq : (fun i x => |F i x|) = F ⊔ -F := by
    funext i x
    exact abs_eq_max_neg
  rw [heq]
  exact hF.submartingale.sup hF.neg.submartingale

theorem martingale_maximal_L1 (hF : Martingale F ℱ μ)
    {lambda : ℝ} (hlambda : 0 < lambda) (N : ℕ) :
    μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤ lambda⁻¹ * ∫ x, |F N x| ∂μ := by
  have hmax := maximal_ineq (martingale_abs hF) (fun i x => abs_nonneg (F i x))
    (ε := ⟨lambda,hlambda.le⟩) N
  change _ * μ {x | lambda ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one (fun i => |F i x|)} ≤
    ENNReal.ofReal (∫ x in {x | lambda ≤ (Finset.range (N + 1)).sup'
      Finset.nonempty_range_add_one (fun i => |F i x|)}, |F N x| ∂μ) at hmax
  have hevent : {x | lambda ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      (fun i => |F i x|)} = {x | ∃ i ≤ N, lambda ≤ |F i x|} := by
    ext x
    simp only [mem_ofPred_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff]
  rw [hevent] at hmax
  have hwhole : (∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ) ≤
      ∫ x, |F N x| ∂μ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => abs_nonneg (F N x)) (hF.integrable N).abs
  have hsetnonneg : 0 ≤ ∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ :=
    integral_nonneg (fun x => abs_nonneg (F N x))
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  have hreal : lambda * μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤
      ∫ x in {x | ∃ i ≤ N, lambda ≤ |F i x|}, |F N x| ∂μ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hsetnonneg] at ht
    exact ht
  have hfinal : μ.real {x | ∃ i ≤ N, lambda ≤ |F i x|} ≤
      (∫ x, |F N x| ∂μ) / lambda := by
    apply (le_div_iff₀ hlambda).mpr
    simpa only [mul_comm] using hreal.trans hwhole
  simpa only [div_eq_mul_inv, mul_comm] using hfinal

theorem martingale_local_maximal_L1 (hF : Martingale F ℱ μ) (n N : ℕ)
    {s : Set X} (hs : MeasurableSet[ℱ n] s) {lambda : ℝ} (hlambda : 0 < lambda) :
    (μ.restrict s).real {x | ∃ i ≤ N, lambda ≤ |F (n + i) x - F n x|} ≤
      lambda⁻¹ * ∫ x in s, |F (n + N) x - F n x| ∂μ := by
  have hshift := martingale_timeShift hF n
  have hconst : Martingale (fun _ => F n) (timeShiftFiltration ℱ n) μ :=
    martingale_const_fun _ _ (by
      change StronglyMeasurable[ℱ n] (F n)
      exact hF.stronglyMeasurable n) (hF.integrable n)
  have hcenter : Martingale (fun i x => F (n + i) x - F n x)
      (timeShiftFiltration ℱ n) μ := hshift.sub hconst
  exact martingale_maximal_L1 (martingale_restrict_initial hcenter
    (by change MeasurableSet[ℱ n] s; exact hs)) hlambda N

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleGoodLambda
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A first-crossing contraction for a finite martingale with bounded
conditional mean oscillation. This is the finite stopping step in the
John--Nirenberg proof; no exponential-tail theorem is assumed. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

theorem martingale_goodLambda (hF : Martingale F ℱ μ) (N : ℕ)
    {A D lambda : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hlambda : 0 ≤ lambda)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) :
    μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) (lambda + D + 2 * A) N) ≤
      (1 / 2 : ℝ) * μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) lambda N) := by
  let U := fun i x => ‖F i x - F 0 x‖
  let B := fun n => firstExceed U lambda n
  have hUm (i : ℕ) : Measurable (U i) :=
    ((hF.stronglyMeasurable i).measurable.le (ℱ.le i)).sub
      ((hF.stronglyMeasurable 0).measurable.le (ℱ.le 0)) |>.norm
  have hBm (n : ℕ) : MeasurableSet[ℱ n] (B n) := by
    let : MeasurableSpace X := ℱ n
    apply measurableSet_firstExceed U lambda n
    intro i hi
    exact ((hF.stronglyMeasurable i).mono (ℱ.mono hi)).measurable.sub
      ((hF.stronglyMeasurable 0).mono (ℱ.mono (Nat.zero_le n))).measurable |>.norm
  have hcell (n : Fin (N + 1)) :
      μ.real (finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) ≤
        (1 / 2 : ℝ) * μ.real (B n) := by
    let S := {x | ∃ i ≤ N - n.val, 2 * A ≤ |F (n.val + i) x - F n x|}
    have hSm : MeasurableSet S := by
      change MeasurableSet {x | ∃ i, i ≤ N - n.val ∧ 2 * A ≤ |F (n.val + i) x - F n x|}
      simp only [ofPred_exists, ofPred_and]
      apply MeasurableSet.iUnion
      intro i
      have hd : Measurable (fun x => F (n.val + i) x - F n x) :=
        ((hF.stronglyMeasurable (n.val + i)).measurable.le (ℱ.le _)).sub
          ((hF.stronglyMeasurable n.val).measurable.le (ℱ.le _))
      simpa only [Real.norm_eq_abs] using
        (MeasurableSet.const (i ≤ N - n.val)).inter
          (measurableSet_le measurable_const hd.norm)
    have hlocal := martingale_local_maximal_L1 hF n.val (N - n.val) (hBm n) (by positivity : 0 < 2 * A)
    have hbudget := hBMO n.val (by omega) (B n) (hBm n)
    have hindex : n.val + (N - n.val) = N := by omega
    rw [hindex] at hlocal
    have hsub : finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n ⊆ S ∩ B n := by
      simpa only [S, U, B, Real.norm_eq_abs] using
        firstExceed_large_subset F N n.val (by omega) hlambda hD
          (by positivity : 0 ≤ 2 * A) hjump
    calc
      _ ≤ μ.real (S ∩ B n) := measureReal_mono hsub
      _ = (μ.restrict (B n)).real S := (measureReal_restrict_apply hSm).symm
      _ ≤ (2 * A)⁻¹ * ∫ x in B n, |F N x - F n x| ∂μ := hlocal
      _ ≤ (2 * A)⁻¹ * (A * μ.real (B n)) :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by field_simp [hA.ne']
  have hcover : finiteMaxEvent U (lambda + D + 2 * A) N ⊆
      ⋃ n : Fin (N + 1), finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n := by
    intro x hx
    obtain ⟨i,hi,hUi⟩ := hx
    have hxsmall : x ∈ finiteMaxEvent U lambda N := ⟨i,hi,by linarith⟩
    rw [← firstExceed_union] at hxsmall
    obtain ⟨n,hn⟩ := mem_iUnion.mp hxsmall
    exact mem_iUnion.mpr ⟨n,⟨i,hi,hUi⟩,hn⟩
  calc
    _ ≤ μ.real (⋃ n : Fin (N + 1), finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) :=
      measureReal_mono hcover
    _ ≤ ∑ n : Fin (N + 1), μ.real (finiteMaxEvent U (lambda + D + 2 * A) N ∩ B n) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ n : Fin (N + 1), (1 / 2 : ℝ) * μ.real (B n) := Finset.sum_le_sum (fun n _ => hcell n)
    _ = (1 / 2 : ℝ) * μ.real (finiteMaxEvent U lambda N) := by
      rw [← Finset.mul_sum, firstExceed_measure_sum μ U lambda N (fun i _ => hUm i)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MartingaleGeometricTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterating the first-crossing contraction gives a geometric tail with
constants independent of the number of time steps. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

variable {X : Type*} {m : MeasurableSpace X} {μ : Measure X}
  [IsFiniteMeasure μ] {ℱ : Filtration ℕ m} {F : ℕ → X → ℝ}

theorem martingale_geometric_tail (hF : Martingale F ℱ μ) (N : ℕ)
    {A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) (k : ℕ) :
    μ.real (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) ((k : ℝ) * (D + 2 * A)) N) ≤
      (1 / 2 : ℝ) ^ k * μ.real univ := by
  induction k with
  | zero =>
    simpa only [Nat.cast_zero, zero_mul, pow_zero, one_mul] using
      (measureReal_mono (μ := μ) (subset_univ
        (finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) 0 N)))
  | succ k ih =>
    have hlambda : 0 ≤ (k : ℝ) * (D + 2 * A) := mul_nonneg (Nat.cast_nonneg k) (by linarith)
    have h := martingale_goodLambda hF N hA hD hlambda hBMO hjump
    have heq : (k : ℝ) * (D + 2 * A) + D + 2 * A =
        ((k + 1 : ℕ) : ℝ) * (D + 2 * A) := by push_cast; ring
    rw [heq] at h
    exact h.trans (by simpa only [pow_succ, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 1 / 2))

theorem martingale_terminal_geometric_tail (hF : Martingale F ℱ μ) (N : ℕ)
    {A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hBMO : TerminalMeanOscillationBound F ℱ μ N A)
    (hjump : ∀ i < N, ∀ x, ‖F (i + 1) x - F i x‖ ≤ D) (k : ℕ) :
    μ.real {x | (k : ℝ) * (D + 2 * A) < ‖F N x - F 0 x‖} ≤
      (1 / 2 : ℝ) ^ k * μ.real univ := by
  apply (measureReal_mono (μ := μ) (show
    {x | (k : ℝ) * (D + 2 * A) < ‖F N x - F 0 x‖} ⊆
      finiteMaxEvent (fun i x => ‖F i x - F 0 x‖) ((k : ℝ) * (D + 2 * A)) N from
        fun _ hx => ⟨N,le_rfl,hx⟩)).trans
  exact martingale_geometric_tail hF N hA hD hBMO hjump k

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_MeanOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local mean oscillation estimates used before John--Nirenberg.
The short part is controlled in mean and the long part by its oscillation.
All constants are independent of the dimension of the range. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_average_sub_le (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (hf : Integrable f μ) (hm : 0 < μ.real univ) (c : E) :
    ‖integralAverage μ f - c‖ ≤ (μ.real univ)⁻¹ * ∫ x, ‖f x - c‖ ∂μ := by
  have heq : integralAverage μ f - c = (μ.real univ)⁻¹ • ∫ x, (f x - c) ∂μ := by
    rw [integral_sub hf (integrable_const c), integral_const, smul_sub,
      smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hm.le)

theorem integral_oscillation_le_twice (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → E) (hf : Integrable f μ) (hm : 0 < μ.real univ) (c : E) :
    (∫ x, ‖f x - integralAverage μ f‖ ∂μ) ≤ 2 * ∫ x, ‖f x - c‖ ∂μ := by
  have hpoint (x : X) : ‖f x - integralAverage μ f‖ ≤
      ‖f x - c‖ + ‖integralAverage μ f - c‖ := by
    simpa only [norm_sub_rev] using
      norm_sub_le_norm_sub_add_norm_sub (f x) c (integralAverage μ f)
  calc
    _ ≤ ∫ x, (‖f x - c‖ + ‖integralAverage μ f - c‖) ∂μ :=
      integral_mono (hf.sub (integrable_const _)).norm
        ((hf.sub (integrable_const c)).norm.add (integrable_const _)) hpoint
    _ = (∫ x, ‖f x - c‖ ∂μ) + μ.real univ * ‖integralAverage μ f - c‖ := by
      rw [integral_add (show Integrable (fun x => ‖f x - c‖) μ from
        (hf.sub (integrable_const c)).norm) (integrable_const _),
        integral_const, smul_eq_mul]
    _ ≤ (∫ x, ‖f x - c‖ ∂μ) +
        μ.real univ * ((μ.real univ)⁻¹ * ∫ x, ‖f x - c‖ ∂μ) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (norm_average_sub_le μ f hf hm c) hm.le)
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hm.ne']; ring

omit [CompleteSpace E] in
theorem integralAverage_add (μ : Measure X) (f g : X → E)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    integralAverage μ (fun x => f x + g x) = integralAverage μ f + integralAverage μ g := by
  simp only [integralAverage, integral_add hf hg, smul_add]

theorem short_long_mean_oscillation (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → E) (hf : Integrable f μ) (hg : Integrable g μ)
    (hm : 0 < μ.real univ) {K L : ℝ}
    (hshort : (∫ x, ‖f x‖ ∂μ) ≤ K * μ.real univ)
    (hlong : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖g x - g y‖ ≤ L) :
    (∫ x, ‖f x + g x - integralAverage μ (fun y => f y + g y)‖ ∂μ) ≤
      (2 * K + L) * μ.real univ := by
  have hgpoint : ∀ᵐ x ∂μ, ‖g x - integralAverage μ g‖ ≤ L := by
    filter_upwards [hlong] with x hx
    exact norm_sub_mean_le μ g hg hm (g x) L hx
  have hfmean := integral_oscillation_le_twice μ f hf hm (0 : E)
  simp only [sub_zero] at hfmean
  have hgmean : (∫ x, ‖g x - integralAverage μ g‖ ∂μ) ≤ L * μ.real univ := by
    simpa only [integral_const, smul_eq_mul, mul_comm, Pi.sub_apply] using
      integral_mono_ae (hg.sub (integrable_const _)).norm (integrable_const L) hgpoint
  calc
    _ ≤ ∫ x, (‖f x - integralAverage μ f‖ + ‖g x - integralAverage μ g‖) ∂μ := by
      apply integral_mono
        (show Integrable (fun x => ‖f x + g x - integralAverage μ (fun y => f y + g y)‖) μ from
          ((hf.add hg).sub (integrable_const _)).norm)
        (show Integrable (fun x => ‖f x - integralAverage μ f‖ +
            ‖g x - integralAverage μ g‖) μ from
          (hf.sub (integrable_const _)).norm.add (hg.sub (integrable_const _)).norm)
      intro x
      rw [integralAverage_add μ f g hf hg]
      dsimp only
      rw [add_sub_add_comm]
      exact norm_add_le (f x - integralAverage μ f) (g x - integralAverage μ g)
    _ = (∫ x, ‖f x - integralAverage μ f‖ ∂μ) +
        ∫ x, ‖g x - integralAverage μ g‖ ∂μ := by
      exact integral_add (show Integrable (fun x => ‖f x - integralAverage μ f‖) μ from
        (hf.sub (integrable_const _)).norm)
        (show Integrable (fun x => ‖g x - integralAverage μ g‖) μ from
          (hg.sub (integrable_const _)).norm)
    _ ≤ (2 * K + L) * μ.real univ := by linarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mean oscillation on the actual line cells controls every martingale
jump by the branching factor. This supplies the overshoot bound in the
dyadic stopping proof of John--Nirenberg. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.FiniteLineGrid

theorem cell_mass (g : FiniteLineGrid) (level i : ℕ) :
    (volume.restrict (g.cell level i)).real univ = g.meshWidth level := by
  rw [measureReal_def, Measure.restrict_apply_univ, cell, Real.volume_Ico]
  have heq : g.origin + g.meshWidth level * (i + 1) -
      (g.origin + g.meshWidth level * i) = g.meshWidth level := by ring
  rw [heq, ENNReal.toReal_ofReal (g.meshWidth_pos level).le]

theorem cellMean_eq_integralAverage (g : FiniteLineGrid) (f : ℝ → ℝ) (level i : ℕ) :
    g.cellMean f level i = integralAverage (volume.restrict (g.cell level i)) f := by
  simp only [integralAverage, g.cell_mass, cellMean, smul_eq_mul]

theorem cellMean_sub_constant_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    {level i : ℕ} (hf : IntegrableOn f (g.cell level i)) (c : ℝ) :
    |g.cellMean f level i - c| ≤
      (g.meshWidth level)⁻¹ * ∫ x in g.cell level i, |f x - c| := by
  rw [g.cellMean_eq_integralAverage]
  simpa only [Real.norm_eq_abs, g.cell_mass] using
    norm_average_sub_le (volume.restrict (g.cell level i)) f hf
      (by rw [g.cell_mass]; exact g.meshWidth_pos level) c

theorem cell_subset_parent (g : FiniteLineGrid) {level i : ℕ}
    (hl : level + 1 ≤ g.depth) (hi : i < g.branching ^ (level + 1)) :
    g.cell (level + 1) i ⊆ g.cell level (i / g.branching) := by
  intro x hx
  have hr := g.cell_subset_root (level + 1) hi hx
  have hix := (g.index_eq_iff_mem_cell hl hr i).mpr hx
  have hp := congrArg Fin.val (g.index_parent (by omega : level < g.depth) x)
  change (g.index level x).val = (g.index (level + 1) x).val / g.branching at hp
  rw [hix] at hp
  exact (g.index_eq_iff_mem_cell (by omega) hr (i / g.branching)).mp hp

theorem parent_index_lt (g : FiniteLineGrid) {level i : ℕ}
    (hi : i < g.branching ^ (level + 1)) : i / g.branching < g.branching ^ level := by
  apply (Nat.div_lt_iff_lt_mul g.branching_pos).mpr
  simpa only [pow_succ] using hi

theorem meshWidth_succ (g : FiniteLineGrid) (level : ℕ) :
    g.meshWidth (level + 1) = g.meshWidth level / g.branching := by
  simp only [meshWidth, pow_succ, div_div]

theorem cellMean_parent_jump (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level i : ℕ} (hl : level + 1 ≤ g.depth) (hi : i < g.branching ^ (level + 1)) :
    |g.cellMean f (level + 1) i - g.cellMean f level (i / g.branching)| ≤
      g.branching * A := by
  have hip := g.parent_index_lt hi
  have hsub := g.cell_subset_parent hl hi
  have hfp : IntegrableOn f (g.cell level (i / g.branching)) :=
    hf.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root level hip))
  have hfc := hfp.mono_set hsub
  have hnorm : IntegrableOn (fun x => |f x - g.cellMean f level (i / g.branching)|)
      (g.cell level (i / g.branching)) := by
    simpa only [IntegrableOn, Real.norm_eq_abs, Pi.sub_apply] using
      (hfp.sub (integrable_const _)).norm
  have hmono : (∫ x in g.cell (level + 1) i, |f x - g.cellMean f level (i / g.branching)|) ≤
      ∫ x in g.cell level (i / g.branching), |f x - g.cellMean f level (i / g.branching)| :=
    setIntegral_mono_set hnorm (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  calc
    _ ≤ (g.meshWidth (level + 1))⁻¹ *
        ∫ x in g.cell (level + 1) i, |f x - g.cellMean f level (i / g.branching)| :=
      g.cellMean_sub_constant_le f hfc _
    _ ≤ (g.meshWidth (level + 1))⁻¹ * (A * g.meshWidth level) :=
      mul_le_mul_of_nonneg_left (hmono.trans (hA level (i / g.branching) (by omega) hip))
        (inv_nonneg.mpr (g.meshWidth_pos _).le)
    _ = _ := by rw [g.meshWidth_succ]; field_simp [(g.meshWidth_pos level).ne']

theorem average_eq_cellMean (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure f level x = g.cellMean f level i := by
  rw [g.average_eq_cell_mean f hf hl hi hx, cellMean, div_eq_mul_inv, mul_comm]

theorem average_jump_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level : ℕ} (hl : level < g.depth) {x : ℝ} (hx : x ∈ g.root) :
    |g.average g.lineMeasure f (level + 1) x - g.average g.lineMeasure f level x| ≤
      g.branching * A := by
  let i := (g.index (level + 1) x).val
  have hi : i < g.branching ^ (level + 1) := g.index_lt_level (by omega) x
  have hxc : x ∈ g.cell (level + 1) i :=
    (g.index_eq_iff_mem_cell (by omega) hx i).mp rfl
  rw [g.average_eq_cellMean f hf (by omega) hi hxc,
    g.average_eq_cellMean f hf (by omega) (g.parent_index_lt hi)
      (g.cell_subset_parent (by omega) hi hxc)]
  exact g.cellMean_parent_jump f hf hA (by omega) hi

theorem average_jump_le_everywhere (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {level : ℕ} (hl : level < g.depth) (x : ℝ) :
    |g.average g.lineMeasure f (level + 1) x - g.average g.lineMeasure f level x| ≤
      g.branching * A := by
  by_cases hx : x ∈ g.root
  · exact g.average_jump_le f hf hA hl hx
  · have ho : g.origin ∈ g.root := ⟨le_rfl, by linarith [g.width_pos]⟩
    have hidx (n : ℕ) : g.index n x = g.index n g.origin := by
      apply Fin.ext
      simp only [index, rawIndex, ite_eq_right hx, ite_eq_left ho, sub_self,
        zero_div, zero_mul, Nat.floor_zero]
    rw [g.average_constant g.lineMeasure f (level + 1) (hidx _),
      g.average_constant g.lineMeasure f level (hidx _)]
    exact g.average_jump_le f hf hA hl ho

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridConditionalBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete cellwise mean-oscillation bound implies the conditional
oscillation hypothesis used by the finite martingale stopping argument. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert.FiniteLineGrid

theorem integrated_oscillation_le (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {n : ℕ} (hn : n ≤ g.depth) {s : Set ℝ} (hs : MeasurableSet[g.filtration n] s) :
    (∫ x in s, |f x - g.average g.lineMeasure f n x| ∂g.lineMeasure) ≤
      A * g.lineMeasure.real s := by
  let G := fun x => |f x - g.average g.lineMeasure f n x|
  have havg : Integrable (g.average g.lineMeasure f n) g.lineMeasure :=
    (g.average_martingale g.lineMeasure f).integrable n
  have hG : Integrable G g.lineMeasure := (hf.sub havg).abs
  have hb : ∀ᵐ x ∂g.lineMeasure, g.average g.lineMeasure G n x ≤ A := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    let i := (g.index n x).val
    have hi : i < g.branching ^ n := g.index_lt_level hn x
    have hxc : x ∈ g.cell n i := (g.index_eq_iff_mem_cell hn hx i).mp rfl
    rw [g.average_eq_cell_mean G hG hn hi hxc]
    have heq : (∫ y in g.cell n i, G y) =
        ∫ y in g.cell n i, |f y - g.cellMean f n i| := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro y hy
      simp only [G, g.average_eq_cellMean f hf hn hi hy]
    rw [heq]
    exact (div_le_iff₀ (g.meshWidth_pos n)).mpr (hA n i hn hi)
  change (∫ x in s, G x ∂g.lineMeasure) ≤ _
  rw [← setIntegral_condExp (g.filtration.le n) hG hs]
  have h := integral_mono_ae (μ := g.lineMeasure.restrict s)
    integrable_condExp.integrableOn (integrable_const A)
    (ae_restrict_of_ae hb)
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm] using h

theorem terminal_mean_oscillation (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : g.HasMeanOscillationBound f A)
    {N : ℕ} (hN : N ≤ g.depth) :
    TerminalMeanOscillationBound (g.average g.lineMeasure f) g.filtration g.lineMeasure N A := by
  intro n hn s hs
  have hsm : MeasurableSet[g.filtration N] s := g.filtration.mono hn _ hs
  have havg : Integrable (g.average g.lineMeasure f n) g.lineMeasure :=
    (g.average_martingale g.lineMeasure f).integrable n
  have heq : g.lineMeasure[(fun x => f x - g.average g.lineMeasure f n x) | g.filtration N] =ᵐ[g.lineMeasure]
      (fun x => g.average g.lineMeasure f N x - g.average g.lineMeasure f n x) := by
    have hsub := condExp_sub hf havg (g.filtration N)
    have hmeas : StronglyMeasurable[g.filtration N] (g.average g.lineMeasure f n) :=
      (g.average_martingale g.lineMeasure f).stronglyMeasurable n |>.mono (g.filtration.mono hn)
    rw [condExp_of_stronglyMeasurable (g.filtration.le N) hmeas havg] at hsub
    exact hsub
  calc
    _ = ∫ x in s, |g.lineMeasure[(fun x => f x - g.average g.lineMeasure f n x) | g.filtration N] x|
        ∂g.lineMeasure := by
      apply setIntegral_congr_ae (g.filtration.le n _ hs)
      filter_upwards [heq] with x hx _
      rw [hx]
    _ ≤ ∫ x in s, |f x - g.average g.lineMeasure f n x| ∂g.lineMeasure :=
      setIntegral_abs_condExp_le hsm _
    _ ≤ _ := g.integrated_oscillation_le f hf hA (hn.trans hN) hs

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridBMO_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric John--Nirenberg tails for the concrete line-cell averages. -/

noncomputable section

open MeasureTheory Set

namespace LipschitzHilbert.FiniteLineGrid

theorem mean_oscillation_average_tail (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasMeanOscillationBound f A) {N : ℕ} (hN : N ≤ g.depth) (k : ℕ) :
    g.lineMeasure.real {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
      |g.average g.lineMeasure f N x - g.average g.lineMeasure f 0 x|} ≤
        (1 / 2 : ℝ) ^ k * g.lineMeasure.real univ := by
  have htail := martingale_terminal_geometric_tail (g.average_martingale g.lineMeasure f) N hA
    (mul_nonneg (Nat.cast_nonneg g.branching) hA.le)
    (g.terminal_mean_oscillation f hf hBMO hN)
    (fun i hi x => by
      simpa only [Real.norm_eq_abs] using
        g.average_jump_le_everywhere f hf hBMO (hi.trans_le hN) x) k
  have hscale : (k : ℝ) * ((g.branching : ℝ) * A + 2 * A) =
      (k : ℝ) * ((g.branching : ℝ) + 2) * A := by ring
  simpa only [hscale, Real.norm_eq_abs] using htail

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Trees_LineGridLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual cell averages converge at every continuity point in the root.
Only this continuous-function specialization of differentiation is needed
for the finite smooth packet and variation functions. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

theorem cell_zero (g : FiniteLineGrid) : g.cell 0 0 = g.root := by
  simp only [cell, meshWidth, pow_zero, div_one, Nat.cast_zero, mul_zero,
    add_zero, zero_add, mul_one, root]

theorem average_zero_eq_integralAverage (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {x : ℝ} (hx : x ∈ g.root) :
    g.average g.lineMeasure f 0 x = integralAverage g.lineMeasure f := by
  rw [g.average_eq_cellMean (i := 0) f hf (Nat.zero_le _) (by simp)
    (by simpa only [g.cell_zero] using hx), g.cellMean_eq_integralAverage, g.cell_zero]
  rfl

theorem average_close_of_mesh (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {n : ℕ} (hn : n ≤ g.depth)
    {x : ℝ} (hx : x ∈ g.root) {epsilon delta : ℝ}
    (hlocal : ∀ y, dist y x < delta → |f y - f x| ≤ epsilon)
    (hmesh : g.meshWidth n < delta) :
    |g.average g.lineMeasure f n x - f x| ≤ epsilon := by
  let i := (g.index n x).val
  have hi : i < g.branching ^ n := g.index_lt_level hn x
  have hxc : x ∈ g.cell n i := (g.index_eq_iff_mem_cell hn hx i).mp rfl
  have hfc : IntegrableOn f (g.cell n i) :=
    hf.mono_measure (Measure.restrict_mono_set volume (g.cell_subset_root n hi))
  have hpoint : ∀ᵐ y ∂volume.restrict (g.cell n i), ‖f x - f y‖ ≤ epsilon := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    have hyr := g.cell_subset_root n hi hy
    have hiy := (g.index_eq_iff_mem_cell hn hyr i).mpr hy
    have heq : g.index n y = g.index n x := Fin.ext hiy
    have hd := g.same_index_distance hn hyr hx heq
    have hdist : dist y x < delta := by
      rw [Real.dist_eq]
      exact hd.trans_lt hmesh
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hlocal y hdist
  have h := norm_sub_mean_le (volume.restrict (g.cell n i)) f hfc
    (by rw [g.cell_mass]; exact g.meshWidth_pos n) (f x) epsilon hpoint
  rw [g.average_eq_cellMean f hf hn hi hxc, g.cellMean_eq_integralAverage]
  simpa only [integralAverage, Real.norm_eq_abs, abs_sub_comm] using h

theorem meshWidth_tendsto_zero (g : FiniteLineGrid) (hb : 1 < g.branching) :
    Tendsto g.meshWidth atTop (𝓝 0) := by
  change Tendsto (fun n => g.width / (g.branching : ℝ) ^ n) atTop (𝓝 0)
  have hbR : (1 : ℝ) < g.branching := by exact_mod_cast hb
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one
    (r := (g.branching : ℝ)⁻¹) (by rw [abs_of_pos (inv_pos.mpr (by linarith))]; exact inv_lt_one_of_one_lt₀ hbR)
  have h : Tendsto (fun n : ℕ => g.width * ((g.branching : ℝ)⁻¹) ^ n)
      atTop (𝓝 (g.width * 0)) := tendsto_const_nhds.mul hpow
  simpa only [mul_zero, meshWidth, div_eq_mul_inv, inv_pow] using
    (h : Tendsto (fun n : ℕ => g.width * ((g.branching : ℝ)⁻¹) ^ n) atTop (𝓝 (g.width * 0)))

theorem average_tendsto_at_continuity (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hf : Integrable f g.lineMeasure)
    {x : ℝ} (hx : x ∈ g.root) (hcont : ContinuousAt f x) :
    Tendsto (fun N => (g.withDepth N).average (g.withDepth N).lineMeasure f N x)
      atTop (𝓝 (f x)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  obtain ⟨delta,hdelta,hlocal⟩ := Metric.continuousAt_iff.mp hcont (epsilon / 2) (by positivity)
  have hmesh := (tendsto_order.mp (g.meshWidth_tendsto_zero hb)).2 delta hdelta
  filter_upwards [hmesh] with N hN
  rw [Real.dist_eq]
  apply lt_of_le_of_lt ((g.withDepth N).average_close_of_mesh f hf le_rfl hx
    (fun y hy => (by simpa only [Real.dist_eq] using (hlocal hy).le)) hN)
  linarith

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ContinuousBMOTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! John--Nirenberg's geometric distribution bound for a continuous
function on an actual finite interval. The proof passes the uniform finite
grid estimate to the function, using pointwise convergence of cell means. -/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_mean_oscillation_tail (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasFullMeanOscillationBound f A) (k : ℕ) :
    g.lineMeasure.real {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
      |f x - integralAverage g.lineMeasure f|} ≤
        (1 / 2 : ℝ) ^ k * g.lineMeasure.real univ := by
  let F := fun N x => |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
    integralAverage g.lineMeasure f|
  have hlim : ∀ᵐ x ∂g.lineMeasure,
      Tendsto (fun N => F N x) atTop (𝓝 |f x - integralAverage g.lineMeasure f|) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    have h := (g.average_tendsto_at_continuity hb f hf hx (hc x hx)).sub_const
      (integralAverage g.lineMeasure f)
    simpa only [F, Real.norm_eq_abs] using h.norm
  apply strict_tail_bound_of_ae_tendsto g.lineMeasure F _ hlim _ _ (by positivity)
  intro N
  have hBN : (g.withDepth N).HasMeanOscillationBound f A := by
    intro n i _ hi
    exact hBMO n i hi
  have htail := (g.withDepth N).mean_oscillation_average_tail f hf hA hBN le_rfl k
  have heq : {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A < F N x} =ᵐ[g.lineMeasure]
      {x | (k : ℝ) * ((g.branching : ℝ) + 2) * A <
        |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
          (g.withDepth N).average (g.withDepth N).lineMeasure f 0 x|} := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    change ((k : ℝ) * ((g.branching : ℝ) + 2) * A < F N x) = ((k : ℝ) * ((g.branching : ℝ) + 2) * A <
        |(g.withDepth N).average (g.withDepth N).lineMeasure f N x -
          (g.withDepth N).average (g.withDepth N).lineMeasure f 0 x|)
    simp only [F, (g.withDepth N).average_zero_eq_integralAverage f hf hx]
    rfl
  have hm := congrArg ENNReal.toReal (measure_congr heq)
  exact hm.trans_le htail

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricTailExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A geometric distribution bound gives an exponential moment by summing
the level strips. The factor is absolute and no boundedness hypothesis is
needed for the function. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LipschitzHilbert

theorem geometric_tail_exponential {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {H : ℝ} (hH : 0 < H)
    (htail : ∀ n : ℕ, μ.real {x | (n : ℝ) * H < f x} ≤
      (1 / 2 : ℝ) ^ n * μ.real univ) :
    (∫⁻ x, ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ) ≤ 7 * μ univ := by
  classical
  let S := fun n : ℕ => {x | (n : ℝ) * H < f x}
  let F := fun n : ℕ => (S n).indicator (fun _ => (3 / 2 : ℝ≥0∞) ^ (n + 1))
  have hSm (n : ℕ) : MeasurableSet (S n) := measurableSet_lt measurable_const hf
  have hFm (n : ℕ) : Measurable (F n) := measurable_const.indicator (hSm n)
  have hpoint (x : X) : ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ≤ 1 + ∑' n, F n x := by
    by_cases hx : f x = 0
    · simp [hx]
    · have hfx : 0 < f x := lt_of_le_of_ne (hf0 x) (Ne.symm hx)
      have hk : 0 < ⌈f x / H⌉₊ := Nat.ceil_pos.mpr (div_pos hfx hH)
      let n := ⌈f x / H⌉₊ - 1
      have hn : n + 1 = ⌈f x / H⌉₊ := by dsimp [n]; omega
      have hns : x ∈ S n := by
        apply (lt_div_iff₀ hH).mp
        apply Nat.lt_ceil.mp
        dsimp [n]
        omega
      have hr : (3 / 2 : ℝ) ^ (f x / H) ≤ (3 / 2 : ℝ) ^ (n + 1) := by
        rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [hn]
        exact Nat.le_ceil _
      have hterm : ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ≤ F n x := by
        dsimp only [F]
        rw [indicator_of_mem hns]
        have h := ENNReal.ofReal_le_ofReal hr
        simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 2),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_ofNat] using h
      have hsum : F n x ≤ ∑' j, F j x := ENNReal.le_tsum (f := fun j => F j x) n
      exact hterm.trans (hsum.trans le_add_self)
  have ht (n : ℕ) : μ (S n) ≤ (1 / 2 : ℝ≥0∞) ^ n * μ univ := by
    have h := ENNReal.ofReal_le_ofReal (htail n)
    rw [ofReal_measureReal, ENNReal.ofReal_mul (pow_nonneg (by norm_num) _),
      ofReal_measureReal] at h
    norm_num only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat] at h
    exact h
  calc
    _ ≤ ∫⁻ x, 1 + ∑' n, F n x ∂μ := lintegral_mono hpoint
    _ = μ univ + ∑' n, ∫⁻ x, F n x ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
        lintegral_tsum (fun n => (hFm n).aemeasurable)]
    _ = μ univ + ∑' n, (3 / 2 : ℝ≥0∞) ^ (n + 1) * μ (S n) := by
      congr 1
      apply tsum_congr
      intro n
      exact lintegral_indicator_const (hSm n) _
    _ ≤ μ univ + ∑' n, (3 / 2 : ℝ≥0∞) ^ (n + 1) * ((1 / 2 : ℝ≥0∞) ^ n * μ univ) := by
      gcongr with n
      exact ht n
    _ = μ univ + (3 / 2 : ℝ≥0∞) * (∑' n : ℕ, (3 / 4 : ℝ≥0∞) ^ n) * μ univ := by
      rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro n
      rw [pow_succ]
      have hp : (3 / 4 : ℝ≥0∞) ^ n = (3 / 2 : ℝ≥0∞) ^ n * (1 / 2 : ℝ≥0∞) ^ n := by
        rw [← mul_pow]
        congr 1
        have hnn : (3 / 4 : ℝ≥0) = (3 / 2 : ℝ≥0) * (1 / 2 : ℝ≥0) := by norm_num
        have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hnn
        simpa only [ENNReal.coe_mul, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
          ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
          ENNReal.coe_one] using hc
      rw [hp]
      ring
    _ = 7 * μ univ := by
      rw [ENNReal.tsum_geometric]
      have hc : (3 / 2 : ℝ≥0∞) * (1 - 3 / 4)⁻¹ = 6 := by
        have hquarter : (1 - 3 / 4 : ℝ≥0) = 1 / 4 := by
          apply NNReal.eq
          rw [NNReal.coe_sub (by exact_mod_cast (show (3 / 4 : ℝ) ≤ 1 by norm_num))]
          norm_num
        have hne : (1 - 3 / 4 : ℝ≥0) ≠ 0 := by rw [hquarter]; norm_num
        have hnn : (3 / 2 : ℝ≥0) * (1 - 3 / 4)⁻¹ = 6 := by rw [hquarter]; norm_num
        have hc := congrArg (fun z : ℝ≥0 => (z : ℝ≥0∞)) hnn
        simpa only [ENNReal.coe_mul, ENNReal.coe_inv hne,
          ENNReal.coe_sub, ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
          ENNReal.coe_div (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat,
          ENNReal.coe_one] using hc
      calc
        _ = (1 + (3 / 2 : ℝ≥0∞) * (1 - 3 / 4)⁻¹) * μ univ := by ring
        _ = _ := by rw [hc]; norm_num

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_GeometricTailMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-power moment bounds from the geometric distribution estimate. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem geometric_tail_rpow_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) {H : ℝ} (hH : 0 < H)
    (htail : ∀ n : ℕ, μ.real {x | (n : ℝ) * H < f x} ≤
      (1 / 2 : ℝ) ^ n * μ.real univ) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) ≤
      7 * ENNReal.ofReal ((p * H / Real.log (3 / 2)) ^ p) * μ univ := by
  let t : ℝ := Real.log (3 / 2) / H
  have hlog : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have ht : 0 < t := div_pos hlog hH
  have hcoef : p / t = p * H / Real.log (3 / 2) := by
    dsimp [t]
    field_simp
  let K : ℝ := (p * H / Real.log (3 / 2)) ^ p
  have hK : 0 ≤ K := Real.rpow_nonneg (by positivity) _
  have hpoint (x : X) : f x ^ p ≤ K * ((3 / 2 : ℝ) ^ (f x / H)) := by
    have h := ProbabilityTheory.rpow_abs_le_mul_exp_abs (f x) hp ht.ne'
    rw [abs_of_pos ht, abs_of_nonneg (hf0 x), hcoef] at h
    have hexp : Real.exp (t * f x) = (3 / 2 : ℝ) ^ (f x / H) := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 1
      dsimp [t]
      ring
    simpa only [hexp, K] using h
  have hpoint' (x : X) : ENNReal.ofReal (f x ^ p) ≤
      ENNReal.ofReal K * ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) := by
    simpa only [ENNReal.ofReal_mul hK] using ENNReal.ofReal_le_ofReal (hpoint x)
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal K * ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ :=
      lintegral_mono hpoint'
    _ = ENNReal.ofReal K * ∫⁻ x, ENNReal.ofReal ((3 / 2 : ℝ) ^ (f x / H)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * (7 * μ univ) :=
      mul_le_mul_right (geometric_tail_exponential μ f hf hf0 hH htail) _
    _ = _ := by dsimp [K]; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ContinuousBMOMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-power John--Nirenberg moments on an actual interval. -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_mean_oscillation_moment (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hm : Measurable f) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A : ℝ} (hA : 0 < A)
    (hBMO : g.HasFullMeanOscillationBound f A) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ENNReal.ofReal (|f x - integralAverage g.lineMeasure f| ^ p) ∂g.lineMeasure) ≤
      7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) *
        g.lineMeasure univ := by
  have hmeas : Measurable (fun x => |f x - integralAverage g.lineMeasure f|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hm.sub measurable_const).norm
  apply geometric_tail_rpow_moment g.lineMeasure _ hmeas (fun _ => abs_nonneg _)
    (mul_pos (by positivity) hA) _ hp
  intro n
  simpa only [mul_assoc] using g.continuous_mean_oscillation_tail hb f hf hc hA hBMO n

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_VariationPacketL1
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variation of packet partial sums is bounded by the sum of packet
norms. This is used for the long-scale spatial oscillation and error terms. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem monotone_partition_crossing_unique {N j : ℕ}
    (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p)
    {i k : Fin N} (hi : (p i.castSucc).val ≤ j ∧ j < (p i.succ).val)
    (hk : (p k.castSucc).val ≤ j ∧ j < (p k.succ).val) : i = k := by
  rcases lt_trichotomy i k with hik | hik | hik
  · have h := hp (show i.succ ≤ k.castSucc by
      simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
        (Nat.succ_le_of_lt (show i.val < k.val from hik)))
    have h' : (p i.succ).val ≤ (p k.castSucc).val := h
    omega
  · exact hik
  · have h := hp (show k.succ ≤ i.castSucc by
      simpa only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] using
        (Nat.succ_le_of_lt (show k.val < i.val from hik)))
    have h' : (p k.succ).val ≤ (p i.castSucc).val := h
    omega

theorem partition_single_step_cube_le {E : Type*} [NormedAddCommGroup E]
    (v : E) (j N : ℕ) (p : Fin (N + 1) → Fin (N + 1)) (hp : Monotone p) :
    (∑ i : Fin N, ‖(if j < (p i.succ).val then v else 0) -
      (if j < (p i.castSucc).val then v else 0)‖ ^ 3) ≤ ‖v‖ ^ 3 := by
  classical
  have hterm (i : Fin N) : ‖(if j < (p i.succ).val then v else 0) -
      (if j < (p i.castSucc).val then v else 0)‖ ^ 3 =
      if (p i.castSucc).val ≤ j ∧ j < (p i.succ).val then ‖v‖ ^ 3 else 0 := by
    have hle : (p i.castSucc).val ≤ (p i.succ).val := hp (Fin.castSucc_le_succ i)
    by_cases hlow : j < (p i.castSucc).val
    · have hhigh : j < (p i.succ).val := hlow.trans_le hle
      simp [hlow, hhigh, Nat.not_le.mpr hlow]
    · by_cases hhigh : j < (p i.succ).val
      · simp [hlow, hhigh, Nat.le_of_not_gt hlow]
      · simp [hlow, hhigh]
  simp_rw [hterm]
  by_cases hex : ∃ i : Fin N, (p i.castSucc).val ≤ j ∧ j < (p i.succ).val
  · obtain ⟨k,hk⟩ := hex
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro i _ hik
      have hi : ¬ ((p i.castSucc).val ≤ j ∧ j < (p i.succ).val) :=
        fun hi => hik (monotone_partition_crossing_unique p hp hi hk)
      simp [hi]
    · simp
  · have hz (i : Fin N) : ¬ ((p i.castSucc).val ≤ j ∧ j < (p i.succ).val) :=
      fun hi => hex ⟨i,hi⟩
    simp only [hz, ite_false, if_false, Finset.sum_const_zero]
    positivity

theorem cubicVariation_single_step_le {E : Type*} [NormedAddCommGroup E]
    (v : E) (j N : ℕ) : cubicVariation (fun n => if j < n then v else 0) N ≤ ‖v‖ := by
  classical
  have hcube : finiteCubicVariation (fun n => if j < n then v else 0) N ≤ ‖v‖ ^ 3 := by
    apply Finset.sup'_le
    intro p _
    split_ifs with hp
    · exact partition_single_step_cube_le v j N p hp
    · positivity
  have h := Real.rpow_le_rpow (finiteCubicVariation_nonneg _ _) hcube (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hpow : (‖v‖ ^ 3) ^ (1 / 3 : ℝ) = ‖v‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg v)]
    norm_num
  simpa only [cubicVariation, hpow] using h

theorem cubicVariation_packetPartialSum_le {E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (f : Fin N → E) : cubicVariation (packetPartialSum f) N ≤ ∑ j, ‖f j‖ := by
  change cubicVariation (fun n => ∑ j : Fin N, if j.val < n then f j else 0) N ≤ _
  exact (cubicVariation_finset_sum (fun (j : Fin N) (n : ℕ) => if j.val < n then f j else 0) Finset.univ N).trans
    (Finset.sum_le_sum (fun j _ => cubicVariation_single_step_le (f j) j.val N))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_LongScaleVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial oscillation of the long-scale partial-sum variation, obtained
from the actual packet derivatives and their geometric scale sum. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

theorem packetPartialSum_sub {E : Type*} [AddCommGroup E] {N : ℕ}
    (f g : Fin N → E) (n : ℕ) :
    packetPartialSum f n - packetPartialSum g n = packetPartialSum (fun j => f j - g j) n := by
  unfold packetPartialSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n <;> simp only [hj, ite_true, if_true, ite_false, if_false, sub_zero]

theorem long_scale_variation_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} (f : Fin N → ℝ → E) (a b : ℝ) (D : Fin N → ℝ)
    (hf : ∀ j x, x ∈ Icc a b → DifferentiableAt ℝ (f j) x)
    (hderiv : ∀ j x, x ∈ Icc a b → ‖deriv (f j) x‖ ≤ D j)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    cubicVariation (fun n => packetPartialSum (fun j => f j x) n -
      packetPartialSum (fun j => f j y) n) N ≤ (∑ j, D j) * |x - y| := by
  simp_rw [packetPartialSum_sub]
  calc
    _ ≤ ∑ j, ‖f j x - f j y‖ := cubicVariation_packetPartialSum_le _
    _ ≤ ∑ j, D j * |x - y| := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Real.norm_eq_abs] using
        (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le (hf j) (hderiv j) hy hx
    _ = _ := (Finset.sum_mul _ _ _).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VerticalMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer horizontal moments through vertical averaging. In applications
the first measure is a fixed expanded vertical interval and the second is
the horizontal line interval. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem lintegral_ofReal_average_swap {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [SFinite μ] [SFinite ν]
    (F : Ω × Ξ → ℝ) (hF : Measurable F)
    (hi : ∀ x, Integrable (fun t => F (t,x)) μ)
    (h0 : ∀ z, 0 ≤ F z) :
    (∫⁻ x, ENNReal.ofReal (⨍ t, F (t,x) ∂μ) ∂ν) =
      (μ Set.univ)⁻¹ * ∫⁻ t, ∫⁻ x, ENNReal.ofReal (F (t,x)) ∂ν ∂μ := by
  simp_rw [ofReal_average (hi _) (Filter.Eventually.of_forall fun t => h0 (t,_)),
    ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul _ (hF.ennreal_ofReal.lintegral_prod_left)]
  congr 1
  exact (lintegral_lintegral_swap hF.ennreal_ofReal.aemeasurable).symm

theorem verticalSquareEnergy_measurable {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [SFinite μ] (V D : Ω × Ξ → ℝ)
    (hV : Measurable V) (hD : Measurable D) :
    Measurable (fun x => verticalSquareEnergy μ (fun t => V (t,x)) (fun t => D (t,x))) := by
  have h : Measurable (fun x => ∫ t, V (t,x)^2 + D (t,x)^2 ∂μ) :=
    ((hV.pow_const 2).add (hD.pow_const 2)).stronglyMeasurable.integral_prod_left'.measurable
  simpa only [verticalSquareEnergy, average_eq, smul_eq_mul] using
    (h.const_mul (μ.real univ)⁻¹).const_mul 2

theorem verticalSquareEnergy_line_moment {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure μ] [NeZero μ] [SFinite ν]
    (V D : Ω × Ξ → ℝ) (hV : Measurable V) (hD : Measurable D) (n : ℕ)
    (hiV : ∀ x, Integrable (fun t => V (t,x)^2) μ)
    (hiD : ∀ x, Integrable (fun t => D (t,x)^2) μ)
    (hi : ∀ x, Integrable (fun t => (V (t,x)^2+D (t,x)^2)^n) μ)
    (hiVn : ∀ x, Integrable (fun t => V (t,x)^(2*n)) μ)
    (hiDn : ∀ x, Integrable (fun t => D (t,x)^(2*n)) μ)
    (C : ℝ≥0∞)
    (hline : ∀ t, (∫⁻ x, ENNReal.ofReal (V (t,x)^(2*n)+D (t,x)^(2*n)) ∂ν) ≤ C) :
    (∫⁻ x, ENNReal.ofReal
      (verticalSquareEnergy μ (fun t => V (t,x)) (fun t => D (t,x)))^n ∂ν) ≤
      (4:ℝ≥0∞)^n * C := by
  have hp (x : Ξ) := averaged_square_moment μ (fun t => V (t,x))
    (fun t => D (t,x)) n (hiV x) (hiD x) (hi x) (hiVn x) (hiDn x)
  have hnonneg (x : Ξ) : 0 ≤ verticalSquareEnergy μ (fun t => V (t,x))
      (fun t => D (t,x)) := by
    apply mul_nonneg (by norm_num)
    exact integral_nonneg (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hpow (x : Ξ) : ENNReal.ofReal
      (verticalSquareEnergy μ (fun t => V (t,x)) (fun t => D (t,x)))^n ≤
      (4:ℝ≥0∞)^n * ENNReal.ofReal (⨍ t, V (t,x)^(2*n)+D (t,x)^(2*n) ∂μ) := by
    have hfour : ENNReal.ofReal (4:ℝ) = 4 := by norm_num
    rw [← ENNReal.ofReal_pow (hnonneg x), ← hfour, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4^n)]
    exact ENNReal.ofReal_le_ofReal (hp x)
  calc
    _ ≤ ∫⁻ x, (4:ℝ≥0∞)^n * ENNReal.ofReal
        (⨍ t, V (t,x)^(2*n)+D (t,x)^(2*n) ∂μ) ∂ν := lintegral_mono hpow
    _ = (4:ℝ≥0∞)^n * ((μ univ)⁻¹ *
        ∫⁻ t, ∫⁻ x, ENNReal.ofReal (V (t,x)^(2*n)+D (t,x)^(2*n)) ∂ν ∂μ) := by
      rw [lintegral_const_mul' _ _ (by finiteness)]
      congr 1
      apply lintegral_ofReal_average_swap μ ν (fun z => V z^(2*n)+D z^(2*n))
        ((hV.pow_const (2*n)).add (hD.pow_const (2*n))) (fun x => (hiVn x).add (hiDn x))
      intro z
      simpa only [pow_mul] using
        add_nonneg (pow_nonneg (sq_nonneg (V z)) n) (pow_nonneg (sq_nonneg (D z)) n)
    _ ≤ (4:ℝ≥0∞)^n * ((μ univ)⁻¹ * ∫⁻ _t, C ∂μ) := by
      gcongr
      exact hline _
    _ = _ := by
      rw [lintegral_const, mul_comm C (μ univ), ← mul_assoc (μ univ)⁻¹,
        ENNReal.inv_mul_cancel (NeZero.ne (μ univ))
          (measure_ne_top μ univ), one_mul]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NeighborhoodEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single measurable energy can control every member of a finite family
of interval sums throughout a vertical neighborhood. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem interval_energy_domination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) {a b : ℝ} (hab : a < b)
    (hf : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hd : MemLp (deriv f) 2 (volume.restrict (Icc a b)))
    (V D : ℝ → ℝ) (hV : ContinuousOn V (Icc a b)) (hD : ContinuousOn D (Icc a b))
    (hbV : ∀ t ∈ Icc a b, ‖f t‖ ≤ V t)
    (hbD : ∀ t ∈ Icc a b, ‖deriv f t‖ ≤ D t)
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x‖^2 ≤ verticalSquareEnergy (volume.restrict (Icc a b)) V
      (fun t => (b-a)*D t) := by
  have hm : 0 < b-a := sub_pos.mpr hab
  have hcont : ContinuousOn f (Icc a b) := fun t ht =>
    (hf t ht).continuousAt.continuousWithinAt
  have hiV : IntegrableOn (fun t => V t^2) (Icc a b) volume := (hV.pow 2).integrableOn_Icc
  have hiD : IntegrableOn (fun t => D t^2) (Icc a b) volume := (hD.pow 2).integrableOn_Icc
  have hvi : (∫ t in Icc a b, ‖f t‖^2) ≤ ∫ t in Icc a b, V t^2 := by
    apply integral_mono_ae (hcont.norm.pow 2).integrableOn_Icc hiV
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_le_pow_left₀ (norm_nonneg _) (hbV t ht) 2
  have hdi : (∫ t in Icc a b, ‖deriv f t‖^2) ≤ ∫ t in Icc a b, D t^2 := by
    apply integral_mono_ae (hd.integrable_norm_pow (by decide)) hiD
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_le_pow_left₀ (norm_nonneg _) (hbD t ht) 2
  have h := (interval_pointwise_square f hab hf hd hx).trans
    (add_le_add (mul_le_mul_of_nonneg_left hvi (by positivity))
      (mul_le_mul_of_nonneg_left hdi (by positivity)))
  have hmass : (volume.restrict (Icc a b)).real univ = b-a := by
    rw [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal hm.le]
  change ‖f x‖^2 ≤ 2 * (⨍ t in Icc a b, V t^2+((b-a)*D t)^2)
  rw [average_eq, hmass, smul_eq_mul]
  simp only [mul_pow]
  rw [integral_add hiV (hiD.const_mul _), integral_const_mul]
  have heq : 2 * ((b-a)⁻¹ * ((∫ t in Icc a b, V t^2) +
      (b-a)^2 * (∫ t in Icc a b, D t^2))) =
      (2/(b-a)) * (∫ t in Icc a b, V t^2) +
      2*(b-a)*(∫ t in Icc a b, D t^2) := by field_simp [hm.ne']
  rwa [heq]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NeighborhoodExceptional
attribute [-instance] _root_.OAI.LipschitzHilbert.FiniteLineGrid.cellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A measurable exceptional set for a common neighborhood majorant.
The moment order is an integer, so even orders may grow with the manuscript
parameter without changing any packet regularity order. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem interval_vertical_moment (ν : Measure ℝ) [SFinite ν]
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    {a b : ℝ} (hab : a < b) (n : ℕ) (C : ℝ≥0∞)
    (hline : ∀ t, (∫⁻ x, ENNReal.ofReal (V (t,x)^(2*n)+D (t,x)^(2*n)) ∂ν) ≤ C) :
    (∫⁻ x, ENNReal.ofReal (verticalSquareEnergy (volume.restrict (Icc a b))
      (fun t => V (t,x)) (fun t => D (t,x)))^n ∂ν) ≤ (4:ℝ≥0∞)^n*C := by
  let μ := volume.restrict (Icc a b)
  have hm : μ univ ≠ 0 := by
    dsimp [μ]
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  let : NeZero μ := ⟨fun h => hm (by rw [h]; simp)⟩
  have hcV (x : ℝ) : Continuous (fun t => V (t,x)) := hV.comp (continuous_id.prodMk continuous_const)
  have hcD (x : ℝ) : Continuous (fun t => D (t,x)) := hD.comp (continuous_id.prodMk continuous_const)
  exact verticalSquareEnergy_line_moment μ ν V D hV.measurable hD.measurable n
    (fun x => ((hcV x).pow 2).continuousOn.integrableOn_Icc)
    (fun x => ((hcD x).pow 2).continuousOn.integrableOn_Icc)
    (fun x => (((hcV x).pow 2).add ((hcD x).pow 2)).pow n |>.continuousOn.integrableOn_Icc)
    (fun x => ((hcV x).pow (2*n)).continuousOn.integrableOn_Icc)
    (fun x => ((hcD x).pow (2*n)).continuousOn.integrableOn_Icc) C hline

theorem energy_superlevel_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Ω → ℝ) (hE : Measurable E)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) (n : ℕ) (C : ℝ≥0∞)
    (hmoment : (∫⁻ x, ENNReal.ofReal (E x)^n ∂μ) ≤ C) :
    (ENNReal.ofReal threshold)^(2*n) * μ {x | threshold^2 ≤ E x} ≤ C := by
  have hsub : {x | threshold^2 ≤ E x} ⊆
      {x | (ENNReal.ofReal threshold)^(2*n) ≤ ENNReal.ofReal (E x)^n} := by
    intro x hx
    change (ENNReal.ofReal threshold)^(2*n) ≤ ENNReal.ofReal (E x)^n
    have h := pow_le_pow_left' (ENNReal.ofReal_le_ofReal hx) n
    simpa only [ENNReal.ofReal_pow hthreshold, pow_mul] using h
  exact (mul_le_mul' le_rfl (measure_mono hsub)).trans
    ((mul_meas_ge_le_lintegral (hE.ennreal_ofReal.pow_const n) _).trans hmoment)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_RawBMOMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uncentered interval moments from the proved John--Nirenberg estimate
and a bound for the interval mean. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_raw_moment (g : FiniteLineGrid) (hb : 1 < g.branching)
    (f : ℝ → ℝ) (hm : Measurable f) (hf : Integrable f g.lineMeasure)
    (hc : ∀ x ∈ g.root, ContinuousAt f x) {A B p : ℝ}
    (hA : 0 < A) (hBMO : g.HasFullMeanOscillationBound f A)
    (hmean : |integralAverage g.lineMeasure f| ≤ B) (hp : 0 ≤ p) :
    (∫⁻ x, (ENNReal.ofReal |f x|) ^ p ∂g.lineMeasure) ≤
      (2 : ℝ≥0∞) ^ p *
        (7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) +
          (ENNReal.ofReal B) ^ p) * g.lineMeasure univ := by
  let m := integralAverage g.lineMeasure f
  have hcenter := g.continuous_mean_oscillation_moment hb f hm hf hc hA hBMO hp
  have hpoint (x : ℝ) : (ENNReal.ofReal |f x|) ^ p ≤
      (2 : ℝ≥0∞) ^ p * ((ENNReal.ofReal |f x - m|) ^ p + (ENNReal.ofReal B) ^ p) := by
    have habs : |f x| ≤ |f x - m| + B := by
      have ha := norm_add_le (f x - m) m
      simp only [Real.norm_eq_abs] at ha
      rw [sub_add_cancel] at ha
      exact ha.trans (add_le_add le_rfl hmean)
    have hB : 0 ≤ B := (abs_nonneg m).trans hmean
    have h0 : ENNReal.ofReal |f x| ≤ ENNReal.ofReal |f x - m| + ENNReal.ofReal B := by
      rw [← ENNReal.ofReal_add (abs_nonneg _) hB]
      exact ENNReal.ofReal_le_ofReal habs
    exact (ENNReal.rpow_le_rpow h0 hp).trans
      (ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp)
  have hmcenter : Measurable (fun x => (ENNReal.ofReal |f x - m|) ^ p) := by
    apply Measurable.pow_const
    apply Measurable.ennreal_ofReal
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hm.sub measurable_const).norm
  have heq : (fun x => (ENNReal.ofReal |f x - m|) ^ p) =
      (fun x => ENNReal.ofReal (|f x - m| ^ p)) := by
    funext x
    exact ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp
  calc
    _ ≤ ∫⁻ x, (2 : ℝ≥0∞) ^ p * ((ENNReal.ofReal |f x - m|) ^ p +
          (ENNReal.ofReal B) ^ p) ∂g.lineMeasure := lintegral_mono hpoint
    _ = (2 : ℝ≥0∞) ^ p * ((∫⁻ x, ENNReal.ofReal (|f x - m| ^ p) ∂g.lineMeasure) +
          (ENNReal.ofReal B) ^ p * g.lineMeasure univ) := by
      rw [lintegral_const_mul (f := fun x => (ENNReal.ofReal |f x - m|) ^ p +
          (ENNReal.ofReal B) ^ p) _ (hmcenter.add measurable_const),
        lintegral_add_left hmcenter, lintegral_const, heq]
    _ ≤ _ := by
      calc
        _ ≤ (2 : ℝ≥0∞) ^ p *
            (7 * ENNReal.ofReal ((p * (((g.branching : ℝ) + 2) * A) / Real.log (3 / 2)) ^ p) *
              g.lineMeasure univ + (ENNReal.ofReal B) ^ p * g.lineMeasure univ) := by
          gcongr
        _ = _ := by ring

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_HilbertPacketSums
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Hilbert packet sums are continuous and agree with the generic
partial sums used for spatial oscillation estimates. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem partialBandSum_continuous {N : ℕ} (f : Fin N → SchwartzMap ℝ ℂ) (n : ℕ) :
    Continuous (partialBandSum f n) := by
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using (f j).continuous
  · simpa only [ite_eq_right hj] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))

theorem hilbertPartialBandSum_continuous {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (n : ℕ) :
    Continuous (hilbertPartialBandSum f n) := by
  exact (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
    (continuous_pi (fun k => partialBandSum_continuous (fun j => f j k) n))

theorem hilbertPartialBandSum_eq_packetPartialSum {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    hilbertPartialBandSum f n x =
      packetPartialSum (fun j => WithLp.toLp 2 (fun k => f j k x)) n := by
  ext k
  change (∑ j : Fin N, if j.val < n then f j k x else 0) = _
  simp only [packetPartialSum, WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketVectorDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dimension-free synthesis and derivative estimates on a reference line.
The multiplication of a Hilbert coefficient by a packet is componentwise. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem vectorPacketSynthesis_hasDerivAt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (vectorPacketSynthesis c f)
      (WithLp.toLp 2 (fun k => ∑ i, c i k * deriv (f i k) x)) x := by
  have hd : HasDerivAt (fun x k => packetSynthesis (fun i => c i k) (fun i => f i k) x)
      (fun k => ∑ i, c i k * deriv (f i k) x) x := by
    apply hasDerivAt_pi.mpr
    intro k
    simp only [packetSynthesis_apply]
    have heq : (fun x => ∑ i, c i k * f i k x) = ∑ i, (fun x => c i k * f i k x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq]
    exact HasDerivAt.sum (u := Finset.univ)
      (fun i _ => ((f i k).differentiable x).hasDerivAt.const_mul (c i k))
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hd

theorem vectorPacketSynthesis_deriv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (vectorPacketSynthesis c f) x =
      ∑ i, WithLp.toLp 2 (fun k => c i k * deriv (f i k) x) := by
  rw [(vectorPacketSynthesis_hasDerivAt c f x).deriv]
  ext k
  simp only [WithLp.ofLp_sum, Finset.sum_apply]

theorem vectorPacketSynthesis_deriv_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (w : ι → ℝ) {C D : ℝ} (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i)
    (hc : ∀ i, ‖c i‖ ≤ 1) (hover : ∑ i, w i ≤ D) (x : ℝ)
    (hf : ∀ i k, ‖deriv (f i k) x‖ ≤ C * w i) :
    ‖deriv (vectorPacketSynthesis c f) x‖ ≤ C * D := by
  rw [vectorPacketSynthesis_deriv]
  calc
    _ ≤ ∑ i, ‖WithLp.toLp 2 (fun k => c i k * deriv (f i k) x)‖ := norm_sum_le _ _
    _ ≤ ∑ i, C * w i := by
      apply Finset.sum_le_sum
      intro i _
      exact (diagonal_packet_norm (c i) _ (mul_nonneg hC (hw i)) (hf i)).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (hc i) (mul_nonneg hC (hw i)))
    _ ≤ C * D := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hover hC

theorem tile_vectorPacketSynthesis_deriv_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (f : ι → κ → SchwartzMap ℝ ℂ)
    (index : ι → ℤ × ℤ) (hinj : Function.Injective index)
    (a b l W x y C : ℝ) (hl : 0 < l) (hW : W ≠ 0) (hC : 0 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ 1)
    (hf : ∀ i k, ‖deriv (f i k) x‖ ≤ (C / l) *
      (lineEnvelope (a + l * (index i).1) l 3 x *
        lineEnvelope (b + W * (index i).2) W 2 y)) :
    ‖deriv (vectorPacketSynthesis c f) x‖ ≤ (C / l) * (4 * Real.pi) ^ 2 := by
  exact vectorPacketSynthesis_deriv_bound c f _ (div_nonneg hC hl.le)
    (fun i => mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)) hc
    (injective_tile_lattice_overlap index hinj a b l W x y hl.ne' hW (by decide) (by decide)) x hf

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_LongLineVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Long-scale oscillation for actual Hilbert packet synthesis. -/

noncomputable section
open Set
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem long_line_variation {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (site : ∀ j, ι j → ℤ × ℤ) (hinj : ∀ j, Function.Injective (site j))
    (a b L W y u r C : ℝ) (hL : 0 < L) (hW : W ≠ 0) (hr : 0 < r) (hC : 0 ≤ C)
    (hc : ∀ j i, ‖c j i‖ ≤ 1)
    (hderiv : ∀ j i k x, ‖deriv (f j i k) x‖ ≤ (C / (L / (2 : ℝ) ^ j.val)) *
      (lineEnvelope (a + (L / (2 : ℝ) ^ j.val) * (site j i).1)
        (L / (2 : ℝ) ^ j.val) 3 x *
        lineEnvelope (b + W * (site j i).2) W 2 y))
    {x z : ℝ} (hx : x ∈ Icc (u - r) (u + r)) (hz : z ∈ Icc (u - r) (u + r)) :
    cubicVariation (fun n =>
      hilbertPartialBandSum (fun j k => if r < L / (2 : ℝ) ^ j.val then
        packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n x -
      hilbertPartialBandSum (fun j k => if r < L / (2 : ℝ) ^ j.val then
        packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n z) N ≤
      4 * (C * (4 * Real.pi) ^ 2) := by
  let len := fun j : Fin N => L / (2 : ℝ) ^ j.val
  let F := fun (j : Fin N) x => if r < len j then vectorPacketSynthesis (c j) (f j) x else 0
  let D := fun j : Fin N => if r < len j then (C / len j) * (4 * Real.pi) ^ 2 else 0
  have hlen (j : Fin N) : 0 < len j := div_pos hL (pow_pos (by norm_num) _)
  have hF (j : Fin N) (x : ℝ) : DifferentiableAt ℝ (F j) x := by
    by_cases hj : r < len j
    · simpa only [F, ite_eq_left hj] using (vectorPacketSynthesis_hasDerivAt (c j) (f j) x).differentiableAt
    · simpa only [F, ite_eq_right hj] using (hasDerivAt_const x (0 : EuclideanSpace ℂ κ)).differentiableAt
  have hd (j : Fin N) (x : ℝ) : ‖deriv (F j) x‖ ≤ D j := by
    by_cases hj : r < len j
    · simpa only [F, D, ite_eq_left hj] using
        tile_vectorPacketSynthesis_deriv_bound (c j) (f j) (site j) (hinj j)
          a b (len j) W x y C (hlen j) hW hC (hc j) (fun i k => hderiv j i k x)
    · simp only [F, D, ite_eq_right hj, deriv_const, norm_zero, le_refl]
  have hsum : (∑ j, D j) ≤ (C * (4 * Real.pi) ^ 2) * (2 / r) := by
    have heq (j : Fin N) : D j = (C * (4 * Real.pi) ^ 2) *
        (if r < len j then (len j)⁻¹ else 0) := by
      by_cases hj : r < len j <;> simp only [D, hj, ite_true, if_true, ite_false, if_false, mul_zero]
      rw [div_eq_mul_inv]
      ring
    simp_rw [heq]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (sum_long_dyadic_reciprocals N L r hL hr) (by positivity)
  have heq (n : ℕ) (v : ℝ) :
      hilbertPartialBandSum (fun j k => if r < len j then
        packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n v =
        packetPartialSum (fun j => F j v) n := by
    rw [hilbertPartialBandSum_eq_packetPartialSum]
    congr 1
    funext j
    by_cases hj : r < len j
    · simp only [F, ite_eq_left hj, vectorPacketSynthesis]
    · simp only [F, ite_eq_right hj]
      rfl
  change cubicVariation (fun n =>
    hilbertPartialBandSum (fun j k => if r < len j then
      packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n x -
    hilbertPartialBandSum (fun j k => if r < len j then
      packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n z) N ≤ _
  simp_rw [heq]
  have hdist : |x - z| ≤ 2 * r :=
    abs_le.mpr ⟨by linarith [hx.1,hz.2], by linarith [hx.2,hz.1]⟩
  calc
    _ ≤ (∑ j, D j) * |x - z| :=
      long_scale_variation_lipschitz F _ _ D (fun j x _ => hF j x) (fun j x _ => hd j x) hx hz
    _ ≤ ((C * (4 * Real.pi) ^ 2) * (2 / r)) * (2 * r) :=
      mul_le_mul hsum hdist (abs_nonneg _) (by positivity)
    _ = _ := by field_simp; ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_BoxPacketVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Short-scale Hilbert packet variation from the explicit coefficient
budget and packet envelopes, retaining the horizontal and transverse
decay of one center box. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

theorem box_packet_variation (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → κ → Type)
      [Fintype κ] [∀ j k, Fintype (ι j k)]
      (c : ∀ j k, ι j k → ℂ) (f : ∀ j k, ι j k → SchwartzMap ℝ ℂ)
      (s rho : ∀ j k, ι j k → ℝ) (len : Fin N → ℝ)
      (u r offset C D T B : ℝ) (q : ℕ),
      (∀ j, 0 < len j) → 0 < r → (∀ j k, ∀ _ : ι j k, len j ≤ r) →
      (∀ j k i, 0 < rho j k i) → (∀ j k i, rho j k i ≤ T) →
      (∀ j k i, |s j k i - (u + r * offset)| ≤ r) → 0 ≤ D → 0 ≤ T →
      (∀ j k x, ∑ i, rho j k i * lineEnvelope (s j k i) (len j) (1 + 2 * q) x ≤ D) →
      (∀ j k i x, ‖f j k i x‖ ≤ C *
        (rho j k i * lineEnvelope (s j k i) (len j) (1 + 2 * q) x)) →
      (∑ j, len j * ∑ k, ∑ i, ‖c j k i‖ ^ 2 ≤ B * r) →
      (∀ j k i ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (f j k i) ξ = 0) →
      (∀ j k i ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j k i) ξ = 0) →
      ENNReal.ofReal ((((1 + |offset|) ^ 2 / 8) ^ q) ^ 2) *
        (∫⁻ x in Icc (u - r) (u + r), ENNReal.ofReal (finiteCubicVariation
          (fun n => hilbertPartialBandSum
            (fun j k => packetSynthesis (c j k) (f j k)) n x) N) ^ (2 / 3 : ℝ)) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal (D * C ^ 2 * 16 ^ q * Real.pi * T * (B * r)) := by
  obtain ⟨K,hK,hlocal⟩ := localized_dyadic_hilbert_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ ι instκ instι c f s rho len u r offset C D T B q
    hlen hr hlenr hrho hrhoT hcenter hD hT hover henv hbudget hlow hhigh
  have hbudget' : (∑ jk : Fin N × κ, len jk.1 * ∑ i, ‖c jk.1 jk.2 i‖ ^ 2) ≤ B * r := by
    rw [Fintype.sum_prod_type]
    simpa only [← Finset.mul_sum] using hbudget
  have henergy := box_synthesis_energy
    (fun jk : Fin N × κ => c jk.1 jk.2) (fun jk => f jk.1 jk.2)
    (fun jk => s jk.1 jk.2) (fun jk => rho jk.1 jk.2) (fun jk => len jk.1)
    (u + r * offset) r C D T B q (fun jk => hlen jk.1) hr
    (fun jk => hlenr jk.1 jk.2) (fun jk => hrho jk.1 jk.2)
    (fun jk => hrhoT jk.1 jk.2) (fun jk => hcenter jk.1 jk.2) hD hT
    (fun jk => hover jk.1 jk.2) (fun jk => henv jk.1 jk.2) hbudget'
  rw [Fintype.sum_prod_type] at henergy
  have h := hlocal N κ (fun j k => packetSynthesis (c j k) (f j k))
    (u + r * offset) r q (Icc (u - r) (u + r)) (((1 + |offset|) ^ 2 / 8) ^ q)
    (fun j k ξ hξ => packetSynthesis_fourier_zero _ _ ξ (fun i => hlow j k i ξ hξ))
    (fun j k ξ hξ => packetSynthesis_fourier_zero _ _ ξ (fun i => hhigh j k i ξ hξ))
    measurableSet_Icc (box_polynomial_weight_pos offset q).le
    (fun x hx => box_polynomial_weight u r offset x q hr
      (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩))
  exact h.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal henergy) _)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual center-box assignment on a reference line and exact grouping
of the finite Schwartz synthesis. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem packetSynthesis_eq_sum_boxes_of_mem {ι : Type*} [Fintype ι]
    (index : ι → ℤ × ℤ) (c : ι → ℂ) (f : ι → SchwartzMap ℝ ℂ)
    (boxes : Finset (ℤ × ℤ)) (hboxes : ∀ i, index i ∈ boxes) :
    packetSynthesis c f = ∑ b ∈ boxes, packetBoxSynthesis index c f b := by
  classical
  unfold packetSynthesis packetBoxSynthesis
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (index i)]
  · simp
  · intro b _ hbi
    simp [Ne.symm hbi]
  · intro hi
    exact (hi (hboxes i)).elim

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ShortPacketBoxes
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite decomposition of the short-scale synthesis into its actual
center boxes. Empty fibers are retained and contribute zero. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem mem_allPacketBoxes {σ : Type*} {ι : σ → Type*} [Fintype σ] [∀ j, Fintype (ι j)]
    (index : ∀ j, ι j → ℤ × ℤ) (j : σ) (i : ι j) : index j i ∈ allPacketBoxes index :=
  Finset.mem_image.mpr ⟨⟨j,i⟩, Finset.mem_univ _, rfl⟩

theorem shortBoxSynthesis_eq {σ : Type*} {ι : σ → Type*} [∀ j, Fintype (ι j)]
    (len : σ → ℝ) (index : ∀ j, ι j → ℤ × ℤ) (r : ℝ)
    (c : ∀ j, ι j → ℂ) (f : ∀ j, ι j → SchwartzMap ℝ ℂ) (b : ℤ × ℤ) (j : σ) :
    shortBoxSynthesis len index r c f b j =
      if len j ≤ r then packetBoxSynthesis (index j) (c j) (f j) b else 0 := by
  have h := Finset.sum_subtype (Finset.univ.filter (fun i : ι j => len j ≤ r ∧ index j i = b))
    (p := fun i : ι j => len j ≤ r ∧ index j i = b) (F := inferInstance)
    (by simp) (fun i => c j i • f j i)
  rw [Finset.sum_filter] at h
  change (∑ i : ShortBoxFiber len index r b j, c j i • f j i) = _
  rw [← h]
  by_cases hj : len j ≤ r
  · simp only [hj, true_and, ite_true, if_true, packetBoxSynthesis]
  · simp [hj]

theorem shortSynthesis_eq_sum_boxes {σ : Type*} {ι : σ → Type*}
    [Fintype σ] [∀ j, Fintype (ι j)]
    (len : σ → ℝ) (index : ∀ j, ι j → ℤ × ℤ) (r : ℝ)
    (c : ∀ j, ι j → ℂ) (f : ∀ j, ι j → SchwartzMap ℝ ℂ) (j : σ) :
    (if len j ≤ r then packetSynthesis (c j) (f j) else 0) =
      ∑ b ∈ allPacketBoxes index, shortBoxSynthesis len index r c f b j := by
  simp_rw [shortBoxSynthesis_eq]
  by_cases hj : len j ≤ r
  · simp only [hj, ite_true, if_true]
    exact packetSynthesis_eq_sum_boxes_of_mem (index j) (c j) (f j) _
      (fun i => mem_allPacketBoxes index j i)
  · simp [hj]

theorem component_coefficient_energy {κ ι : Type*} [Fintype κ] [Fintype ι]
    (c : ι → EuclideanSpace ℂ κ) :
    (∑ k, ∑ i, ‖c i k‖ ^ 2) = ∑ i, ‖c i‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (EuclideanSpace.norm_sq_eq (c i)).symm

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ShortBoxEstimate
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-box estimate for the actual short-packet fibers. Lattice
overlap, box location, and transverse decay are all discharged here. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem short_box_variation (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)]
      (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
      (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ × ℤ) (len : Fin N → ℝ)
      (a0 b0 u y r W C B : ℝ) (b : ℤ × ℤ),
      (∀ j, Function.Injective (site j)) → (∀ j, 0 < len j) → 0 < r → 0 < W →
      (∀ j i, X j i = a0 + len j * (site j i).1) →
      (∀ j i, Z j i = b0 + W * (site j i).2) →
      (∀ j i k x, ‖f j i k x‖ ≤ C *
        (lineEnvelope (X j i) (len j) 3 x * lineEnvelope (Z j i) W 2 y)) →
      (∑ j, len j * ∑ i : ShortBoxFiber len (centerBoxIndex X Z u y r W) r b j,
        ‖c j i‖ ^ 2) ≤ B * r →
      (∀ j i k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (f j i k) ξ = 0) →
      (∀ j i k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j i k) ξ = 0) →
      ENNReal.ofReal (((1 + |(b.1 : ℝ)|) ^ 2 / 8) ^ 2) *
        (∫⁻ x in Icc (u - r) (u + r), ENNReal.ofReal (finiteCubicVariation
          (fun n => hilbertPartialBandSum
            (fun j k => shortBoxSynthesis len (centerBoxIndex X Z u y r W) r
              (fun j i => c j i k) (fun j i => f j i k) b j) n x) N) ^ (2 / 3 : ℝ)) ≤
        (K : ℝ≥0∞) * ENNReal.ofReal ((4 * Real.pi) ^ 2 * C ^ 2 * 16 * Real.pi *
          (((1 + |(b.2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹ * (B * r)) := by
  obtain ⟨K,hK,hbound⟩ := box_packet_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ ι instκ instι c f X Z site len a0 b0 u y r W C B b
    hinj hlen hr hW hX hZ henv hbudget hlow hhigh
  let index := centerBoxIndex X Z u y r W
  let fiber := fun j => ShortBoxFiber len index r b j
  have hcx (j : Fin N) (i : fiber j) : |X j i - (u + r * b.1)| ≤ r := by
    have h := packetBoxIndex_horizontal u y r W (X j i) (Z j i) hr
    change |X j i - (u + r * (index j i).1)| ≤ r at h
    rw [i.property.2] at h
    exact h
  have hcz (j : Fin N) (i : fiber j) : |Z j i - (y + W * b.2)| ≤ W := by
    have h := packetBoxIndex_vertical u y r W (X j i) (Z j i) hW
    change |Z j i - (y + W * (index j i).2)| ≤ W at h
    rw [i.property.2] at h
    exact h
  have hover (j : Fin N) (x : ℝ) :
      (∑ i : fiber j, lineEnvelope (Z j i) W 2 y * lineEnvelope (X j i) (len j) 3 x) ≤
        (4 * Real.pi) ^ 2 := by
    have h := injective_tile_lattice_overlap (fun i : fiber j => site j i)
      ((hinj j).comp Subtype.val_injective) a0 b0 (len j) W x y
      (hlen j).ne' hW.ne' (by norm_num : 1 ≤ (3 : ℕ)) (by norm_num : 1 ≤ (2 : ℕ))
    simpa only [hX, hZ, mul_comm] using h
  have hbudget' : (∑ j, len j * ∑ k, ∑ i : fiber j, ‖c j i k‖ ^ 2) ≤ B * r := by
    simpa only [component_coefficient_energy] using hbudget
  have h := hbound N κ (fun j _ => fiber j)
    (fun j k i => c j i k) (fun j k i => f j i k) (fun j _ i => X j i)
    (fun j _ i => lineEnvelope (Z j i) W 2 y) len u r b.1 C ((4 * Real.pi) ^ 2)
    ((((1 + |(b.2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹) B 1
    hlen hr (fun _ _ i => i.property.1)
    (fun _ _ _ => by unfold lineEnvelope; positivity)
    (fun j _ i => transverse_box_envelope (Z j i) y W b.2 2 hW (hcz j i))
    (fun j _ i => hcx j i) (by positivity) (by positivity)
    (fun j _ x => by simpa using hover j x)
    (fun j k i x => by simpa [mul_comm] using henv j i k x)
    hbudget' (fun j k i ξ hξ => hlow j i k ξ hξ) (fun j k i ξ hξ => hhigh j i k ξ hξ)
  simpa only [pow_one, shortBoxSynthesis, index, fiber] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_HilbertPacketLinearity
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact linearity of partial packet sums across a finite box decomposition. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem partialBandSum_finset_sum {B : Type*} {N : ℕ} (s : Finset B)
    (f : B → Fin N → SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    partialBandSum (fun j => ∑ b ∈ s, f b j) n x =
      ∑ b ∈ s, partialBandSum (f b) n x := by
  simp only [partialBandSum, sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n
  · simp only [hj, ite_true, if_true]
  · simp only [hj, ite_false, if_false, Finset.sum_const_zero]

theorem hilbertPartialBandSum_finset_sum {B : Type*} {N : ℕ} {κ : Type*} [Fintype κ]
    (s : Finset B) (f : B → Fin N → κ → SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) :
    hilbertPartialBandSum (fun j k => ∑ b ∈ s, f b j k) n x =
      ∑ b ∈ s, hilbertPartialBandSum (f b) n x := by
  ext k
  change partialBandSum (fun j => ∑ b ∈ s, f b j k) n x = _
  rw [partialBandSum_finset_sum]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_ShortLineVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual short-scale packet boxes on one reference interval. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

theorem short_line_variation (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)]
      (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
      (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ × ℤ) (len : Fin N → ℝ)
      (a0 b0 u y r W C B : ℝ),
      (∀ j, Function.Injective (site j)) → (∀ j, 0 < len j) → 0 < r → 0 < W → 0 ≤ B →
      (∀ j i, X j i = a0 + len j * (site j i).1) →
      (∀ j i, Z j i = b0 + W * (site j i).2) →
      (∀ j i k x, ‖f j i k x‖ ≤ C *
        (lineEnvelope (X j i) (len j) 3 x * lineEnvelope (Z j i) W 2 y)) →
      (∀ b : ℤ × ℤ, (∑ j, len j *
        ∑ i : ShortBoxFiber len (centerBoxIndex X Z u y r W) r b j, ‖c j i‖ ^ 2) ≤ B * r) →
      (∀ j i k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (f j i k) ξ = 0) →
      (∀ j i k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (f j i k) ξ = 0) →
      (∫⁻ x in Icc (u - r) (u + r), ENNReal.ofReal (finiteCubicVariation
        (fun n => hilbertPartialBandSum
          (fun j k => if len j ≤ r then packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0)
          n x) N) ^ (2 / 3 : ℝ)) ≤ ENNReal.ofReal (A * C ^ 2 * B * r) := by
  obtain ⟨K,hK,hbox⟩ := short_box_variation hL hlo hhi
  have hKr : 0 < (K : ℝ) := by exact_mod_cast hK
  let A : ℝ := (4 * Real.pi) ^ 4 * 4096 * ((K : ℝ) * (4 * Real.pi) ^ 2 * 16 * Real.pi)
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro N κ ι instκ instι c f X Z site len a0 b0 u y r W C B
    hinj hlen hr hW hB hX hZ henv hbudget hlow hhigh
  let index := centerBoxIndex X Z u y r W
  let boxes := allPacketBoxes index
  let G := fun (b : {b // b ∈ boxes}) j k =>
    shortBoxSynthesis len index r (fun j i => c j i k) (fun j i => f j i k) b j
  let F := fun (b : {b // b ∈ boxes}) n x => hilbertPartialBandSum (G b) n x
  let M : ℝ := (K : ℝ) * (4 * Real.pi) ^ 2 * C ^ 2 * 16 * Real.pi * (B * r)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hF (b : {b // b ∈ boxes}) (n : ℕ) : Measurable (F b n) :=
    (hilbertPartialBandSum_continuous (G b) n).measurable
  have hbox' (b : {b // b ∈ boxes}) :
      ENNReal.ofReal (((1 + |(b.val.1 : ℝ)|) ^ 2 / 8) ^ 2) *
        (∫⁻ x in Icc (u - r) (u + r), ENNReal.ofReal
          (finiteCubicVariation (fun n => F b n x) N) ^ (2 / 3 : ℝ)) ≤
        ENNReal.ofReal (M * (((1 + |(b.val.2 : ℝ)|) ^ 2 / 8) ^ 2)⁻¹) := by
    have h := hbox N κ ι c f X Z site len a0 b0 u y r W C B b
      hinj hlen hr hW hX hZ henv (hbudget b) hlow hhigh
    apply h.trans_eq
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg]
    congr 1
    dsimp [M]
    ring
  have hsum (n : ℕ) (x : ℝ) :
      hilbertPartialBandSum
        (fun j k => if len j ≤ r then packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) n x =
      ∑ b : {b // b ∈ boxes}, F b n x := by
    have hs (j : Fin N) (k : κ) :
        (if len j ≤ r then packetSynthesis (fun i => c j i k) (fun i => f j i k) else 0) =
          ∑ b : {b // b ∈ boxes}, G b j k := by
      rw [shortSynthesis_eq_sum_boxes len index r (fun j i => c j i k) (fun j i => f j i k) j]
      exact Finset.sum_subtype boxes (fun _ => Iff.rfl) _
    simp_rw [hs]
    exact hilbertPartialBandSum_finset_sum Finset.univ G n x
  have h := lintegral_sum_box_variation (volume.restrict (Icc (u - r) (u + r)))
    F hF N Subtype.val Subtype.val_injective hM hbox'
  simp_rw [hsum]
  apply h.trans_eq
  congr 1
  dsimp [A, M]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SquareMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Passing a local square bound to a local mean bound. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem integral_le_of_square_mean_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ)
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    {K : ℝ} (hK : 0 < K) (h2 : (∫ x, f x ^ 2 ∂μ) ≤ K ^ 2 * μ.real univ) :
    (∫ x, f x ∂μ) ≤ K * μ.real univ := by
  have hpoint (x : X) : (2 * K) * f x ≤ f x ^ 2 + K ^ 2 := by
    nlinarith [sq_nonneg (f x - K)]
  have h := integral_mono (hf.const_mul (2 * K)) (hf2.add (integrable_const (K ^ 2))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hf2 (integrable_const (K ^ 2)), integral_const,
    smul_eq_mul] at h
  nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationContinuous
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the actual finite variation function. This permits
pointwise interval John--Nirenberg bounds, without exceptional lines. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem continuous_finiteCubicVariation {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => finiteCubicVariation (fun n => F n x) N) := by
  classical
  let g := fun (p : Fin (N + 1) → Fin (N + 1)) (x : X) =>
    if Monotone p then ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ ^ 3 else 0
  have hg (p : Fin (N + 1) → Fin (N + 1)) : Continuous (g p) := by
    by_cases hp : Monotone p
    · simp only [g, ite_eq_left hp]
      exact continuous_finsetSum _ (fun i _ => ((hF _).sub (hF _)).norm.pow 3)
    · simp only [g, ite_eq_right hp]
      exact continuous_const
  have hs := Continuous.finset_sup' Finset.univ_nonempty (fun p _ => hg p)
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [finiteCubicVariation, g, Finset.sup'_apply]

theorem continuous_cubicVariation {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] (F : ℕ → X → E) (hF : ∀ n, Continuous (F n)) (N : ℕ) :
    Continuous (fun x => cubicVariation (fun n => F n x) N) := by
  apply (continuous_finiteCubicVariation F hF N).rpow_const
  intro x
  exact Or.inr (by norm_num)

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Perturbing finite variation by a short-scale sequence. -/

noncomputable section

namespace LipschitzHilbert

theorem cubicVariation_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → E) (N : ℕ) : cubicVariation (fun n => -F n) N = cubicVariation F N := by
  have heq : (fun n => -F n) = fun n => (-1 : ℝ) • F n := by funext n; simp
  rw [heq, cubicVariation, finiteCubicVariation_smul]
  norm_num [cubicVariation]

theorem cubicVariation_add_le {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) : cubicVariation (fun n => F n + G n) N ≤
      cubicVariation F N + cubicVariation G N := finiteCubicVariation_add_rpow F G N

theorem abs_cubicVariation_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : ℕ → E) (N : ℕ) : |cubicVariation F N - cubicVariation G N| ≤
      cubicVariation (fun n => F n - G n) N := by
  have hFG : (fun n => G n + (F n - G n)) = F := by funext n; abel
  have hGF : (fun n => F n + (G n - F n)) = G := by funext n; abel
  have hneg : (fun n => G n - F n) = fun n => -(F n - G n) := by funext n; abel
  have h1 := cubicVariation_add_le G (fun n => F n - G n) N
  rw [hFG] at h1
  have h2 := cubicVariation_add_le F (fun n => G n - F n) N
  rw [hGF, hneg, cubicVariation_neg] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem abs_cubicVariation_add_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S L : ℕ → E) (N : ℕ) :
    |cubicVariation (fun n => S n + L n) N - cubicVariation L N| ≤ cubicVariation S N := by
  have h := abs_cubicVariation_sub_le (fun n => S n + L n) L N
  simpa only [add_sub_cancel_right] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_VariationMeanOscillation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local BMO step for variation: short-scale L1 control and
long-scale oscillation control imply mean oscillation of the full variation. -/

noncomputable section
open MeasureTheory Set

namespace LipschitzHilbert

theorem variation_short_long_mean_oscillation {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasure μ] (S L : ℕ → X → E) (N : ℕ)
    (hs : Integrable (fun x => cubicVariation (fun n => S n x) N) μ)
    (hl : Integrable (fun x => cubicVariation (fun n => L n x) N) μ)
    (hf : Integrable (fun x => cubicVariation (fun n => S n x + L n x) N) μ)
    (hm : 0 < μ.real univ) {K C : ℝ}
    (hshort : (∫ x, cubicVariation (fun n => S n x) N ∂μ) ≤ K * μ.real univ)
    (hlong : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ,
      cubicVariation (fun n => L n x - L n y) N ≤ C) :
    (∫ x, |cubicVariation (fun n => S n x + L n x) N -
      integralAverage μ (fun y => cubicVariation (fun n => S n y + L n y) N)| ∂μ) ≤
        (2 * K + C) * μ.real univ := by
  let f := fun x => cubicVariation (fun n => S n x + L n x) N
  let g := fun x => cubicVariation (fun n => L n x) N
  have hfg : Integrable (fun x => f x - g x) μ := hf.sub hl
  have hshort' : (∫ x, ‖f x - g x‖ ∂μ) ≤ K * μ.real univ := by
    apply le_trans (integral_mono hfg.norm hs _) hshort
    intro x
    simpa only [Real.norm_eq_abs] using
      abs_cubicVariation_add_sub_le (fun n => S n x) (fun n => L n x) N
  have hlong' : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ‖g x - g y‖ ≤ C := by
    filter_upwards [hlong] with x hx
    filter_upwards [hx] with y hy
    simpa only [Real.norm_eq_abs] using
      (abs_cubicVariation_sub_le (fun n => L n x) (fun n => L n y) N).trans hy
  have h := short_long_mean_oscillation μ (fun x => f x - g x) g hfg hl hm hshort' hlong'
  have heq : (fun x => (f x - g x) + g x) = f := by funext x; ring
  rw [heq] at h
  simpa only [sub_add_cancel, Real.norm_eq_abs] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_VariationLineBMO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Applying the interval John--Nirenberg theorem to a finite packet
variation, using the actual short/long decomposition on each cell. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem continuous_integrable_cell (g : FiniteLineGrid) {f : ℝ → ℝ}
    (hf : Continuous f) (level i : ℕ) : IntegrableOn f (g.cell level i) := by
  unfold cell
  exact hf.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self

theorem variation_full_mean_oscillation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : FiniteLineGrid) (F : ℕ → ℝ → E) (S L : ℕ → ℕ → ℕ → ℝ → E) (N : ℕ)
    (hS : ∀ level i n, Continuous (S level i n))
    (hL : ∀ level i n, Continuous (L level i n))
    (hdecomp : ∀ level i n x, F n x = S level i n x + L level i n x)
    {K C : ℝ} (hK : 0 < K)
    (hshort : ∀ level i, i < g.branching ^ level →
      (∫ x in g.cell level i, (cubicVariation (fun n => S level i n x) N) ^ 2) ≤
        K ^ 2 * g.meshWidth level)
    (hlong : ∀ level i, i < g.branching ^ level → ∀ x ∈ g.cell level i, ∀ y ∈ g.cell level i,
      cubicVariation (fun n => L level i n x - L level i n y) N ≤ C) :
    g.HasFullMeanOscillationBound (fun x => cubicVariation (fun n => F n x) N) (2 * K + C) := by
  intro level i hi
  have hscont := continuous_cubicVariation (S level i) (hS level i) N
  have hlcont := continuous_cubicVariation (L level i) (hL level i) N
  have hfcont := continuous_cubicVariation (fun n x => S level i n x + L level i n x)
    (fun n => (hS level i n).add (hL level i n)) N
  have hs := g.continuous_integrable_cell hscont level i
  have hl := g.continuous_integrable_cell hlcont level i
  have hf := g.continuous_integrable_cell hfcont level i
  have hs2 := g.continuous_integrable_cell (hscont.pow 2) level i
  have hmean := integral_le_of_square_mean_bound (volume.restrict (g.cell level i)) _ hs hs2 hK
    (by simpa only [g.cell_mass] using hshort level i hi)
  have hosc : ∀ᵐ x ∂volume.restrict (g.cell level i), ∀ᵐ y ∂volume.restrict (g.cell level i),
      cubicVariation (fun n => L level i n x - L level i n y) N ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    exact hlong level i hi x hx y hy
  have h := variation_short_long_mean_oscillation (volume.restrict (g.cell level i))
    (S level i) (L level i) N hs hl hf (by rw [g.cell_mass]; exact g.meshWidth_pos level) hmean hosc
  simp_rw [← hdecomp level i] at h
  simpa only [g.cell_mass, g.cellMean_eq_integralAverage] using h

end LipschitzHilbert.FiniteLineGrid

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_LinePacketFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite packet data on a reference line, with local coefficient
budgets kept explicit. No concentration or synthesis estimate is part of
the data. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators FourierTransform ENNReal

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

namespace LinePacketFamily

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem length_pos (P : LinePacketFamily N κ ι) (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

theorem continuous_variation (P : LinePacketFamily N κ ι) : Continuous P.variation :=
  continuous_cubicVariation _ (hilbertPartialBandSum_continuous P.packets) N

theorem partial_sum_split (P : LinePacketFamily N κ ι) (r : ℝ) (n : ℕ) (x : ℝ) :
    hilbertPartialBandSum P.packets n x =
      hilbertPartialBandSum (P.shortPackets r) n x +
      hilbertPartialBandSum (P.longPackets r) n x := by
  ext k
  change partialBandSum (fun j => P.packets j k) n x =
    partialBandSum (fun j => P.shortPackets r j k) n x +
      partialBandSum (fun j => P.longPackets r j k) n x
  unfold partialBandSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < n
  · simp only [hj, ite_true, if_true]
    by_cases hlen : P.length j ≤ r
    · simp only [shortPackets, longPackets, ite_eq_left hlen, ite_eq_right (not_lt.mpr hlen),
        zero_apply, add_zero]
    · simp only [shortPackets, longPackets, ite_eq_right hlen, ite_eq_left (lt_of_not_ge hlen),
        zero_apply, zero_add]
  · simp only [hj, ite_false, if_false, zero_add]

theorem long_oscillation (P : LinePacketFamily N κ ι) (u r : ℝ) (hr : 0 < r)
    {x z : ℝ} (hx : x ∈ Icc (u-r) (u+r)) (hz : z ∈ Icc (u-r) (u+r)) :
    cubicVariation (fun n => hilbertPartialBandSum (P.longPackets r) n x -
      hilbertPartialBandSum (P.longPackets r) n z) N ≤ 4 * (P.constant * (4 * Real.pi) ^ 2) :=
  long_line_variation P.coeff P.wave P.site P.site_injective P.baseX P.baseZ
    P.topLength P.width P.lineY u r P.constant P.topLength_pos P.width_pos.ne' hr
    P.constant_pos.le P.coeff_norm P.deriv_bound hx hz

end LinePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PacketLineConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference-line concentration of the full packet variation, assembled
from the actual short-scale energy and long-scale derivative estimates. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal FourierTransform

namespace LipschitzHilbert.LinePacketFamily

attribute [local instance] Classical.propDecidable

variable {N : ℕ} {κ : Type} {ι : Fin N → Type} [Fintype κ] [∀ j, Fintype (ι j)]

theorem full_mean_oscillation (P : LinePacketFamily N κ ι) (g : FiniteLineGrid)
    {D : ℝ} (hD : 0 ≤ D)
    (hshort : ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2) ≤ D * r) :
    g.HasFullMeanOscillationBound P.variation
      (2 * Real.sqrt (D + 1) + 4 * (P.constant * (4 * Real.pi) ^ 2)) := by
  let r := fun level => g.meshWidth level / 2
  let u := fun level i => g.origin + g.meshWidth level * i + r level
  let S := fun level (_i : ℕ) n x => hilbertPartialBandSum (P.shortPackets (r level)) n x
  let L := fun level (_i : ℕ) n x => hilbertPartialBandSum (P.longPackets (r level)) n x
  have hr (level : ℕ) : 0 < r level := by dsimp [r]; exact half_pos (g.meshWidth_pos level)
  have hcell (level i : ℕ) : g.cell level i = Ico (u level i - r level) (u level i + r level) := by
    dsimp [FiniteLineGrid.cell, u, r]
    congr 1 <;> ring
  apply g.variation_full_mean_oscillation
    (fun n x => hilbertPartialBandSum P.packets n x) S L N
    (fun level _ n => hilbertPartialBandSum_continuous _ n)
    (fun level _ n => hilbertPartialBandSum_continuous _ n)
    (fun level _ n x => P.partial_sum_split (r level) n x)
    (Real.sqrt_pos.mpr (by linarith))
  · intro level i _
    change (∫ x in g.cell level i,
      (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets (r level)) n x) N) ^ 2) ≤ _
    rw [hcell, ← integral_Icc_eq_integral_Ico]
    apply (hshort (u level i) (r level) (hr level)).trans
    rw [Real.sq_sqrt (by linarith : 0 ≤ D + 1)]
    dsimp [r]
    nlinarith [g.meshWidth_pos level]
  · intro level i _ x hx z hz
    change cubicVariation (fun n => hilbertPartialBandSum (P.longPackets (r level)) n x -
      hilbertPartialBandSum (P.longPackets (r level)) n z) N ≤ _
    rw [hcell] at hx hz
    exact P.long_oscillation (u level i) (r level) (hr level)
      (Ico_subset_Icc_self hx) (Ico_subset_Icc_self hz)

end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_UniformLineMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Expose the dimension and scale-count uniformity of the already proved
short energy and line moments. The constant is chosen before the finite
packet spaces, as required for the final uniform operator estimate. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform

namespace LipschitzHilbert.LinePacketFamily

theorem uniform_short_energy (hL : LepingleInput) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : LinePacketFamily N κ ι) (B : ℝ), 0 ≤ B → P.HasLocalBudget B →
      (∀ j i k ξ, |ξ| < lo * (2 : ℝ) ^ j.val → 𝓕 (P.wave j i k) ξ = 0) →
      (∀ j i k ξ, hi * (2 : ℝ) ^ j.val < |ξ| → 𝓕 (P.wave j i k) ξ = 0) →
      ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2) ≤
        A * P.constant ^ 2 * B * r := by
  obtain ⟨A,hA,hshort⟩ := short_line_variation hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P B hB hbudget hlow hhigh u r hr
  have he := hshort N κ ι P.coeff P.wave P.centerX P.centerZ P.site P.length
    P.baseX P.baseZ u P.lineY r P.width P.constant B P.site_injective P.length_pos hr
    P.width_pos hB (fun _ _ => rfl) (fun _ _ => rfl) P.wave_bound (hbudget u r hr) hlow hhigh
  have hc := continuous_cubicVariation _ (hilbertPartialBandSum_continuous (P.shortPackets r)) N
  have hint : IntegrableOn (fun x =>
      (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2)
      (Icc (u-r) (u+r)) volume := (hc.pow 2).continuousOn.integrableOn_Icc
  have heq : ENNReal.ofReal (∫ x in Icc (u-r) (u+r),
      (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ 2) =
      ∫⁻ x in Icc (u-r) (u+r), ENNReal.ofReal (finiteCubicVariation
        (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ (2 / 3 : ℝ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
    apply lintegral_congr
    intro x
    rw [cubicVariation_sq]
    exact (ENNReal.ofReal_rpow_of_nonneg (finiteCubicVariation_nonneg _ _) (by norm_num)).symm
  change (∫⁻ x in Icc (u-r) (u+r), ENNReal.ofReal (finiteCubicVariation
    (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N) ^ (2 / 3 : ℝ)) ≤
      ENNReal.ofReal (A * P.constant ^ 2 * B * r) at he
  rw [← heq] at he
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ A * P.constant ^ 2 * B * r)] using ht


end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ThresholdSynthesis
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A monotone threshold selects one terminal interval of dyadic scales.
Its synthesis is controlled by the actual partial-sum variation. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem increment_cube_le_finiteCubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    ‖F b - F a‖^3 ≤ finiteCubicVariation F N := by
  classical
  by_cases hN : N = 0
  · subst N
    have : a = 0 ∧ b = 0 := by omega
    rcases this with ⟨rfl,rfl⟩
    simpa using finiteCubicVariation_nonneg F 0
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let p : Fin (N+1) → Fin (N+1) := fun i =>
    if i.val = 0 then ⟨a, by omega⟩ else ⟨b, by omega⟩
  have hp : Monotone p := by
    intro i j hij
    dsimp [p]
    split_ifs with hi hj hj
    · exact le_rfl
    · exact hab
    · have hij' : i.val ≤ j.val := hij
      omega
    · exact le_rfl
  have hsum := partition_le_finiteCubicVariation F N p hp
  have hs : ‖F b - F a‖^3 ≤
      ∑ i : Fin N, ‖F (p i.succ) - F (p i.castSucc)‖^3 := by
    have h := Finset.single_le_sum
      (f := fun i : Fin N => ‖F (p i.succ) - F (p i.castSucc)‖^3)
      (s := Finset.univ) (a := (⟨0,hNpos⟩ : Fin N))
      (fun i _ => pow_nonneg (norm_nonneg _) _) (Finset.mem_univ _)
    simpa only [p, Fin.val_succ, Fin.val_castSucc, Nat.zero_add,
      Nat.one_ne_zero, ite_false, if_false, ite_true, if_true] using h
  exact hs.trans hsum

theorem increment_le_cubicVariation {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    ‖F b - F a‖ ≤ cubicVariation F N := by
  have h := Real.rpow_le_rpow (pow_nonneg (norm_nonneg (F b-F a)) 3)
    (increment_cube_le_finiteCubicVariation F N a b hab hb)
    (by norm_num : (0:ℝ) ≤ 1/3)
  have heq : (‖F b-F a‖^3)^(1/3:ℝ) = ‖F b-F a‖ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  simpa only [heq, cubicVariation] using h

theorem monotone_threshold_suffix {N : ℕ} (d : Fin N → ℝ)
    (hd : Monotone d) (v : ℝ) :
    ∃ n : ℕ, n ≤ N ∧ ∀ j : Fin N, v ≤ d j ↔ n ≤ j.val := by
  classical
  let s := Finset.univ.filter (fun j : Fin N => v ≤ d j)
  by_cases hs : s.Nonempty
  · let j0 := s.min' hs
    have hj0 : v ≤ d j0 := (Finset.mem_filter.mp (Finset.min'_mem s hs)).2
    refine ⟨j0.val, Nat.le_of_lt j0.isLt, ?_⟩
    intro j
    constructor
    · intro hj
      exact Finset.min'_le s j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
    · intro hj
      exact hj0.trans (hd hj)
  · refine ⟨N, le_rfl, ?_⟩
    intro j
    constructor
    · intro hj
      exact False.elim (hs ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩)
    · intro hj
      omega

theorem threshold_sum_eq_partial_difference {E : Type*} [AddCommGroup E]
    {N : ℕ} (f : Fin N → E) (d : Fin N → ℝ) (hd : Monotone d) (v : ℝ) :
    ∃ n : ℕ, n ≤ N ∧ (∑ j, if v ≤ d j then f j else 0) =
      packetPartialSum f N - packetPartialSum f n := by
  obtain ⟨n,hn,hselect⟩ := monotone_threshold_suffix d hd v
  refine ⟨n,hn,?_⟩
  unfold packetPartialSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left j.isLt]
  by_cases hj : v ≤ d j
  · have hn' : ¬ j.val < n := Nat.not_lt.mpr ((hselect j).mp hj)
    simp only [ite_eq_left hj, ite_eq_right hn', sub_zero]
  · have hn' : j.val < n := Nat.lt_of_not_ge (fun h => hj ((hselect j).mpr h))
    simp only [ite_eq_right hj, ite_eq_left hn', sub_self]

theorem threshold_sum_le_variation {E : Type*} [NormedAddCommGroup E]
    {N : ℕ} (f : Fin N → E) (d : Fin N → ℝ) (hd : Monotone d) (v : ℝ) :
    ‖∑ j, if v ≤ d j then f j else 0‖ ≤ cubicVariation (packetPartialSum f) N := by
  obtain ⟨n,hn,heq⟩ := threshold_sum_eq_partial_difference f d hd v
  rw [heq]
  exact increment_le_cubicVariation _ N n N hn le_rfl

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted Cauchy–Schwarz step in the local coefficient estimate. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert

theorem weighted_lintegral_cauchySchwarz {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w f : Ω → ℝ) (hw : Measurable w) (hf : Measurable f)
    (hpos : ∀ x, 0 < w x) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal ((w x)⁻¹ ^ 2) ∂μ) ^ (1/2 : ℝ) *
      (∫⁻ x, ENNReal.ofReal ((w x)^2 * (f x)^2) ∂μ) ^ (1/2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (2:ℝ).HolderConjugate 2 from by norm_num [Real.holderConjugate_iff])
    (f := fun x => ENNReal.ofReal ((w x)⁻¹))
    (g := fun x => ENNReal.ofReal (w x * f x))
    (hw.inv.ennreal_ofReal.aemeasurable) ((hw.mul hf).ennreal_ofReal.aemeasurable)
  have heq (x : Ω) : ENNReal.ofReal ((w x)⁻¹) * ENNReal.ofReal (w x * f x) =
      ENNReal.ofReal (f x) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (hpos x).le), ← mul_assoc,
      inv_mul_cancel₀ (hpos x).ne', one_mul]
  have hs (x : Ω) : ENNReal.ofReal (w x * f x) ^ (2:ℝ) ≤
      ENNReal.ofReal ((w x)^2 * (f x)^2) := by
    rw [ENNReal.rpow_two]
    by_cases hx : 0 ≤ f x
    · rw [← ENNReal.ofReal_pow (mul_nonneg (hpos x).le hx), mul_pow]
    · rw [ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos (hpos x).le (le_of_not_ge hx)), zero_pow (by decide)]
      exact bot_le
  simpa only [Pi.mul_apply, heq, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (inv_nonneg.mpr (hpos _).le)] using
    h.trans (mul_le_mul_right (ENNReal.rpow_le_rpow (lintegral_mono hs) (by norm_num)) _)

theorem referenceWeight_pos (a b r W : ℝ) (z : ℝ × ℝ) :
    0 < referenceWeight a b r W z :=
  mul_pos (lt_of_lt_of_le zero_lt_one (polynomialWeight_one_le _ _ _ _))
    (lt_of_lt_of_le zero_lt_one (polynomialWeight_one_le _ _ _ _))

theorem referenceWeight_measurable (a b r W : ℝ) :
    Measurable (referenceWeight a b r W) := by
  unfold referenceWeight polynomialWeight
  fun_prop

theorem referenceWeight_inverse_integral (a b r W : ℝ) (hr : 0 < r) (hW : 0 < W) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal ((referenceWeight a b r W z)⁻¹ ^ 2)) ≤
      ENNReal.ofReal (Real.pi^2 * r * W) := by
  have hpoint (z : ℝ × ℝ) : (referenceWeight a b r W z)⁻¹ ^ 2 ≤
      lineEnvelope b W 1 z.1 * lineEnvelope a r 1 z.2 := by
    have hx := lineEnvelope_antitone a r z.2 (by decide : 1 ≤ 2)
    have hy := lineEnvelope_antitone b W z.1 (by decide : 1 ≤ 2)
    have heq : (referenceWeight a b r W z)⁻¹ ^ 2 =
        lineEnvelope b W 2 z.1 * lineEnvelope a r 2 z.2 := by
      simp only [referenceWeight, polynomialWeight, pow_one, mul_inv_rev, mul_pow,
        lineEnvelope, ← div_pow, ← inv_pow]
    rw [heq]
    exact mul_le_mul hy hx (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  calc
    _ ≤ ∫⁻ z : ℝ × ℝ, ENNReal.ofReal
        (lineEnvelope b W 1 z.1 * lineEnvelope a r 1 z.2) :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (hpoint z))
    _ = ENNReal.ofReal (Real.pi^2 * r * W) := by
      rw [Measure.volume_eq_prod, lintegral_prod _ (by apply Measurable.aemeasurable; unfold lineEnvelope; fun_prop)]
      simp_rw [ENNReal.ofReal_mul (lineEnvelope_nonneg _ _ _ _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_lineEnvelope_one a r hr)
        (Filter.Eventually.of_forall (lineEnvelope_nonneg a r 1)),
        integral_lineEnvelope_one a r hr,
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        ← ofReal_integral_eq_lintegral_ofReal (integrable_lineEnvelope_one b W hW)
          (Filter.Eventually.of_forall (lineEnvelope_nonneg b W 1)),
        integral_lineEnvelope_one b W hW, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_WeightedPacketEnergy
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomially localized packet synthesis energy with arbitrary dual
coefficients. No local coefficient budget is assumed here. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

theorem weighted_component_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → EuclideanSpace ℂ κ) (rho : ι → ℝ) :
    (∑ k, ∑ i, ‖c i k‖ ^ 2 * rho i) = ∑ i, ‖c i‖ ^ 2 * rho i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, ← EuclideanSpace.norm_sq_eq]

theorem weighted_packet_energy {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ × ℤ) (len : Fin N → ℝ)
    (a0 b0 a r W y C : ℝ) (hr : 0 < r) (hW : 0 < W)
    (hlen : ∀ j, 0 < len j) (hlenr : ∀ j, ∀ _ : ι j, len j ≤ r)
    (hinj : ∀ j, Function.Injective (site j))
    (hX : ∀ j i, X j i = a0+len j*(site j i).1)
    (hZ : ∀ j i, Z j i = b0+W*(site j i).2)
    (hcenter : ∀ j i, |X j i-a| ≤ r)
    (hf : ∀ j i k x, ‖f j i k x‖ ≤ C *
      (lineEnvelope (X j i) (len j) 3 x * lineEnvelope (Z j i) W 3 y)) :
    (∑ j, ∑ k, ∫ x, ‖polynomialLocalization a r 1
      (packetSynthesis (fun i => c j i k) (fun i => f j i k)) x‖ ^ 2) ≤
      ((4 * Real.pi)^2 * C^2 * 16 * Real.pi) *
        ∑ j, len j * ∑ i, ‖c j i‖ ^ 2 * lineEnvelope (Z j i) W 3 y := by
  let D := (4 * Real.pi)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hscalar (j : Fin N) (k : κ) :
      (∫ x, ‖polynomialLocalization a r 1
        (packetSynthesis (fun i => c j i k) (fun i => f j i k)) x‖ ^ 2) ≤
        (D * C^2 * 16 * Real.pi) * len j *
          ∑ i, ‖c j i k‖ ^ 2 * lineEnvelope (Z j i) W 3 y := by
    classical
    by_cases hj : Nonempty (ι j)
    swap
    · let : IsEmpty (ι j) := ⟨fun i => hj ⟨i⟩⟩
      simp [packetSynthesis, polynomialLocalization_apply]
    have hrho (i : ι j) : 0 < lineEnvelope (Z j i) W 3 y := by unfold lineEnvelope; positivity
    have hover (x : ℝ) : (∑ i, lineEnvelope (Z j i) W 3 y * lineEnvelope (X j i) (len j) 3 x) ≤ D := by
      simp_rw [hX,hZ]
      simpa only [D, mul_comm] using injective_tile_lattice_overlap (site j) (hinj j)
        a0 b0 (len j) W x y (hlen j).ne' hW.ne' (by decide : 1 ≤ 3) (by decide : 1 ≤ 3)
    have h := polynomial_packetSynthesis_energy (fun i => c j i k) (fun i => f j i k)
      (X j) (fun i => lineEnvelope (Z j i) W 3 y) a (len j) r C D 1
      (hlen j) hr (hlenr j (Classical.choice hj)) hrho (hcenter j) hD hover
      (fun i x => by simpa only [show 1 + 1 * 2 = (3 : ℕ) from rfl, mul_comm] using hf j i k x)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  calc
    _ ≤ ∑ j, ∑ k, (D * C^2 * 16 * Real.pi) * len j *
        ∑ i, ‖c j i k‖ ^ 2 * lineEnvelope (Z j i) W 3 y :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hscalar j k))
    _ = _ := by
      simp_rw [← Finset.mul_sum, weighted_component_energy]
      simp only [D, ← Finset.mul_sum, mul_assoc]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_ReferencePacketFamily
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual finite packet data in one reference box. Coefficients are
left arbitrary for the weighted synthesis and subsequent duality argument. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem coefficientEnergy_nonneg (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) : 0 ≤ P.coefficientEnergy c := by
  unfold coefficientEnergy
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (P.length_pos j).le
    (Finset.sum_nonneg (fun i _ => sq_nonneg ‖c j i‖)))

theorem horizontal_energy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) :
    (∑ j, ∑ k, ∫ x, ‖polynomialLocalization P.centerX P.radius 1
      (P.packets c y j k) x‖ ^ 2) ≤
      ((4 * Real.pi)^2 * P.constant^2 * 16 * Real.pi) *
        ∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2 *
          lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 3 y :=
  weighted_packet_energy c (fun j i k => P.wave j i k y)
    (fun j i => P.baseX + P.length j * (P.site j i).1)
    (fun j i => P.baseZ + P.width * (P.site j i).2)
    P.site P.length P.baseX P.baseZ P.centerX P.radius P.width y P.constant
    P.radius_pos P.width_pos P.length_pos P.length_le P.site_injective
    (fun _ _ => rfl) (fun _ _ => rfl) P.center_x
    (fun j i k x => P.wave_bound j i k y x)

theorem weighted_energy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) :
    polynomialWeight P.centerZ P.width 1 y ^ 2 *
      (∑ j, ∑ k, ∫ x, ‖polynomialLocalization P.centerX P.radius 1
        (P.packets c y j k) x‖ ^ 2) ≤
      ((4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi) *
        ∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2 *
          lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 1 y := by
  have hp (j : Fin N) (i : ι j) := polynomialWeight_sq_mul_envelope y
    (P.baseZ + P.width * (P.site j i).2) P.centerZ P.width P.width 1 1
    P.width_pos P.width_pos le_rfl (P.center_z j i)
  have hm : polynomialWeight P.centerZ P.width 1 y ^ 2 *
      (∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2 *
        lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 3 y) ≤
      16 * (∑ j, P.length j * ∑ i, ‖c j i‖ ^ 2 *
        lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 1 y) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = (P.length j * ‖c j i‖^2) *
          (polynomialWeight P.centerZ P.width 1 y ^ 2 *
            lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 3 y) := by ring
      _ ≤ (P.length j * ‖c j i‖^2) *
          (16 * lineEnvelope (P.baseZ + P.width * (P.site j i).2) P.width 1 y) :=
        mul_le_mul_of_nonneg_left (by simpa only [pow_one] using hp j i)
          (mul_nonneg (P.length_pos j).le (sq_nonneg _))
      _ = _ := by ring

  calc
    _ ≤ polynomialWeight P.centerZ P.width 1 y ^ 2 *
        (((4 * Real.pi)^2 * P.constant^2 * 16 * Real.pi) * _) :=
      mul_le_mul_of_nonneg_left (P.horizontal_energy c y) (sq_nonneg _)
    _ = ((4 * Real.pi)^2 * P.constant^2 * 16 * Real.pi) *
        (polynomialWeight P.centerZ P.width 1 y ^ 2 * _) := by ring
    _ ≤ ((4 * Real.pi)^2 * P.constant^2 * 16 * Real.pi) * (16 * _) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_WeightedReferenceVariation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomially weighted maximal-synthesis estimate about an arbitrary
reference box, conditional only on the published scalar Lépingle input. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem transverseEnergy_nonneg (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (y : ℝ) : 0 ≤ P.transverseEnergy c y := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (P.length_pos j).le (Finset.sum_nonneg
    (fun i _ => mul_nonneg (sq_nonneg _) (lineEnvelope_nonneg _ _ _ _)))

theorem transverseEnergy_integrable (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) : Integrable (P.transverseEnergy c) := by
  apply integrable_finsetSum
  intro j _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  exact (integrable_lineEnvelope_one _ _ P.width_pos).const_mul _

theorem integral_transverseEnergy (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) :
    (∫ y, P.transverseEnergy c y) = Real.pi * P.width * P.coefficientEnergy c := by
  unfold transverseEnergy
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    simp_rw [integral_finsetSum Finset.univ (fun i _ =>
      (integrable_lineEnvelope_one _ _ P.width_pos).const_mul _)]
    simp_rw [integral_const_mul, integral_lineEnvelope_one _ _ P.width_pos]
    simp only [coefficientEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro j _
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro i _
    exact (integrable_lineEnvelope_one _ _ P.width_pos).const_mul _

theorem weighted_variation (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : ReferencePacketFamily N κ ι)
      (c : ∀ j, ι j → EuclideanSpace ℂ κ),
      (∀ j i k y ξ, |ξ| < lo * (2 : ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi * (2 : ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      P.weightedVariationEnergy c ≤ (K : ℝ≥0∞) * ENNReal.ofReal
        (((4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi^2) *
          P.width * P.coefficientEnergy c) := by
  obtain ⟨K,hK,hbound⟩ := dyadic_hilbert_annular_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ ι instκ instι P c hlow hhigh
  let A := (4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hline (y : ℝ) :
      (∫⁻ x, ENNReal.ofReal (polynomialWeight P.centerX P.radius 1 x ^ 2) *
        ENNReal.ofReal (finiteCubicVariation
          (fun n => hilbertPartialBandSum (P.packets c y) n x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal
        (∑ j, ∑ k, ∫ x, ‖polynomialLocalization P.centerX P.radius 1
          (P.packets c y j k) x‖ ^ 2) := by
    have hl (j : Fin N) (k : κ) (ξ : ℝ) (hξ : |ξ| < lo*(2:ℝ)^j.val) :
        𝓕 (P.packets c y j k) ξ = 0 :=
      packetSynthesis_fourier_zero _ _ ξ (fun i => hlow j i k y ξ hξ)
    have hh (j : Fin N) (k : κ) (ξ : ℝ) (hξ : hi*(2:ℝ)^j.val < |ξ|) :
        𝓕 (P.packets c y j k) ξ = 0 :=
      packetSynthesis_fourier_zero _ _ ξ (fun i => hhigh j i k y ξ hξ)
    have h := hbound N κ
      (fun j k => polynomialLocalization P.centerX P.radius 1 (P.packets c y j k))
      (fun j k => polynomialLocalization_low _ _ _ _ _ _ (hl j k) (hh j k))
      (fun j k => polynomialLocalization_high _ _ _ _ _ _ (hl j k) (hh j k))
    simpa only [hilbertPartialBandSum_polynomialLocalization,
      ennreal_finiteCubicVariation_smul_square] using h
  have hpoint (y : ℝ) :
      ENNReal.ofReal (polynomialWeight P.centerZ P.width 1 y ^ 2) *
      (∫⁻ x, ENNReal.ofReal (polynomialWeight P.centerX P.radius 1 x ^ 2) *
        ENNReal.ofReal (finiteCubicVariation
          (fun n => hilbertPartialBandSum (P.packets c y) n x) N) ^ (2 / 3 : ℝ)) ≤
      (K : ℝ≥0∞) * ENNReal.ofReal (A * P.transverseEnergy c y) := by
    calc
      _ ≤ ENNReal.ofReal (polynomialWeight P.centerZ P.width 1 y ^ 2) *
          ((K : ℝ≥0∞) * ENNReal.ofReal _) := mul_le_mul_right (hline y) _
      _ = (K : ℝ≥0∞) * ENNReal.ofReal
          (polynomialWeight P.centerZ P.width 1 y ^ 2 * _) := by
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
        ac_rfl
      _ ≤ _ := mul_le_mul_right (ENNReal.ofReal_le_ofReal (P.weighted_energy c y)) _
  calc
    _ ≤ ∫⁻ y, (K : ℝ≥0∞) * ENNReal.ofReal (A * P.transverseEnergy c y) :=
      lintegral_mono hpoint
    _ = (K : ℝ≥0∞) * ENNReal.ofReal (∫ y, A * P.transverseEnergy c y) := by
      rw [lintegral_const_mul' _ _ (by simp),
        ofReal_integral_eq_lintegral_ofReal ((P.transverseEnergy_integrable c).const_mul A)
          (Filter.Eventually.of_forall (fun y => mul_nonneg hA (P.transverseEnergy_nonneg c y)))]
    _ = _ := by
      rw [integral_const_mul, P.integral_transverseEnergy]
      congr 2
      dsimp [A]
      ring

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Measurable planar synthesis, threshold selection, and the weighted
variation integral in the reference chart (transverse, longitudinal). -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem thresholdSynthesis_le_variation (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (d : Fin N → ℝ) (hd : Monotone d)
    (v : ℝ × ℝ → ℝ) (z : ℝ × ℝ) :
    ‖P.thresholdSynthesis c d v z‖ ≤ P.variation c z := by
  have heq : packetPartialSum (fun j => P.scaleSynthesis c j z) =
      (fun n => hilbertPartialBandSum (P.packets c z.1) n z.2) := by
    funext n
    exact (hilbertPartialBandSum_eq_packetPartialSum (P.packets c z.1) n z.2).symm
  simpa only [thresholdSynthesis, variation, heq] using
    threshold_sum_le_variation (fun j => P.scaleSynthesis c j z) d hd (v z)

theorem partialSynthesis_measurable (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) (n : ℕ) :
    Measurable (fun z : ℝ × ℝ => hilbertPartialBandSum (P.packets c z.1) n z.2) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_iff.mpr
  intro k
  apply Finset.measurable_sum
  intro j _
  by_cases hj : j.val < n
  · simp only [ite_eq_left hj]
    unfold packets
    simp only [packetSynthesis_apply]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (hw j i k))
  · simpa only [ite_eq_right hj] using
      (measurable_const : Measurable (fun _ : ℝ × ℝ => (0:ℂ)))

theorem variation_measurable (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) :
    Measurable (P.variation c) :=
  (measurable_finiteCubicVariation _ (P.partialSynthesis_measurable c hw) N).pow_const _

theorem weightedVariationEnergy_eq (P : ReferencePacketFamily N κ ι)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal
      (referenceWeight P.centerX P.centerZ P.radius P.width z ^ 2 * P.variation c z ^ 2)) =
      P.weightedVariationEnergy c := by
  rw [Measure.volume_eq_prod]
  rw [lintegral_prod (fun z : ℝ × ℝ => ENNReal.ofReal
    (referenceWeight P.centerX P.centerZ P.radius P.width z ^ 2 * P.variation c z ^ 2))
    (((referenceWeight_measurable _ _ _ _).pow_const 2).mul
      ((P.variation_measurable c hw).pow_const 2)).ennreal_ofReal.aemeasurable]
  unfold weightedVariationEnergy
  apply lintegral_congr
  intro y
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro x
  simp only [referenceWeight, mul_pow, variation, cubicVariation_sq]
  rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_rpow_of_nonneg
      (finiteCubicVariation_nonneg _ _) (by norm_num : (0:ℝ) ≤ 2/3)]
  ac_rfl

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceSynthesisL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The L1 synthesis estimate that supplies the dual local coefficient
budget. Reference length need not be a dyadic scale. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal FourierTransform NNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem threshold_lintegral (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ K : ℝ≥0, 0 < K ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : ReferencePacketFamily N κ ι)
      (c : ∀ j, ι j → EuclideanSpace ℂ κ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ),
      Monotone d →
      (∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) →
      (∀ j i k y ξ, |ξ| < lo * (2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi * (2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal ‖P.thresholdSynthesis c d v z‖) ≤
        ENNReal.ofReal (Real.pi^2 * P.radius * P.width) ^ (1/2:ℝ) *
        ((K : ℝ≥0∞) * ENNReal.ofReal
          (((4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi^2) *
            P.width * P.coefficientEnergy c)) ^ (1/2:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := weighted_variation hL hlo hhi
  refine ⟨K,hK,?_⟩
  intro N κ ι instκ instι P c d v hd hw hlow hhigh
  have hcs := weighted_lintegral_cauchySchwarz volume
    (referenceWeight P.centerX P.centerZ P.radius P.width) (P.variation c)
    (referenceWeight_measurable _ _ _ _) (P.variation_measurable c hw)
    (referenceWeight_pos _ _ _ _)
  rw [P.weightedVariationEnergy_eq c hw] at hcs
  calc
    _ ≤ ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (P.variation c z) :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal
        (P.thresholdSynthesis_le_variation c d hd v z))
    _ ≤ _ := hcs
    _ ≤ _ := mul_le_mul
      (ENNReal.rpow_le_rpow
        (referenceWeight_inverse_integral _ _ _ _ P.radius_pos P.width_pos) (by norm_num))
      (ENNReal.rpow_le_rpow (hbound N κ ι P c hlow hhigh) (by norm_num)) bot_le bot_le

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzingCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Hilbert duality for coefficients defined by actual analyzing
integrals. The self-pairing uses the same selected synthesizing packets. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω] [Fintype σ] [Fintype κ]

omit [Fintype σ] [Fintype κ] in
theorem analyzingCoefficient_mul_area (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, area i ≠ 0) (i : σ) (k : κ) :
    (area i : ℂ) * analyzingCoefficient μ area wave g i k =
      ∫ z, g z k * conj (wave i k z) ∂μ := by
  change (area i : ℂ) * (((area i)⁻¹ : ℂ) * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (show (area i : ℂ) ≠ 0 by exact_mod_cast ha i), one_mul]

theorem analyzingCoefficient_self_pairing (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, area i ≠ 0)
    (hint : ∀ i k, Integrable (fun z => g z k * conj (wave i k z)) μ) :
    ((∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2 : ℝ) : ℂ) =
      ∫ z, inner ℂ (diagonalSynthesis wave (analyzingCoefficient μ area wave g) z) (g z) ∂μ := by
  let a := analyzingCoefficient μ area wave g
  have hterm (i : σ) : ((area i * ‖a i‖^2 : ℝ) : ℂ) =
      ∑ k, conj (a i k) * ∫ z, g z k * conj (wave i k z) ∂μ := by
    have hnorm : (‖a i‖ : ℂ)^2 = inner ℂ (a i) (a i) :=
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (a i)).symm
    rw [Complex.ofReal_mul, Complex.ofReal_pow, hnorm]
    simp only [PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← analyzingCoefficient_mul_area μ area wave g ha i k]
    ring
  have hInt (i : σ) (k : κ) :
      Integrable (fun z => conj (a i k) * (g z k * conj (wave i k z))) μ :=
    (hint i k).const_mul _
  calc
    _ = ∑ i, ∑ k, conj (a i k) * ∫ z, g z k * conj (wave i k z) ∂μ := by
      rw [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∫ z, ∑ i, ∑ k, conj (a i k) * (g z k * conj (wave i k z)) ∂μ := by
      simp_rw [← integral_const_mul]
      rw [integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum _ (fun k _ => hInt i k))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum Finset.univ (fun k _ => hInt i k)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [diagonalSynthesis, PiLp.inner_apply, RCLike.inner_apply,
        map_sum, map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem analyzingCoefficient_energy_le (μ : Measure Ω) (area : σ → ℝ)
    (wave : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (ha : ∀ i, 0 < area i)
    (hint : ∀ i k, Integrable (fun z => g z k * conj (wave i k z)) μ)
    (hg : ∀ z, ‖g z‖ ≤ 1) :
    ENNReal.ofReal (∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2) ≤
      ∫⁻ z, ENNReal.ofReal ‖diagonalSynthesis wave (analyzingCoefficient μ area wave g) z‖ ∂μ := by
  have hn : ‖((∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2 : ℝ) : ℂ)‖ =
      ∑ i, area i * ‖analyzingCoefficient μ area wave g i‖^2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg
      (fun i _ => mul_nonneg (ha i).le (sq_nonneg _)))]
  rw [← hn, analyzingCoefficient_self_pairing μ area wave g (fun i => (ha i).ne') hint]
  rw [ofReal_norm]
  apply (enorm_integral_le_lintegral_enorm _).trans
  apply lintegral_mono
  intro z
  dsimp only
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  exact (norm_inner_le_norm _ _).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg z) (norm_nonneg _))

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceAnalysis
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual selected analyzing integrals on the reference chart. Integrability
is obtained from the two-coordinate packet envelope and a bounded test. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem wave_integrable (P : ReferencePacketFamily N κ ι)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2))
    (j : Fin N) (i : ι j) (k : κ) :
    Integrable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2) := by
  have hz := integrable_lineEnvelope (P.baseZ + P.width * (P.site j i).2)
    P.width P.width_pos (by decide : 1 ≤ 3)
  have hx := integrable_lineEnvelope (P.baseX + P.length j * (P.site j i).1)
    (P.length j) (P.length_pos j) (by decide : 1 ≤ 3)
  apply ((hz.mul_prod hx).const_mul P.constant).mono' (hw j i k).aestronglyMeasurable
  filter_upwards [] with z
  simpa only [mul_comm] using P.wave_bound j i k z.1 z.2

theorem selectedWave_measurable (P : ReferencePacketFamily N κ ι)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2))
    (s : Σ j, ι j) (k : κ) : Measurable (P.selectedWave d v s k) :=
  Measurable.ite (measurableSet_le hv measurable_const) (hw s.1 s.2 k) measurable_const

theorem selectedWave_integrable (P : ReferencePacketFamily N κ ι)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2))
    (s : Σ j, ι j) (k : κ) : Integrable (P.selectedWave d v s k) := by
  exact (P.wave_integrable hw s.1 s.2 k).indicator (measurableSet_le hv measurable_const)

theorem analyzing_integrable (P : ReferencePacketFamily N κ ι)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (hw : ∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2))
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (s : Σ j, ι j) (k : κ) :
    Integrable (fun z => g z k * conj (P.selectedWave d v s k z)) := by
  have hgm : Measurable (fun z => g z k) :=
    (measurable_pi_apply k).comp ((WithLp.measurable_ofLp 2 _).comp hg)
  apply (P.selectedWave_integrable d v hv hw s k).norm.mono'
    (hgm.mul (continuous_star.measurable.comp (P.selectedWave_measurable d v hv hw s k))).aestronglyMeasurable
  filter_upwards [] with z
  dsimp only [Pi.mul_apply, Function.comp_apply]
  rw [norm_mul, norm_star]
  have hgk : ‖g z k‖ ≤ 1 := (PiLp.norm_apply_le (g z) k).trans (hg1 z)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hgk (norm_nonneg _)

theorem diagonalSynthesis_selectedWave (P : ReferencePacketFamily N κ ι)
    (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (z : ℝ × ℝ) :
    diagonalSynthesis (P.selectedWave d v) (fun s : Σ j, ι j => c s.1 s.2) z =
      P.thresholdSynthesis c d v z := by
  classical
  ext k
  simp only [diagonalSynthesis, thresholdSynthesis, WithLp.ofLp_sum, Finset.sum_apply,
    Fintype.sum_sigma, selectedWave]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : v z ≤ d j
  · simp only [ite_eq_left hj, scaleSynthesis, packets, packetSynthesis_apply]
  · simp only [ite_eq_right hj, mul_zero, Finset.sum_const_zero]
    rfl

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_SelfEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Removing the dual coefficient norm from the self-pairing estimate. -/

noncomputable section
open scoped ENNReal

namespace LipschitzHilbert

theorem energy_le_of_sqrt_self {B A D : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (h : ENNReal.ofReal B ≤ ENNReal.ofReal A ^ (1/2:ℝ) *
      ENNReal.ofReal (D * B) ^ (1/2:ℝ)) : B ≤ A * D := by
  have hs := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 2)
  have hsq (x : ℝ≥0∞) : (x^(1/2:ℝ))^2 = x := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [ENNReal.rpow_two, mul_pow, hsq] at hs
  have ht := ENNReal.toReal_mono (by finiteness) hs
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hB, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal (mul_nonneg hD hB)] at ht
  by_cases hz : B = 0
  · rw [hz]
    exact mul_nonneg hA hD
  · have hp : 0 < B := lt_of_le_of_ne hB (Ne.symm hz)
    nlinarith

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_ReferenceCarleson
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local Carleson budget for the actual main analyzing coefficients
in a reference box, conditional only on scalar Lépingle. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal NNReal

namespace LipschitzHilbert
namespace ReferencePacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem mainCoefficient_carleson (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : ReferencePacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ),
      Monotone d → Measurable v → Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      (∀ j i k, Measurable (fun z : ℝ × ℝ => P.wave j i k z.1 z.2)) →
      (∀ j i k y ξ, |ξ| < lo * (2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi * (2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      P.width * P.coefficientEnergy (P.mainCoefficient d v g) ≤
        A * P.constant^2 * (P.radius * P.width) := by
  obtain ⟨K,hK,hL1⟩ := threshold_lintegral hL hlo hhi
  refine ⟨(K:ℝ) * (4*Real.pi)^2 * 256 * Real.pi^4, by positivity, ?_⟩
  intro N κ ι instκ instι P d v g hd hv hg hg1 hw hlow hhigh
  let a := P.mainCoefficient d v g
  let B := P.width * P.coefficientEnergy a
  let D := (K:ℝ) * ((4*Real.pi)^2 * P.constant^2 * 256 * Real.pi^2)
  have hB : 0 ≤ B := mul_nonneg P.width_pos.le (P.coefficientEnergy_nonneg a)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hsum : (∑ s : Σ j, ι j, (P.length s.1 * P.width) *
      ‖analyzingCoefficient volume (fun s : Σ j, ι j => P.length s.1 * P.width)
        (P.selectedWave d v) g s‖^2) = B := by
    rw [Fintype.sum_sigma]
    dsimp [B, coefficientEnergy]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    change (P.length j * P.width) * ‖a j i‖^2 = _
    ring
  have hpair := analyzingCoefficient_energy_le volume
    (fun s : Σ j, ι j => P.length s.1 * P.width) (P.selectedWave d v) g
    (fun s => mul_pos (P.length_pos s.1) P.width_pos)
    (P.analyzing_integrable d v hv hw g hg hg1) hg1
  rw [hsum] at hpair
  have heq (z : ℝ × ℝ) : diagonalSynthesis (P.selectedWave d v)
      (analyzingCoefficient volume (fun s : Σ j, ι j => P.length s.1 * P.width)
        (P.selectedWave d v) g) z = P.thresholdSynthesis a d v z :=
    P.diagonalSynthesis_selectedWave d v a z
  simp_rw [heq] at hpair
  have h := hpair.trans (hL1 N κ ι P a d v hd hw hlow hhigh)
  have hprod : (K : ℝ≥0∞) * ENNReal.ofReal
      (((4 * Real.pi)^2 * P.constant^2 * 256 * Real.pi^2) * P.width * P.coefficientEnergy a) =
      ENNReal.ofReal (D * B) := by
    dsimp [D,B]
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [← ENNReal.ofReal_mul K.coe_nonneg]
    congr 1
    ring
  rw [hprod] at h
  have hbudget := energy_le_of_sqrt_self hB (mul_nonneg (mul_nonneg (sq_nonneg _) P.radius_pos.le) P.width_pos.le) hD h
  change B ≤ _
  convert hbudget using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [D]
  ring

end ReferencePacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PlanarCoefficientBudget
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The proved main-coefficient budget on every short-packet center box.
The same constant works for all reference lengths and all finite families. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform

namespace LipschitzHilbert
namespace PlanarPacketFamily

theorem mainCoefficient_localBudget (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (g : ℝ × ℝ → EuclideanSpace ℂ κ),
      Monotone d → Measurable v → Measurable g → (∀ z, ‖g z‖ ≤ 1) →
      (∀ j i k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      ∀ u y r : ℝ, 0 < r → ∀ b : ℤ × ℤ,
      (∑ j, P.length j * ∑ i : P.BoxFiber u y r b j, ‖P.mainCoefficient d v g j i‖^2) ≤
        A * P.constant^2 * r := by
  obtain ⟨A,hA,hbound⟩ := ReferencePacketFamily.mainCoefficient_carleson hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι instκ instι P d v g hd hv hg hg1 hlow hhigh u y r hr b
  have h := hbound N κ (P.BoxFiber u y r b) (P.referenceBox u y r hr b)
    d v g hd hv hg hg1 (fun j i k => P.wave_measurable j i k)
    (fun j i k y ξ hξ => hlow j i k y ξ hξ)
    (fun j i k y ξ hξ => hhigh j i k y ξ hξ)
  change P.width *
    (∑ j, P.length j * ∑ i : P.BoxFiber u y r b j, ‖P.mainCoefficient d v g j i‖^2) ≤
      A * P.constant^2 * (r * P.width) at h
  apply (mul_le_mul_iff_right₀ P.width_pos).mp
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end PlanarPacketFamily
end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_PolynomialMomentBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the explicit John--Nirenberg moment expression in the polynomial
form needed when the moment order grows with the manuscript parameter. -/

noncomputable section
open scoped ENNReal

namespace LipschitzHilbert

theorem polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ)^n * (7*((n:ℝ)*Q)^n+R^n) ≤ (16*(Q+R+1)*(n:ℝ))^n := by
  let S := Q+R+1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hA : (n:ℝ)*Q ≤ (n:ℝ)*S := by dsimp [S]; nlinarith
  have hB : R ≤ (n:ℝ)*S := by
    have h := mul_le_mul_of_nonneg_right hnR hS
    dsimp [S] at h ⊢
    nlinarith
  have hAn := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) hQ) hA n
  have hBn := pow_le_pow_left₀ hR hB n
  have h8 : (8:ℝ) ≤ 8^n := by
    simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 8) hn
  calc
    _ ≤ 2^n * (8*((n:ℝ)*S)^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ ≤ 2^n * (8^n*((n:ℝ)*S)^n) := by gcongr
    _ = (16*(Q+R+1)*(n:ℝ))^n := by
      rw [← mul_assoc, ← mul_pow, ← mul_pow]
      congr 1
      dsimp [S]
      ring

theorem ennreal_polynomial_moment_majorant (Q R : ℝ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ≥0∞)^(n:ℝ) * (7*ENNReal.ofReal (((n:ℝ)*Q)^(n:ℝ)) +
      (ENNReal.ofReal R)^(n:ℝ)) ≤ ENNReal.ofReal ((16*(Q+R+1)*(n:ℝ))^n) := by
  have h := ENNReal.ofReal_le_ofReal (polynomial_moment_majorant Q R hQ hR n hn)
  simpa only [Real.rpow_natCast, ENNReal.rpow_natCast,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2^n),
    ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ 7*((n:ℝ)*Q)^n) (pow_nonneg hR n),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 7),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_pow hR,
    ENNReal.ofReal_ofNat] using h

theorem lineMomentBase_pos (C D branching : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ branching) :
    0 < lineMomentBase C D branching := by
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  unfold lineMomentBase
  positivity

theorem line_moment_expression_le (C D branching : ℝ) (hC : 0 ≤ C) (hb : 0 ≤ branching)
    (n : ℕ) (hn : 1 ≤ n) :
    (2:ℝ≥0∞)^(n:ℝ) * (7 * ENNReal.ofReal
      ((((n:ℝ)*((branching+2)*(2*Real.sqrt D+4*(C*(4*Real.pi)^2))))/Real.log (3/2))^(n:ℝ)) +
      (ENNReal.ofReal (Real.sqrt D))^(n:ℝ)) ≤
    ENNReal.ofReal ((lineMomentBase C D branching*(n:ℝ))^n) := by
  have hlog : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
  have hQ : 0 ≤ ((branching+2)*(2*Real.sqrt D+4*(C*(4*Real.pi)^2)))/Real.log (3/2) := by
    positivity
  simpa only [lineMomentBase, mul_div_assoc] using
    ennreal_polynomial_moment_majorant _ _ hQ (Real.sqrt_nonneg D) n hn

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_DemodulatedVertical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Remove the vertical carrier before applying the interval Sobolev
estimate. The derivative norm is exactly the covariant derivative norm,
independently of the carrier frequencies and Hilbert dimension. -/

noncomputable section
open MeasureTheory

namespace LipschitzHilbert
open PhaseCombinatorics

theorem character_hasDerivAt (frequency y : ℝ) :
    HasDerivAt (character frequency) ((frequency:ℂ)*Complex.I*character frequency y) y := by
  have h := (((hasDerivAt_id y).const_mul frequency).ofReal_comp.mul_const Complex.I).cexp
  refine h.congr_deriv ?_
  · simp only [id_eq, mul_one]
    symm
    change (frequency:ℂ)*Complex.I*character frequency y =
      character frequency y*((frequency:ℂ)*Complex.I)
    ring

theorem demodulatedSignal_norm {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ) :
    ‖demodulatedSignal frequency f y‖ = ‖(WithLp.toLp 2 (fun k => f k y) : EuclideanSpace ℂ κ)‖ :=
  norm_diagonalModulation (fun k => -frequency k) (WithLp.toLp 2 (fun k => f k y)) y

theorem demodulatedSignal_hasDerivAt {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) y) :
    HasDerivAt (demodulatedSignal frequency f)
      (diagonalModulation (fun k => -frequency k) (covariantSignal frequency f y) y) y := by
  have hc : HasDerivAt (fun t k => f k t * character (-frequency k) t)
      (fun k => (deriv (f k) y - (frequency k:ℂ)*Complex.I*f k y) *
        character (-frequency k) y) y := by
    apply hasDerivAt_pi.mpr
    intro k
    have h := (hf k).hasDerivAt.mul (character_hasDerivAt (-frequency k) y)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℂ)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt y hc

theorem demodulatedSignal_deriv_norm {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (y : ℝ)
    (hf : ∀ k, DifferentiableAt ℝ (f k) y) :
    ‖deriv (demodulatedSignal frequency f) y‖ = ‖covariantSignal frequency f y‖ := by
  rw [(demodulatedSignal_hasDerivAt frequency f y hf).deriv, norm_diagonalModulation]

theorem demodulated_deriv_memLp {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) (μ : Measure ℝ)
    (hf : ∀ᵐ y ∂μ, ∀ k, DifferentiableAt ℝ (f k) y)
    (hD : MemLp (covariantSignal frequency f) 2 μ) :
    MemLp (deriv (demodulatedSignal frequency f)) 2 μ := by
  apply hD.congr_norm (aestronglyMeasurable_deriv _ μ)
  filter_upwards [hf] with y hy
  exact (demodulatedSignal_deriv_norm frequency f y hy).symm

theorem covariant_interval_energy {κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : κ → ℝ → ℂ) {a b : ℝ} (hab : a < b)
    (hf : ∀ y ∈ Set.Icc a b, ∀ k, DifferentiableAt ℝ (f k) y)
    (hD : MemLp (covariantSignal frequency f) 2 (volume.restrict (Set.Icc a b)))
    (V D : ℝ → ℝ) (hV : ContinuousOn V (Set.Icc a b)) (hDC : ContinuousOn D (Set.Icc a b))
    (hbV : ∀ y ∈ Set.Icc a b, ‖(WithLp.toLp 2 (fun k => f k y) : EuclideanSpace ℂ κ)‖ ≤ V y)
    (hbD : ∀ y ∈ Set.Icc a b, ‖covariantSignal frequency f y‖ ≤ D y)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ‖(WithLp.toLp 2 (fun k => f k x) : EuclideanSpace ℂ κ)‖^2 ≤
      verticalSquareEnergy (volume.restrict (Set.Icc a b)) V (fun t => (b-a)*D t) := by
  have hd := demodulated_deriv_memLp frequency f (volume.restrict (Set.Icc a b))
    ((ae_restrict_mem measurableSet_Icc).mono fun y hy => hf y hy) hD
  have h := interval_energy_domination (demodulatedSignal frequency f) hab
    (fun y hy => (demodulatedSignal_hasDerivAt frequency f y (hf y hy)).differentiableAt)
    hd V D hV hDC
    (fun y hy => by rw [demodulatedSignal_norm]; exact hbV y hy)
    (fun y hy => by rw [demodulatedSignal_deriv_norm frequency f y (hf y hy)]; exact hbD y hy) hx
  simpa only [demodulatedSignal_norm] using h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_TopNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform vertical neighborhoods for an entire family of sums, with
one measurable exceptional set and an explicit area moment bound. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem top_neighborhood_exceptional {α κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ)
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    (U : Set ℝ) (hU : MeasurableSet U) (c r threshold : ℝ)
    (hr : 0 < r) (hthreshold : 0 ≤ threshold) (n : ℕ) (C : ℝ≥0∞)
    (hline : ∀ y, (∫⁻ x in U, ENNReal.ofReal
      (V (y,x)^(2*n)+(4*r*D (y,x))^(2*n))) ≤ C)
    (hf : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) → ∀ k,
      DifferentiableAt ℝ (f i k x) y)
    (hmem : ∀ i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (c-2*r) (c+2*r))))
    (hbV : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ V (y,x))
    (hbD : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖covariantSignal frequency (fun k => f i k x) y‖ ≤ D (y,x)) :
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ U ×ˢ Icc (c-r) (c+r) ∧
      (ENNReal.ofReal threshold)^(2*n)*(volume.prod volume) bad ≤
        (4:ℝ≥0∞)^n*C*ENNReal.ofReal (2*r) ∧
      ∀ i x z v, x ∈ U → |z-c| ≤ r → |v| ≤ r → (x,z) ∉ bad →
        ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖ ≤ threshold := by
  let μ := volume.restrict (Icc (c-2*r) (c+2*r))
  let E : ℝ → ℝ := fun x => verticalSquareEnergy μ
    (fun y => V (y,x)) (fun y => 4*r*D (y,x))
  have hE : Measurable E := verticalSquareEnergy_measurable μ V
    (fun z => 4*r*D z) hV.measurable (hD.measurable.const_mul _)
  let B := {x | threshold^2 ≤ E x}
  have hB : MeasurableSet B := measurableSet_le measurable_const hE
  let bad := (U ∩ B) ×ˢ Icc (c-r) (c+r)
  have hmoment : (∫⁻ x in U, ENNReal.ofReal (E x)^n) ≤ (4:ℝ≥0∞)^n*C :=
    interval_vertical_moment (volume.restrict U) V (fun z => 4*r*D z) hV
      (hD.const_mul _) (by linarith : c-2*r < c+2*r) n C hline
  have hmark := energy_superlevel_moment (volume.restrict U) E hE threshold hthreshold n
    ((4:ℝ≥0∞)^n*C) hmoment
  change (ENNReal.ofReal threshold)^(2*n)*(volume.restrict U) B ≤ _ at hmark
  rw [Measure.restrict_apply hB, inter_comm B U] at hmark
  refine ⟨bad, (hU.inter hB).prod measurableSet_Icc, ?_, ?_, ?_⟩
  · exact prod_mono inter_subset_left Subset.rfl
  · change (ENNReal.ofReal threshold)^(2*n) *
      (volume.prod volume) ((U ∩ B) ×ˢ Icc (c-r) (c+r)) ≤ _
    rw [Measure.prod_prod, Real.volume_Icc, show c+r-(c-r)=2*r by ring, ← mul_assoc]
    exact mul_le_mul' hmark le_rfl
  · intro i x z v hx hz hv hout
    have hzi : z ∈ Icc (c-r) (c+r) := by
      rcases abs_le.mp hz with ⟨h1,h2⟩
      constructor <;> linarith
    have houtE : ¬ threshold^2 ≤ E x := fun he => hout ⟨⟨hx,he⟩,hzi⟩
    have hzv : z+v ∈ Icc (c-2*r) (c+2*r) := by
      rcases abs_le.mp hz with ⟨h1,h2⟩
      rcases abs_le.mp hv with ⟨h3,h4⟩
      constructor <;> linarith
    have hp := covariant_interval_energy frequency (fun k => f i k x)
      (by linarith : c-2*r < c+2*r) (fun y hy => hf i x y hy) (hmem i x)
      (fun y => V (y,x)) (fun y => D (y,x))
      (hV.comp (continuous_id.prodMk continuous_const)).continuousOn
      (hD.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun y hy => hbV i x y hy) (fun y hy => hbD i x y hy) hzv
    have hs : ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖^2 ≤ E x := by
      convert hp using 1
      all_goals try with_reducible_and_instances rfl
      dsimp only [E, μ]
      congr 1
      funext y
      ring
    have he := lt_of_not_ge houtE
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)]

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Estimates_NeighborhoodGeometric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common vertical-neighborhood exceptional set has exponentially
small area when the chosen even line moment has polynomial growth. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LipschitzHilbert

theorem quarter_area_of_even_moment (X M : ℝ≥0∞) (A : ℝ) (hA : 0 < A) (n : ℕ)
    (h : (ENNReal.ofReal (4*A))^(2*n)*X ≤ (ENNReal.ofReal (2*A))^(2*n)*M) :
    X ≤ (1/4:ℝ≥0∞)^n*M := by
  have ha0 : (ENNReal.ofReal (4*A))^(2*n) ≠ 0 :=
    pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  have hat : (ENNReal.ofReal (4*A))^(2*n) ≠ ⊤ := by finiteness
  have hr : ENNReal.ofReal (2*A)/ENNReal.ofReal (4*A) = (1/2:ℝ≥0∞) := by
    rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < 4*A)]
    have heq : (2*A)/(4*A) = (1/2:ℝ) := by field_simp [hA.ne']; norm_num
    rw [heq, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num [pow_two]
  calc
    X = ((ENNReal.ofReal (4*A))^(2*n))⁻¹ *
        ((ENNReal.ofReal (4*A))^(2*n)*X) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hat, one_mul]
    _ ≤ ((ENNReal.ofReal (4*A))^(2*n))⁻¹ *
        ((ENNReal.ofReal (2*A))^(2*n)*M) := mul_le_mul' le_rfl h
    _ = (ENNReal.ofReal (2*A)/ENNReal.ofReal (4*A))^(2*n)*M := by
      rw [ENNReal.div_eq_inv_mul, mul_pow, ENNReal.inv_pow]
      ring
    _ = _ := by
      have hquarter : (1/2:ℝ≥0∞)^2 = 1/4 := by
        rw [ENNReal.div_eq_inv_mul, mul_one, ← ENNReal.inv_pow]
        norm_num [pow_two]
      rw [hr, pow_mul, hquarter]

theorem top_neighborhood_geometric {α κ : Type*} [Fintype κ]
    (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ)
    (V D : ℝ × ℝ → ℝ) (hV : Continuous V) (hD : Continuous D)
    (U : Set ℝ) (hU : MeasurableSet U) (c r A : ℝ)
    (hr : 0 < r) (hA : 0 < A) (n : ℕ) (M : ℝ≥0∞)
    (hline : ∀ y, (∫⁻ x in U, ENNReal.ofReal
      (V (y,x)^(2*n)+(4*r*D (y,x))^(2*n))) ≤ 2*(ENNReal.ofReal A)^(2*n)*M)
    (hf : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) → ∀ k,
      DifferentiableAt ℝ (f i k x) y)
    (hmem : ∀ i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (c-2*r) (c+2*r))))
    (hbV : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ V (y,x))
    (hbD : ∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
      ‖covariantSignal frequency (fun k => f i k x) y‖ ≤ D (y,x)) :
    ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ U ×ˢ Icc (c-r) (c+r) ∧
      (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*M*ENNReal.ofReal (2*r) ∧
      ∀ i x z v, x ∈ U → |z-c| ≤ r → |v| ≤ r → (x,z) ∉ bad →
        ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖ ≤ 4*A := by
  obtain ⟨bad,hbad,hsub,harea,hpoint⟩ := top_neighborhood_exceptional frequency f V D hV hD U hU
    c r (4*A) hr (by positivity) n (2*(ENNReal.ofReal A)^(2*n)*M) hline hf hmem hbV hbD
  refine ⟨bad,hbad,hsub,?_,hpoint⟩
  have heq : (4:ℝ≥0∞)^n*(2*(ENNReal.ofReal A)^(2*n)*M)*ENNReal.ofReal (2*r) =
      (ENNReal.ofReal (2*A))^(2*n)*(2*M*ENNReal.ofReal (2*r)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    simp only [ENNReal.ofReal_ofNat, pow_mul]
    norm_num
    ring
  have h := quarter_area_of_even_moment ((volume.prod volume) bad)
    (2*M*ENNReal.ofReal (2*r)) A hA n (harea.trans_eq heq)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Fourier_FiniteBandDerivative
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical differentiation commutes with the actual finite band sums.
The covariant derivative uses the same carrier in every band of a fixed
coordinate, so no carrier-frequency factor is lost. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

theorem scalarBandPartial_hasDerivAt {N : ℕ} (F : Fin N → ℝ → ℂ)
    (n : ℕ) (y : ℝ) (hF : ∀ j, DifferentiableAt ℝ (F j) y) :
    HasDerivAt (scalarBandPartial F n)
      (scalarBandPartial (fun j => deriv (F j)) n y) y := by
  apply HasDerivAt.fun_sum
  intro j _
  by_cases hj : j.val < n
  · simpa only [hj, ite_true, if_true] using (hF j).hasDerivAt
  · simpa only [hj, ite_false, if_false] using (hasDerivAt_const y (0:ℂ))

theorem scalarBandPartial_covariant {N : ℕ} (F : Fin N → ℝ → ℂ)
    (n : ℕ) (frequency y : ℝ) (hF : ∀ j, DifferentiableAt ℝ (F j) y) :
    deriv (scalarBandPartial F n) y - (frequency:ℂ)*Complex.I*scalarBandPartial F n y =
      scalarBandPartial (fun j t => deriv (F j) t-(frequency:ℂ)*Complex.I*F j t) n y := by
  rw [(scalarBandPartial_hasDerivAt F n y hF).deriv]
  unfold scalarBandPartial
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem bandIntervalSignal_covariant {N : ℕ} {κ : Type*} [Fintype κ]
    (F : Fin N → κ → ℝ → ℂ) (a b : ℕ) (frequency : κ → ℝ) (y : ℝ)
    (hF : ∀ j k, DifferentiableAt ℝ (F j k) y) :
    covariantSignal frequency (fun k t => bandIntervalSignal F a b t k) y =
      bandIntervalSignal (fun j k t => deriv (F j k) t-
        (frequency k:ℂ)*Complex.I*F j k t) a b y := by
  ext k
  change deriv (fun t => scalarBandPartial (fun j => F j k) b t -
      scalarBandPartial (fun j => F j k) a t) y -
      (frequency k:ℂ)*Complex.I*(scalarBandPartial (fun j => F j k) b y -
        scalarBandPartial (fun j => F j k) a y) = _
  have hd := (scalarBandPartial_hasDerivAt (fun j => F j k) b y (fun j => hF j k)).sub
    (scalarBandPartial_hasDerivAt (fun j => F j k) a y (fun j => hF j k))
  change HasDerivAt (fun t => scalarBandPartial (fun j => F j k) b t -
    scalarBandPartial (fun j => F j k) a t) _ y at hd
  rw [hd.deriv]
  have hb := scalarBandPartial_covariant (fun j => F j k) b (frequency k) y (fun j => hF j k)
  have ha := scalarBandPartial_covariant (fun j => F j k) a (frequency k) y (fun j => hF j k)
  change _ = scalarBandPartial _ b y - scalarBandPartial _ a y
  rw [← hb, ← ha]
  rw [(scalarBandPartial_hasDerivAt (fun j => F j k) b y (fun j => hF j k)).deriv,
    (scalarBandPartial_hasDerivAt (fun j => F j k) a y (fun j => hF j k)).deriv]
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_UniformAnalyzedLine
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform local budgets for the actual analyzing coefficients. The
constant is fixed before the finite Hilbert and scale index types. -/

noncomputable section
open MeasureTheory
open scoped BigOperators FourierTransform ENNReal

namespace LipschitzHilbert.PlanarPacketFamily

theorem uniform_analyzedLine_localBudget (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
      (y : ℝ)
      (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant / P.length j) *
        (lineEnvelope (P.centerX j i) (P.length j) 3 x *
         lineEnvelope (P.centerZ j i) P.width 2 y)),
      Monotone d →
      (∀ j i k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      (P.analyzedLine d v hv g hg hg1 y hderiv).HasLocalBudget
        (A * P.constant^2 * P.coefficientScale⁻¹^2) := by
  obtain ⟨A,hA,hbudget⟩ := mainCoefficient_localBudget hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 y hderiv hd hlow hhigh u r hr b
  have h := hbudget N κ ι P d v g hd hv hg hg1 hlow hhigh u y r hr b
  change (∑ j, P.length j * ∑ i : P.BoxFiber u y r b j,
    ‖P.coefficientScale⁻¹ • P.mainCoefficient d v g j i‖^2) ≤ _
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr P.coefficientScale_pos), mul_pow]
  calc
    _ = P.coefficientScale⁻¹^2 *
        (∑ j, P.length j * ∑ i : P.BoxFiber u y r b j, ‖P.mainCoefficient d v g j i‖^2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ P.coefficientScale⁻¹^2 * (A * P.constant^2 * r) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by ring


end LipschitzHilbert.PlanarPacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_AnalyzedReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Replacement synthesis packets retain the local budget of the actual
integral-defined analyzing coefficients. The same coefficient budget applies to top weights and covariant
derivative packets. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace LipschitzHilbert.PlanarPacketFamily
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem uniform_analyzedReplacement_budget (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
      (y : ℝ) (hderiv : ∀ j i k x, ‖deriv (P.wave j i k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j i) (P.length j) 3 x *
          lineEnvelope (P.centerZ j i) P.width 2 y)),
      Monotone d →
      (∀ j i k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k y) ξ = 0) →
      (∀ j i k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k y) ξ = 0) →
      ∀ C hC wave hb hdb,
      (P.analyzedReplacement d v hv g hg hg1 y hderiv C hC wave hb hdb).HasLocalBudget
        (A*P.constant^2*P.coefficientScale⁻¹^2) := by
  obtain ⟨A,hA,hbudget⟩ := uniform_analyzedLine_localBudget hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 y hderiv hd hlo' hhi' C hC wave hb hdb
  exact hbudget N κ ι P d v hv g hg hg1 y hderiv hd hlo' hhi'

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketDifferentiation
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact vertical derivatives of packet syntheses. Coefficients stay
fixed during differentiation, including when they are analyzing integrals. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketBand_hasDerivAt (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (j : Fin N) (k : κ) (x y : ℝ)
    (hw : ∀ i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    HasDerivAt (planarPacketBand coeff wave j k x)
      (∑ i, coeff j i k * deriv (fun t => wave j i k t x) y) y := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (hw i).hasDerivAt.const_mul _

omit [Fintype κ] in
theorem planarPacketBand_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (j : Fin N) (k : κ) (x y : ℝ)
    (hw : ∀ i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    deriv (planarPacketBand coeff wave j k x) y -
      (frequency k:ℂ)*Complex.I*planarPacketBand coeff wave j k x y =
    planarPacketBand coeff
      (fun j i k t s => deriv (fun z => wave j i k z s) t -
        (frequency k:ℂ)*Complex.I*wave j i k t s) j k x y := by
  rw [(planarPacketBand_hasDerivAt coeff wave j k x y hw).deriv]
  unfold planarPacketBand
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype κ] in
theorem planarPacketInterval_smul (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (s : ℝ) (a b : ℕ) (x y : ℝ) :
    planarPacketInterval coeff (fun j i k t z => (s:ℂ)*wave j i k t z) a b x y =
      s • planarPacketInterval coeff wave a b x y := by
  have hs (j : Fin N) (k : κ) :
      planarPacketBand coeff (fun j i k t z => (s:ℂ)*wave j i k t z) j k x y =
        (s:ℂ)*planarPacketBand coeff wave j k x y := by
    simp only [planarPacketBand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp (n : ℕ) (k : κ) :
      scalarBandPartial (fun j => planarPacketBand coeff
        (fun j i k t z => (s:ℂ)*wave j i k t z) j k x) n y =
      (s:ℂ)*scalarBandPartial (fun j => planarPacketBand coeff wave j k x) n y := by
    simp only [scalarBandPartial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp only [hs, mul_zero]
  ext k
  change _ = (s:ℂ)*(_-_)
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp, hp, mul_sub]

theorem planarPacketInterval_covariant (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (a b : ℕ) (x y : ℝ)
    (hw : ∀ j i k t, DifferentiableAt ℝ (fun z => wave j i k z x) t) :
    covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y =
    planarPacketInterval coeff
      (fun j i k t s => deriv (fun z => wave j i k z s) t -
        (frequency k:ℂ)*Complex.I*wave j i k t s) a b x y := by
  unfold planarPacketInterval
  rw [bandIntervalSignal_covariant _ _ _ _ _ (fun j k =>
    (planarPacketBand_hasDerivAt coeff wave j k x y (fun i => hw j i k y)).differentiableAt)]
  congr 1
  funext j k t
  exact planarPacketBand_covariant coeff wave frequency j k x t
    (fun i => hw j i k t)

theorem planarPacketInterval_eq_partial_difference
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (P : LinePacketFamily N κ ι)
    (y : ℝ) (hc : ∀ j i, coeff j i = P.coeff j i)
    (hw : ∀ j i k x, wave j i k y x = P.wave j i k x) (a b : ℕ) (x : ℝ) :
    planarPacketInterval coeff wave a b x y =
      hilbertPartialBandSum P.packets b x - hilbertPartialBandSum P.packets a x := by
  have hs (j : Fin N) (k : κ) : planarPacketBand coeff wave j k x y = P.packets j k x := by
    simp only [planarPacketBand, hc, hw, LinePacketFamily.packets, packetSynthesis_apply]
  ext k
  simp only [planarPacketInterval, bandIntervalSignal, WithLp.ofLp_toLp,
    WithLp.ofLp_sub, Pi.sub_apply, hilbertPartialBandSum, scalarBandPartial,
    partialBandSum, hs]

theorem planarPacketInterval_norm_le
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (P : LinePacketFamily N κ ι)
    (y : ℝ) (hc : ∀ j i, coeff j i = P.coeff j i)
    (hw : ∀ j i k x, wave j i k y x = P.wave j i k x)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) (x : ℝ) :
    ‖planarPacketInterval coeff wave a b x y‖ ≤ P.variation x := by
  rw [planarPacketInterval_eq_partial_difference coeff wave P y hc hw]
  exact increment_le_cubicVariation (fun n => hilbertPartialBandSum P.packets n x) N a b hab hb

theorem planarPacketInterval_scaled_covariant_norm_le
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (P : LinePacketFamily N κ ι)
    (frequency : κ → ℝ) (s y : ℝ) (hs : 0 ≤ s)
    (hc : ∀ j i, coeff j i = P.coeff j i)
    (hw : ∀ j i k x, (s:ℂ)*(deriv (fun t => wave j i k t x) y -
      (frequency k:ℂ)*Complex.I*wave j i k y x) = P.wave j i k x)
    (hd : ∀ j i k x t, DifferentiableAt ℝ (fun z => wave j i k z x) t)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) (x : ℝ) :
    s*‖covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) y‖ ≤
      P.variation x := by
  have h := planarPacketInterval_norm_le coeff
    (fun j i k t z => (s:ℂ)*(deriv (fun u => wave j i k u z) t -
      (frequency k:ℂ)*Complex.I*wave j i k t z)) P y hc hw a b hab hb x
  rw [planarPacketInterval_smul, ← planarPacketInterval_covariant coeff wave frequency a b x y
    (fun j i k => hd j i k x), norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] at h
  exact h

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_PlanarPacketContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint continuity and local square integrability for actual packet
interval sums and their covariant derivatives. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace LipschitzHilbert
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

omit [Fintype κ] in
theorem planarPacketBand_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2))
    (j : Fin N) (k : κ) :
    Continuous (fun z : ℝ × ℝ => planarPacketBand coeff wave j k z.2 z.1) := by
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hw j i k))

omit [Fintype κ] in
theorem planarPacketPartial_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2)) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => (WithLp.toLp 2 (fun k =>
      scalarBandPartial (fun j => planarPacketBand coeff wave j k z.2) n z.1) :
        EuclideanSpace ℂ κ)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [hj, ite_true, if_true] using planarPacketBand_continuous coeff wave hw j k
  · simpa only [hj, ite_false, if_false] using (continuous_const : Continuous (fun _ : ℝ × ℝ => (0:ℂ)))

theorem planarPacketInterval_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2)) (a b : ℕ) :
    Continuous (fun z : ℝ × ℝ => planarPacketInterval coeff wave a b z.2 z.1) := by
  convert (planarPacketPartial_continuous coeff wave hw b).sub
    (planarPacketPartial_continuous coeff wave hw a) using 1
  all_goals try with_reducible_and_instances rfl
  ext z k
  rfl

theorem lineFamily_variation_continuous (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (P : ℝ → LinePacketFamily N κ ι)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2))
    (hcoeff : ∀ y j i, coeff j i = (P y).coeff j i)
    (hwave : ∀ y j i k x, wave j i k y x = (P y).wave j i k x) :
    Continuous (fun z : ℝ × ℝ => (P z.1).variation z.2) := by
  have heq (z : ℝ × ℝ) (n : ℕ) :
      hilbertPartialBandSum (P z.1).packets n z.2 =
        WithLp.toLp 2 (fun k => scalarBandPartial
          (fun j => planarPacketBand coeff wave j k z.2) n z.1) := by
    ext k
    simp only [hilbertPartialBandSum, WithLp.ofLp_toLp, partialBandSum,
      scalarBandPartial, LinePacketFamily.packets, packetSynthesis_apply,
      planarPacketBand, hcoeff z.1, hwave z.1]
  simp_rw [LinePacketFamily.variation, heq]
  exact continuous_cubicVariation _ (planarPacketPartial_continuous coeff wave hw) N

theorem planarPacketInterval_memLp (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ)
    (hw : ∀ j i k, Continuous (fun z : ℝ × ℝ => wave j i k z.1 z.2))
    (a b : ℕ) (x lower upper : ℝ) :
    MemLp (planarPacketInterval coeff wave a b x) 2 (volume.restrict (Icc lower upper)) := by
  have hplane := planarPacketInterval_continuous coeff wave hw a b
  have hc := hplane.comp (f := fun y : ℝ => (y,x))
    (continuous_id.prodMk continuous_const)
  change Continuous (planarPacketInterval coeff wave a b x) at hc
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (hc.norm.pow 2).continuousOn.integrableOn_Icc

omit [Fintype κ] in
theorem planarPacketInterval_component_differentiable
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (a b : ℕ) (x y : ℝ) (k : κ)
    (hd : ∀ j i, DifferentiableAt ℝ (fun t => wave j i k t x) y) :
    DifferentiableAt ℝ (fun t => planarPacketInterval coeff wave a b x t k) y := by
  change DifferentiableAt ℝ (fun t =>
    scalarBandPartial (fun j => planarPacketBand coeff wave j k x) b t -
    scalarBandPartial (fun j => planarPacketBand coeff wave j k x) a t) y
  have hb (n : ℕ) := (scalarBandPartial_hasDerivAt
    (fun j => planarPacketBand coeff wave j k x) n y (fun j =>
      (planarPacketBand_hasDerivAt coeff wave j k x y (hd j)).differentiableAt)).differentiableAt
  exact (hb b).sub (hb a)

theorem planarPacketInterval_covariant_memLp
    (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
    (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
    (hd : ∀ j i k x t, DifferentiableAt ℝ (fun z => wave j i k z x) t)
    (hD : ∀ j i k, Continuous (fun z : ℝ × ℝ =>
      deriv (fun t => wave j i k t z.2) z.1 - (frequency k:ℂ)*Complex.I*wave j i k z.1 z.2))
    (a b : ℕ) (x lower upper : ℝ) :
    MemLp (covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k))
      2 (volume.restrict (Icc lower upper)) := by
  let D := fun j i k t s => deriv (fun z => wave j i k z s) t -
    (frequency k:ℂ)*Complex.I*wave j i k t s
  have heq : covariantSignal frequency (fun k t => planarPacketInterval coeff wave a b x t k) =
      fun y => planarPacketInterval coeff D a b x y := by
    funext y
    exact planarPacketInterval_covariant coeff wave frequency a b x y (fun j i k => hd j i k x)
  have hDc : ∀ j i k, Continuous (fun z : ℝ × ℝ => D j i k z.1 z.2) := hD
  rw [heq]
  exact planarPacketInterval_memLp coeff D hDc a b x lower upper

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Empty initial scales impose no lower bound on the reference window.
The root moment estimates need only contain the lengths of actual
retained packets. This is the situation for the fixed short reference
collection in §8. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal FourierTransform
namespace LipschitzHilbert.LinePacketFamily
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : LinePacketFamily N κ ι)

theorem shortPackets_eq_of_supported (r : ℝ) (hr : ∀ j (_u : ι j), P.length j ≤ r) :
    P.shortPackets r = P.packets := by
  funext j k
  by_cases hj : P.length j ≤ r
  · exact ite_eq_left hj
  · have : IsEmpty (ι j) := ⟨fun u => hj (hr j u)⟩
    simp [shortPackets,hj,packets,packetSynthesis]

theorem root_square_bound_of_supported (grid : FiniteLineGrid)
    (hwidth : ∀ j (_u : ι j), P.length j ≤ grid.width) {D : ℝ}
    (hshort : ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N)^2) ≤ D*r) :
    (∫ x, P.variation x^2 ∂grid.lineMeasure) ≤ D*grid.width := by
  have hs := hshort grid.origin grid.width grid.width_pos
  rw [P.shortPackets_eq_of_supported grid.width hwidth] at hs
  have hsub : grid.root ⊆ Icc (grid.origin-grid.width) (grid.origin+grid.width) := by
    intro x hx
    exact ⟨by linarith [hx.1,grid.width_pos],hx.2.le⟩
  have hi : IntegrableOn (fun x => P.variation x^2)
      (Icc (grid.origin-grid.width) (grid.origin+grid.width)) :=
    (P.continuous_variation.pow 2).continuousOn.integrableOn_Icc
  exact (setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun x => sq_nonneg (P.variation x)))
    (Filter.Eventually.of_forall (fun _ hx => hsub hx))).trans hs

theorem mean_bound_of_supported (grid : FiniteLineGrid)
    (hwidth : ∀ j (_u : ι j), P.length j ≤ grid.width) {D : ℝ} (hD : 0 ≤ D)
    (hshort : ∀ u r : ℝ, 0 < r →
      (∫ x in Icc (u-r) (u+r),
        (cubicVariation (fun n => hilbertPartialBandSum (P.shortPackets r) n x) N)^2) ≤ D*r) :
    |integralAverage grid.lineMeasure P.variation| ≤ Real.sqrt (D+1) := by
  have hv : Integrable P.variation grid.lineMeasure := by
    have h := grid.continuous_integrable_cell P.continuous_variation 0 0
    rw [grid.cell_zero] at h
    exact h
  have hv2 : Integrable (fun x => P.variation x^2) grid.lineMeasure := by
    have h := grid.continuous_integrable_cell (P.continuous_variation.pow 2) 0 0
    rw [grid.cell_zero] at h
    exact h
  have hmass : grid.lineMeasure.real univ = grid.width := by
    change (volume.restrict grid.root).real univ = grid.width
    simpa only [grid.cell_zero,FiniteLineGrid.meshWidth,pow_zero,div_one] using grid.cell_mass 0 0
  have hroot := P.root_square_bound_of_supported grid hwidth hshort
  have hsq : (∫ x, P.variation x^2 ∂grid.lineMeasure) ≤
      (Real.sqrt (D+1))^2*grid.lineMeasure.real univ := by
    rw [Real.sq_sqrt (by linarith : 0 ≤ D+1),hmass]
    nlinarith [grid.width_pos]
  have hmean := integral_le_of_square_mean_bound grid.lineMeasure P.variation hv hv2
    (Real.sqrt_pos.mpr (by linarith)) hsq
  have hnonneg : 0 ≤ integralAverage grid.lineMeasure P.variation := by
    unfold integralAverage
    exact smul_nonneg (inv_nonneg.mpr measureReal_nonneg)
      (integral_nonneg (fun _ => cubicVariation_nonneg _ _))
  rw [abs_of_nonneg hnonneg,integralAverage,smul_eq_mul]
  calc
    _ ≤ (grid.lineMeasure.real univ)⁻¹*(Real.sqrt (D+1)*grid.lineMeasure.real univ) :=
      mul_le_mul_of_nonneg_left hmean (inv_nonneg.mpr measureReal_nonneg)
    _ = _ := by rw [hmass]; field_simp [grid.width_pos.ne']

/-- The published-input constant is uniform before choosing the finite
packet family. The reference window contains only the retained lengths. -/
theorem uniform_line_moment_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : LinePacketFamily N κ ι) (B : ℝ),
      0 ≤ B → P.HasLocalBudget B →
      (∀ j i k xi, |xi| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k) xi = 0) →
      (∀ j i k xi, hi*(2:ℝ)^j.val < |xi| → 𝓕 (P.wave j i k) xi = 0) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ j (_u : ι j), P.length j ≤ grid.width) → ∀ p : ℝ, 0 ≤ p →
      (∫⁻ x, (ENNReal.ofReal |P.variation x|)^p ∂grid.lineMeasure) ≤
        (2:ℝ≥0∞)^p*(7*ENNReal.ofReal ((p*(((grid.branching:ℝ)+2)*
          (2*Real.sqrt (A*P.constant^2*B+1)+4*(P.constant*(4*Real.pi)^2)))/
            Real.log (3/2))^p)+
          (ENNReal.ofReal (Real.sqrt (A*P.constant^2*B+1)))^p)*grid.lineMeasure univ := by
  obtain ⟨A,hA,hshort⟩ := uniform_short_energy hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P B hB hbudget hlow hhigh grid hb hwidth p hp
  have hD : 0 ≤ A*P.constant^2*B := by positivity
  have hs := hshort N κ ι P B hB hbudget hlow hhigh
  have hpos : 0 < 2*Real.sqrt (A*P.constant^2*B+1)+4*(P.constant*(4*Real.pi)^2) := by
    have hC := P.constant_pos
    positivity
  have hint : Integrable P.variation grid.lineMeasure := by
    have h := grid.continuous_integrable_cell P.continuous_variation 0 0
    rw [grid.cell_zero] at h
    exact h
  exact grid.continuous_raw_moment hb P.variation P.continuous_variation.measurable hint
    (fun _ _ => P.continuous_variation.continuousAt) hpos
    (P.full_mean_oscillation grid hD hs) (P.mean_bound_of_supported grid hwidth hD hs) hp

end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedPolynomialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory
open scoped FourierTransform ENNReal

namespace LipschitzHilbert.LinePacketFamily

theorem uniform_polynomial_line_moment_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : LinePacketFamily N κ ι) (B : ℝ),
      0 ≤ B → P.HasLocalBudget B →
      (∀ j i k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j i k) ξ = 0) →
      (∀ j i k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j i k) ξ = 0) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching → (∀ j (_u : ι j), P.length j ≤ grid.width) →
      ∀ n : ℕ, 1 ≤ n →
      (∫⁻ x, ENNReal.ofReal (P.variation x)^n ∂grid.lineMeasure) ≤
        ENNReal.ofReal ((lineMomentBase P.constant (A*P.constant^2*B+1)
          grid.branching*(n:ℝ))^n)*grid.lineMeasure Set.univ := by
  obtain ⟨A,hA,hm⟩ := uniform_line_moment_of_supported hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ P B hB hbudget hlow hhigh grid hb hwidth n hn
  have h := hm N κ ι P B hB hbudget hlow hhigh grid hb hwidth n (Nat.cast_nonneg n)
  have hp := line_moment_expression_le P.constant (A*P.constant^2*B+1) grid.branching
    P.constant_pos.le (Nat.cast_nonneg _) n hn
  have hs := h.trans (mul_le_mul' hp le_rfl)
  have hnonneg (x : ℝ) : 0 ≤ P.variation x := cubicVariation_nonneg _ _
  simpa only [ENNReal.rpow_natCast, abs_of_nonneg (hnonneg _)] using hs

end LipschitzHilbert.LinePacketFamily

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedLineNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal

namespace LipschitzHilbert

theorem uniform_line_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (α : Type)
      (P : Fin 2 → ℝ → LinePacketFamily N κ ι) (C B : ℝ),
      0 < C → 0 ≤ B →
      (∀ i y, (P i y).constant = C) →
      (∀ i y, (P i y).HasLocalBudget B) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 ((P i y).wave j u k) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 ((P i y).wave j u k) ξ = 0) →
      (∀ i, Continuous (fun z : ℝ × ℝ => (P i z.1).variation z.2)) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ i y j (_u : ι j), (P i y).length j ≤ grid.width) →
      ∀ (frequency : κ → ℝ) (f : α → κ → ℝ → ℝ → ℂ) (c r : ℝ), 0 < r →
      (∀ i x y, y ∈ Icc (c-2*r) (c+2*r) → ∀ k, DifferentiableAt ℝ (f i k x) y) →
      (∀ i x, MemLp (covariantSignal frequency (fun k => f i k x)) 2
        (volume.restrict (Icc (c-2*r) (c+2*r)))) →
      (∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
        ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ (P 0 y).variation x) →
      (∀ i x y, y ∈ Icc (c-2*r) (c+2*r) →
        (4*r)*‖covariantSignal frequency (fun k => f i k x) y‖ ≤ (P 1 y).variation x) →
      ∀ n : ℕ, 1 ≤ n →
      let K := lineMomentBase C (A*C^2*B+1) grid.branching
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        bad ⊆ grid.root ×ˢ Icc (c-r) (c+r) ∧
        (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*grid.lineMeasure univ*ENNReal.ofReal (2*r) ∧
        ∀ i x z v, x ∈ grid.root → |z-c| ≤ r → |v| ≤ r → (x,z) ∉ bad →
          ‖(WithLp.toLp 2 (fun k => f i k x (z+v)) : EuclideanSpace ℂ κ)‖ ≤ 8*K*(n:ℝ) := by
  obtain ⟨A,hA,hm⟩ := LinePacketFamily.uniform_polynomial_line_moment_of_supported hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ α P C B hC hB hconstant hbudget hlow hhigh hcont grid hb hwidth
    frequency f c r hr hf hmem hV hD n hn
  dsimp only
  let K := lineMomentBase C (A*C^2*B+1) grid.branching
  have hK : 0 < K := lineMomentBase_pos _ _ _ hC.le (Nat.cast_nonneg _)
  have hnR : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hn)
  have hr4 : 0 < 4*r := by positivity
  let V : ℝ × ℝ → ℝ := fun z => (P 0 z.1).variation z.2
  let D : ℝ × ℝ → ℝ := fun z => (P 1 z.1).variation z.2/(4*r)
  have hscale (y x : ℝ) : 4*r*D (y,x) = (P 1 y).variation x := by
    dsimp [D]
    field_simp
  have hline (y : ℝ) : (∫⁻ x in grid.root, ENNReal.ofReal
      (V (y,x)^(2*n)+(4*r*D (y,x))^(2*n))) ≤
        2*(ENNReal.ofReal (K*(2*n:ℕ)))^(2*n)*grid.lineMeasure univ := by
    have hmoment (i : Fin 2) := hm N κ ι (P i y) B hB (hbudget i y)
      (hlow i y) (hhigh i y) grid hb (hwidth i y) (2*n) (by omega)
    have hv0 (x : ℝ) : 0 ≤ (P 0 y).variation x := cubicVariation_nonneg _ _
    have hv1 (x : ℝ) : 0 ≤ (P 1 y).variation x := cubicVariation_nonneg _ _
    simp_rw [hscale, V, ENNReal.ofReal_add (pow_nonneg (hv0 _) _) (pow_nonneg (hv1 _) _),
      ENNReal.ofReal_pow (hv0 _), ENNReal.ofReal_pow (hv1 _)]
    rw [lintegral_add_left ((P 0 y).continuous_variation.measurable.ennreal_ofReal.pow_const _)]
    have h0 := hmoment 0
    have h1 := hmoment 1
    rw [hconstant] at h0 h1
    change (∫⁻ x, _ ∂grid.lineMeasure) + (∫⁻ x, _ ∂grid.lineMeasure) ≤ _
    calc
      _ ≤ 2*ENNReal.ofReal ((K*(2*n:ℕ))^(2*n))*grid.lineMeasure univ := by
        have hsum := add_le_add h0 h1
        convert hsum using 1
        all_goals try with_reducible_and_instances rfl
        ring
      _ = _ := by rw [ENNReal.ofReal_pow (by positivity)]
  obtain ⟨bad,hbad,hsub,harea,hpoint⟩ := top_neighborhood_geometric frequency f V D
    (hcont 0) ((hcont 1).div_const _) grid.root measurableSet_Ico c r (K*(2*n:ℕ))
    hr (by positivity) n (grid.lineMeasure univ) hline hf hmem hV
    (by
      intro i x y hy
      apply (le_div_iff₀ hr4).mpr
      simpa only [mul_comm] using hD i x y hy)
  refine ⟨bad,hbad,hsub,harea,?_⟩
  intro i x z v hx hz hv hout
  convert hpoint i x z v hx hz hv hout using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedPacketNeighborhood
attribute [-instance] _root_.OAI.LipschitzHilbert.SourceLabeledLattice.slotItemFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal

namespace LipschitzHilbert

theorem packet_interval_neighborhood_of_supported (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)]
      (coeff : ∀ j, ι j → EuclideanSpace ℂ κ)
      (wave : ∀ j, ι j → κ → ℝ → ℝ → ℂ) (frequency : κ → ℝ)
      (P : Fin 2 → ℝ → LinePacketFamily N κ ι) (C B c r : ℝ),
      0 < C → 0 ≤ B → 0 < r →
      (∀ i y, (P i y).constant = C) →
      (∀ i y, (P i y).HasLocalBudget B) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 ((P i y).wave j u k) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 ((P i y).wave j u k) ξ = 0) →
      (∀ i y j u, coeff j u = (P i y).coeff j u) →
      (∀ y j u k x, wave j u k y x = (P 0 y).wave j u k x) →
      (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => wave j u k t x) y -
        (frequency k:ℂ)*Complex.I*wave j u k y x) = (P 1 y).wave j u k x) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ => wave j u k z.1 z.2)) →
      (∀ j u k x t, DifferentiableAt ℝ (fun y => wave j u k y x) t) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ =>
        deriv (fun t => wave j u k t z.2) z.1 -
          (frequency k:ℂ)*Complex.I*wave j u k z.1 z.2)) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching →
      (∀ i y j (_u : ι j), (P i y).length j ≤ grid.width) →
      ∀ n : ℕ, 1 ≤ n →
      let K := lineMomentBase C (A*C^2*B+1) grid.branching
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ grid.root ×ˢ Icc (c-r) (c+r) ∧
        (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*grid.lineMeasure univ*ENNReal.ofReal (2*r) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z v,
          x ∈ grid.root → |z-c| ≤ r → |v| ≤ r → (x,z) ∉ bad →
          ‖planarPacketInterval coeff wave a b x (z+v)‖ ≤ 8*K*(n:ℝ) := by
  obtain ⟨A,hA,htop⟩ := uniform_line_neighborhood_of_supported hL hlo hhi
  refine ⟨A,hA,?_⟩
  intro N κ ι _ _ coeff wave frequency P C B c r hC hB hr hconstant hbudget
    hlow hhigh hcoeff hwave hcov hcont hdiff hD grid hb hwidth n hn
  dsimp only
  let α := {p : ℕ × ℕ // p.1 ≤ p.2 ∧ p.2 ≤ N}
  let f : α → κ → ℝ → ℝ → ℂ := fun i k x y =>
    planarPacketInterval coeff wave i.val.1 i.val.2 x y k
  have hregular (i : Fin 2) : Continuous (fun z : ℝ × ℝ => (P i z.1).variation z.2) := by
    fin_cases i
    · exact lineFamily_variation_continuous coeff wave (P 0) hcont (hcoeff 0) hwave
    · apply lineFamily_variation_continuous coeff
        (fun j u k y x => (4*r:ℂ)*(deriv (fun t => wave j u k t x) y -
          (frequency k:ℂ)*Complex.I*wave j u k y x)) (P 1)
      · intro j u k
        exact continuous_const.mul (hD j u k)
      · exact hcoeff 1
      · exact hcov
  have hf (i : α) (x y : ℝ) (_hy : y ∈ Icc (c-2*r) (c+2*r)) (k : κ) :
      DifferentiableAt ℝ (f i k x) y :=
    planarPacketInterval_component_differentiable coeff wave _ _ x y k (fun j u => hdiff j u k x y)
  have hmem (i : α) (x : ℝ) : MemLp (covariantSignal frequency (fun k => f i k x)) 2
      (volume.restrict (Icc (c-2*r) (c+2*r))) :=
    planarPacketInterval_covariant_memLp coeff wave frequency hdiff hD _ _ x _ _
  have hv (i : α) (x y : ℝ) (_hy : y ∈ Icc (c-2*r) (c+2*r)) :
      ‖(WithLp.toLp 2 (fun k => f i k x y) : EuclideanSpace ℂ κ)‖ ≤ (P 0 y).variation x := by
    change ‖planarPacketInterval coeff wave i.val.1 i.val.2 x y‖ ≤ _
    exact planarPacketInterval_norm_le coeff wave (P 0 y) y (hcoeff 0 y) (hwave y)
      _ _ i.property.1 i.property.2 x
  have hd (i : α) (x y : ℝ) (_hy : y ∈ Icc (c-2*r) (c+2*r)) :
      4*r*‖covariantSignal frequency (fun k => f i k x) y‖ ≤ (P 1 y).variation x :=
    planarPacketInterval_scaled_covariant_norm_le coeff wave (P 1 y) frequency (4*r) y
      (by positivity) (hcoeff 1 y) (by simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hcov y)
      hdiff _ _ i.property.1 i.property.2 x
  obtain ⟨bad,hbad,hsub,harea,hpoint⟩ := htop N κ ι α P C B hC hB hconstant hbudget
    hlow hhigh hregular grid hb hwidth frequency f c r hr hf hmem hv hd n hn
  refine ⟨bad,hbad,hsub,harea,?_⟩
  intro a b hab hbn x z v hx hz hv hout
  exact hpoint ⟨(a,b),hab,hbn⟩ x z v hx hz hv hout

end LipschitzHilbert

end

end OAI
end

section
-- module Solutions.OAIQ090_LH.LipschitzHilbert_Packets_SourceSupportedAnalyzedNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The source neighborhood estimate needs only the lengths of actual packets.
Empty scales impose no condition on the reference window; all constants are unchanged. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform ENNReal

namespace LipschitzHilbert.PlanarPacketFamily

theorem analyzed_interval_neighborhood_of_supported_oai (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) :
    ∃ Ab Am : ℝ, 0 < Ab ∧ 0 < Am ∧ ∀ (N : ℕ) (κ : Type) (ι : Fin N → Type)
      [Fintype κ] [∀ j, Fintype (ι j)] (P : PlanarPacketFamily N κ ι)
      (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (_hv : Measurable v)
      (g : ℝ × ℝ → EuclideanSpace ℂ κ) (_hg : Measurable g) (_hg1 : ∀ z, ‖g z‖ ≤ 1)
      (_hderiv : ∀ y j u k x, ‖deriv (P.wave j u k y) x‖ ≤ (P.constant/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)),
      Monotone d →
      (∀ j u k y ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (P.wave j u k y) ξ = 0) →
      (∀ j u k y ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (P.wave j u k y) ξ = 0) →
      ∀ (synth : Fin 2 → ∀ j, ι j → κ → ℝ → SchwartzMap ℝ ℂ)
        (frequency : κ → ℝ) (C c r : ℝ), 0 < C → 0 < r →
      (∀ i y j u k x, ‖synth i j u k y x‖ ≤ C*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k x, ‖deriv (synth i j u k y) x‖ ≤ (C/P.length j)*
        (lineEnvelope (P.centerX j u) (P.length j) 3 x *
          lineEnvelope (P.centerZ j u) P.width 2 y)) →
      (∀ i y j u k ξ, |ξ| < lo*(2:ℝ)^j.val → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ i y j u k ξ, hi*(2:ℝ)^j.val < |ξ| → 𝓕 (synth i j u k y) ξ = 0) →
      (∀ y j u k x, (4*r:ℂ)*(deriv (fun t => synth 0 j u k t x) y -
        (frequency k:ℂ)*Complex.I*synth 0 j u k y x) = synth 1 j u k y x) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ => synth 0 j u k z.1 z.2)) →
      (∀ j u k x t, DifferentiableAt ℝ (fun y => synth 0 j u k y x) t) →
      (∀ j u k, Continuous (fun z : ℝ × ℝ =>
        deriv (fun t => synth 0 j u k t z.2) z.1 -
          (frequency k:ℂ)*Complex.I*synth 0 j u k z.1 z.2)) →
      ∀ (grid : FiniteLineGrid), 1 < grid.branching → (∀ j (_u : ι j), P.length j ≤ grid.width) →
      ∀ n : ℕ, 1 ≤ n →
      let K := lineMomentBase C (Am*C^2*(Ab*P.constant^2*P.coefficientScale⁻¹^2)+1) grid.branching
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧ bad ⊆ grid.root ×ˢ Icc (c-r) (c+r) ∧
        (volume.prod volume) bad ≤ 2*(1/4:ℝ≥0∞)^n*grid.lineMeasure univ*ENNReal.ofReal (2*r) ∧
        ∀ a b : ℕ, a ≤ b → b ≤ N → ∀ x z w,
          x ∈ grid.root → |z-c| ≤ r → |w| ≤ r → (x,z) ∉ bad →
          ‖planarPacketInterval (fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u)
            (fun j u k y x => synth 0 j u k y x) a b x (z+w)‖ ≤ 8*K*(n:ℝ) := by
  obtain ⟨Ab,hAb,hbudget⟩ := uniform_analyzedReplacement_budget hL hlo hhi
  obtain ⟨Am,hAm,hneighborhood⟩ := packet_interval_neighborhood_of_supported hL hlo hhi
  refine ⟨Ab,Am,hAb,hAm,?_⟩
  intro N κ ι _ _ P d v hv g hg hg1 hderiv hd hlow hhigh synth frequency C c r hC hr
    hbound hdbound hslow hshigh hcov hcont hdiff hD grid hb hwidth n hn
  dsimp only
  let Q : Fin 2 → ℝ → LinePacketFamily N κ ι := fun i y =>
    P.analyzedReplacement d v hv g hg hg1 y (hderiv y) C hC
      (fun j u k => synth i j u k y) (hbound i y) (hdbound i y)
  have hQbudget (i : Fin 2) (y : ℝ) :
      (Q i y).HasLocalBudget (Ab*P.constant^2*P.coefficientScale⁻¹^2) :=
    hbudget N κ ι P d v hv g hg hg1 y (hderiv y) hd hlow hhigh
      C hC _ (hbound i y) (hdbound i y)
  exact hneighborhood N κ ι
    (fun j u => P.coefficientScale⁻¹ • P.mainCoefficient d v g j u)
    (fun j u k y x => synth 0 j u k y x) frequency Q C
    (Ab*P.constant^2*P.coefficientScale⁻¹^2) c r hC (by positivity) hr
    (fun _ _ => rfl) hQbudget hslow hshigh (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl) hcov hcont hdiff hD grid hb (fun _ _ => hwidth) n hn

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
end

theorem solution : type_of% @OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported_oai := @OAI.LipschitzHilbert.PlanarPacketFamily.analyzed_interval_neighborhood_of_supported_oai
