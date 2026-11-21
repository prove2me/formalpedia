-- Prove2me | solution 1 for MasulloRH.positive_width_zero_jet_convolution_trace
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:57:40.392089+00:00
-- url     : https://prove2.me/submissions/3e223b7d-02dd-4337-b484-42b9a5e96a94

import Theorems.Thm_MasulloRH_finite_high_zero_interpolating_mellin_kernels
import Definitions.Def_MasulloRH_WeightedStripJetSpace
import Mathlib
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic
import Theorems.Thm_MasulloGRH_sobolev_oscillatory_jet_memLp_iff
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_MasulloGRH_nuclear_of_summable_rank_mul_opNorm
import Theorems.Thm_MasulloGRH_operatorTrace_of_nuclear_series
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Convolution
import Theorems.Thm_MasulloGRH_traceNorm_tail_of_summable_rank_mul_opNorm
import Theorems.Thm_MasulloRH_rational_theta_test_factorization

section StandaloneSobolevStripWeight

open MeasureTheory Filter
open scoped Topology
namespace MasulloRH.SobolevStrip
noncomputable section

/-- The exponential and Sobolev exponents, in this order. -/
abbrev P := NNReal × NNReal
abbrev H := Lp ℂ 2 (volume : Measure ℝ)

def weight (v : P) (x : ℝ) : ℝ := (1+x^2)^(-(v.2:ℝ)/2) * Real.exp (-(v.1:ℝ)*|x|)
def growth (v : P) (y : ℝ) : ℝ := (1+|y|)^(v.2:ℝ) * Real.exp ((v.1:ℝ)*|y|)
def polyConstant (p : NNReal) : ℝ := (⌈(p:ℝ)⌉₊.factorial:ℝ)*Real.exp 1

theorem weight_pos (v : P) (x : ℝ) : 0<weight v x := by unfold weight; positivity
theorem growth_pos (v : P) (y : ℝ) : 0<growth v y := by unfold growth; positivity

theorem continuous_weight (v : P) : Continuous (weight v) := by
  unfold weight; exact (Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))).mul (by fun_prop)
theorem continuous_growth (v : P) : Continuous (growth v) := by
  unfold growth; exact (Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))).mul (by fun_prop)

@[simp] theorem growth_zero (v : P) : growth v 0=1 := by simp [growth]
@[simp] theorem growth_neg (v : P) (y : ℝ) : growth v (-y)=growth v y := by simp [growth]
theorem growth_ge_one (v : P) (y : ℝ) : 1≤growth v y := by
  unfold growth
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith [abs_nonneg y]) v.2.prop)
    (Real.one_le_exp (mul_nonneg v.1.prop (abs_nonneg _)))

private theorem cyclic_SobolevStripWeight_ratio_identity (v : P) (x y : ℝ) :
    weight v x/weight v (x+y) =
    ((1+(x+y)^2)/(1+x^2))^((v.2:ℝ)/2) * Real.exp (-(v.1:ℝ)*|x|+(v.1:ℝ)*|x+y|) := by
  unfold weight
  have hx : 0≤1+x^2 := by positivity
  have hz : 0≤1+(x+y)^2 := by positivity
  rw [show -(v.2:ℝ)/2= -((v.2:ℝ)/2) by ring,Real.rpow_neg hx,Real.rpow_neg hz,
    Real.div_rpow hz hx,show -(v.1:ℝ)*|x|+(v.1:ℝ)*|x+y| = -(v.1:ℝ)*|x| - (-(v.1:ℝ)*|x+y|) by ring,Real.exp_sub]
  simp only [div_eq_mul_inv,mul_inv,inv_inv]; ring

private theorem cyclic_SobolevStripWeight_bracket_bound (x y : ℝ) :
    (1+(x+y)^2)/(1+x^2) ≤ (1+|y|)^2 := by
  rw [div_le_iff₀ (by positivity)]
  have hx : |x|≤1+x^2 := by nlinarith [sq_nonneg (|x|-1/2),sq_abs x]
  have hm := mul_le_mul_of_nonneg_right hx (abs_nonneg y)
  have hab : x*y≤|x| * |y| := by rw [←abs_mul]; exact le_abs_self _
  nlinarith only [hm,hab,sq_abs y,mul_nonneg (sq_nonneg x) (sq_nonneg y)]

private theorem cyclic_SobolevStripWeight_ratio_exp (v : P) (x y : ℝ) :
    Real.exp (-(v.1:ℝ)*|x|+(v.1:ℝ)*|x+y|) ≤ Real.exp ((v.1:ℝ)*|y|) := by
  have h : (v.1:ℝ)*|x+y|≤(v.1:ℝ)*(|x|+|y|) := mul_le_mul_of_nonneg_left (abs_add_le x y) v.1.prop
  rw [Real.exp_le_exp]; linarith

theorem weight_ratio_le (v : P) (x y : ℝ) : weight v x/weight v (x+y) ≤ growth v y := by
  rw [cyclic_SobolevStripWeight_ratio_identity,growth]
  apply mul_le_mul _ (cyclic_SobolevStripWeight_ratio_exp v x y) (Real.exp_nonneg _) (by positivity)
  apply (Real.rpow_le_rpow (by positivity) (cyclic_SobolevStripWeight_bracket_bound x y) (by positivity : 0≤(v.2:ℝ)/2)).trans_eq
  rw [← Real.rpow_natCast (1+|y|) 2,← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

theorem weight_ratio_quadratic (v : P) (x y : ℝ) : weight v x/weight v (x+y) ≤
    (2+2*y^2)^((v.2:ℝ)/2)*Real.exp ((v.1:ℝ)*|y|) := by
  rw [cyclic_SobolevStripWeight_ratio_identity]
  apply mul_le_mul _ (cyclic_SobolevStripWeight_ratio_exp v x y) (Real.exp_nonneg _) (by positivity)
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (x-y),sq_nonneg (x*y)]

theorem growth_le_exp (v : P) (y : ℝ) : growth v y ≤ polyConstant v.2 * Real.exp (((v.1:ℝ)+1)*|y|) := by
  let j := ⌈(v.2:ℝ)⌉₊
  have h₁ : (1+|y|)^(v.2:ℝ) ≤ (1+|y|)^j := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (Nat.le_ceil _)
  have h₂ := Real.pow_div_factorial_le_exp (1+|y|) (by positivity) j
  rw [div_le_iff₀ (by positivity)] at h₂
  rw [growth]
  apply (mul_le_mul_of_nonneg_right (h₁.trans h₂) (Real.exp_nonneg _)).trans_eq
  rw [Real.exp_add,show ((v.1:ℝ)+1)*|y|=|y|+(v.1:ℝ)*|y| by ring,Real.exp_add]
  dsimp [polyConstant,j]; ring

end
end MasulloRH.SobolevStrip

end StandaloneSobolevStripWeight

section StandaloneSobolevStripTranslation

open MeasureTheory Filter
open scoped Topology ENNReal
namespace MasulloRH.SobolevStrip
noncomputable section

private def cyclic_SobolevStripTranslation_ratio (v : P) (y x : ℝ) : ℂ := (weight v x / weight v (x+y) : ℝ)

private lemma cyclic_SobolevStripTranslation_ratio_norm (v : P) (y x : ℝ) : ‖cyclic_SobolevStripTranslation_ratio v y x‖ = weight v x / weight v (x+y) := by
  exact Complex.norm_of_nonneg (div_nonneg (weight_pos _ _).le (weight_pos _ _).le)

private lemma cyclic_SobolevStripTranslation_ratio_mem (v : P) (y : ℝ) : MemLp (cyclic_SobolevStripTranslation_ratio v y) ⊤ volume := by
  apply memLp_top_of_bound _ (growth v y) (ae_of_all _ fun x => (cyclic_SobolevStripTranslation_ratio_norm v y x).le.trans (weight_ratio_le v x y))
  apply Continuous.aestronglyMeasurable
  exact Complex.continuous_ofReal.comp <| (continuous_weight v).div
    ((continuous_weight v).comp (continuous_id.add_const y)) (fun x => (weight_pos _ _).ne')

private def cyclic_SobolevStripTranslation_shift (y : ℝ) : H →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x+y) (measurePreserving_add_right volume y)

def translation (v : P) (y : ℝ) : H →L[ℂ] H :=
  (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2) ((cyclic_SobolevStripTranslation_ratio_mem v y).toLp (cyclic_SobolevStripTranslation_ratio v y))).comp
    (cyclic_SobolevStripTranslation_shift y).toContinuousLinearMap

lemma translation_apply_ae (v : P) (y : ℝ) (f : H) :
    (translation v y f : ℝ → ℂ) =ᵐ[volume] fun x =>
      ((weight v x / weight v (x+y) : ℝ) : ℂ) * f (x+y) := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((cyclic_SobolevStripTranslation_ratio_mem v y).toLp (cyclic_SobolevStripTranslation_ratio v y)) (cyclic_SobolevStripTranslation_shift y f)
  have hs := Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)
  refine h.trans ?_
  filter_upwards [(cyclic_SobolevStripTranslation_ratio_mem v y).coeFn_toLp, hs] with x hx hsx
  change ((cyclic_SobolevStripTranslation_ratio_mem v y).toLp (cyclic_SobolevStripTranslation_ratio v y)) x * (cyclic_SobolevStripTranslation_shift y f) x = _
  change (cyclic_SobolevStripTranslation_shift y f) x = f (x+y) at hsx
  rw [hx, hsx]; rfl

lemma norm_translation_le (v : P) (y : ℝ) :
    ‖translation v y‖ ≤ growth v y := by
  apply ContinuousLinearMap.opNorm_le_bound _ (growth_pos _ _).le
  intro f
  rw [← (cyclic_SobolevStripTranslation_shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [translation_apply_ae v y f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hs
  change (cyclic_SobolevStripTranslation_shift y f) x = f (x+y) at hs
  rw [hx, hs, norm_mul]
  exact mul_le_mul_of_nonneg_right ((cyclic_SobolevStripTranslation_ratio_norm v y x).le.trans (weight_ratio_le v x y)) (norm_nonneg _)

lemma translation_zero (v : P) : translation v 0 = .id ℂ H := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [translation_apply_ae v 0 f] with x h
  change (translation v 0 f) x = f x
  simpa only [add_zero, div_self (weight_pos v x).ne', Complex.ofReal_one, one_mul] using h

lemma translation_add (v : P) (y z : ℝ) :
    translation v (y+z) = (translation v y).comp (translation v z) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hz := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp
    (translation_apply_ae v z f)
  filter_upwards [translation_apply_ae v (y+z) f,
    translation_apply_ae v y ((translation v z) f), hz] with x hall hy hz
  change (translation v z f) (x+y) = _ at hz
  change (translation v (y+z) f) x = (translation v y ((translation v z) f)) x
  rw [hall, hy, hz]
  simp only [Function.comp_apply, ← add_assoc, ← mul_assoc, ← Complex.ofReal_mul]
  field_simp [ne_of_gt (weight_pos v (x+y)), ne_of_gt (weight_pos v (x+y+z))]

private lemma cyclic_SobolevStripTranslation_ratio_sub_one_bound (v : P) (x y : ℝ) :
    |weight v x / weight v (x+y) - 1| ≤ growth v y - 1 := by
  let a := weight v x / weight v (x+y)
  let D := growth v y
  have hD : 1 ≤ D := growth_ge_one v y
  have ha : a ≤ D := weight_ratio_le v x y
  have hinv := weight_ratio_le v (x+y) (-y)
  simp only [add_neg_cancel_right, growth_neg] at hinv
  have hDa : 1 ≤ D*a := by
    change 1 ≤ D * (weight v x / weight v (x+y))
    rw [← mul_div_assoc, le_div_iff₀ (weight_pos v (x+y)), one_mul]
    exact (div_le_iff₀ (weight_pos v x)).mp hinv
  change |a-1| ≤ D-1
  apply abs_le.mpr
  refine ⟨?_, by linarith⟩
  by_cases h : a ≤ 1
  · have h' := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hD)
    nlinarith
  · linarith

private lemma cyclic_SobolevStripTranslation_shift_continuous (f : H) : Continuous (fun y : ℝ => cyclic_SobolevStripTranslation_shift y f) := by
  let g : C(ℝ × ℝ, ℝ) := ⟨fun z => z.2 + z.1, continuous_snd.add continuous_fst⟩
  exact continuous_const.compMeasurePreservingLp (g := g.curry) g.curry.continuous
    (fun y => measurePreserving_add_right volume y) (by norm_num)

private lemma cyclic_SobolevStripTranslation_diff_shift_bound (v : P) (y : ℝ) (f : H) :
    ‖translation v y f - cyclic_SobolevStripTranslation_shift y f‖ ≤ (growth v y-1) * ‖f‖ := by
  rw [← (cyclic_SobolevStripTranslation_shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [translation_apply_ae v y f,
    Lp.coeFn_sub (translation v y f) (cyclic_SobolevStripTranslation_shift y f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hsub hs
  change (cyclic_SobolevStripTranslation_shift y f) x = f (x+y) at hs
  rw [hsub, Pi.sub_apply, hx, hs, ← sub_one_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact cyclic_SobolevStripTranslation_ratio_sub_one_bound v x y

lemma continuous_translation_orbit (v : P) (f : H) :
    Continuous (fun y : ℝ => translation v y f) := by
  have hlim : Tendsto (fun y : ℝ => translation v y f) (𝓝 0) (𝓝 f) := by
    have hg : Continuous (fun y : ℝ => (growth v y-1) * ‖f‖) := by
      exact ((continuous_growth v).sub continuous_const).mul continuous_const
    have hbound : Tendsto (fun y : ℝ => (growth v y-1) * ‖f‖) (𝓝 0) (𝓝 0) := by
      simpa using hg.tendsto 0
    have hdiff : Tendsto (fun y : ℝ => translation v y f - cyclic_SobolevStripTranslation_shift y f) (𝓝 0) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => norm_nonneg _) (fun y => cyclic_SobolevStripTranslation_diff_shift_bound v y f) hbound
    have hs0 : cyclic_SobolevStripTranslation_shift 0 f = f := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume (0:ℝ))] with x hx
      change (cyclic_SobolevStripTranslation_shift 0 f) x = f (x+0) at hx
      simpa only [add_zero] using hx
    have hs := (cyclic_SobolevStripTranslation_shift_continuous f).tendsto 0
    rw [hs0] at hs
    simpa only [sub_add_cancel, zero_add] using hdiff.add hs
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : Tendsto (fun z : ℝ => z-y) (𝓝 y) (𝓝 0) := by simpa using (show Continuous (fun z : ℝ => z-y) from continuous_id.sub continuous_const).tendsto y
  have h := (translation v y).continuous.continuousAt.tendsto.comp (hlim.comp hd)
  refine h.congr fun z => ?_
  change (translation v y) ((translation v (z-y)) f) = _
  rw [← ContinuousLinearMap.comp_apply, ← translation_add]
  simp

end
end MasulloRH.SobolevStrip

end StandaloneSobolevStripTranslation

section StandaloneSobolevStripConvolution

open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace MasulloRH.SobolevStrip
noncomputable section

private lemma cyclic_SobolevStripConvolution_orbit_bound (v : P) (k : ℝ→ℂ) (f : H) (y : ℝ) :
    ‖k y • translation v y f‖ ≤ (‖k y‖*growth v y)*‖f‖ := by
  rw [norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (((translation v y).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (norm_translation_le v y) (norm_nonneg _))) (norm_nonneg _)

theorem integrable_orbit (v : P) {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) (f : H) :
    Integrable (fun y : ℝ => k y • translation v y f) :=
  (hW.mul_const ‖f‖).mono' (hk.smul (continuous_translation_orbit v f).aestronglyMeasurable)
    (Eventually.of_forall (cyclic_SobolevStripConvolution_orbit_bound v k f))

private def cyclic_SobolevStripConvolution_convolutionLinear (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) : H →ₗ[ℂ] H where
  toFun f := ∫ y : ℝ, k y • translation v y f
  map_add' f g := by simp only [map_add,smul_add,integral_add (integrable_orbit v hk hW f) (integrable_orbit v hk hW g)]
  map_smul' c f := by simp only [map_smul,RingHom.id_apply]; simp_rw [smul_comm (k _) c, integral_smul]

private theorem cyclic_SobolevStripConvolution_convolution_bound (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) (f : H) :
    ‖cyclic_SobolevStripConvolution_convolutionLinear v k hk hW f‖ ≤ (∫ y : ℝ, ‖k y‖*growth v y)*‖f‖ := by
  exact (norm_integral_le_of_norm_le (hW.mul_const _) (Eventually.of_forall (cyclic_SobolevStripConvolution_orbit_bound v k f))).trans_eq
    (integral_mul_const ..)

def convolution (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) : H →L[ℂ] H :=
  (cyclic_SobolevStripConvolution_convolutionLinear v k hk hW).mkContinuous _ (cyclic_SobolevStripConvolution_convolution_bound v k hk hW)

theorem convolution_apply (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) (f : H) :
    convolution v k hk hW f = ∫ y : ℝ, k y • translation v y f := rfl

theorem norm_convolution_le (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) :
    ‖convolution v k hk hW‖ ≤ ∫ y : ℝ, ‖k y‖*growth v y :=
  (cyclic_SobolevStripConvolution_convolutionLinear v k hk hW).mkContinuous_norm_le (integral_nonneg fun y => mul_nonneg (norm_nonneg _) (growth_pos _ _).le)
    (cyclic_SobolevStripConvolution_convolution_bound v k hk hW)

theorem convolution_pairing (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) (f g : H) :
    ⟪g,convolution v k hk hW f⟫_ℂ = ∫ y : ℝ, k y * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
        (((weight v x / weight v (x+y) : ℝ) : ℂ) * f (x+y)) := by
  rw [convolution_apply,← integral_inner (integrable_orbit v hk hW f) g]
  apply integral_congr_ae (ae_of_all _ fun y => ?_)
  rw [inner_smul_right,MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [translation_apply_ae v y f] with x hx
  rw [RCLike.inner_apply',hx]

end
end MasulloRH.SobolevStrip

end StandaloneSobolevStripConvolution

section StandaloneStripPhysicalTranslation

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace MasulloRH.StripPhysical
noncomputable section

abbrev H := Lp ℂ 2 (volume : Measure ℝ)

def weight (p x : ℝ) : ℝ := Real.exp (-p*|x|)

lemma weight_pos (p x : ℝ) : 0 < weight p x := Real.exp_pos _

end
end MasulloRH.StripPhysical
end StandaloneStripPhysicalTranslation

section StandaloneStripPhysicalJets

open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace MasulloRH.StripPhysical
noncomputable section

/-- A polynomial factor uses only the strict margin between the two exponential rates. -/
theorem polynomial_exp_bound {a b : ℝ} (h : |a|<b) (r : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : ℝ, |x|^r*Real.exp (a*x) ≤ C*Real.exp (b*|x|) := by
  let d := b-|a|
  have hd : 0<d := sub_pos.mpr h
  let C : ℝ := (r.factorial:ℝ)/d^r
  refine ⟨C,by dsimp [C]; positivity,fun x => ?_⟩
  have hbd := Real.pow_div_factorial_le_exp _ (mul_nonneg hd.le (abs_nonneg x)) r
  have hp : |x|^r ≤ C * Real.exp (d*|x|) := by
    have hb := (div_le_iff₀ (by positivity : 0<(r.factorial:ℝ))).mp hbd
    rw [mul_pow] at hb
    dsimp [C]
    rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos hd _)]
    simpa only [mul_comm] using hb
  have he : a*x ≤ |a| *|x| := by rw [← abs_mul]; exact le_abs_self _
  calc
    _ ≤ (C*Real.exp (d*|x|))*Real.exp (|a| *|x|) :=
      mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_nonneg _) (by dsimp [C]; positivity)
    _ = _ := by rw [mul_assoc,← Real.exp_add]; dsimp [d]; ring_nf

private theorem cyclic_StripPhysicalJets_integrable_exp_abs {d : ℝ} (hd : 0<d) :
    Integrable (fun x : ℝ => Real.exp (-d*|x|)) := by
  let f (x : ℝ) := Real.exp (-d*|x|)
  have hr : IntegrableOn f (Ioi 0) := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) 0).congr_fun
    (fun x hx => by simp only [f,abs_of_pos (show 0<x from hx)]) measurableSet_Ioi
  have hl : IntegrableOn f (Iic 0) := (integrableOn_exp_mul_Iic hd 0).congr_fun
    (fun x hx => by simp only [f,abs_of_nonpos (show x≤0 from hx),neg_mul_neg]) measurableSet_Iic
  change Integrable f
  simpa using hl.union hr

def jetFunction (b : ℝ) (z : ℂ) (r : ℕ) (x : ℝ) : ℂ :=
  (weight b x:ℂ)*(x:ℂ)^r*Complex.exp (z*(x:ℂ))

theorem jet_memLp {b : ℝ} {z : ℂ} (hz : |z.re|<b) (r : ℕ) :
    MemLp (jetFunction b z r) 2 volume := by
  have hc : Continuous (jetFunction b z r) := by unfold jetFunction weight; fun_prop
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
  let c := (b+|z.re|)/2
  have hmid : |z.re|<c := by dsimp [c]; linarith
  have hgap : 0<2*(b-c) := by dsimp [c]; linarith
  obtain ⟨C,hC,hx⟩ := polynomial_exp_bound hmid r
  apply ((cyclic_StripPhysicalJets_integrable_exp_abs hgap).const_mul (C^2)).mono' (hc.norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  have he : ‖jetFunction b z r x‖ ≤ C*Real.exp ((c-b)*|x|) := by
    simp only [jetFunction,norm_mul,norm_pow,Complex.norm_of_nonneg (weight_pos b x).le,
      Complex.norm_real,Real.norm_eq_abs, Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    rw [mul_assoc]
    apply (mul_le_mul_of_nonneg_left (hx x) (weight_pos b x).le).trans_eq
    rw [mul_left_comm,weight,← Real.exp_add]
    congr 2; ring
  change ‖‖jetFunction b z r x‖^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (C*Real.exp ((c-b)*|x|))^2 := pow_le_pow_left₀ (norm_nonneg _) he 2
    _ = _ := by rw [mul_pow,sq (Real.exp _),← Real.exp_add]; congr 2; ring

end
end MasulloRH.StripPhysical
end StandaloneStripPhysicalJets

section StandaloneSobolevStripJets

open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace MasulloRH.SobolevStrip
noncomputable section

private def cyclic_SobolevStripJets_base (p : ℝ) (r : ℕ) (x : ℝ) :=
  (1+x^2)^(-p/2)*|x|^r

private theorem cyclic_SobolevStripJets_base_nonneg (p : ℝ) (r : ℕ) (x : ℝ) : 0≤cyclic_SobolevStripJets_base p r x := by
  unfold cyclic_SobolevStripJets_base; positivity

private theorem cyclic_SobolevStripJets_base_cont (p : ℝ) (r : ℕ) : Continuous (cyclic_SobolevStripJets_base p r) := by
  unfold cyclic_SobolevStripJets_base
  exact (Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))).mul (by fun_prop)

private theorem cyclic_SobolevStripJets_base_iff_pos (p : ℝ) (hp : 1/2<p) (r : ℕ) :
    MemLp (cyclic_SobolevStripJets_base p r) 2 volume ↔ (r:ℝ)+1/2<p := by
  have h := MasulloGRH.sobolev_oscillatory_jet_memLp_iff r 0 (2*p) (by linarith)
  rw [memLp_map_measure_iff (by fun_prop) Real.continuous_exp.aemeasurable] at h
  let f (x : ℝ) : ℂ := ((1+x^2)^(-p/2):ℝ) • ((x:ℂ)^r)
  have he : (fun t : ℝ => ((1+(Real.log t)^2)^(-(2*p)/4) : ℝ) •
      (Complex.exp (↑((0:ℝ)*Real.log t) * Complex.I) * (Real.log t:ℂ)^r)) ∘ Real.exp = f := by
    funext x
    simp [f,show -(2*p)/4= -p/2 by ring]
  rw [he] at h
  have hf : Continuous f := (Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))).smul (by fun_prop)
  have hn : (fun x => ‖f x‖) = cyclic_SobolevStripJets_base p r := by
    funext x; dsimp [f,cyclic_SobolevStripJets_base]
    rw [norm_mul,Complex.norm_of_nonneg (by positivity),norm_pow,Complex.norm_real,Real.norm_eq_abs]
  rw [←hn,memLp_norm_iff hf.aestronglyMeasurable,h]; constructor <;> intro h <;> linarith

private theorem cyclic_SobolevStripJets_base_inc (p : ℝ) (r : ℕ) (x : ℝ) : cyclic_SobolevStripJets_base (p+1) (r+1) x ≤ cyclic_SobolevStripJets_base p r x := by
  let a := 1+x^2
  have ha : 0<a := by dsimp [a]; positivity
  have hs : |x|≤Real.sqrt a := (Real.le_sqrt (abs_nonneg _) ha.le).mpr (by dsimp [a]; nlinarith [sq_abs x])
  have hq : a^(-(1/2:ℝ))*|x| ≤ 1 := by
    rw [Real.rpow_neg ha.le,← Real.sqrt_eq_rpow,← div_eq_inv_mul,div_le_one (Real.sqrt_pos.mpr ha)]
    exact hs
  change a^(-(p+1)/2)*|x|^(r+1)≤a^(-p/2)*|x|^r
  rw [show -(p+1)/2= -p/2 + -(1/2:ℝ) by ring,Real.rpow_add ha,pow_succ]
  calc
    _ = (a^(-p/2)*|x|^r)*(a^(-(1/2:ℝ))*|x|) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hq

private theorem cyclic_SobolevStripJets_base_iff (p : NNReal) (r : ℕ) :
    MemLp (cyclic_SobolevStripJets_base p r) 2 volume ↔ (r:ℝ)+1/2<p := by
  constructor
  · intro h
    have h' : MemLp (cyclic_SobolevStripJets_base ((p:ℝ)+1) (r+1)) 2 volume := h.mono'
      (cyclic_SobolevStripJets_base_cont _ _).aestronglyMeasurable (Eventually.of_forall (fun x => by
        rw [Real.norm_of_nonneg (cyclic_SobolevStripJets_base_nonneg _ _ _)]; exact cyclic_SobolevStripJets_base_inc _ _ _))
    have ht := (cyclic_SobolevStripJets_base_iff_pos ((p:ℝ)+1) (by linarith [p.prop]) _).mp h'
    push_cast at ht; linarith
  · intro hr
    exact (cyclic_SobolevStripJets_base_iff_pos p (by linarith [Nat.cast_nonneg (α:=ℝ) r]) r).mpr hr

def jetFunction (v : P) (z : ℂ) (r : ℕ) (x : ℝ) : ℂ :=
  (weight v x:ℂ)*(x:ℂ)^r*Complex.exp (z*(x:ℂ))

theorem jetFunction_cont (v : P) (z : ℂ) (r : ℕ) : Continuous (jetFunction v z r) := by
  unfold jetFunction
  exact ((Complex.continuous_ofReal.comp (continuous_weight v)).mul (by fun_prop)).mul (by fun_prop)

private theorem cyclic_SobolevStripJets_jet_norm (v : P) (z : ℂ) (r : ℕ) (x : ℝ) :
    ‖jetFunction v z r x‖ = cyclic_SobolevStripJets_base v.2 r x * Real.exp (z.re*x-(v.1:ℝ)*|x|) := by
  simp only [jetFunction,norm_mul,norm_pow,Complex.norm_of_nonneg (weight_pos v x).le,
    Complex.norm_real,Real.norm_eq_abs, Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero]
  rw [weight,cyclic_SobolevStripJets_base,show z.re*x-(v.1:ℝ)*|x| = -(v.1:ℝ)*|x|+z.re*x by ring,Real.exp_add]
  ring

private theorem cyclic_SobolevStripJets_exponent_nonpos (v : P) (z : ℂ) (hz : |z.re|≤v.1) (x : ℝ) :
    z.re*x-(v.1:ℝ)*|x|≤0 := by
  have h : z.re*x ≤ |z.re| * |x| := by rw [←abs_mul]; exact le_abs_self _
  linarith [mul_le_mul_of_nonneg_right hz (abs_nonneg x)]

def Admissible (v : P) (z : ℂ) (r : ℕ) : Prop :=
  |z.re|<(v.1:ℝ) ∨ (|z.re|≤(v.1:ℝ) ∧ (r:ℝ)+1/2<(v.2:ℝ))

theorem admissible_mono {v : P} {z : ℂ} {r s : ℕ} (hr : Admissible v z r) (hs : s≤r) :
    Admissible v z s := hr.imp_right (fun h => ⟨h.1,by
      have hh : (s:ℝ)≤r := by exact_mod_cast hs
      linarith [h.2]⟩)

theorem jet_memLp {v : P} {z : ℂ} {r : ℕ} (h : Admissible v z r) :
    MemLp (jetFunction v z r) 2 volume := by
  rcases h with hi|⟨hz,hr⟩
  · apply (StripPhysical.jet_memLp hi r).mono (jetFunction_cont v z r).aestronglyMeasurable
    filter_upwards with x
    have hp : (1+x^2)^(-(v.2:ℝ)/2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by linarith [v.2.prop])
    have he : jetFunction v z r x = (((1+x^2)^(-(v.2:ℝ)/2):ℝ):ℂ)*StripPhysical.jetFunction v.1 z r x := by
      simp only [jetFunction,StripPhysical.jetFunction,weight,StripPhysical.weight,Complex.ofReal_mul]; ring
    rw [he,norm_mul,Complex.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (norm_nonneg _) hp
  · apply ((cyclic_SobolevStripJets_base_iff v.2 r).mpr hr).mono' (jetFunction_cont v z r).aestronglyMeasurable
    filter_upwards with x
    rw [cyclic_SobolevStripJets_jet_norm]
    exact mul_le_of_le_one_right (cyclic_SobolevStripJets_base_nonneg _ _ _) (Real.exp_le_one_iff.mpr (cyclic_SobolevStripJets_exponent_nonpos v z hz x))

theorem edge_memLp_iff {v : P} {z : ℂ} (hz : |z.re|=(v.1:ℝ)) (r : ℕ) :
    MemLp (jetFunction v z r) 2 volume ↔ (r:ℝ)+1/2<(v.2:ℝ) := by
  refine ⟨fun h => (cyclic_SobolevStripJets_base_iff v.2 r).mp ?_,fun hr => jet_memLp (Or.inr ⟨hz.le,hr⟩)⟩
  let g := jetFunction v z r
  have href := h.norm.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  apply (h.norm.add href).mono' (cyclic_SobolevStripJets_base_cont _ _).aestronglyMeasurable
  filter_upwards with x
  change ‖cyclic_SobolevStripJets_base v.2 r x‖≤‖g x‖+‖g (-x)‖
  rw [Real.norm_of_nonneg (cyclic_SobolevStripJets_base_nonneg _ _ _)]
  have h1 := norm_nonneg (g x)
  have h2 := norm_nonneg (g (-x))
  have he : z.re*x=(v.1:ℝ)*|x| ∨ z.re*(-x)=(v.1:ℝ)*|x| := by
    rw [←hz,←abs_mul]
    rcases le_total 0 (z.re*x) with hp|hn
    · exact Or.inl (abs_of_nonneg hp).symm
    · right; rw [mul_neg,abs_of_nonpos hn]
  rcases he with he|he
  · change _≤‖jetFunction v z r x‖+_
    rw [cyclic_SobolevStripJets_jet_norm,he,sub_self,Real.exp_zero,mul_one]; linarith
  · change _≤_+‖jetFunction v z r (-x)‖
    rw [cyclic_SobolevStripJets_jet_norm v z r (-x),abs_neg,he,sub_self,Real.exp_zero,mul_one,show cyclic_SobolevStripJets_base v.2 r (-x)=cyclic_SobolevStripJets_base v.2 r x by simp [cyclic_SobolevStripJets_base]]
    linarith

/-- A jet mode in ordinary L², conjugated by the Sobolev/exponential amplitude. -/
def jet (v : P) (z : ℂ) (r : ℕ) : H := by
  classical
  exact if h : Admissible v z r then (jet_memLp h).toLp _ else 0

theorem jet_apply_ae {v : P} {z : ℂ} {r : ℕ} (hr : Admissible v z r) :
    (jet v z r : ℝ→ℂ) =ᵐ[volume] jetFunction v z r := by
  classical
  rw [jet,dif_pos hr]; exact (jet_memLp hr).coeFn_toLp

theorem jet_ne_zero {v : P} {z : ℂ} {r : ℕ} (hr : Admissible v z r) : jet v z r ≠ 0 := by
  intro he
  have h := jet_apply_ae hr
  rw [he] at h
  have hh := Measure.eq_of_ae_eq (h.symm.trans (Lp.coeFn_zero ℂ 2 volume))
    (jetFunction_cont v z r) continuous_const
  have h1 := congrFun hh 1
  simp [jetFunction,(weight_pos _ _).ne',Complex.exp_ne_zero] at h1

private lemma cyclic_SobolevStripJets_jet_expand (v : P) (z : ℂ) (r : ℕ) (x y : ℝ) :
    ((weight v x / weight v (x+y) : ℝ):ℂ)*jetFunction v z r (x+y) =
      ∑ s ∈ Finset.range (r+1), ((r.choose s:ℂ)*(y:ℂ)^(r-s)*Complex.exp (z*y))*jetFunction v z s x := by
  simp only [jetFunction,Complex.ofReal_add,Complex.ofReal_div,mul_add,Complex.exp_add]
  have hw : (weight v (x+y):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (weight_pos _ _).ne'
  calc
    _ = ((weight v x:ℂ)*Complex.exp (z*x)*Complex.exp (z*y)) * ((x:ℂ)+(y:ℂ))^r := by field_simp
    _ = _ := by
      rw [add_pow,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)

theorem translation_jet {v : P} {z : ℂ} {r : ℕ} (hr : Admissible v z r) (y : ℝ) :
    translation v y (jet v z r) =
      ∑ s ∈ Finset.range (r+1), ((r.choose s:ℂ)*(y:ℂ)^(r-s)*Complex.exp (z*y)) • jet v z s := by
  let a (s : ℕ) : ℂ := (r.choose s:ℂ)*(y:ℂ)^(r-s)*Complex.exp (z*y)
  have hs (s : ℕ) : ∀ᵐ x ∂volume, s≤r → (a s • jet v z s : H) x = a s * jetFunction v z s x := by
    by_cases h : s≤r
    · filter_upwards [Lp.coeFn_smul (a s) (jet v z s),jet_apply_ae (admissible_mono hr h)] with x hx hx'
      simp only [hx,Pi.smul_apply,smul_eq_mul,hx',implies_true]
    · simp [h]
  apply Lp.ext
  filter_upwards [translation_apply_ae v y (jet v z r),
    (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp (jet_apply_ae hr),
    Lp.coeFn_fun_finsetSum (Finset.range (r+1)) (fun s => a s • jet v z s),ae_all_iff.mpr hs]
    with x hu hx hsum hall
  change (translation v y (jet v z r)) x = (∑ s ∈ Finset.range (r+1), a s • jet v z s : H) x
  rw [hu,hsum]
  change jet v z r (x+y) = jetFunction v z r (x+y) at hx
  rw [hx,cyclic_SobolevStripJets_jet_expand]
  exact Finset.sum_congr rfl fun s h => (hall s (by clear hall; simpa using h)).symm

end
end MasulloRH.SobolevStrip

end StandaloneSobolevStripJets

section StandaloneJetIndependence

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff Polynomial
namespace MasulloRH
noncomputable section

private def cyclic_JetIndependence_jetSpace : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℂ)))
  add_mem' := by
    intro f g hf hg
    exact (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  smul_mem' := by
    intro c f hf
    exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => c)).smul (show ContDiff ℝ ∞ f from hf)

private lemma cyclic_JetIndependence_jet_smooth (f : cyclic_JetIndependence_jetSpace) : ContDiff ℝ ∞ f.val := f.property

private def cyclic_JetIndependence_jetDeriv : Module.End ℂ cyclic_JetIndependence_jetSpace where
  toFun f := ⟨deriv f.val, by
    change ContDiff ℝ ∞ (deriv _)
    apply ContDiff.deriv'
    simpa using cyclic_JetIndependence_jet_smooth f⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact deriv_add ((cyclic_JetIndependence_jet_smooth f).differentiable (by simp) x) ((cyclic_JetIndependence_jet_smooth g).differentiable (by simp) x)
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact deriv_const_smul c ((cyclic_JetIndependence_jet_smooth f).differentiable (by simp) x)

private def cyclic_JetIndependence_jet (a : ℂ) (n : ℕ) : cyclic_JetIndependence_jetSpace :=
  ⟨fun x => (x:ℂ)^n * Complex.exp (a * x), by
    change ContDiff ℝ ∞ _
    have hc : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    exact (hc.pow n).mul ((Complex.contDiff_exp : ContDiff ℝ ∞ Complex.exp).comp (contDiff_const.mul hc))⟩

private theorem cyclic_JetIndependence_jet_deriv_sub (a : ℂ) (n : ℕ) :
    (cyclic_JetIndependence_jetDeriv - a • 1) (cyclic_JetIndependence_jet a n) = (n:ℂ) • cyclic_JetIndependence_jet a (n-1) := by
  apply Subtype.ext
  funext x
  change deriv (fun y : ℝ => (y:ℂ)^n * Complex.exp (a * y)) x -
    a * ((x:ℂ)^n * Complex.exp (a*x)) =
      (n:ℂ) * ((x:ℂ)^(n-1) * Complex.exp (a*x))
  have h : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using! (Complex.ofRealCLM.hasDerivAt (x := x))
  have hd := ((h.pow n).mul ((h.const_mul a).cexp)).deriv
  change deriv (fun y : ℝ => (y:ℂ)^n * Complex.exp (a * y)) x = _ at hd
  rw [hd]
  simp only [Pi.pow_apply]
  ring

private theorem cyclic_JetIndependence_jet_nilpotent (a : ℂ) (n : ℕ) :
    ((cyclic_JetIndependence_jetDeriv - a • 1) ^ (n+1)) (cyclic_JetIndependence_jet a n) = 0 := by
  induction n with
  | zero => rw [Nat.zero_add, pow_one, cyclic_JetIndependence_jet_deriv_sub]; simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, cyclic_JetIndependence_jet_deriv_sub, map_smul]
    simp [ih]

private def cyclic_JetIndependence_jetPolynomial (a : ℂ) : ℂ[X] →ₗ[ℂ] (ℝ → ℂ) where
  toFun P x := P.eval (x:ℂ) * Complex.exp (a * x)
  map_add' P Q := by ext x; simp [add_mul]
  map_smul' c P := by ext x; simp [mul_assoc]

private theorem cyclic_JetIndependence_jetPolynomial_injective (a : ℂ) : Function.Injective (cyclic_JetIndependence_jetPolynomial a) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro P hP
  apply P.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro _ ⟨x, rfl⟩
  have h := congrFun hP x
  exact (mul_eq_zero.mp h).resolve_right (Complex.exp_ne_zero _)

private theorem cyclic_JetIndependence_jet_layer_independent (a : ℂ) : LinearIndependent ℂ (cyclic_JetIndependence_jet a) := by
  apply LinearIndependent.of_comp cyclic_JetIndependence_jetSpace.subtype
  have hb := (Polynomial.basisMonomials ℂ).linearIndependent.map' (cyclic_JetIndependence_jetPolynomial a)
    (LinearMap.ker_eq_bot.mpr (cyclic_JetIndependence_jetPolynomial_injective a))
  change LinearIndependent ℂ (fun n => fun x : ℝ => (x:ℂ)^n * Complex.exp (a*x))
  simpa only [Polynomial.coe_basisMonomials, Function.comp_def, cyclic_JetIndependence_jetPolynomial, LinearMap.coe_mk,
    AddHom.coe_mk, Polynomial.eval_monomial, one_mul] using hb

theorem polynomialExponentialJets_independent :
    LinearIndependent ℂ (fun i : ℂ × ℕ => fun x : ℝ => (x : ℂ) ^ i.2 * Complex.exp (i.1 * x)) := by
  have hm : ∀ a, Submodule.span ℂ (Set.range (cyclic_JetIndependence_jet a)) ≤ cyclic_JetIndependence_jetDeriv.maxGenEigenspace a := by
    intro a
    rw [Submodule.span_le]
    rintro _ ⟨n,rfl⟩
    exact (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨n+1, cyclic_JetIndependence_jet_nilpotent a n⟩
  have hs := cyclic_JetIndependence_jetDeriv.independent_maxGenEigenspace.mono hm
  have hSigma := linearIndependent_iUnion_finite cyclic_JetIndependence_jet_layer_independent
    (fun _ _ _ h => hs.disjoint_biSup h)
  have hprod := hSigma.comp (fun i : ℂ × ℕ => (⟨i.1,i.2⟩ : Σ _ : ℂ, ℕ)) (by
    intro a b h
    have h₁ := congrArg Sigma.fst h
    have h₂ := congrArg (fun i : Σ _ : ℂ, ℕ => i.2) h
    exact Prod.ext h₁ h₂)
  exact hprod.map' cyclic_JetIndependence_jetSpace.subtype (LinearMap.ker_eq_bot.mpr cyclic_JetIndependence_jetSpace.injective_subtype)

open MeasureTheory Filter

theorem linearIndependent_weightedLp_of_continuous {ι : Type*}
    (F : ι → ℝ → ℂ) (hF : ∀ i, Continuous (F i)) (hI : LinearIndependent ℂ F)
    (w : ℝ → ℂ) (hw : ∀ᵐ x ∂volume, w x ≠ 0) (u : ι → Lp ℂ 2 (volume : Measure ℝ))
    (hu : ∀ i, u i =ᵐ[volume] fun x => w x * F i x) : LinearIndependent ℂ u := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc
  have hsum (S : Finset ι) :
      (↑(∑ i ∈ S, c i • u i) : ℝ → ℂ) =ᵐ[volume]
        fun x => w x * ∑ i ∈ S, c i * F i x := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, mul_zero]
      filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
      exact hx
    | insert i S hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • u i) (∑ j ∈ S, c j • u j), Lp.coeFn_smul (c i) (u i),
        hu i, ih] with x h₁ h₂ h₃ h₄
      rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, smul_eq_mul, h₃, h₄, Finset.sum_insert hi]
      ring
  have hzero : (fun x => ∑ i ∈ s, c i * F i x) =ᵐ[volume] fun _ => 0 := by
    have h := hsum s
    rw [hc] at h
    filter_upwards [h, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ), hw] with x hx hz hwx
    rw [hz] at hx
    exact (mul_eq_zero.mp hx.symm).resolve_left hwx
  have hpoint := Measure.eq_of_ae_eq hzero (continuous_finsetSum _ fun i _ => continuous_const.mul (hF i)) continuous_const
  apply linearIndependent_iff'.mp hI s c
  funext x
  simpa using congrFun hpoint x

theorem weightedPolynomialExponentialJets_independent {ι : Type*}
    (a : ι → ℂ × ℕ) (ha : Function.Injective a)
    (w : ℝ → ℂ) (hw : ∀ᵐ x ∂volume, w x ≠ 0)
    (u : ι → Lp ℂ 2 (volume : Measure ℝ))
    (hu : ∀ i, u i =ᵐ[volume] fun x => w x * ((x:ℂ)^(a i).2 * Complex.exp ((a i).1*x))) :
    LinearIndependent ℂ u := by
  exact linearIndependent_weightedLp_of_continuous
    (fun i x => (x:ℂ)^(a i).2 * Complex.exp ((a i).1*x))
    (fun _ => by fun_prop) (polynomialExponentialJets_independent.comp a ha) w hw u hu

end
end MasulloRH

end StandaloneJetIndependence

section StandaloneSobolevStripIndependent

open MeasureTheory Filter Set
open scoped Topology
namespace MasulloRH.SobolevStrip
noncomputable section

theorem linearIndependent_jet (v : P) {ι : Type*} (a : ι → ℂ × ℕ)
    (ha : Function.Injective a) (hadm : ∀ i, Admissible v (a i).1 (a i).2) :
    LinearIndependent ℂ (fun i => jet v (a i).1 (a i).2) := by
  apply weightedPolynomialExponentialJets_independent a ha (fun x => (weight v x:ℂ))
    (ae_of_all _ (fun x => Complex.ofReal_ne_zero.mpr (weight_pos _ _).ne'))
  intro i
  exact (jet_apply_ae (hadm i)).trans (ae_of_all _ fun x => by dsimp [jetFunction]; ring)

theorem admissible_iff (v : P) (z : ℂ) (r : ℕ) :
    Admissible v z r ↔ |z.re| < (v.1:ℝ) ∨ |z.re| = (v.1:ℝ) ∧ (r:ℝ)+1/2 < (v.2:ℝ) := by
  unfold Admissible
  constructor
  · rintro (h | ⟨h,hr⟩)
    · exact Or.inl h
    rcases h.lt_or_eq with h|h
    · exact Or.inl h
    · exact Or.inr ⟨h,hr⟩
  · rintro (h | ⟨h,hr⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h.le,hr⟩

theorem closed_strip_memLp_iff {v : P} {z : ℂ} (hz : |z.re|≤(v.1:ℝ)) (r : ℕ) :
    MemLp (jetFunction v z r) 2 volume ↔ Admissible v z r := by
  refine ⟨fun h => ?_, jet_memLp⟩
  rcases hz.lt_or_eq with hl|he
  · exact Or.inl hl
  · exact Or.inr ⟨hz,(edge_memLp_iff he r).mp h⟩

theorem norm_translation_le_exp (v : P) (y : ℝ) :
    ‖translation v y‖ ≤ polyConstant v.2 * Real.exp (((v.1:ℝ)+1)*|y|) :=
  (norm_translation_le v y).trans (growth_le_exp v y)

theorem norm_translation_le_quadratic (v : P) (y : ℝ) : ‖translation v y‖ ≤
    (2+2*y^2)^((v.2:ℝ)/2)*Real.exp ((v.1:ℝ)*|y|) := by
  apply (norm_translation_le v y).trans
  unfold growth
  apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
  have h : (1+|y|)^2 ≤ 2+2*y^2 := by nlinarith only [sq_nonneg (|y|-1),sq_abs y]
  have h₂ := Real.rpow_le_rpow (by positivity) h (by positivity : 0≤(v.2:ℝ)/2)
  rw [← Real.rpow_natCast (1+|y|) 2,←Real.rpow_mul (by positivity)] at h₂
  rw [show ((2:ℕ):ℝ)*((v.2:ℝ)/2) = (v.2:ℝ) by push_cast; ring] at h₂
  exact h₂

end
end MasulloRH.SobolevStrip

end StandaloneSobolevStripIndependent

section StandaloneStripTestAmplitude

open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff BigOperators
namespace MasulloRH.StripTrace
noncomputable section

def lap (f : ℝ → ℂ) (s : ℂ) := ∫ y : ℝ, Complex.exp (s*y)*f y

theorem log_compact (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasCompactSupport (fun y => φ (Real.exp y)) := by
  have hk := hφ.2.1.image_of_continuousOn (Real.continuousOn_log.mono (fun x hx => ne_of_gt (hφ.2.2.1 hx)))
  exact HasCompactSupport.of_support_subset_isCompact hk (fun x hx =>
    ⟨Real.exp x,subset_tsupport _ hx,Real.log_exp x⟩)

theorem mellin_eq_lap (φ : ℝ → ℂ) (w : ℂ) : mellin φ w = lap (fun y => φ (Real.exp y)) w := by
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have him : Real.exp '' univ = Ioi 0 := by rw [image_univ,Real.range_exp]
  unfold mellin lap
  rw [← him,integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,setIntegral_univ]
  apply integral_congr_ae; filter_upwards with x
  rw [abs_of_pos (Real.exp_pos _),Complex.real_smul,smul_eq_mul,Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp,
    Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2; ring

theorem mellin_entire (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) : Differentiable ℂ (mellin φ) := by
  have hz0 : φ =ᶠ[𝓝[>] (0:ℝ)] 0 := by
    have h0 : 0 ∉ tsupport φ := fun h => (lt_irrefl (0:ℝ)) (hφ.2.2.1 h)
    exact (notMem_tsupport_iff_eventuallyEq.mp h0).filter_mono nhdsWithin_le_nhds
  have hzT : φ =ᶠ[atTop] 0 := by
    obtain ⟨M,hM⟩ := hφ.2.1.bddAbove
    filter_upwards [eventually_gt_atTop M] with x hx
    exact image_eq_zero_of_notMem_tsupport (fun hx' => (not_le_of_gt hx) (hM hx'))
  intro s
  apply mellin_differentiableAt_of_isBigO_rpow (a:=s.re+1) (b:=s.re-1)
    (hφ.1.continuous.locallyIntegrable.locallyIntegrableOn _)
    ((isBigO_zero _ _).congr' hzT.symm EventuallyEq.rfl) (by linarith)
    ((isBigO_zero _ _).congr' hz0.symm EventuallyEq.rfl) (by linarith)

private theorem cyclic_StripTestAmplitude_lap_integrable {f : ℝ → ℂ} (hc : Continuous f) (hs : HasCompactSupport f) (s : ℂ) :
    Integrable (fun y : ℝ => Complex.exp (s*y)*f y) :=
  ((show Continuous (fun y : ℝ => Complex.exp (s*y)) by fun_prop).mul hc).integrable_of_hasCompactSupport hs.mul_left

theorem lap_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (s : ℂ) :
    lap (deriv f) s = -s * lap f s := by
  let E (y : ℝ) := Complex.exp (s*y)
  have hE (y : ℝ) : HasDerivAt E (s*E y) y := by
    simpa [E,mul_comm] using! (((hasDerivAt_id (y:ℂ)).const_mul s).cexp.comp_ofReal)
  have hI := cyclic_StripTestAmplitude_lap_integrable hf.continuous hs s
  have hd := hf.continuous_deriv (by simp)
  have hI' := cyclic_StripTestAmplitude_lap_integrable hd hs.deriv s
  have hJ : Integrable (fun x : ℝ => s*E x*f x) := by
    simpa only [mul_assoc,E] using hI.const_mul s
  have hh := integral_mul_deriv_eq_deriv_mul_of_integrable (u:=E) (v:=f)
    (fun y _ => hE y) (fun y _ => (hf.differentiable (by simp) y).hasDerivAt) hI' hJ hI
  change (∫ x : ℝ, E x*deriv f x) = -s*(∫ x : ℝ, E x*f x)
  rw [hh]
  simp only [mul_assoc,integral_const_mul,neg_mul]

private theorem cyclic_StripTestAmplitude_uniform_bound {f : ℝ → ℂ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℂ, |s.re|≤2 → ‖lap f s‖ ≤ B := by
  let G := fun x : ℝ => Real.exp (2*|x|)*‖f x‖
  have hG : Integrable G := ((show Continuous (fun x : ℝ => Real.exp (2*|x|)) by fun_prop).mul
    hf.norm).integrable_of_hasCompactSupport hcs.norm.mul_left
  refine ⟨∫ x, G x, integral_nonneg (fun x => mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)),?_⟩
  intro s hs
  apply (norm_integral_le_integral_norm _).trans (integral_mono (cyclic_StripTestAmplitude_lap_integrable hf hcs s).norm hG (fun x => ?_))
  dsimp [G]
  rw [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hs (abs_nonneg _))))

theorem lap_power_bound (r : ℕ) (f : ℝ→ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ∃ B : ℝ, 0≤B ∧ ∀ s : ℂ, |s.re|≤2 → ‖s‖^r*‖lap f s‖ ≤ B := by
  induction r generalizing f with
  | zero => simpa using cyclic_StripTestAmplitude_uniform_bound hf.continuous hs
  | succ r ih =>
    obtain ⟨B,hB,h⟩ := ih _ (ContDiff.deriv' (by simpa using hf)) hs.deriv
    refine ⟨B,hB,fun s hh => ?_⟩
    have hx := h s hh
    rwa [lap_deriv hf hs,norm_mul,norm_neg,←mul_assoc,←pow_succ] at hx

theorem mellin_strip_rapid (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) (r : ℕ) :
    ∃ B : ℝ, 0≤B ∧ ∀ s : ℂ, |s.re|≤2 → (1+|s.im|)^r*‖mellin φ s‖ ≤ B := by
  let f (y : ℝ) := φ (Real.exp y)
  have hs := log_compact φ hφ
  have hf : ContDiff ℝ ∞ f := hφ.1.comp Real.contDiff_exp
  obtain ⟨B,hB,h0⟩ := cyclic_StripTestAmplitude_uniform_bound hf.continuous hs
  obtain ⟨D,hD,hd⟩ := lap_power_bound r f hf hs
  refine ⟨2^r*(B+D),by positivity,?_⟩
  intro s h
  rw [mellin_eq_lap]
  change (1+|s.im|)^r*‖lap f s‖ ≤ _
  by_cases ht : |s.im|≤1
  · exact (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith : 1+|s.im|≤2) r) (h0 s h)
      (norm_nonneg _) (by positivity)).trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  · have he : 1+|s.im| ≤ 2*‖s‖ := by linarith [Complex.abs_im_le_norm s]
    calc
      _ ≤ (2*‖s‖)^r*‖lap f s‖ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he r) (norm_nonneg _)
      _ ≤ _ := by rw [mul_pow,mul_assoc]; exact mul_le_mul_of_nonneg_left ((hd s h).trans (by linarith)) (by positivity)
end
end MasulloRH.StripTrace

end StandaloneStripTestAmplitude

section StandaloneStripJetZeroData

open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace MasulloRH.StripJetSpace
noncomputable section

abbrev Z (b : ℝ) := ZetaZerosInTraceStrip b
abbrev mult {b : ℝ} (z : Z b) := analyticOrderNatAt riemannZeta z.val
abbrev center {b : ℝ} (z : Z b) := z.val-(1/2:ℂ)
theorem mem_strip {b : ℝ} (z : Z b) : |(center z).re|<b := by
  simpa [center] using z.prop.2.2.2

def cutoff (n : ℕ) : ℝ := 5/2+2*(n:ℝ)
def low (b : ℝ) (n : ℕ) : Set (Z b) := {z | |z.val.im|≤cutoff n}
abbrev Low (b : ℝ) (n : ℕ) := ↥(low b n)
theorem mult_pos {b : ℝ} (z : Z b) : 0 < mult z := by
  have h1 : z.val ≠ 1 := fun h => (not_lt_of_ge (le_of_eq (congrArg Complex.re h).symm)) z.prop.2.2.1
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hf := analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  have hne := (analyticOn_riemannZeta _ h1).analyticOrderAt_ne_zero.mpr z.prop.1
  exact Nat.pos_of_ne_zero (fun h => (ENat.toNat_eq_zero.mp h).elim hne hf)

theorem low_weight {b : ℝ} {n : ℕ} (z : Low b n) :
    (mult z.val:ℝ) ≤ (1+(cutoff n)^2)*zeroDecayWeight b z.val := by
  have hz : |z.val.val.im|≤cutoff n := z.prop
  have hi := pow_le_pow_left₀ (abs_nonneg _) hz 2
  rw [sq_abs] at hi
  unfold zeroDecayWeight
  rw [← mul_div_assoc, le_div_iff₀ (by positivity)]
  change (mult z.val:ℝ)*(1+_) ≤ (1+_)*(mult z.val:ℝ)
  nlinarith only [mul_nonneg (sub_nonneg.mpr hi) (Nat.cast_nonneg (α:=ℝ) (mult z.val))]

theorem low_finite (b : ℝ) (n : ℕ) : (low b n).Finite := by
  by_cases hb : 0<b
  · let t := 1/(1+(cutoff n)^2)
    have ht : 0<t := by dsimp [t]; positivity
    have he := (weighted_zero_summability b hb).tendsto_cofinite_zero.eventually_lt_const ht
    apply (Filter.eventually_cofinite.mp he).subset
    intro z hz
    change ¬zeroDecayWeight b z<t
    apply not_lt.mpr
    rw [div_le_iff₀ (by positivity : 0<1+(cutoff n)^2),mul_comm]
    exact (Nat.one_le_cast.mpr (mult_pos z)).trans (low_weight ⟨z,hz⟩)
  · apply Set.finite_empty.subset
    intro z _
    exact (hb ((abs_nonneg _).trans_lt (mem_strip z))).elim

noncomputable instance (b : ℝ) (n : ℕ) : Fintype (Low b n) := (low_finite b n).fintype

theorem low_sums_tendsto {b : ℝ} {F : Type*} [NormedAddCommGroup F] {f : Z b → F} (hf : Summable f) :
    Tendsto (fun n => ∑ z : Low b n, f z.val) atTop (𝓝 (∑' z,f z)) := by
  classical
  let L := fun n => (low_finite b n).toFinset
  have hL : Tendsto L atTop atTop := by
    apply tendsto_atTop.mpr
    intro s
    change ∀ᶠ n : ℕ in atTop,∀ z∈s,z∈L n
    apply s.eventually_all.mpr
    intro z _
    obtain ⟨N,hN⟩ := exists_nat_ge |z.val.im|
    filter_upwards [eventually_ge_atTop N] with n hn
    change z∈(low_finite b n).toFinset
    rw [Set.Finite.mem_toFinset]
    change |z.val.im| ≤ 5/2+2*(n:ℝ)
    have h : (N:ℝ)≤n := by exact_mod_cast hn
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have he (n : ℕ) : ∑ z ∈ L n,f z=∑ z : Low b n,f z.val :=
    Finset.sum_subtype _ (fun _ => Set.Finite.mem_toFinset _) _
  simpa only [Function.comp_def,he] using hf.hasSum.comp hL

theorem rational_trace_summable {b : ℝ} (hb : 0<b) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    Summable (zetaTraceTerm φ b) := by
  obtain ⟨B,hB,h⟩ := StripTrace.mellin_strip_rapid φ hφ 2
  apply ((weighted_zero_summability b hb).mul_left B).of_norm_bounded
  intro z
  have hc : |(center z).re|≤2 := by
    rw [abs_le]
    simp only [center,Complex.sub_re]; norm_num; constructor <;> linarith [z.prop.2.1,z.prop.2.2.1]
  have hi : (center z).im=z.val.im := by simp [center]
  have he := h (center z) hc
  rw [hi] at he
  have hden : 1+z.val.im^2 ≤ (1+|z.val.im|)^2 := by nlinarith [abs_nonneg z.val.im,sq_abs z.val.im]
  have hdiv : ‖mellin φ (center z)‖≤B/(1+z.val.im^2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right hden (norm_nonneg _)).trans he
  change ‖(mult z:ℂ)*mellin φ (center z)‖ ≤ B*zeroDecayWeight b z
  rw [norm_mul,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)).trans_eq (by unfold zeroDecayWeight; ring)

end
end MasulloRH.StripJetSpace

end StandaloneStripJetZeroData

section StandaloneStripFiniteTrace

open MasulloGRH Set Filter
open scoped Topology BigOperators
namespace MasulloRH.StripTrace
noncomputable section
private lemma cyclic_StripFiniteTrace_padded_sum {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (d : ℕ) (g : ℕ → E) (hg : ∀ i, d ≤ i → g i = 0) :
    HasSum g (∑ i : Fin d, g i.val) := by
  rw [Fin.sum_univ_eq_sum_range]
  exact hasSum_sum_of_ne_finset_zero (fun i hi => hg i (Nat.le_of_not_gt (by simpa using hi)))

theorem trace_on_finite_span {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype ι]
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] (B : Module.Basis ι ℂ W)
    (A : H →L[ℂ] H) (hA : ∀ u, A u ∈ W) :
    operatorTrace A = ∑ i, B.coord i (⟨A (B i : H), hA _⟩ : W) := by
  classical
  let d := Fintype.card ι
  let e : Fin d ≃ ι := (Fintype.equivFin ι).symm
  let L (i : ι) : H →L[ℂ] ℂ := (LinearMap.toContinuousLinearMap (B.coord i)).comp (A.codRestrict W hA)
  let x (j : ℕ) : H := if h : j < d then (InnerProductSpace.toDual ℂ H).symm (L (e ⟨j,h⟩)) else 0
  let y (j : ℕ) : H := if h : j < d then (B (e ⟨j,h⟩) : H) else 0
  have hpair (j : Fin d) (u : H) : inner ℂ (x j.val) u = L (e j) u := by
    simp [x, j.isLt, InnerProductSpace.toDual_symm_apply]
  have hy (j : Fin d) : y j.val = (B (e j) : H) := by simp [y, j.isLt]
  have hy0 {j : ℕ} (hj : d ≤ j) : y j = 0 := by simp [y, Nat.not_lt.mpr hj]
  have hcost := cyclic_StripFiniteTrace_padded_sum d (fun j => ‖x j‖ * ‖y j‖) (fun j hj => by simp [hy0 hj])
  have hrepr (u : H) : HasSum (fun j => inner ℂ (x j) u • y j) (A u) := by
    have h := cyclic_StripFiniteTrace_padded_sum d (fun j => inner ℂ (x j) u • y j) (fun j hj => by simp [hy0 hj])
    convert h using 1
    simp only [hpair, hy]
    rw [e.sum_comp (fun i => L i u • (B i : H))]
    have hb := congrArg W.subtype (B.sum_repr ((A.codRestrict W hA) u))
    rw [map_sum] at hb
    simpa only [L, ContinuousLinearMap.comp_apply, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply, map_smul, Submodule.subtype_apply, ContinuousLinearMap.coe_codRestrict_apply] using hb.symm
  rw [operatorTrace_of_nuclear_series A x y hcost.summable hrepr,
    (cyclic_StripFiniteTrace_padded_sum d (fun j => inner ℂ (x j) (y j)) (fun j hj => by simp [hy0 hj])).tsum_eq]
  simp only [hpair, hy]
  exact e.sum_comp (fun i => L i (B i : H))

end
end MasulloRH.StripTrace

end StandaloneStripFiniteTrace

section StandaloneStripJetDepth

open Set Filter MeasureTheory MasulloGRH
open scoped Topology BigOperators
namespace MasulloRH.StripJetDepth
noncomputable section
open StripJetSpace (Z Low mult center low low_finite low_weight cutoff low_sums_tendsto rational_trace_summable)
variable {b : ℝ} {d : Z b → ℕ}

abbrev Index (d : Z b → ℕ) := Σ z : Z b, Fin (d z)
abbrev StageIndex (d : Z b → ℕ) (n : ℕ) := Σ z : Low b n, Fin (d z.val)

def lower (i : Index d) (j : Fin (i.2.val+1)) : Index d :=
  ⟨i.1,⟨j.val,lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.2.isLt)⟩⟩

def entry {n : ℕ} (i : StageIndex d n) : Index d := ⟨i.1.val,i.2⟩

theorem entry_injective (d : Z b → ℕ) (n : ℕ) : Function.Injective (@entry b d n) := by
  rintro ⟨⟨z,hz⟩,i⟩ ⟨⟨t,ht⟩,j⟩ he
  have hzt : z=t := congrArg Sigma.fst he
  subst t
  have h : i.val=j.val := congrArg (fun j : Index d => j.2.val) he
  cases Fin.ext h
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def stage (u : Index d → E) (n : ℕ) : Submodule ℂ E :=
  Submodule.span ℂ (Set.range (fun i : StageIndex d n => u (entry i)))

def stageBasis {u : Index d → E} (hu : LinearIndependent ℂ u) (n : ℕ) :
    Module.Basis (StageIndex d n) ℂ (stage u n) :=
  Module.Basis.span (hu.comp _ (entry_injective d n))

@[simp] theorem stageBasis_coe {u : Index d → E} (hu : LinearIndependent ℂ u) (n : ℕ)
    (i : StageIndex d n) : (stageBasis hu n i : E)=u (entry i) :=
  Module.Basis.coe_span_apply _ _

theorem stage_finite (u : Index d → E) (n : ℕ) : FiniteDimensional ℂ (stage u n) :=
  Module.Finite.span_of_finite ℂ (Set.finite_range _)

theorem stage_finrank {u : Index d → E} (hu : LinearIndependent ℂ u) (n : ℕ) :
    Module.finrank ℂ (stage u n) = ∑ z : Low b n, d z.val := by
  rw [Module.finrank_eq_card_basis (stageBasis hu n),Fintype.card_sigma]
  simp

theorem stage_mono (u : Index d → E) : Monotone (stage u) := by
  intro n m hnm
  apply Submodule.span_le.mpr
  rintro x ⟨i,rfl⟩
  have hnm' : cutoff n ≤ cutoff m := by unfold cutoff; gcongr
  have hm : i.1.val ∈ low b m := le_trans (show |i.1.val.val.im|≤cutoff n from i.1.prop) hnm'
  exact Submodule.subset_span ⟨⟨⟨i.1.val,hm⟩,i.2⟩,rfl⟩

theorem stage_finrank_bound {u : Index d → E} (hb : 0<b) (hd : ∀ z, d z ≤ mult z) (hu : LinearIndependent ℂ u) (n : ℕ) :
    (Module.finrank ℂ (stage u n):ℝ) ≤ (8*∑' z : Z b,zeroDecayWeight b z)*((n:ℝ)+1)^2 := by
  classical
  rw [stage_finrank hu,Nat.cast_sum]
  have hsub := (weighted_zero_summability b hb).tsum_subtype_le (zeroDecayWeight b) (low b n)
    (fun z => by unfold zeroDecayWeight; positivity)
  rw [tsum_fintype] at hsub
  calc
    _ ≤ ∑ z : Low b n,(1+(cutoff n)^2)*zeroDecayWeight b z.val :=
      Finset.sum_le_sum fun z _ => (Nat.cast_le.mpr (hd z.val)).trans (low_weight z)
    _ = (1+(cutoff n)^2)* ∑ z : Low b n,zeroDecayWeight b z.val := by rw [Finset.mul_sum]
    _ ≤ (1+(cutoff n)^2)* ∑' z : Z b,zeroDecayWeight b z :=
      mul_le_mul_of_nonneg_left hsub (by positivity)
    _ ≤ _ := by
      have hn : 0≤(n:ℝ) := by positivity
      have h : 1+(cutoff n)^2 ≤ 8*((n:ℝ)+1)^2 := by unfold cutoff; nlinarith [sq_nonneg (n:ℝ)]
      have hpos : 0 ≤ ∑' z : Z b,zeroDecayWeight b z := tsum_nonneg (fun z => by unfold zeroDecayWeight; positivity)
      nlinarith only [mul_le_mul_of_nonneg_right h hpos]

variable [CompleteSpace E]

def stageLower {n : ℕ} (i : StageIndex d n) (j : Fin (i.2.val+1)) : StageIndex d n :=
  ⟨i.1,⟨j.val,lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.2.isLt)⟩⟩

theorem stageLower_last {n : ℕ} (i : StageIndex d n) : stageLower i (Fin.last i.2.val)=i := by
  cases i
  rfl

theorem stageLower_eq_iff {n : ℕ} (i : StageIndex d n) (j : Fin (i.2.val+1)) :
    stageLower i j=i ↔ j=Fin.last i.2.val := by
  constructor
  · intro h
    exact Fin.ext (congrArg (fun t : StageIndex d n => t.2.val) h)
  · rintro rfl
    exact stageLower_last i

abbrev Triangular (u : Index d → E) (L : E→L[ℂ] E) (a : (i : Index d) → Fin (i.2.val+1) → ℂ) :=
  ∀ i, L (u i)=∑ j : Fin (i.2.val+1), a i j • u (lower i j)

omit [CompleteSpace E] in
theorem stage_invariant {u : Index d → E} {L : E→L[ℂ] E}
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a) (n : ℕ) :
    ∀ x∈stage u n,L x∈stage u n := by
  change stage u n ≤ (stage u n).comap L.toLinearMap
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L (u (entry i))∈stage u n
  rw [ha]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨stageLower i j,rfl⟩)

noncomputable instance stageFiniteDimensional (u : Index d → E) (n : ℕ) :
    FiniteDimensional ℂ (stage u n) := stage_finite u n

def projectConvolution (u : Index d → E) (L : E→L[ℂ] E) (n : ℕ) : E→L[ℂ] E :=
  (stage u n).starProjection.comp L

omit [CompleteSpace E] in
theorem projectConvolution_mem (u : Index d → E) (L : E→L[ℂ] E) (n : ℕ) (x : E) :
    projectConvolution u L n x∈stage u n := (stage u n).starProjection_apply_mem _

theorem stage_trace {u : Index d → E} (hu : LinearIndependent ℂ u) {L : E→L[ℂ] E}
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a) (n : ℕ) :
    operatorTrace (projectConvolution u L n)=
      ∑ i : StageIndex d n,a (entry i) (Fin.last i.2.val) := by
  classical
  let B := stageBasis hu n
  rw [StripTrace.trace_on_finite_span (stage u n) B _ (projectConvolution_mem u L n)]
  apply Finset.sum_congr rfl
  intro i _
  have he : (⟨projectConvolution u L n (B i),projectConvolution_mem u L n _⟩ : stage u n) =
      ∑ j : Fin (i.2.val+1), a (entry i) j • B (stageLower i j) := by
    apply Subtype.ext
    change (stage u n).starProjection (L ((B i : stage u n):E)) = (stage u n).subtype _
    rw [Submodule.starProjection_eq_self_iff.mpr (stage_invariant ha n _ (B i).property),map_sum]
    simp only [B,stageBasis_coe,map_smul,Submodule.subtype_apply]
    exact ha (entry i)
  rw [he,map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single (Fin.last i.2.val)]
  · simp [stageLower_last,Module.Basis.coord_apply]
  · intro j _ hj
    have hij := (stageLower_eq_iff i j).not.mpr hj
    simp [Module.Basis.coord_apply,Ne.symm hij]
  · simp

omit [CompleteSpace E] in
theorem mem_stage_of_low (u : Index d → E) (n : ℕ) (i : Index d) (hi : |i.1.val.im|≤cutoff n) :
    u i ∈ stage u n := Submodule.subset_span ⟨⟨⟨i.1,hi⟩,i.2⟩,rfl⟩

theorem stage_trace_grouped {u : Index d → E} (hu : LinearIndependent ℂ u) {L : E→L[ℂ] E}
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a) (g : Z b → ℂ)
    (hg : ∀ i : Index d, a i (Fin.last i.2.val)=g i.1) (n : ℕ) :
    operatorTrace (projectConvolution u L n)=∑z : Low b n,(d z.val:ℂ)*g z.val := by
  rw [stage_trace hu ha n,Fintype.sum_sigma]
  simp only [hg,entry,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem stage_trace_limit {u : Index d → E} (hu : LinearIndependent ℂ u) {L : E→L[ℂ] E}
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a) (g : Z b → ℂ)
    (hg : ∀ i : Index d, a i (Fin.last i.2.val)=g i.1)
    (hs : Summable (fun z : Z b => (d z:ℂ)*g z)) :
    Tendsto (fun n => operatorTrace (projectConvolution u L n)) atTop (𝓝 (∑' z : Z b,(d z:ℂ)*g z)) := by
  simp only [stage_trace_grouped hu ha g hg]
  exact low_sums_tendsto hs

theorem test_summable (hb : 0<b) (hd : ∀ z, d z ≤ mult z) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    Summable (fun z : Z b => (d z:ℂ)*mellin φ (center z)) := by
  apply (rational_trace_summable hb φ hφ).norm.of_norm_bounded
  intro z
  change ‖(d z:ℂ)*mellin φ (center z)‖ ≤ ‖(mult z:ℂ)*mellin φ (center z)‖
  rw [norm_mul,norm_mul,Complex.norm_natCast,Complex.norm_natCast]
  gcongr
  exact hd z

theorem test_trace_limit {u : Index d → E} (hu : LinearIndependent ℂ u) {L : E→L[ℂ] E}
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a)
    (hb : 0<b) (hd : ∀ z, d z ≤ mult z) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ)
    (hg : ∀ i : Index d, a i (Fin.last i.2.val)=mellin φ (center i.1)) :
    Tendsto (fun n => operatorTrace (projectConvolution u L n)) atTop
      (𝓝 (∑' z : Z b,(d z:ℂ)*mellin φ (center z))) :=
  stage_trace_limit hu ha _ hg (test_summable hb hd φ hφ)

end
end MasulloRH.StripJetDepth

end StandaloneStripJetDepth

section StandaloneStripJetDepthModel

open Set Filter
open scoped Topology BigOperators
namespace MasulloRH.StripJetDepth
noncomputable section
open StripJetSpace (Z)
variable {b : ℝ} {d : Z b → ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def spanModel (u : Index d → E) : Submodule ℂ E :=
  (Submodule.span ℂ (Set.range u)).topologicalClosure

instance [CompleteSpace E] (u : Index d → E) : CompleteSpace (spanModel u) :=
  inferInstanceAs (CompleteSpace (Submodule.topologicalClosure _))

theorem mem_spanModel (u : Index d → E) (i : Index d) : u i∈spanModel u :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i,rfl⟩)

def inside (P : Submodule ℂ E) (u : Index d → E) (h : ∀ i,u i∈P) (i : Index d) : P := ⟨u i,h i⟩

theorem inside_independent (P : Submodule ℂ E) {u : Index d → E} (h : ∀ i,u i∈P)
    (hu : LinearIndependent ℂ u) : LinearIndependent ℂ (inside P u h) :=
  LinearIndependent.of_comp P.subtype hu

theorem inside_dense (P : Submodule ℂ E) {u : Index d → E} (h : ∀ i,u i∈P)
    (hP : P=spanModel u) : Dense (Submodule.span ℂ (Set.range (inside P u h)) : Set P) := by
  rw [Subtype.dense_iff]
  have he : P.subtype '' (Submodule.span ℂ (Set.range (inside P u h)) : Set P) =
      (Submodule.span ℂ (Set.range u) : Set E) := by
    change ((Submodule.span ℂ (Set.range (inside P u h))).map P.subtype : Set E) = _
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  change (P : Set E) ⊆ closure (P.subtype '' _)
  rw [he,hP,spanModel,Submodule.topologicalClosure_coe]

abbrev modelV (u : Index d → E) := inside (spanModel u) u (mem_spanModel u)

theorem modelV_dense (u : Index d → E) :
    Dense (Submodule.span ℂ (Set.range (modelV u)) : Set (spanModel u)) :=
  inside_dense _ _ rfl

theorem modelV_independent {u : Index d → E} (hu : LinearIndependent ℂ u) :
    LinearIndependent ℂ (modelV u) := inside_independent _ _ hu

theorem spanModel_invariant {u : Index d → E} {L : E→L[ℂ] E}
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a) :
    ∀ x∈spanModel u,L x∈spanModel u := by
  apply (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).mp
  apply Submodule.topologicalClosure_mem_invtSubmodule
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  change Submodule.span ℂ (Set.range u) ≤ (Submodule.span ℂ (Set.range u)).comap _
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change L (u i) ∈ Submodule.span ℂ (Set.range u)
  rw [ha]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨lower i j,rfl⟩)

theorem restrict_norm_le (P : Submodule ℂ E) (L : E→L[ℂ] E) (hL : ∀ x∈P,L x∈P) :
    ‖L.restrict hL‖≤‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  exact fun x => L.le_opNorm (x:E)

theorem inside_triangular (P : Submodule ℂ E) {u : Index d → E} (h : ∀ i,u i∈P)
    {L : E→L[ℂ] E} (hL : ∀ x∈P,L x∈P)
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a) :
    Triangular (inside P u h) (L.restrict hL) a := by
  intro i
  apply Subtype.ext
  change L (u i) = P.subtype _
  rw [map_sum,ha]
  simp only [LinearMap.map_smul_of_tower]; rfl

def modelOperator {u : Index d → E} {L : E→L[ℂ] E}
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a) : spanModel u→L[ℂ] spanModel u :=
  L.restrict (spanModel_invariant ha)

theorem modelOperator_triangular {u : Index d → E} {L : E→L[ℂ] E}
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a) :
    Triangular (modelV u) (modelOperator ha) a :=
  inside_triangular _ _ _ ha

theorem norm_modelOperator_le {u : Index d → E} {L : E→L[ℂ] E}
    {a : (i : Index d) → Fin (i.2.val+1) → ℂ} (ha : Triangular u L a) :
    ‖modelOperator ha‖ ≤ ‖L‖ := restrict_norm_le _ L _

end
end MasulloRH.StripJetDepth

end StandaloneStripJetDepthModel

section StandaloneStripPublicModes

open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace MasulloRH.WeightedStripTrace
noncomputable section
open SobolevStrip (P H Admissible)
open StripJetSpace (Z mult center)
abbrev Full := Z (1/2)
abbrev Space (v : P) := rationalStripJetSpace (v.1:ℝ) (v.2:ℝ)

def degree (v : P) (z : Full) : ℕ :=
  if |z.val.re-1/2|<(v.1:ℝ) then mult z
  else if |z.val.re-1/2|=(v.1:ℝ) then min (mult z) ⌈(v.2:ℝ)-1/2⌉₊ else 0

theorem degree_le (v : P) (z : Full) : degree v z ≤ mult z := by
  unfold degree; split_ifs <;> first | rfl | exact min_le_left _ _ | exact Nat.zero_le _

theorem lt_degree (v : P) (z : Full) (r : ℕ) :
    r<degree v z ↔ r < mult z ∧ (|z.val.re-1/2|<(v.1:ℝ) ∨
      (|z.val.re-1/2|=(v.1:ℝ) ∧ (r:ℝ)+1/2<(v.2:ℝ))) := by
  by_cases hi : |z.val.re-1/2|<(v.1:ℝ)
  · rw [degree,if_pos hi]
    exact ⟨fun h => ⟨h,Or.inl hi⟩,fun h => h.1⟩
  by_cases he : |z.val.re-1/2|=(v.1:ℝ)
  · rw [degree,if_neg hi,if_pos he,lt_min_iff]
    constructor
    · rintro ⟨hm,h⟩
      exact ⟨hm,Or.inr ⟨he,by linarith [Nat.lt_ceil.mp h]⟩⟩
    · rintro ⟨hm,h|⟨_,h⟩⟩
      · exact (hi h).elim
      exact ⟨hm,Nat.lt_ceil.mpr (by linarith)⟩
  rw [degree,if_neg hi,if_neg he]
  constructor
  · exact fun h => (Nat.not_lt_zero r h).elim
  · rintro ⟨_,h|⟨h,_⟩⟩
    · exact (hi h).elim
    exact (he h).elim

abbrev Index (v : P) := StripJetDepth.Index (degree v)

def locations {v : P} (i : Index v) : ℂ × ℕ := (center i.1,i.2.val)

theorem locations_injective (v : P) : Function.Injective (@locations v) := by
  rintro ⟨z,i⟩ ⟨t,j⟩ he
  have h₁ : center z = center t := congrArg Prod.fst he
  have hzt : z=t := Subtype.ext (sub_left_inj.mp h₁)
  subst t
  have h₂ : i.val=j.val := congrArg Prod.snd he
  cases Fin.ext h₂
  rfl

theorem admissible {v : P} (i : Index v) : Admissible v (center i.1) i.2.val := by
  obtain h|⟨h₁,h₂⟩ := ((lt_degree v i.1 _).mp i.2.isLt).2
  · exact Or.inl (by simpa [StripJetSpace.center] using h)
  exact Or.inr ⟨by simpa [StripJetSpace.center] using h₁.le,h₂⟩

def mode (v : P) (i : Index v) : H := SobolevStrip.jet v (center i.1) i.2.val

theorem space_eq (v : P) :
    Space v = (Submodule.span ℂ (Set.range (mode v))).topologicalClosure := by
  unfold Space rationalStripJetSpace
  congr 2
  ext f
  constructor
  · rintro ⟨z,hz,h0,h1,r,hr,hw,hf⟩
    let t : Full := ⟨z,hz,h0,h1,abs_lt.mpr ⟨by linarith,by linarith⟩⟩
    let i : Index v := ⟨t,⟨r,(lt_degree v t r).mpr ⟨hr,hw⟩⟩⟩
    refine ⟨i, Lp.ext ?_⟩
    exact (SobolevStrip.jet_apply_ae (admissible i)).trans hf.symm
  · rintro ⟨i,rfl⟩
    obtain ⟨hr,hw⟩ := (lt_degree v i.1 i.2.val).mp i.2.isLt
    exact ⟨i.1.val,i.1.prop.1,i.1.prop.2.1,i.1.prop.2.2.1,i.2.val,hr,hw,
      SobolevStrip.jet_apply_ae (admissible i)⟩

def u (v : P) (i : Index v) : Space v :=
  ⟨mode v i, by rw [space_eq]; exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i,rfl⟩)⟩

theorem u_independent (v : P) : LinearIndependent ℂ (u v) :=
  LinearIndependent.of_comp (Space v).subtype
    (SobolevStrip.linearIndependent_jet v locations (locations_injective v) admissible)

theorem u_dense (v : P) : Dense (Submodule.span ℂ (Set.range (u v)) : Set (Space v)) := by
  exact StripJetDepth.inside_dense (Space v) (fun i => (u v i).prop) (space_eq v)

end
end MasulloRH.WeightedStripTrace

end StandaloneStripPublicModes

section StandaloneStripPhysicalMoments

open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace MasulloRH.StripPhysical
noncomputable section

def moment (k : ℝ→ℂ) (z : ℂ) (j : ℕ) : ℂ :=
  ∫ y : ℝ, k y*(y:ℂ)^j*Complex.exp (z*(y:ℂ))

theorem moment_integrable {b : ℝ} {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) {z : ℂ} (hz : |z.re|<b) (j : ℕ) :
    Integrable (fun y : ℝ => k y*(y:ℂ)^j*Complex.exp (z*(y:ℂ))) := by
  obtain ⟨C,_,hb⟩ := polynomial_exp_bound hz j
  apply (hW.mul_const C).mono'
  · apply (hk.mul (show Continuous (fun y : ℝ => (y:ℂ)^j) by fun_prop).aestronglyMeasurable).mul
    exact (show Continuous (fun y : ℝ => Complex.exp (z*(y:ℂ))) by fun_prop).aestronglyMeasurable
  · apply Eventually.of_forall
    intro y
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left (hb y) (norm_nonneg (k y))).trans_eq (by ring)

end
end MasulloRH.StripPhysical
end StandaloneStripPhysicalMoments

section StandaloneSobolevStripMoments

open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace MasulloRH.SobolevStrip
noncomputable section
abbrev moment := StripPhysical.moment

theorem exp_integrable_of_growth (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) :
    Integrable (fun y => ‖k y‖*Real.exp ((v.1:ℝ)*|y|)) := by
  apply hW.mono' (hk.norm.mul (show Continuous (fun y : ℝ => Real.exp ((v.1:ℝ)*|y|)) by fun_prop).aestronglyMeasurable)
  filter_upwards with y
  change ‖‖k y‖*Real.exp ((v.1:ℝ)*|y|)‖ ≤ ‖k y‖*growth v y
  rw [Real.norm_of_nonneg (by positivity),growth]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact le_mul_of_one_le_left (Real.exp_nonneg _) (Real.one_le_rpow (by linarith [abs_nonneg y]) v.2.prop)

theorem moment_integrable (v : P) {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) {z : ℂ} {r : ℕ} (hr : Admissible v z r) :
    Integrable (fun y : ℝ => k y*(y:ℂ)^r*Complex.exp (z*(y:ℂ))) := by
  rcases hr with hz|⟨hz,hp⟩
  · exact StripPhysical.moment_integrable hk (exp_integrable_of_growth v _ hk hW) hz r
  apply hW.mono'
  · exact ((hk.mul (show Continuous (fun y : ℝ => (y:ℂ)^r) by fun_prop).aestronglyMeasurable).mul
      (show Continuous (fun y : ℝ => Complex.exp (z*(y:ℂ))) by fun_prop).aestronglyMeasurable)
  filter_upwards with y
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,growth]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul _ (Real.exp_le_exp.mpr (by
    have h := le_abs_self (z.re*y)
    rw [abs_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right hz (abs_nonneg _)))) (Real.exp_nonneg _) (by positivity)
  calc
    _ ≤ (1+|y|)^r := by gcongr; linarith
    _ ≤ (1+|y|)^(v.2:ℝ) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg y]) (by linarith)

theorem convolution_jet (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*growth v y)) {z : ℂ} {r : ℕ} (hr : Admissible v z r) :
    convolution v k hk hW (jet v z r) =
      ∑ s ∈ Finset.range (r+1), ((r.choose s:ℂ)*moment k z (r-s)) • jet v z s := by
  let m (j : ℕ) (y : ℝ) := k y*(y:ℂ)^j*Complex.exp (z*(y:ℂ))
  have hf (y : ℝ) : k y • translation v y (jet v z r) =
      ∑ s ∈ Finset.range (r+1), ((r.choose s:ℂ)*m (r-s) y) • jet v z s := by
    rw [translation_jet hr,Finset.smul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [smul_smul]; congr 1; dsimp [m]; ring
  rw [convolution_apply]
  simp_rw [hf]
  rw [integral_finsetSum _ (fun s _ =>
    ((moment_integrable v hk hW (admissible_mono hr (Nat.sub_le r s))).const_mul (r.choose s:ℂ)).smul_const (jet v z s))]
  exact Finset.sum_congr rfl fun s _ => by rw [integral_smul_const,integral_const_mul]; rfl

theorem integrable_growth_of_exp (v : P) {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hE : Integrable (fun y => ‖k y‖*Real.exp (((v.1:ℝ)+1)*|y|))) :
    Integrable (fun y => ‖k y‖*growth v y) := by
  apply (hE.const_mul (polyConstant v.2)).mono' (hk.norm.mul (continuous_growth v).aestronglyMeasurable)
  filter_upwards with y
  change ‖‖k y‖*growth v y‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (growth_pos _ _).le)]
  apply (mul_le_mul_of_nonneg_left (growth_le_exp v y) (norm_nonneg _)).trans_eq; ring

theorem norm_convolution_le_exp (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hE : Integrable (fun y => ‖k y‖*Real.exp (((v.1:ℝ)+1)*|y|))) :
    ‖convolution v k hk (integrable_growth_of_exp v hk hE)‖ ≤
      polyConstant v.2 * ∫ y, ‖k y‖*Real.exp (((v.1:ℝ)+1)*|y|) := by
  apply (norm_convolution_le v k hk _).trans
  rw [← integral_const_mul]
  apply integral_mono (integrable_growth_of_exp v hk hE) (hE.const_mul _)
  intro y
  apply (mul_le_mul_of_nonneg_left (growth_le_exp v y) (norm_nonneg _)).trans_eq; ring

end
end MasulloRH.SobolevStrip

end StandaloneSobolevStripMoments

section StandaloneStripFilter

open Set Filter
open scoped Topology ComplexConjugate
namespace MasulloRH.StripFilter
noncomputable section
abbrev Z := ZetaZerosInTraceStrip (1/2)
def centered (z : Z) : ℂ := z.val-1/2
def mult (z : Z) := analyticOrderNatAt riemannZeta z.val
end
end MasulloRH.StripFilter
end StandaloneStripFilter

section StandaloneStripLaplaceMoments

open MeasureTheory Filter Set
open scoped Topology
namespace MasulloRH.StripTrace
noncomputable section
open StripPhysical

private def cyclic_StripLaplaceMoments_kernelIntegrand (k : ℝ→ℂ) (j : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  k y*(y:ℂ)^j*Complex.exp (s*(y:ℂ))

private theorem cyclic_StripLaplaceMoments_kernel_meas {k : ℝ→ℂ} (hk : AEStronglyMeasurable k) (j : ℕ) (s : ℂ) :
    AEStronglyMeasurable (cyclic_StripLaplaceMoments_kernelIntegrand k j s) := by
  apply (hk.mul (show Continuous (fun y : ℝ => (y:ℂ)^j) by fun_prop).aestronglyMeasurable).mul
  exact (show Continuous (fun y : ℝ => Complex.exp (s*(y:ℂ))) by fun_prop).aestronglyMeasurable

theorem moment_hasDerivAt {a : ℝ} {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (a*|y|))) (j : ℕ) {s : ℂ} (hs : |s.re|<a) :
    HasDerivAt (fun t : ℂ => moment k t j) (moment k s (j+1)) s := by
  let c := (|s.re|+a)/2
  have hc : 0≤c := by dsimp [c]; linarith [abs_nonneg s.re]
  have hsc : |s.re|<c := by dsimp [c]; linarith
  have hca : c<a := by dsimp [c]; linarith
  let U := {t : ℂ | |t.re|<c}
  have hU : U∈𝓝 s := (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).mem_nhds hsc
  obtain ⟨C,hC,hbd⟩ := polynomial_exp_bound (show |c|<a by simpa [abs_of_nonneg hc] using hca) (j+1)
  have hb (y : ℝ) (t : ℂ) (ht : t∈U) :
      ‖cyclic_StripLaplaceMoments_kernelIntegrand k (j+1) t y‖ ≤ (‖k y‖*Real.exp (a*|y|)) * C := by
    have h1 : t.re*y ≤ c*|y| := (le_abs_self _).trans
      ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right (show |t.re|<c from ht).le (abs_nonneg _)))
    have h2 := hbd |y|
    rw [abs_abs] at h2
    dsimp only [cyclic_StripLaplaceMoments_kernelIntegrand]
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [mul_assoc]
    refine (mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1)
      (pow_nonneg (abs_nonneg _) _)).trans h2) (norm_nonneg _)).trans_eq ?_
    ring
  have hd (y : ℝ) (t : ℂ) : HasDerivAt (fun w : ℂ => cyclic_StripLaplaceMoments_kernelIntegrand k j w y)
      (cyclic_StripLaplaceMoments_kernelIntegrand k (j+1) t y) t := by
    have hh := (((hasDerivAt_id t).mul_const (y:ℂ)).cexp.const_mul (k y*(y:ℂ)^j))
    dsimp only [id_eq,one_mul] at hh
    unfold cyclic_StripLaplaceMoments_kernelIntegrand
    convert! hh using 1 <;> first | rfl | (rw [pow_succ]; ring) | ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=cyclic_StripLaplaceMoments_kernelIntegrand k j)
    (F':=cyclic_StripLaplaceMoments_kernelIntegrand k (j+1)) hU (.of_forall (cyclic_StripLaplaceMoments_kernel_meas hk j))
    (moment_integrable hk hW hs j) (cyclic_StripLaplaceMoments_kernel_meas hk _ _)
    (.of_forall hb) (hW.mul_const C) (.of_forall (fun y t _ => hd y t))).2

theorem lap_iteratedDeriv {a : ℝ} {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (a*|y|))) (j : ℕ) {s : ℂ} (hs : |s.re|<a) :
    iteratedDeriv j (lap k) s = moment k s j := by
  induction j generalizing s with
  | zero =>
    simp only [iteratedDeriv_zero,lap,moment,pow_zero,mul_one]
    apply integral_congr_ae; exact .of_forall (fun y => mul_comm _ _)
  | succ j ih =>
    have hn : ∀ᶠ t : ℂ in 𝓝 s, |t.re|<a :=
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).mem_nhds hs
    have he : iteratedDeriv j (lap k) =ᶠ[𝓝 s] fun t => moment k t j := hn.mono (fun _ h => ih h)
    rw [iteratedDeriv_succ,he.deriv_eq,(moment_hasDerivAt hk hW j hs).deriv]

theorem logKernel_integrable (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) (a : ℝ) :
    Integrable (fun y : ℝ => ‖φ (Real.exp y)‖*Real.exp (a*|y|)) := by
  apply ((hφ.1.continuous.comp Real.continuous_exp).norm.mul
    (show Continuous (fun y : ℝ => Real.exp (a*|y|)) by fun_prop)).integrable_of_hasCompactSupport
  exact (log_compact φ hφ).norm.mul_right

theorem mellin_iterated_eq_moment (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) (j : ℕ) (s : ℂ) :
    iteratedDeriv j (mellin φ) s = moment (fun y => φ (Real.exp y)) s j := by
  rw [show mellin φ = lap (fun y => φ (Real.exp y)) from funext (mellin_eq_lap φ)]
  exact lap_iteratedDeriv (hφ.1.continuous.comp Real.continuous_exp).aestronglyMeasurable
    (logKernel_integrable φ hφ (|s.re|+1)) j (by linarith)

end
end MasulloRH.StripTrace

end StandaloneStripLaplaceMoments

section StandaloneStripKernelReduction

open MeasureTheory Set Filter
open scoped Topology
namespace MasulloRH.StripTrace
noncomputable section
open StripFilter StripPhysical

def HasSmallErrorKernels (φ : ℝ→ℂ) : Prop :=
  ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, ∀ F : Finset StripFilter.Z,
    (∀ z∈F, (5/2:ℝ)+2*n < |z.val.im|) →
    ∃ k : ℝ→ℂ, AEStronglyMeasurable k ∧
      Integrable (fun y => ‖k y‖*Real.exp ((3/2:ℝ)*|y|)) ∧
      (∫ y : ℝ, ‖k y‖*Real.exp ((3/2:ℝ)*|y|)) ≤ K/((n:ℝ)+1)^4 ∧
      ∀ z∈F, ∀ j < StripFilter.mult z,
        moment (fun y => φ (Real.exp y)) (centered z) j = moment k (centered z) j

end
end MasulloRH.StripTrace

end StandaloneStripKernelReduction

section StandaloneStripPublicOperator

open MeasureTheory Set Filter
open scoped Topology BigOperators InnerProductSpace
namespace MasulloRH.WeightedStripTrace
noncomputable section
open SobolevStrip (P H)
open StripJetDepth (Triangular)
open StripPhysical (moment)

def coeff {v : P} (k : ℝ→ℂ) (i : Index v) (j : Fin (i.2.val+1)) : ℂ :=
  (i.2.val.choose j.val:ℂ)*moment k (StripJetSpace.center i.1) (i.2.val-j.val)

theorem ambient_triangular (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*SobolevStrip.growth v y)) :
    Triangular (mode v) (SobolevStrip.convolution v k hk hW) (coeff k) := by
  intro i
  change _ = ∑ j : Fin (i.2.val+1), ((i.2.val.choose j.val:ℂ)*
    moment k (StripJetSpace.center i.1) (i.2.val-j.val)) • SobolevStrip.jet v (StripJetSpace.center i.1) j.val
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((i.2.val.choose j:ℂ)*moment k (StripJetSpace.center i.1)
    (i.2.val-j)) • SobolevStrip.jet v (StripJetSpace.center i.1) j)]
  exact SobolevStrip.convolution_jet v k hk hW (admissible i)

theorem preserves (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*SobolevStrip.growth v y)) :
    ∀ x∈Space v, SobolevStrip.convolution v k hk hW x∈Space v := by
  rw [space_eq]
  exact StripJetDepth.spanModel_invariant (ambient_triangular v k hk hW)

def op (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*SobolevStrip.growth v y)) : Space v →L[ℂ] Space v :=
  (SobolevStrip.convolution v k hk hW).restrict (preserves v k hk hW)

theorem op_triangular (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*SobolevStrip.growth v y)) :
    Triangular (u v) (op v k hk hW) (coeff k) :=
  StripJetDepth.inside_triangular _ (fun i => (u v i).prop) _ (ambient_triangular v k hk hW)

theorem op_bound (v : P) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*SobolevStrip.growth v y)) :
    ‖op v k hk hW‖ ≤ ∫y : ℝ, ‖k y‖*SobolevStrip.growth v y :=
  (StripJetDepth.restrict_norm_le _ _ _).trans (SobolevStrip.norm_convolution_le v k hk hW)

def testKernel (φ : ℝ→ℂ) (y : ℝ) : ℂ := φ (Real.exp y)

theorem test_meas (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    AEStronglyMeasurable (testKernel φ) := (hφ.1.continuous.comp Real.continuous_exp).aestronglyMeasurable

theorem test_int (v : P) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    Integrable (fun y : ℝ => ‖testKernel φ y‖*SobolevStrip.growth v y) :=
  SobolevStrip.integrable_growth_of_exp v (test_meas φ hφ) (StripTrace.logKernel_integrable φ hφ _)

def testOp (v : P) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) : Space v →L[ℂ] Space v :=
  op v (testKernel φ) (test_meas φ hφ) (test_int v φ hφ)

theorem test_physical (v : P) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    IsRationalStripJetConvolution (v.1:ℝ) (v.2:ℝ) φ (testOp v φ hφ) :=
  fun f g => SobolevStrip.convolution_pairing v (testKernel φ) (test_meas φ hφ) (test_int v φ hφ) f.val g

theorem test_unique (v : P) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ)
    (T : Space v →L[ℂ] Space v) (hT : IsRationalStripJetConvolution v.1 v.2 φ T) :
    T=testOp v φ hφ := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  apply ext_inner_left ℂ
  exact fun g => (hT x g).trans (test_physical v φ hφ x g).symm

theorem diagonal (v : P) (φ : ℝ→ℂ) (i : Index v) :
    coeff (testKernel φ) i (Fin.last i.2.val)=mellin φ (StripJetSpace.center i.1) := by
  rw [StripTrace.mellin_eq_lap]
  simp only [coeff,Fin.val_last,Nat.choose_self,Nat.cast_one,Nat.sub_self,moment,pow_zero,mul_one,one_mul,
    StripTrace.lap,testKernel]
  exact integral_congr_ae (.of_forall (fun y => mul_comm _ _))

end
end MasulloRH.WeightedStripTrace

end StandaloneStripPublicOperator

section StandaloneStripNuclear

open MasulloGRH Set Filter
open scoped Topology BigOperators
namespace MasulloRH.StripTrace
noncomputable section

private def cyclic_StripNuclear_increment {X : Type*} [Sub X] (a : ℕ → X) : ℕ → X
  | 0 => a 0
  | n+1 => a (n+1)-a n

private theorem cyclic_StripNuclear_sum_increments {X : Type*} [AddCommGroup X] (a : ℕ → X) (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), cyclic_StripNuclear_increment a j = a n := by
  induction n with
  | zero => simp [cyclic_StripNuclear_increment]
  | succ n ih => rw [Finset.sum_range_succ,ih,cyclic_StripNuclear_increment]; abel

private theorem cyclic_StripNuclear_trace_sub_shared {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) [FiniteDimensional ℂ W] (A B : H →L[ℂ] H)
    (hA : ∀ x,A x∈W) (hB : ∀ x,B x∈W) :
    operatorTrace (A-B) = operatorTrace A-operatorTrace B := by
  let b := Module.finBasis ℂ W
  have hAB : ∀ x,(A-B) x∈W := fun x => W.sub_mem (hA x) (hB x)
  rw [trace_on_finite_span W b (A-B) hAB,trace_on_finite_span W b A hA,trace_on_finite_span W b B hB,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact map_sub (b.coord i) (⟨_,hA (b i)⟩:W) (⟨_,hB (b i)⟩:W)

private theorem cyclic_StripNuclear_pow_summable (p : ℕ) (hp : 1<p) : Summable (fun n : ℕ => 1/((n:ℝ)+1)^p) := by
  simpa only [Nat.cast_add,Nat.cast_one] using
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr hp)

/-- Uniform operator approximation faster than the polynomial rank growth yields a nuclear
operator and convergence of the actual Hilbert traces of its finite-rank approximants. -/
theorem nuclear_trace_of_approximants {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (X : ℕ → H →L[ℂ] H) (W : ℕ → Submodule ℂ H) [∀ n, FiniteDimensional ℂ (W n)]
    (hnest : Monotone W) (hX : ∀ n u, X n u ∈ W n)
    {D K : ℝ} (hD : 0≤D) (hK : 0≤K)
    (hdim : ∀ n : ℕ, (Module.finrank ℂ (W n):ℝ) ≤ D*((n:ℝ)+1)^2)
    (herr : ∀ n : ℕ, ‖X n-T‖ ≤ K/((n:ℝ)+1)^4) :
    IsNuclearOperator T ∧ Tendsto (fun n => operatorTrace (X n)) atTop (𝓝 (operatorTrace T)) := by
  let A := cyclic_StripNuclear_increment X
  have hrange (n : ℕ) (u : H) : A n u∈W n := by
    cases n with
    | zero => exact hX 0 u
    | succ n => exact (W (n+1)).sub_mem (hX _ u) (hnest (Nat.le_succ n) (hX n u))
  have hinc (n : ℕ) : ‖A (n+1)‖ ≤ 2*K/((n:ℝ)+1)^4 := by
    have hd : ((n:ℝ)+1)^4 ≤ (((n+1:ℕ):ℝ)+1)^4 := by gcongr <;> norm_num
    calc
      ‖A (n+1)‖ = ‖(X (n+1)-T)-(X n-T)‖ := by dsimp [A,cyclic_StripNuclear_increment]; congr 1; abel
      _ ≤ _ := (norm_sub_le ..).trans (add_le_add (herr _) (herr _))
      _ ≤ _ := by rw [mul_div_assoc,two_mul]; exact add_le_add (div_le_div_of_nonneg_left hK (by positivity) hd) le_rfl
  have hcost : Summable (fun n => (Module.finrank ℂ (W n):ℝ)*‖A n‖) := by
    apply (summable_nat_add_iff 1).mp
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ ((cyclic_StripNuclear_pow_summable 2 (by omega)).mul_left (8*D*K))
    intro n
    have hp : (((n+1:ℕ):ℝ)+1)^2 ≤ 4*((n:ℝ)+1)^2 := by
      push_cast
      nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
    have hp' := (hdim (n+1)).trans (mul_le_mul_of_nonneg_left hp hD)
    have h := mul_le_mul hp' (hinc n) (norm_nonneg _) (by positivity)
    exact h.trans_eq (by field_simp; ring)
  have hnorm : Summable (fun n => ‖A n‖) := by
    apply (summable_nat_add_iff 1).mp
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by simpa [div_eq_mul_inv] using hinc n)
      ((cyclic_StripNuclear_pow_summable 4 (by omega)).mul_left (2*K))
  have ht : Tendsto X atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) herr ?_
    have hs := ((cyclic_StripNuclear_pow_summable 4 (by omega)).mul_left K).tendsto_atTop_zero
    simpa [div_eq_mul_inv] using hs
  have hs (u : H) : HasSum (fun n => A n u) (T u) := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm
      (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => (A n).le_opNorm u) (hnorm.mul_right ‖u‖))).mpr
    apply (tendsto_add_atTop_iff_nat 1).mp
    have he : Continuous (fun F : H →L[ℂ] H => F u) := (ContinuousLinearMap.apply ℂ H u).continuous
    apply (he.continuousAt.tendsto.comp ht).congr
    intro n
    exact (show (∑ j ∈ Finset.range (n+1), A j u) = X n u by
      rw [← ContinuousLinearMap.sum_apply,show ∑ j ∈ Finset.range (n+1), A j = X n from cyclic_StripNuclear_sum_increments X n]).symm
  obtain ⟨hn,hh⟩ := nuclear_of_summable_rank_mul_opNorm A W hrange hcost T hs
  refine ⟨hn,?_⟩
  have hTrace (n : ℕ) : operatorTrace (A n) = cyclic_StripNuclear_increment (fun j => operatorTrace (X j)) n := by
    cases n with
    | zero => rfl
    | succ n => exact cyclic_StripNuclear_trace_sub_shared (W (n+1)) _ _ (hX _) (fun u => hnest (Nat.le_succ n) (hX n u))
  have hsum := hh.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  apply hsum.congr
  intro n
  simpa only [Function.comp_apply,hTrace] using cyclic_StripNuclear_sum_increments (fun j => operatorTrace (X j)) n

end
end MasulloRH.StripTrace

end StandaloneStripNuclear

section StandaloneStripApproximation

open Set Filter
open scoped Topology BigOperators
namespace MasulloRH.StripTrace
noncomputable section

private theorem cyclic_StripApproximation_finite_jet_support {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (v : ι → H) {x : H} (hx : x ∈ Submodule.span ℂ (Set.range v)) :
    ∃ F : Finset ι, x ∈ Submodule.span ℂ (v '' (F : Set ι)) := by
  classical
  induction hx using Submodule.span_induction with
  | mem y h =>
    obtain ⟨i,rfl⟩ := h
    exact ⟨{i},Submodule.subset_span ⟨i,by simp,rfl⟩⟩
  | zero => exact ⟨∅,Submodule.zero_mem _⟩
  | add _ _ _ _ hu hw =>
    obtain ⟨F,hF⟩ := hu
    obtain ⟨G,hG⟩ := hw
    refine ⟨F∪G,Submodule.add_mem _ (Submodule.span_mono (Set.image_mono ?_) hF)
      (Submodule.span_mono (Set.image_mono ?_) hG)⟩
    · exact fun i hi => Finset.mem_union_left G hi
    · exact fun i hi => Finset.mem_union_right F hi
  | smul a y _ h =>
    obtain ⟨F,hF⟩ := h
    exact ⟨F,Submodule.smul_mem _ _ hF⟩

/-- The approximating filter may depend on the finite spectral support of the vector.
Only its norm bound must be independent of that support. -/
theorem projection_approx_of_local_filters {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (v : ι → H) (hd : Dense (Submodule.span ℂ (Set.range v) : Set H))
    (T : H →L[ℂ] H) (W : Submodule ℂ H) [FiniteDimensional ℂ W] {δ : ℝ} (hδ : 0≤δ)
    (h : ∀ F : Finset ι, ∃ E : H →L[ℂ] H, ‖E‖≤δ ∧ ∀ i∈F, (T-E) (v i)∈W) :
    ‖W.starProjection.comp T - T‖ ≤ δ := by
  let P := W.starProjection
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  let A := {x : H | ‖P (T x)-T x‖ ≤ δ*‖x‖}
  have hcl : IsClosed A :=
    isClosed_le ((P.continuous.comp T.continuous).sub T.continuous).norm (continuous_const.mul continuous_norm)
  intro x
  apply (show A=univ from Set.eq_univ_of_univ_subset (by
    rw [← hd.closure_eq]
    apply closure_minimal _ hcl
    intro a ha
    obtain ⟨F,hF⟩ := cyclic_StripApproximation_finite_jet_support v ha
    obtain ⟨E,hE,hEF⟩ := h F
    have hmap : Submodule.span ℂ (v '' (F:Set ι)) ≤ W.comap (T-E).toLinearMap :=
      Submodule.span_le.mpr (by rintro _ ⟨i,hi,rfl⟩; exact hEF i hi)
    let w : W := ⟨(T-E) a,hmap hF⟩
    change ‖P (T a)-T a‖ ≤ δ*‖a‖
    rw [norm_sub_rev,show P= W.starProjection from rfl,Submodule.starProjection_minimal]
    refine (ciInf_le (bddBelow_def.mpr ⟨0,by rintro _ ⟨b,rfl⟩; exact norm_nonneg _⟩) w).trans ?_
    change ‖T a-(T a-E a)‖ ≤ _
    rw [sub_sub_cancel]
    exact (E.le_opNorm a).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg _)))) ▸ Set.mem_univ x

end
end MasulloRH.StripTrace

end StandaloneStripApproximation

section StandaloneStripPublicApprox

open MeasureTheory Set Filter MasulloGRH
open scoped Topology BigOperators
namespace MasulloRH.WeightedStripTrace
noncomputable section
open SobolevStrip (P H)
open StripJetDepth (stage)

private theorem cyclic_StripPublicApprox_growth_le (v : P) (hv : (v.1:ℝ)≤1/2) (y : ℝ) :
    SobolevStrip.growth v y ≤ SobolevStrip.polyConstant v.2 * Real.exp ((3/2:ℝ)*|y|) := by
  have hc : 0≤SobolevStrip.polyConstant v.2 := by unfold SobolevStrip.polyConstant; positivity
  exact (SobolevStrip.growth_le_exp v y).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _))) hc)

theorem growth_bound (v : P) (hv : (v.1:ℝ)≤1/2) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hE : Integrable (fun y => ‖k y‖*Real.exp ((3/2:ℝ)*|y|))) :
    Integrable (fun y => ‖k y‖*SobolevStrip.growth v y) ∧
    (∫y : ℝ, ‖k y‖*SobolevStrip.growth v y) ≤ SobolevStrip.polyConstant v.2 *
      ∫ y : ℝ, ‖k y‖*Real.exp ((3/2:ℝ)*|y|) := by
  let C := SobolevStrip.polyConstant v.2
  have h (y : ℝ) : ‖k y‖*SobolevStrip.growth v y ≤ C*(‖k y‖*Real.exp ((3/2:ℝ)*|y|)) :=
    (mul_le_mul_of_nonneg_left (cyclic_StripPublicApprox_growth_le v hv y) (norm_nonneg _)).trans_eq (by ring)
  have hi : Integrable (fun y => ‖k y‖*SobolevStrip.growth v y) :=
    (hE.const_mul C).mono' (hk.norm.mul (SobolevStrip.continuous_growth v).aestronglyMeasurable)
      (.of_forall fun y => by rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (SobolevStrip.growth_pos _ _).le)]; exact h y)
  exact ⟨hi,(integral_mono hi (hE.const_mul C) h).trans_eq (integral_const_mul ..)⟩

theorem op_approx (v : P) (hv : (v.1:ℝ)≤1/2) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ)
    (hsmall : StripTrace.HasSmallErrorKernels φ) :
    ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, ‖StripJetDepth.projectConvolution (u v) (testOp v φ hφ) n - testOp v φ hφ‖ ≤
      K/((n:ℝ)+1)^4 := by
  classical
  obtain ⟨K,hK,h⟩ := hsmall
  let C := SobolevStrip.polyConstant v.2
  have hC : 0<C := by dsimp [C,SobolevStrip.polyConstant]; positivity
  refine ⟨C*K,mul_pos hC hK,fun n => ?_⟩
  letI := StripJetDepth.stage_finite (u v) n
  apply StripTrace.projection_approx_of_local_filters (u v) (u_dense v) _ (stage (u v) n) (by positivity)
  intro F
  let G : Finset Full := (F.filter (fun i => StripJetSpace.cutoff n < |i.1.val.im|)).image Sigma.fst
  have hg : ∀ z∈G, (5/2:ℝ)+2*n < |z.val.im| := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hi).2
  obtain ⟨k,hk,hE,hI,hM⟩ := h n G hg
  obtain ⟨hW,hB⟩ := growth_bound v hv k hk hE
  let E := op v k hk hW
  have hT := op_triangular v (testKernel φ) (test_meas φ hφ) (test_int v φ hφ)
  have hA := op_triangular v k hk hW
  refine ⟨E,(op_bound v k hk hW).trans (hB.trans ((mul_le_mul_of_nonneg_left hI hC.le).trans_eq (by ring))),?_⟩
  intro i hi
  by_cases hlo : |i.1.val.im|≤StripJetSpace.cutoff n
  · have hm := StripJetDepth.mem_stage_of_low (u v) n i hlo
    exact (stage (u v) n).sub_mem (StripJetDepth.stage_invariant hT n _ hm)
      (StripJetDepth.stage_invariant hA n _ hm)
  have hG : i.1∈G := Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,lt_of_not_ge hlo⟩,rfl⟩
  have he : testOp v φ hφ (u v i)=E (u v i) := by
    change op _ _ _ _ _ = op _ _ _ _ _
    rw [hT,hA]
    apply Finset.sum_congr rfl
    intro j _
    unfold coeff
    have hj : i.2.val-j.val < StripFilter.mult i.1 := (Nat.sub_le _ _).trans_lt (i.2.isLt.trans_le (degree_le v i.1))
    exact congrArg (fun c : ℂ => ((i.2.val.choose j.val:ℂ)*c) • u v (StripJetDepth.lower i j)) (hM _ hG _ hj)
  rw [ContinuousLinearMap.sub_apply,he,sub_self]
  exact Submodule.zero_mem _

end
end MasulloRH.WeightedStripTrace

end StandaloneStripPublicApprox

section StandaloneStripSmallErrorKernels

namespace MasulloRH.StripTrace

theorem hasSmallErrorKernels (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) : HasSmallErrorKernels φ :=
  MasulloRH.finite_high_zero_interpolating_mellin_kernels φ hφ

end MasulloRH.StripTrace

end StandaloneStripSmallErrorKernels

section StandaloneStripNuclearTail

open MasulloGRH Set Filter
open scoped Topology BigOperators
namespace MasulloRH.StripTrace
noncomputable section

private lemma cyclic_StripNuclearTail_dyadic_quotient (c N : ℝ) (j p : ℕ) :
    c/((2:ℝ)^j*N)^p = (c/N^p)*(1/(2:ℝ)^p)^j := by
  rw [mul_pow, div_pow,one_pow, ← pow_mul, ← pow_mul, Nat.mul_comm j p]
  ring

/-- Summing differences along the dyadic subsequence with starting index n bounds the
trace-norm remainder quadratically, even though the operator norm has a fourth-order bound. -/
theorem traceNorm_tail_of_approximants {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (X : ℕ → H →L[ℂ] H) (W : ℕ → Submodule ℂ H)
    [∀ n, FiniteDimensional ℂ (W n)] (hnest : Monotone W) (hX : ∀ n u, X n u ∈ W n)
    {D K : ℝ} (hD : 0≤D) (hK : 0≤K)
    (hdim : ∀ n : ℕ, (Module.finrank ℂ (W n):ℝ) ≤ D*((n:ℝ)+1)^2)
    (herr : ∀ n : ℕ, ‖X n-T‖ ≤ K/((n:ℝ)+1)^4) (n : ℕ) :
    traceNorm (T-X n) ≤ (32/3:ℝ)*D*K/((n:ℝ)+1)^2 := by
  let N : ℝ := (n:ℝ)+1
  let r (j : ℕ) := 2^j*(n+1)-1
  let t (j : ℕ) := (2:ℝ)^j*N
  have hN : 0<N := by dsimp [N]; positivity
  have ht (j) : 0<t j := by dsimp [t]; positivity
  have hr (j) : (r j:ℝ)+1=t j := by
    have h : r j+1=2^j*(n+1) := Nat.sub_add_cancel (by
      exact Nat.one_le_iff_ne_zero.mpr (by positivity))
    dsimp [t,N]
    exact_mod_cast h
  have hr₀ : r 0 = n := by simp [r]
  have ht_succ j : t (j+1)=2*t j := by dsimp [t]; rw [pow_succ]; ring
  have hrmono (j : ℕ) : r j ≤ r (j+1) := by
    have h : (r j:ℝ)+1 ≤ (r (j+1):ℝ)+1 := by rw [hr,hr,ht_succ]; linarith [ht j]
    exact_mod_cast (by linarith : (r j:ℝ)≤r (j+1))
  let A (j : ℕ) := X (r (j+1))-X (r j)
  let S (j : ℕ) := W (r (j+1))
  have hAS (j : ℕ) (u : H) : A j u∈S j := (S j).sub_mem (hX _ u) (hnest (hrmono j) (hX _ u))
  have hgeom (j : ℕ) : ‖X (r j)-T‖ ≤ (K/N^4)*(1/16:ℝ)^j := by
    have h := herr (r j)
    rw [hr] at h
    simpa only [t,cyclic_StripNuclearTail_dyadic_quotient,show (2:ℝ)^4=16 by norm_num] using h
  have hinc (j : ℕ) : ‖A j‖≤2*K/(t j)^4 := by
    have hh := herr (r (j+1))
    rw [hr,ht_succ] at hh
    have h := herr (r j)
    rw [hr] at h
    have hle : K/(2*t j)^4 ≤ K/(t j)^4 :=
      div_le_div_of_nonneg_left hK (by positivity [ht j]) (by gcongr; linarith [ht j])
    calc
      _ = ‖(X (r (j+1))-T)-(X (r j)-T)‖ := by dsimp [A]; congr 1; abel
      _ ≤ _ := (norm_sub_le ..).trans (add_le_add (hh.trans hle) h)
      _ = _ := by ring
  have hnorm : Summable (fun j => ‖A j‖) := by
    apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) _ ((summable_geometric_of_lt_one
      (by norm_num : (0:ℝ)≤1/16) (by norm_num)).mul_left (2*K/N^4))
    exact fun j => by simpa only [t,cyclic_StripNuclearTail_dyadic_quotient,show (2:ℝ)^4=16 by norm_num] using hinc j
  have hcost (j : ℕ) : (Module.finrank ℂ (S j):ℝ)*‖A j‖ ≤ (8*D*K/N^2)*(1/4:ℝ)^j := by
    have hd := hdim (r (j+1))
    rw [hr,ht_succ] at hd
    have hh := mul_le_mul hd (hinc j) (norm_nonneg _) (by positivity [ht j])
    apply hh.trans_eq
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,← cyclic_StripNuclearTail_dyadic_quotient (8*D*K) N j 2]
    change D*(2*t j)^2*(2*K/(t j)^4) = 8*D*K/(t j)^2
    field_simp [(ht j).ne']
    ring
  have hmajor := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4) (by norm_num)).mul_left (8*D*K/N^2)
  have hc := Summable.of_nonneg_of_le (fun j => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hcost hmajor.summable
  have hconv : Tendsto (fun j => X (r j)) atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) hgeom ?_
    exact ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/16) (by norm_num)).mul_left (K/N^4)).tendsto_atTop_zero
  have htel (j : ℕ) : ∑ i ∈ Finset.range j,A i = X (r j)-X n := by
    induction j with
    | zero => simp [hr₀]
    | succ j ih => rw [Finset.sum_range_succ,ih]; dsimp [A]; abel
  have hsum (u : H) : HasSum (fun j => A j u) ((T-X n) u) := by
    apply (hasSum_iff_tendsto_nat_of_summable_norm
      (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => (A j).le_opNorm u) (hnorm.mul_right ‖u‖))).mpr
    have hev : Continuous (fun L : H→L[ℂ] H => L u) := (ContinuousLinearMap.apply ℂ H u).continuous
    apply (hev.continuousAt.tendsto.comp (hconv.sub_const (X n))).congr
    intro j
    rw [← sum_apply,htel]
    rfl
  have htrace := (traceNorm_tail_of_summable_rank_mul_opNorm A S hAS hc (T-X n) hsum).1 ∅
  simp only [Finset.sum_empty,sub_zero] at htrace
  apply htrace.trans ((hc.tsum_le_tsum hcost hmajor.summable).trans_eq ?_)
  rw [hmajor.tsum_eq]
  dsimp [N]
  ring

end
end MasulloRH.StripTrace

end StandaloneStripNuclearTail

section StandaloneStripOperatorTheorem

open MeasureTheory Set Filter MasulloGRH
open scoped Topology BigOperators
namespace MasulloRH.WeightedStripTrace
noncomputable section
open SobolevStrip (P)
open StripJetDepth (stage projectConvolution)
open StripJetSpace (Z Low cutoff)

theorem finite_trace (v : P) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) (n : ℕ) :
    operatorTrace (projectConvolution (u v) (testOp v φ hφ) n) =
      ∑' z : Full, if |z.val.im| ≤ 5/2+2*(n:ℝ) then
        (degree v z:ℂ)*mellin φ (z.val-1/2) else 0 := by
  classical
  let f (z : Full) := (degree v z:ℂ)*mellin φ (z.val-1/2)
  have he := StripJetDepth.stage_trace_grouped (u_independent v)
    (op_triangular v (testKernel φ) (test_meas φ hφ) (test_int v φ hφ)) (fun z : Full => mellin φ (StripJetSpace.center z)) (diagonal v φ) n
  change operatorTrace (projectConvolution (u v) (testOp v φ hφ) n) = ∑ z : Low (1/2) n, f z.val at he
  rw [he,← (tsum_fintype (fun z : Low (1/2) n => f z.val) : (∑' z : Low (1/2) n, f z.val)=_),
    tsum_subtype (StripJetSpace.low (1/2) n) f]
  apply tsum_congr
  intro z
  by_cases h : z ∈ StripJetSpace.low (1/2) n
  · rw [Set.indicator_of_mem h,if_pos (show |z.val.im|≤5/2+2*(n:ℝ) from h)]
  · rw [Set.indicator_of_notMem h,if_neg (show ¬|z.val.im|≤5/2+2*(n:ℝ) from h)]

theorem result (v : P) (hv : (v.1:ℝ)≤1/2) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    ∃! T : Space v →L[ℂ] Space v,
      IsRationalStripJetConvolution v.1 v.2 φ T ∧ IsNuclearOperator T ∧
      HasSum (fun z : Full => (degree v z:ℂ)*mellin φ (z.val-1/2)) (operatorTrace T) ∧
      ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∃ W : Submodule ℂ (Space v), ∃ X : Space v →L[ℂ] Space v,
        FiniteDimensional ℂ W ∧ (Module.finrank ℂ W:ℝ) ≤ C*((n:ℝ)+1)^2 ∧
        (∀ f, X f∈W ∧ T f-X f∈Wᗮ) ∧ ‖X-T‖ ≤ C/((n:ℝ)+1)^4 ∧
        traceNorm (T-X) ≤ C/((n:ℝ)+1)^2 ∧
        operatorTrace X = ∑' z : Full, if |z.val.im|≤5/2+2*(n:ℝ) then
          (degree v z:ℂ)*mellin φ (z.val-1/2) else 0 := by
  classical
  let T := testOp v φ hφ
  let W := stage (u v)
  let X := projectConvolution (u v) T
  let D := 8*∑' z : Full,zeroDecayWeight (1/2) z
  have hD : 0≤D := mul_nonneg (by norm_num) (tsum_nonneg (fun z => by unfold zeroDecayWeight; positivity))
  have hw (n : ℕ) : (Module.finrank ℂ (W n):ℝ) ≤ D*((n:ℝ)+1)^2 :=
    StripJetDepth.stage_finrank_bound (by norm_num) (degree_le v) (u_independent v) n
  obtain ⟨K,hK,hN⟩ := op_approx v hv φ hφ (StripTrace.hasSmallErrorKernels φ hφ)
  let _ (n : ℕ) : FiniteDimensional ℂ (W n) := StripJetDepth.stage_finite (u v) n
  have hi := StripJetDepth.stage_mono (u v)
  have hX := StripJetDepth.projectConvolution_mem (u v) T
  obtain ⟨hn,ht⟩ := StripTrace.nuclear_trace_of_approximants T X W hi hX hD hK.le hw hN
  have hTr := StripTrace.traceNorm_tail_of_approximants T X W hi hX hD hK.le hw hN
  have hsum := StripJetDepth.test_summable (by norm_num : (0:ℝ)<1/2) (degree_le v) φ hφ
  have hs := StripJetDepth.test_trace_limit (u_independent v)
    (op_triangular v (testKernel φ) (test_meas φ hφ) (test_int v φ hφ))
    (by norm_num) (degree_le v) φ hφ (diagonal v φ)
  have hval : (∑' z : Full, (degree v z:ℂ)*mellin φ (z.val-1/2))=operatorTrace T :=
    tendsto_nhds_unique hs ht
  refine ⟨T,⟨test_physical v φ hφ,hn,hval ▸ hsum.hasSum,?_⟩,fun T' hT' => test_unique v φ hφ T' hT'.1⟩
  let C := max (max D K) ((32/3:ℝ)*D*K)
  have hKC : K≤C := (le_max_right D K).trans (le_max_left ..)
  refine ⟨C,hK.trans_le hKC,fun n => ⟨W n,X n,inferInstance,?_,?_,?_,?_,finite_trace v φ hφ n⟩⟩
  · exact (hw n).trans (mul_le_mul_of_nonneg_right ((le_max_left D K).trans (le_max_left ..)) (by positivity))
  · exact fun f => ⟨hX n f,Submodule.sub_starProjection_mem_orthogonal (K:=W n) (T f)⟩
  · exact (hN n).trans (div_le_div_of_nonneg_right hKC (by positivity))
  · exact (hTr n).trans (div_le_div_of_nonneg_right (le_max_right ..) (by positivity))

end
end MasulloRH.WeightedStripTrace

end StandaloneStripOperatorTheorem

section StandaloneStripThetaInclusion

open MeasureTheory Filter Set
open scoped InnerProductSpace Topology SchwartzMap
namespace MasulloRH.StripTheta
noncomputable section
open StripPhysical StripTrace

private theorem cyclic_StripThetaInclusion_mellin_log_int (f : ℝ → ℂ) (s : ℂ) (hf : MellinConvergent f s) :
    Integrable (fun x : ℝ => Complex.exp (s*x)*f (Real.exp x)) := by
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have him : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  rw [MellinConvergent,← him,integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hd Real.exp_injective.injOn,integrableOn_univ] at hf
  apply hf.congr
  apply ae_of_all
  intro x
  dsimp only
  rw [abs_of_pos (Real.exp_pos _),Complex.real_smul,smul_eq_mul,Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),← Complex.ofReal_log (Real.exp_nonneg _),
    Real.log_exp,Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2; ring

private theorem cyclic_StripThetaInclusion_centered_norm (f : ℝ→ℂ) (a x : ℝ) :
    ‖(Real.exp (x/2):ℂ)*f (Real.exp x)‖*Real.exp (a*x) =
      ‖Complex.exp (↑(1/2+a:ℝ)*(x:ℂ))*f (Real.exp x)‖ := by
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _),Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [mul_right_comm,←Real.exp_add]
  congr 2; ring

/-- The logarithmic Mellin pairing with every jet strictly below the zeta multiplicity vanishes. -/
theorem theta_jet_moment (g : 𝓢(ℝ,ℂ)) (hg : g 0=0) (hI : (∫ x : ℝ, g x)=0)
    (z : ℂ) (hz0 : 0<z.re) (hz1 : z.re<1) (r : ℕ) (hr : r<analyticOrderNatAt riemannZeta z) :
    ∫ x : ℝ, ((Real.exp (x/2):ℂ)*(∑' n : ℤ, g ((n:ℝ)*Real.exp x))) *
      (x:ℂ)^r * Complex.exp ((z-1/2)*x) = 0 := by
  let θ (t : ℝ) := ∑' n : ℤ, g ((n:ℝ)*t)
  let k (x : ℝ) := (Real.exp (x/2):ℂ)*θ (Real.exp x)
  have ht := rational_theta_test_factorization g hg hI
  obtain ⟨T,hT,-⟩ := ht.2
  have hk : Continuous k := by
    change Continuous (fun x : ℝ => (Real.exp (x/2):ℂ)*θ (Real.exp x))
    rw [show (fun x : ℝ => (Real.exp (x/2):ℂ)*θ (Real.exp x)) = (T:ℝ→ℂ) from (funext hT).symm]
    exact T.continuous
  let a : ℝ := (1/2+|z.re-1/2|)/2
  have hu : |z.re-1/2|<1/2 := abs_lt.mpr ⟨by linarith,by linarith⟩
  have hza : |z.re-1/2|<a := by dsimp [a]; linarith
  have ha : a<1/2 := by dsimp [a]; linarith
  have ha0 : 0≤a := (abs_nonneg _).trans hza.le
  have hi (u : ℝ) (h0 : 0<1/2+u) (h1 : 1/2+u<1) :
      Integrable (fun x : ℝ => ‖k x‖*Real.exp (u*x)) := by
    have hne : (↑(1/2+u:ℝ):ℂ) ≠ 1 := by exact_mod_cast h1.ne
    have h := (ht.1 (↑(1/2+u:ℝ)) h0 hne).1.1
    exact (cyclic_StripThetaInclusion_mellin_log_int θ _ h).norm.congr
      (.of_forall fun x => (cyclic_StripThetaInclusion_centered_norm θ u x).symm)
  have hi₁ := hi a (by linarith) (by linarith)
  have hi₂ := hi (-a) (by linarith) (by linarith)
  have hW : Integrable (fun x : ℝ => ‖k x‖*Real.exp (a*|x|)) := by
    apply (hi₁.add hi₂).mono' (hk.norm.mul (by fun_prop : Continuous (fun x : ℝ => Real.exp (a*|x|)))).aestronglyMeasurable
    apply ae_of_all
    intro x
    change ‖‖k x‖*Real.exp (a*|x|)‖ ≤ ‖k x‖*Real.exp (a*x) + ‖k x‖*Real.exp (-a*x)
    rw [Real.norm_of_nonneg (by positivity)]
    by_cases hx : 0≤x
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (by positivity)
    · rw [abs_of_neg (lt_of_not_ge hx),mul_neg,←neg_mul]
      exact le_add_of_nonneg_left (by positivity)
  have hshift : mellin θ = fun s : ℂ => lap k (s-1/2) := by
    funext s
    rw [mellin_eq_lap]
    unfold lap
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only [k]
    rw [Complex.ofReal_exp,←mul_assoc,←Complex.exp_add]
    congr 2; push_cast; ring
  have hne : z ≠ 1 := by intro h; rw [h] at hz1; exact (lt_irrefl _ hz1)
  have ho := (ht.1 z hz0 hne).2
  have hcast : (analyticOrderNatAt riemannZeta z : ℕ∞) ≤ analyticOrderAt (mellin θ) z :=
    (ENat.natCast_toNat_le_self _).trans ho
  have hA : AnalyticAt ℂ (mellin θ) z := by
    by_contra hn
    rw [analyticOrderAt_of_not_analyticAt hn] at hcast
    have hz : analyticOrderNatAt riemannZeta z = 0 := by exact_mod_cast le_antisymm hcast bot_le
    omega
  have hzero := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mp hcast r hr
  rw [hshift,iteratedDeriv_comp_sub_const] at hzero
  change iteratedDeriv r (lap k) (z-1/2) = 0 at hzero
  rw [lap_iteratedDeriv hk.aestronglyMeasurable hW r (by simpa using hza : |(z-1/2).re|<a)] at hzero
  exact hzero

theorem jetSpace_le_theta_orthogonal (b p : ℝ) :
    rationalStripJetSpace b p ≤ (Submodule.span ℂ {f : Lp ℂ 2 (volume : Measure ℝ) |
      ∃ g : 𝓢(ℝ,ℂ), g 0=0 ∧ (∫ x : ℝ, g x)=0 ∧ (f:ℝ→ℂ) =ᵐ[volume] fun x : ℝ =>
        (starRingEnd ℂ) (((1/rationalStripWeight b p x:ℝ):ℂ) *
          ((Real.exp (x/2):ℂ) * ∑' n : ℤ, g ((n:ℝ)*Real.exp x)))})ᗮ := by
  unfold rationalStripJetSpace
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
  apply Submodule.span_le.mpr
  rintro v ⟨z,_,h0,h1,r,hr,_,hv⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨g,hg,hI,hu⟩ := hu
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans (theta_jet_moment g hg hI z h0 h1 r hr)
    filter_upwards [hu,hv] with x hx hy
    rw [RCLike.inner_apply,hx,hy]
    simp only [starRingEnd_self_apply,Complex.ofReal_div,Complex.ofReal_one]
    have hw : (rationalStripWeight b p x:ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      unfold rationalStripWeight
      positivity
    field_simp
    simp only [mul_comm (Real.exp x)]
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left,hx,hy]
  | smul c x _ hx => simp [inner_smul_left,hx]

end
end MasulloRH.StripTheta

end StandaloneStripThetaInclusion

section StandaloneThetaGeneralBounds

open Set Filter MeasureTheory Asymptotics
open scoped Topology SchwartzMap FourierTransform
namespace MasulloRH
noncomputable section

private lemma cyclic_ThetaGeneralBounds_absInt_scale (f : ℝ → ℂ) (s : ℂ) (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1) • f (a*x)‖ =
      a^(-s.re) * ∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1) • f x‖ := by
  let F (u : ℝ) := ‖(u:ℂ)^(s-1) • f u‖
  have hpow : (a^(s.re-1))⁻¹ * a⁻¹ = a^(-s.re) := by
    rw [← Real.rpow_neg ha.le, ← Real.rpow_neg_one, ← Real.rpow_add ha]
    congr 1; ring
  calc
    _ = ∫ x : ℝ in Ioi 0, (a^(s.re-1))⁻¹ * F (a*x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 0 < x at hx
      simp only [F, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
        Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha hx), Complex.sub_re, Complex.one_re, Real.mul_rpow ha.le hx.le]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos ha (s.re-1))]
    _ = _ := by
      rw [integral_const_mul, integral_comp_mul_left_Ioi F 0 ha, mul_zero, smul_eq_mul, ← mul_assoc, hpow]

/-- The Mellin transform of the positive integral dilates of an arbitrary test function,
in the half-plane of absolute Dirichlet convergence. -/
lemma mellin_pos_dilates (f : ℝ → ℂ) (s : ℂ) (hs : 1 < s.re) (hf : MellinConvergent f s) :
    mellin (fun x : ℝ => ∑' n : ℕ, f (((n:ℝ)+1)*x)) s = riemannZeta s * mellin f s := by
  let F (n : ℕ) (x : ℝ) : ℂ := (x:ℂ)^(s-1) • f (((n:ℝ)+1)*x)
  have hInt (n : ℕ) : Integrable (F n) (volume.restrict (Ioi 0)) :=
    (MellinConvergent.comp_mul_left (f:=f) (s:=s) (a:=(n:ℝ)+1) (by positivity)).mpr hf
  have hSum : Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0, ‖F n x‖) := by
    have h₀ : Summable (fun n : ℕ => ((n:ℝ)+1)^(-s.re)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
    apply (h₀.mul_right (∫ x : ℝ in Ioi 0, ‖(x:ℂ)^(s-1) • f x‖)).congr
    intro n
    exact (cyclic_ThetaGeneralBounds_absInt_scale f s ((n:ℝ)+1) (by positivity)).symm
  have he := hasSum_integral_of_summable_integral_norm hInt hSum
  calc
    _ = ∫ x : ℝ in Ioi 0, ∑' n, F n x := by simp [mellin,F,tsum_mul_left,smul_eq_mul]
    _ = ∑' n, ∫ x : ℝ in Ioi 0, F n x := he.tsum_eq.symm
    _ = ∑' n : ℕ, (1/((n:ℂ)+1)^s)*mellin f s := by
      apply tsum_congr
      intro n
      change mellin (fun x => f (((n:ℝ)+1)*x)) s = _
      rw [mellin_comp_mul_left f s (by positivity : (0:ℝ)<n+1)]
      simp [Complex.cpow_neg,smul_eq_mul]
    _ = _ := by rw [tsum_mul_right, zeta_eq_tsum_one_div_nat_add_one_cpow hs]

private def cyclic_ThetaGeneralBounds_latticeWeight (k : ℕ) (n : ℕ) : ℝ := (((n:ℝ)+1)^k)⁻¹

private lemma cyclic_ThetaGeneralBounds_summable_latticeWeight (k : ℕ) (hk : 1 < k) : Summable (cyclic_ThetaGeneralBounds_latticeWeight k) := by
  have h : -((k:ℕ):ℝ) < -1 := by exact_mod_cast (show -((k:ℕ):ℤ) < -1 by omega)
  have hz := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr h)
  apply hz.congr
  intro n
  dsimp [cyclic_ThetaGeneralBounds_latticeWeight]
  rw [Nat.cast_add, Nat.cast_one, Real.rpow_neg (by positivity), Real.rpow_natCast]

def thetaNat (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℕ, f (((n:ℝ)+1)*x)

private lemma cyclic_ThetaGeneralBounds_thetaTerm_bound (f : 𝓢(ℝ,ℂ)) (k n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖f (((n:ℝ)+1)*x)‖ ≤ ((SchwartzMap.seminorm ℝ k 0) f) * (x^k)⁻¹ * cyclic_ThetaGeneralBounds_latticeWeight k n := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have h := SchwartzMap.norm_pow_mul_le_seminorm ℝ f k (((n:ℝ)+1)*x)
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hn hx), mul_pow] at h
  rw [cyclic_ThetaGeneralBounds_latticeWeight, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hn _), ← div_eq_mul_inv, le_div_iff₀ (pow_pos hx _)]
  nlinarith only [h]

private lemma cyclic_ThetaGeneralBounds_thetaNat_summable (f : 𝓢(ℝ,ℂ)) (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => f (((n:ℝ)+1)*x)) :=
  ((cyclic_ThetaGeneralBounds_summable_latticeWeight 2 (by norm_num)).mul_left _).of_norm_bounded (fun n => cyclic_ThetaGeneralBounds_thetaTerm_bound f 2 n hx)

private lemma cyclic_ThetaGeneralBounds_thetaNat_bound (f : 𝓢(ℝ,ℂ)) (k : ℕ) (hk : 1 < k) {x : ℝ} (hx : 0 < x) :
    ‖thetaNat f x‖ ≤ (((SchwartzMap.seminorm ℝ k 0) f) * ∑' n, cyclic_ThetaGeneralBounds_latticeWeight k n) * (x^k)⁻¹ := by
  apply (norm_tsum_le_tsum_norm ((cyclic_ThetaGeneralBounds_thetaNat_summable f x hx).norm)).trans
  apply (Summable.tsum_le_tsum (fun n => cyclic_ThetaGeneralBounds_thetaTerm_bound f k n hx) (cyclic_ThetaGeneralBounds_thetaNat_summable f x hx).norm
    ((cyclic_ThetaGeneralBounds_summable_latticeWeight k hk).mul_left _)).trans_eq
  rw [tsum_mul_left]; ring

lemma thetaNat_continuousOn (f : 𝓢(ℝ,ℂ)) : ContinuousOn (thetaNat f) (Ioi 0) := by
  intro x hx
  change 0 < x at hx
  have hu : Summable (fun n : ℕ => (SchwartzMap.seminorm ℝ 2 0 f) * ((x/2)^2)⁻¹ * cyclic_ThetaGeneralBounds_latticeWeight 2 n) :=
    (cyclic_ThetaGeneralBounds_summable_latticeWeight 2 (by norm_num)).mul_left _
  have hc : ContinuousOn (thetaNat f) (Ioi (x/2)) := by
    apply continuousOn_tsum (fun n => (f.continuous.comp (continuous_const.mul continuous_id)).continuousOn) hu
    intro n y hy
    have hx' : 0 < x/2 := by positivity
    have hy' : x/2 < y := hy
    apply (cyclic_ThetaGeneralBounds_thetaTerm_bound f 2 n (lt_trans hx' hy')).trans
    gcongr
    dsimp [cyclic_ThetaGeneralBounds_latticeWeight]; positivity
  exact ((hc.continuousAt (isOpen_Ioi.mem_nhds (show x/2 < x by linarith)))).continuousWithinAt

def reflectS (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := ℝ)) f

def theta (f : 𝓢(ℝ,ℂ)) (x : ℝ) := ∑' n : ℤ, f ((n:ℝ)*x)

lemma theta_split (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) {x : ℝ} (hx : 0 < x) :
    theta f x = thetaNat (f + reflectS f) x := by
  have h₁ := cyclic_ThetaGeneralBounds_thetaNat_summable f x hx
  have h₂ := cyclic_ThetaGeneralBounds_thetaNat_summable (reflectS f) x hx
  have hpos : Summable (fun n : ℕ => f ((((n:ℤ)+1 : ℤ) : ℝ)*x)) := by simpa using h₁
  have hneg : Summable (fun n : ℕ => f (((-((n:ℤ)+1) : ℤ) : ℝ)*x)) := by
    apply h₂.congr
    intro n
    change f (-(((n:ℝ)+1)*x)) = _
    push_cast; congr 1; ring
  have hsum := tsum_of_add_one_of_neg_add_one (f:=fun n : ℤ => f ((n:ℝ)*x)) hpos hneg
  change (∑' n : ℤ, f ((n:ℝ)*x)) = _
  rw [hsum]
  simp only [Int.cast_add, Int.cast_one, Int.cast_natCast, Int.cast_neg, Int.cast_zero, zero_mul, hf, add_zero]
  change _ = ∑' n : ℕ, (f (((n:ℝ)+1)*x) + f (-(((n:ℝ)+1)*x)))
  rw [h₁.tsum_add (g:=fun n : ℕ => f (-(((n:ℝ)+1)*x))) h₂]
  simp only [neg_mul]

/-- Uniform positive-scale decay of the Schwartz lattice sum in every integral order above one. -/
theorem thetaSchwartz_bound (f : 𝓢(ℝ,ℂ)) (hf : f 0 = 0) (k : ℕ) (hk : 1 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖∑' n : ℤ, f ((n:ℝ)*x)‖ ≤ C * (x^k)⁻¹ := by
  refine ⟨(SchwartzMap.seminorm ℝ k 0) (f+reflectS f) * ∑' n, cyclic_ThetaGeneralBounds_latticeWeight k n, ?_, ?_⟩
  · apply mul_nonneg (by positivity)
    apply tsum_nonneg
    intro n; dsimp [cyclic_ThetaGeneralBounds_latticeWeight]; positivity
  · intro x hx
    change ‖theta f x‖ ≤ _
    rw [theta_split f hf hx]
    exact cyclic_ThetaGeneralBounds_thetaNat_bound _ k hk hx

end
end MasulloRH

end StandaloneThetaGeneralBounds

section StandaloneThetaPoisson

open MeasureTheory Filter Set FourierTransform
open scoped SchwartzMap FourierTransform Topology
set_option autoImplicit false
namespace MasulloSynthesis
noncomputable section

theorem theta_poisson_scaled (f : 𝓢(ℝ,ℂ)) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, f ((n:ℝ)*a)) =
    (a⁻¹:ℝ) • ∑' n : ℤ, (𝓕 f) ((n:ℝ)*a⁻¹) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha.ne')
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg (x : ℝ) : g x = f (a*x) := rfl
  have hscale (ξ : ℝ) : (𝓕 g) ξ = (a⁻¹:ℝ) • (𝓕 f) (ξ*a⁻¹) := by
    change 𝓕 (⇑g) ξ = (a⁻¹:ℝ) • 𝓕 (⇑f) (ξ*a⁻¹)
    rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
    let F (x : ℝ) := Complex.exp (↑(-2*Real.pi*x*(ξ*a⁻¹)) * Complex.I) • f x
    calc
      _ = ∫ x : ℝ, F (a*x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          dsimp only [F]
          rw [hg]
          congr 3
          field_simp
      _ = _ := by
        have h := Measure.integral_comp_mul_left F a
        simpa only [abs_of_pos (inv_pos.mpr ha)] using h
  have h := g.tsum_eq_tsum_fourier 0
  simp only [zero_add, hg, hscale, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one] at h
  rw [← tsum_const_smul'']
  simpa [mul_comm a] using h
theorem theta_poisson_near_zero (f : 𝓢(ℝ,ℂ)) (hI : (∫ x : ℝ, f x) = 0) :
    (fun x : ℝ => ∑' n : ℤ, f ((n:ℝ)*x)) =O[𝓝[>] (0:ℝ)] (fun _ : ℝ => (1:ℝ)) := by
  have hF0 : (𝓕 f : 𝓢(ℝ,ℂ)) 0 = 0 := by
    change 𝓕 (⇑f) 0 = 0
    simpa [Real.fourier_real_eq_integral_exp_smul] using hI
  obtain ⟨C,hC,hbound⟩ := MasulloRH.thetaSchwartz_bound (𝓕 f) hF0 2 (by decide)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num))] with x hx hx1
  have hpos : 0 < x := hx
  have hxle : x ≤ 1 := le_of_lt hx1
  change ‖∑' n : ℤ, f ((n:ℝ)*x)‖ ≤ C * ‖(1:ℝ)‖
  rw [theta_poisson_scaled f hpos, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hpos).le]
  simp only [norm_one, mul_one]
  calc
    _ ≤ x⁻¹ * (C * ((x⁻¹)^2)⁻¹) := mul_le_mul_of_nonneg_left (hbound _ (inv_pos.mpr hpos)) (inv_pos.mpr hpos).le
    _ = C * x := by field_simp
    _ ≤ C := mul_le_of_le_one_right hC hxle
end
end MasulloSynthesis

end StandaloneThetaPoisson

section StandaloneStripThetaRows

open MeasureTheory Filter Set FourierTransform
open scoped Topology FourierTransform SchwartzMap
namespace MasulloRH.StripTheta
noncomputable section

def logTheta (g : 𝓢(ℝ,ℂ)) (x : ℝ) : ℂ :=
  (Real.exp (x/2):ℂ)* ∑' n : ℤ,g ((n:ℝ)*Real.exp x)

theorem logTheta_continuous (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) : Continuous (logTheta g) := by
  apply (show Continuous (fun x : ℝ => (Real.exp (x/2):ℂ)) by fun_prop).mul
  have he : (fun x : ℝ => ∑' n : ℤ,g ((n:ℝ)*Real.exp x)) = thetaNat (g+reflectS g) ∘ Real.exp :=
    funext (fun x => theta_split g h0 (Real.exp_pos x))
  rw [he]
  exact (thetaNat_continuousOn _).comp_continuous Real.continuous_exp Real.exp_pos

theorem logTheta_poisson (g : 𝓢(ℝ,ℂ)) (x : ℝ) : logTheta g x=logTheta (𝓕 g) (-x) := by
  simp only [logTheta,MasulloSynthesis.theta_poisson_scaled g (Real.exp_pos x),Real.exp_neg,
    Complex.real_smul,←mul_assoc,←Complex.ofReal_mul]
  congr 2
  rw [←Real.exp_neg,←Real.exp_add]
  congr 1
  ring

private theorem cyclic_StripThetaRows_logTheta_decay_right (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (k : ℕ) (hk : 1<k) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖logTheta g x‖≤C*Real.exp ((1/2-(k:ℝ))*x) := by
  obtain ⟨C,hC,h⟩ := thetaSchwartz_bound g h0 k hk
  refine ⟨C,hC,fun x => ?_⟩
  rw [logTheta,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_nonneg _)]
  apply (mul_le_mul_of_nonneg_left (h _ (Real.exp_pos x)) (Real.exp_nonneg _)).trans_eq
  rw [←Real.exp_nat_mul,←Real.exp_neg,mul_left_comm,←Real.exp_add]
  congr 2
  ring

/-- Theta rows of two-moment tests decay faster than any fixed exponential in both log tails. -/
theorem logTheta_exp_decay (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hI : (∫ t : ℝ,g t)=0) (a : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, ‖logTheta g x‖ ≤ C*Real.exp (-a*|x|) := by
  obtain ⟨j,hj⟩ := exists_nat_ge a
  let k := j+2
  have hk : 1<k := by dsimp [k]; omega
  have hka : 1/2-(k:ℝ) ≤ -a := by dsimp [k]; push_cast; linarith
  have hF : (𝓕 g : 𝓢(ℝ,ℂ)) 0=0 := by
    change 𝓕 (⇑g) 0=0; simpa [Real.fourier_real_eq_integral_exp_smul] using hI
  obtain ⟨A,hA,h₁⟩ := cyclic_StripThetaRows_logTheta_decay_right g h0 k hk
  obtain ⟨B,hB,h₂⟩ := cyclic_StripThetaRows_logTheta_decay_right (𝓕 g) hF k hk
  refine ⟨max A B,hA.trans (le_max_left _ _),fun x => ?_⟩
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    exact (h₁ x).trans (mul_le_mul (le_max_left _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hka hx)) (Real.exp_nonneg _) (hA.trans (le_max_left _ _)))
  · rw [abs_of_nonpos hx,logTheta_poisson g x]
    exact (h₂ (-x)).trans (mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hka (neg_nonneg.mpr hx))) (Real.exp_nonneg _)
      (hB.trans (le_max_right _ _)))

private theorem cyclic_StripThetaRows_weight_pos (b p x : ℝ) : 0<rationalStripWeight b p x := by unfold rationalStripWeight; positivity

private theorem cyclic_StripThetaRows_reciprocal_weight_bound (b p x : ℝ) :
    1/rationalStripWeight b p x ≤ Real.exp ((|p|+|b|)*|x|) := by
  have hpos : 0<1+x^2 := by positivity
  have hlog : Real.log (1+x^2) ≤ 2*|x| := by
    rw [←Real.log_exp (2*|x|)]
    apply Real.log_le_log hpos
    rw [two_mul,Real.exp_add]
    have h := Real.add_one_le_exp |x|
    have hp := mul_self_le_mul_self (by positivity : 0≤|x|+1) h
    nlinarith only [hp,sq_abs x,abs_nonneg x]
  have h0 : 0≤Real.log (1+x^2) := Real.log_nonneg (by linarith [sq_nonneg x])
  unfold rationalStripWeight
  rw [Real.rpow_def_of_pos hpos,←Real.exp_add,one_div,←Real.exp_neg,Real.exp_le_exp]
  have hpp := mul_le_mul (le_abs_self p) hlog h0 (abs_nonneg _)
  have hbb := mul_le_mul_of_nonneg_right (le_abs_self b) (abs_nonneg x)
  linarith

private theorem cyclic_StripThetaRows_integrable_double_exp : Integrable (fun x : ℝ => Real.exp (-2*|x|)) := by
  let f (x : ℝ) := Real.exp (-2*|x|)
  have hr : IntegrableOn f (Ioi 0) := (integrableOn_exp_mul_Ioi (by norm_num : (-2:ℝ)<0) 0).congr_fun
    (fun x hx => by simp only [f,abs_of_pos (show 0<x from hx)]) measurableSet_Ioi
  have hl : IntegrableOn f (Iic 0) := (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<2) 0).congr_fun
    (fun x hx => by simp only [f,abs_of_nonpos (show x≤0 from hx),neg_mul_neg]) measurableSet_Iic
  change Integrable f
  simpa using hl.union hr

theorem theta_row_memLp (b p : ℝ) (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hI : (∫t : ℝ,g t)=0) :
    MemLp (fun x : ℝ => ((1/rationalStripWeight b p x:ℝ):ℂ)*
      ((Real.exp (x/2):ℂ)*∑' n : ℤ,g ((n:ℝ)*Real.exp x))) 2 volume := by
  let f (x : ℝ) := ((1/rationalStripWeight b p x:ℝ):ℂ)*logTheta g x
  change MemLp f 2 volume
  have hw : Continuous (rationalStripWeight b p) := by
    unfold rationalStripWeight
    exact (Continuous.rpow_const (by fun_prop) (fun x => Or.inl (by positivity))).mul (by fun_prop)
  have hc : Continuous f := (Complex.continuous_ofReal.comp (continuous_const.div hw
    (fun x => (cyclic_StripThetaRows_weight_pos b p x).ne'))).mul (logTheta_continuous g h0)
  obtain ⟨C,hC,h⟩ := logTheta_exp_decay g h0 hI (|p|+|b|+1)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
  apply (cyclic_StripThetaRows_integrable_double_exp.const_mul (C^2)).mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards with x
  have hh : ‖f x‖ ≤ C*Real.exp (-|x|) := by
    dsimp only [f]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity [cyclic_StripThetaRows_weight_pos b p x])]
    apply (mul_le_mul (cyclic_StripThetaRows_reciprocal_weight_bound b p x) (h x) (norm_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [mul_left_comm,←Real.exp_add]
    congr 2
    ring
  change ‖‖f x‖^2‖≤C^2*Real.exp (-2*|x|)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq
  rw [mul_pow,←Real.exp_nat_mul]
  congr 2
  ring
end
end MasulloRH.StripTheta

end StandaloneStripThetaRows

section StandaloneStripThetaInclusionTests

open MeasureTheory Filter
open scoped InnerProductSpace SchwartzMap
namespace MasulloRH.StripTheta
noncomputable section

theorem physical_theta_annihilation (b p : ℝ) (u : rationalStripJetSpace b p)
    (g : 𝓢(ℝ,ℂ)) (h0 : g 0=0) (hI : (∫ t : ℝ, g t)=0) :
    Integrable (fun x : ℝ => (((1/rationalStripWeight b p x:ℝ):ℂ) *
      ((Real.exp (x/2):ℂ)*∑' n : ℤ, g ((n:ℝ)*Real.exp x))) * u.val x) ∧
    (∫ x : ℝ, (((1/rationalStripWeight b p x:ℝ):ℂ) *
      ((Real.exp (x/2):ℂ)*∑' n : ℤ, g ((n:ℝ)*Real.exp x))) * u.val x) = 0 := by
  let P (x : ℝ) := ((1/rationalStripWeight b p x:ℝ):ℂ) *
    ((Real.exp (x/2):ℂ)*∑' n : ℤ, g ((n:ℝ)*Real.exp x))
  have hp : MemLp P 2 volume := theta_row_memLp b p g h0 hI
  let v := hp.star.toLp (star P)
  have hv : (v : ℝ→ℂ) =ᵐ[volume] fun x => (starRingEnd ℂ) (P x) := hp.star.coeFn_toLp
  have he : (fun x : ℝ => ⟪v x,u.val x⟫_ℂ) =ᵐ[volume] fun x => P x*u.val x := by
    filter_upwards [hv] with x hx
    simp [RCLike.inner_apply,hx,mul_comm]
  have hi := (L2.integrable_inner (𝕜:=ℂ) v u.val).congr he
  have hz := (Submodule.mem_orthogonal _ _).mp (jetSpace_le_theta_orthogonal b p u.property)
    v (Submodule.subset_span ⟨g,h0,hI,hv⟩)
  exact ⟨hi,(integral_congr_ae he).symm.trans hz⟩

end
end MasulloRH.StripTheta

end StandaloneStripThetaInclusionTests

section StandaloneSobolevStripExterior

open MeasureTheory Filter Set
open scoped Topology
namespace MasulloRH.SobolevStrip
noncomputable section

private theorem cyclic_SobolevStripExterior_along_growing_side {v : P} {z : ℂ} (hz : (v.1:ℝ)< |z.re|) (r : ℕ) :
    ∀ᶠ x : ℝ in atTop, 1≤‖jetFunction v z r x‖+‖jetFunction v z r (-x)‖ := by
  have he := (tendsto_exp_mul_div_rpow_atTop (2*(v.2:ℝ)) _ (sub_pos.mpr hz)).eventually_ge_atTop 1
  filter_upwards [he,eventually_ge_atTop (2:ℝ)] with x hx hx₂
  have hx₀ : 0<x := by linarith
  have hx₁ : 1≤x := by linarith
  have hpol : (1+x^2)^((v.2:ℝ)/2) ≤ x^(2*(v.2:ℝ)) := by
    calc
      _ ≤ (x^4)^((v.2:ℝ)/2) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        have h2 : 4≤x^2 := by nlinarith [mul_nonneg (by linarith : 0≤x-2) (by linarith : 0≤x+2)]
        nlinarith [mul_nonneg (by linarith : 0≤x^2-4) (by positivity : 0≤x^2)]
      _ = _ := by
        rw [←Real.rpow_natCast x 4,←Real.rpow_mul hx₀.le]
        congr 1; push_cast; ring
  have hh : (1+x^2)^((v.2:ℝ)/2) ≤ Real.exp ((|z.re|-(v.1:ℝ))*x) := by
    apply hpol.trans
    exact (one_le_div₀ (Real.rpow_pos_of_pos hx₀ _)).mp hx
  let y := if 0≤z.re then x else -x
  have hy : |y|=x := by dsimp [y]; split <;> simp [abs_of_nonneg hx₀.le]
  have hs : y^2=x^2 := by dsimp [y]; split <;> ring
  have hzy : z.re*y=|z.re| *x := by
    dsimp [y]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have hnorm : ‖jetFunction v z r y‖=
      (1+x^2)^(-(v.2:ℝ)/2)*x^r*Real.exp ((|z.re|-(v.1:ℝ))*x) := by
    simp only [jetFunction,norm_mul,norm_pow,Complex.norm_of_nonneg (weight_pos v y).le,
      Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero]
    rw [weight,hs,hy,hzy]
    rw [sub_mul,show |z.re| *x-(v.1:ℝ)*x = -(v.1:ℝ)*x+|z.re| *x by ring,Real.exp_add]
    ring
  have hbig : 1≤‖jetFunction v z r y‖ := by
    rw [hnorm,show -(v.2:ℝ)/2= -((v.2:ℝ)/2) by ring,Real.rpow_neg (by positivity)]
    have ha : 0<(1+x^2)^((v.2:ℝ)/2) := by positivity
    have h' := (one_le_div₀ ha).mpr hh
    calc
      1 ≤ Real.exp ((|z.re|-(v.1:ℝ))*x) / (1+x^2)^((v.2:ℝ)/2) := h'
      _ ≤ (Real.exp ((|z.re|-(v.1:ℝ))*x) / (1+x^2)^((v.2:ℝ)/2)) * x^r :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ hx₁)
      _ = _ := by ring
  dsimp [y] at hbig
  split_ifs at hbig <;> linarith [norm_nonneg (jetFunction v z r x),norm_nonneg (jetFunction v z r (-x))]

theorem exterior_not_memLp {v : P} {z : ℂ} (hz : (v.1:ℝ)< |z.re|) (r : ℕ) :
    ¬MemLp (jetFunction v z r) 2 volume := by
  intro h
  let f := jetFunction v z r
  have hsum := h.norm.add (h.norm.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ)))
  have hmeas := hsum.meas_ge_lt_top (by norm_num) (by norm_num) (ε:=(1:NNReal)) one_ne_zero
  obtain ⟨R,hR⟩ := eventually_atTop.mp (cyclic_SobolevStripExterior_along_growing_side hz r)
  have hle : volume (Ioi R) < (⊤:ENNReal) := lt_of_le_of_lt (measure_mono (fun x hx => ?_)) hmeas
  · simp at hle
  · change (1:NNReal) ≤ ‖‖f x‖+‖f (-x)‖‖₊
    apply NNReal.coe_le_coe.mp
    change 1≤‖‖f x‖+‖f (-x)‖‖
    rw [Real.norm_of_nonneg (by positivity)]
    exact hR x hx.le

/-- Complete L² membership criterion, including the exterior of the closed strip. -/
theorem jet_memLp_iff (v : P) (z : ℂ) (r : ℕ) :
    MemLp (jetFunction v z r) 2 volume ↔ Admissible v z r := by
  refine ⟨fun h => ?_,jet_memLp⟩
  rcases le_or_gt |z.re| (v.1:ℝ) with hl|hg
  · exact (closed_strip_memLp_iff hl r).mp h
  · exact False.elim (exterior_not_memLp hg r h)

end
end MasulloRH.SobolevStrip

end StandaloneSobolevStripExterior

section StandaloneStripFinal

open MasulloRH MasulloGRH MeasureTheory Set Filter
open scoped Topology SchwartzMap BigOperators

theorem solution (b p : ℝ) (hb : 0≤b) (hB : b≤1/2) (hp : 0≤p) :
    (∀ (s : ℂ) (r : ℕ), MemLp (fun x : ℝ =>
      (rationalStripWeight b p x:ℂ)*(x:ℂ)^r*Complex.exp (s*x)) 2 volume ↔
        |s.re|<b ∨ (|s.re|=b ∧ (r:ℝ)+1/2<p)) ∧
    (∀ g : 𝓢(ℝ,ℂ), g 0=0 → (∫ t : ℝ,g t)=0 →
      let row := fun x : ℝ => ((1/rationalStripWeight b p x:ℝ):ℂ) *
        ((Real.exp (x/2):ℂ)*∑' n : ℤ,g ((n:ℝ)*Real.exp x))
      MemLp row 2 volume ∧ ∀ u : rationalStripJetSpace b p,
        Integrable (fun x : ℝ => row x*u.val x) ∧ (∫ x : ℝ, row x*u.val x)=0) ∧
    ∀ φ : ℝ→ℂ, IsRationalTraceTest φ →
      let d := fun z : ZetaZerosInTraceStrip (1/2) =>
        if |z.val.re-1/2|<b then analyticOrderNatAt riemannZeta z.val
        else if |z.val.re-1/2|=b then min (analyticOrderNatAt riemannZeta z.val) ⌈p-1/2⌉₊ else 0
      ∃! T : rationalStripJetSpace b p →L[ℂ] rationalStripJetSpace b p,
        IsRationalStripJetConvolution b p φ T ∧ IsNuclearOperator T ∧
        HasSum (fun z : ZetaZerosInTraceStrip (1/2) => (d z:ℂ)*mellin φ (z.val-1/2)) (operatorTrace T) ∧
        ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∃ W : Submodule ℂ (rationalStripJetSpace b p),
          ∃ X : rationalStripJetSpace b p →L[ℂ] rationalStripJetSpace b p,
            FiniteDimensional ℂ W ∧ (Module.finrank ℂ W:ℝ) ≤ C*((n:ℝ)+1)^2 ∧
            (∀ f, X f∈W ∧ T f-X f∈Wᗮ) ∧ ‖X-T‖ ≤ C/((n:ℝ)+1)^4 ∧
            traceNorm (T-X) ≤ C/((n:ℝ)+1)^2 ∧
            operatorTrace X = ∑' z : ZetaZerosInTraceStrip (1/2), if |z.val.im|≤5/2+2*(n:ℝ)
              then (d z:ℂ)*mellin φ (z.val-1/2) else 0 := by
  let v : SobolevStrip.P := (⟨b,hb⟩,⟨p,hp⟩)
  refine ⟨fun s r => (SobolevStrip.jet_memLp_iff v s r).trans (SobolevStrip.admissible_iff v s r),
    fun g h0 hI => ⟨StripTheta.theta_row_memLp b p g h0 hI,fun u => StripTheta.physical_theta_annihilation b p u g h0 hI⟩,?_⟩
  exact fun φ hφ => WeightedStripTrace.result v hB φ hφ

end StandaloneStripFinal
