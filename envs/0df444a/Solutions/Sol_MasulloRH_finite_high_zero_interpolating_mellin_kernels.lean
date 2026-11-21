-- Prove2me | solution 1 for MasulloRH.finite_high_zero_interpolating_mellin_kernels
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:36:12.897876+00:00
-- url     : https://prove2.me/submissions/0861d31d-a252-4de5-b30e-33361939c3be

import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic
import Mathlib
import Definitions.Def_MasulloRH_RationalTrace
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_zero_decay_tail_at_real_lattice
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Convolution

section StandaloneStripPhysicalTranslation

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal

namespace MasulloRH.StripPhysical
noncomputable section

abbrev H := Lp ℂ 2 (volume : Measure ℝ)

def weight (p x : ℝ) : ℝ := Real.exp (-p*|x|)

lemma weight_pos (p x : ℝ) : 0 < weight p x := Real.exp_pos _

lemma continuous_weight (p : ℝ) : Continuous (weight p) := by unfold weight; fun_prop

lemma weight_ratio_le {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    weight p x / weight p (x+y) ≤ Real.exp (p*|y|) := by
  rw [weight, weight, ← Real.exp_sub, Real.exp_le_exp]
  nlinarith [mul_le_mul_of_nonneg_left (abs_add_le x y) hp]

private def cyclic_StripPhysicalTranslation_ratio (p y x : ℝ) : ℂ := (weight p x / weight p (x+y) : ℝ)

private lemma cyclic_StripPhysicalTranslation_ratio_norm (p y x : ℝ) : ‖cyclic_StripPhysicalTranslation_ratio p y x‖ = weight p x / weight p (x+y) := by
  exact Complex.norm_of_nonneg (div_nonneg (weight_pos _ _).le (weight_pos _ _).le)

private lemma cyclic_StripPhysicalTranslation_ratio_mem (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : MemLp (cyclic_StripPhysicalTranslation_ratio p y) ⊤ volume := by
  apply memLp_top_of_bound _ (Real.exp (p*|y|)) (ae_of_all _ fun x => (cyclic_StripPhysicalTranslation_ratio_norm p y x).le.trans (weight_ratio_le hp x y))
  apply Continuous.aestronglyMeasurable
  exact Complex.continuous_ofReal.comp <| (continuous_weight p).div
    ((continuous_weight p).comp (continuous_id.add_const y)) (fun x => (weight_pos _ _).ne')

private def cyclic_StripPhysicalTranslation_shift (y : ℝ) : H →ₗᵢ[ℂ] H :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x+y) (measurePreserving_add_right volume y)

def translation (p : ℝ) (hp : 0 ≤ p) (y : ℝ) : H →L[ℂ] H :=
  (((ContinuousLinearMap.mul ℂ ℂ).holderL volume ⊤ 2 2) ((cyclic_StripPhysicalTranslation_ratio_mem p hp y).toLp (cyclic_StripPhysicalTranslation_ratio p y))).comp
    (cyclic_StripPhysicalTranslation_shift y).toContinuousLinearMap

lemma translation_apply_ae (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : H) :
    (translation p hp y f : ℝ → ℂ) =ᵐ[volume] fun x =>
      ((weight p x / weight p (x+y) : ℝ) : ℂ) * f (x+y) := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((cyclic_StripPhysicalTranslation_ratio_mem p hp y).toLp (cyclic_StripPhysicalTranslation_ratio p y)) (cyclic_StripPhysicalTranslation_shift y f)
  have hs := Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)
  refine h.trans ?_
  filter_upwards [(cyclic_StripPhysicalTranslation_ratio_mem p hp y).coeFn_toLp, hs] with x hx hsx
  change ((cyclic_StripPhysicalTranslation_ratio_mem p hp y).toLp (cyclic_StripPhysicalTranslation_ratio p y)) x * (cyclic_StripPhysicalTranslation_shift y f) x = _
  change (cyclic_StripPhysicalTranslation_shift y f) x = f (x+y) at hsx
  rw [hx, hsx]; rfl

lemma norm_translation_le (p : ℝ) (hp : 0 ≤ p) (y : ℝ) :
    ‖translation p hp y‖ ≤ Real.exp (p*|y|) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [← (cyclic_StripPhysicalTranslation_shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [translation_apply_ae p hp y f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hs
  change (cyclic_StripPhysicalTranslation_shift y f) x = f (x+y) at hs
  rw [hx, hs, norm_mul]
  exact mul_le_mul_of_nonneg_right ((cyclic_StripPhysicalTranslation_ratio_norm p y x).le.trans (weight_ratio_le hp x y)) (norm_nonneg _)

lemma translation_zero (p : ℝ) (hp : 0 ≤ p) : translation p hp 0 = .id ℂ H := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [translation_apply_ae p hp 0 f] with x h
  change (translation p hp 0 f) x = f x
  simpa only [add_zero, div_self (weight_pos p x).ne', Complex.ofReal_one, one_mul] using h

lemma translation_add (p : ℝ) (hp : 0 ≤ p) (y z : ℝ) :
    translation p hp (y+z) = (translation p hp y).comp (translation p hp z) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hz := (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp
    (translation_apply_ae p hp z f)
  filter_upwards [translation_apply_ae p hp (y+z) f,
    translation_apply_ae p hp y ((translation p hp z) f), hz] with x hall hy hz
  change (translation p hp z f) (x+y) = _ at hz
  change (translation p hp (y+z) f) x = (translation p hp y ((translation p hp z) f)) x
  rw [hall, hy, hz]
  simp only [Function.comp_apply, ← add_assoc, ← mul_assoc, ← Complex.ofReal_mul]
  field_simp [ne_of_gt (weight_pos p (x+y)), ne_of_gt (weight_pos p (x+y+z))]

private lemma cyclic_StripPhysicalTranslation_ratio_sub_one_bound {p : ℝ} (hp : 0 ≤ p) (x y : ℝ) :
    |weight p x / weight p (x+y) - 1| ≤ Real.exp (p*|y|) - 1 := by
  let a := weight p x / weight p (x+y)
  let D := Real.exp (p*|y|)
  have hD : 1 ≤ D := Real.one_le_exp_iff.mpr (mul_nonneg hp (abs_nonneg y))
  have ha : a ≤ D := weight_ratio_le hp x y
  have hinv := weight_ratio_le hp (x+y) (-y)
  simp only [add_neg_cancel_right, abs_neg] at hinv
  have hDa : 1 ≤ D*a := by
    change 1 ≤ D * (weight p x / weight p (x+y))
    rw [← mul_div_assoc, le_div_iff₀ (weight_pos p (x+y)), one_mul]
    exact (div_le_iff₀ (weight_pos p x)).mp hinv
  change |a-1| ≤ D-1
  apply abs_le.mpr
  refine ⟨?_, by linarith⟩
  by_cases h : a ≤ 1
  · have h' := mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hD)
    nlinarith
  · linarith

private lemma cyclic_StripPhysicalTranslation_shift_continuous (f : H) : Continuous (fun y : ℝ => cyclic_StripPhysicalTranslation_shift y f) := by
  let g : C(ℝ × ℝ, ℝ) := ⟨fun z => z.2 + z.1, continuous_snd.add continuous_fst⟩
  exact continuous_const.compMeasurePreservingLp (g := g.curry) g.curry.continuous
    (fun y => measurePreserving_add_right volume y) (by norm_num)

private lemma cyclic_StripPhysicalTranslation_diff_shift_bound (p : ℝ) (hp : 0 ≤ p) (y : ℝ) (f : H) :
    ‖translation p hp y f - cyclic_StripPhysicalTranslation_shift y f‖ ≤ (Real.exp (p*|y|)-1) * ‖f‖ := by
  rw [← (cyclic_StripPhysicalTranslation_shift y).norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [translation_apply_ae p hp y f,
    Lp.coeFn_sub (translation p hp y f) (cyclic_StripPhysicalTranslation_shift y f),
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume y)] with x hx hsub hs
  change (cyclic_StripPhysicalTranslation_shift y f) x = f (x+y) at hs
  rw [hsub, Pi.sub_apply, hx, hs, ← sub_one_mul, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact cyclic_StripPhysicalTranslation_ratio_sub_one_bound hp x y

lemma continuous_translation_orbit (p : ℝ) (hp : 0 ≤ p) (f : H) :
    Continuous (fun y : ℝ => translation p hp y f) := by
  have hlim : Tendsto (fun y : ℝ => translation p hp y f) (𝓝 0) (𝓝 f) := by
    have hg : Continuous (fun y : ℝ => (Real.exp (p*|y|)-1) * ‖f‖) := by
      fun_prop
    have hbound : Tendsto (fun y : ℝ => (Real.exp (p*|y|)-1) * ‖f‖) (𝓝 0) (𝓝 0) := by
      simpa using hg.tendsto 0
    have hdiff : Tendsto (fun y : ℝ => translation p hp y f - cyclic_StripPhysicalTranslation_shift y f) (𝓝 0) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr <| squeeze_zero (fun _ => norm_nonneg _) (fun y => cyclic_StripPhysicalTranslation_diff_shift_bound p hp y f) hbound
    have hs0 : cyclic_StripPhysicalTranslation_shift 0 f = f := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume (0:ℝ))] with x hx
      change (cyclic_StripPhysicalTranslation_shift 0 f) x = f (x+0) at hx
      simpa only [add_zero] using hx
    have hs := (cyclic_StripPhysicalTranslation_shift_continuous f).tendsto 0
    rw [hs0] at hs
    simpa only [sub_add_cancel, zero_add] using hdiff.add hs
  apply continuous_iff_continuousAt.mpr
  intro y
  have hd : Tendsto (fun z : ℝ => z-y) (𝓝 y) (𝓝 0) := by simpa using (show Continuous (fun z : ℝ => z-y) from continuous_id.sub continuous_const).tendsto y
  have h := (translation p hp y).continuous.continuousAt.tendsto.comp (hlim.comp hd)
  refine h.congr fun z => ?_
  change (translation p hp y) ((translation p hp (z-y)) f) = _
  rw [← ContinuousLinearMap.comp_apply, ← translation_add]
  simp

end
end MasulloRH.StripPhysical

end StandaloneStripPhysicalTranslation

section StandaloneStripPhysicalConvolution

open MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace MasulloRH.StripPhysical
noncomputable section

private lemma cyclic_StripPhysicalConvolution_orbit_bound {b : ℝ} (hb : 0≤b) (k : ℝ→ℂ) (f : H) (y : ℝ) :
    ‖k y • translation b hb y f‖ ≤ (‖k y‖*Real.exp (b*|y|))*‖f‖ := by
  rw [norm_smul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (((translation b hb y).le_opNorm f).trans
    (mul_le_mul_of_nonneg_right (norm_translation_le b hb y) (norm_nonneg _))) (norm_nonneg _)

theorem integrable_orbit {b : ℝ} (hb : 0≤b) {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) (f : H) :
    Integrable (fun y : ℝ => k y • translation b hb y f) :=
  (hW.mul_const ‖f‖).mono' (hk.smul (continuous_translation_orbit b hb f).aestronglyMeasurable)
    (Eventually.of_forall (cyclic_StripPhysicalConvolution_orbit_bound hb k f))

private def cyclic_StripPhysicalConvolution_convolutionLinear {b : ℝ} (hb : 0≤b) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) : H →ₗ[ℂ] H where
  toFun f := ∫ y : ℝ, k y • translation b hb y f
  map_add' f g := by simp only [map_add,smul_add,integral_add (integrable_orbit hb hk hW f) (integrable_orbit hb hk hW g)]
  map_smul' c f := by simp only [map_smul,RingHom.id_apply]; simp_rw [smul_comm (k _) c, integral_smul]

private theorem cyclic_StripPhysicalConvolution_convolution_bound {b : ℝ} (hb : 0≤b) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) (f : H) :
    ‖cyclic_StripPhysicalConvolution_convolutionLinear hb k hk hW f‖ ≤ (∫ y : ℝ, ‖k y‖*Real.exp (b*|y|))*‖f‖ := by
  exact (norm_integral_le_of_norm_le (hW.mul_const _) (Eventually.of_forall (cyclic_StripPhysicalConvolution_orbit_bound hb k f))).trans_eq
    (integral_mul_const ..)

def convolution {b : ℝ} (hb : 0≤b) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) : H →L[ℂ] H :=
  (cyclic_StripPhysicalConvolution_convolutionLinear hb k hk hW).mkContinuous _ (cyclic_StripPhysicalConvolution_convolution_bound hb k hk hW)

theorem convolution_apply {b : ℝ} (hb : 0≤b) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) (f : H) :
    convolution hb k hk hW f = ∫ y : ℝ, k y • translation b hb y f := rfl

theorem norm_convolution_le {b : ℝ} (hb : 0≤b) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) :
    ‖convolution hb k hk hW‖ ≤ ∫ y : ℝ, ‖k y‖*Real.exp (b*|y|) :=
  (cyclic_StripPhysicalConvolution_convolutionLinear hb k hk hW).mkContinuous_norm_le (integral_nonneg fun y => by positivity)
    (cyclic_StripPhysicalConvolution_convolution_bound hb k hk hW)

theorem convolution_pairing {b : ℝ} (hb : 0≤b) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) (f g : H) :
    ⟪g,convolution hb k hk hW f⟫_ℂ = ∫ y : ℝ, k y * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
        (((weight b x / weight b (x+y) : ℝ) : ℂ) * f (x+y)) := by
  rw [convolution_apply,← integral_inner (integrable_orbit hb hk hW f) g]
  apply integral_congr_ae (ae_of_all _ fun y => ?_)
  rw [inner_smul_right,MeasureTheory.L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [translation_apply_ae b hb y f] with x hx
  rw [RCLike.inner_apply',hx]

end
end MasulloRH.StripPhysical

end StandaloneStripPhysicalConvolution

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

def jet {b : ℝ} (z : ℂ) (hz : |z.re|<b) (r : ℕ) : H :=
  (jet_memLp hz r).toLp _

theorem jet_apply_ae {b : ℝ} (z : ℂ) (hz : |z.re|<b) (r : ℕ) :
    (jet z hz r : ℝ→ℂ) =ᵐ[volume] jetFunction b z r := (jet_memLp hz r).coeFn_toLp

theorem jet_ne_zero {b : ℝ} (z : ℂ) (hz : |z.re|<b) (r : ℕ) : jet z hz r ≠ 0 := by
  intro he
  have h := jet_apply_ae z hz r
  rw [he] at h
  have hz' : jetFunction b z r =ᵐ[volume] fun _ => 0 := h.symm.trans (Lp.coeFn_zero ℂ 2 volume)
  have hc : Continuous (jetFunction b z r) := by unfold jetFunction weight; fun_prop
  have hall := Measure.eq_of_ae_eq hz' hc continuous_const
  have hone := congrFun hall 1
  have hw : (weight b 1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (weight_pos _ _).ne'
  simp [jetFunction, hw,Complex.exp_ne_zero] at hone

private lemma cyclic_StripPhysicalJets_jet_expand {b : ℝ} (z : ℂ) (r : ℕ) (x y : ℝ) :
    ((weight b x / weight b (x+y) : ℝ):ℂ)*jetFunction b z r (x+y) =
      ∑ s ∈ Finset.range (r+1), ((r.choose s:ℂ)*(y:ℂ)^(r-s)*Complex.exp (z*y))*jetFunction b z s x := by
  simp only [jetFunction,Complex.ofReal_add,Complex.ofReal_div,mul_add,Complex.exp_add]
  have hw : (weight b (x+y):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (weight_pos _ _).ne'
  calc
    _ = ((weight b x:ℂ)*Complex.exp (z*x)*Complex.exp (z*y)) * ((x:ℂ)+(y:ℂ))^r := by field_simp
    _ = _ := by
      rw [add_pow,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)

theorem translation_jet {b : ℝ} (hb : 0≤b) (z : ℂ) (hz : |z.re|<b) (r : ℕ) (y : ℝ) :
    translation b hb y (jet z hz r) =
      ∑ s ∈ Finset.range (r+1), ((r.choose s:ℂ)*(y:ℂ)^(r-s)*Complex.exp (z*y)) • jet z hz s := by
  let a (s : ℕ) : ℂ := (r.choose s:ℂ)*(y:ℂ)^(r-s)*Complex.exp (z*y)
  have hs (s : ℕ) : (a s • jet z hz s : H) =ᵐ[volume] fun x => a s * jetFunction b z s x := by
    filter_upwards [Lp.coeFn_smul (a s) (jet z hz s),jet_apply_ae z hz s] with x hx hx'
    simp only [hx,Pi.smul_apply,smul_eq_mul,hx']
  apply Lp.ext
  filter_upwards [translation_apply_ae b hb y (jet z hz r),
    (measurePreserving_add_right volume y).quasiMeasurePreserving.ae_eq_comp (jet_apply_ae z hz r),
    Lp.coeFn_fun_finsetSum (Finset.range (r+1)) (fun s => a s • jet z hz s),ae_all_iff.mpr hs]
    with x hu hr hsum hall
  change (translation b hb y (jet z hz r)) x = (∑ s ∈ Finset.range (r+1), a s • jet z hz s : H) x
  rw [hu,hsum]
  change jet z hz r (x+y) = jetFunction b z r (x+y) at hr
  rw [hr,cyclic_StripPhysicalJets_jet_expand]
  exact Finset.sum_congr rfl fun s _ => (hall s).symm

end
end MasulloRH.StripPhysical

end StandaloneStripPhysicalJets

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

theorem convolution_jet {b : ℝ} (hb : 0≤b) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) (z : ℂ) (hz : |z.re|<b) (r : ℕ) :
    convolution hb k hk hW (jet z hz r) =
      ∑ s ∈ Finset.range (r+1), ((r.choose s:ℂ)*moment k z (r-s)) • jet z hz s := by
  let m (j : ℕ) (y : ℝ) := k y*(y:ℂ)^j*Complex.exp (z*(y:ℂ))
  have hfun (y : ℝ) : k y • translation b hb y (jet z hz r) =
      ∑ s ∈ Finset.range (r+1), ((r.choose s:ℂ)*m (r-s) y) • jet z hz s := by
    rw [translation_jet,Finset.smul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [smul_smul]; congr 1; dsimp [m]; ring
  rw [convolution_apply]
  simp_rw [hfun]
  rw [integral_finsetSum _ (fun s _ => ((moment_integrable hk hW hz (r-s)).const_mul (r.choose s:ℂ)).smul_const (jet z hz s))]
  exact Finset.sum_congr rfl fun s _ => by rw [integral_smul_const,integral_const_mul]; rfl

theorem jet_diagonal (k : ℝ→ℂ) (z : ℂ) (r : ℕ) :
    (r.choose r:ℂ)*moment k z (r-r) = ∫ y : ℝ, k y*Complex.exp (z*(y:ℂ)) := by
  simp [moment]

theorem convolution_eigenvector {b : ℝ} (hb : 0≤b) (k : ℝ→ℂ) (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (b*|y|))) (z : ℂ) (hz : |z.re|<b) :
    convolution hb k hk hW (jet z hz 0) =
      (∫ y : ℝ, k y*Complex.exp (z*(y:ℂ))) • jet z hz 0 := by
  simpa [moment] using convolution_jet hb k hk hW z hz 0

end
end MasulloRH.StripPhysical

end StandaloneStripPhysicalMoments

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

section StandaloneTraceRateMellin

open MeasureTheory Set Filter MasulloRH
open scoped Topology
namespace MasulloRH.TraceRate
noncomputable section

private def cyclic_TraceRateMellin_cut (N x : ℝ) := Real.smoothTransition (N*x-1) * (1-Real.smoothTransition (x/N-1))
private def cyclic_TraceRateMellin_kern (w : ℂ) (x : ℝ) :=
  Complex.exp ((w-5/2)*x) - Complex.exp ((w-2)*x)

private lemma cyclic_TraceRateMellin_cut_cont (N : ℝ) : Continuous (cyclic_TraceRateMellin_cut N) := by
  unfold cyclic_TraceRateMellin_cut; fun_prop (disch := first | exact Real.smoothTransition.continuous)
private lemma cyclic_TraceRateMellin_cut_bounds (N x : ℝ) : 0≤cyclic_TraceRateMellin_cut N x ∧ cyclic_TraceRateMellin_cut N x≤1 := by
  unfold cyclic_TraceRateMellin_cut
  have hA := Real.smoothTransition.nonneg (N*x-1)
  have hB := Real.smoothTransition.le_one (N*x-1)
  have hC := Real.smoothTransition.nonneg (x/N-1)
  have hD := Real.smoothTransition.le_one (x/N-1)
  exact ⟨mul_nonneg hA (sub_nonneg.mpr hD),(mul_le_of_le_one_right hA (by linarith)).trans hB⟩

private lemma cyclic_TraceRateMellin_cut_one {N x : ℝ} (hN : 0<N) (h : 2/N≤x) (h' : x≤N) : cyclic_TraceRateMellin_cut N x=1 := by
  have hx := (div_le_iff₀ hN).mp h
  have hd := (div_le_one hN).mpr h'
  simp [cyclic_TraceRateMellin_cut,Real.smoothTransition.one_of_one_le (by nlinarith : 1≤N*x-1),
    Real.smoothTransition.zero_of_nonpos (by linarith : x/N-1≤0)]

private lemma cyclic_TraceRateMellin_kern_int {w : ℂ} (hw : w.re ≤ 1/2) :
    IntegrableOn (cyclic_TraceRateMellin_kern w) (Ioi 0) := by
  have h1 : (w-5/2).re < 0 := by norm_num [Complex.sub_re] at *; linarith
  have h2 : (w-2).re < 0 := by norm_num [Complex.sub_re] at *; linarith
  exact (integrableOn_exp_mul_complex_Ioi h1 0).sub (integrableOn_exp_mul_complex_Ioi h2 0)

private lemma cyclic_TraceRateMellin_kern_integral {w : ℂ} (hw : w.re ≤ 1/2) :
    (∫ x in Ioi 0, cyclic_TraceRateMellin_kern w x) = 1/((3:ℂ)-1/2-w)-1/(2-w) := by
  have h1 : (w-5/2).re < 0 := by norm_num [Complex.sub_re] at *; linarith
  have h2 : (w-2).re < 0 := by norm_num [Complex.sub_re] at *; linarith
  unfold cyclic_TraceRateMellin_kern
  rw [integral_sub (integrableOn_exp_mul_complex_Ioi h1 0) (integrableOn_exp_mul_complex_Ioi h2 0),
    integral_exp_mul_complex_Ioi h1,integral_exp_mul_complex_Ioi h2]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  rw [show (3:ℂ)-1/2-w=-(w-5/2) by ring,show (2:ℂ)-w=-(w-2) by ring]
  simp only [div_neg,neg_div]

private lemma cyclic_TraceRateMellin_kern_norm {w : ℂ} (hw : w.re≤1/2) {x : ℝ} (hx : 0≤x) :
    ‖cyclic_TraceRateMellin_kern w x‖ ≤ x/2 ∧ ‖cyclic_TraceRateMellin_kern w x‖ ≤ Real.exp ((-3/2)*x) := by
  have he : cyclic_TraceRateMellin_kern w x = Complex.exp ((w-2)*x) * ((Real.exp (-x/2):ℝ)-1:ℂ) := by
    unfold cyclic_TraceRateMellin_kern
    rw [mul_sub, mul_one,Complex.ofReal_exp,← Complex.exp_add]
    congr 2; push_cast; ring
  have hh : (w-2).re*x ≤ (-3/2)*x := by norm_num [Complex.sub_re]; nlinarith [mul_nonneg (sub_nonneg.mpr hw) hx]
  have hr : ‖cyclic_TraceRateMellin_kern w x‖ = Real.exp ((w-2).re*x) * (1-Real.exp (-x/2)) := by
    rw [he,norm_mul,Complex.norm_exp]
    have hn : ((Real.exp (-x/2):ℝ):ℂ)-1 = ((Real.exp (-x/2)-1:ℝ):ℂ) := by push_cast; rfl
    rw [hn,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith [Real.exp_le_one_iff.mpr (show -x/2≤0 by linarith)] : Real.exp (-x/2)-1≤0)]
    simp [Complex.mul_re]
  rw [hr]
  have hA : 1-Real.exp (-x/2) ≤ x/2 := by linarith [Real.add_one_le_exp (-x/2)]
  have hB := Real.exp_le_one_iff.mpr (hh.trans (by nlinarith : (-3/2)*x≤0))
  have hC : 0≤1-Real.exp (-x/2) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  exact ⟨(mul_le_of_le_one_left hC hB).trans hA,
    (mul_le_of_le_one_right (Real.exp_nonneg _) (by linarith [Real.exp_pos (-x/2)])).trans (Real.exp_le_exp.mpr hh)⟩

private lemma cyclic_TraceRateMellin_mellin_log (f : ℝ → ℂ) (w : ℂ) :
    mellin f w = ∫ x : ℝ, Complex.exp (w*x)*f (Real.exp x) := by
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have him : Real.exp '' univ = Ioi 0 := by rw [image_univ,Real.range_exp]
  unfold mellin
  rw [← him,integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,setIntegral_univ]
  apply integral_congr_ae; filter_upwards with x
  rw [abs_of_pos (Real.exp_pos _),Complex.real_smul,smul_eq_mul,Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp,
    Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  congr 2; ring

private lemma cyclic_TraceRateMellin_reg_log (n : ℕ) (w : ℂ) :
    mellin (regularizedTraceTest n 3) w = ∫ x in Ioi 0, ((cyclic_TraceRateMellin_cut (n+1) x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x := by
  rw [cyclic_TraceRateMellin_mellin_log,← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae; filter_upwards with x
  by_cases hx : 0<x
  · rw [indicator_of_mem (show x ∈ Ioi 0 from hx)]
    have ht : 1<Real.exp x := Real.one_lt_exp_iff.mpr hx
    simp only [regularizedTraceTest,traceLogCutoff,if_pos ht,Real.log_exp]
    change Complex.exp (w*x)*((cyclic_TraceRateMellin_cut (n+1) x:ℂ)*(_-_))=_
    rw [show ∀ z : ℂ, ((Real.exp x:ℝ):ℂ)^z = Complex.exp (x*z) from fun z => by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp]]
    rw [show ((Real.exp x:ℝ):ℂ)^(-2:ℂ)=Complex.exp (x*(-2:ℂ)) by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp]]
    unfold cyclic_TraceRateMellin_kern; rw [mul_left_comm, mul_sub,← Complex.exp_add,← Complex.exp_add]
    congr 2 <;> congr 1 <;> ring
  · rw [indicator_of_notMem (show x ∉ Ioi 0 from hx)]
    simp [regularizedTraceTest,not_lt.mpr (Real.exp_le_one_iff.mpr (not_lt.mp hx))]

private lemma cyclic_TraceRateMellin_cut_int {w : ℂ} (hw : w.re≤1/2) (N : ℝ) :
    IntegrableOn (fun x => ((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x) (Ioi 0) := by
  apply (cyclic_TraceRateMellin_kern_int hw).norm.mono'
  · apply Continuous.aestronglyMeasurable
    have h : Continuous (cyclic_TraceRateMellin_kern w) := by unfold cyclic_TraceRateMellin_kern; fun_prop
    exact (Complex.continuous_ofReal.comp (cyclic_TraceRateMellin_cut_cont N)).mul h
  · filter_upwards with x
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (cyclic_TraceRateMellin_cut_bounds N x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (cyclic_TraceRateMellin_cut_bounds N x).2

private lemma cyclic_TraceRateMellin_error_dom {w : ℂ} (hw : w.re≤1/2) {N x : ℝ} (hN : 0<N) (hx : 0<x) :
    ‖((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x-cyclic_TraceRateMellin_kern w x‖ ≤
      (Ioc 0 (2/N)).indicator (fun y : ℝ => y/2) x + (Ioi N).indicator (fun y : ℝ => Real.exp ((-3/2)*y)) x := by
  have hc := cyclic_TraceRateMellin_cut_bounds N x
  have hh : ‖((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x-cyclic_TraceRateMellin_kern w x‖ ≤ ‖cyclic_TraceRateMellin_kern w x‖ := by
    rw [← sub_one_mul,show ((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)-1=((cyclic_TraceRateMellin_cut N x-1:ℝ):ℂ) by push_cast; rfl,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hc.2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have hd := cyclic_TraceRateMellin_kern_norm hw hx.le
  by_cases ha : x≤2/N
  · rw [indicator_of_mem (show x∈Ioc 0 (2/N) from ⟨hx,ha⟩)]
    exact (hh.trans hd.1).trans (le_add_of_nonneg_right <| indicator_nonneg (fun y _ => Real.exp_nonneg _) _)
  · rw [indicator_of_notMem (show x ∉ Ioc 0 (2/N) from fun z => ha z.2),zero_add]
    by_cases hb : N<x
    · rw [indicator_of_mem (show x ∈ Ioi N from hb)]; exact hh.trans hd.2
    · rw [indicator_of_notMem (show x ∉ Ioi N from hb),cyclic_TraceRateMellin_cut_one hN (not_le.mp ha).le (not_lt.mp hb)]; simp

private lemma cyclic_TraceRateMellin_err_integral {w : ℂ} (hw : w.re≤1/2) {N : ℝ} (hN : 0<N) :
    ‖(∫ x in Ioi 0, ((cyclic_TraceRateMellin_cut N x:ℝ):ℂ)*cyclic_TraceRateMellin_kern w x)-(∫ x in Ioi 0,cyclic_TraceRateMellin_kern w x)‖ ≤
      1/N^2+(2/3)*Real.exp ((-3/2)*N) := by
  let V (x : ℝ) := (Ioc 0 (2/N)).indicator (fun y : ℝ => y/2) x
  let T (x : ℝ) := (Ioi N).indicator (fun y : ℝ => Real.exp ((-3/2)*y)) x
  have hV : Integrable V := (integrable_indicator_iff measurableSet_Ioc).mpr
    ((continuous_id.div_const 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hT : Integrable T := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_exp_mul_Ioi (by norm_num : (-3/2:ℝ)<0) N)
  rw [← integral_sub (cyclic_TraceRateMellin_cut_int hw _) (cyclic_TraceRateMellin_kern_int hw)]
  have hbound := integral_mono_ae (((cyclic_TraceRateMellin_cut_int hw N).sub (cyclic_TraceRateMellin_kern_int hw)).norm)
    ((hV.add hT).integrableOn (s:=Ioi 0))
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ hx => cyclic_TraceRateMellin_error_dom hw hN hx)
  apply (norm_integral_le_integral_norm _).trans (hbound.trans ?_)
  have hp : 0≤2/N := by positivity
  have hIV : (∫ x in Ioi 0,V x) = 1/N^2 := by
    dsimp [V]; rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (fun x h => h.1), ← intervalIntegral.integral_of_le hp,intervalIntegral.integral_div,
      integral_id]; ring
  have hIT : (∫ x in Ioi 0,T x) = (2/3)*Real.exp ((-3/2)*N) := by
    dsimp [T]; rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi hN.le),integral_exp_mul_Ioi (by norm_num : (-3/2:ℝ)<0)]; ring
  change (∫ x in Ioi 0,V x+T x) ≤ _
  rw [integral_add hV.integrableOn hT.integrableOn,hIV,hIT]

theorem regularized_mellin_error (n : ℕ) (w : ℂ) (hw : w.re≤1/2) :
    ‖mellin (regularizedTraceTest n 3) w - (1/((3:ℂ)-1/2-w)-1/(2-w))‖ ≤
      1/((n:ℝ)+1)^2+(2/3)*Real.exp ((-3/2)*((n:ℝ)+1)) := by
  rw [cyclic_TraceRateMellin_reg_log, ← cyclic_TraceRateMellin_kern_integral hw]; exact cyclic_TraceRateMellin_err_integral hw (by positivity)

theorem regularized_mellin_error_sq (n : ℕ) (w : ℂ) (hw : w.re≤1/2) :
    ‖mellin (regularizedTraceTest n 3) w - (1/((3:ℂ)-1/2-w)-1/(2-w))‖ ≤ 2/((n:ℝ)+1)^2 := by
  apply (regularized_mellin_error n w hw).trans
  let N : ℝ := n+1
  have hN : 0<N := by dsimp [N]; positivity
  change 1/N^2+ (2/3)*Real.exp ((-3/2)*N) ≤ 2/N^2
  have h := Real.quadratic_le_exp_of_nonneg (by positivity : 0≤(3/2)*N)
  rw [show (-3/2)*N= -((3/2)*N) by ring,Real.exp_neg]
  field_simp [hN.ne',Real.exp_pos]
  rw [show N*3/2=(3/2)*N by ring]
  nlinarith only [h, hN.le, sq_nonneg N]

end
end MasulloRH.TraceRate

end StandaloneTraceRateMellin

section StandaloneTraceRateSpectral

open Set Filter MeasureTheory
open scoped Topology
namespace MasulloRH.TraceRate
noncomputable section

private abbrev cyclic_TraceRateSpectral_Z := ZetaZerosInTraceStrip (1/2)
private abbrev cyclic_TraceRateSpectral_m (z : cyclic_TraceRateSpectral_Z) := analyticOrderNatAt riemannZeta z.val
private abbrev cyclic_TraceRateSpectral_wt (z : cyclic_TraceRateSpectral_Z) := zeroDecayWeight (1/2) z
private abbrev cyclic_TraceRateSpectral_res (z : cyclic_TraceRateSpectral_Z) := zeroResolventTerm (1/2) 3 z
private abbrev cyclic_TraceRateSpectral_ml (n : ℕ) (z : cyclic_TraceRateSpectral_Z) := mellin (regularizedTraceTest n 3) (z.val-1/2)

private theorem cyclic_TraceRateSpectral_term_limit (z : cyclic_TraceRateSpectral_Z) :
    Tendsto (fun n : ℕ => (cyclic_TraceRateSpectral_m z : ℂ)*cyclic_TraceRateSpectral_ml n z) atTop (𝓝 (cyclic_TraceRateSpectral_res z)) := by
  have hr : (z.val-1/2).re=z.val.re-1/2 := by simp
  have hb := z.property.2.2.1
  have h := regularized_mellin_limit 3 (z.val-1/2) (by rw [hr]; norm_num; linarith)
    (by rw [hr]; linarith)
  rw [show (3:ℂ)-1/2-(z.val-1/2)=3-z.val by ring,show (2:ℂ)-(z.val-1/2)=5/2-z.val by ring] at h
  exact h.const_mul _

private theorem cyclic_TraceRateSpectral_pointwise_low (n : ℕ) (z : cyclic_TraceRateSpectral_Z) :
    ‖(cyclic_TraceRateSpectral_m z:ℂ)*cyclic_TraceRateSpectral_ml n z-cyclic_TraceRateSpectral_res z‖ ≤ 2/((n:ℝ)+1)^2 * (cyclic_TraceRateSpectral_m z:ℝ) := by
  have h := regularized_mellin_error_sq n (z.val-1/2) (by
    have h := z.prop.2.2.1; simp only [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]; linarith)
  rw [show (3:ℂ)-1/2-(z.val-1/2)=3-z.val by ring,show (2:ℂ)-(z.val-1/2)=5/2-z.val by ring] at h
  change ‖(cyclic_TraceRateSpectral_m z:ℂ)*cyclic_TraceRateSpectral_ml n z-(cyclic_TraceRateSpectral_m z:ℂ)*_‖≤_
  rw [← mul_sub,norm_mul,Complex.norm_natCast,mul_comm (2/_)]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

private theorem cyclic_TraceRateSpectral_pointwise_truncated {C : ℝ} (hc :
    ∀ n : ℕ, ∀ z : cyclic_TraceRateSpectral_Z, ‖(cyclic_TraceRateSpectral_m z:ℂ)*cyclic_TraceRateSpectral_ml n z‖≤ C*cyclic_TraceRateSpectral_wt z) (n : ℕ) (z : cyclic_TraceRateSpectral_Z) {d : ℕ} (hd : d≤cyclic_TraceRateSpectral_m z) :
    ‖(d:ℂ)*cyclic_TraceRateSpectral_ml n z‖≤C*cyclic_TraceRateSpectral_wt z := by
  refine le_trans ?_ (hc n z)
  simp only [norm_mul,Complex.norm_natCast]
  gcongr

/-- The same estimate applies to every injectively indexed family of zeros, with multiplicities
capped away from the low-height range. -/
theorem sum_error_by_low_high {J : Type*} (i : J → cyclic_TraceRateSpectral_Z) (hi : Function.Injective i)
    (C : ℝ) (hC : 0≤C) (hc : ∀ n : ℕ, ∀ z : cyclic_TraceRateSpectral_Z, ‖(cyclic_TraceRateSpectral_m z:ℂ)*cyclic_TraceRateSpectral_ml n z‖≤C*cyclic_TraceRateSpectral_wt z)
    (n : ℕ) (d : J → ℕ) (hd : ∀ j, d j≤cyclic_TraceRateSpectral_m (i j)) (S : Set cyclic_TraceRateSpectral_Z)
    (hfull : ∀ j, i j∈S → d j=cyclic_TraceRateSpectral_m (i j))
    (hL : Summable (S.indicator (fun z => (cyclic_TraceRateSpectral_m z:ℝ)))) :
    ‖(∑' j : J,(d j:ℂ)*cyclic_TraceRateSpectral_ml n (i j))-(∑' j : J,cyclic_TraceRateSpectral_res (i j))‖ ≤
      2/((n:ℝ)+1)^2*(∑' z : cyclic_TraceRateSpectral_Z,S.indicator (fun a => (cyclic_TraceRateSpectral_m a:ℝ)) z)+
        (2*C)*(∑' z : cyclic_TraceRateSpectral_Z,Sᶜ.indicator cyclic_TraceRateSpectral_wt z) := by
  classical
  have hw := weighted_zero_summability (1/2) (by norm_num)
  have hR (z : cyclic_TraceRateSpectral_Z) : ‖cyclic_TraceRateSpectral_res z‖≤C*cyclic_TraceRateSpectral_wt z := le_of_tendsto' (cyclic_TraceRateSpectral_term_limit z).norm (fun n => hc n z)
  have hiW : Summable (fun j => C*cyclic_TraceRateSpectral_wt (i j)) := (hw.comp_injective hi).mul_left C
  have ha := hiW.of_norm_bounded (fun j => cyclic_TraceRateSpectral_pointwise_truncated hc n (i j) (hd j))
  have hb := hiW.of_norm_bounded (fun j => hR (i j))
  let a := 2/((n:ℝ)+1)^2
  let B (z : cyclic_TraceRateSpectral_Z) := a*S.indicator (fun t => (cyclic_TraceRateSpectral_m t:ℝ)) z+(2*C)*Sᶜ.indicator cyclic_TraceRateSpectral_wt z
  have hnB (z : cyclic_TraceRateSpectral_Z) : 0≤B z := by
    dsimp [B]; apply add_nonneg
    · exact mul_nonneg (by dsimp [a]; positivity) (indicator_nonneg (fun _ _ => Nat.cast_nonneg _) _)
    · apply mul_nonneg (by positivity)
      exact indicator_nonneg (fun z _ => by dsimp [cyclic_TraceRateSpectral_wt,zeroDecayWeight]; positivity) _
  have hH : Summable (Sᶜ.indicator cyclic_TraceRateSpectral_wt) := hw.indicator _
  have hB : Summable B := (hL.mul_left a).add (hH.mul_left (2*C))
  have hpt (j : J) : ‖(d j:ℂ)*cyclic_TraceRateSpectral_ml n (i j)-cyclic_TraceRateSpectral_res (i j)‖ ≤ B (i j) := by
    by_cases h : i j∈S
    · simpa [B,a,h,hfull j h] using cyclic_TraceRateSpectral_pointwise_low n (i j)
    · simpa [B,h,two_mul,add_mul] using (norm_sub_le _ _).trans
        (add_le_add (cyclic_TraceRateSpectral_pointwise_truncated hc n (i j) (hd j)) (hR (i j)))
  rw [← ha.tsum_sub hb]
  apply (norm_tsum_le_tsum_norm (ha.sub hb).norm).trans
  apply ((ha.sub hb).norm.tsum_le_tsum hpt (hB.comp_injective hi)).trans
  apply (tsum_comp_le_tsum_of_inj hB hnB hi).trans_eq
  dsimp only [B]
  rw [(hL.mul_left a).tsum_add (hH.mul_left (2*C)),tsum_mul_left,tsum_mul_left]

private abbrev cyclic_TraceRateSpectral_ZC := {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}
private def cyclic_TraceRateSpectral_em (z : cyclic_TraceRateSpectral_ZC) : cyclic_TraceRateSpectral_Z :=
  ⟨z.val,z.property.1,by rw [z.property.2]; norm_num,by rw [z.property.2]; norm_num,
    by rw [z.property.2]; norm_num⟩
private theorem cyclic_TraceRateSpectral_em_inj : Function.Injective cyclic_TraceRateSpectral_em := fun _ _ hh =>
  Subtype.ext (congrArg (fun z : cyclic_TraceRateSpectral_Z => z.val) hh)

/-- Common full-strip and critical-line spectral error estimate in terms of the low-height count,
high-height weighted tail, and the cutoff for multiplicities. -/
theorem spectral_rates_of_height_estimates (S : ℕ → Set cyclic_TraceRateSpectral_Z)
    (L H : ℝ) (hL : 0≤L) (hH : 0≤H)
    (h : ∀ᶠ n : ℕ in atTop,
      Summable ((S n).indicator (fun z => (cyclic_TraceRateSpectral_m z:ℝ))) ∧
      (∑' z : cyclic_TraceRateSpectral_Z,(S n).indicator (fun a => (cyclic_TraceRateSpectral_m a:ℝ)) z)≤L*((n:ℝ)+1)*Real.log ((n:ℝ)+2) ∧
      (∑' z : cyclic_TraceRateSpectral_Z,(S n)ᶜ.indicator cyclic_TraceRateSpectral_wt z)≤H*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ∀ z∈S n, cyclic_TraceRateSpectral_m z≤n+1) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop,
      ‖cutoffSpectral (1/2) n 3-regularizedSpectral (1/2) 3‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖(∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        ((min (analyticOrderNatAt riemannZeta z.val) ⌈((n:ℝ)+1)-1/2⌉₊:ℕ):ℂ) *
          mellin (regularizedTraceTest n 3) (z.val-1/2))-
        (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}, (analyticOrderNatAt riemannZeta z.val:ℂ) *
          (1/((3:ℂ)-z.val)-1/(5/2-z.val)))‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
  obtain ⟨B,hB,hd⟩ := regularized_spectral_domination_any_window (1/2) 3 (by norm_num)
  refine ⟨2*L+2*B*H+1,by positivity,?_⟩
  filter_upwards [h] with n hn
  obtain ⟨hs,hl,hh,hm⟩ := hn
  have hp : 0<((n:ℝ)+1) := by positivity
  have hnlog : 0≤Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have each {J : Type} (i : J → cyclic_TraceRateSpectral_Z) (hi : Function.Injective i) (d : J → ℕ)
      (hle : ∀ j, d j≤cyclic_TraceRateSpectral_m (i j)) (he : ∀ j, i j∈S n → d j=cyclic_TraceRateSpectral_m (i j)) :
      ‖(∑' j : J,(d j:ℂ)*cyclic_TraceRateSpectral_ml n (i j))-(∑' j : J,cyclic_TraceRateSpectral_res (i j))‖ ≤
        (2*L+2*B*H+1)*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
    apply (sum_error_by_low_high i hi B hB.le hd n d hle (S n) he hs).trans
    apply (add_le_add (mul_le_mul_of_nonneg_left hl (by positivity)) (mul_le_mul_of_nonneg_left hh (by positivity))).trans
    have hr : 2/((n:ℝ)+1)^2*(L*((n:ℝ)+1)*Real.log ((n:ℝ)+2))+
        (2*B)*(H*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)))=
        (2*L+2*B*H)*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by field_simp [hp.ne']
    rw [hr]; exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hnlog hp.le)
  refine ⟨each id Function.injective_id cyclic_TraceRateSpectral_m (fun _ => le_rfl) (fun _ _ => rfl),?_⟩
  let d (j : cyclic_TraceRateSpectral_ZC) := min (cyclic_TraceRateSpectral_m (cyclic_TraceRateSpectral_em j)) ⌈((n:ℝ)+1)-1/2⌉₊
  apply each cyclic_TraceRateSpectral_em cyclic_TraceRateSpectral_em_inj d (fun _ => min_le_left _ _)
  intro j hj
  apply min_eq_left
  have hnceil : n+1 ≤ ⌈((n:ℝ)+1)-1/2⌉₊ := by
    apply Nat.add_one_le_iff.mpr
    exact (Nat.lt_ceil).mpr (by linarith)
  exact (hm (cyclic_TraceRateSpectral_em j) hj).trans hnceil

private lemma cyclic_TraceRateSpectral_finite_initial_uniform_bound (u v : ℕ → ℝ) (hu : ∀ n,0≤u n)
    (hv : ∀ n,0<v n) {C : ℝ} (hC : 0<C) (h : ∀ᶠ n in atTop,u n≤C*v n) :
    ∃ B : ℝ, 0<B ∧ ∀ n, u n≤B*v n := by
  obtain ⟨k,hk⟩ := eventually_atTop.mp h
  let D := ∑ j ∈ Finset.range k,u j/v j
  have hD : 0≤D := Finset.sum_nonneg (fun j _ => div_nonneg (hu j) (hv j).le)
  refine ⟨C+D,by positivity,fun n => ?_⟩
  by_cases hn : k≤n
  · exact (hk n hn).trans (mul_le_mul_of_nonneg_right (by linarith) (hv n).le)
  · have hl : u n/v n≤D := Finset.single_le_sum (f:=fun j => u j/v j)
       (fun j _ => div_nonneg (hu j) (hv j).le) (Finset.mem_range.mpr (lt_of_not_ge hn))
    exact (div_le_iff₀ (hv n)).mp (hl.trans (by linarith))

theorem spectral_rate_all_of_eventually (u v : ℕ → ℂ) {C : ℝ} (hC : 0<C)
    (h : ∀ᶠ n : ℕ in atTop, ‖u n‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖v n‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1))) :
    ∃ B : ℝ, 0<B ∧ ∀ n : ℕ, ‖u n‖≤B*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖v n‖≤B*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
  have hv (n : ℕ) : 0<Real.log ((n:ℝ)+2)/((n:ℝ)+1) :=
    div_pos (Real.log_pos (by linarith [Nat.cast_nonneg (α:=ℝ) n])) (by positivity)
  obtain ⟨B,hB,hb⟩ := cyclic_TraceRateSpectral_finite_initial_uniform_bound (fun n => max ‖u n‖ ‖v n‖) _
    (fun n => (norm_nonneg _).trans (le_max_left _ _)) hv hC (h.mono (fun n hn => max_le hn.1 hn.2))
  exact ⟨B,hB,fun n => ⟨(le_max_left _ _).trans (hb n),(le_max_right _ _).trans (hb n)⟩⟩

end
end MasulloRH.TraceRate

end StandaloneTraceRateSpectral

section StandaloneTraceRateLattice

open Set Filter
open scoped Topology
namespace MasulloRH.TraceRate
noncomputable section

def lowHeight (n : ℕ) : Set (ZetaZerosInTraceStrip (1/2)) := {z | |z.val.im|≤(5/2:ℝ)+2*n}

theorem lattice_tail_bound :
    ∃ H : ℝ, 0≤H ∧ ∀ n : ℕ,
      (∑' z : ZetaZerosInTraceStrip (1/2), (lowHeight n)ᶜ.indicator (zeroDecayWeight (1/2)) z)≤
        H*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
  let c : ℝ := 8*((zetaLogDeriv 3).re-(zetaLogDeriv (5/2)+regularizedArch 3-regularizedPolar 3).re)-(zetaLogDeriv (5/2)).re
  refine ⟨4*(|c|+1),by positivity,fun n => ?_⟩
  have h := zero_decay_tail_at_real_lattice n
  dsimp only at h
  have heq : (lowHeight n)ᶜ.indicator (zeroDecayWeight (1/2)) =
      fun z : ZetaZerosInTraceStrip (1/2) => if (5/2:ℝ)+2*n < |z.val.im| then zeroDecayWeight (1/2) z else 0 := by
    funext z; simp [indicator,lowHeight]
  rw [heq]; apply h.trans
  let L := Real.log ((n:ℝ)+2)
  have hn : 0≤(n:ℝ) := by positivity
  have hp : 0<(n:ℝ)+1 := by positivity
  have hD : 0<(5/2:ℝ)+2*n-1 := by linarith
  have hL : 1/2≤L := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ))
    have h3 := Real.log_le_log (by norm_num : 0<(2:ℝ)) (show 2≤(n:ℝ)+2 by linarith)
    dsimp [L]; norm_num at h2; linarith
  have hlog : Real.log (n:ℝ)≤L := by
    rcases eq_or_ne n 0 with rfl|hz
    · simpa [L] using (Real.log_nonneg (by norm_num : 1≤(2:ℝ)))
    · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz); linarith
  change 2/(5/2+2*(n:ℝ)-1)*(c+(1+Real.log n)/2) ≤ (4*(|c|+1))*(L/((n:ℝ)+1))
  have hk : c+(1+Real.log (n:ℝ))/2 ≤ 2*(|c|+1)*L := by
    nlinarith [le_abs_self c,mul_nonneg (abs_nonneg c) (sub_nonneg.mpr hL)]
  apply (mul_le_mul_of_nonneg_left hk (by positivity : 0≤2/(5/2+2*(n:ℝ)-1))).trans
  have hden : 2/(5/2+2*(n:ℝ)-1) ≤ 2/((n:ℝ)+1) :=
    div_le_div_of_nonneg_left (by norm_num) hp (by linarith)
  apply (mul_le_mul_of_nonneg_right hden (by positivity : 0≤2*(|c|+1)*L)).trans_eq
  ring

theorem spectral_rates_all_of_lattice_low
    (hlow : ∃ L : ℝ, 0≤L ∧ ∀ᶠ n : ℕ in atTop,
      Summable ((lowHeight n).indicator (fun z => (analyticOrderNatAt riemannZeta z.val:ℝ))) ∧
      ((∑' z, (lowHeight n).indicator (fun z => (analyticOrderNatAt riemannZeta z.val:ℝ)) z)≤
        L*((n:ℝ)+1)*Real.log ((n:ℝ)+2)) ∧
      ∀ z∈lowHeight n, analyticOrderNatAt riemannZeta z.val≤n+1) :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ,
      ‖cutoffSpectral (1/2) n 3-regularizedSpectral (1/2) 3‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) ∧
      ‖(∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2},
        ((min (analyticOrderNatAt riemannZeta z.val) ⌈((n:ℝ)+1)-1/2⌉₊:ℕ):ℂ) *
          mellin (regularizedTraceTest n 3) (z.val-1/2))-
        (∑' z : {z : ℂ // riemannZeta z=0 ∧ z.re=1/2}, (analyticOrderNatAt riemannZeta z.val:ℂ) *
          (1/((3:ℂ)-z.val)-1/(5/2-z.val)))‖≤C*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
  obtain ⟨H,hH,ht⟩ := lattice_tail_bound
  obtain ⟨L,hL,hl⟩ := hlow
  obtain ⟨C,hC,h⟩ := spectral_rates_of_height_estimates lowHeight L H hL hH
    (hl.mono (fun n hn => ⟨hn.1,hn.2.1,ht n,hn.2.2⟩))
  exact spectral_rate_all_of_eventually _ _ hC h

end
end MasulloRH.TraceRate

end StandaloneTraceRateLattice

section StandaloneStripFilter

open Set Filter
open scoped Topology ComplexConjugate
namespace MasulloRH.StripFilter
noncomputable section
abbrev Z := ZetaZerosInTraceStrip (1/2)
def centered (z : Z) : ℂ := z.val-1/2
def mult (z : Z) := analyticOrderNatAt riemannZeta z.val
def factor (z s : ℂ) := (s-z)/(s+6+conj z)
def pair (z s : ℂ) := factor z s * factor (conj z) s
def filterProd (F : Finset Z) (s : ℂ) := ∏ z ∈ F, pair (centered z) s ^ mult z
def selector (F : Finset Z) (s : ℂ) := 1-(1-filterProd F s)^8

theorem center_re (z : Z) : |(centered z).re|≤1/2 := by
  simp only [centered,Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]; exact z.prop.2.2.2.le

@[simp] theorem center_im (z : Z) : (centered z).im=z.val.im := by simp [centered]

private theorem cyclic_StripFilter_denominator {z s : ℂ} (hz : -3<z.re) (hs : -3<s.re) : s+6+conj z≠0 := by
  intro h; have h' := congrArg Complex.re h; norm_num at h'; linarith

theorem factor_contract {z s : ℂ} (hz : -3<z.re) (hs : -3<s.re) : ‖factor z s‖≤1 := by
  rw [factor,norm_div,div_le_one (norm_pos_iff.mpr (cyclic_StripFilter_denominator hz hs))]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [Complex.sq_norm,Complex.sq_norm,Complex.normSq_apply,Complex.normSq_apply]
  norm_num; nlinarith only [mul_nonneg (show 0 ≤ s.re+3 by linarith) (show 0≤z.re+3 by linarith)]

private theorem cyclic_StripFilter_pair_contract {z s : ℂ} (hz : -3<z.re) (hs : -3<s.re) : ‖pair z s‖≤1 := by
  rw [pair,norm_mul]; exact mul_le_one₀ (factor_contract hz hs) (norm_nonneg _) (factor_contract hz hs)

private theorem cyclic_StripFilter_centered_gt (z : Z) : -3<(centered z).re := by
  have hz := (abs_le.mp (center_re z)).1; linarith

theorem filter_contract (F : Finset Z) {s : ℂ} (hs : -3<s.re) : ‖filterProd F s‖≤1 := by
  rw [filterProd,norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun z _ => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (cyclic_StripFilter_pair_contract (cyclic_StripFilter_centered_gt z) hs))

theorem global_two (F : Finset Z) {s : ℂ} (hs : -3<s.re) : ‖1-filterProd F s‖≤2 := by
  exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [filter_contract F hs])

private theorem cyclic_StripFilter_pair_formula {z s : ℂ} (hz : -3<z.re) (hs : -3<s.re) :
    1-pair z s = (4*(3+(z.re:ℂ))*(s+3))/((s+6+conj z)*(s+6+z)) := by
  have hc : s+6+z ≠ 0 := by simpa using cyclic_StripFilter_denominator (z:=conj z) hz hs
  have hd := cyclic_StripFilter_denominator hz hs
  have hsum : z+conj z = (2:ℂ)*(z.re:ℂ) := by apply Complex.ext <;> simp <;> ring
  dsimp [pair,factor]; simp only [Complex.conj_conj]
  field_simp [hd,hc]
  linear_combination (2*s+6) * hsum

private theorem cyclic_StripFilter_pair_estimate {s z : ℂ} (hre : |s.re|≤2) (hz : |z.re|≤1/2)
    (hT : 1≤|z.im|) (ht : |s.im|≤|z.im|/2) :
    ‖1-pair z s‖ ≤ 560*(1+|s.im|)/(1+z.im^2) := by
  have hzr := abs_le.mp hz; have hsr := abs_le.mp hre
  have hn1 : |z.im|/2 ≤ ‖s+6+conj z‖ := by
    have h0 := abs_sub_abs_le_abs_sub z.im s.im
    have h := Complex.abs_im_le_norm (s+6+conj z)
    norm_num at h
    rw [abs_sub_comm] at h0
    convert (le_trans (by linarith : |z.im|/2≤|z.im|-|s.im|) (h0.trans ?_)) using 0
    convert h using 1; congr 1; ring
  have hn2 : |z.im|/2 ≤ ‖s+6+z‖ := by
    have h0 := abs_sub_abs_le_abs_sub z.im (-s.im)
    have h := Complex.abs_im_le_norm (s+6+z)
    norm_num at h; rw [abs_neg,sub_neg_eq_add,add_comm z.im] at h0
    exact (by linarith : |z.im|/2≤|z.im|-|s.im|).trans (h0.trans h)
  have hs' : -3<s.re := by linarith [hsr.1]
  have hz' : -3<z.re := by linarith [hzr.1]
  have hsn : ‖s+3‖ ≤ 5*(1+|s.im|) := by
    have hh := Complex.norm_le_abs_re_add_abs_im (s+3)
    norm_num at hh; rw [abs_of_nonneg (by linarith [hsr.1])] at hh
    linarith [abs_nonneg s.im,hsr.2]
  have hzn : ‖(3:ℂ)+(z.re:ℂ)‖≤7/2 := by
    rw [← Complex.ofReal_ofNat (n:=3),← Complex.ofReal_add, Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hzr.1])]; linarith [hzr.2]
  have hp : 0<‖s+6+conj z‖*‖s+6+z‖ := by
    apply mul_pos <;> linarith
  have hq : 0<1+z.im^2 := by positivity
  rw [cyclic_StripFilter_pair_formula hz' hs',norm_div,norm_mul,norm_mul,norm_mul,
    div_le_div_iff₀ hp hq]
  have hnum : ‖(4:ℂ)‖*‖3+(z.re:ℂ)‖*‖s+3‖ ≤ 70*(1+|s.im|) := by
    calc
      _ ≤ 4*(7/2)*(5*(1+|s.im|)) := by norm_num; gcongr; linarith
      _ = _ := by ring
  have hprod := mul_le_mul hn1 hn2 (by positivity) (norm_nonneg _)
  have hden : 1+z.im^2≤8*(‖s+6+conj z‖*‖s+6+z‖) := by
    nlinarith only [hprod,sq_abs z.im,mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hT]
  calc
    _ ≤ (70*(1+|s.im|))*(1+z.im^2) := mul_le_mul_of_nonneg_right hnum hq.le
    _ ≤ (70*(1+|s.im|))*(8*(‖s+6+conj z‖*‖s+6+z‖)) := by gcongr
    _ = _ := by ring

private theorem cyclic_StripFilter_one_sub_mul {a b : ℂ} (ha : ‖a‖≤1) :
    ‖1-a*b‖ ≤ ‖1-a‖+‖1-b‖ := by
  rw [show 1-a*b=(1-a)+a*(1-b) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul]; exact add_le_add_right (mul_le_of_le_one_left (norm_nonneg _) ha) _

private theorem cyclic_StripFilter_one_sub_pow {a : ℂ} (ha : ‖a‖≤1) (k : ℕ) : ‖1-a^k‖ ≤ (k:ℝ)*‖1-a‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_succ,add_mul,one_mul]
    exact (cyclic_StripFilter_one_sub_mul (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)).trans (add_le_add_left ih _)

private theorem cyclic_StripFilter_one_sub_finprod {ι : Type*} (f : ι→ℂ) (F : Finset ι) (hf : ∀z∈F,‖f z‖≤1) :
    ‖1-∏ z ∈ F,f z‖ ≤ ∑ z∈F,‖1-f z‖ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    exact (cyclic_StripFilter_one_sub_mul (hf _ (Finset.mem_insert_self _ _))).trans
      (add_le_add_right (ih (fun z hz => hf z (Finset.mem_insert_of_mem hz))) _)

theorem finite_filter_bound :
    ∃ C : ℝ, 0<C ∧ ∀ (n : ℕ) (F : Finset Z), (∀ z∈F, (5/2:ℝ)+2*n< |z.val.im|) →
      ∀ s : ℂ, |s.re|≤2 →
       ‖1-filterProd F s‖≤C*(1+|s.im|)*(Real.log ((n:ℝ)+2)/((n:ℝ)+1)) := by
  obtain ⟨K,hK,htail⟩ := MasulloRH.TraceRate.lattice_tail_bound
  refine ⟨560*K+4,by positivity,?_⟩
  intro n F hF s hrs
  have hsr : -3<s.re := by have := (abs_le.mp hrs).1; linarith
  let H : ℝ := 5/2+2*n
  let R := Real.log ((n:ℝ)+2)/((n:ℝ)+1)
  have hN : 0<((n:ℝ)+1) := by positivity
  have hL : 1/2≤Real.log ((n:ℝ)+2) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : 0<(2:ℝ)); norm_num at h2
    exact h2.trans (Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) n]))
  have hr : 0≤R := div_nonneg (by linarith) hN.le
  change _≤(560*K+4)*(1+|s.im|)*R
  by_cases hy : |s.im|≤H/2
  · let W := zeroDecayWeight (1/2)
    have hw := weighted_zero_summability (1/2) (by norm_num)
    let S := (MasulloRH.TraceRate.lowHeight n)ᶜ
    have hsum : (∑ z∈F,W z)≤K*R := by
      have he : ∑ z∈F,W z=∑ z∈F,S.indicator W z := by
        apply Finset.sum_congr rfl
        intro z hz; rw [indicator_of_mem (show z∈S from not_le.mpr (hF z hz))]
      rw [he]; exact (Summable.sum_le_tsum F (fun z _ => indicator_nonneg
        (fun z _ => by dsimp [W,zeroDecayWeight]; positivity) _) (hw.indicator S)).trans (htail n)
    have one (z : Z) (hz : z∈F) : ‖1-pair (centered z) s ^ mult z‖ ≤
        (560*(1+|s.im|))*W z := by
      have hhigh : H< |z.val.im| := hF z hz
      have hge : 1≤H := by dsimp [H]; linarith [Nat.cast_nonneg (α:=ℝ) n]
      apply (cyclic_StripFilter_one_sub_pow (cyclic_StripFilter_pair_contract (cyclic_StripFilter_centered_gt z) hsr) _).trans
      apply (mul_le_mul_of_nonneg_left (cyclic_StripFilter_pair_estimate hrs (center_re z)
        (by rw [center_im]; exact hge.trans hhigh.le) (by rw [center_im]; linarith)) (Nat.cast_nonneg (mult z))).trans_eq
      rw [center_im]; dsimp only [W,zeroDecayWeight,mult]; ring
    have hg := cyclic_StripFilter_one_sub_finprod (fun z => pair (centered z) s ^ mult z) F (fun z _ =>
      by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (cyclic_StripFilter_pair_contract (cyclic_StripFilter_centered_gt z) hsr))
    apply (hg.trans (Finset.sum_le_sum one)).trans
    rw [← Finset.mul_sum]
    apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans
    nlinarith [mul_nonneg (abs_nonneg s.im) hr]
  · have hy' : ((n:ℝ)+1)≤1+|s.im| := by dsimp [H] at hy; linarith [lt_of_not_ge hy]
    have hg := mul_le_mul_of_nonneg_right hy' hr
    have he : ((n:ℝ)+1)*R = Real.log ((n:ℝ)+2) := by dsimp [R]; field_simp
    rw [he] at hg
    apply (global_two F hsr).trans
    nlinarith only [hL,hg,mul_nonneg hK (mul_nonneg (show 0≤1+|s.im| by positivity) hr)]

private theorem cyclic_StripFilter_factor_analytic {z u : ℂ} (hz : -3<z.re) (hu : -3<u.re) :
    AnalyticAt ℂ (factor z) u := by
  unfold factor
  exact (analyticAt_id.sub analyticAt_const).div ((analyticAt_id.add analyticAt_const).add analyticAt_const)
      (cyclic_StripFilter_denominator hz hu)

private theorem cyclic_StripFilter_pair_analytic {z u : ℂ} (hz : -3<z.re) (hu : -3<u.re) :
    AnalyticAt ℂ (pair z) u := (cyclic_StripFilter_factor_analytic hz hu).mul (cyclic_StripFilter_factor_analytic hz hu)

theorem filter_analytic (F : Finset Z) {u : ℂ} (hu : -3<u.re) :
    AnalyticAt ℂ (filterProd F) u :=
  F.analyticAt_fun_prod (fun z _ => (cyclic_StripFilter_pair_analytic (cyclic_StripFilter_centered_gt z) hu).pow _)

theorem selector_analytic (F : Finset Z) {u : ℂ} (hu : -3<u.re) :
    AnalyticAt ℂ (selector F) u :=
  analyticAt_const.sub ((analyticAt_const.sub (filter_analytic F hu)).pow 8)

theorem selector_factorization (F : Finset Z) (z : Z) (hz : z∈F) :
    ∃ g : ℂ→ℂ, (∀ u : ℂ, -3<u.re → AnalyticAt ℂ g u) ∧
      ∀ s : ℂ, selector F s=(s-centered z)^mult z*g s := by
  classical
  let a := centered z
  let b (s:ℂ) := (s+6+conj a)⁻¹ * factor (conj a) s
  let P (s:ℂ) := filterProd (F.erase z) s
  let Q (s:ℂ) := ∑ k ∈ Finset.range 8, (1-filterProd F s)^k
  refine ⟨fun s => (b s)^mult z*P s*Q s,?_,?_⟩
  · intro u hu
    have hb : AnalyticAt ℂ b u :=
      (((analyticAt_id.add analyticAt_const).add analyticAt_const).inv
       (cyclic_StripFilter_denominator (cyclic_StripFilter_centered_gt z) hu)).mul (cyclic_StripFilter_factor_analytic (cyclic_StripFilter_centered_gt z) hu)
    have hP : AnalyticAt ℂ P u := filter_analytic _ hu
    have hq : AnalyticAt ℂ Q u := (Finset.range 8).analyticAt_fun_sum
      (fun k _ => (analyticAt_const.sub (filter_analytic F hu)).pow k)
    exact ((hb.pow _).mul hP).mul hq
  · intro s
    have hprod : filterProd F s = (s-a)^mult z*((b s)^mult z*P s) := by
      have hh := Finset.mul_prod_erase F (fun j => pair (centered j) s ^ mult j) hz
      change _ = _ at hh
      change (∏ j ∈ F, pair (centered j) s ^ mult j)=_
      rw [← hh]
      have he : pair (centered z) s=(s-a)*b s := by dsimp [pair,b,factor,a]; ring
      rw [he,mul_pow]; exact mul_assoc _ _ _
    have hgeom : selector F s=filterProd F s*Q s := by
      simpa only [selector,sub_sub_cancel,Q] using (mul_neg_geom_sum (1-filterProd F s) 8).symm
    rw [hgeom,hprod]; ring

theorem selector_zero_jets (F : Finset Z) (z : Z) (hz : z∈F) :
    ∀ k < mult z, iteratedDeriv k (selector F) (centered z)=0 := by
  have ha := selector_analytic F (cyclic_StripFilter_centered_gt z)
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).mp
  apply (natCast_le_analyticOrderAt ha).mpr
  obtain ⟨g,hg,he⟩ := selector_factorization F z hz
  exact ⟨g,hg _ (cyclic_StripFilter_centered_gt z),Filter.Eventually.of_forall (fun s => he s)⟩

end
end MasulloRH.StripFilter

end StandaloneStripFilter

section StandaloneStripFilterMoment

open MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace MasulloRH.StripFilter
noncomputable section

theorem selector_uniform (F : Finset Z) {s : ℂ} (hs : -3<s.re) : ‖selector F s‖≤257 := by
  apply (norm_sub_le _ _).trans
  rw [norm_one,norm_pow]
  have hb := pow_le_pow_left₀ (norm_nonneg _) (global_two F hs) 8
  norm_num at hb; linarith

theorem selector_conj (F : Finset Z) (s : ℂ) : selector F (conj s)=conj (selector F s) := by
  have hb (z : ℂ) : pair z (conj s) = conj (pair z s) := by
    have h6 : conj (6:ℂ)=6 := map_natCast (starRingEnd ℂ) 6
    simp [pair,factor,mul_comm,h6]
  simp [selector,filterProd, hb]

/-- The eighth power compensates for the logarithm with a uniform fourth-order rate. -/
private theorem cyclic_StripFilterMoment_eighth_rate (n : ℕ) :
    (Real.log ((n:ℝ)+2)/((n:ℝ)+1))^8 ≤ 4096/((n:ℝ)+1)^4 := by
  let N : ℝ := n+1
  have hN : 1≤N := by dsimp [N]; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hp : 0<N := by linarith
  have hL : Real.log (N+1) ≤ 2*Real.sqrt (N+1) := by
    have h := Real.log_le_rpow_div (x:=N+1) (by positivity) (show (0:ℝ)<1/2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h; linarith
  have hlog := Real.log_nonneg (show 1≤N+1 by linarith)
  have hsq : Real.log (N+1)^2≤8*N := by
    have h := pow_le_pow_left₀ hlog hL 2
    nlinarith [Real.sq_sqrt (show 0≤N+1 by positivity)]
  have h4 := pow_le_pow_left₀ (sq_nonneg _) hsq 4
  change (Real.log ((n:ℝ)+2)/N)^8≤4096/N^4
  rw [show ((n:ℝ)+2)=N+1 by dsimp [N]; ring,div_pow]
  calc
    _ ≤ (8*N)^4/N^8 := by apply div_le_div_of_nonneg_right _ (by positivity); convert h4 using 1 <;> ring
    _ = _ := by field_simp; ring

def vertical (σ t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I

@[simp] theorem vertical_re (σ t : ℝ) : (vertical σ t).re=σ := by simp [vertical]
@[simp] theorem vertical_im (σ t : ℝ) : (vertical σ t).im=t := by simp [vertical]

/-- The error in a vertical integral is controlled by one fixed weighted moment of the multiplier. -/
theorem boundary_L1_error :
    ∃ D : ℝ, 0<D ∧ ∀ n : ℕ, ∀ F : Finset Z,
      (∀ z∈F, (5/2:ℝ)+2*n < |z.val.im|) → ∀ σ : ℝ, |σ|≤2 →
      ∀ h : ℝ→ℂ, AEStronglyMeasurable h volume →
      Integrable (fun t : ℝ => (1+|t|)^8*‖h t‖) →
      Integrable (fun t : ℝ => (1-selector F (vertical σ t))*h t) ∧
      (∫ t : ℝ, ‖(1-selector F (vertical σ t))*h t‖) ≤
        (D/((n:ℝ)+1)^4) * (∫ t : ℝ, (1+|t|)^8*‖h t‖) := by
  obtain ⟨C,hC,hb⟩ := finite_filter_bound
  refine ⟨4096*C^8,by positivity,?_⟩
  intro n F hF σ hσ h hm hi
  let d := (4096*C^8)/((n:ℝ)+1)^4
  let A (t : ℝ) := (1+|t|)^8*‖h t‖
  let e (t : ℝ) := (1-selector F (vertical σ t))*h t
  have hl := Real.log_nonneg (show 1≤(n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have he (t : ℝ) : ‖e t‖≤d*A t := by
    change ‖(1-selector F (vertical σ t))*h t‖≤_
    rw [selector,sub_sub_cancel,norm_mul,norm_pow]
    have hss : |(vertical σ t).re|≤2 := by simpa using hσ
    have hh := hb n F hF (vertical σ t) hss
    rw [vertical_im] at hh
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hh 8) (norm_nonneg _)).trans
    rw [mul_pow,mul_pow]
    calc
      _ ≤ (C^8*(1+|t|)^8)*(4096/((n:ℝ)+1)^4)*‖h t‖ := by gcongr; exact cyclic_StripFilterMoment_eighth_rate n
      _ = d*A t := by dsimp [d,A]; ring
  have hs : Continuous (fun t : ℝ => selector F (vertical σ t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hsr : -3<(vertical σ t).re := by rw [vertical_re]; linarith [(abs_le.mp hσ).1]
    apply (selector_analytic F hsr).continuousAt.comp
    unfold vertical; fun_prop
  have hi' : Integrable (fun t => d * A t) := hi.const_mul d
  have heI : Integrable e := hi'.mono' ((continuous_const.sub hs).aestronglyMeasurable.mul hm)
    (Filter.Eventually.of_forall he)
  refine ⟨heI,?_⟩
  apply (integral_mono_ae heI.norm hi' (Filter.Eventually.of_forall he)).trans_eq
  exact integral_const_mul d A

open scoped SchwartzMap

theorem schwartz_moment_eight (h : 𝓢(ℝ,ℂ)) : Integrable (fun t : ℝ => (1+|t|)^8*‖h t‖) := by
  have hi := (h.integrable (μ:=volume)).norm.add (h.integrable_pow_mul volume 8)
  apply (hi.const_mul (256:ℝ)).mono'
  · apply Continuous.aestronglyMeasurable
    exact ((continuous_const.add continuous_abs).pow 8).mul h.continuous.norm
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    change (1+|t|)^8*‖h t‖≤256*(‖h t‖+‖t‖^8*‖h t‖)
    rw [Real.norm_eq_abs]
    have hh : (1+|t|)^8≤256*(1+|t|^8) := by
      by_cases ht : |t|≤1
      · have hq := pow_le_pow_left₀ (show 0≤1+|t| by positivity) (show 1+|t|≤2 by linarith) 8
        norm_num at hq; linarith [show 0≤|t|^8 by positivity]
      · have hq := pow_le_pow_left₀ (show 0≤1+|t| by positivity) (show 1+|t|≤2*|t| by linarith [not_le.mp ht]) 8
        rw [mul_pow] at hq; norm_num at hq; linarith
    simpa only [mul_assoc,add_mul,one_mul] using mul_le_mul_of_nonneg_right hh (norm_nonneg _)

theorem schwartz_boundary_error (h : 𝓢(ℝ,ℂ)) :
    ∃ D : ℝ, 0<D ∧ ∀ n : ℕ, ∀ F : Finset Z,
      (∀ z∈F, (5/2:ℝ)+2*n < |z.val.im|) → ∀ σ : ℝ, |σ|≤2 →
      Integrable (fun t : ℝ => (1-selector F (vertical σ t))*h t) ∧
      (∫ t : ℝ, ‖(1-selector F (vertical σ t))*h t‖) ≤ D/((n:ℝ)+1)^4 := by
  obtain ⟨C,hC,hb⟩ := boundary_L1_error
  let M := ∫ t : ℝ, (1+|t|)^8*‖h t‖
  have hM : 0≤M := integral_nonneg (fun t => by positivity)
  refine ⟨C*M+1,by positivity,?_⟩
  intro n F hF σ hσ
  obtain ⟨hi,he⟩ := hb n F hF σ hσ h h.continuous.aestronglyMeasurable (schwartz_moment_eight h)
  refine ⟨hi,he.trans ?_⟩
  change C/((n:ℝ)+1)^4*M ≤ (C*M+1)/((n:ℝ)+1)^4
  rw [div_mul_eq_mul_div]; gcongr; linarith

end
end MasulloRH.StripFilter

end StandaloneStripFilterMoment

section StandaloneStripFilterUniform

open MeasureTheory
open scoped Topology
namespace MasulloRH.StripFilter
noncomputable section

/-- A single tenth-order multiplier bound gives a fourth-order vertical L¹ error with
a constant independent of the evaluation line, the height index, and the selected finite zeros. -/
theorem uniform_boundary_error (g : ℂ → ℂ) (hg : Continuous g) (B : ℝ) (hB : 0≤B)
    (hbd : ∀ s : ℂ, |s.re|≤2 → (1+|s.im|)^10*‖g s‖≤B) :
    ∃ D : ℝ, 0<D ∧ ∀ n : ℕ, ∀ F : Finset Z,
      (∀ z∈F, (5/2:ℝ)+2*n < |z.val.im|) → ∀ σ : ℝ, |σ|≤2 →
      Integrable (fun t : ℝ => (1-selector F (vertical σ t))*g (vertical σ t)) ∧
      (∫ t : ℝ, ‖(1-selector F (vertical σ t))*g (vertical σ t)‖) ≤ D/((n:ℝ)+1)^4 := by
  let v (t : ℝ) := ((1+|t|)^2)⁻¹
  have hv : Integrable v := by
    have h := (integrable_one_add_norm (μ:=volume) (E:=ℝ) (r:=2) (by simp))
    apply h.congr
    filter_upwards with x
    rw [Real.norm_eq_abs,Real.rpow_neg (by positivity),Real.rpow_two]
  have vnn (t : ℝ) : 0≤v t := by dsimp [v]; positivity
  obtain ⟨C,hC,hc⟩ := boundary_L1_error
  let M := B*(∫ t : ℝ,v t)
  have hM : 0≤M := mul_nonneg hB (integral_nonneg vnn)
  refine ⟨C*M+1,by positivity,?_⟩
  intro n F hF σ hσ
  let h (t:ℝ) := g (vertical σ t)
  let A (t:ℝ) := (1+|t|)^8*‖h t‖
  have hn (t:ℝ) : A t≤B*v t := by
    have h10 := hbd (vertical σ t) (by simpa using hσ)
    rw [vertical_im] at h10
    dsimp only [A,h,v]
    rw [← div_eq_mul_inv,le_div_iff₀ (by positivity : 0<(1+|t|)^2)]
    calc
      _ = (1+|t|)^10*‖g (vertical σ t)‖ := by ring
      _ ≤ B := h10
  have hcont : Continuous h := by apply hg.comp; unfold vertical; fun_prop
  have hAc : Continuous A := ((continuous_const.add continuous_abs).pow 8).mul hcont.norm
  have hAi : Integrable A := (hv.const_mul B).mono' hAc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤A t by dsimp [A]; positivity)]
      exact hn t))
  have hm : (∫ t : ℝ,A t)≤M := by
    apply (integral_mono_ae hAi (hv.const_mul B) (Filter.Eventually.of_forall hn)).trans_eq
    exact integral_const_mul B v
  obtain ⟨hi,he⟩ := hc n F hF σ hσ h hcont.aestronglyMeasurable hAi
  refine ⟨hi,he.trans ?_⟩
  apply (mul_le_mul_of_nonneg_left hm (by positivity : 0≤C/((n:ℝ)+1)^4)).trans
  rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end
end MasulloRH.StripFilter

end StandaloneStripFilterUniform

section StandaloneStripFilterMellin

open MeasureTheory Set Filter
open scoped Topology
namespace MasulloRH.StripFilter
noncomputable section

theorem mellin_boundary_error (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ D : ℝ, 0<D ∧ ∀ n : ℕ, ∀ F : Finset Z,
      (∀ z∈F, (5/2:ℝ)+2*n < |z.val.im|) → ∀ σ : ℝ, |σ|≤2 →
      Integrable (fun t : ℝ => (1-selector F (vertical σ t))*mellin φ (vertical σ t)) ∧
      (∫ t : ℝ, ‖(1-selector F (vertical σ t))*mellin φ (vertical σ t)‖) ≤ D/((n:ℝ)+1)^4 := by
  obtain ⟨B,hB,h⟩ := StripTrace.mellin_strip_rapid φ hφ 10
  exact uniform_boundary_error _ (StripTrace.mellin_entire φ hφ).continuous B hB h

theorem filtered_mellin_zero_jets (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ)
    (F : Finset Z) (z : Z) (hz : z∈F) :
    ∀ j < mult z, iteratedDeriv j (fun s => selector F s * mellin φ s) (centered z)=0 := by
  let a := centered z
  have hs : -3<a.re := by have h := (abs_le.mp (center_re z)).1; dsimp [a]; linarith
  have hf : AnalyticAt ℂ (selector F) a := selector_analytic F hs
  have hm : AnalyticAt ℂ (mellin φ) a := (StripTrace.mellin_entire φ hφ).analyticAt _
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.mul hm)).mp
  apply (natCast_le_analyticOrderAt (hf.mul hm)).mpr
  obtain ⟨g,hg,he⟩ := selector_factorization F z hz
  exact ⟨fun s => g s*mellin φ s,(hg _ hs).mul hm,.of_forall (fun s => by
    change selector F s*mellin φ s=(s-centered z)^mult z*(g s*mellin φ s)
    rw [he]; exact mul_assoc _ _ _)⟩

end
end MasulloRH.StripFilter

end StandaloneStripFilterMellin

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

def errorAmplitude (φ : ℝ→ℂ) (F : Finset StripFilter.Z) (s : ℂ) : ℂ :=
  (1-selector F s)*mellin φ s

theorem errorAmplitude_analytic (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) (F : Finset StripFilter.Z)
    {s : ℂ} (hs : -3<s.re) : AnalyticAt ℂ (errorAmplitude φ F) s :=
  (analyticAt_const.sub (selector_analytic F hs)).mul ((mellin_entire φ hφ).analyticAt _)

theorem errorAmplitude_rapid (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) (j : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (F : Finset StripFilter.Z) (s : ℂ), |s.re|≤2 →
      (1+|s.im|)^j * ‖errorAmplitude φ F s‖ ≤ C := by
  obtain ⟨B,hB,h⟩ := mellin_strip_rapid φ hφ j
  refine ⟨256*B,by positivity,fun F s hs => ?_⟩
  have hs' : -3<s.re := by linarith [(abs_le.mp hs).1]
  have he : ‖(1:ℂ)-selector F s‖≤256 := by
    rw [selector,sub_sub_cancel,norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (global_two F hs') 8).trans (by norm_num)
  unfold errorAmplitude
  rw [norm_mul,mul_left_comm]
  exact mul_le_mul he (h s hs) (by positivity) (by norm_num)

theorem matching_moments (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) (F : Finset StripFilter.Z)
    {k : ℝ→ℂ} (hk : AEStronglyMeasurable k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp ((3/2:ℝ)*|y|)))
    (hL : ∀ s : ℂ, |s.re|<3/2 → lap k s=errorAmplitude φ F s)
    (z : StripFilter.Z) (hz : z∈F) (j : ℕ) (hj : j<StripFilter.mult z) :
    moment (fun y => φ (Real.exp y)) (centered z) j = moment k (centered z) j := by
  let a := centered z
  have ha : |a.re| < 3/2 := (center_re z).trans_lt (by norm_num)
  have hs : -3<a.re := by linarith [(abs_lt.mp ha).1]
  have hloc : ∀ᶠ t : ℂ in 𝓝 a, |t.re|<3/2 := (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const).mem_nhds ha
  have h₁ : lap k =ᶠ[𝓝 a] errorAmplitude φ F := hloc.mono (fun _ ht => hL _ ht)
  have h₂ : (fun s => mellin φ s - errorAmplitude φ F s) = fun s => selector F s*mellin φ s := by
    funext s; unfold errorAmplitude; ring
  have hn := filtered_mellin_zero_jets φ hφ F z hz j hj
  rw [← h₂] at hn
  change iteratedDeriv j (mellin φ - errorAmplitude φ F) a = 0 at hn
  rw [iteratedDeriv_sub ((mellin_entire φ hφ).analyticAt a).contDiffAt
    (errorAmplitude_analytic φ hφ F hs).contDiffAt,sub_eq_zero] at hn
  exact (mellin_iterated_eq_moment φ hφ j a).symm.trans (hn.trans ((h₁.iteratedDeriv_eq j).symm.trans (lap_iteratedDeriv hk hW j ha)))

/-- Only the inverse transform at order zero is needed; the derivative data for every
selected zero follow from analytic differentiation. -/
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

section StandaloneStripWallBound

open MeasureTheory Filter Set
open scoped Topology FourierTransform
namespace MasulloRH.StripTrace
noncomputable section
open StripFilter

private def cyclic_StripWallBound_tilt (k : ℝ→ℂ) (σ y : ℝ) : ℂ := (Real.exp (σ*y):ℂ)*k y

private theorem cyclic_StripWallBound_tilt_norm (k : ℝ→ℂ) (σ y : ℝ) :
    ‖cyclic_StripWallBound_tilt k σ y‖=‖k y‖*Real.exp (σ*y) := by
  rw [cyclic_StripWallBound_tilt,norm_mul,Complex.norm_of_nonneg (Real.exp_nonneg _),mul_comm]

private theorem cyclic_StripWallBound_tilt_fourier (k : ℝ→ℂ) (σ t : ℝ) :
    𝓕 (cyclic_StripWallBound_tilt k σ) t = lap k (vertical σ ((-2*Real.pi)*t)) := by
  rw [Real.fourier_real_eq_integral_exp_smul,lap]
  apply integral_congr_ae
  filter_upwards with y
  simp only [cyclic_StripWallBound_tilt,smul_eq_mul,Complex.ofReal_exp,←mul_assoc,←Complex.exp_add,vertical]
  congr 2
  push_cast
  ring

private theorem cyclic_StripWallBound_tilt_bound (k : ℝ→ℂ) (hk : Continuous k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (2*|y|))) (σ : ℝ) (hσ : |σ|≤2)
    (hi : Integrable (fun t : ℝ => lap k (vertical σ t))) (y : ℝ) :
    ‖k y‖*Real.exp (σ*y) ≤ ∫ t : ℝ, ‖lap k (vertical σ t)‖ := by
  let f := cyclic_StripWallBound_tilt k σ
  let g (t : ℝ) := lap k (vertical σ t)
  have hc : Continuous f := (show Continuous (fun y : ℝ => (Real.exp (σ*y):ℂ)) by fun_prop).mul hk
  have hI : Integrable f := hW.mono' hc.aestronglyMeasurable (.of_forall fun t => by
    rw [show ‖f t‖=‖k t‖*Real.exp (σ*t) by exact cyclic_StripWallBound_tilt_norm _ _ _]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    have hl := le_abs_self (σ*t)
    rw [abs_mul] at hl
    exact hl.trans (mul_le_mul_of_nonneg_right hσ (abs_nonneg _)))
  have heq : 𝓕 f = fun t => g ((-2*Real.pi)*t) := funext (cyclic_StripWallBound_tilt_fourier k σ)
  have hbeat : (-2*Real.pi:ℝ)≠0 := by have := Real.pi_pos; positivity
  have hF : Integrable (𝓕 f) := by
    rw [heq]
    exact hi.comp_mul_left' hbeat
  rw [← cyclic_StripWallBound_tilt_norm,show cyclic_StripWallBound_tilt k σ y=f y by rfl,←hI.fourierInv_fourier_eq hF hc.continuousAt]
  calc
    _ ≤ ∫ t : ℝ, ‖𝓕 f t‖ := by
      rw [Real.fourierInv_eq]
      exact (norm_integral_le_integral_norm _).trans_eq (by simp only [Circle.norm_smul])
    _ = |(-2*Real.pi)⁻¹| *(∫ t : ℝ, ‖g t‖) := by
      rw [heq]
      exact Measure.integral_comp_mul_left (fun t => ‖g t‖) _
    _ ≤ _ := by
      apply mul_le_of_le_one_left (integral_nonneg (fun t => norm_nonneg _))
      rw [abs_inv,inv_le_one₀ (abs_pos.mpr hbeat),abs_of_neg (by have := Real.pi_pos; linarith)]
      linarith [Real.pi_gt_three]

private theorem cyclic_StripWallBound_half_gap_integrable : Integrable (fun x : ℝ => Real.exp ((-1/2:ℝ)*|x|)) := by
  let f (x : ℝ) := Real.exp ((-1/2:ℝ)*|x|)
  have hr : IntegrableOn f (Ioi 0) := (integrableOn_exp_mul_Ioi (by norm_num : (-1/2:ℝ)<0) 0).congr_fun
    (fun x hx => by simp only [f,abs_of_pos (show 0<x from hx)]) measurableSet_Ioi
  have hl : IntegrableOn f (Iic 0) := (integrableOn_exp_mul_Iic (by norm_num : 0<(1/2:ℝ)) 0).congr_fun
    (fun x hx => by dsimp [f]; rw [abs_of_nonpos (show x≤0 from hx)]; congr 1; ring) measurableSet_Iic
  change Integrable f
  simpa using hl.union hr

private theorem cyclic_StripWallBound_half_gap_integral : (∫x : ℝ, Real.exp ((-1/2:ℝ)*|x|))=4 := by
  rw [integral_comp_abs (f:=fun x => Real.exp ((-1/2:ℝ)*x)),integral_exp_mul_Ioi (by norm_num : (-1/2:ℝ)<0)]
  norm_num

theorem weighted_wall_bound {k : ℝ→ℂ} (hk : Continuous k)
    (hW : Integrable (fun y => ‖k y‖*Real.exp (2*|y|))) (E : ℝ)
    (hwall : ∀ σ : ℝ, |σ| = 2 →
      Integrable (fun t : ℝ => lap k (vertical σ t)) ∧ (∫t : ℝ, ‖lap k (vertical σ t)‖)≤E) :
    Integrable (fun y : ℝ => ‖k y‖*Real.exp ((3/2:ℝ)*|y|)) ∧
    (∫ y : ℝ, ‖k y‖*Real.exp ((3/2:ℝ)*|y|)) ≤ 4*E := by
  have hm (y : ℝ) : ‖k y‖*Real.exp ((3/2:ℝ)*|y|) ≤ E*Real.exp ((-1/2:ℝ)*|y|) := by
    let σ : ℝ := if 0≤y then 2 else -2
    have hσ : |σ|=2 := by dsimp [σ]; split <;> norm_num
    have he : σ*y=2*|y| := by
      dsimp [σ]; split_ifs with h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
    have h := (cyclic_StripWallBound_tilt_bound k hk hW σ hσ.le (hwall σ hσ).1 y).trans (hwall σ hσ).2
    rw [he] at h
    calc
      _ = (‖k y‖*Real.exp (2*|y|))*Real.exp ((-1/2:ℝ)*|y|) := by
        rw [mul_assoc,←Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h (Real.exp_nonneg _)
  have hI : Integrable (fun y : ℝ => ‖k y‖*Real.exp ((3/2:ℝ)*|y|)) :=
    (cyclic_StripWallBound_half_gap_integrable.const_mul E).mono'
      (hk.norm.mul (show Continuous (fun y : ℝ => Real.exp ((3/2:ℝ)*|y|)) by fun_prop)).aestronglyMeasurable
      (.of_forall (fun y => by
        change ‖‖k y‖*Real.exp ((3/2:ℝ)*|y|)‖≤_
        rw [Real.norm_of_nonneg (by positivity)]
        exact hm y))
  refine ⟨hI,(integral_mono hI (cyclic_StripWallBound_half_gap_integrable.const_mul E) hm).trans_eq ?_⟩
  rw [integral_const_mul,cyclic_StripWallBound_half_gap_integral,mul_comm]

theorem small_error_kernels_of_wall_inverse (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ)
    (hinv : ∀ F : Finset StripFilter.Z, ∃ k : ℝ→ℂ, Continuous k ∧
      Integrable (fun y => ‖k y‖*Real.exp (2*|y|)) ∧ ∀ s : ℂ, |s.re|≤2 → lap k s=errorAmplitude φ F s) :
    HasSmallErrorKernels φ := by
  obtain ⟨D,hD,hbd⟩ := StripFilter.mellin_boundary_error φ hφ
  refine ⟨4*D,by positivity,fun n F hF => ?_⟩
  obtain ⟨k,hk,hW,hkL⟩ := hinv F
  have hwall (σ : ℝ) (hσ : |σ|=2) :
      Integrable (fun t : ℝ => lap k (vertical σ t)) ∧
      (∫ t : ℝ, ‖lap k (vertical σ t)‖)≤D/((n:ℝ)+1)^4 := by
    have he : (fun t : ℝ => lap k (vertical σ t)) = fun t : ℝ => errorAmplitude φ F (vertical σ t) :=
      funext (fun t => hkL _ (by simpa [vertical] using hσ.le))
    have h := hbd n F hF σ hσ.le
    constructor
    · rw [he]; exact h.1
    · simp_rw [show ∀ t : ℝ, lap k (vertical σ t)=errorAmplitude φ F (vertical σ t) from fun t => congrFun he t]
      exact h.2
  obtain ⟨hJ,hJb⟩ := weighted_wall_bound hk hW _ hwall
  refine ⟨k,hk.aestronglyMeasurable,hJ,hJb.trans_eq (by ring),?_⟩
  exact fun z hz j hj => matching_moments φ hφ F hk.aestronglyMeasurable hJ
    (fun s h => hkL s (by linarith)) z hz j hj

end
end MasulloRH.StripTrace

end StandaloneStripWallBound

section StandaloneStripRationalKernelAlgebra

open MeasureTheory Set Filter
open scoped Topology Convolution ComplexConjugate
namespace MasulloRH.StripRationalKernel
noncomputable section
open StripTrace (lap)

def twist (s : ℂ) (f : ℝ→ℂ) (y : ℝ) := Complex.exp (s*y)*f y
def Kern (f : ℝ→ℂ) : Prop := ∀ s : ℂ, |s.re|≤2 → Integrable (twist s f)
def conv (f g : ℝ→ℂ) := f ⋆[ContinuousLinearMap.mul ℂ ℂ] g

theorem kern_integrable {f : ℝ→ℂ} (hf : Kern f) : Integrable f := by
  have h : twist 0 f=f := funext (fun y => by simp [twist])
  simpa only [h] using hf 0 (by norm_num)

theorem kern_energy {f : ℝ→ℂ} (hf : Kern f) :
    Integrable (fun y => ‖f y‖*Real.exp (2*|y|)) := by
  have h := ((hf 2 (by norm_num)).norm).add ((hf (-2) (by norm_num)).norm)
  apply h.mono' ((kern_integrable hf).aestronglyMeasurable.norm.mul
    (show Continuous (fun y : ℝ => Real.exp (2*|y|)) by fun_prop).aestronglyMeasurable)
  filter_upwards with y
  change ‖‖f y‖*Real.exp (2*|y|)‖ ≤ ‖twist 2 f y‖+‖twist (-2) f y‖
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [twist,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero,Complex.neg_re,Complex.re_ofNat]
  rcases le_total 0 y with hy|hy
  · rw [abs_of_nonneg hy,mul_comm (‖f y‖)]
    exact le_add_of_nonneg_right (by positivity)
  · rw [abs_of_nonpos hy,show 2*(-y)=(-2)*y by ring,mul_comm (‖f y‖)]
    exact le_add_of_nonneg_left (by positivity)

theorem kern_zero : Kern 0 := by
  intro s _
  rw [show twist s 0=0 by funext y; simp [twist]]
  exact integrable_zero _ _ _
theorem lap_zero (s : ℂ) : lap 0 s=0 := by simp [lap]

theorem kern_add {f g : ℝ→ℂ} (hf : Kern f) (hg : Kern g) : Kern (f+g) := by
  intro s hs
  rw [show twist s (f+g)=twist s f+twist s g by funext y; simp [twist,mul_add]]
  exact (hf s hs).add (hg s hs)

theorem lap_add {f g : ℝ→ℂ} (hf : Kern f) (hg : Kern g) (s : ℂ) (hs : |s.re|≤2) :
    lap (f+g) s = lap f s + lap g s := by
  simp only [lap,Pi.add_apply,mul_add]
  exact integral_add (hf s hs) (hg s hs)

theorem kern_scale {f : ℝ→ℂ} (hf : Kern f) (c : ℂ) : Kern (fun y => c*f y) := by
  intro s hs
  rw [show twist s (fun y => c*f y)=(fun y=>c*twist s f y) by funext y; dsimp [twist]; ring]
  exact (hf s hs).const_mul c

theorem lap_scale (f : ℝ→ℂ) (c s : ℂ) : lap (fun y => c*f y) s = c*lap f s := by
  simp only [lap,mul_left_comm (Complex.exp _ : ℂ) c,integral_const_mul]

theorem twist_conv (s : ℂ) (f g : ℝ→ℂ) : twist s (conv f g) = conv (twist s f) (twist s g) := by
  funext x
  change Complex.exp (s*x)*(∫ t : ℝ,f t*g (x-t)) =
    ∫ t : ℝ,(Complex.exp (s*t)*f t)*(Complex.exp (s*((x-t:ℝ):ℂ))*g (x-t))
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [show s*(x:ℂ)=s*(t:ℂ)+s*((x-t:ℝ):ℂ) by push_cast; ring, Complex.exp_add]
  ring

theorem kern_conv {f g : ℝ→ℂ} (hf : Kern f) (hg : Kern g) : Kern (conv f g) := by
  intro s hs
  rw [twist_conv]
  exact (hf s hs).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (hg s hs)

theorem lap_conv {f g : ℝ→ℂ} (hf : Kern f) (hg : Kern g) (s : ℂ) (hs : |s.re|≤2) :
    lap (conv f g) s = lap f s * lap g s := by
  change (∫ y,twist s (conv f g) y)=_
  rw [twist_conv]
  exact integral_convolution (ContinuousLinearMap.mul ℂ ℂ) (hf s hs) (hg s hs)

/-- Laplace transform on the strip of a point mass plus a density integrable on both walls. -/
def Realized (A : ℂ→ℂ) := ∃ c : ℂ, ∃ f : ℝ→ℂ, Kern f ∧ ∀ s : ℂ, |s.re|≤2 → A s=c+lap f s

theorem realized_const (c : ℂ) : Realized (fun _ => c) :=
  ⟨c,0,kern_zero,fun s _ => by rw [lap_zero,add_zero]⟩

theorem realized_add {A B : ℂ→ℂ} (ha : Realized A) (hb : Realized B) : Realized (fun s => A s+B s) := by
  obtain ⟨a,f,hf,hA⟩ := ha
  obtain ⟨b,g,hg,hB⟩ := hb
  exact ⟨a+b,f+g,kern_add hf hg,fun s hs => by dsimp only; rw [hA s hs,hB s hs,lap_add hf hg s hs]; ring⟩

theorem realized_scale {A : ℂ→ℂ} (ha : Realized A) (c : ℂ) : Realized (fun s => c*A s) := by
  obtain ⟨a,f,hf,hA⟩ := ha
  exact ⟨c*a,fun y => c*f y,kern_scale hf c,fun s hs => by dsimp only; rw [hA s hs,lap_scale]; ring⟩

theorem realized_one_sub {A : ℂ→ℂ} (ha : Realized A) : Realized (fun s => 1-A s) := by
  simpa [sub_eq_add_neg] using realized_add (realized_const 1) (realized_scale ha (-1))

theorem realized_mul {A B : ℂ→ℂ} (ha : Realized A) (hb : Realized B) : Realized (fun s => A s*B s) := by
  obtain ⟨a,f,hf,hA⟩ := ha
  obtain ⟨b,g,hg,hB⟩ := hb
  let f₁ := fun y => a*g y
  let f₂ := fun y => b*f y
  have h₁ : Kern f₁ := kern_scale hg a
  have h₂ : Kern f₂ := kern_scale hf b
  have h₃ := kern_conv hf hg
  refine ⟨a*b,(f₁+f₂)+conv f g,kern_add (kern_add h₁ h₂) h₃,fun s hs => ?_⟩
  dsimp only
  rw [hA s hs,hB s hs,lap_add (kern_add h₁ h₂) h₃ s hs,lap_add h₁ h₂ s hs,lap_conv hf hg s hs]
  simp only [f₁,f₂,lap_scale]
  ring

theorem realized_pow {A : ℂ→ℂ} (ha : Realized A) (n : ℕ) : Realized (fun s => (A s)^n) := by
  induction n with
  | zero => simpa using realized_const 1
  | succ n ih => simpa only [pow_succ] using realized_mul ih ha

theorem realized_finprod {ι : Type*} (F : Finset ι) (A : ι→ℂ→ℂ) (ha : ∀ i,Realized (A i)) :
    Realized (fun s => ∏ i∈F,A i s) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using realized_const 1
  | insert i F hi ih => simpa [Finset.prod_insert hi] using realized_mul (ha i) ih

end
end MasulloRH.StripRationalKernel

end StandaloneStripRationalKernelAlgebra

section StandaloneStripRationalKernel

open MeasureTheory Set Filter
open scoped Topology Convolution ComplexConjugate
namespace MasulloRH.StripRationalKernel
noncomputable section
open StripTrace (lap)

def causal (a : ℂ) : ℝ→ℂ := (Iic 0).indicator (fun y : ℝ => Complex.exp (a*y))

theorem twist_causal (s a : ℂ) : twist s (causal a) = causal (s+a) := by
  classical
  funext y
  by_cases hy : y∈Iic (0:ℝ)
  · simp [twist,causal,hy,add_mul,Complex.exp_add]
  · simp [twist,causal,hy]

theorem kern_causal {a : ℂ} (ha : 2<a.re) : Kern (causal a) := by
  intro s hs
  rw [twist_causal]
  have hh : 0<(s+a).re := by rw [Complex.add_re]; linarith [(abs_le.mp hs).1]
  exact (integrableOn_exp_mul_complex_Iic hh 0).integrable_indicator measurableSet_Iic

theorem lap_causal {a : ℂ} (ha : 2<a.re) (s : ℂ) (hs : |s.re|≤2) :
    lap (causal a) s=1/(s+a) := by
  change (∫ y,twist s (causal a) y)=_
  rw [twist_causal,causal,integral_indicator measurableSet_Iic]
  have hh : 0<(s+a).re := by rw [Complex.add_re]; linarith [(abs_le.mp hs).1]
  simpa using integral_exp_mul_complex_Iic hh 0

theorem realized_factor (z : ℂ) (hz : |z.re|≤1/2) : Realized (StripFilter.factor z) := by
  let a : ℂ := 6+conj z
  have ha : 2<a.re := by simp only [a,Complex.add_re,Complex.re_ofNat,Complex.conj_re]; linarith [(abs_le.mp hz).1]
  let c := -(6+z+conj z)
  refine ⟨1,fun y => c*causal a y,kern_scale (kern_causal ha) c,fun s hs => ?_⟩
  rw [lap_scale,lap_causal ha s hs]
  have hden : s+a ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    rw [Complex.add_re,Complex.zero_re] at hr
    linarith [(abs_le.mp hs).1]
  unfold StripFilter.factor
  rw [show s+6+conj z=s+a by dsimp [a]; ring]
  field_simp [hden]
  dsimp [a,c]; ring

theorem realized_filter (F : Finset StripFilter.Z) : Realized (StripFilter.filterProd F) := by
  unfold StripFilter.filterProd
  apply realized_finprod
  intro z
  apply realized_pow
  apply realized_mul
  · exact realized_factor _ (StripFilter.center_re z)
  · exact realized_factor _ (by simpa using StripFilter.center_re z)

theorem realized_error_multiplier (F : Finset StripFilter.Z) :
    Realized (fun s => 1-StripFilter.selector F s) := by
  simpa only [StripFilter.selector,sub_sub_cancel] using realized_pow (realized_one_sub (realized_filter F)) 8

theorem apply_realized {A : ℂ→ℂ} (hA : Realized A) (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ k : ℝ→ℂ, Continuous k ∧ Integrable (fun y => ‖k y‖*Real.exp (2*|y|)) ∧
      ∀ s : ℂ, |s.re|≤2 → lap k s = A s*mellin φ s := by
  let g (y : ℝ) := φ (Real.exp y)
  have hc : Continuous g := hφ.1.continuous.comp Real.continuous_exp
  have hsupp : HasCompactSupport g := StripTrace.log_compact φ hφ
  have hg : Kern g := by
    intro s _
    apply (show Continuous (twist s g) from (show Continuous (fun y : ℝ => Complex.exp (s*y)) by fun_prop).mul hc).integrable_of_hasCompactSupport
    exact hsupp.mul_left
  obtain ⟨c,f,hf,hAs⟩ := hA
  let k₁ := fun y => c*g y
  let k₂ := conv f g
  have hk₁ : Kern k₁ := kern_scale hg _
  have hk₂ : Kern k₂ := kern_conv hf hg
  have hc₁ : Continuous k₁ := continuous_const.mul hc
  have hc₂ : Continuous k₂ := hsupp.continuous_convolution_right (ContinuousLinearMap.mul ℂ ℂ)
    (kern_integrable hf).locallyIntegrable hc
  refine ⟨k₁+k₂,hc₁.add hc₂,kern_energy (kern_add hk₁ hk₂),fun s hs => ?_⟩
  rw [lap_add hk₁ hk₂ s hs,hAs s hs,StripTrace.mellin_eq_lap]
  change lap (fun y => c*g y) s+lap (conv f g) s=(c+lap f s)*lap g s
  rw [lap_scale,lap_conv hf hg s hs,add_mul]

theorem exists_error_kernel (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) (F : Finset StripFilter.Z) :
    ∃ k : ℝ→ℂ, Continuous k ∧ Integrable (fun y => ‖k y‖*Real.exp (2*|y|)) ∧
      ∀ s : ℂ, |s.re|≤2 → lap k s = StripTrace.errorAmplitude φ F s :=
  apply_realized (realized_error_multiplier F) φ hφ

end
end MasulloRH.StripRationalKernel

end StandaloneStripRationalKernel

section StandaloneStripSmallErrorKernels

namespace MasulloRH.StripTrace

theorem hasSmallErrorKernels (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) : HasSmallErrorKernels φ :=
  small_error_kernels_of_wall_inverse φ hφ (StripRationalKernel.exists_error_kernel φ hφ)

end MasulloRH.StripTrace

end StandaloneStripSmallErrorKernels

section StandaloneStripHighKernelFinal

open MeasureTheory MasulloRH
open scoped Topology

theorem solution (φ : ℝ→ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, ∀ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z∈F, (5/2:ℝ)+2*n < |z.val.im|) →
      ∃ k : ℝ→ℂ, AEStronglyMeasurable k ∧
        Integrable (fun y => ‖k y‖*Real.exp ((3/2:ℝ)*|y|)) ∧
        (∫ y : ℝ, ‖k y‖*Real.exp ((3/2:ℝ)*|y|)) ≤ K/((n:ℝ)+1)^4 ∧
        ∀ z∈F, ∀ j < analyticOrderNatAt riemannZeta z.val,
          (∫ y : ℝ, φ (Real.exp y)*(y:ℂ)^j*Complex.exp ((z.val-1/2)*y)) =
          ∫ y : ℝ, k y*(y:ℂ)^j*Complex.exp ((z.val-1/2)*y) := by
  exact MasulloRH.StripTrace.hasSmallErrorKernels φ hφ

end StandaloneStripHighKernelFinal
