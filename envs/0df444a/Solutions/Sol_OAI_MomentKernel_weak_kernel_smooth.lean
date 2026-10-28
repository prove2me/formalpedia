-- Prove2me | solution 1 for OAI.MomentKernel.weak_kernel_smooth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T05:20:19.920663+00:00
-- url     : https://prove2.me/submissions/3b39d7ac-e72a-4084-91dc-948540dc7acf

import Mathlib
import Definitions.Def_OAIW2LB000

section
-- module Solutions.OAIW2_LogBM.LogVolume_BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open scoped Real
namespace LocalPeetre
noncomputable section

lemma rpow_compare {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁ : a ≤ b*c) (h₂ : b ≤ a*c) : a^r ≤ c^|r| * b^r := by
  by_cases hr : 0 ≤ r
  · rw [abs_of_nonneg hr]
    calc
      a^r ≤ (b*c)^r := Real.rpow_le_rpow ha.le h₁ hr
      _ = c^r*b^r := by rw [Real.mul_rpow hb.le hc.le]; ring
  · have ht : 0 ≤ -r := neg_nonneg.mpr (le_of_not_ge hr)
    have hh := Real.rpow_le_rpow hb.le h₂ ht
    rw [Real.mul_rpow ha.le hc.le, Real.rpow_neg ha.le, Real.rpow_neg hb.le] at hh
    rw [abs_of_neg (lt_of_not_ge hr), Real.rpow_neg hc.le]
    have hpa : 0 < a^r := Real.rpow_pos_of_pos ha r
    have hpb : 0 < b^r := Real.rpow_pos_of_pos hb r
    have hpc : 0 < c^r := Real.rpow_pos_of_pos hc r
    rw [Real.rpow_neg hc.le] at hh
    have hprod : a^r*c^r ≤ b^r := by
      exact (inv_le_inv₀ hpb (mul_pos hpa hpc)).mp (by simpa only [mul_inv] using hh)
    rw [mul_comm, ← div_eq_mul_inv]
    exact (le_div_iff₀ hpc).mpr hprod

variable {E : Type*} [SeminormedAddCommGroup E]

lemma quadratic_add (x y : E) : 1+‖x+y‖^2 ≤ 2*(1+‖x‖^2)*(1+‖y‖^2) := by
  have ht := norm_add_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hxy := norm_nonneg (x+y)
  nlinarith [sq_nonneg (‖x‖-‖y‖), mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖y‖)]

lemma weight_pos (s : ℝ) (x : E) : 0 < weight s x := by
  apply Real.rpow_pos_of_pos
  positivity

theorem weight_sub (s : ℝ) (x y : E) :
    weight s x ≤ 2^(|s|/2)*weight |s| y*weight s (x-y) := by
  have h₁ : 1+‖x‖^2 ≤ (1+‖x-y‖^2)*(2*(1+‖y‖^2)) := by
    simpa only [sub_add_cancel, mul_assoc, mul_left_comm] using quadratic_add (x-y) y
  have h₂ : 1+‖x-y‖^2 ≤ (1+‖x‖^2)*(2*(1+‖y‖^2)) := by
    simpa only [← sub_eq_add_neg,norm_neg,mul_assoc,mul_left_comm] using quadratic_add x (-y)
  have hh := rpow_compare (r:=s/2) (by positivity) (by positivity) (by positivity) h₁ h₂
  simpa only [weight, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), Real.mul_rpow (by positivity : (0:ℝ) ≤ 2)
    (by positivity : 0 ≤ 1+‖y‖^2)] using hh

end
end LocalPeetre

open MeasureTheory
open scoped Topology

namespace LocalConvolution
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma integral_mul_le_L2 {c d : X → ℝ} (hc : MemLp c 2 μ) (hd : MemLp d 2 μ) :
    (∫ x, c x * d x ∂μ) ≤ ‖hc.toLp c‖ * ‖hd.toLp d‖ := by
  have he : (∫ x, c x * d x ∂μ) = inner ℝ (hc.toLp c) (hd.toLp d) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hc.coeFn_toLp, hd.coeFn_toLp] with x hx hy
    simp [hx,hy,mul_comm]
  rw [he]
  exact real_inner_le_norm _ _

lemma integral_sq_eq_norm_sq {d : X → ℝ} (hd : MemLp d 2 μ) :
    (∫ x, d x ^ 2 ∂μ) = ‖hd.toLp d‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hd.coeFn_toLp] with x hx
  simp [hx,pow_two]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem norm_le_convolution_majorant {b c d : E → ℝ}
    (hb : Integrable b) (hc₁ : Integrable c) (hc : MemLp c 2 volume)
    (hd : MemLp d 2 volume) (hdcont : Continuous d)
    (hbn : ∀ x, 0 ≤ b x) (hdn : ∀ x, 0 ≤ d x)
    (hdBound : ∃ D, ∀ x, ‖d x‖ ≤ D)
    (hmajor : ∀ x, d x ≤ ∫ y, b y * c (x-y)) :
    ‖hd.toLp d‖ ≤ (∫ y, b y) * ‖hc.toLp c‖ := by
  obtain ⟨D,hD⟩ := hdBound
  have hh₀ : Integrable (fun p : E × E => b p.2 * c (p.1-p.2))
      (volume.prod volume) := hb.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hc₁
  have hh : Integrable (fun p : E × E => d p.1 * (b p.2*c (p.1-p.2)))
      (volume.prod volume) := hh₀.bdd_mul (hdcont.comp continuous_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hD p.1)
  have hcs (y : E) : (∫ x, c (x-y)*d x) ≤ ‖hc.toLp c‖*‖hd.toLp d‖ := by
    have hp : MeasurePreserving (fun x : E => x-y) volume volume := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure E) (-y)
    have ht := hc.comp_measurePreserving hp
    have hn : ‖ht.toLp (c ∘ (fun x : E => x-y))‖ = ‖hc.toLp c‖ :=
      Lp.norm_compMeasurePreserving (hc.toLp c) hp
    simpa only [hn,Function.comp_apply] using integral_mul_le_L2 ht hd
  have hnorm : ‖hd.toLp d‖^2 ≤ ((∫ y, b y)*‖hc.toLp c‖)*‖hd.toLp d‖ := by
    calc
      ‖hd.toLp d‖^2 = ∫ x, d x^2 := (integral_sq_eq_norm_sq hd).symm
      _ ≤ ∫ x, ∫ y, d x * (b y*c (x-y)) := by
        apply integral_mono hd.integrable_sq hh.integral_prod_left
        intro x
        change d x^2 ≤ ∫ y, d x*(b y*c (x-y))
        rw [integral_const_mul]
        simpa only [pow_two] using mul_le_mul_of_nonneg_left (hmajor x) (hdn x)
      _ = ∫ y, ∫ x, d x * (b y*c (x-y)) := integral_integral_swap hh
      _ = ∫ y, b y * (∫ x, c (x-y)*d x) := by
        congr 1
        ext y
        rw [← integral_const_mul]
        congr 1
        ext x
        ring
      _ ≤ ∫ y, b y * (‖hc.toLp c‖*‖hd.toLp d‖) := by
        apply integral_mono ?_ (hb.mul_const _)
        · intro y
          exact mul_le_mul_of_nonneg_left (hcs y) (hbn y)
        · convert hh.integral_prod_right using 1
          ext y
          rw [← integral_const_mul]
          congr 1
          ext x
          ring
      _ = ((∫ y, b y)*‖hc.toLp c‖)*‖hd.toLp d‖ := by rw [integral_mul_const]; ring
  by_cases he : ‖hd.toLp d‖ = 0
  · rw [he]
    exact mul_nonneg (integral_nonneg hbn) (norm_nonneg _)
  · have hp : 0 < ‖hd.toLp d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    nlinarith

end
end LocalConvolution

open MeasureTheory FourierTransform Convolution
open scoped SchwartzMap
namespace LocalFourier
noncomputable section
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

lemma fourierInv_pairing (a : 𝓢(E,ℂ)) (f : 𝓢(E,F)) :
    𝓕⁻ (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) a f) =
    SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) (𝓕⁻ a) (𝓕⁻ f) := by
  simp [SchwartzMap.convolution]

omit [CompleteSpace F] in
lemma fourierInv_apply (f : 𝓢(E,F)) (x : E) : (𝓕⁻ f) x = (𝓕 f) (-x) := rfl

lemma fourier_pairing_apply (a : 𝓢(E,ℂ)) (f : 𝓢(E,F)) (x : E) :
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) a f) x =
    ∫ y, (𝓕 a) y • (𝓕 f) (x-y) := by
  have he := congrArg (fun (g : 𝓢(E,F)) => g (-x)) (fourierInv_pairing a f)
  rw [fourierInv_apply, neg_neg, SchwartzMap.convolution_apply] at he
  change _ = ∫ y, ((𝓕⁻ a) y) • ((𝓕⁻ f) (-x-y)) at he
  rw [he]
  simp only [fourierInv_apply, neg_sub]
  convert integral_neg_eq_self (fun y : E => (𝓕 a) y • (𝓕 f) (x-y)) volume using 1
  congr 1
  ext y
  congr 1
  congr 1
  abel

end
end LocalFourier

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology

noncomputable section
namespace SobolevModel
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma embedding_injective (s : ℝ) : Function.Injective (embedding E F s) := by
  intro f g h
  have hh := congrArg (besselPotential E F s) h
  simp only [embedding, ContinuousLinearMap.comp_apply,
    besselPotential_besselPotential_apply, neg_add_cancel, besselPotential_zero,
    ContinuousLinearMap.id_apply] at hh
  exact LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F:=F) (μ:=volume)) hh

lemma embedding_memSobolev (s : ℝ) (f : Model E F) :
    MemSobolev s 2 (embedding E F s f) := by
  refine ⟨f, ?_⟩
  simp [embedding]

lemma memSobolev_iff_range (s : ℝ) (u : 𝓢'(E,F)) :
    MemSobolev s 2 u ↔ u ∈ Set.range (embedding E F s) := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f, ?_⟩
    change besselPotential E F (-s) (f : 𝓢'(E,F)) = u
    rw [← hf, besselPotential_besselPotential_apply]
    simp
  · rintro ⟨f,rfl⟩
    exact embedding_memSobolev s f

lemma schwartzBessel_add (s t : ℝ) (f : 𝓢(E,F)) :
    schwartzBessel E F s (schwartzBessel E F t f) = schwartzBessel E F (s+t) f := by
  rw [schwartzBessel, schwartzBessel,
    SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr 2
  ext x
  simp only [Pi.mul_apply, ← Complex.ofReal_mul]
  rw [← Real.rpow_add (by positivity)]
  congr 2
  ring

lemma schwartzBessel_surjective (s : ℝ) : Function.Surjective (schwartzBessel E F s) := by
  intro f
  exact ⟨schwartzBessel E F (-s) f, by rw [schwartzBessel_add]; simp⟩

lemma schwartzBessel_distribution (s : ℝ) (f : 𝓢(E,F)) :
    (schwartzBessel E F s f : 𝓢'(E,F)) = besselPotential E F s (f : 𝓢'(E,F)) := by
  exact (TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq
    (by fun_prop) f).symm

@[simp] lemma embedding_coordinate (s : ℝ) (f : 𝓢(E,F)) :
    embedding E F s (coordinate E F s f) = (f : 𝓢'(E,F)) := by
  change besselPotential E F (-s)
    (((schwartzBessel E F s f).toLp 2 volume) : 𝓢'(E,F)) = _
  rw [Lp.toTemperedDistribution_toLp_eq, schwartzBessel_distribution,
    besselPotential_besselPotential_apply]
  simp

lemma denseRange_coordinate (s : ℝ) : DenseRange (coordinate E F s) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℂ F 2 (volume : Measure E)) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  exact hd.comp (schwartzBessel_surjective s).denseRange (SchwartzMap.toLpCLM ℂ F 2 volume).continuous

theorem lift_operator {s t C : ℝ} (hC : 0 ≤ C)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F)) (Q : 𝓢(E,F) →L[ℂ] 𝓢(E,F))
    (hcompat : ∀ f : 𝓢(E,F), P (f : 𝓢'(E,F)) = (Q f : 𝓢'(E,F)))
    (hbound : ∀ f, ‖coordinate E F t (Q f)‖ ≤ C * ‖coordinate E F s f‖) :
    ∃ R : Model E F →L[ℂ] Model E F, ‖R‖ ≤ C ∧
      ∀ f, embedding E F t (R f) = P (embedding E F s f) := by
  let e := (coordinate E F s).toLinearMap
  let q := ((coordinate E F t).comp Q).toLinearMap
  have hd : DenseRange e := denseRange_coordinate s
  let R := q.extendOfNorm e
  refine ⟨R, LinearMap.opNorm_extendOfNorm_le hd hC hbound, ?_⟩
  intro f
  refine hd.induction_on f (isClosed_eq ((embedding E F t).continuous.comp R.continuous)
    (P.continuous.comp (embedding E F s).continuous)) ?_
  intro g
  change embedding E F t (q.extendOfNorm e (e g)) = P (embedding E F s (e g))
  rw [LinearMap.extendOfNorm_eq hd ⟨C,hbound⟩]
  change embedding E F t (coordinate E F t (Q g)) =
    P (embedding E F s (coordinate E F s g))
  rw [embedding_coordinate, embedding_coordinate, hcompat]

end SobolevModel

namespace LocalSobolev
section
open MeasureTheory FourierTransform
open scoped SchwartzMap
open LocalPeetre
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weight_growth (s : ℝ) : (fun x : E => Complex.ofReal (weight s x)).HasTemperateGrowth := by
  unfold weight
  fun_prop

omit [CompleteSpace F] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weighted_apply (s : ℝ) (f : 𝓢(E,F)) (x : E) :
    weighted s f x = (Complex.ofReal (weight s x)) • f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (weight_growth s) f x

omit [CompleteSpace F] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_weighted (s : ℝ) (f : 𝓢(E,F)) (x : E) :
    ‖weighted s f x‖ = weight s x * ‖f x‖ := by
  rw [weighted_apply,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (weight_pos s x)]

lemma norm_coordinate (s : ℝ) (f : 𝓢(E,F)) :
    ‖SobolevModel.coordinate E F s f‖ = ‖(weighted s (𝓕 f)).toLp 2‖ := by
  simp only [SobolevModel.coordinate, ContinuousLinearMap.comp_apply,
    SchwartzMap.toLpCLM_apply]
  rw [← SchwartzMap.norm_fourier_toL2_eq (SobolevModel.schwartzBessel E F s f)]
  simp only [SobolevModel.schwartzBessel, SchwartzMap.fourierMultiplierCLM_apply,
    fourier_fourierInv_eq]
  rfl

omit [CompleteSpace F] in
lemma integrable_norm_product (a : 𝓢(E,ℂ)) (f : 𝓢(E,F)) (x : E) :
    Integrable (fun y => ‖a y‖ * ‖f (x-y)‖) := by
  apply a.integrable.norm.mul_bdd
    ((f.continuous.comp (continuous_const.sub continuous_id)).norm.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun y => by simpa using f.norm_le_seminorm ℂ (x-y)

lemma weighted_fourier_majorant (s : ℝ) (a : 𝓢(E,ℂ)) (f : 𝓢(E,F)) (x : E) :
    ‖weighted s (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) a f)) x‖ ≤
      ∫ y, (2^(|s|/2) * ‖weighted |s| (𝓕 a) y‖) * ‖weighted s (𝓕 f) (x-y)‖ := by
  rw [norm_weighted,LocalFourier.fourier_pairing_apply]
  calc
    weight s x * ‖∫ y, (𝓕 a) y • (𝓕 f) (x-y)‖ ≤
        weight s x * (∫ y, ‖(𝓕 a) y‖ * ‖(𝓕 f) (x-y)‖) := by
      apply mul_le_mul_of_nonneg_left _ (weight_pos s x).le
      calc
        _ ≤ ∫ y, ‖(𝓕 a) y • (𝓕 f) (x-y)‖ := norm_integral_le_integral_norm _
        _ = _ := by
          congr 1
          ext y
          exact norm_smul ((𝓕 a) y) ((𝓕 f) (x-y))
    _ = ∫ y, weight s x * (‖(𝓕 a) y‖ * ‖(𝓕 f) (x-y)‖) :=
      (integral_const_mul _ _).symm
    _ ≤ _ := by
      apply integral_mono ((integrable_norm_product (𝓕 a) (𝓕 f) x).const_mul _)
        (by
          convert (integrable_norm_product (weighted |s| (𝓕 a)) (weighted s (𝓕 f)) x).const_mul
            (2^(|s|/2)) using 1
          simp only [mul_assoc])
      intro y
      dsimp only
      rw [norm_weighted,norm_weighted]
      nlinarith [mul_le_mul_of_nonneg_right (weight_sub s x y)
        (mul_nonneg (norm_nonneg ((𝓕 a) y)) (norm_nonneg ((𝓕 f) (x-y))))]

omit [CompleteSpace F] in
lemma toLp_norm_norm (f : 𝓢(E,F)) :
    ‖(f.memLp 2 volume).norm.toLp (fun x => ‖f x‖)‖ = ‖f.toLp 2‖ := by
  rw [Lp.norm_toLp,eLpNorm_norm f,SchwartzMap.norm_toLp]

theorem multiplication_bound (s : ℝ) (a : 𝓢(E,ℂ)) (f : 𝓢(E,F)) :
    ‖SobolevModel.coordinate E F s
      (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) a f)‖ ≤
      (2^(|s|/2) * ‖(weighted |s| (𝓕 a)).toLp 1‖) *
        ‖SobolevModel.coordinate E F s f‖ := by
  let d := weighted s (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) a f))
  let c := weighted s (𝓕 f)
  let b := weighted |s| (𝓕 a)
  have hb : Integrable (fun y => 2^(|s|/2) * ‖b y‖) := b.integrable.norm.const_mul _
  have hh := LocalConvolution.norm_le_convolution_majorant hb c.integrable.norm
    (c.memLp 2 volume).norm (d.memLp 2 volume).norm d.continuous.norm
    (fun y => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (norm_nonneg _))
    (fun y => norm_nonneg (d y))
    ⟨SchwartzMap.seminorm ℂ 0 0 d, fun y => by simpa using d.norm_le_seminorm ℂ y⟩
    (weighted_fourier_majorant s a f)
  rw [toLp_norm_norm,toLp_norm_norm,integral_const_mul,← SchwartzMap.norm_toLp_one] at hh
  simpa only [norm_coordinate,d,c,b] using hh

omit [CompleteSpace F] in
lemma multiplication_distribution (a : 𝓢(E,ℂ)) (f : 𝓢(E,F)) :
    TemperedDistribution.smulLeftCLM F a (f : 𝓢'(E,F)) =
      (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) a f : 𝓢'(E,F)) := by
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply, SchwartzMap.coe_apply,
    SchwartzMap.coe_apply]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [SchwartzMap.smulLeftCLM_apply_apply a.hasTemperateGrowth,
    SchwartzMap.pairing_apply_apply]
  simpa only [smul_smul, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
    smul_comm (a x) (φ x) (f x)

theorem multiplication_lift (s : ℝ) (a : 𝓢(E,ℂ)) :
    ∃ R : SobolevModel.Model E F →L[ℂ] SobolevModel.Model E F,
      ‖R‖ ≤ 2^(|s|/2) * ‖(weighted |s| (𝓕 a)).toLp 1‖ ∧
      ∀ f, SobolevModel.embedding E F s (R f) =
        TemperedDistribution.smulLeftCLM F a (SobolevModel.embedding E F s f) := by
  exact SobolevModel.lift_operator (by positivity)
    (TemperedDistribution.smulLeftCLM F a)
    (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) a)
    (multiplication_distribution a) (multiplication_bound s a)

lemma continuous_multiplier_gauge (s : ℝ) :
    Continuous (fun a : 𝓢(E,ℂ) => 2^(|s|/2) * ‖(weighted |s| (𝓕 a)).toLp 1‖) := by
  exact continuous_const.mul (((SchwartzMap.toLpCLM ℂ ℂ 1 volume).continuous.comp
    ((weighted |s|).continuous.comp (fourierCLM ℂ (𝓢(E,ℂ))).continuous)).norm)

end

open MeasureTheory FourierTransform LocalPeetre
open scoped SchwartzMap
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma weight_add (s t : ℝ) (x : E) : weight (s+t) x = weight s x * weight t x := by
  unfold weight
  rw [show (s+t)/2=s/2+t/2 by ring, Real.rpow_add (by positivity)]

lemma fourier_multiplier_bound {s t C : ℝ} {p : E → ℂ}
    (hp : p.HasTemperateGrowth) (hb : ∀ x, weight (t-s) x * ‖p x‖ ≤ C)
    (f : 𝓢(E,F)) :
    ‖SobolevModel.coordinate E F t (SchwartzMap.fourierMultiplierCLM F p f)‖ ≤
      C * ‖SobolevModel.coordinate E F s f‖ := by
  rw [norm_coordinate, norm_coordinate]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [SchwartzMap.coeFn_toLp (weighted t (𝓕 (SchwartzMap.fourierMultiplierCLM F p f))) (p:=2) (μ:=volume),
    SchwartzMap.coeFn_toLp (weighted s (𝓕 f)) (p:=2) (μ:=volume)] with x hx hy
  rw [hx,hy,norm_weighted,norm_weighted,SchwartzMap.fourierMultiplierCLM_apply,
    fourier_fourierInv_eq,SchwartzMap.smulLeftCLM_apply_apply hp,norm_smul]
  have ht : weight t x = weight (t-s) x * weight s x := by
    rw [← weight_add]; congr 1; ring
  rw [ht]
  nlinarith [mul_le_mul_of_nonneg_right (hb x)
    (mul_nonneg (weight_pos s x).le (norm_nonneg ((𝓕 f) x)))]

theorem fourier_multiplier_lift {s t C : ℝ} (hC : 0 ≤ C) {p : E → ℂ}
    (hp : p.HasTemperateGrowth) (hb : ∀ x, weight (t-s) x * ‖p x‖ ≤ C) :
    ∃ R : SobolevModel.Model E F →L[ℂ] SobolevModel.Model E F, ‖R‖ ≤ C ∧
      ∀ f, SobolevModel.embedding E F t (R f) =
        TemperedDistribution.fourierMultiplierCLM F p (SobolevModel.embedding E F s f) := by
  exact SobolevModel.lift_operator hC (TemperedDistribution.fourierMultiplierCLM F p)
    (SchwartzMap.fourierMultiplierCLM F p)
    (fun f => TemperedDistribution.fourierMultiplierCLM_toTemperedDistributionCLM_eq hp f)
    (fourier_multiplier_bound hp hb)

end LocalSobolev

namespace SobolevModel
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma kernel_eq_zero_of_small (s : ℝ) (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (R : Model E F →L[ℂ] Model E F) (hR : ‖R‖ < 1)
    (compat : ∀ v, embedding E F s (R v) = P (embedding E F s v))
    {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (heq : u-P u=0) : u=0 := by
  obtain ⟨v,rfl⟩ := (memSobolev_iff_range s u).mp hu
  have he : (1-R) v = 0 := by
    apply embedding_injective s
    simp only [map_zero, sub_apply, one_apply_eq_self,
      map_sub,compat,heq]
  have hi : Function.Injective ((1-R) : Model E F →L[ℂ] Model E F) :=
    (ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_of_norm_lt_one hR)).1
  have hv : v=0 := hi (by simpa using he)
  simp [hv]

theorem regularity_of_small_perturbation {s t : ℝ} (hst : s ≤ t)
    (P : 𝓢'(E,F) →L[ℂ] 𝓢'(E,F))
    (Rs Rt : Model E F →L[ℂ] Model E F) (hs : ‖Rs‖ < 1) (ht : ‖Rt‖ < 1)
    (cs : ∀ v, embedding E F s (Rs v) = P (embedding E F s v))
    (ct : ∀ v, embedding E F t (Rt v) = P (embedding E F t v))
    {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (hPu : MemSobolev t 2 (u-P u)) :
    MemSobolev t 2 u := by
  obtain ⟨w, hw⟩ := (memSobolev_iff_range t (u-P u)).mp hPu
  obtain ⟨v,hv⟩ := (ContinuousLinearMap.isUnit_iff_bijective.mp
    (isUnit_one_sub_of_norm_lt_one ht)).2 w
  have he : embedding E F t v - P (embedding E F t v) = u-P u := by
    rw [← ct, ← map_sub]
    exact (congrArg (embedding E F t) hv).trans hw
  have hmem := (embedding_memSobolev t v).mono hst
  have hzero : u-embedding E F t v=0 := by
    apply kernel_eq_zero_of_small s P Rs hs cs (hu.sub hmem)
    rw [map_sub]
    calc
      _ = (u-P u) - (embedding E F t v-P (embedding E F t v)) := by abel
      _ = 0 := sub_eq_zero.mpr he.symm
  rw [sub_eq_zero] at hzero
  rw [hzero]
  exact embedding_memSobolev t v

end SobolevModel

namespace LocalParametrix
open MeasureTheory FourierTransform TemperedDistribution LocalPeetre LocalSobolev
open scoped SchwartzMap BigOperators
variable {E : Type*} {F : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

lemma coefficientGauge_nonneg (s : ℝ) (a : 𝓢(E,ℂ)) : 0 ≤ coefficientGauge s a := by
  unfold coefficientGauge
  positivity

lemma continuous_coefficientGauge (s : ℝ) : Continuous (coefficientGauge (E:=E) s) :=
  continuous_multiplier_gauge s

theorem perturbation_lift (s m Cq : ℝ) (Cp : ι → ℝ) (hCq : 0 ≤ Cq)
    (hCp : ∀ i, 0 ≤ Cp i) {q : E → ℂ} (hq : q.HasTemperateGrowth)
    (hbq : ∀ x, weight m x * ‖q x‖ ≤ Cq)
    {p : ι → E → ℂ} (hp : ∀ i, (p i).HasTemperateGrowth)
    (hbp : ∀ i x, weight (-m) x * ‖p i x‖ ≤ Cp i) (a : ι → 𝓢(E,ℂ)) :
    ∃ R : SobolevModel.Model E F →L[ℂ] SobolevModel.Model E F,
      ‖R‖ ≤ Cq * ∑ i, coefficientGauge (s-m) (a i) * Cp i ∧
      ∀ f, SobolevModel.embedding E F s (R f) =
        perturbation (F:=F) q p a (SobolevModel.embedding E F s f) := by
  obtain ⟨Q,hQ,cQ⟩ := fourier_multiplier_lift (s:=s-m) (t:=s) (F:=F) hCq hq
    (by convert hbq using 1; ring_nf)
  have hD : ∀ i, ∃ D : SobolevModel.Model E F →L[ℂ] SobolevModel.Model E F,
      ‖D‖ ≤ Cp i ∧ ∀ f, SobolevModel.embedding E F (s-m) (D f) =
        TemperedDistribution.fourierMultiplierCLM F (p i) (SobolevModel.embedding E F s f) := by
    intro i
    apply fourier_multiplier_lift (hCp i) (hp i)
    convert hbp i using 1; ring_nf
  choose D hD cD using hD
  have hA : ∀ i, ∃ A : SobolevModel.Model E F →L[ℂ] SobolevModel.Model E F,
      ‖A‖ ≤ coefficientGauge (s-m) (a i) ∧
      ∀ f, SobolevModel.embedding E F (s-m) (A f) =
        TemperedDistribution.smulLeftCLM F (a i) (SobolevModel.embedding E F (s-m) f) :=
    fun i => multiplication_lift (s-m) (a i)
  choose A hA cA using hA
  refine ⟨Q.comp (∑ i, (A i).comp (D i)), ?_, ?_⟩
  · calc
      _ ≤ ‖Q‖ * ‖∑ i, (A i).comp (D i)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ Cq * ∑ i, coefficientGauge (s-m) (a i) * Cp i := by
        apply mul_le_mul hQ _ (norm_nonneg _) hCq
        calc
          _ ≤ ∑ i, ‖(A i).comp (D i)‖ := norm_sum_le _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul (hA i) (hD i) (norm_nonneg _) (coefficientGauge_nonneg _ _))
  · intro f
    simp only [ContinuousLinearMap.comp_apply, cQ, map_sum,
      sum_apply, cA, cD, perturbation]

theorem gain_of_small_principal {s t m Cq : ℝ} (hst : s ≤ t) (Cp : ι → ℝ)
    (hCq : 0 ≤ Cq) (hCp : ∀ i, 0 ≤ Cp i) {q : E → ℂ} (hq : q.HasTemperateGrowth)
    (hbq : ∀ x, weight m x * ‖q x‖ ≤ Cq)
    {p : ι → E → ℂ} (hp : ∀ i, (p i).HasTemperateGrowth)
    (hbp : ∀ i x, weight (-m) x * ‖p i x‖ ≤ Cp i) (a : ι → 𝓢(E,ℂ))
    (hs : Cq * ∑ i, coefficientGauge (s-m) (a i) * Cp i < 1)
    (ht : Cq * ∑ i, coefficientGauge (t-m) (a i) * Cp i < 1)
    {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u)
    (hf : MemSobolev t 2 (u - perturbation (F:=F) q p a u)) : MemSobolev t 2 u := by
  obtain ⟨Rs,hRs,cRs⟩ := perturbation_lift (F:=F) s m Cq Cp hCq hCp hq hbq hp hbp a
  obtain ⟨Rt,hRt,cRt⟩ := perturbation_lift (F:=F) t m Cq Cp hCq hCp hq hbq hp hbp a
  exact SobolevModel.regularity_of_small_perturbation hst _ Rs Rt
    (hRs.trans_lt hs) (hRt.trans_lt ht) cRs cRt hu hf

theorem eventually_small_coefficients {α : Type*} {l : Filter α}
    {a : α → ι → 𝓢(E,ℂ)} (ha : ∀ i, Filter.Tendsto (fun r => a r i) l (nhds 0))
    (s t m Cq : ℝ) (Cp : ι → ℝ) :
    ∀ᶠ r in l,
      Cq * ∑ i, coefficientGauge (s-m) (a r i) * Cp i < 1 ∧
      Cq * ∑ i, coefficientGauge (t-m) (a r i) * Cp i < 1 := by
  have hbound : ∀ z : ℝ, Filter.Tendsto
      (fun r => Cq * ∑ i, coefficientGauge (z-m) (a r i) * Cp i) l (nhds 0) := by
    intro z
    have hi : ∀ i, Filter.Tendsto (fun r => coefficientGauge (z-m) (a r i) * Cp i)
        l (nhds (0:ℝ)) := by
      intro i
      simpa using (((continuous_coefficientGauge (z-m)).continuousAt.tendsto.comp
        (ha i)).mul_const (Cp i))
    simpa using (Filter.Tendsto.const_mul Cq (tendsto_finsetSum Finset.univ (fun i _ => hi i)))
  exact ((hbound s).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).and
    ((hbound t).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)))

end LocalParametrix
end

open MeasureTheory TemperedDistribution FourierTransform LineDeriv
open scoped SchwartzMap ContDiff
noncomputable section
namespace LocalDifferential
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma schwartz_product_derivative (v : E) (a b : 𝓢(E,ℂ)) :
    ∂_{v} (product a b) = product (∂_{v} a) b + product a (∂_{v} b) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have heq : (product a b : E → ℂ) = (fun y => a y * b y) := funext (product_apply a b)
  rw [heq]
  rw [fderiv_fun_mul a.differentiableAt b.differentiableAt]
  simp [product_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm, add_comm]

theorem derivative_multiply (v : E) (a : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    ∂_{v} (TemperedDistribution.smulLeftCLM F a u) =
      TemperedDistribution.smulLeftCLM F (∂_{v} a : 𝓢(E,ℂ)) u +
      TemperedDistribution.smulLeftCLM F a (∂_{v} u) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, add_apply, map_neg]
  change -u (product a (∂_{v} φ)) =
    u (product (∂_{v} a) φ) + -u (∂_{v} (product a φ))
  rw [schwartz_product_derivative, map_add]
  abel

variable [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]

theorem derivative_sobolev {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (vs : List E) :
    MemSobolev (s-(vs.length:ℝ)) 2 (derivative vs u) := by
  induction vs with
  | nil => simpa using hu
  | cons v vs ih =>
      simpa only [derivative_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
        sub_add_eq_sub_sub] using (ih.lineDerivOp (m:=v))

end LocalDifferential

namespace LocalBootstrap
open MeasureTheory TemperedDistribution FourierTransform LineDeriv LocalSobolev LocalDifferential
open scoped SchwartzMap BigOperators
variable {E : Type*} {F : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem multiply_sobolev {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (a : 𝓢(E,ℂ)) :
    MemSobolev s 2 (TemperedDistribution.smulLeftCLM F a u) := by
  obtain ⟨f,rfl⟩ := (SobolevModel.memSobolev_iff_range s u).mp hu
  obtain ⟨R,_,hR⟩ := multiplication_lift (F:=F) s a
  rw [←hR f]
  exact SobolevModel.embedding_memSobolev s (R f)

theorem commutator_sobolev {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u)
    (a : 𝓢(E,ℂ)) (vs : List E) :
    MemSobolev (s-(vs.length:ℝ)+1) 2
      (derivative vs (TemperedDistribution.smulLeftCLM F a u) -
        TemperedDistribution.smulLeftCLM F a (derivative vs u)) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      have heq : derivative (v::vs) (TemperedDistribution.smulLeftCLM F a u) -
          TemperedDistribution.smulLeftCLM F a (derivative (v::vs) u) =
          ∂_{v} (derivative vs (TemperedDistribution.smulLeftCLM F a u) -
            TemperedDistribution.smulLeftCLM F a (derivative vs u)) +
          TemperedDistribution.smulLeftCLM F (∂_{v} a : 𝓢(E,ℂ)) (derivative vs u) := by
        simp only [derivative_cons]
        change _ = (lineDerivOpCLM ℂ 𝓢'(E,F) v) (_ - _) + _
        rw [map_sub]
        change _ = ∂_{v} (derivative vs (TemperedDistribution.smulLeftCLM F a u)) -
          ∂_{v} (TemperedDistribution.smulLeftCLM F a (derivative vs u)) + _
        rw [derivative_multiply]
        abel
      rw [heq]
      have h1 : MemSobolev (s-(vs.length:ℝ)) 2
          (∂_{v} (derivative vs (TemperedDistribution.smulLeftCLM F a u) -
            TemperedDistribution.smulLeftCLM F a (derivative vs u))) := by
        convert ih.lineDerivOp (m:=v) using 1
        ring
      have h2 := multiply_sobolev (derivative_sobolev hu vs) (∂_{v} a)
      convert h1.add h2 using 1
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

lemma sobolev_finset_sum {s : ℝ} (I : Finset ι) (u : ι → 𝓢'(E,F))
    (hu : ∀ i ∈ I, MemSobolev s 2 (u i)) : MemSobolev s 2 (∑ i ∈ I, u i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hu i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj)))

theorem lower_order_sobolev [Fintype ι] {s : ℝ} {m : ℕ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (a : ι → 𝓢(E,ℂ)) (vs : ι → List E)
    (horder : ∀ i, (vs i).length < m) :
    MemSobolev (s-(m:ℝ)+1) 2
      (∑ i, TemperedDistribution.smulLeftCLM F (a i) (derivative (vs i) u)) := by
  apply sobolev_finset_sum
  intro i hi
  apply (multiply_sobolev (derivative_sobolev hu (vs i)) (a i)).mono
  have hh : ((vs i).length:ℝ)+1 ≤ (m:ℝ) := by exact_mod_cast horder i
  linarith

theorem gain_from_frozen_equation [Fintype ι] {s m Cq : ℝ}
    (Cp : ι → ℝ) (hCq : 0 ≤ Cq) (hCp : ∀ i, 0 ≤ Cp i)
    {q p₀ : E → ℂ} (hq : q.HasTemperateGrowth) (hp₀ : p₀.HasTemperateGrowth)
    (hinv : ∀ x, p₀ x * q x = 1)
    (hbq : ∀ x, LocalPeetre.weight m x * ‖q x‖ ≤ Cq)
    {p : ι → E → ℂ} (hp : ∀ i, (p i).HasTemperateGrowth)
    (hbp : ∀ i x, LocalPeetre.weight (-m) x * ‖p i x‖ ≤ Cp i)
    (a : ι → 𝓢(E,ℂ))
    (hs : Cq * ∑ i, LocalParametrix.coefficientGauge (s-m) (a i) * Cp i < 1)
    (ht : Cq * ∑ i, LocalParametrix.coefficientGauge (s+1-m) (a i) * Cp i < 1)
    {u f : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (hf : MemSobolev (s-m+1) 2 f)
    (heq : TemperedDistribution.fourierMultiplierCLM F p₀ u -
      ∑ i, TemperedDistribution.smulLeftCLM F (a i)
        (TemperedDistribution.fourierMultiplierCLM F (p i) u) = f) :
    MemSobolev (s+1) 2 u := by
  apply LocalParametrix.gain_of_small_principal (by linarith) Cp hCq hCp hq hbq hp hbp a hs ht hu
  obtain ⟨Q,_,hQ⟩ := fourier_multiplier_lift (s:=s-m+1) (t:=s+1) (F:=F) hCq hq
    (by convert hbq using 1; ring_nf)
  obtain ⟨v,hv⟩ := (SobolevModel.memSobolev_iff_range (s-m+1) f).mp hf
  have hreg : MemSobolev (s+1) 2 (TemperedDistribution.fourierMultiplierCLM F q f) := by
    rw [←hv, ←hQ]
    exact SobolevModel.embedding_memSobolev (s+1) (Q v)
  have he := congrArg (TemperedDistribution.fourierMultiplierCLM F q) heq
  rw [map_sub, TemperedDistribution.fourierMultiplierCLM_fourierMultiplierCLM_apply hp₀ hq] at he
  have hpq : p₀*q = 1 := by ext x; exact hinv x
  rw [hpq] at he
  have hone : TemperedDistribution.fourierMultiplierCLM F (1 : E → ℂ) u = u := by
    change TemperedDistribution.fourierMultiplierCLM F (fun _ => 1) u = u
    simp
  rw [hone] at he
  have he' : u - LocalParametrix.perturbation (F:=F) q p a u =
      TemperedDistribution.fourierMultiplierCLM F q f := by
    simpa only [LocalParametrix.perturbation, ContinuousLinearMap.comp_apply, sum_apply] using he
  rw [he']
  exact hreg

end LocalBootstrap

namespace LocalDifferential
open MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap Real
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

omit [InnerProductSpace ℝ E] in
lemma symbolConstant_nonneg (vs : List E) : 0 ≤ symbolConstant vs := by
  induction vs with
  | nil => norm_num [symbolConstant]
  | cons v vs ih => exact mul_nonneg ih (by positivity)

lemma symbol_growth (vs : List E) : (symbol vs).HasTemperateGrowth := by
  induction vs with
  | nil => exact Function.HasTemperateGrowth.const _
  | cons v vs ih =>
    exact ih.mul (by fun_prop)

omit [InnerProductSpace ℝ E] in
lemma norm_le_weight_one (x : E) : ‖x‖ ≤ (1+‖x‖^2)^((1:ℝ)/2) := by
  rw [←Real.sqrt_eq_rpow]
  apply (Real.le_sqrt (norm_nonneg x) (by positivity)).mpr
  nlinarith

lemma symbol_bound (vs : List E) (x : E) :
    ‖symbol vs x‖ ≤ symbolConstant vs * (1+‖x‖^2)^((vs.length:ℝ)/2) := by
  induction vs with
  | nil => simp [symbol, symbolConstant]
  | cons v vs ih =>
    have h1 : ‖Complex.ofReal (inner ℝ x v)‖ ≤ (1+‖x‖^2)^((1:ℝ)/2) * ‖v‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_real_inner_le_norm x v).trans (mul_le_mul_of_nonneg_right (norm_le_weight_one x) (norm_nonneg v))
    calc
      ‖symbol (v::vs) x‖ = ‖symbol vs x‖ * (‖(2 * Real.pi * Complex.I : ℂ)‖ * ‖Complex.ofReal (inner ℝ x v)‖) := by simp only [symbol, norm_mul]
      _ ≤ (symbolConstant vs * (1+‖x‖^2)^((vs.length:ℝ)/2)) *
        (‖(2 * Real.pi * Complex.I : ℂ)‖ * ((1+‖x‖^2)^((1:ℝ)/2) * ‖v‖)) := by
          gcongr
          exact mul_nonneg (symbolConstant_nonneg vs) (by positivity)
      _ = symbolConstant (v::vs) * (1+‖x‖^2)^(((v::vs).length:ℝ)/2) := by
        simp only [symbolConstant, List.length_cons, Nat.cast_add, Nat.cast_one, add_div,
          Real.rpow_add (by positivity : 0 < 1+‖x‖^2)]
        ring

lemma weighted_symbol_bound (vs : List E) (x : E) :
    (1+‖x‖^2)^(-(vs.length:ℝ)/2) * ‖symbol vs x‖ ≤ symbolConstant vs := by
  calc
    _ ≤ (1+‖x‖^2)^(-(vs.length:ℝ)/2) *
      (symbolConstant vs * (1+‖x‖^2)^((vs.length:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left (symbol_bound vs x) (by positivity)
    _ = symbolConstant vs := by
      rw [neg_div, Real.rpow_neg (by positivity : 0 ≤ 1+‖x‖^2)]
      field_simp

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma derivative_fourier (vs : List E) (u : 𝓢'(E,F)) :
    derivative vs u = fourierMultiplierCLM F (symbol vs) u := by
  induction vs with
  | nil => simp [symbol]
  | cons v vs ih =>
    rw [derivative_cons, ih, lineDeriv_eq_fourierMultiplierCLM]
    rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (symbol_growth vs) (by fun_prop)]
    rw [←smul_apply, ←fourierMultiplierCLM_smul ((symbol_growth vs).mul (by fun_prop))]
    congr 2
    ext x
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, symbol]
    ring

end LocalDifferential

namespace LocalSupport
open MeasureTheory TemperedDistribution LineDeriv Filter
open scoped SchwartzMap Topology
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma supported_multiply (χ : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    SupportedIn (smulLeftCLM F χ u) (tsupport χ) := by
  intro φ hφ
  rw [smulLeftCLM_apply_apply]
  have hz : SchwartzMap.smulLeftCLM ℂ χ φ = 0 := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
    by_cases hx : χ x = 0
    · simp [hx]
    · have hpx := (hφ x (subset_tsupport χ (Function.mem_support.mpr hx))).self_of_nhds
      simp [hpx]
  rw [hz, map_zero]

lemma SupportedIn.lineDeriv {u : 𝓢'(E,F)} {K : Set E} (hu : SupportedIn u K) (v : E) :
    SupportedIn (∂_{v} u) K := by
  intro φ hφ
  rw [TemperedDistribution.lineDerivOp_apply_apply]
  rw [map_neg, hu (∂_{v} φ) ?_, neg_zero]
  intro x hx
  have he := (hφ x hx).fderiv (𝕜:=ℝ)
  filter_upwards [he] with y hy
  simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_zero, Pi.zero_apply, zero_apply]
    using congrArg (fun A : E →L[ℝ] ℂ => A v) hy

lemma SupportedIn.derivative {u : 𝓢'(E,F)} {K : Set E} (hu : SupportedIn u K) (vs : List E) :
    SupportedIn (LocalDifferential.derivative vs u) K := by
  induction vs with
  | nil => exact hu
  | cons v vs ih => exact ih.lineDeriv v

lemma SupportedIn.multiply_congr {u : 𝓢'(E,F)} {K : Set E} (hu : SupportedIn u K)
    {a b : E → ℂ} (ha : a.HasTemperateGrowth) (hb : b.HasTemperateGrowth)
    (hab : ∀ x ∈ K, a =ᶠ[𝓝 x] b) : smulLeftCLM F a u = smulLeftCLM F b u := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ a φ) = u (SchwartzMap.smulLeftCLM ℂ b φ)
  apply sub_eq_zero.mp
  rw [←map_sub]
  apply hu
  intro x hx
  filter_upwards [hab x hx] with y hy
  simp only [sub_apply, SchwartzMap.smulLeftCLM_apply_apply ha,
    SchwartzMap.smulLeftCLM_apply_apply hb, hy, sub_self, Pi.zero_apply]

lemma SupportedIn.cutoff_identity {u : 𝓢'(E,F)} {K : Set E} (hu : SupportedIn u K)
    (η : 𝓢(E,ℂ)) (hη : ∀ x ∈ K, (η : E → ℂ) =ᶠ[𝓝 x] 1) :
    smulLeftCLM F η u = u := by
  have he := hu.multiply_congr η.hasTemperateGrowth (Function.HasTemperateGrowth.const (1:ℂ)) hη
  simpa using he

end LocalSupport

namespace LocalOperator
open MeasureTheory TemperedDistribution FourierTransform LocalDifferential LocalBootstrap LocalSupport
open scoped SchwartzMap BigOperators
variable {E : Type*} {F : Type*} {ι : Type*} {κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]

lemma operator_apply (a : ι → 𝓢(E,ℂ)) (vs : ι → List E) (u : 𝓢'(E,F)) :
    operator a vs u = ∑ i, smulLeftCLM F (a i) (derivative (vs i) u) := by
  simp only [operator, sum_apply, ContinuousLinearMap.comp_apply]

lemma multiply_comm (a b : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    smulLeftCLM F a (smulLeftCLM F b u) = smulLeftCLM F b (smulLeftCLM F a u) := by
  rw [smulLeftCLM_smulLeftCLM_apply b.hasTemperateGrowth a.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply a.hasTemperateGrowth b.hasTemperateGrowth, mul_comm]

lemma operator_cutoff (a : ι → 𝓢(E,ℂ)) (vs : ι → List E) (χ : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    operator a vs (smulLeftCLM F χ u) =
      smulLeftCLM F χ (operator a vs u) +
        ∑ i, smulLeftCLM F (a i) (derivative (vs i) (smulLeftCLM F χ u) -
          smulLeftCLM F χ (derivative (vs i) u)) := by
  simp only [operator_apply, map_sum, map_sub]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [multiply_comm χ (a i)]
  abel

omit [Fintype ι] in
lemma perturb_on_cutoff (c : ι → ℂ) (η χ : 𝓢(E,ℂ)) (a : ι → 𝓢(E,ℂ))
    (hη : ∀ x ∈ tsupport χ, (η : E → ℂ) =ᶠ[nhds x] 1)
    (vs : ι → List E) (u : 𝓢'(E,F)) (i : ι) :
    smulLeftCLM F (perturbCoefficient c η a i) (derivative (vs i) (smulLeftCLM F χ u)) =
      c i • derivative (vs i) (smulLeftCLM F χ u) -
        smulLeftCLM F (a i) (derivative (vs i) (smulLeftCLM F χ u)) := by
  have hcut := ((supported_multiply χ u).derivative (vs i)).cutoff_identity η hη
  change smulLeftCLM F (c i • (η : E → ℂ) - (a i : E → ℂ)) _ = _
  have hg : (c i • (η : E → ℂ)).HasTemperateGrowth := by
    simpa only [Pi.smul_def, Pi.mul_def, smul_eq_mul] using
      (Function.HasTemperateGrowth.const (c i)).smul η.hasTemperateGrowth
  rw [smulLeftCLM_sub hg (a i).hasTemperateGrowth,
    sub_apply, smulLeftCLM_smul η.hasTemperateGrowth, smul_apply, hcut]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma frozenSymbol_growth (c : ι → ℂ) (vs : ι → List E) :
    (frozenSymbol c vs).HasTemperateGrowth := by
  apply (Function.HasTemperateGrowth.const (1:ℂ)).add
  apply Function.HasTemperateGrowth.sum
  intro i hi
  simpa only [Pi.smul_def, Pi.mul_def, smul_eq_mul] using
    (Function.HasTemperateGrowth.const (c i)).smul (symbol_growth (vs i))

lemma fourier_add {a b : E → ℂ} (ha : a.HasTemperateGrowth) (hb : b.HasTemperateGrowth)
    (u : 𝓢'(E,F)) : fourierMultiplierCLM F (a+b) u =
      fourierMultiplierCLM F a u + fourierMultiplierCLM F b u := by
  simp only [fourierMultiplierCLM_apply, smulLeftCLM_add ha hb, add_apply, fourierInv_add]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma sumSymbol_growth (c : ι → ℂ) (vs : ι → List E) :
    (fun x => ∑ i, (c i • symbol (vs i)) x).HasTemperateGrowth := by
  apply Function.HasTemperateGrowth.sum
  intro i hi
  simpa only [Pi.smul_def, Pi.mul_def, smul_eq_mul] using
    (Function.HasTemperateGrowth.const (c i)).smul (symbol_growth (vs i))

lemma sumSymbol_operator (c : ι → ℂ) (vs : ι → List E) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (fun x => ∑ i, (c i • symbol (vs i)) x) u =
      ∑ i, c i • derivative (vs i) u := by
  have hg : ∀ i ∈ (Finset.univ : Finset ι), (c i • symbol (vs i)).HasTemperateGrowth := by
    intro i hi
    simpa only [Pi.smul_def, Pi.mul_def, smul_eq_mul] using
      (Function.HasTemperateGrowth.const (c i)).smul (symbol_growth (vs i))
  rw [fourierMultiplierCLM_sum F hg, sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fourierMultiplierCLM_smul (symbol_growth (vs i)), smul_apply, ←derivative_fourier]

lemma frozenSymbol_operator (c : ι → ℂ) (vs : ι → List E) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (frozenSymbol c vs) u = u + ∑ i, c i • derivative (vs i) u := by
  rw [frozenSymbol, fourier_add (Function.HasTemperateGrowth.const (1:ℂ)) (sumSymbol_growth c vs),
    sumSymbol_operator]
  congr 1
  simp only [fourierMultiplierCLM_const, ContinuousLinearMap.id_apply, one_smul]

lemma frozen_equation (c : ι → ℂ) (η χ : 𝓢(E,ℂ)) (a : ι → 𝓢(E,ℂ))
    (hη : ∀ x ∈ tsupport χ, (η : E → ℂ) =ᶠ[nhds x] 1)
    (vs : ι → List E) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (frozenSymbol c vs) (smulLeftCLM F χ u) -
      ∑ i, smulLeftCLM F (perturbCoefficient c η a i)
        (fourierMultiplierCLM F (symbol (vs i)) (smulLeftCLM F χ u)) =
      smulLeftCLM F χ u + operator a vs (smulLeftCLM F χ u) := by
  simp only [frozenSymbol_operator, ←derivative_fourier,
    perturb_on_cutoff c η χ a hη vs u, operator_apply, Finset.sum_sub_distrib]
  abel

variable [CompleteSpace F] [Fintype κ]

theorem gain_for_localized_operator {s Cq : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (c : ι → ℂ) (η χ : 𝓢(E,ℂ)) (a : ι → 𝓢(E,ℂ)) (b : κ → 𝓢(E,ℂ))
    (vs : ι → List E) (ws : κ → List E) (hvs : ∀ i, (vs i).length = m)
    (hws : ∀ i, (ws i).length < m)
    (hη : ∀ x ∈ tsupport χ, (η : E → ℂ) =ᶠ[nhds x] 1)
    {q : E → ℂ} (hq : q.HasTemperateGrowth) (hCq : 0 ≤ Cq)
    (hinv : ∀ x, frozenSymbol c vs x * q x = 1)
    (hbq : ∀ x, LocalPeetre.weight (m:ℝ) x * ‖q x‖ ≤ Cq)
    (hs : Cq * ∑ i, LocalParametrix.coefficientGauge (s-(m:ℝ))
      (perturbCoefficient c η a i) * symbolConstant (vs i) < 1)
    (ht : Cq * ∑ i, LocalParametrix.coefficientGauge (s+1-(m:ℝ))
      (perturbCoefficient c η a i) * symbolConstant (vs i) < 1)
    {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u)
    (hP : smulLeftCLM F χ (operator a vs u + operator b ws u) = 0) :
    MemSobolev (s+1) 2 (smulLeftCLM F χ u) := by
  have hv := multiply_sobolev hu χ
  have hlow : MemSobolev (s-(m:ℝ)+1) 2 (smulLeftCLM F χ (operator b ws u)) := by
    apply multiply_sobolev
    simpa only [operator_apply] using lower_order_sobolev hu b ws hws
  have hcomm : MemSobolev (s-(m:ℝ)+1) 2
      (∑ i, smulLeftCLM F (a i) (derivative (vs i) (smulLeftCLM F χ u) -
        smulLeftCLM F χ (derivative (vs i) u))) := by
    apply sobolev_finset_sum
    intro i hi
    have hh := multiply_sobolev (commutator_sobolev hu χ (vs i)) (a i)
    simpa only [hvs i] using hh
  have hcut : smulLeftCLM F χ (operator a vs u) = - smulLeftCLM F χ (operator b ws u) := by
    rw [map_add] at hP
    exact eq_neg_of_add_eq_zero_left hP
  have hf : MemSobolev (s-(m:ℝ)+1) 2
      (smulLeftCLM F χ u + operator a vs (smulLeftCLM F χ u)) := by
    rw [operator_cutoff, hcut]
    apply (hv.mono ?_).add (hlow.neg.add hcomm)
    have hh : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  apply gain_from_frozen_equation (fun i => symbolConstant (vs i)) hCq
    (fun i => symbolConstant_nonneg (vs i)) hq (frozenSymbol_growth c vs) hinv hbq
    (fun i => symbol_growth (vs i)) ?_ (perturbCoefficient c η a) hs ht hv hf
    (frozen_equation c η χ a hη vs u)
  intro i x
  simpa only [LocalPeetre.weight, hvs i] using weighted_symbol_bound (vs i) x

end LocalOperator
end

open Filter Function
open scoped SchwartzMap Topology ContDiff
noncomputable section
namespace LocalSchwartz

variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma contDiff_partial_iterated (g : ℝ → E → F)
    (hg : ContDiff ℝ ∞ (Function.uncurry g)) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × E => iteratedFDeriv ℝ n (g p.1) p.2) := by
  induction n with
  | zero =>
      simpa +unfoldPartialApp only [iteratedFDeriv_zero_eq_comp,Function.comp_def, Function.uncurry_def, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
        ((continuousMultilinearCurryFin0 ℝ E F).symm : F →L[ℝ] E [×0]→L[ℝ] F).contDiff.comp hg
  | succ n ih =>
      have hpar : ContDiff ℝ ∞ (fun q : (ℝ × E) × E =>
          iteratedFDeriv ℝ n (g q.1.1) q.2) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd := ContDiff.fderiv (f:=fun p : ℝ × E => iteratedFDeriv ℝ n (g p.1))
        (g:=fun p : ℝ × E => p.2) hpar (contDiff_snd (n:=∞)) (by simp)
      simpa +unfoldPartialApp only [iteratedFDeriv_succ_eq_comp_left,Function.comp_def, ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm :
          (E →L[ℝ] E [×n]→L[ℝ] F) →L[ℝ] E [×(n+1)]→L[ℝ] F).contDiff.comp hd

lemma tendsto_zero_of_compact_support {a : ℝ → 𝓢(E,F)} {K : Set E}
    (hK : IsCompact K) (hsupp : ∀ r, tsupport (a r) ⊆ K) (ha0 : a 0 = 0)
    (hder : ∀ n, Continuous (fun p : ℝ × E => iteratedFDeriv ℝ n (a p.1) p.2)) :
    Tendsto a (𝓝 0) (𝓝 0) := by
  rw [(schwartz_withSeminorms ℝ E F).tendsto_nhds]
  rintro ⟨k,n⟩ ε hε
  have hc : Continuous (fun p : ℝ × E => ‖p.2‖^k * ‖iteratedFDeriv ℝ n (a p.1) p.2‖) :=
    (continuous_snd.norm.pow k).mul (hder n).norm
  have he : ∀ᶠ r in 𝓝 (0:ℝ), ∀ x ∈ K,
      ‖x‖^k * ‖iteratedFDeriv ℝ n (a r) x‖ < ε/2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro x hx
    have hh : ‖x‖^k * ‖iteratedFDeriv ℝ n (a 0) x‖ < ε/2 := by
      simp [ha0, half_pos hε]
    exact hc.continuousAt.eventually (gt_mem_nhds hh)
  filter_upwards [he] with r hr
  simp only [sub_zero, SchwartzMap.schwartzSeminormFamily_apply]
  apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (a r) (le_of_lt (half_pos hε)) ?_)
    (half_lt_self hε)
  intro x
  by_cases hx : x ∈ K
  · exact (hr x hx).le
  · have hz : iteratedFDeriv ℝ n (a r) x = 0 := by
      apply Function.notMem_support.mp
      intro hc
      exact hx (hsupp r (support_iteratedFDeriv_subset n hc))
    simp [hz, (half_pos hε).le]

variable [NormedSpace ℂ F]

theorem frozenDifference_tendsto (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ)
    (v : E → ℂ) (hv : ContDiff ℝ ∞ v) (x₀ : E) :
    Tendsto (frozenDifference χ hχ v hv x₀) (𝓝 0) (𝓝 0) := by
  apply tendsto_zero_of_compact_support hχ
  · intro r
    exact tsupport_mul_subset_left
  · ext x
    simp [frozenDifference]
  · intro n
    apply (contDiff_partial_iterated (fun r x => χ x * (v (x₀+r • x)-v x₀)) ?_ n).continuous
    exact (χ.smooth'.comp contDiff_snd).mul
      ((hv.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))).sub contDiff_const)

end LocalSchwartz

namespace LocalOperator
open MeasureTheory TemperedDistribution Filter LocalDifferential LocalSchwartz
open scoped SchwartzMap Topology ContDiff
variable {E : Type*} {F : Type*} {ι : Type*} {κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] in
lemma perturb_frozen_tendsto (η : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (a : ι → E → ℂ) (ha : ∀ i, ContDiff ℝ ∞ (a i)) (x₀ : E) (i : ι) :
    Tendsto (fun r => perturbCoefficient (fun j => a j x₀) η
      (fun j => frozenCoefficient η hη (a j) (ha j) x₀ r) i) (𝓝 0) (𝓝 0) := by
  have he : (fun r => perturbCoefficient (fun j => a j x₀) η
      (fun j => frozenCoefficient η hη (a j) (ha j) x₀ r) i) =
      fun r => -frozenDifference η hη (a i) (ha i) x₀ r := by
    funext r
    simp [perturbCoefficient, frozenCoefficient]
  rw [he]
  simpa using (frozenDifference_tendsto η hη (a i) (ha i) x₀).neg

theorem frozen_coefficients_eventually_small (η : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (a : ι → E → ℂ) (ha : ∀ i, ContDiff ℝ ∞ (a i)) (x₀ : E)
    (s t m Cq : ℝ) (vs : ι → List E) :
    ∀ᶠ r in 𝓝 (0:ℝ),
      Cq * ∑ i, LocalParametrix.coefficientGauge (s-m)
        (perturbCoefficient (fun j => a j x₀) η
          (fun j => frozenCoefficient η hη (a j) (ha j) x₀ r) i) * symbolConstant (vs i) < 1 ∧
      Cq * ∑ i, LocalParametrix.coefficientGauge (t-m)
        (perturbCoefficient (fun j => a j x₀) η
          (fun j => frozenCoefficient η hη (a j) (ha j) x₀ r) i) * symbolConstant (vs i) < 1 := by
  exact LocalParametrix.eventually_small_coefficients (perturb_frozen_tendsto η hη a ha x₀)
    s t m Cq (fun i => symbolConstant (vs i))

theorem eventually_gain_rescaled {s Cq : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (η χ : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (a : ι → E → ℂ) (ha : ∀ i, ContDiff ℝ ∞ (a i)) (x₀ : E)
    (vs : ι → List E) (ws : κ → List E)
    (hvs : ∀ i, (vs i).length = m) (hws : ∀ i, (ws i).length < m)
    (hcov : ∀ x ∈ tsupport χ, (η : E → ℂ) =ᶠ[nhds x] 1)
    {q : E → ℂ} (hq : q.HasTemperateGrowth) (hCq : 0 ≤ Cq)
    (hinv : ∀ x, frozenSymbol (fun i => a i x₀) vs x * q x = 1)
    (hbq : ∀ x, LocalPeetre.weight (m:ℝ) x * ‖q x‖ ≤ Cq) :
    ∀ᶠ r in 𝓝 (0:ℝ), ∀ (b : κ → 𝓢(E,ℂ)) (u : 𝓢'(E,F)), MemSobolev s 2 u →
      smulLeftCLM F χ (operator (fun i => frozenCoefficient η hη (a i) (ha i) x₀ r) vs u +
        operator b ws u) = 0 → MemSobolev (s+1) 2 (smulLeftCLM F χ u) := by
  filter_upwards [frozen_coefficients_eventually_small η hη a ha x₀ s (s+1) m Cq vs] with r hr
  intro b u hu hP
  exact gain_for_localized_operator hm (fun i => a i x₀) η χ _ b vs ws hvs hws hcov
    hq hCq hinv hbq hr.1 hr.2 hu hP

end LocalOperator

namespace AffineDistribution
section
open MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap Real Topology ENNReal
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma dilate_lineDeriv (r : ℝ) (hr : r ≠ 0) (v : E) (u : 𝓢'(E,F)) :
    ∂_{v} (dilate r hr u) = dilate r hr (∂_{r • v} u) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, dilate_apply]
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  simp [homothety_symm_apply, smul_smul, hr]

lemma dilate_multiply (r : ℝ) (hr : r ≠ 0) (a : E → ℂ)
    (ha : a.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    dilate r hr (TemperedDistribution.smulLeftCLM F a u) =
      TemperedDistribution.smulLeftCLM F (fun x => a (r • x)) (dilate r hr u) := by
  have ha' : (fun x : E => a (r • x)).HasTemperateGrowth := by fun_prop
  ext φ
  simp only [dilate_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  congr 2
  ext x
  simp [SchwartzMap.smulLeftCLM_apply_apply ha, SchwartzMap.smulLeftCLM_apply_apply ha',
    homothety_symm_apply, smul_smul, hr]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]

lemma dilate_Lp {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : Lp F p (volume : Measure E))
    (r : ℝ) (hr : r ≠ 0) :
    dilate r hr (f : 𝓢'(E,F)) =
      ((memLp_dilate (Lp.memLp f) r hr).toLp (fun x => f (r • x)) : 𝓢'(E,F)) := by
  ext φ
  simp only [dilate_apply, Lp.toTemperedDistribution_apply]
  have hrep : (∫ x, φ x • (((memLp_dilate (Lp.memLp f) r hr).toLp
      (fun y => f (r • y))) : E → F) x) = ∫ x, φ x • f (r • x) := by
    apply integral_congr_ae
    filter_upwards [(memLp_dilate (Lp.memLp f) r hr).coeFn_toLp] with x hx
    rw [hx]
  rw [hrep]
  have he := Measure.integral_comp_smul volume
    (fun x : E => φ (r⁻¹ • x) • f x) r
  simp only [inv_smul_smul₀ hr] at he
  simpa only [jac, Complex.coe_smul, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, homothety_symm_apply] using he.symm

omit [CompleteSpace F] in

lemma fourier_comp_dilate (f : E → F) (r : ℝ) (hr : r ≠ 0) (ξ : E) :
    𝓕 (fun x => f (r • x)) ξ = jac (E:=E) r • (𝓕 f) (r⁻¹ • ξ) := by
  have he := Measure.integral_comp_smul volume
    (fun x : E => Real.fourierChar (-inner ℝ x (r⁻¹ • ξ)) • f x) r
  simpa only [Real.fourier_eq, jac, inner_smul_left, inner_smul_right,
    conj_trivial, inv_mul_cancel_left₀ hr] using he

lemma fourier_schwartz_dilate (φ : 𝓢(E,ℂ)) (r : ℝ) (hr : r ≠ 0) :
    𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (homothety (E:=E) r hr) φ) =
      (Complex.ofReal (jac (E:=E) r)) •
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (homothety (E:=E) r hr).symm (𝓕 φ) := by
  ext ξ
  change 𝓕 (fun x => φ (r • x)) ξ = (Complex.ofReal (jac (E:=E) r)) •
    (𝓕 (φ : E → ℂ)) (r⁻¹ • ξ)
  simpa only [Complex.coe_smul] using fourier_comp_dilate (φ : E → ℂ) r hr ξ

omit [CompleteSpace F] in
lemma fourier_dilate_test (r : ℝ) (hr : r ≠ 0) (u : 𝓢'(E,F)) (φ : 𝓢(E,ℂ)) :
    𝓕 (dilate r hr u) φ =
      (𝓕 u) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (homothety (E:=E) r hr) φ) := by
  simp only [TemperedDistribution.fourier_apply, dilate_apply, fourier_schwartz_dilate, map_smul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma jac_inv (r : ℝ) : jac (E:=E) r⁻¹ = (jac (E:=E) r)⁻¹ := by
  simp [jac, inv_pow, abs_inv]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma jac_ne_zero (r : ℝ) (hr : r ≠ 0) : jac (E:=E) r ≠ 0 := by
  simp [jac, hr]

omit [CompleteSpace F] in
lemma fourier_dilate (r : ℝ) (hr : r ≠ 0) (u : 𝓢'(E,F)) :
    𝓕 (dilate r hr u) = (Complex.ofReal (jac (E:=E) r)) •
      dilate r⁻¹ (inv_ne_zero hr) (𝓕 u) := by
  ext φ
  have heq : (homothety (E:=E) r⁻¹ (inv_ne_zero hr)).symm = homothety r hr := by
    ext x; simp
  have hj : Complex.ofReal (jac (E:=E) r) ≠ 0 := by
    exact_mod_cast jac_ne_zero (E:=E) r hr
  simp only [smul_apply, dilate_apply, heq, jac_inv, Complex.ofReal_inv, smul_smul,
    mul_inv_cancel₀ hj, one_smul,
    fourier_dilate_test]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma scaleWeight_growth (s r : ℝ) : (scaleWeight (E:=E) s r).HasTemperateGrowth := by
  have h1 : (fun x : E => (1+‖r • x‖^2)^(s/2)).HasTemperateGrowth :=
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s/2)).comp (by fun_prop)
  have h2 := Function.hasTemperateGrowth_one_add_norm_sq_rpow E (-s/2)
  exact (Complex.ofRealCLM.hasTemperateGrowth).comp (h1.mul h2)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma scaleWeight_bounded (s r : ℝ) (hr : r ≠ 0) :
    ∃ C, ∀ x : E, ‖scaleWeight s r x‖ ≤ C := by
  by_cases hs : 0 ≤ s
  · refine ⟨(max 1 (r^2))^(s/2), fun x => ?_⟩
    have hx : 0 < 1+‖x‖^2 := by positivity
    have he : 1+‖r • x‖^2 ≤ max 1 (r^2)*(1+‖x‖^2) := by
      have h1 := le_max_left (1:ℝ) (r^2)
      have h2 := le_max_right (1:ℝ) (r^2)
      have hn := sq_nonneg ‖x‖
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      nlinarith
    have hq : (1+‖r • x‖^2)/(1+‖x‖^2) ≤ max 1 (r^2) :=
      (div_le_iff₀ hx).mpr he
    have hp : 0 < 1+‖r • x‖^2 := by positivity
    rw [scaleWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      neg_div, Real.rpow_neg hx.le, ←div_eq_mul_inv, ←Real.div_rpow hp.le hx.le]
    exact Real.rpow_le_rpow (by positivity) hq (by positivity)
  · refine ⟨(min 1 (r^2))^(s/2), fun x => ?_⟩
    have hx : 0 < 1+‖x‖^2 := by positivity
    have hc : 0 < min 1 (r^2) := lt_min (by norm_num) (sq_pos_of_ne_zero hr)
    have he : min 1 (r^2)*(1+‖x‖^2) ≤ 1+‖r • x‖^2 := by
      have h1 := min_le_left (1:ℝ) (r^2)
      have h2 := min_le_right (1:ℝ) (r^2)
      have hn := sq_nonneg ‖x‖
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      nlinarith
    have hq : min 1 (r^2) ≤ (1+‖r • x‖^2)/(1+‖x‖^2) :=
      (le_div_iff₀ hx).mpr he
    have hp : 0 < 1+‖r • x‖^2 := by positivity
    rw [scaleWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      neg_div, Real.rpow_neg hx.le, ←div_eq_mul_inv, ←Real.div_rpow hp.le hx.le]
    exact Real.rpow_le_rpow_of_nonpos hc hq (by linarith)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma scaleWeight_mul (s r : ℝ) (x : E) :
    Complex.ofReal ((1+‖x‖^2)^(s/2)) * scaleWeight s r x =
      Complex.ofReal ((1+‖r • x‖^2)^(s/2)) := by
  have hx : 0 < 1+‖x‖^2 := by positivity
  simp only [scaleWeight, ←Complex.ofReal_mul]
  congr 1
  rw [neg_div, Real.rpow_neg hx.le]
  field_simp

lemma rescaled_fourier_Lp {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u)
    (r : ℝ) (hr : r ≠ 0) : ∃ f' : Lp F 2 (volume : Measure E),
      smulLeftCLM F (fun x => Complex.ofReal ((1+‖r • x‖^2)^(s/2))) (𝓕 u) = f' := by
  obtain ⟨f,hf⟩ := memSobolev_iff_exists_smulLeftCLM_fourier.mp hu
  obtain ⟨C,hC⟩ := scaleWeight_bounded (E:=E) s r hr
  let a := scaleWeight (E:=E) s r
  have ha : a.HasTemperateGrowth := scaleWeight_growth s r
  let ab := BoundedContinuousFunction.ofNormedAddCommGroup a ha.1.continuous C hC
  let f' : Lp F 2 (volume : Measure E) := (ab.memLp_top.toLp _ (μ := volume)) • f
  have hf' : (f' : 𝓢'(E,F)) =
      smulLeftCLM F (fun x => Complex.ofReal ((1+‖r • x‖^2)^(s/2))) (𝓕 u) := by
    change (((ab.memLp_top.toLp _ (μ := volume)) • f : Lp F 2 volume) : 𝓢'(E,F)) = _
    rw [Lp.toTemperedDistribution_smul_eq (by apply ha), ← hf]
    change smulLeftCLM F a
      (smulLeftCLM F (fun x : E => Complex.ofReal ((1+‖x‖^2)^(s/2))) (𝓕 u)) = _
    rw [smulLeftCLM_smulLeftCLM_apply (by fun_prop :
      (fun x : E => Complex.ofReal ((1+‖x‖^2)^(s/2))).HasTemperateGrowth) ha]
    congr 2
    ext x
    exact scaleWeight_mul s r x
  exact ⟨f', hf'.symm⟩

theorem memSobolev_dilate {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u)
    (r : ℝ) (hr : r ≠ 0) : MemSobolev s 2 (dilate r hr u) := by
  obtain ⟨f',hf'⟩ := rescaled_fourier_Lp hu r hr
  rw [memSobolev_iff_exists_smulLeftCLM_fourier]
  use (Complex.ofReal (jac (E:=E) r)) •
    (memLp_dilate (Lp.memLp f') r⁻¹ (inv_ne_zero hr)).toLp (fun x => f' (r⁻¹ • x))
  rw [←Lp.toTemperedDistributionCLM_apply, map_smul]
  change _ = (Complex.ofReal (jac (E:=E) r)) •
    (((memLp_dilate (Lp.memLp f') r⁻¹ (inv_ne_zero hr)).toLp
      (fun x => f' (r⁻¹ • x))) : 𝓢'(E,F))
  rw [←dilate_Lp f' r⁻¹ (inv_ne_zero hr)]
  rw [fourier_dilate r hr, map_smul, ←hf']
  apply congrArg (fun v : 𝓢'(E,F) => (Complex.ofReal (jac (E:=E) r)) • v)
  have hw : (fun x : E => Complex.ofReal ((1+‖r • x‖^2)^(s/2))).HasTemperateGrowth :=
    (Complex.ofRealCLM.hasTemperateGrowth).comp
      ((Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s/2)).comp (by fun_prop))
  rw [dilate_multiply r⁻¹ (inv_ne_zero hr) _ hw]
  congr 2
  ext x
  simp [smul_smul, hr]

end

open MeasureTheory TemperedDistribution LineDeriv LocalDifferential
open scoped SchwartzMap
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma test_translate_lineDeriv (a v : E) (φ : 𝓢(E,ℂ)) :
    ∂_{v} (SchwartzMap.compSubConstCLM ℂ a φ) =
      SchwartzMap.compSubConstCLM ℂ a (∂_{v} φ) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have he : (SchwartzMap.compSubConstCLM ℂ a φ : E → ℂ) = fun y => φ (y-a) := rfl
  rw [he]
  have hd : HasFDerivAt (fun y : E => y-a) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).sub_const a
  have hd' : HasFDerivAt (fun y => φ (y-a)) (fderiv ℝ φ (x-a)) x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      (φ.differentiableAt.hasFDerivAt.comp x hd)
  rw [hd'.fderiv]
  rfl

lemma translate_lineDeriv (a v : E) (u : 𝓢'(E,F)) :
    ∂_{v} (translate a u) = translate a (∂_{v} u) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, translate_apply, map_neg]
  rw [test_translate_lineDeriv]

lemma translate_derivative (a : E) (vs : List E) (u : 𝓢'(E,F)) :
    derivative vs (translate a u) = translate a (derivative vs u) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [derivative_cons, ih, translate_lineDeriv, derivative_cons]

lemma dilate_derivative (r : ℝ) (hr : r ≠ 0) (vs : List E) (u : 𝓢'(E,F)) :
    derivative vs (dilate r hr u) = (Complex.ofReal (r^vs.length)) •
      dilate r hr (derivative vs u) := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      rw [derivative_cons, ih, lineDerivOp_smul, dilate_lineDeriv,
        lineDerivOp_left_smul, ContinuousLinearMap.map_smul_of_tower]
      simp only [derivative_cons, List.length_cons, pow_succ, Complex.ofReal_mul,
        Complex.coe_smul, smul_smul, mul_comm]
      rw [←Complex.ofReal_mul, Complex.coe_smul]

lemma translate_multiply (x₀ : E) (a : E → ℂ) (ha : a.HasTemperateGrowth)
    (u : 𝓢'(E,F)) :
    translate x₀ (smulLeftCLM F a u) =
      smulLeftCLM F (fun x => a (x+x₀)) (translate x₀ u) := by
  have ha' : (fun x => a (x+x₀)).HasTemperateGrowth := by fun_prop
  ext φ
  simp only [translate_apply, TemperedDistribution.smulLeftCLM_apply_apply]
  congr 1
  ext x
  simp [SchwartzMap.smulLeftCLM_apply_apply ha, SchwartzMap.smulLeftCLM_apply_apply ha']

@[simp] lemma dilate_inv_dilate (r : ℝ) (hr : r ≠ 0) (u : 𝓢'(E,F)) :
    dilate r⁻¹ (inv_ne_zero hr) (dilate r hr u) = u := by
  ext φ
  simp only [dilate_apply, smul_smul, ←Complex.ofReal_mul, jac_inv,
    inv_mul_cancel₀ (jac_ne_zero r hr), Complex.ofReal_one, one_smul]
  congr 1
  ext x
  simp [homothety_symm_apply, smul_smul, hr]

lemma dilate_derivative_inverse (r : ℝ) (hr : r ≠ 0) (vs : List E) (u : 𝓢'(E,F)) :
    dilate r hr (derivative vs u) = (Complex.ofReal (r⁻¹^vs.length)) •
      derivative vs (dilate r hr u) := by
  rw [dilate_derivative r hr, smul_smul, ←Complex.ofReal_mul, ←mul_pow,
    inv_mul_cancel₀ hr, one_pow, Complex.ofReal_one, one_smul]

end AffineDistribution

namespace TranslationSobolev
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma translate_schwartz (a : E) (f : 𝓢(E,F)) :
    translate a (f : 𝓢'(E,F)) =
      (SchwartzMap.compSubConstCLM ℂ (-a) f : 𝓢'(E,F)) := by
  ext φ
  change (∫ x, φ (x-a) • f x) = ∫ x, φ x • f (x-(-a))
  have he := integral_add_right_eq_self (μ:=volume) (fun x : E => φ (x-a) • f x) a
  simpa only [add_sub_cancel_right, sub_neg_eq_add] using he.symm

omit [CompleteSpace F] in
lemma norm_fourier_translate (a : E) (f : E → F) (ξ : E) :
    ‖𝓕 (fun x => f (x+a)) ξ‖ = ‖𝓕 f ξ‖ := by
  have he := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    volume (innerₗ E) f a) ξ
  have hn := congrArg norm he
  rw [Circle.norm_smul] at hn
  convert hn using 1 <;> first | rfl | simp only [Real.fourier_eq, VectorFourier.fourierIntegral,
    Function.comp_apply, innerₗ_apply_apply]

lemma norm_coordinate (s : ℝ) (f : 𝓢(E,F)) :
    ‖SobolevModel.coordinate E F s f‖ = ‖(weighted s (𝓕 f)).toLp 2‖ := by
  simp only [SobolevModel.coordinate, ContinuousLinearMap.comp_apply,
    SchwartzMap.toLpCLM_apply]
  rw [← SchwartzMap.norm_fourier_toL2_eq (SobolevModel.schwartzBessel E F s f)]
  simp only [SobolevModel.schwartzBessel, SchwartzMap.fourierMultiplierCLM_apply,
    fourier_fourierInv_eq]
  rfl

lemma norm_coordinate_translate_le (s : ℝ) (a : E) (f : 𝓢(E,F)) :
    ‖SobolevModel.coordinate E F s (SchwartzMap.compSubConstCLM ℂ (-a) f)‖ ≤
      1 * ‖SobolevModel.coordinate E F s f‖ := by
  rw [norm_coordinate, norm_coordinate]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [SchwartzMap.coeFn_toLp
    (weighted s (𝓕 (SchwartzMap.compSubConstCLM ℂ (-a) f))) (p:=2) (μ:=volume),
    SchwartzMap.coeFn_toLp (weighted s (𝓕 f)) (p:=2) (μ:=volume)] with x hx hy
  rw [hx,hy]
  simp only [weighted, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop :
    (fun x : E => Complex.ofReal ((1+‖x‖^2)^(s/2))).HasTemperateGrowth), norm_smul,
    one_mul]
  have hn : ‖𝓕 (SchwartzMap.compSubConstCLM ℂ (-a) f) x‖ = ‖𝓕 f x‖ := by
    change ‖𝓕 (fun x => f (x-(-a))) x‖ = ‖𝓕 (f : E → F) x‖
    simpa only [sub_neg_eq_add] using norm_fourier_translate a (f : E → F) x
  rw [hn]

theorem memSobolev_translate {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (a : E) :
    MemSobolev s 2 (translate a u) := by
  obtain ⟨R,_,hR⟩ := SobolevModel.lift_operator (by norm_num : (0:ℝ) ≤ 1)
    (translate (F:=F) a) (SchwartzMap.compSubConstCLM ℂ (-a))
    (translate_schwartz a) (norm_coordinate_translate_le s a)
  obtain ⟨f,rfl⟩ := (SobolevModel.memSobolev_iff_range s u).mp hu
  rw [←hR]
  exact SobolevModel.embedding_memSobolev s (R f)

end TranslationSobolev

namespace AffineDistribution
section
open MeasureTheory TemperedDistribution LineDeriv LocalDifferential
open scoped SchwartzMap
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma transform_multiply (x₀ : E) (r : ℝ) (hr : r ≠ 0) (a : E → ℂ)
    (ha : a.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    transform x₀ r hr (smulLeftCLM F a u) =
      smulLeftCLM F (fun x => a (x₀+r • x)) (transform x₀ r hr u) := by
  change dilate r hr (translate x₀ (smulLeftCLM F a u)) = _
  rw [translate_multiply x₀ a ha, dilate_multiply r hr _ (by fun_prop)]
  simp only [add_comm]
  rfl

lemma transform_derivative (x₀ : E) (r : ℝ) (hr : r ≠ 0) (vs : List E) (u : 𝓢'(E,F)) :
    transform x₀ r hr (derivative vs u) = Complex.ofReal (r⁻¹^vs.length) •
      derivative vs (transform x₀ r hr u) := by
  change dilate r hr (translate x₀ (derivative vs u)) = _
  rw [←translate_derivative, dilate_derivative_inverse]
  rfl

lemma transform_cutoff (x₀ : E) (r : ℝ) (hr : r ≠ 0) (χ : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    transform x₀ r hr (smulLeftCLM F (physicalCutoff x₀ r hr χ) u) =
      smulLeftCLM F χ (transform x₀ r hr u) := by
  rw [transform_multiply x₀ r hr _ (physicalCutoff x₀ r hr χ).hasTemperateGrowth]
  congr 2
  ext x
  simp [physicalCutoff_apply, smul_smul, hr]

lemma inverse_transform (x₀ : E) (r : ℝ) (hr : r ≠ 0) (u : 𝓢'(E,F)) :
    translate (-x₀) (dilate r⁻¹ (inv_ne_zero hr) (transform x₀ r hr u)) = u := by
  change translate (-x₀) (dilate r⁻¹ (inv_ne_zero hr) (dilate r hr (translate x₀ u))) = _
  rw [dilate_inv_dilate, translate_translate, neg_add_cancel, translate_zero]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]

lemma memSobolev_transform {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u)
    (x₀ : E) (r : ℝ) (hr : r ≠ 0) : MemSobolev s 2 (transform x₀ r hr u) := by
  have ht : MemSobolev s 2 (translate x₀ u) := TranslationSobolev.memSobolev_translate hu x₀
  exact memSobolev_dilate ht r hr

lemma memSobolev_of_transform {s : ℝ} {u : 𝓢'(E,F)} (x₀ : E) (r : ℝ) (hr : r ≠ 0)
    (hu : MemSobolev s 2 (transform x₀ r hr u)) : MemSobolev s 2 u := by
  have hs := memSobolev_dilate hu r⁻¹ (inv_ne_zero hr)
  have ht : MemSobolev s 2 (translate (-x₀) (dilate r⁻¹ (inv_ne_zero hr) (transform x₀ r hr u))) :=
    TranslationSobolev.memSobolev_translate hs (-x₀)
  rwa [inverse_transform] at ht

lemma memSobolev_physicalCutoff {s : ℝ} {u : 𝓢'(E,F)} (x₀ : E) (r : ℝ) (hr : r ≠ 0)
    (χ : 𝓢(E,ℂ)) (hu : MemSobolev s 2 (smulLeftCLM F χ (transform x₀ r hr u))) :
    MemSobolev s 2 (smulLeftCLM F (physicalCutoff x₀ r hr χ) u) := by
  apply memSobolev_of_transform x₀ r hr
  rwa [transform_cutoff]

end

open MeasureTheory TemperedDistribution LocalDifferential LocalOperator
open scoped SchwartzMap
variable {E : Type*} {F : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]

lemma frozen_cutoff (η χ : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (hcov : ∀ x ∈ tsupport χ, η x = 1) (a : 𝓢(E,ℂ)) (x₀ : E) (r : ℝ)
    (u : 𝓢'(E,F)) :
    smulLeftCLM F χ (smulLeftCLM F (frozenCoefficient η hη a a.smooth' x₀ r) u) =
      smulLeftCLM F χ (smulLeftCLM F (fun x => a (x₀+r • x)) u) := by
  rw [smulLeftCLM_smulLeftCLM_apply
    (frozenCoefficient η hη a a.smooth' x₀ r).hasTemperateGrowth χ.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) χ.hasTemperateGrowth]
  congr 2
  ext x
  by_cases hx : x ∈ tsupport χ
  · simp [frozenCoefficient_apply, hcov x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

lemma power_normalize (r : ℝ) (hr : r ≠ 0) {k m : ℕ} (hkm : k ≤ m) :
    r^m * r⁻¹^k = r^(m-k) := by
  have he : m = m-k+k := (Nat.sub_add_cancel hkm).symm
  conv_lhs => rw [he, pow_add]
  rw [mul_assoc, ←mul_pow, mul_inv_cancel₀ hr, one_pow, mul_one]

lemma transform_term (χ a : 𝓢(E,ℂ)) (x₀ : E) (r : ℝ) (hr : r ≠ 0)
    (vs : List E) (u : 𝓢'(E,F)) :
    transform x₀ r hr (smulLeftCLM F (physicalCutoff x₀ r hr χ)
      (smulLeftCLM F a (derivative vs u))) =
      Complex.ofReal (r⁻¹^vs.length) • smulLeftCLM F χ
        (smulLeftCLM F (fun x => a (x₀+r • x))
          (derivative vs (transform x₀ r hr u))) := by
  rw [transform_cutoff, transform_multiply x₀ r hr a a.hasTemperateGrowth,
    transform_derivative, map_smul, map_smul]

lemma normalized_term (η χ : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (hcov : ∀ x ∈ tsupport χ, η x = 1) (a : 𝓢(E,ℂ))
    (x₀ : E) (r : ℝ) (hr : r ≠ 0) (vs : List E) {m : ℕ} (hvm : vs.length ≤ m)
    (u : 𝓢'(E,F)) :
    Complex.ofReal (r^m) • transform x₀ r hr
      (smulLeftCLM F (physicalCutoff x₀ r hr χ) (smulLeftCLM F a (derivative vs u))) =
      smulLeftCLM F χ
        (smulLeftCLM F (Complex.ofReal (r^(m-vs.length)) •
          (frozenCoefficient η hη a a.smooth' x₀ r : E → ℂ))
          (derivative vs (transform x₀ r hr u))) := by
  rw [transform_term, smul_smul, ←Complex.ofReal_mul, power_normalize r hr hvm,
    smulLeftCLM_smul (frozenCoefficient η hη a a.smooth' x₀ r).hasTemperateGrowth,
    smul_apply, map_smul, frozen_cutoff η χ hη hcov]

lemma normalized_operator (η χ : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (hcov : ∀ x ∈ tsupport χ, η x = 1) (a : ι → 𝓢(E,ℂ))
    (x₀ : E) (r : ℝ) (hr : r ≠ 0) (vs : ι → List E) {m : ℕ}
    (hvm : ∀ i, (vs i).length ≤ m) (u : 𝓢'(E,F)) :
    Complex.ofReal (r^m) • transform x₀ r hr
      (smulLeftCLM F (physicalCutoff x₀ r hr χ) (operator a vs u)) =
      smulLeftCLM F χ (operator (fun i => Complex.ofReal (r^(m-(vs i).length)) •
        frozenCoefficient η hη (a i) (a i).smooth' x₀ r) vs (transform x₀ r hr u)) := by
  simp only [operator_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact normalized_term η χ hη hcov (a i) x₀ r hr (vs i) (hvm i) u

variable {κ : Type*} [Fintype κ]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in

lemma normalized_weak_equation (η χ : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (hcov : ∀ x ∈ tsupport χ, η x = 1) (a : ι → 𝓢(E,ℂ)) (b : κ → 𝓢(E,ℂ))
    (x₀ : E) (r : ℝ) (hr : r ≠ 0) (vs : ι → List E) (ws : κ → List E) {m : ℕ}
    (hvs : ∀ i, (vs i).length = m) (hws : ∀ i, (ws i).length ≤ m)
    (u : 𝓢'(E,F))
    (hP : smulLeftCLM F (physicalCutoff x₀ r hr χ) (operator a vs u + operator b ws u) = 0) :
    smulLeftCLM F χ (operator (fun i => frozenCoefficient η hη (a i) (a i).smooth' x₀ r)
      vs (transform x₀ r hr u) +
      operator (fun i => Complex.ofReal (r^(m-(ws i).length)) •
        frozenCoefficient η hη (b i) (b i).smooth' x₀ r) ws (transform x₀ r hr u)) = 0 := by
  have he := congrArg (fun v => Complex.ofReal (r^m) • transform x₀ r hr v) hP
  simp only [map_add, smul_add, map_zero, smul_zero] at he
  rw [normalized_operator η χ hη hcov a x₀ r hr vs (fun i => (hvs i).le),
    normalized_operator η χ hη hcov b x₀ r hr ws hws] at he
  simpa only [hvs, Nat.sub_self, pow_zero, Complex.ofReal_one, one_smul, map_add] using he

theorem eventually_physical_gain {s Cq : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (η χ : 𝓢(E,ℂ)) (hη : HasCompactSupport η)
    (a : ι → 𝓢(E,ℂ)) (b : κ → 𝓢(E,ℂ)) (x₀ : E)
    (vs : ι → List E) (ws : κ → List E)
    (hvs : ∀ i, (vs i).length = m) (hws : ∀ i, (ws i).length < m)
    (hcov : ∀ x ∈ tsupport χ, (η : E → ℂ) =ᶠ[nhds x] 1)
    {q : E → ℂ} (hq : q.HasTemperateGrowth) (hCq : 0 ≤ Cq)
    (hinv : ∀ x, frozenSymbol (fun i => a i x₀) vs x * q x = 1)
    (hbq : ∀ x, LocalPeetre.weight (m:ℝ) x * ‖q x‖ ≤ Cq) :
    ∀ᶠ r in nhds (0:ℝ), ∀ (hr : r ≠ 0) (u : 𝓢'(E,F)), MemSobolev s 2 u →
      smulLeftCLM F (physicalCutoff x₀ r hr χ) (operator a vs u + operator b ws u) = 0 →
      MemSobolev (s+1) 2 (smulLeftCLM F (physicalCutoff x₀ r hr χ) u) := by
  filter_upwards [eventually_gain_rescaled (F:=F) hm η χ hη
    (fun i => (a i : E → ℂ)) (fun i => (a i).smooth') x₀ vs ws hvs hws hcov
    hq hCq hinv hbq (s:=s)] with r hgain
  intro hr u hu hP
  apply memSobolev_physicalCutoff x₀ r hr
  apply hgain _ _ (memSobolev_transform hu x₀ r hr)
  exact normalized_weak_equation η χ hη (fun x hx => (hcov x hx).self_of_nhds)
    a b x₀ r hr vs ws hvs (fun i => (hws i).le) u hP

end AffineDistribution

namespace LocalSupport
open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap Topology
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
lemma supported_multiply_growth (a : E → ℂ) (ha : a.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    SupportedIn (smulLeftCLM F a u) (tsupport a) := by
  intro φ hφ
  rw [smulLeftCLM_apply_apply]
  have hz : SchwartzMap.smulLeftCLM ℂ a φ = 0 := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply ha]
    by_cases hx : a x = 0
    · simp [hx]
    · have hpx := (hφ x (subset_tsupport a (Function.mem_support.mpr hx))).self_of_nhds
      simp [hpx]
  rw [hz, map_zero]

lemma SupportedIn.annihilate {u : 𝓢'(E,F)} {K : Set E} (hu : SupportedIn u K)
    (a : E → ℂ) (ha : a.HasTemperateGrowth)
    (hz : ∀ x ∈ K, a =ᶠ[𝓝 x] 0) : smulLeftCLM F a u = 0 := by
  ext φ
  rw [smulLeftCLM_apply_apply, zero_apply]
  apply hu
  intro x hx
  filter_upwards [hz x hx] with y hy
  simp only [SchwartzMap.smulLeftCLM_apply_apply ha, hy, Pi.zero_apply, zero_smul]

lemma cutoff_derivative_eq (θ χ : 𝓢(E,ℂ))
    (hθ : ∀ x ∈ tsupport χ, (θ : E → ℂ) =ᶠ[𝓝 x] 1)
    (vs : List E) (u : 𝓢'(E,F)) :
    smulLeftCLM F χ (LocalDifferential.derivative vs (smulLeftCLM F θ u)) =
      smulLeftCLM F χ (LocalDifferential.derivative vs u) := by
  have hg : ((1 : E → ℂ) - (θ : E → ℂ)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (1:ℂ)).sub θ.hasTemperateGrowth
  have hg1 : (1:E → ℂ).HasTemperateGrowth := Function.HasTemperateGrowth.const (1:ℂ)
  have he : smulLeftCLM F ((1 : E → ℂ) - (θ : E → ℂ)) u = u - smulLeftCLM F θ u := by
    rw [smulLeftCLM_sub hg1 θ.hasTemperateGrowth,
      sub_apply]
    congr 1
    change smulLeftCLM F (fun _ : E => (1:ℂ)) u = u
    rw [smulLeftCLM_const, one_smul]
  have hs := (supported_multiply_growth ((1 : E → ℂ)-(θ : E → ℂ)) hg u).derivative vs
  have hz : ∀ x ∈ tsupport ((1 : E → ℂ)-(θ : E → ℂ)), (χ : E → ℂ) =ᶠ[𝓝 x] 0 := by
    intro x hx
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hxχ
    apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
    filter_upwards [hθ x hxχ] with y hy
    simp only [Pi.sub_apply, Pi.one_apply, hy, sub_self, Pi.zero_apply]
  have hh := hs.annihilate χ χ.hasTemperateGrowth hz
  rw [he, map_sub, map_sub] at hh
  exact (sub_eq_zero.mp hh).symm

end LocalSupport

namespace SobolevGerms
open MeasureTheory TemperedDistribution LocalDifferential LocalBootstrap
open scoped SchwartzMap Topology
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma aggregate_eq_one {as : List (𝓢(E,ℂ))} {x : E}
    (h : ∃ a ∈ as, a x = 1) : aggregate as x = 1 := by
  induction as with
  | nil => simp at h
  | cons a as ih =>
      obtain ⟨b,hb,hbx⟩ := h
      rcases List.mem_cons.mp hb with rfl | hb
      · simp [aggregate, hbx]
      · simp [aggregate, ih ⟨b,hb,hbx⟩]

lemma aggregate_sobolev {s : ℝ} {u : 𝓢'(E,F)} (as : List (𝓢(E,ℂ)))
    (h : ∀ a ∈ as, MemSobolev s 2 (smulLeftCLM F a u)) :
    MemSobolev s 2 (smulLeftCLM F (aggregate as) u) := by
  induction as with
  | nil =>
      change MemSobolev s 2 (smulLeftCLM F (fun _ => 0) u)
      simp
  | cons a as ih =>
      have ha := h a (List.mem_cons_self ..)
      have hb := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      have hab := multiply_sobolev hb a
      have he : (product a (aggregate as) : E → ℂ) = (aggregate as : E → ℂ) * a := by
        ext x
        simp [mul_comm]
      change MemSobolev s 2 (smulLeftCLM F ((a : E → ℂ) + (aggregate as : E → ℂ) - (product a (aggregate as) : E → ℂ)) u)
      rw [smulLeftCLM_sub (a.hasTemperateGrowth.add (aggregate as).hasTemperateGrowth)
        (product a (aggregate as)).hasTemperateGrowth, sub_apply,
        smulLeftCLM_add a.hasTemperateGrowth (aggregate as).hasTemperateGrowth, add_apply,
        he, ←smulLeftCLM_smulLeftCLM_apply (aggregate as).hasTemperateGrowth a.hasTemperateGrowth]
      exact (ha.add hb).sub hab

theorem compact_cutoff {s : ℝ} {u : 𝓢'(E,F)} (hu : ∀ x, At s u x)
    (φ : 𝓢(E,ℂ)) (hφ : HasCompactSupport φ) :
    MemSobolev s 2 (smulLeftCLM F φ u) := by
  classical
  choose χ hχ hreg using hu
  let U : E → Set E := fun x => interior {y | χ x y = 1}
  have hxU : ∀ x, x ∈ U x := by
    intro x
    exact mem_interior_iff_mem_nhds.mpr (hχ x)
  obtain ⟨J,hJ⟩ := hφ.elim_finite_subcover U (fun _ => isOpen_interior) (by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x,hxU x⟩)
  let as := J.toList.map χ
  have has : MemSobolev s 2 (smulLeftCLM F (aggregate as) u) := by
    apply aggregate_sobolev
    intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact hreg x
  have h1 : ∀ x ∈ tsupport φ, aggregate as x = 1 := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := Set.mem_iUnion₂.mp (hJ hx)
    apply aggregate_eq_one
    exact ⟨χ y, List.mem_map.mpr ⟨y, Finset.mem_toList.mpr hy, rfl⟩,
      (show x ∈ {z | χ y z = 1} from interior_subset hxy)⟩
  have he : (aggregate as : E → ℂ) * φ = φ := by
    ext x
    by_cases hx : x ∈ tsupport φ
    · simp [h1 x hx]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hh := multiply_sobolev has φ
  rw [smulLeftCLM_smulLeftCLM_apply (aggregate as).hasTemperateGrowth φ.hasTemperateGrowth,
    he] at hh
  exact hh

end SobolevGerms

namespace LocalBumps
open MeasureTheory Filter Metric
open scoped SchwartzMap Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma complexBump_tsupport (f : ContDiffBump (0:E)) :
    tsupport (complexBump f) = closedBall 0 f.rOut := by
  change tsupport (Complex.ofReal ∘ (f : E → ℝ)) = _
  rw [tsupport_comp_eq (by simp), f.tsupport_eq]

lemma complexBump_compact (f : ContDiffBump (0:E)) : HasCompactSupport (complexBump f) := by
  rw [HasCompactSupport, complexBump_tsupport]
  exact isCompact_closedBall _ _

lemma complexBump_one (f : ContDiffBump (0:E)) {x : E} (hx : x ∈ ball 0 f.rIn) :
    (complexBump f : E → ℂ) =ᶠ[𝓝 x] 1 := by
  filter_upwards [f.eventuallyEq_one_of_mem_ball hx] with y hy
  simp only [complexBump_apply, hy, Pi.one_apply, Complex.ofReal_one]

lemma outer_compact : HasCompactSupport (outer : 𝓢(E,ℂ)) := complexBump_compact _
lemma inner_tsupport : tsupport (inner : 𝓢(E,ℂ)) = closedBall 0 1 := complexBump_tsupport _
lemma inner_one : (inner : E → ℂ) =ᶠ[𝓝 0] 1 :=
  complexBump_one _ (mem_ball_self (by norm_num : (0:ℝ) < 1/2))
lemma outer_covers_inner (x : E) (hx : x ∈ tsupport (inner : 𝓢(E,ℂ))) :
    (outer : E → ℂ) =ᶠ[𝓝 x] 1 := by
  apply complexBump_one
  rw [inner_tsupport, mem_closedBall, dist_zero_right] at hx
  rw [mem_ball, dist_zero_right]
  change ‖x‖ < 2
  linarith

end LocalBumps

namespace AffineDistribution
open MeasureTheory TemperedDistribution Filter Metric
open scoped SchwartzMap Topology
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

omit [FiniteDimensional ℝ E] in
lemma physicalCutoff_one (x₀ : E) (r : ℝ) (hr : r ≠ 0) (χ : 𝓢(E,ℂ))
    (hχ : (χ : E → ℂ) =ᶠ[𝓝 0] 1) :
    (physicalCutoff x₀ r hr χ : E → ℂ) =ᶠ[𝓝 x₀] 1 := by
  have ht : Tendsto (fun x : E => r⁻¹ • (x-x₀)) (𝓝 x₀) (𝓝 0) := by
    simpa using (show Continuous (fun x : E => r⁻¹ • (x-x₀)) by fun_prop).tendsto x₀
  filter_upwards [hχ.comp_tendsto ht] with x hx
  exact hx

lemma physical_inner_bound (x₀ : E) (r : ℝ) (hr : r ≠ 0) (x : E)
    (hx : x ∈ tsupport (physicalCutoff x₀ r hr (LocalBumps.inner : 𝓢(E,ℂ)))) :
    dist x x₀ ≤ |r| := by
  have hx' : r⁻¹ • (x-x₀) ∈ tsupport (LocalBumps.inner : 𝓢(E,ℂ)) :=
    tsupport_comp_subset_preimage (f:=fun y : E => r⁻¹ • (y-x₀))
      (LocalBumps.inner : E → ℂ) (by fun_prop) hx
  rw [LocalBumps.inner_tsupport, mem_closedBall, dist_zero_right] at hx'
  have hid : x-x₀ = r • (r⁻¹ • (x-x₀)) := by simp [smul_smul, hr]
  calc
    dist x x₀ = ‖x-x₀‖ := dist_eq_norm _ _
    _ = |r| * ‖r⁻¹ • (x-x₀)‖ := by
      conv_lhs => rw [hid]
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |r| * 1 := mul_le_mul_of_nonneg_left hx' (abs_nonneg _)
    _ = |r| := mul_one _

lemma eventually_physical_covered (x₀ : E) (θ : 𝓢(E,ℂ))
    (hθ : (θ : E → ℂ) =ᶠ[𝓝 x₀] 1) :
    ∀ᶠ r in 𝓝 (0:ℝ), ∀ (hr : r ≠ 0) x,
      x ∈ tsupport (physicalCutoff x₀ r hr (LocalBumps.inner : 𝓢(E,ℂ))) →
      (θ : E → ℂ) =ᶠ[𝓝 x] 1 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hθ
  have he : ∀ᶠ r in 𝓝 (0:ℝ), |r| < ε :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hε)
  filter_upwards [he] with r hr
  intro hr0 x hx
  have hxball : x ∈ ball x₀ ε := lt_of_le_of_lt (physical_inner_bound x₀ r hr0 x hx) hr
  exact Filter.mem_of_superset (isOpen_ball.mem_nhds hxball) hball

end AffineDistribution

namespace LocalSupport
open MeasureTheory TemperedDistribution LocalDifferential LocalOperator
open scoped SchwartzMap Topology
variable {E : Type*} {F : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]

lemma cutoff_operator_eq (θ χ : 𝓢(E,ℂ))
    (hθ : ∀ x ∈ tsupport χ, (θ : E → ℂ) =ᶠ[𝓝 x] 1)
    (a : ι → 𝓢(E,ℂ)) (vs : ι → List E) (u : 𝓢'(E,F)) :
    smulLeftCLM F χ (operator a vs (smulLeftCLM F θ u)) =
      smulLeftCLM F χ (operator a vs u) := by
  simp only [operator_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [multiply_comm χ (a i), cutoff_derivative_eq θ χ hθ,
    multiply_comm (a i) χ]

lemma cutoff_multiply_eq (θ χ : 𝓢(E,ℂ))
    (hθ : ∀ x ∈ tsupport χ, (θ : E → ℂ) =ᶠ[𝓝 x] 1) (u : 𝓢'(E,F)) :
    smulLeftCLM F χ (smulLeftCLM F θ u) = smulLeftCLM F χ u := by
  rw [multiply_comm χ θ]
  exact (supported_multiply χ u).cutoff_identity θ hθ

lemma cutoff_zero (θ χ : 𝓢(E,ℂ))
    (hθ : ∀ x ∈ tsupport χ, (θ : E → ℂ) =ᶠ[𝓝 x] 1)
    (u : 𝓢'(E,F)) (hu : smulLeftCLM F θ u = 0) : smulLeftCLM F χ u = 0 := by
  rw [←cutoff_multiply_eq θ χ hθ u, hu, map_zero]

end LocalSupport

namespace LocalElliptic
open MeasureTheory TemperedDistribution LocalDifferential LocalOperator AffineDistribution
open LocalSupport Filter Metric
open scoped SchwartzMap Topology
variable {E : Type*} {F : Type*} {ι : Type*} {κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [Fintype ι] [Fintype κ]

theorem gain_at {s Cq : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (a : ι → 𝓢(E,ℂ)) (b : κ → 𝓢(E,ℂ)) (x₀ : E)
    (vs : ι → List E) (ws : κ → List E)
    (hvs : ∀ i, (vs i).length = m) (hws : ∀ i, (ws i).length < m)
    {q : E → ℂ} (hq : q.HasTemperateGrowth) (hCq : 0 ≤ Cq)
    (hinv : ∀ x, frozenSymbol (fun i => a i x₀) vs x * q x = 1)
    (hbq : ∀ x, LocalPeetre.weight (m:ℝ) x * ‖q x‖ ≤ Cq)
    {u : 𝓢'(E,F)} (hu : SobolevGerms.At s u x₀)
    (hP : ∃ ψ : 𝓢(E,ℂ), (ψ : E → ℂ) =ᶠ[𝓝 x₀] 1 ∧
      smulLeftCLM F ψ (operator a vs u + operator b ws u) = 0) :
    SobolevGerms.At (s+1) u x₀ := by
  obtain ⟨θ,hθ,hreg⟩ := hu
  obtain ⟨ψ,hψ,hzero⟩ := hP
  have hev := eventually_physical_gain hm LocalBumps.outer LocalBumps.inner
    LocalBumps.outer_compact a b x₀ vs ws hvs hws LocalBumps.outer_covers_inner
    hq hCq hinv hbq (s:=s) (F:=F)
  have hθv := eventually_physical_covered x₀ θ hθ
  have hψv := eventually_physical_covered x₀ ψ hψ
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp ((hev.and hθv).and hψv)
  have hd : 0 < δ/2 := half_pos hδ
  have hr : δ/2 ≠ 0 := ne_of_gt hd
  have hmem : δ/2 ∈ ball (0:ℝ) δ := by
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hd]
    exact half_lt_self hδ
  have hh := hδball hmem
  let χ := physicalCutoff x₀ (δ/2) hr (LocalBumps.inner : 𝓢(E,ℂ))
  have hθχ : ∀ x ∈ tsupport χ, (θ : E → ℂ) =ᶠ[𝓝 x] 1 := hh.1.2 hr
  have hψχ : ∀ x ∈ tsupport χ, (ψ : E → ℂ) =ᶠ[𝓝 x] 1 := hh.2 hr
  refine ⟨χ, physicalCutoff_one x₀ (δ/2) hr _ LocalBumps.inner_one, ?_⟩
  have heq : smulLeftCLM F χ
      (operator a vs (smulLeftCLM F θ u) + operator b ws (smulLeftCLM F θ u)) = 0 := by
    rw [map_add, cutoff_operator_eq θ χ hθχ, cutoff_operator_eq θ χ hθχ, ←map_add]
    exact cutoff_zero ψ χ hψχ _ hzero
  have hgain := hh.1.1 hr _ hreg heq
  rwa [cutoff_multiply_eq θ χ hθχ] at hgain

end LocalElliptic

end

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Topology ContDiff
noncomputable section
namespace SobolevSmooth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma weighted_L1_of_distribution_eq (f g : Lp ℂ 1 (volume : Measure E))
    {w : E → ℂ} (hw : w.HasTemperateGrowth)
    (heq : TemperedDistribution.smulLeftCLM ℂ w (f : 𝓢'(E,ℂ)) = (g : 𝓢'(E,ℂ))) :
    Integrable (fun x => w x * f x) := by
  have hae : (fun x => w x * f x) =ᵐ[volume] g := by
    apply ae_eq_of_integral_contDiff_smul_eq
      ((Lp.memLp f).locallyIntegrable (by norm_num) |>.continuous_mul hw.1.continuous)
      ((Lp.memLp g).locallyIntegrable (by norm_num))
    intro φ hφ hφc
    let Φ : 𝓢(E,ℂ) := (hφc.comp_left (show Complex.ofRealCLM 0=0 by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
    have hh := congrArg (fun T : 𝓢'(E,ℂ) => T Φ) heq
    simp only [TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply] at hh
    convert hh using 1 <;> apply integral_congr_ae <;> filter_upwards [] with x
    · rw [SchwartzMap.smulLeftCLM_apply_apply hw]
      simp [Φ, smul_eq_mul, mul_assoc, mul_left_comm]
    · simp [Φ]
  exact (memLp_one_iff_integrable.mp (Lp.memLp g)).congr hae.symm

theorem exists_fourier_all_moments {u : 𝓢'(E,ℂ)}
    (hu : ∀ n : ℕ, MemSobolev (n:ℝ) 2 u) :
    ∃ f : Lp ℂ 1 (volume : Measure E), 𝓕 u = (f : 𝓢'(E,ℂ)) ∧
      ∀ n : ℕ, Integrable (fun x => ‖x‖^n * ‖f x‖) := by
  let d := Module.finrank ℝ E + 1
  have hd : (Module.finrank ℝ E : ℝ) < 2*(d:ℝ) := by dsimp [d]; norm_cast; omega
  obtain ⟨f,hf⟩ := (hu d).fourier_memL1 hd
  refine ⟨f,hf,?_⟩
  intro n
  have hnu : MemSobolev (d:ℝ) 2 (besselPotential E ℂ (n:ℝ) u) := by
    apply memSobolev_besselPotential_iff.mpr
    simpa only [Nat.cast_add] using hu (n+d)
  obtain ⟨g,hg⟩ := hnu.fourier_memL1 hd
  rw [fourier_besselPotential_eq_smulLeftCLM_fourier_apply,hf] at hg
  have hi := weighted_L1_of_distribution_eq f g (by fun_prop) hg
  apply Integrable.mono' hi.norm
    (by fun_prop : AEStronglyMeasurable (fun x => ‖x‖^n * ‖f x‖) volume)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hr : ‖x‖^n = (‖x‖^2)^((n:ℝ)/2) := by
    rw [← Real.rpow_natCast ‖x‖ n, ← Real.rpow_natCast ‖x‖ 2,
      ← Real.rpow_mul (norm_nonneg x)]
    congr 1; ring
  rw [hr]
  exact Real.rpow_le_rpow (sq_nonneg _) (by linarith) (by positivity)

theorem smooth_representative {u : 𝓢'(E,ℂ)}
    (hu : ∀ n : ℕ, MemSobolev (n:ℝ) 2 u) :
    ∃ v : E → ℂ, ContDiff ℝ ∞ v ∧
      ∀ φ : 𝓢(E,ℂ), u φ = ∫ x, φ x * v x := by
  obtain ⟨f,hf,hm⟩ := exists_fourier_all_moments hu
  refine ⟨𝓕⁻ (f : E → ℂ), ?_, ?_⟩
  · have hd : ContDiff ℝ ∞ (𝓕 (f : E → ℂ)) :=
      Real.contDiff_fourier (fun n _ => hm n)
    have heq : 𝓕⁻ (f : E → ℂ) = (fun x => 𝓕 (f : E → ℂ) (-x)) :=
      funext (Real.fourierInv_eq_fourier_neg _)
    rw [heq]
    exact hd.comp contDiff_id.neg
  · intro φ
    calc
      u φ = (𝓕⁻ (𝓕 u)) φ := by rw [fourierInv_fourier_eq]
      _ = ∫ x, (𝓕⁻ φ) x * f x := by
        rw [hf, TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
        simp only [smul_eq_mul]
      _ = ∫ x, φ x * (𝓕⁻ (f : E → ℂ)) x := by
        simpa [SchwartzMap.fourierInv_coe, smul_eq_mul, FourierTransformInv.fourierInv,
          VectorFourier.fourierIntegral, real_inner_comm, SchwartzMap.fourier_coe,
          Real.fourier_eq] using!
          (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := -innerₗ E) (μ := volume) (ν := volume)
            Real.continuous_fourierChar continuous_inner.neg φ.integrable
            (memLp_one_iff_integrable.mp (Lp.memLp f)))
    all_goals rfl

end SobolevSmooth

namespace LocalElliptic
open MeasureTheory TemperedDistribution LocalDifferential LocalOperator AffineDistribution
open LocalSupport Filter Metric
open scoped SchwartzMap Topology
variable {E : Type*} {F : Type*} {ι : Type*} {κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [Fintype ι] [Fintype κ]

theorem all_orders_at {Cq : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (a : ι → 𝓢(E,ℂ)) (b : κ → 𝓢(E,ℂ)) (x₀ : E)
    (vs : ι → List E) (ws : κ → List E)
    (hvs : ∀ i, (vs i).length = m) (hws : ∀ i, (ws i).length < m)
    {q : E → ℂ} (hq : q.HasTemperateGrowth) (hCq : 0 ≤ Cq)
    (hinv : ∀ x, frozenSymbol (fun i => a i x₀) vs x * q x = 1)
    (hbq : ∀ x, LocalPeetre.weight (m:ℝ) x * ‖q x‖ ≤ Cq)
    {u : 𝓢'(E,F)} (hu : SobolevGerms.At 0 u x₀)
    (hP : ∃ ψ : 𝓢(E,ℂ), (ψ : E → ℂ) =ᶠ[𝓝 x₀] 1 ∧
      smulLeftCLM F ψ (operator a vs u + operator b ws u) = 0) :
    ∀ n : ℕ, SobolevGerms.At (n:ℝ) u x₀ := by
  intro n
  induction n with
  | zero => simpa only [Nat.cast_zero] using hu
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one] using
      gain_at hm a b x₀ vs ws hvs hws hq hCq hinv hbq ih hP

lemma at_of_memSobolev {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (x₀ : E) :
    SobolevGerms.At s u x₀ := by
  refine ⟨physicalCutoff x₀ 1 one_ne_zero LocalBumps.inner,
    physicalCutoff_one x₀ 1 one_ne_zero _ LocalBumps.inner_one, ?_⟩
  exact LocalBootstrap.multiply_sobolev hu _

omit [MeasurableSpace E] [BorelSpace E] in
lemma physical_inner_compact (x₀ : E) (r : ℝ) (hr : r ≠ 0) :
    HasCompactSupport (physicalCutoff x₀ r hr (LocalBumps.inner : 𝓢(E,ℂ))) := by
  apply (isCompact_closedBall x₀ |r|).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  exact physical_inner_bound x₀ r hr x hx

theorem local_smooth_cutoffs {u : 𝓢'(E,ℂ)}
    (hu : ∀ n : ℕ, ∀ x, SobolevGerms.At (n:ℝ) u x) (x₀ : E) :
    ∃ χ : 𝓢(E,ℂ), (χ : E → ℂ) =ᶠ[𝓝 x₀] 1 ∧
      ∃ v : E → ℂ, ContDiff ℝ ∞ v ∧
        ∀ φ : 𝓢(E,ℂ), smulLeftCLM ℂ χ u φ = ∫ x, φ x * v x := by
  let χ := physicalCutoff x₀ 1 one_ne_zero (LocalBumps.inner : 𝓢(E,ℂ))
  refine ⟨χ, physicalCutoff_one x₀ 1 one_ne_zero _ LocalBumps.inner_one, ?_⟩
  exact SobolevSmooth.smooth_representative (fun n =>
    SobolevGerms.compact_cutoff (hu n) χ (physical_inner_compact x₀ 1 one_ne_zero))

end LocalElliptic

namespace SmoothPatching
open MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma cutoff_rep_ae (f : Lp ℂ 2 (volume : Measure E)) (χ : 𝓢(E,ℂ))
    (v : E → ℂ) (hv : Continuous v)
    (hrep : ∀ φ : 𝓢(E,ℂ), smulLeftCLM ℂ χ (f : 𝓢'(E,ℂ)) φ = ∫ x, φ x * v x) :
    (fun x => χ x * f x) =ᵐ[volume] v := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp f).locallyIntegrable (by norm_num) |>.continuous_mul χ.continuous)
    hv.locallyIntegrable
  intro φ hφ hφc
  let Φ : 𝓢(E,ℂ) := (hφc.comp_left (show Complex.ofRealCLM 0=0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hφ)
  have he := hrep Φ
  rw [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply] at he
  convert he using 1 <;> apply integral_congr_ae <;> filter_upwards [] with x
  · rw [SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth]
    simp [Φ, smul_eq_mul, mul_assoc, mul_left_comm]
  · simp [Φ]

theorem patch (f : Lp ℂ 2 (volume : Measure E))
    (hlocal : ∀ x₀ : E, ∃ χ : 𝓢(E,ℂ), (χ : E → ℂ) =ᶠ[𝓝 x₀] 1 ∧
      ∃ v : E → ℂ, ContDiff ℝ ∞ v ∧
        ∀ φ : 𝓢(E,ℂ), smulLeftCLM ℂ χ (f : 𝓢'(E,ℂ)) φ = ∫ x, φ x * v x) :
    ∃ w : E → ℂ, ContDiff ℝ ∞ w ∧ (f : E → ℂ) =ᵐ[volume] w := by
  classical
  choose χ hχ v hv hrep using hlocal
  have hae (x : E) : (fun y => χ x y * f y) =ᵐ[volume] v x :=
    cutoff_rep_ae f (χ x) (v x) (hv x).continuous (hrep x)
  have hcompat (x y : E) : (fun z => χ y z * v x z) = (fun z => χ x z * v y z) := by
    apply Measure.eq_of_ae_eq (μ := volume) _ ((χ y).continuous.mul (hv x).continuous)
      ((χ x).continuous.mul (hv y).continuous)
    filter_upwards [hae x, hae y] with z hz₁ hz₂
    simp only [Pi.mul_apply]
    rw [←hz₁, ←hz₂]
    ring
  let w : E → ℂ := fun x => v x x
  have hpoint (x y : E) (hy : χ x y = 1) : w y = v x y := by
    have he := congrFun (hcompat x y) y
    have hyy : χ y y = 1 := (hχ y).self_of_nhds
    simpa only [hy,hyy,one_mul] using he.symm
  have hgerm (x : E) : w =ᶠ[𝓝 x] v x := by
    filter_upwards [hχ x] with y hy
    exact hpoint x y hy
  have hw : ContDiff ℝ ∞ w := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (hv x).contDiffAt.congr_of_eventuallyEq (hgerm x)
  refine ⟨w,hw,?_⟩
  let U : E → Set E := fun x => interior {y | χ x y = 1}
  have hxU (x : E) : x ∈ U x := mem_interior_iff_mem_nhds.mpr (hχ x)
  obtain ⟨S,hS,hcover⟩ := isLindelof_univ.elim_countable_subcover U
    (fun _ => isOpen_interior) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨x,hxU x⟩)
  let : Countable S := hS.to_subtype
  have hloc (x : E) : ∀ᵐ y ∂volume, y ∈ U x → f y = w y := by
    filter_upwards [hae x] with y hy
    intro hyU
    have hχy : χ x y = 1 := (show y ∈ {z | χ x z = 1} from interior_subset hyU)
    rw [hχy,one_mul] at hy
    exact hy.trans (hpoint x y hχy).symm
  have hall : ∀ᵐ y ∂volume, ∀ x : S, y ∈ U x → f y = w y :=
    (ae_all_iff).mpr (fun x => hloc x)
  filter_upwards [hall] with y hy
  obtain ⟨x,hxS,hxy⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ y))
  exact hy ⟨x,hxS⟩ hxy

end SmoothPatching

namespace DistributionExpansion
section
open MeasureTheory TemperedDistribution LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma derivative_add (v : E) (u w : 𝓢'(E,F)) :
    ∂_{v} (u+w) = ∂_{v} u + ∂_{v} w :=
  map_add (lineDerivOpCLM ℂ 𝓢'(E,F) v) u w

lemma eval_differentiate (v : E) (ts : List (Term E)) (u : 𝓢'(E,F)) :
    eval (differentiate v ts) u = ∂_{v} (eval ts u) := by
  induction ts with
  | nil => simp [differentiate]
  | cons t ts ih =>
    change evalTerm (∂_{v} t.1,t.2) u +
      (evalTerm (t.1,v::t.2) u + eval (differentiate v ts) u) =
      ∂_{v} (evalTerm t u + eval ts u)
    rw [ih,derivative_add]
    simp only [evalTerm,derivative_cons,derivative_multiply]
    abel

lemma derivative_multiply_expansion (vs : List E) (a : 𝓢(E,ℂ)) (u : 𝓢'(E,F)) :
    derivative vs (smulLeftCLM F a u) =
      smulLeftCLM F a (derivative vs u) + eval (lower vs a) u := by
  induction vs with
  | nil => simp [lower]
  | cons v vs ih =>
    simp only [derivative_cons,lower,eval_cons,eval_differentiate]
    rw [ih]
    rw [derivative_add,derivative_multiply]
    simp only [evalTerm]
    abel

lemma lower_order (vs : List E) (a : 𝓢(E,ℂ)) :
    ∀ t ∈ lower vs a, t.2.length < vs.length := by
  induction vs with
  | nil => simp [lower]
  | cons v vs ih =>
    intro t ht
    simp only [lower,List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp
    · obtain ⟨t',ht',ht⟩ := List.mem_flatMap.mp ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      · exact (ih t' ht').trans (Nat.lt_succ_self _)
      · simpa using Nat.succ_lt_succ (ih t' ht')

end

section
open TemperedDistribution LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma eval_append (ts ss : List (Term E)) (u : 𝓢'(E,F)) :
    eval (ts++ss) u = eval ts u + eval ss u := by
  simp [eval]

lemma eval_flatten (tss : List (List (Term E))) (u : 𝓢'(E,F)) :
    eval tss.flatten u = (tss.map (fun ts => eval ts u)).sum := by
  induction tss with
  | nil => rfl
  | cons ts tss ih =>
    simpa only [List.flatten_cons,eval_append,List.map_cons,List.sum_cons] using
      congrArg (fun z => eval ts u+z) ih

lemma eval_ofFn {N : ℕ} (ts : Fin N → Term E) (u : 𝓢'(E,F)) :
    eval (List.ofFn ts) u = ∑ i, evalTerm (ts i) u := by
  simp [eval,List.map_ofFn,List.sum_ofFn]

lemma eval_eq_sum (ts : List (Term E)) (u : 𝓢'(E,F)) :
    eval ts u = ∑ i : Fin ts.length, evalTerm ts[i.val] u := by
  simpa only [List.ofFn_getElem] using eval_ofFn (fun i : Fin ts.length => ts[i.val]) u

lemma eval_flatten_ofFn {N : ℕ} (tss : Fin N → List (Term E)) (u : 𝓢'(E,F)) :
    eval (List.ofFn tss).flatten u = ∑ i, eval (tss i) u := by
  rw [eval_flatten,List.map_ofFn,List.sum_ofFn]
  rfl

lemma divergence_expansion {N M : ℕ} (a : Fin N → 𝓢(E,ℂ)) (vs : Fin N → List E)
    (b : Fin M → 𝓢(E,ℂ)) (ws : Fin M → List E) (u : 𝓢'(E,F)) :
    divergence a vs u + divergence b ws u =
      (∑ i, smulLeftCLM F (a i) (derivative (vs i) u)) + eval (lowerTerms a vs b ws) u := by
  simp only [divergence,derivative_multiply_expansion,Finset.sum_add_distrib,
    lowerTerms,eval_append,eval_flatten_ofFn,eval_cons,evalTerm]
  abel

lemma lowerTerms_order {N M m : ℕ} (a : Fin N → 𝓢(E,ℂ)) (vs : Fin N → List E)
    (b : Fin M → 𝓢(E,ℂ)) (ws : Fin M → List E)
    (hvs : ∀ i, (vs i).length = m) (hws : ∀ i, (ws i).length < m) :
    ∀ t ∈ lowerTerms a vs b ws, t.2.length < m := by
  intro t ht
  simp only [lowerTerms,List.mem_append,List.mem_flatten,List.mem_ofFn] at ht
  rcases ht with ⟨ts,⟨i,rfl⟩,ht⟩ | ⟨ts,⟨i,rfl⟩,ht⟩
  · simpa only [hvs i] using lower_order (vs i) (a i) t ht
  · simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hws i
    · exact (lower_order (ws i) (b i) t ht).trans (hws i)

end

open MeasureTheory TemperedDistribution LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma derivative_pairing (vs : List E) (u : 𝓢'(E,ℂ)) (φ : 𝓢(E,ℂ)) :
    derivative vs u φ = (-1:ℂ)^vs.length * u (testDerivative vs φ) := by
  induction vs generalizing φ with
  | nil => simp [testDerivative]
  | cons v vs ih =>
    rw [derivative_cons,TemperedDistribution.lineDerivOp_apply_apply,ih]
    simp only [List.length_cons,pow_succ,testDerivative,ContinuousLinearMap.comp_apply,map_neg]
    change (-1:ℂ)^vs.length * -u (testDerivative vs (∂_{v} φ)) =
      ((-1:ℂ)^vs.length * -1) * u (testDerivative vs (∂_{v} φ))
    ring

end DistributionExpansion

namespace SchwartzOperator
section
open LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma derivative_append (vs ws : List E) (φ : 𝓢(E,ℂ)) :
    derivative (vs++ws) φ = derivative vs (derivative ws φ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.cons_append,derivative_cons,ih]

lemma operator_append (ts ss : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (ts++ss) φ = operator ts φ + operator ss φ := by
  simp only [operator,List.map_append,List.sum_append,add_apply]

lemma operator_map_coefficient (a : 𝓢(E,ℂ)) (ts : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (ts.map (fun t => (product a t.1,t.2))) φ = product a (operator ts φ) := by
  induction ts with
  | nil => simp [product]
  | cons t ts ih =>
    simp only [List.map_cons,operator_cons,term_apply,ih]
    ext x
    simp only [product_apply,add_apply]
    ring

lemma operator_differentiate (v : E) (ts : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (differentiate v ts) φ = ∂_{v} (operator ts φ) := by
  induction ts with
  | nil => simp [differentiate]
  | cons t ts ih =>
    change term (∂_{v} t.1,t.2) φ +
      (term (t.1,v::t.2) φ + operator (differentiate v ts) φ) =
      ∂_{v} (term t φ + operator ts φ)
    rw [ih,lineDerivOp_add]
    simp only [term_apply,derivative_cons,schwartz_product_derivative]
    abel

lemma derivative_product (vs : List E) (a φ : 𝓢(E,ℂ)) :
    derivative vs (product a φ) = product a (derivative vs φ) + operator (lower vs a) φ := by
  induction vs with
  | nil => simp [lower]
  | cons v vs ih =>
    simp only [derivative_cons,lower,operator_cons,operator_differentiate]
    rw [ih,lineDerivOp_add,schwartz_product_derivative]
    simp only [term_apply]
    abel

lemma lower_order (vs : List E) (a : 𝓢(E,ℂ)) :
    ∀ t ∈ lower vs a, t.2.length < vs.length := by
  induction vs with
  | nil => simp [lower]
  | cons v vs ih =>
    intro t ht
    simp only [lower,List.mem_cons] at ht
    rcases ht with rfl | ht
    · simp
    · obtain ⟨t',ht',ht⟩ := List.mem_flatMap.mp ht
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
      rcases ht with rfl | rfl
      · exact (ih t' ht').trans (Nat.lt_succ_self _)
      · simpa using Nat.succ_lt_succ (ih t' ht')

lemma operator_append_directions (ts : List (Term E)) (ws : List E) (φ : 𝓢(E,ℂ)) :
    operator (ts.map (fun t => (t.1,t.2++ws))) φ = operator ts (derivative ws φ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons,operator_cons,term_apply,derivative_append,ih]

lemma operator_composeTerm (t s : Term E) (φ : 𝓢(E,ℂ)) :
    operator (composeTerm t s) φ = term t (term s φ) := by
  rw [composeTerm,operator_cons,term_apply,term_apply,term_apply,derivative_append,
    derivative_product]
  have he : composeLower t s =
      ((lower t.2 s.1).map (fun r => (r.1,r.2++s.2))).map (fun r => (product t.1 r.1,r.2)) := by
    simp [composeLower,List.map_map,Function.comp_def]
  rw [he,operator_map_coefficient,operator_append_directions]
  ext x
  simp only [product_apply,add_apply]
  ring

lemma composeLower_order (t s : Term E) :
    ∀ r ∈ composeLower t s, r.2.length < t.2.length+s.2.length := by
  intro r hr
  change r ∈ (lower t.2 s.1).map (fun r => (product t.1 r.1,r.2++s.2)) at hr
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
  simpa only [List.length_append] using Nat.add_lt_add_right (lower_order t.2 s.1 z hz) s.2.length

lemma composeTerm_order (t s : Term E) :
    ∀ r ∈ composeTerm t s, r.2.length ≤ t.2.length+s.2.length := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp
  · exact (composeLower_order t s r hr).le


lemma operator_compose_fixed (t : Term E) (ss : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (ss.flatMap (composeTerm t)) φ = term t (operator ss φ) := by
  induction ss with
  | nil => simp [product]
  | cons s ss ih =>
    simp only [List.flatMap_cons,operator_append,operator_composeTerm,ih,operator_cons,map_add]

lemma operator_compose (ts ss : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (compose ts ss) φ = operator ts (operator ss φ) := by
  induction ts with
  | nil => simp [compose]
  | cons t ts ih =>
    simp only [compose,List.flatMap_cons,operator_append,operator_compose_fixed,operator_cons]
    exact congrArg (fun z => term t (operator ss φ)+z) ih

lemma operator_compose_split_fixed (t : Term E) (ss : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (ss.flatMap (composeTerm t)) φ =
      operator (ss.map (fun s => (product t.1 s.1,t.2++s.2))) φ +
      operator (ss.flatMap (composeLower t)) φ := by
  induction ss with
  | nil => simp [product]
  | cons s ss ih =>
    simp only [List.flatMap_cons,List.map_cons,operator_append,operator_cons,composeTerm,ih]
    abel

lemma operator_compose_split (ts ss : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (compose ts ss) φ =
      operator (principalCompose ts ss) φ + operator (lowerCompose ts ss) φ := by
  induction ts with
  | nil => simp [compose,principalCompose,lowerCompose]
  | cons t ts ih =>
    simp only [compose,principalCompose,lowerCompose,List.flatMap_cons,operator_append]
    rw [operator_compose_split_fixed]
    change (_+_) + operator (compose ts ss) φ = _
    rw [ih]
    abel

lemma principalCompose_order {m n : ℕ} (ts ss : List (Term E))
    (ht : ∀ t ∈ ts, t.2.length=m) (hs : ∀ s ∈ ss, s.2.length=n) :
    ∀ r ∈ principalCompose ts ss, r.2.length=m+n := by
  intro r hr
  change r ∈ ts.flatMap _ at hr
  obtain ⟨t,hts,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨s,hss,rfl⟩ := List.mem_map.mp hr
  simp [ht t hts,hs s hss]

lemma lowerCompose_order {m n : ℕ} (ts ss : List (Term E))
    (ht : ∀ t ∈ ts, t.2.length=m) (hs : ∀ s ∈ ss, s.2.length=n) :
    ∀ r ∈ lowerCompose ts ss, r.2.length < m+n := by
  intro r hr
  change r ∈ ts.flatMap _ at hr
  obtain ⟨t,hts,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨s,hss,hr⟩ := List.mem_flatMap.mp hr
  simpa only [ht t hts,hs s hss] using composeLower_order t s r hr

lemma compose_order {m n : ℕ} (ts ss : List (Term E))
    (ht : ∀ t ∈ ts, t.2.length ≤ m) (hs : ∀ s ∈ ss, s.2.length ≤ n) :
    ∀ r ∈ compose ts ss, r.2.length ≤ m+n := by
  intro r hr
  change r ∈ ts.flatMap _ at hr
  obtain ⟨t,hts,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨s,hss,hr⟩ := List.mem_flatMap.mp hr
  exact (composeTerm_order t s r hr).trans (Nat.add_le_add (ht t hts) (hs s hss))

lemma operator_negTerms (ts : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (negTerms ts) φ = -operator ts φ := by
  induction ts with
  | nil => simp [negTerms]
  | cons t ts ih =>
    change term (-t.1,t.2) φ + operator (negTerms ts) φ = -(term t φ + operator ts φ)
    rw [ih]
    ext x
    simp only [term_apply,product_apply,add_apply,neg_apply]
    ring

lemma secondOrder_square_expansion (ts us : List (Term E)) (φ : 𝓢(E,ℂ)) :
    operator (ts++us) (operator (ts++us) φ-φ) =
      operator (principalCompose ts ts) φ + operator (secondOrderRemainder ts us) φ := by
  rw [operator_append,map_sub,map_sub]
  simp only [operator_append,map_add]
  rw [←operator_compose ts ts,←operator_compose ts us,←operator_compose us ts,
    ←operator_compose us us,operator_compose_split ts ts]
  simp only [secondOrderRemainder,operator_append,operator_negTerms]
  abel

lemma secondOrderRemainder_order (ts us : List (Term E))
    (ht : ∀ t ∈ ts, t.2.length=2) (hu : ∀ t ∈ us, t.2.length ≤ 1) :
    ∀ r ∈ secondOrderRemainder ts us, r.2.length < 4 := by
  intro r hr
  simp only [secondOrderRemainder,List.mem_append] at hr
  rcases hr with (((hr|hr)|hr)|hr)|hr
  · exact lowerCompose_order ts ts ht ht r hr
  · exact (compose_order ts us (fun t h => (ht t h).le) hu r hr).trans_lt (by decide)
  · exact (compose_order us ts hu (fun t h => (ht t h).le) r hr).trans_lt (by decide)
  · exact (compose_order us us hu hu r hr).trans_lt (by decide)
  · change r ∈ (ts++us).map _ at hr
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    rcases List.mem_append.mp hz with hz|hz
    · simp only [ht z hz]; decide
    · exact (hu z hz).trans_lt (by decide)

end

open MeasureTheory TemperedDistribution LocalDifferential LineDeriv
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma testDerivative_append (vs ws : List E) (φ : 𝓢(E,ℂ)) :
    DistributionExpansion.testDerivative (vs++ws) φ =
      DistributionExpansion.testDerivative ws (DistributionExpansion.testDerivative vs φ) := by
  induction vs generalizing φ with
  | nil => rfl
  | cons v vs ih =>
    simpa only [List.cons_append,DistributionExpansion.testDerivative,
      ContinuousLinearMap.comp_apply] using ih ((lineDerivOpCLM ℂ 𝓢(E,ℂ) v) φ)

lemma testDerivative_reverse (vs : List E) (φ : 𝓢(E,ℂ)) :
    DistributionExpansion.testDerivative vs.reverse φ = derivative vs φ := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [List.reverse_cons,testDerivative_append,ih]
    rfl

lemma adjointTerm_pairing (t : Term E) (u : 𝓢'(E,ℂ)) (φ : 𝓢(E,ℂ)) :
    adjointTerm t u φ = u (term t φ) := by
  rw [adjointTerm,DistributionExpansion.derivative_pairing,List.length_reverse,
    TemperedDistribution.smulLeftCLM_apply_apply,testDerivative_reverse]
  change (-1:ℂ)^t.2.length * u (product ((-1:ℂ)^t.2.length • t.1) (derivative t.2 φ)) = _
  have he : product ((-1:ℂ)^t.2.length • t.1) (derivative t.2 φ) =
      (-1:ℂ)^t.2.length • product t.1 (derivative t.2 φ) := by
    ext x
    simp [product_apply,smul_eq_mul,mul_assoc]
  rw [he,map_smul,smul_eq_mul,←mul_assoc,←mul_pow]
  simp only [neg_one_mul,neg_neg,one_pow,one_mul,term_apply]

lemma adjoint_pairing (ts : List (Term E)) (u : 𝓢'(E,ℂ)) (φ : 𝓢(E,ℂ)) :
    adjoint ts u φ = u (operator ts φ) := by
  induction ts with
  | nil => simp [adjoint]
  | cons t ts ih =>
    change adjointTerm t u φ + adjoint ts u φ = u (term t φ + operator ts φ)
    rw [adjointTerm_pairing,ih,map_add]

lemma adjoint_ofFn {N : ℕ} (ts : Fin N → Term E) (u : 𝓢'(E,ℂ)) :
    adjoint (List.ofFn ts) u = DistributionExpansion.divergence
      (fun i => (-1:ℂ)^(ts i).2.length • (ts i).1)
      (fun i => (ts i).2.reverse) u := by
  simp [adjoint,List.map_ofFn,List.sum_ofFn,DistributionExpansion.divergence,adjointTerm]

lemma adjoint_eq_divergence (ts : List (Term E)) (u : 𝓢'(E,ℂ)) :
    adjoint ts u = DistributionExpansion.divergence
      (fun i : Fin ts.length => (-1:ℂ)^(ts[i.val]).2.length • (ts[i.val]).1)
      (fun i : Fin ts.length => (ts[i.val]).2.reverse) u := by
  simpa only [List.ofFn_getElem] using adjoint_ofFn (fun i : Fin ts.length => ts[i.val]) u

lemma localized_adjoint_vanishes (ts ss : List (Term E)) (χ : 𝓢(E,ℂ)) (u : 𝓢'(E,ℂ))
    (hweak : ∀ φ : 𝓢(E,ℂ), u (operator ts (product χ φ) + operator ss (product χ φ)) = 0) :
    smulLeftCLM ℂ χ (adjoint ts u + adjoint ss u) = 0 := by
  ext φ
  rw [TemperedDistribution.smulLeftCLM_apply_apply,add_apply,
    adjoint_pairing,adjoint_pairing,←map_add]
  exact hweak φ

end SchwartzOperator

namespace LocalSymbol
section
open Function
open scoped Real ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker, Sébastien Gouëzel

The following temperate growth theorem is adapted from Mathlib.Analysis.Distribution.TemperateGrowth.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Distribution/TemperateGrowth.lean

This code has been modified.
-/

lemma rpow_growth {f : E → ℝ} (hf : f.HasTemperateGrowth) (hf_one : ∀ x, 1 ≤ f x)
    (r : ℝ) : (fun x => f x ^ r).HasTemperateGrowth := by

  set t := {y : ℝ | 1 / 2 < y}
  have ht : Set.range f ⊆ t := by
    rintro - ⟨y, rfl⟩
    simp only [Set.mem_ofPred_eq, t]
    exact lt_of_lt_of_le (by norm_num) (hf_one y)
  have hdiff : ContDiffOn ℝ ∞ (fun x ↦ x ^ r) t :=
    contDiffOn_fun_id.rpow_const_of_ne fun x hx ↦ (lt_trans (by norm_num) hx).ne'
  have hunique : UniqueDiffOn ℝ t := (isOpen_lt' (1 / 2)).uniqueDiffOn
  apply HasTemperateGrowth.comp' ht hunique hdiff _ hf

  intro N

  obtain ⟨k, hk⟩ := exists_nat_ge (max r <| (N - r) * Real.log 2 / (Real.log (3 / 2)))
  have hk₁ : r ≤ k := le_sup_left.trans hk
  have hk₂ : Real.log 2 * (N - r) ≤ (Real.log (3 / 2)) * k := by
    have := le_sup_right.trans hk
    field_simp at this
    grind
  use k, ∑ k ∈ Finset.range (N + 1), ‖Polynomial.eval r (descPochhammer ℝ k)‖, by positivity
  intro n hn x hx
  have : ContDiffAt ℝ n (fun x ↦ x ^ r) x :=
    Real.contDiffAt_rpow_const <| Or.inl (lt_trans (by norm_num) hx).ne'

  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hunique this hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul]
  gcongr 1
  · have : n ∈ Finset.range (N + 1) := by grind
    apply Finset.single_le_sum (fun _ _ ↦ by positivity) this

  have hx' : 1 / 2 < x := by simpa [t] using hx
  have hx'' : 0 < x := lt_of_lt_of_le (by norm_num) hx'.le
  simp only [Real.norm_eq_abs]
  apply (Real.abs_rpow_le_abs_rpow _ _).trans

  by_cases! h : 0 ≤ r - n
  · have : r - n ≤ k := by simpa using hk₁.trans (by simp)
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow (by positivity) (by simp) h).trans
      (Real.rpow_le_rpow_of_exponent_le (by simp) this)
  have h : 0 < n - r := by grind
  calc

    _ = x ^ (-(n - r)) := by
      rw [neg_sub]
      congr
      simpa using hx''.le
    _ ≤ (2 : ℝ) ^ (n - r) := by
      simp only [one_div, Set.mem_ofPred_eq, t] at hx
      rw [Real.rpow_neg_eq_inv_rpow]
      gcongr
      exact ((inv_lt_comm₀ hx'' (by norm_num)).mpr hx).le
    _ = Real.exp (Real.log 2 * (n - r)) := by
      rw [Real.rpow_def_of_pos]
      norm_num
    _ ≤ Real.exp (Real.log (3 / 2) * k) := by
      gcongr 1
      apply le_trans _ hk₂
      gcongr
    _ ≤ (3 / 2) ^ k := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos]
      norm_num
    _ ≤ _ := by
      gcongr
      grind

lemma quadratic_growth (A : E →L[ℝ] E) : (quadratic A).HasTemperateGrowth := by
  unfold quadratic
  exact (innerSL ℝ).bilinear_hasTemperateGrowth (by fun_prop) A.hasTemperateGrowth

lemma inverseSymbol_growth (A : E →L[ℝ] E) : (inverseSymbol A).HasTemperateGrowth := by
  have hf : (fun x => 1+quadratic A x^2).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).add ((quadratic_growth A).pow 2)
  have hp := rpow_growth hf (by intro x; nlinarith [sq_nonneg (quadratic A x)]) (-1)
  convert (Complex.ofRealCLM.hasTemperateGrowth).comp hp using 1
  ext x
  simp [inverseSymbol, Real.rpow_neg_one]

lemma inverse_identity (A : E →L[ℝ] E) (x : E) :
    regularized A x * inverseSymbol A x = 1 := by
  have hp : 0 < 1+quadratic A x^2 := by positivity
  change (1+Complex.ofReal (quadratic A x)^2) *
    Complex.ofReal ((1+quadratic A x^2)⁻¹) = 1
  rw [←Complex.ofReal_pow, ←Complex.ofReal_one, ←Complex.ofReal_add,
    ←Complex.ofReal_mul, mul_inv_cancel₀ hp.ne']

lemma inverse_order_bound (A : E →L[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : ∀ x, c*‖x‖^2 ≤ quadratic A x) (x : E) :
    (1+‖x‖^2)^((4:ℝ)/2) * ‖inverseSymbol A x‖ ≤ 2*(1+c⁻¹^2) := by
  have h1 : 0 < 1+quadratic A x^2 := by positivity
  have h2 : 0 ≤ quadratic A x := (by positivity : 0 ≤ c*‖x‖^2).trans (hA x)
  have h3 : ‖x‖^2 ≤ c⁻¹*quadratic A x := by
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hc).mpr
    simpa [mul_comm] using hA x
  have h4 : ‖x‖^4 ≤ c⁻¹^2*quadratic A x^2 := by
    nlinarith [(sq_le_sq₀ (by positivity : 0 ≤ ‖x‖^2) (by positivity : 0 ≤ c⁻¹*quadratic A x)).mpr h3]
  have h5 : (1+‖x‖^2)^2 ≤ 2*(1+‖x‖^4) := by nlinarith [sq_nonneg (1-‖x‖^2)]
  have hb : (1+‖x‖^2)^2 ≤ (2*(1+c⁻¹^2))*(1+quadratic A x^2) := by
    nlinarith [sq_nonneg c⁻¹, sq_nonneg (quadratic A x), mul_nonneg (sq_nonneg c⁻¹) (sq_nonneg (quadratic A x))]
  norm_num only [show (4:ℝ)/2=2 by norm_num, Real.rpow_two]
  rw [inverseSymbol, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    ←div_eq_mul_inv]
  exact (div_le_iff₀ h1).mpr hb

end

open Metric
open scoped Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_coercivity (A : E →L[ℝ] E)
    (hA : ∀ x : E, x ≠ 0 → 0 < quadratic A x) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c*‖x‖^2 ≤ quadratic A x := by
  obtain ⟨c,hc,hbound⟩ := (isCompact_sphere (0:E) 1).exists_forall_le'
    (quadratic_growth A).1.continuous.continuousOn (fun y hy => hA y (by
      intro he
      simp [he] at hy))
  refine ⟨c,hc,?_⟩
  intro x
  by_cases hx : x=0
  · simp [hx,quadratic]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hxunit : ‖x‖⁻¹ • x ∈ sphere (0:E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hn]
  have he := hbound _ hxunit
  have hq : quadratic A (‖x‖⁻¹ • x) = ‖x‖⁻¹^2 * quadratic A x := by
    simp only [quadratic, map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hq] at he
  have hp := mul_le_mul_of_nonneg_right he (sq_nonneg ‖x‖)
  have heq : (‖x‖⁻¹^2 * quadratic A x) * ‖x‖^2 = quadratic A x := by
    field_simp [hn]
  rwa [heq] at hp

end LocalSymbol

namespace FourthOrderSymbol
open LocalDifferential LocalSymbol
open scoped BigOperators Real
variable {E : Type*} {ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

lemma symbol_append (vs ws : List E) (x : E) :
    symbol (vs++ws) x = symbol vs x * symbol ws x := by
  induction vs with
  | nil => simp [symbol]
  | cons v vs ih => simp only [List.cons_append,symbol,ih]; ring

end FourthOrderSymbol

namespace SchwartzOperator
section
open LocalDifferential FourthOrderSymbol
open scoped SchwartzMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma symbol_reverse (vs : List E) (ξ : E) :
    LocalDifferential.symbol vs.reverse ξ = LocalDifferential.symbol vs ξ := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [List.reverse_cons,symbol_append,ih]
    simp only [LocalDifferential.symbol]
    ring

lemma testSymbol_append (ts ss : List (Term E)) (x ξ : E) :
    testSymbol (ts++ss) x ξ = testSymbol ts x ξ + testSymbol ss x ξ := by
  simp [testSymbol]

lemma testSymbol_principal_fixed (t : Term E) (ss : List (Term E)) (x ξ : E) :
    testSymbol (ss.map (fun s => (product t.1 s.1,t.2++s.2))) x ξ =
      (t.1 x * LocalDifferential.symbol t.2 ξ) * testSymbol ss x ξ := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons,testSymbol_cons,ih,product_apply,symbol_append]
    ring

lemma testSymbol_principalCompose (ts ss : List (Term E)) (x ξ : E) :
    testSymbol (principalCompose ts ss) x ξ = testSymbol ts x ξ * testSymbol ss x ξ := by
  induction ts with
  | nil => simp [principalCompose]
  | cons t ts ih =>
    change testSymbol (_ ++ principalCompose ts ss) x ξ = _
    rw [testSymbol_append,testSymbol_principal_fixed,ih,testSymbol_cons,add_mul]

lemma testSymbol_ofFn {N : ℕ} (ts : Fin N → Term E) (x ξ : E) :
    testSymbol (List.ofFn ts) x ξ = ∑ i, (ts i).1 x * LocalDifferential.symbol (ts i).2 ξ := by
  simp [testSymbol,List.map_ofFn,List.sum_ofFn]

lemma testSymbol_eq_sum (ts : List (Term E)) (x ξ : E) :
    testSymbol ts x ξ = ∑ i : Fin ts.length, (ts[i.val]).1 x *
      LocalDifferential.symbol (ts[i.val]).2 ξ := by
  simpa only [List.ofFn_getElem] using testSymbol_ofFn (fun i : Fin ts.length => ts[i.val]) x ξ

end

open MeasureTheory TemperedDistribution LocalDifferential LocalOperator
open scoped SchwartzMap Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem smooth_of_weak_square (f : Lp ℂ 2 (volume : Measure E))
    (hlocal : ∀ x₀ : E, ∃ ts us : List (Term E), ∃ A : E →L[ℝ] E,
      (∀ t ∈ ts, t.2.length = 2) ∧ (∀ t ∈ us, t.2.length ≤ 1) ∧
      (∀ ξ : E, ξ ≠ 0 → 0 < LocalSymbol.quadratic A ξ) ∧
      (∀ ξ, testSymbol ts x₀ ξ = (LocalSymbol.quadratic A ξ : ℂ)) ∧
      ∃ ψ : 𝓢(E,ℂ), (ψ : E → ℂ) =ᶠ[𝓝 x₀] 1 ∧
        ∀ φ : 𝓢(E,ℂ), (f : 𝓢'(E,ℂ))
          (operator (ts++us) (operator (ts++us) (product ψ φ) - product ψ φ)) = 0) :
    ∃ w : E → ℂ, ContDiff ℝ ∞ w ∧ (f : E → ℂ) =ᵐ[volume] w := by
  classical
  apply SmoothPatching.patch f
  apply LocalElliptic.local_smooth_cutoffs
  intro n x₀
  obtain ⟨ts,us,A,ht,hu,hA,hsym,ψ,hψ,hweak⟩ := hlocal x₀
  let ps := principalCompose ts ts
  let rs := secondOrderRemainder ts us
  have hp : ∀ t ∈ ps, t.2.length = 4 := principalCompose_order ts ts ht ht
  have hr : ∀ t ∈ rs, t.2.length < 4 := secondOrderRemainder_order ts us ht hu
  let a : Fin ps.length → 𝓢(E,ℂ) := fun i => (-1:ℂ)^(ps[i.val]).2.length • (ps[i.val]).1
  let vs : Fin ps.length → List E := fun i => (ps[i.val]).2.reverse
  let b : Fin rs.length → 𝓢(E,ℂ) := fun i => (-1:ℂ)^(rs[i.val]).2.length • (rs[i.val]).1
  let ws : Fin rs.length → List E := fun i => (rs[i.val]).2.reverse
  have hvs (i : Fin ps.length) : (vs i).length = 4 := by
    simpa only [vs,List.length_reverse] using hp _ (List.getElem_mem i.isLt)
  have hws (i : Fin rs.length) : (ws i).length < 4 := by
    simpa only [ws,List.length_reverse] using hr _ (List.getElem_mem i.isLt)
  have hsymbol (ξ : E) : frozenSymbol (fun i => a i x₀) vs ξ = LocalSymbol.regularized A ξ := by
    change 1 + (∑ i : Fin ps.length, a i x₀ * LocalDifferential.symbol (vs i) ξ) = _
    have hsum : (∑ i : Fin ps.length, a i x₀ * LocalDifferential.symbol (vs i) ξ) =
        testSymbol ps x₀ ξ := by
      rw [testSymbol_eq_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi4 := hp _ (List.getElem_mem i.isLt)
      norm_num [a,vs,hi4,symbol_reverse]
    rw [hsum]
    change 1+testSymbol (principalCompose ts ts) x₀ ξ = _
    rw [testSymbol_principalCompose,hsym]
    simp only [LocalSymbol.regularized,LocalSymbol.principal]
    ring
  obtain ⟨c,hc,hcA⟩ := LocalSymbol.exists_coercivity A hA
  have hinv (ξ : E) : frozenSymbol (fun i => a i x₀) vs ξ * LocalSymbol.inverseSymbol A ξ = 1 := by
    rw [hsymbol]
    exact LocalSymbol.inverse_identity A ξ
  have hbq (ξ : E) : LocalPeetre.weight (4:ℝ) ξ * ‖LocalSymbol.inverseSymbol A ξ‖ ≤ 2*(1+c⁻¹^2) :=
    LocalSymbol.inverse_order_bound A hc hcA ξ
  let ls := DistributionExpansion.lowerTerms a vs b ws
  let d : Fin ls.length → 𝓢(E,ℂ) := fun i => (ls[i.val]).1
  let zs : Fin ls.length → List E := fun i => (ls[i.val]).2
  have hzs (i : Fin ls.length) : (zs i).length < 4 :=
    DistributionExpansion.lowerTerms_order a vs b ws hvs hws _ (List.getElem_mem i.isLt)
  have he : LocalOperator.operator a vs (f : 𝓢'(E,ℂ)) +
      LocalOperator.operator d zs (f : 𝓢'(E,ℂ)) = adjoint ps (f : 𝓢'(E,ℂ)) +
        adjoint rs (f : 𝓢'(E,ℂ)) := by
    rw [adjoint_eq_divergence,adjoint_eq_divergence]
    change _ = DistributionExpansion.divergence a vs _ + DistributionExpansion.divergence b ws _
    rw [DistributionExpansion.divergence_expansion,LocalOperator.operator_apply,
      LocalOperator.operator_apply,DistributionExpansion.eval_eq_sum]
    rfl
  have hf : MemSobolev 0 2 (f : 𝓢'(E,ℂ)) := memSobolev_zero_iff.mpr ⟨f,rfl⟩
  apply LocalElliptic.all_orders_at (m:=4) (by decide) a d x₀ vs zs hvs hzs
    (LocalSymbol.inverseSymbol_growth A) (by positivity : 0 ≤ 2*(1+c⁻¹^2)) hinv hbq
    (LocalElliptic.at_of_memSobolev hf x₀) _ n
  refine ⟨ψ,hψ,?_⟩
  rw [he]
  apply localized_adjoint_vanishes
  intro φ
  simpa only [secondOrder_square_expansion] using hweak φ

end SchwartzOperator

namespace SmoothOperator
section
open LocalDifferential Filter
open scoped SchwartzMap Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma derivative_smooth (vs : List E) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (derivative vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact (ih.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const

lemma derivative_eq_schwartz (vs : List E) (φ : 𝓢(E,ℂ)) :
    derivative vs (φ : E → ℂ) = (SchwartzOperator.derivative vs φ : E → ℂ) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    ext x
    simp only [derivative,ih,SchwartzOperator.derivative_cons,SchwartzMap.lineDerivOp_apply_eq_fderiv]

lemma derivative_support (vs : List E) (f : E → ℂ) :
    tsupport (derivative vs f) ⊆ tsupport f := by
  induction vs with
  | nil => exact Set.Subset.rfl
  | cons v vs ih =>
    apply Set.Subset.trans _ ((tsupport_fderiv_subset ℝ).trans ih)
    apply closure_mono
    intro x hx
    change fderiv ℝ (derivative vs f) x ≠ 0
    intro hz
    exact hx (by simp [derivative,hz])

lemma operator_smooth (ts : List (Term E)) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (operator ts f) := by
  induction ts with
  | nil => exact contDiff_const
  | cons t ts ih => exact (t.1.smooth.mul (derivative_smooth t.2 hf)).add ih

lemma operator_support (ts : List (Term E)) (f : E → ℂ) :
    tsupport (operator ts f) ⊆ tsupport f := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    change tsupport ((fun x => t.1 x * derivative t.2 f x) + operator ts f) ⊆ _
    exact (tsupport_add _ _).trans (Set.union_subset
      (tsupport_mul_subset_right.trans (derivative_support t.2 f)) ih)

lemma operator_compact (ts : List (Term E)) {f : E → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (operator ts f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (operator_support ts f)

lemma localize_apply (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ) (t : Term E) (x : E) :
    (localizeTerm χ hχ t).1 x = χ x * t.1 x := rfl

lemma localize_operator (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ) (ts : List (Term E)) (φ : 𝓢(E,ℂ)) :
    (SchwartzOperator.operator (localize χ hχ ts) φ : E → ℂ) =
      fun x => χ x * operator ts φ x := by
  induction ts with
  | nil => ext; simp [localize]
  | cons t ts ih =>
    ext x
    change SchwartzOperator.term (localizeTerm χ hχ t) φ x +
      SchwartzOperator.operator (localize χ hχ ts) φ x = _
    rw [SchwartzOperator.term_apply,product_apply,localize_apply,congrFun ih]
    rw [operator_cons,Pi.add_apply,←derivative_eq_schwartz]
    change (χ x * t.1 x) * derivative t.2 φ x + χ x * operator ts φ x = _
    ring

lemma localize_operator_eq (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ) (ts : List (Term E))
    (φ : 𝓢(E,ℂ)) (heq : ∀ x ∈ tsupport φ, χ x = 1) :
    (SchwartzOperator.operator (localize χ hχ ts) φ : E → ℂ) = operator ts φ := by
  rw [localize_operator]
  ext x
  by_cases hx : x ∈ tsupport φ
  · rw [heq x hx,one_mul]
  · have hz : operator ts φ x = 0 := by
      apply Function.notMem_support.mp
      intro hz
      exact hx (operator_support ts φ (subset_tsupport _ hz))
    simp [hz]

lemma localize_append (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ) (ts ss : List (Term E)) :
    localize χ hχ (ts++ss) = localize χ hχ ts ++ localize χ hχ ss := List.map_append

lemma localize_square (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ) (ts : List (Term E))
    (φ : 𝓢(E,ℂ)) (heq : ∀ x ∈ tsupport φ, χ x = 1) :
    (SchwartzOperator.operator (localize χ hχ ts)
      (SchwartzOperator.operator (localize χ hχ ts) φ - φ) : E → ℂ) =
      operator ts (operator ts φ - φ) := by
  have hfirst := localize_operator_eq χ hχ ts φ heq
  have hsecond : ∀ x ∈ tsupport (SchwartzOperator.operator (localize χ hχ ts) φ - φ), χ x = 1 := by
    intro x hx
    have hsub : ((SchwartzOperator.operator (localize χ hχ ts) φ - φ : 𝓢(E,ℂ)) : E → ℂ) =
        operator ts φ - φ := by ext y; exact congrArg (fun z => z-φ y) (congrFun hfirst y)
    rw [hsub] at hx
    exact heq x ((tsupport_sub _ _).trans (Set.union_subset (operator_support ts φ) Set.Subset.rfl) hx)
  rw [localize_operator_eq χ hχ ts _ hsecond]
  congr 1
  ext y
  exact congrArg (fun z => z-φ y) (congrFun hfirst y)

end

open MeasureTheory LocalDifferential Filter Metric TemperedDistribution
open scoped SchwartzMap Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma localize_symbol (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ) (ts : List (Term E)) (x ξ : E) :
    SchwartzOperator.testSymbol (localize χ hχ ts) x ξ = χ x * testSymbol ts x ξ := by
  induction ts with
  | nil => simp [localize,testSymbol]
  | cons t ts ih =>
    change SchwartzOperator.testSymbol (localizeTerm χ hχ t :: localize χ hχ ts) x ξ = _
    rw [SchwartzOperator.testSymbol_cons,localize_apply,ih]
    change (χ x * t.1 x) * LocalDifferential.symbol t.2 ξ + χ x * testSymbol ts x ξ =
      χ x * (t.1 x * LocalDifferential.symbol t.2 ξ + testSymbol ts x ξ)
    ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma localize_order {m : ℕ} (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ)
    (ts : List (Term E)) (hts : ∀ t ∈ ts, t.2.length = m) :
    ∀ t ∈ localize χ hχ ts, t.2.length = m := by
  intro t ht
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
  exact hts z hz

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma localize_order_le {m : ℕ} (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport χ)
    (ts : List (Term E)) (hts : ∀ t ∈ ts, t.2.length ≤ m) :
    ∀ t ∈ localize χ hχ ts, t.2.length ≤ m := by
  intro t ht
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht
  exact hts z hz

omit [MeasurableSpace E] [BorelSpace E] in

lemma local_cutoff_pair (x₀ : E) :
    ∃ ψ χ : 𝓢(E,ℂ), HasCompactSupport ψ ∧ HasCompactSupport χ ∧
      (ψ : E → ℂ) =ᶠ[𝓝 x₀] 1 ∧ χ x₀ = 1 ∧ ∀ x ∈ tsupport ψ, χ x = 1 := by
  let p : ContDiffBump x₀ := ⟨1/2,1,by norm_num,by norm_num⟩
  let c : ContDiffBump x₀ := ⟨2,3,by norm_num,by norm_num⟩
  let ψ : 𝓢(E,ℂ) := (p.hasCompactSupport.comp_left (show Complex.ofReal (0:ℝ)=0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp p.contDiff)
  let χ : 𝓢(E,ℂ) := (c.hasCompactSupport.comp_left (show Complex.ofReal (0:ℝ)=0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp c.contDiff)
  have hψs : tsupport ψ = closedBall x₀ 1 := by
    change tsupport (Complex.ofReal ∘ (p : E → ℝ)) = _
    rw [tsupport_comp_eq (by simp),p.tsupport_eq]
  have hχs : tsupport χ = closedBall x₀ 3 := by
    change tsupport (Complex.ofReal ∘ (c : E → ℝ)) = _
    rw [tsupport_comp_eq (by simp),c.tsupport_eq]
  refine ⟨ψ,χ,?_,?_,?_,?_,?_⟩
  · rw [HasCompactSupport,hψs]; exact isCompact_closedBall _ _
  · rw [HasCompactSupport,hχs]; exact isCompact_closedBall _ _
  · filter_upwards [p.eventuallyEq_one_of_mem_ball (mem_ball_self (by norm_num : (0:ℝ)<1/2))] with y hy
    change Complex.ofReal (p y) = 1
    simp only [hy,Pi.one_apply,Complex.ofReal_one]
  · change Complex.ofReal (c x₀) = 1
    rw [c.one_of_mem_closedBall (mem_closedBall_self (by norm_num : (0:ℝ)≤2))]
    rfl
  · intro x hx
    change Complex.ofReal (c x) = 1
    rw [c.one_of_mem_closedBall ?_]
    · rfl
    · rw [hψs,mem_closedBall] at hx
      exact mem_closedBall.mpr (hx.trans (by norm_num : (1:ℝ)≤2))

theorem smooth_of_compact_weak_square (ts us : List (Term E))
    (ht : ∀ t ∈ ts, t.2.length = 2) (hu : ∀ t ∈ us, t.2.length ≤ 1)
    (hprincipal : ∀ x₀ : E, ∃ A : E →L[ℝ] E,
      (∀ ξ : E, ξ ≠ 0 → 0 < LocalSymbol.quadratic A ξ) ∧
      ∀ ξ, testSymbol ts x₀ ξ = (LocalSymbol.quadratic A ξ : ℂ))
    (f : Lp ℂ 2 (volume : Measure E))
    (hweak : ∀ φ : E → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, operator (ts++us) (operator (ts++us) φ - φ) x * f x) = 0) :
    ∃ w : E → ℂ, ContDiff ℝ ∞ w ∧ (f : E → ℂ) =ᵐ[volume] w := by
  apply SchwartzOperator.smooth_of_weak_square f
  intro x₀
  obtain ⟨ψ,χ,hψc,hχc,hψ,hχ₀,hχ⟩ := local_cutoff_pair x₀
  obtain ⟨A,hA,hsym⟩ := hprincipal x₀
  refine ⟨localize χ hχc ts,localize χ hχc us,A,
    localize_order χ hχc ts ht,localize_order_le χ hχc us hu,hA,?_,ψ,hψ,?_⟩
  · intro ξ
    rw [localize_symbol,hχ₀,one_mul,hsym]
  · intro φ
    rw [Lp.toTemperedDistribution_apply]
    have hcover : ∀ x ∈ tsupport (product ψ φ), χ x = 1 := by
      intro x hx
      apply hχ
      simp only [show (product ψ φ : E → ℂ) = (fun y => ψ y * φ y) from funext (product_apply ψ φ)] at hx
      exact tsupport_mul_subset_left hx
    have heq := localize_square χ hχc (ts++us) (product ψ φ) hcover
    rw [localize_append] at heq
    simp_rw [congrFun heq]
    apply hweak _ (product ψ φ).smooth'
    change HasCompactSupport ((product ψ φ) : E → ℂ)
    rw [show (product ψ φ : E → ℂ) = (fun y => ψ y * φ y) from funext (product_apply ψ φ)]
    exact hψc.mul_right

end SmoothOperator

namespace RealSmoothOperator
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma derivative_re (vs : List E) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    (fun x => (SmoothOperator.derivative vs f x).re) = derivative vs (fun x => (f x).re) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change (fun x => (fderiv ℝ (SmoothOperator.derivative vs f) x v).re) =
      fun x => fderiv ℝ (derivative vs (fun x => (f x).re)) x v
    rw [← ih]
    ext x
    have hh := (Complex.reCLM.hasFDerivAt.comp x
      ((SmoothOperator.derivative_smooth vs hf).differentiable (by simp) x).hasFDerivAt).fderiv
    exact (congrArg (fun L => L v) hh).symm

lemma derivative_im (vs : List E) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    (fun x => (SmoothOperator.derivative vs f x).im) = derivative vs (fun x => (f x).im) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change (fun x => (fderiv ℝ (SmoothOperator.derivative vs f) x v).im) =
      fun x => fderiv ℝ (derivative vs (fun x => (f x).im)) x v
    rw [← ih]
    ext x
    have hh := (Complex.imCLM.hasFDerivAt.comp x
      ((SmoothOperator.derivative_smooth vs hf).differentiable (by simp) x).hasFDerivAt).fderiv
    exact (congrArg (fun L => L v) hh).symm

lemma operator_re (ts : List (Term E)) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    (fun x => (SmoothOperator.operator (complexify ts) f x).re) =
      operator ts (fun x => (f x).re) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    ext x
    change ((t.1 x : ℂ) * SmoothOperator.derivative t.2 f x +
      SmoothOperator.operator (complexify ts) f x).re = _
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [congrFun (derivative_re t.2 hf) x,congrFun ih x]
    rfl

lemma operator_im (ts : List (Term E)) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    (fun x => (SmoothOperator.operator (complexify ts) f x).im) =
      operator ts (fun x => (f x).im) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    ext x
    change ((t.1 x : ℂ) * SmoothOperator.derivative t.2 f x +
      SmoothOperator.operator (complexify ts) f x).im = _
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    rw [congrFun (derivative_im t.2 hf) x,congrFun ih x]
    rfl

lemma square_re (ts : List (Term E)) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    (fun x => (SmoothOperator.operator (complexify ts)
      (SmoothOperator.operator (complexify ts) f-f) x).re) =
      operator ts (operator ts (fun x => (f x).re) - (fun x => (f x).re)) := by
  rw [operator_re ts (f := SmoothOperator.operator (complexify ts) f-f)
    ((SmoothOperator.operator_smooth (complexify ts) hf).sub hf)]
  congr 1
  ext x
  simp only [Pi.sub_apply,Complex.sub_re]
  rw [congrFun (operator_re ts hf) x]

lemma square_im (ts : List (Term E)) {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    (fun x => (SmoothOperator.operator (complexify ts)
      (SmoothOperator.operator (complexify ts) f-f) x).im) =
      operator ts (operator ts (fun x => (f x).im) - (fun x => (f x).im)) := by
  rw [operator_im ts (f := SmoothOperator.operator (complexify ts) f-f)
    ((SmoothOperator.operator_smooth (complexify ts) hf).sub hf)]
  congr 1
  ext x
  simp only [Pi.sub_apply,Complex.sub_im]
  rw [congrFun (operator_im ts hf) x]

variable [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ] [BorelSpace E]

lemma complex_weak_square (ts : List (Term E)) (f : E → ℝ) (hf : MemLp f 2 μ)
    (hw : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, operator ts (operator ts φ-φ) x*f x ∂μ)=0)
    {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, SmoothOperator.operator (complexify ts)
      (SmoothOperator.operator (complexify ts) φ-φ) x*(f x : ℂ) ∂μ)=0 := by
  let q := SmoothOperator.operator (complexify ts) (SmoothOperator.operator (complexify ts) φ-φ)
  have hqs : ContDiff ℝ ∞ q :=
    SmoothOperator.operator_smooth _ ((SmoothOperator.operator_smooth _ hφ).sub hφ)
  have hqc : HasCompactSupport q :=
    SmoothOperator.operator_compact _ ((SmoothOperator.operator_compact _ hc).sub hc)
  have hqi : Integrable (fun x => q x*(f x : ℂ)) μ :=
    (hqs.continuous.memLp_of_hasCompactSupport hqc (p:=2)).integrable_mul hf.ofReal
  have hr := hw (fun x => (φ x).re) (Complex.reCLM.contDiff.comp hφ)
    (hc.comp_left (show Complex.re (0:ℂ)=0 from rfl))
  have hi := hw (fun x => (φ x).im) (Complex.imCLM.contDiff.comp hφ)
    (hc.comp_left (show Complex.im (0:ℂ)=0 from rfl))
  apply Complex.ext
  · change Complex.reCLM (∫ x, q x*(f x : ℂ) ∂μ) = 0
    rw [← Complex.reCLM.integral_comp_comm hqi]
    change (∫ x, (q x*(f x : ℂ)).re ∂μ) = 0
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    simpa only [q,congrFun (square_re ts hφ)] using hr
  · change Complex.imCLM (∫ x, q x*(f x : ℂ) ∂μ) = 0
    rw [← Complex.imCLM.integral_comp_comm hqi]
    change (∫ x, (q x*(f x : ℂ)).im ∂μ) = 0
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
    simpa only [q,congrFun (square_im ts hφ)] using hi

end

section
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma complexify_append (ts us : List (Term E)) :
    complexify (ts++us) = complexify ts ++ complexify us := List.map_append

theorem smooth_of_weak_square (ts us : List (Term E))
    (ht : ∀ t ∈ ts, t.2.length = 2) (hu : ∀ t ∈ us, t.2.length ≤ 1)
    (hsym : ∀ x₀ : E, ∃ A : E →L[ℝ] E,
      (∀ ξ : E, ξ ≠ 0 → 0 < LocalSymbol.quadratic A ξ) ∧
      ∀ ξ, SmoothOperator.testSymbol (complexify ts) x₀ ξ = (LocalSymbol.quadratic A ξ : ℂ))
    (f : E → ℝ) (hf : MemLp f 2 (volume : Measure E))
    (hw : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, operator (ts++us) (operator (ts++us) φ-φ) x*f x)=0) :
    ∃ w : E → ℝ, ContDiff ℝ ∞ w ∧ f =ᵐ[volume] w := by
  let fc : Lp ℂ 2 (volume : Measure E) := hf.ofReal.toLp (fun x => (f x : ℂ))
  have hfc : (fc : E → ℂ) =ᵐ[volume] (fun x => (f x : ℂ)) := hf.ofReal.coeFn_toLp
  have htc : ∀ t ∈ complexify ts, t.2.length = 2 := by
    intro t ht'
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht'
    exact ht z hz
  have huc : ∀ t ∈ complexify us, t.2.length ≤ 1 := by
    intro t ht'
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ht'
    exact hu z hz
  obtain ⟨w,hwc,hwe⟩ := SmoothOperator.smooth_of_compact_weak_square
    (complexify ts) (complexify us) htc huc hsym fc (by
      intro φ hφ hφc
      rw [← complexify_append]
      calc
        _ = ∫ x, SmoothOperator.operator (complexify (ts++us))
          (SmoothOperator.operator (complexify (ts++us)) φ-φ) x * (f x : ℂ) := by
            apply integral_congr_ae
            filter_upwards [hfc] with x hx
            rw [hx]
        _ = 0 := complex_weak_square volume (ts++us) f hf hw hφ hφc)
  refine ⟨fun x => (w x).re,Complex.reCLM.contDiff.comp hwc,?_⟩
  filter_upwards [hfc,hwe] with x hx hy
  have hh := congrArg Complex.re (hx.symm.trans hy)
  exact hh

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma derivative_push (e : E ≃L[ℝ] F) (vs : List E) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    derivative (vs.map e) (f ∘ e.symm) = derivative vs f ∘ e.symm := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.map_cons,derivative]
    rw [ih]
    ext x
    have hh := (((derivative_smooth vs hf).differentiable (by simp) (e.symm x)).hasFDerivAt.comp x e.symm.hasFDerivAt).fderiv
    rw [hh]
    simp

lemma operator_push (e : E ≃L[ℝ] F) (ts : List (Term E)) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    operator (push e ts) (f ∘ e.symm) = operator ts f ∘ e.symm := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    ext x
    change t.1 (e.symm x) * derivative (List.map e t.2) (f ∘ e.symm) x +
      operator (push e ts) (f ∘ e.symm) x = _
    rw [congrFun (derivative_push e t.2 hf) x,congrFun ih x]
    rfl

lemma square_push (e : E ≃L[ℝ] F) (ts : List (Term E)) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    operator (push e ts) (operator (push e ts) (f ∘ e.symm) - (f ∘ e.symm)) =
      operator ts (operator ts f-f) ∘ e.symm := by
  rw [operator_push e ts hf]
  have he : operator ts f ∘ e.symm - f ∘ e.symm = (operator ts f-f) ∘ e.symm := rfl
  rw [he,operator_push e ts (f := operator ts f-f) ((operator_smooth ts hf).sub hf)]

end

variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma push_append (e : E ≃L[ℝ] F) (ts us : List (Term E)) :
    push e (ts++us) = push e ts ++ push e us := List.map_append
end RealSmoothOperator
namespace MatrixOperator
section
open MeasureTheory RealSmoothOperator Matrix
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma principal_length (τ : Space ι → Matrix ι ι ℝ)
    (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) :
    ∀ t ∈ principal τ hτ, t.2.length = 2 := by
  intro t ht
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp ht
  rfl
lemma drift_length : ∀ t ∈ (drift : List (Term (Space ι))), t.2.length ≤ 1 := by
  intro t ht
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
  norm_num

lemma operator_actual (τ : Space ι → Matrix ι ι ℝ)
    (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (f : Space ι → ℝ) :
    operator (principal τ hτ++drift) f = A τ f := by
  ext x
  simp only [operator,principal,drift,List.map_append,List.sum_append,List.map_map,
    Function.comp_def,Finset.sum_map_toList,Finset.sum_apply,Pi.add_apply,
    Fintype.sum_prod_type,derivative,e,A,neg_mul,Finset.sum_neg_distrib]
  ring

lemma principal_push_length (τ : Space ι → Matrix ι ι ℝ)
    (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) :
    ∀ t ∈ push coordinates (principal τ hτ), t.2.length = 2 := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  simpa [pushTerm] using principal_length τ hτ s hs

lemma drift_push_length :
    ∀ t ∈ push (coordinates (ι:=ι)) drift, t.2.length ≤ 1 := by
  intro t ht
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ht
  simpa [pushTerm] using drift_length s hs

lemma inner_coordinates_e (ξ : Euclid ι) (i : ι) :
    inner ℝ ξ (coordinates (e i)) = ξ.ofLp i := by
  change inner ℝ ξ (EuclideanSpace.single i 1) = _
  simp [EuclideanSpace.inner_single_right]

lemma symbol_two (ξ : Euclid ι) (i j : ι) :
    LocalDifferential.symbol [coordinates (e i),coordinates (e j)] ξ =
      (-(4*Real.pi^2*(ξ.ofLp i)*(ξ.ofLp j)) : ℝ) := by
  simp only [LocalDifferential.symbol,inner_coordinates_e,one_mul]
  push_cast
  calc
    _ = 4*(Real.pi : ℂ)^2*((ξ.ofLp i : ℂ)*(ξ.ofLp j : ℂ))*Complex.I^2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

lemma principal_symbol (τ : Space ι → Matrix ι ι ℝ)
    (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (x ξ : Euclid ι) :
    SmoothOperator.testSymbol (complexify (push coordinates (principal τ hτ))) x ξ =
      (4*Real.pi^2*(ξ.ofLp ⬝ᵥ (τ x.ofLp *ᵥ ξ.ofLp)) : ℝ) := by
  simp only [SmoothOperator.testSymbol,complexify,push,principal,List.map_map,
    Function.comp_def,Finset.sum_map_toList,Fintype.sum_prod_type]
  change (∑ i, ∑ j, ((-τ x.ofLp i j : ℝ) : ℂ) *
    LocalDifferential.symbol [coordinates (e i),coordinates (e j)] ξ) = _
  simp_rw [symbol_two]
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,Complex.ofReal_sum,Complex.ofReal_mul,
    Complex.ofReal_neg]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

lemma quadratic_frozen (τ : Matrix ι ι ℝ) (ξ : Euclid ι) :
    LocalSymbol.quadratic (frozen τ) ξ = 4*Real.pi^2*(ξ.ofLp ⬝ᵥ (τ *ᵥ ξ.ofLp)) := by
  change inner ℝ ξ ((4*Real.pi^2) • WithLp.toLp 2 (τ *ᵥ ξ.ofLp)) = _
  rw [inner_smul_right,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]

lemma principal_elliptic (τ : Space ι → Matrix ι ι ℝ)
    (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j)) (hp : ∀ x, (τ x).PosDef) :
    ∀ x₀ : Euclid ι, ∃ B : Euclid ι →L[ℝ] Euclid ι,
      (∀ ξ : Euclid ι, ξ ≠ 0 → 0 < LocalSymbol.quadratic B ξ) ∧
      ∀ ξ, SmoothOperator.testSymbol (complexify (push coordinates (principal τ hτ))) x₀ ξ =
        (LocalSymbol.quadratic B ξ : ℂ) := by
  intro x₀
  refine ⟨frozen (τ x₀.ofLp),?_,?_⟩
  · intro ξ hξ
    rw [quadratic_frozen]
    apply mul_pos (by positivity)
    have hne : ξ.ofLp ≠ 0 := by
      intro he
      apply hξ
      exact (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective he
    simpa only [star_trivial] using (hp x₀.ofLp).dotProduct_mulVec_pos hne
  · intro ξ
    rw [principal_symbol,quadratic_frozen]

lemma weak_coordinate_square
    (τ : Space ι → Matrix ι ι ℝ) (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j))
    (f : Space ι → ℝ)
    (hw : ∀ ψ : Space ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space ι, A τ (A τ ψ-ψ) x*f x)=0)
    (ψ : Euclid ι → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Euclid ι, operator (push coordinates (principal τ hτ)++push coordinates drift)
      (operator (push coordinates (principal τ hτ)++push coordinates drift) ψ-ψ) x *
      f (coordinates.symm x)) = 0 := by
  let φ : Space ι → ℝ := ψ ∘ coordinates
  have hφ : ContDiff ℝ ∞ φ := hψ.comp (coordinates (ι:=ι)).contDiff
  have hφc : HasCompactSupport φ := hc.comp_homeomorph coordinates.toHomeomorph
  have he : φ ∘ coordinates.symm = ψ := by ext x; simp [φ]
  have hs := square_push (E := Space ι) (F := Euclid ι) coordinates (principal τ hτ++drift) hφ
  rw [he,push_append] at hs
  simp only [operator_actual] at hs
  rw [hs]
  change (∫ x : Euclid ι, A τ (A τ φ-φ) (coordinates.symm x)*f (coordinates.symm x)) = 0
  have hm := (PiLp.volume_preserving_ofLp ι).integral_comp
    coordinates.symm.toHomeomorph.measurableEmbedding
    (fun x : Space ι => A τ (A τ φ-φ) x*f x)
  change (∫ x : Euclid ι, A τ (A τ φ-φ) (coordinates.symm x)*f (coordinates.symm x)) = _ at hm
  rw [hm]
  exact hw φ hφ hφc

end

open MeasureTheory RealSmoothOperator
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem smooth_of_weak_square
    (τ : Space ι → Matrix ι ι ℝ) (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j))
    (hp : ∀ x, (τ x).PosDef) (f : Space ι → ℝ) (hf : MemLp f 2 volume)
    (hw : ∀ ψ : Space ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x, A τ (A τ ψ-ψ) x*f x)=0) :
    ∃ w : Space ι → ℝ, ContDiff ℝ ∞ w ∧ f =ᵐ[volume] w := by
  let fc : Euclid ι → ℝ := f ∘ (coordinates (ι:=ι)).symm
  have hfc : MemLp fc 2 volume := hf.comp_measurePreserving (PiLp.volume_preserving_ofLp ι)
  obtain ⟨w,hws,hwe⟩ := RealSmoothOperator.smooth_of_weak_square (E := Euclid ι)
    (push (coordinates (ι:=ι)) (principal τ hτ)) (push (coordinates (ι:=ι)) (drift (ι:=ι)))
    (principal_push_length τ hτ) (drift_push_length (ι:=ι)) (principal_elliptic τ hτ hp) fc hfc (weak_coordinate_square τ hτ f hw)
  refine ⟨w ∘ (coordinates (ι:=ι)),hws.comp (coordinates (ι:=ι)).contDiff,?_⟩
  have hh := (PiLp.volume_preserving_toLp ι).quasiMeasurePreserving.ae hwe
  filter_upwards [hh] with x hx
  exact hx

end MatrixOperator

namespace WeightedRegularity
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [MeasurableSpace E]

lemma density_absolutelyContinuous (μ : Measure E) {ρ : E → ℝ}
    (hm : Measurable ρ) (hp : ∀ x, 0 < ρ x) : μ ≪ densityMeasure μ ρ := by
  exact withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hm).aemeasurable
    (Filter.Eventually.of_forall fun x => by exact (ENNReal.ofReal_pos.mpr (hp x)).ne')

lemma integral_density (μ : Measure E) {ρ : E → ℝ}
    (hm : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x) (f : E → ℝ) :
    (∫ x, f x ∂densityMeasure μ ρ) = ∫ x, ρ x*f x ∂μ := by
  have hh := integral_withDensity_eq_integral_toReal_smul
    (μ:=μ) (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hm)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f
  simpa only [densityMeasure,Function.comp_apply,ENNReal.toReal_ofReal (hp _),smul_eq_mul] using hh

lemma density_mul_memLp (μ : Measure E) {ρ : E → ℝ}
    (hm : Measurable ρ) (hp : ∀ x, 0 < ρ x) {C : ℝ} (hC : ∀ x, ρ x ≤ C)
    {g : E → ℝ} (hg : MemLp g 2 (densityMeasure μ ρ)) :
    MemLp (fun x => ρ x*g x) 2 μ := by
  have hga : AEStronglyMeasurable g μ := hg.aestronglyMeasurable.mono_ac
    (density_absolutelyContinuous μ hm hp)
  have ha : AEStronglyMeasurable (fun x => ρ x*g x) μ := hm.aestronglyMeasurable.mul hga
  apply (memLp_two_iff_integrable_sq ha).mpr
  have hi : Integrable (fun x => ρ x*(g x)^2) μ := by
    have hh := (integrable_withDensity_iff_integrable_smul'
      (ENNReal.measurable_ofReal.comp hm) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hg.integrable_sq
    simpa only [Function.comp_apply,ENNReal.toReal_ofReal (hp _).le,smul_eq_mul] using hh
  apply (hi.const_mul C).mono' (ha.pow 2)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb := mul_le_mul_of_nonneg_right (hC x) (mul_nonneg (hp x).le (sq_nonneg (g x)))
  change (ρ x*g x)^2 ≤ C*(ρ x*g x^2)
  nlinarith

lemma weighted_weak (μ : Measure E) {ρ : E → ℝ}
    (hm : Measurable ρ) (hp : ∀ x, 0 ≤ ρ x) (g q : E → ℝ)
    (h : (∫ x, q x*g x ∂densityMeasure μ ρ)=0) :
    (∫ x, q x*(ρ x*g x) ∂μ)=0 := by
  rw [integral_density μ hm hp] at h
  simpa only [mul_left_comm (ρ _) (q _)] using h

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]

omit [BorelSpace E] in
lemma smooth_density_quotient (μ : Measure E) {ρ g w : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hp : ∀ x, 0 < ρ x) (hw : ContDiff ℝ ∞ w)
    (he : (fun x => ρ x*g x) =ᵐ[μ] w) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ g =ᵐ[densityMeasure μ ρ] v := by
  refine ⟨fun x => w x/ρ x,hw.div hρ (fun x => (hp x).ne'),?_⟩
  apply (withDensity_absolutelyContinuous μ _).ae_le
  filter_upwards [he] with x hx
  rw [← hx,mul_div_cancel_left₀ _ (hp x).ne']

end WeightedRegularity

namespace MatrixOperator
open MeasureTheory WeightedRegularity
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem smooth_of_weighted_weak_square
    (τ : Space ι → Matrix ι ι ℝ) (hτ : ∀ i j, ContDiff ℝ ∞ (fun x => τ x i j))
    (hp : ∀ x, (τ x).PosDef) (ρ : Space ι → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρp : ∀ x, 0 < ρ x) {C : ℝ} (hρC : ∀ x, ρ x ≤ C)
    (f : Space ι → ℝ) (hf : MemLp f 2 (densityMeasure volume ρ))
    (hw : ∀ ψ : Space ι → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x, A τ (A τ ψ-ψ) x*f x ∂densityMeasure volume ρ)=0) :
    ∃ w : Space ι → ℝ, ContDiff ℝ ∞ w ∧ f =ᵐ[densityMeasure volume ρ] w := by
  have hf' := density_mul_memLp volume hρ.continuous.measurable hρp hρC hf
  obtain ⟨w,hws,hwe⟩ := smooth_of_weak_square τ hτ hp (fun x => ρ x*f x) hf' (by
    intro ψ hψ hc
    exact weighted_weak volume hρ.continuous.measurable (fun x => (hρp x).le)
      f (A τ (A τ ψ-ψ)) (hw ψ hψ hc))
  exact smooth_density_quotient volume hρ hρp hws hwe

end MatrixOperator
end

open MeasureTheory
open scoped Topology ContDiff

noncomputable section
namespace WeightedCalculus


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma smooth_weight {V : E → ℝ} (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (weight V) := hV.neg.exp


end WeightedCalculus

end

open Matrix
open scoped ContDiff Matrix.Norms.Elementwise

open scoped ContDiff Topology

noncomputable section

namespace MomentKernel

open MeasureTheory Matrix WeightedCalculus MomentCoordinates TargetCoordinates
open scoped ContDiff
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_A_eq (τ : Space ι → Matrix ι ι ℝ) (f : Space ι → ℝ) :
    MatrixOperator.A τ f = DensityEnergy.A τ f := rfl

theorem weak_kernel_smooth_oai {φ V : Space ι → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hV : ContDiff ℝ ∞ V) (hpos : ∀ z, (hess φ z).PosDef) {Z m : ℝ} (hZ : 0 < Z)
    (hVlower : ∀ x, m ≤ V x)
    (Φ : Space ι ≃ₜ Space ι) (hInv : ContDiff ℝ ∞ (Φ.symm : Space ι → Space ι))
    {g : Space ι → ℝ} (hg : MemLp g 2 (targetMeasure volume V Z))
    (hweak : ∀ f : Space ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, g x*DensityEnergy.A (MomentOperator.tau Φ φ)
        (DensityEnergy.A (MomentOperator.tau Φ φ) f-f) x ∂targetMeasure volume V Z) = 0) :
    ∃ w : Space ι → ℝ, ContDiff ℝ ∞ w ∧ g =ᵐ[targetMeasure volume V Z] w := by
  let ρ : Space ι → ℝ := fun x => weight V x/Z
  have hρ : ContDiff ℝ ∞ ρ := (smooth_weight hV).div_const Z
  have hρp (x : Space ι) : 0 < ρ x := div_pos (Real.exp_pos _) hZ
  have hρC (x : Space ι) : ρ x ≤ Real.exp (-m)/Z := by
    exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (hVlower x))) hZ.le
  have hw : ∀ f : Space ι → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∫ x, MatrixOperator.A (MomentOperator.tau Φ φ)
        (MatrixOperator.A (MomentOperator.tau Φ φ) f-f) x*g x ∂
          WeightedRegularity.densityMeasure volume ρ)=0 := by
    intro f hf hc
    have hμ : WeightedRegularity.densityMeasure volume ρ = targetMeasure volume V Z := rfl
    rw [hμ,matrix_A_eq,matrix_A_eq]
    change (∫ x, DensityEnergy.A (MomentOperator.tau Φ φ)
      (DensityEnergy.A (MomentOperator.tau Φ φ) f-f) x*g x ∂targetMeasure volume V Z)=0
    simpa only [mul_comm] using hweak f hf hc
  exact MatrixOperator.smooth_of_weighted_weak_square (ι:=ι)
    (MomentOperator.tau Φ φ) (smooth_tau hφ Φ hInv) (fun x => hpos (Φ.symm x))
    ρ hρ hρp hρC g hg hw


end MomentKernel

end

open Matrix
open scoped BigOperators Kronecker

open MeasureTheory
open scoped BigOperators

open scoped BigOperators InnerProductSpace Topology

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MomentKernel.weak_kernel_smooth_oai.{u_1} := @OAI.MomentKernel.weak_kernel_smooth_oai.{u_1}
