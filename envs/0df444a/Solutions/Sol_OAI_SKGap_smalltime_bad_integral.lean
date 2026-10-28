-- Prove2me | solution 1 for OAI.SKGap.smalltime_bad_integral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:49:44.440674+00:00
-- url     : https://prove2.me/submissions/8eb4fe66-1c36-4f17-b9d0-857ca7f646c7

import Mathlib
import Definitions.Def_OAIQ072A000

section
-- module Solutions.OAIQ072_SK.Compat
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_KernelDensity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
variable {ι κ : Type*} [Fintype κ]

theorem additive_noise_lintegral (μ : Measure (ι → ℝ)) [SFinite μ]
    (φ : (κ → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (L : (ι → ℝ) → (κ → ℝ)) (hL : Measurable L)
    (F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1,L z.1+z.2) ∂μ.prod ((volume : Measure (κ → ℝ)).withDensity φ)) =
      ∫⁻ y, ∫⁻ x, φ (y-L x)*F (x,y) ∂μ ∂volume := by
  rw [lintegral_prod _ (by fun_prop)]
  have he (x : ι → ℝ) :
      (∫⁻ e, F (x,L x+e) ∂(volume : Measure (κ → ℝ)).withDensity φ)=
      ∫⁻ y, φ (y-L x)*F (x,y) ∂volume := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hφ (by fun_prop)]
    have hh := lintegral_add_left_eq_self
      (μ := (volume : Measure (κ → ℝ))) (fun y => φ (y-L x)*F (x,y)) (L x)
    simpa only [Pi.mul_apply,add_sub_cancel_left] using hh
  simp only [he]
  exact lintegral_lintegral_swap (by fun_prop)

theorem residual_density_lintegral (ρ : Measure (ι → ℝ)) [SFinite ρ]
    (p : (κ → ℝ) → ℝ≥0∞) (hp : Measurable p)
    (K : (κ → ℝ) → (ι → ℝ)) (hK : Measurable K)
    (F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F (z.1+K z.2,z.2) ∂ρ.prod ((volume : Measure (κ → ℝ)).withDensity p)) =
      ∫⁻ y, p y*(∫⁻ r, F (r+K y,y) ∂ρ) ∂volume := by
  rw [lintegral_prod_symm _ (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ hp (by fun_prop)]
  rfl

theorem kernel_test_ae (μ ρ : Measure (ι → ℝ)) [SFinite μ] [SFinite ρ]
    {φ p : (κ → ℝ) → ℝ≥0∞} (hφ : Measurable φ) (hp : Measurable p)
    {L : (ι → ℝ) → (κ → ℝ)} {K : (κ → ℝ) → (ι → ℝ)}
    (hL : Measurable L) (hK : Measurable K)
    (hjoint : (μ.prod ((volume : Measure (κ → ℝ)).withDensity φ)).map
      (fun z => (z.1,L z.1+z.2)) =
      (ρ.prod ((volume : Measure (κ → ℝ)).withDensity p)).map
        (fun z => (z.1+K z.2,z.2)))
    (f : (ι → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (fun y => ∫⁻ x, φ (y-L x)*f x ∂μ)=ᵐ[volume]
      (fun y => p y*(∫⁻ r, f (r+K y) ∂ρ)) := by
  have h1 : Measurable (fun y => ∫⁻ x, φ (y-L x)*f x ∂μ) := by fun_prop
  have h2 : Measurable (fun y => p y*(∫⁻ r, f (r+K y) ∂ρ)) := by fun_prop
  apply (withDensity_eq_iff_of_sigmaFinite h1.aemeasurable h2.aemeasurable).mp
  ext s hs
  rw [withDensity_apply _ hs,withDensity_apply _ hs]
  let F : (ι → ℝ) × (κ → ℝ) → ℝ≥0∞ := fun z => s.indicator (fun _ => f z.1) z.2
  have hF : Measurable F := by
    exact (hf.comp measurable_fst).indicator (hs.preimage measurable_snd)
  have hh := congrArg (fun ν => ∫⁻ z, F z ∂ν) hjoint
  rw [lintegral_map hF (by fun_prop),lintegral_map hF (by fun_prop),
    additive_noise_lintegral μ φ hφ L hL F hF,
    residual_density_lintegral ρ p hp K hK F hF] at hh
  have he1 (y : κ → ℝ) : (∫⁻ x, φ (y-L x)*F (x,y) ∂μ)=
      s.indicator (fun y => ∫⁻ x, φ (y-L x)*f x ∂μ) y := by
    by_cases hy : y ∈ s <;> simp [F,hy]
  have he2 (y : κ → ℝ) : p y*(∫⁻ r, F (r+K y,y) ∂ρ)=
      s.indicator (fun y => p y*(∫⁻ r, f (r+K y) ∂ρ)) y := by
    by_cases hy : y ∈ s <;> simp [F,hy]
  simp_rw [he1,he2] at hh
  simpa only [lintegral_indicator hs] using hh

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Brownian_ContinuousKernel
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal BoundedContinuousFunction
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
lemma integrable_bounded (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) :
    Integrable f μ := Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hC)

theorem continuous_kernel_posterior (μ ρ : Measure (ι → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ρ]
    {φ p : (κ → ℝ) → ℝ} (hφ : Continuous φ) (hp : Continuous p)
    (hφpos : ∀ y,0 ≤ φ y) (hppos : ∀ y,0 ≤ p y)
    {C : ℝ} (hC : 0 ≤ C) (hφC : ∀ y,φ y ≤ C)
    {L : (ι → ℝ) → (κ → ℝ)} {K : (κ → ℝ) → (ι → ℝ)}
    (hL : Continuous L) (hK : Continuous K)
    (hjoint : (μ.prod ((volume : Measure (κ → ℝ)).withDensity (fun y => ENNReal.ofReal (φ y)))).map
      (fun z => (z.1,L z.1+z.2)) =
      (ρ.prod ((volume : Measure (κ → ℝ)).withDensity (fun y => ENNReal.ofReal (p y)))).map
        (fun z => (z.1+K z.2,z.2))) (z : κ → ℝ) :
    μ.withDensity (fun x => ENNReal.ofReal (φ (z-L x))) =
      ENNReal.ofReal (p z) • ρ.map (fun r => r+K z) := by
  have hiφ (y : κ → ℝ) : Integrable (fun x => φ (y-L x)) μ :=
    integrable_bounded μ (by fun_prop) (fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hφpos _)]; exact hφC _)
  have := isFiniteMeasure_withDensity_ofReal (hiφ z).hasFiniteIntegral
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  let fr : (ι → ℝ) →ᵇ ℝ := ⟨⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩,
    f.map_bounded'⟩
  have hfr (x : ι → ℝ) : 0 ≤ fr x := (f x).coe_nonneg
  have hb (x : ι → ℝ) : ‖fr x‖ ≤ ‖fr‖ := fr.norm_coe_le_norm x
  have hi1 (y : κ → ℝ) : Integrable (fun x => φ (y-L x)*fr x) μ := by
    apply integrable_bounded μ (by fun_prop) (C := C*‖fr‖)
    intro x
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφpos _)]
    exact mul_le_mul (hφC _) (hb x) (norm_nonneg _) hC
  have hi2 (y : κ → ℝ) : Integrable (fun r => fr (r+K y)) ρ :=
    integrable_bounded ρ (by fun_prop) (fun r => hb _)
  have hc1 : Continuous (fun y => ∫ x, φ (y-L x)*fr x ∂μ) := by
    apply continuous_of_dominated (bound := fun _ => C*‖fr‖)
    · intro y; exact (hi1 y).aestronglyMeasurable
    · intro y; exact Filter.Eventually.of_forall (fun x => by
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (hφpos _)]
        exact mul_le_mul (hφC _) (hb x) (norm_nonneg _) hC)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall (fun x => by fun_prop)
  have hc2 : Continuous (fun y => ∫ r, fr (r+K y) ∂ρ) := by
    apply continuous_of_dominated (bound := fun _ => ‖fr‖)
    · intro y; exact (hi2 y).aestronglyMeasurable
    · intro y; exact Filter.Eventually.of_forall (fun r => hb _)
    · exact integrable_const _
    · exact Filter.Eventually.of_forall (fun r => by fun_prop)
  have he1 (y : κ → ℝ) :
      (∫⁻ x, ENNReal.ofReal (φ (y-L x))*(f x : ℝ≥0∞) ∂μ)=
      ENNReal.ofReal (∫ x, φ (y-L x)*fr x ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hi1 y) (Filter.Eventually.of_forall (fun x => mul_nonneg (hφpos _) (hfr x)))]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (hφpos _)]
    change _ * (f x : ℝ≥0∞) = _ * ENNReal.ofReal (f x : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
  have he2 (y : κ → ℝ) :
      ENNReal.ofReal (p y)*(∫⁻ r, (f (r+K y) : ℝ≥0∞) ∂ρ)=
      ENNReal.ofReal (p y*(∫ r, fr (r+K y) ∂ρ)) := by
    rw [ENNReal.ofReal_mul (hppos y),ofReal_integral_eq_lintegral_ofReal (hi2 y)
      (Filter.Eventually.of_forall (fun r => hfr _))]
    congr 1
    apply lintegral_congr
    intro r
    change (f (r+K y) : ℝ≥0∞) = ENNReal.ofReal (f (r+K y) : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
  have hae := kernel_test_ae μ ρ hφ.measurable.ennreal_ofReal hp.measurable.ennreal_ofReal
    hL.measurable hK.measurable hjoint (fun x => (f x : ℝ≥0∞)) (by fun_prop)
  simp only [he1,he2] at hae
  have hall := (Continuous.ae_eq_iff_eq (volume : Measure (κ → ℝ))
    (ENNReal.continuous_ofReal.comp hc1) (ENNReal.continuous_ofReal.comp (hp.mul hc2))).mp hae
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    lintegral_smul_measure,lintegral_map (by fun_prop) (by fun_prop)]
  change (∫⁻ x, ENNReal.ofReal (φ (z-L x))*(f x : ℝ≥0∞) ∂μ)=
    ENNReal.ofReal (p z)*(∫⁻ r, (f (r+K z) : ℝ≥0∞) ∂ρ)
  rw [he1,he2]
  exact congrFun hall z

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EmpiricalLaw
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma empiricalLaw_coe (y : ι → ℝ) : (empiricalLaw y : Measure ℝ) =
    (Fintype.card ι : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (y i) := rfl

lemma integrable_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) : Integrable f (empiricalLaw y : Measure ℝ) := by
  rw [empiricalLaw_coe]
  apply Integrable.smul_measure
  · exact integrable_finsetSum_measure.mpr (fun i _ => integrable_dirac (by simp))
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast ((Fintype.card_pos (α := ι)).ne'))

lemma integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂empiricalLaw y) = (Fintype.card ι : ℝ)⁻¹ * ∑ i, f (y i) := by
  rw [empiricalLaw_coe, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

lemma card_mul_integral_empiricalLaw (y : ι → ℝ) (f : ℝ → ℝ) :
    (Fintype.card ι : ℝ)*(∫ x, f x ∂empiricalLaw y) = ∑ i, f (y i) := by
  rw [integral_empiricalLaw, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := ι)).ne'), one_mul]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_NormalLogConst
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

variable {ι : Type*} [Fintype ι]

lemma exp_normalLogDensity (d : ℝ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    exp (normalLogDensity d s x) = gaussianPDFReal d s.toNNReal x := by
  have hsp : 0 < sqrt (2*Real.pi*s) := sqrt_pos.mpr (by positivity)
  have he : normalLogDensity d s x = -log (sqrt (2*Real.pi*s)) - (x-d)^2/(2*s) := by
    unfold normalLogDensity normalLogConst
    field_simp
    ring
  rw [he, sub_eq_add_neg, exp_add, exp_neg, exp_log hsp]
  simp only [gaussianPDFReal, Real.coe_toNNReal s hs.le]
  congr 1
  congr 1
  ring

lemma continuousOn_normalLogConst : ContinuousOn (fun p : ℝ×ℝ => normalLogConst p.1 p.2)
    {p | 0 < p.2} := by
  unfold normalLogConst
  apply ContinuousOn.sub
  · apply ContinuousOn.neg
    apply ContinuousOn.log
    · fun_prop
    · intro p hp
      have hp' : 0 < p.2 := hp
      exact (sqrt_pos.mpr (by positivity : 0 < 2*Real.pi*p.2)).ne'
  · exact (continuous_fst.pow 2).continuousOn.div (continuous_const.mul continuous_snd).continuousOn
      (fun p hp => mul_ne_zero (by norm_num) (ne_of_gt hp))

lemma normalLogDensity_sub_le (d' s' d s x : ℝ) :
    normalLogDensity d' s' x-normalLogDensity d s x ≤
      |normalLogConst d' s'-normalLogConst d s| + |d'/s'-d/s| *|x| +
        |1/(2*s')-1/(2*s)| *x^2 := by
  have hx := le_abs_self ((d'/s'-d/s)*x)
  rw [abs_mul] at hx
  have hq := neg_le_abs (1/(2*s')-1/(2*s))
  have hm := mul_le_mul_of_nonneg_right hq (sq_nonneg x)
  have hc := le_abs_self (normalLogConst d' s'-normalLogConst d s)
  have he : normalLogDensity d' s' x-normalLogDensity d s x =
      (normalLogConst d' s'-normalLogConst d s)+(d'/s'-d/s)*x -
        (1/(2*s')-1/(2*s))*x^2 := by
    unfold normalLogDensity
    ring
  rw [he]
  linarith

lemma normalLogDensity_sum_sub_le {y : ι → ℝ} {R : ℝ}
    (hy : ∑ i, (y i)^2 ≤ (Fintype.card ι : ℝ)*R) (d' s' d s : ℝ) :
    (∑ i, normalLogDensity d' s' (y i))-(∑ i, normalLogDensity d s (y i)) ≤
      (Fintype.card ι : ℝ) * (|normalLogConst d' s'-normalLogConst d s| +
        |d'/s'-d/s| *(1+R)+|1/(2*s')-1/(2*s)| *R) := by
  have hl : ∑ i, |y i| ≤ (Fintype.card ι : ℝ)*(1+R) := by
    calc
      _ ≤ ∑ i, (1+(y i)^2) := Finset.sum_le_sum (fun i _ => by
        nlinarith [sq_abs (y i), sq_nonneg (|y i|-1)])
      _ = (Fintype.card ι : ℝ) + ∑ i, (y i)^2 := by simp [Finset.sum_add_distrib]
      _ ≤ _ := by nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => normalLogDensity_sub_le d' s' d s (y i))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum] at hh
  have h1 := mul_le_mul_of_nonneg_left hl (abs_nonneg (d'/s'-d/s))
  have h2 := mul_le_mul_of_nonneg_left hy (abs_nonneg (1/(2*s')-1/(2*s)))
  calc
    _ ≤ _ := hh
    _ ≤ _ := by nlinarith

lemma productNormal_eq_exp (d : ℝ) {s : ℝ} (hs : 0 < s) (y : ι → ℝ) :
    productNormal d s y = exp (∑ i, normalLogDensity d s (y i)) := by
  rw [exp_sum]
  unfold productNormal
  apply Finset.prod_congr rfl
  intro i hi
  exact (exp_normalLogDensity d hs (y i)).symm

lemma productNormal_nonneg (d s : ℝ) (y : ι → ℝ) : 0 ≤ productNormal d s y :=
  Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg d s.toNNReal (y i))

lemma integrable_tiltedNormal (f : ℝ →ᵇ ℝ) (d : ℝ) (s : ℝ≥0) :
    Integrable (fun x => exp (f x)*gaussianPDFReal d s x) := by
  have h := (integrable_gaussianPDFReal d s).bdd_mul
    (continuous_exp.comp f.continuous).aestronglyMeasurable
    (c := exp ‖f‖) (ae_of_all _ (fun x => by
      dsimp only [Function.comp_def]
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))))
  exact h

lemma integral_tiltedNormal (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ≥0} (hs : s ≠ 0) :
    (∫ x, exp (f x)*gaussianPDFReal d s x) = ∫ x, exp (f x) ∂gaussianReal d s := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul, mul_comm]

lemma tiltedNormal_mass_pos (f : ℝ →ᵇ ℝ) (d : ℝ) (s : ℝ≥0) :
    0 < ∫ x, exp (f x) ∂gaussianReal d s := by
  have hi : Integrable (fun x => exp (f x)) (gaussianReal d s) := Integrable.of_bound
    (by fun_prop) (exp ‖f‖) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))))
  exact integral_pos_iff_support_of_nonneg (fun _ => (exp_pos _).le) hi |>.mpr
    (by simp [Function.support, (exp_pos _).ne'])

lemma product_tiltedNormal_integral (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ y : ι → ℝ, exp (∑ i, f (y i))*productNormal d s y) =
      exp ((Fintype.card ι : ℝ)*log (∫ x, exp (f x) ∂gaussianReal d s.toNNReal)) := by
  have hs' : s.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hs)
  have he (y : ι → ℝ) : exp (∑ i, f (y i))*productNormal d s y =
      ∏ i, (exp (f (y i))*gaussianPDFReal d s.toNNReal (y i)) := by
    rw [exp_sum, productNormal, Finset.prod_mul_distrib]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => exp (f x)*gaussianPDFReal d s.toNNReal x), integral_tiltedNormal f d hs',
    exp_nat_mul, exp_log (tiltedNormal_mass_pos f d s.toNNReal)]

lemma product_tiltedNormal_integrable (f : ℝ →ᵇ ℝ) (d s : ℝ) :
    Integrable (fun y : ι → ℝ => exp (∑ i, f (y i))*productNormal d s y) := by
  have h := Integrable.fintype_prod (fun _ : ι => integrable_tiltedNormal f d s.toNNReal)
  simpa only [exp_sum, productNormal, Finset.prod_mul_distrib, volume_pi] using h

end SKGap

namespace SKGap

lemma normalDensityError_self (R d s : ℝ) : normalDensityError R d s d s = 0 := by
  simp [normalDensityError]

lemma continuous_normalDensityError {X : Type*} [TopologicalSpace X]
    {d s : X → ℝ} (hd : Continuous d) (hs : Continuous s) (hspos : ∀ x, 0 < s x)
    (R d₀ s₀ : ℝ) : Continuous (fun x => normalDensityError R (d x) (s x) d₀ s₀) := by
  have hlog : Continuous (fun x => normalLogConst (d x) (s x)) :=
    continuousOn_normalLogConst.comp_continuous (hd.prodMk hs) (fun x => hspos x)
  have hdiv := hd.div hs (fun x => (hspos x).ne')
  have hinv : Continuous (fun x => (1 : ℝ)/(2*s x)) := continuous_const.div (continuous_const.mul hs) (fun x => mul_ne_zero (by norm_num) (hspos x).ne')
  exact ((hlog.sub continuous_const).abs.add ((hdiv.sub continuous_const).abs.mul continuous_const)).add
    ((hinv.sub continuous_const).abs.mul continuous_const)

theorem finite_gaussian_test_cover {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R r : ℝ)
    (hW : ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < r) :
    ∃ (C : Finset K) (f : K → ℝ →ᵇ ℝ), ∀ z ∈ K, ∃ x ∈ C,
      ψ z-(∫ y, f x y ∂P z)+normalDensityError R (d z) (s z) (d x) (s x)+
      log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal) < r := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose f hf using (fun x : K => hW x.1 x.2)
  let U (x : K) : Set K := {z | ψ z-(∫ y, f x y ∂P z)+
    normalDensityError R (d z) (s z) (d x) (s x)+
      log (∫ y, exp (f x y) ∂gaussianReal (d x) (s x).toNNReal) < r}
  have hU (x : K) : IsOpen (U x) := by
    apply isOpen_lt _ continuous_const
    have hint : Continuous (fun z : K => ∫ y, f x y ∂P z) :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (f x)).comp hP.domRestrict
    exact ((hψ.domRestrict.sub hint).add
      (continuous_normalDensityError hd.domRestrict hs.domRestrict
        (fun z : K => hpos z.1 z.2) R (d x) (s x))).add continuous_const
  have hcov : (univ : Set K) ⊆ ⋃ x : K, U x := by
    intro z _
    refine mem_iUnion.mpr ⟨z, ?_⟩
    change ψ z-(∫ y, f z y ∂P z)+normalDensityError R (d z) (s z) (d z) (s z)+
      log (∫ y, exp (f z y) ∂gaussianReal (d z) (s z).toNNReal) < r
    simpa only [normalDensityError_self, add_zero] using hf z
  obtain ⟨C,hC⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  refine ⟨C,f,?_⟩
  intro z hz
  have hh := hC (mem_univ (⟨z,hz⟩ : K))
  obtain ⟨x,hx⟩ := mem_iUnion.mp hh
  obtain ⟨hxC,hxU⟩ := mem_iUnion.mp hx
  exact ⟨x,hxC,hxU⟩

end SKGap
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianTiltMass
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
lemma gaussian_tilt_mass (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ} (hs : 0 < s) (r : ℝ) :
    (∫ y : ι → ℝ, exp ((Fintype.card ι : ℝ)*r -
      (Fintype.card ι : ℝ)*log (∫ x, exp (f x) ∂gaussianReal d s.toNNReal)) *
      (exp (∑ i, f (y i))*productNormal d s y)) = exp ((Fintype.card ι : ℝ)*r) := by
  rw [integral_const_mul, product_tiltedNormal_integral f d hs, ← exp_add]
  congr 1
  ring

theorem gaussian_covered_laplace {X : Type*} (C : Finset X) (f : X → ℝ →ᵇ ℝ)
    (d₀ s₀ : X → ℝ) (hs₀ : ∀ x ∈ C, 0 < s₀ x)
    (d s ψ : (ι → ℝ) → ℝ) (R r : ℝ) {E : Set (ι → ℝ)} (hE : MeasurableSet E)
    (hpos : ∀ y ∈ E, 0 < s y)
    (hmom : ∀ y ∈ E, ∑ i, (y i)^2 ≤ (Fintype.card ι : ℝ)*R)
    (hcover : ∀ y ∈ E, ∃ x ∈ C,
      ψ y-(∫ u, f x u ∂empiricalLaw y)+normalDensityError R (d y) (s y) (d₀ x) (s₀ x)+
        log (∫ u, exp (f x u) ∂gaussianReal (d₀ x) (s₀ x).toNNReal) < r) :
    (∫⁻ y in E, ENNReal.ofReal (exp ((Fintype.card ι : ℝ)*ψ y)*productNormal (d y) (s y) y)) ≤
      ENNReal.ofReal ((C.card : ℝ)*exp ((Fintype.card ι : ℝ)*r)) := by
  classical
  let F (x : X) (y : ι → ℝ) : ℝ :=
    exp ((Fintype.card ι : ℝ)*r-(Fintype.card ι : ℝ)*
      log (∫ u, exp (f x u) ∂gaussianReal (d₀ x) (s₀ x).toNNReal)) *
      (exp (∑ i, f x (y i))*productNormal (d₀ x) (s₀ x) y)
  have hFi (x : X) : Integrable (F x) :=
    (product_tiltedNormal_integrable (f x) (d₀ x) (s₀ x)).const_mul _
  have hFnn (x : X) (y : ι → ℝ) : 0 ≤ F x y :=
    mul_nonneg (exp_pos _).le (mul_nonneg (exp_pos _).le (productNormal_nonneg _ _ _))
  have hnorm (x : X) (hx : x ∈ C) : ∫ y, F x y = exp ((Fintype.card ι : ℝ)*r) :=
    gaussian_tilt_mass (f x) (d₀ x) (hs₀ x hx) r
  have hdom (y : ι → ℝ) (hy : y ∈ E) :
      exp ((Fintype.card ι : ℝ)*ψ y)*productNormal (d y) (s y) y ≤ ∑ x ∈ C, F x y := by
    obtain ⟨x,hx,hc⟩ := hcover y hy
    have hdens := normalLogDensity_sum_sub_le (hmom y hy) (d y) (s y) (d₀ x) (s₀ x)
    change _ ≤ (Fintype.card ι : ℝ)*normalDensityError R (d y) (s y) (d₀ x) (s₀ x) at hdens
    have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
    have hc' := mul_lt_mul_of_pos_left hc hn
    have hemp := card_mul_integral_empiricalLaw y (f x)
    have hsmall : exp ((Fintype.card ι : ℝ)*ψ y)*productNormal (d y) (s y) y ≤ F x y := by
      dsimp only [F]
      rw [productNormal_eq_exp _ (hpos y hy), productNormal_eq_exp _ (hs₀ x hx),
        ← exp_add, ← exp_add, ← exp_add]
      apply exp_le_exp.mpr
      nlinarith
    exact hsmall.trans (Finset.single_le_sum (fun a _ => hFnn a y) hx)
  have hsumI : Integrable (fun y => ∑ x ∈ C, F x y) := integrable_finsetSum C (fun x _ => hFi x)
  calc
    _ ≤ ∫⁻ y in E, ENNReal.ofReal (∑ x ∈ C, F x y) := lintegral_mono_ae
      ((ae_restrict_mem hE).mono (fun y hy => ENNReal.ofReal_le_ofReal (hdom y hy)))
    _ ≤ ∫⁻ y, ENNReal.ofReal (∑ x ∈ C, F x y) := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ENNReal.ofReal (∫ y, ∑ x ∈ C, F x y) :=
      (ofReal_integral_eq_lintegral_ofReal hsumI (ae_of_all _ (fun y => Finset.sum_nonneg (fun x _ => hFnn x y)))).symm
    _ = _ := by
      rw [integral_finsetSum C (fun x _ => hFi x)]
      simp_rw [Finset.sum_congr rfl hnorm]
      simp

end SKGap

namespace SKGap

theorem gaussian_compact_laplace {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R r : ℝ)
    (hW : ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < r) :
    ∃ M : ℕ, ∀ n : ℕ, ∀ hn : 0 < n, ∀ z : (Fin n → ℝ) → X,
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K) →
      (∀ y ∈ E, P (z y) = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*ψ (z y))*productNormal (d (z y)) (s (z y)) y)) ≤
        ENNReal.ofReal ((M:ℝ)*exp ((n:ℝ)*r)) := by
  classical
  obtain ⟨C,f,hC⟩ := finite_gaussian_test_cover hK hP hd hs hψ hpos R r hW
  refine ⟨C.card, ?_⟩
  intro n hn z E hE hz hemp hmom
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hh := gaussian_covered_laplace C f (fun x : K => d x) (fun x : K => s x)
      (fun x _ => hpos x x.2) (fun y => d (z y)) (fun y => s (z y))
      (fun y => ψ (z y)) R r hE (fun y hy => hpos (z y) (hz y hy))
      (by simpa only [Fintype.card_fin] using hmom) (fun y hy => by
        obtain ⟨x,hx,hcx⟩ := hC (z y) (hz y hy)
        rw [hemp y hy] at hcx
        exact ⟨x,hx,hcx⟩)
  simpa only [Fintype.card_fin] using hh

lemma absorb_finite_exponential_factor (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r : ℝ,
      (M:ℝ)*exp ((n:ℝ)*r) ≤ exp ((n:ℝ)*(r+ε)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (log ((M:ℝ)+1)/ε)
  refine ⟨N,?_⟩
  intro n hn r
  have hcast : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : log ((M:ℝ)+1) ≤ (n:ℝ)*ε := by
    have h := (div_lt_iff₀ hε).mp hN
    nlinarith
  have he : (M:ℝ) ≤ exp ((n:ℝ)*ε) := by
    have h := exp_le_exp.mpr hnlog
    rw [exp_log (by positivity)] at h
    linarith
  calc
    _ ≤ exp ((n:ℝ)*ε)*exp ((n:ℝ)*r) := mul_le_mul_of_nonneg_right he (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

theorem gaussian_compact_rate {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {P : X → ProbabilityMeasure ℝ} {d s ψ : X → ℝ}
    (hP : ContinuousOn P K) (hd : ContinuousOn d K) (hs : ContinuousOn s K)
    (hψ : ContinuousOn ψ K) (hpos : ∀ x ∈ K, 0 < s x) (R r : ℝ)
    (hW : ∀ x ∈ K, ∃ f : ℝ →ᵇ ℝ, ψ x-(∫ y, f y ∂P x)+
      log (∫ y, exp (f y) ∂gaussianReal (d x) (s x).toNNReal) < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ z : (Fin n → ℝ) → X,
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K) →
      (∀ y ∈ E, P (z y) = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*ψ (z y))*productNormal (d (z y)) (s (z y)) y)) ≤
        ENNReal.ofReal (exp ((n:ℝ)*(r+ε))) := by
  obtain ⟨M,hM⟩ := gaussian_compact_laplace hK hP hd hs hψ hpos R r hW
  obtain ⟨N,hN⟩ := absorb_finite_exponential_factor M hε
  refine ⟨N,?_⟩
  intro n hn hn' z E hE hz hemp hmom
  exact (hM n hn' z E hE hz hemp hmom).trans (ENNReal.ofReal_le_ofReal (hN n hn r))

end SKGap

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_EntropyEll
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
namespace SKGap

theorem entropyEll_hasDerivAt {u : ℝ} (hu : u < 1) :
    HasDerivAt entropyEll (u / (1 - u)) u := by
  have hd := ((((hasDerivAt_id u).const_sub 1).log (by linarith : 1 - u ≠ 0)).neg).sub
    (hasDerivAt_id u)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  field_simp [show 1 - u ≠ 0 by linarith]
  ring

theorem entropyEll_nonneg {u : ℝ} (hu : u < 1) : 0 ≤ entropyEll u := by
  have h := log_le_sub_one_of_pos (by linarith : 0 < 1 - u)
  dsimp [entropyEll]
  linarith

theorem entropyEll_le_half_sq_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    entropyEll u ≤ u ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x => x ^ 2 / 2 - entropyEll x
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (-x ^ 2 / (1 - x)) x := by
    convert! (((hasDerivAt_id x).pow 2).div_const 2).sub (entropyEll_hasDerivAt hx) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    field_simp [show 1 - x ≠ 0 by linarith]
    ring
  have hm : AntitoneOn f (Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · intro x hx
      exact (hd x (by simp only [mem_Iic] at hx; linarith)).continuousAt.continuousWithinAt
    · intro x hx
      have hx0 : x < 0 := by simpa only [interior_Iic, mem_Iio] using hx
      exact (hd x (by linarith)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx0 : x < 0 := by simpa only [interior_Iic, mem_Iio] using hx
      rw [(hd x (by linarith)).deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by linarith)
  have h := hm (show u ∈ Iic 0 from hu) (show (0 : ℝ) ∈ Iic 0 by simp) hu
  simpa [f, entropyEll] using h

theorem entropySlack_pos_of_neg {B u : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1) (hu : u < 0) :
    0 < entropySlack B u := by
  have he := mul_le_mul_of_nonneg_left (entropyEll_le_half_sq_of_nonpos hu.le) hB0
  have hs : 0 < u ^ 2 := sq_pos_of_ne_zero hu.ne
  dsimp [entropySlack]
  nlinarith

theorem value_le_of_deriv_nonneg {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Icc a b, 0 ≤ g x) : f a ≤ f b := by
  have hm : MonotoneOn f (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x (interior_subset hx)).deriv]
      exact hg x (interior_subset hx)
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem half_sq_le_entropyEll {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u ^ 2 / 2 ≤ entropyEll u := by
  let f : ℝ → ℝ := fun x => entropyEll x - x ^ 2 / 2
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (x ^ 2 / (1 - x)) x := by
    convert! (entropyEll_hasDerivAt hx).sub (((hasDerivAt_id x).pow 2).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    field_simp [show 1 - x ≠ 0 by linarith]
    ring
  have h := value_le_of_deriv_nonneg hu0 (fun x hx => hd x (hx.2.trans_lt hu1))
    (fun x hx => div_nonneg (sq_nonneg x) (by linarith [hx.2]))
  simpa [f, entropyEll] using h

theorem entropySlack_cubic_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u ^ 3 / 6 ≤ entropySlack (1 - u) u := by
  let f : ℝ → ℝ := fun x => entropySlack (1 - x) x - x ^ 3 / 6
  have hd (x : ℝ) (hx : x < 1) : HasDerivAt f (entropyEll x - x ^ 2 / 2) x := by
    convert! ((((hasDerivAt_id x).pow 2).div_const 2).sub
      (((hasDerivAt_id x).const_sub 1).mul (entropyEll_hasDerivAt hx))).sub
        (((hasDerivAt_id x).pow 3).div_const 6) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    field_simp [show 1 - x ≠ 0 by linarith]
    ring
  have h := value_le_of_deriv_nonneg hu0 (fun x hx => hd x (hx.2.trans_lt hu1))
    (fun x hx => sub_nonneg.mpr (half_sq_le_entropyEll hx.1 (hx.2.trans_lt hu1)))
  simpa [f, entropySlack, entropyEll] using h

theorem entropySlack_cubic_lower_of_le {B u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hB : B ≤ 1 - u) : u ^ 3 / 6 ≤ entropySlack B u := by
  have h := mul_le_mul_of_nonneg_right hB (entropyEll_nonneg hu1)
  have hl := entropySlack_cubic_lower hu0 hu1
  dsimp [entropySlack] at *
  linarith

theorem entropySlack_pos {B u : ℝ} (hB0 : 0 ≤ B) (hB1 : B < 1)
    (huB : u ≤ 1 - B) (hu1 : u < 1) (hu0 : u ≠ 0) : 0 < entropySlack B u := by
  rcases hu0.lt_or_gt with hneg | hpos
  · exact entropySlack_pos_of_neg hB0 hB1 hneg
  · have h := entropySlack_cubic_lower_of_le hpos.le hu1 (by linarith : B ≤ 1 - u)
    exact (div_pos (pow_pos hpos 3) (by norm_num : (0 : ℝ) < 6)).trans_le h

theorem log_one_add_cubic_upper {x : ℝ} (hx : 0 ≤ x) :
    log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun y => y - y ^ 2 / 2 + y ^ 3 / 3 - log (1 + y)
  have hd (y : ℝ) (hy : 0 ≤ y) : HasDerivAt f (y ^ 3 / (1 + y)) y := by
    convert! (((hasDerivAt_id y).sub (((hasDerivAt_id y).pow 2).div_const 2)).add
      (((hasDerivAt_id y).pow 3).div_const 3)).sub
        (((hasDerivAt_id y).const_add 1).log (by linarith : 1 + y ≠ 0)) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    field_simp [show 1 + y ≠ 0 by linarith]
    ring
  have h := value_le_of_deriv_nonneg hx (fun y hy => hd y hy.1)
    (fun y hy => div_nonneg (pow_nonneg hy.1 3) (by linarith [hy.1]))
  simpa [f] using h

theorem entropyVarianceSlack_hasDerivAt {k B C : ℝ} (hk : 0 < k) (hC : 0 < C) :
    HasDerivAt (entropyVarianceSlack k B) (entropyVarianceSlope k B C) C := by
  have hden : C ^ 2 / k ≠ 0 := div_ne_zero (pow_ne_zero 2 hC.ne') hk.ne'
  convert! (((((hasDerivAt_id C).pow 2).div_const k).sub_const 1).sub
    ((((hasDerivAt_id C).pow 2).div_const k).log hden)).sub
      ((((hasDerivAt_id C).sub_const B).pow 2).div_const (1 + k)) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [entropyVarianceSlope]
  field_simp

theorem entropyVarianceSlope_hasDerivAt {k B C : ℝ} (hk : 0 < k) (hC : 0 < C) :
    HasDerivAt (entropyVarianceSlope k B) (2 / (k * (1 + k)) + 2 / C ^ 2) C := by
  convert! ((((hasDerivAt_id C).const_mul 2).div_const k).sub
    ((hasDerivAt_const C (2 : ℝ)).div (hasDerivAt_id C) hC.ne')).sub
      ((((hasDerivAt_id C).sub_const B).const_mul 2).div_const (1 + k)) using 1
  all_goals try with_reducible_and_instances rfl
  dsimp
  field_simp
  ring

theorem entropyVariance_curvature_one {k C : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (_hC : 0 < C) :
    1 ≤ 2 / (k * (1 + k)) + 2 / C ^ 2 := by
  have hp : 0 < k * (1 + k) := mul_pos hk0 (by linarith)
  have hk2 : k * (1 + k) ≤ 2 := by nlinarith
  have hdiv : 1 ≤ 2 / (k * (1 + k)) := by rwa [le_div_iff₀ hp, one_mul]
  have hpos : 0 ≤ 2 / C ^ 2 := div_nonneg (by norm_num) (sq_nonneg _)
  linarith

theorem entropyVariance_taylor_lower {k B C₀ C : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hC₀ : 0 < C₀) (hC : C₀ ≤ C) :
    entropyVarianceSlack k B C₀ + entropyVarianceSlope k B C₀ * (C - C₀) +
      (C - C₀)^2 / 2 ≤ entropyVarianceSlack k B C := by
  have hslope (x : ℝ) (hx : C₀ ≤ x) :
      entropyVarianceSlope k B C₀ + (x - C₀) ≤ entropyVarianceSlope k B x := by
    have h := value_le_of_deriv_nonneg hx
      (f := fun y => entropyVarianceSlope k B y - y)
      (g := fun y => 2 / (k * (1 + k)) + 2 / y ^ 2 - 1)
      (fun y hy => (entropyVarianceSlope_hasDerivAt hk0 (hC₀.trans_le hy.1)).sub (hasDerivAt_id y))
      (fun y hy => sub_nonneg.mpr (entropyVariance_curvature_one hk0 hk1 (hC₀.trans_le hy.1)))
    linarith
  have hd (x : ℝ) (hx : C₀ ≤ x) :
      HasDerivAt (fun y => entropyVarianceSlack k B y -
        entropyVarianceSlope k B C₀ * (y - C₀) - (y - C₀)^2 / 2)
        (entropyVarianceSlope k B x - entropyVarianceSlope k B C₀ - (x - C₀)) x := by
    convert! ((entropyVarianceSlack_hasDerivAt hk0 (hC₀.trans_le hx)).sub
      (((hasDerivAt_id x).sub_const C₀).const_mul (entropyVarianceSlope k B C₀))).sub
        ((((hasDerivAt_id x).sub_const C₀).pow 2).div_const 2) using 1
    all_goals try with_reducible_and_instances rfl
    dsimp
    ring
  have h := value_le_of_deriv_nonneg hC (fun x hx => hd x hx.1)
    (fun x hx => by linarith [hslope x hx.1])
  simp only [sub_self, mul_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div, sub_zero] at h
  linarith

theorem entropyVariance_at_base_lower {k a : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (ha : 0 ≤ a) :
    -(2 * a ^ 3 / 3) ≤ entropyVarianceSlack k (1 - a) (1 + k * a) := by
  have hC : 0 < 1 + k * a := by positivity
  have heq : entropyVarianceSlack k (1 - a) (1 + k * a) =
      1 / k - 1 + log k + 2 * a - a ^ 2 - 2 * log (1 + k * a) := by
    unfold entropyVarianceSlack
    rw [log_div (pow_ne_zero 2 hC.ne') hk0.ne', log_pow]
    field_simp
    ring
  rw [heq]
  have hlogk := one_sub_inv_le_log_of_pos hk0
  have hlog := log_le_log hC (show 1 + k * a ≤ 1 + a by nlinarith)
  have hcubic := log_one_add_cubic_upper ha
  simp only [one_div] at *
  linarith

theorem entropyVarianceSlope_at_base {k a : ℝ} (hk : 0 < k) (ha : 0 ≤ a) :
    entropyVarianceSlope k (1 - a) (1 + k * a) = 2 / k - 2 / (1 + k * a) := by
  unfold entropyVarianceSlope
  field_simp
  ring

theorem entropyVarianceSlope_at_base_lower {k a : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1) (ha : 0 ≤ a) :
    2 * a / (1 + a) ≤ entropyVarianceSlope k (1 - a) (1 + k * a) := by
  rw [entropyVarianceSlope_at_base hk0 ha]
  have hkp : 0 < 1 + k * a := by positivity
  have hap : 0 < 1 + a := by positivity
  have heq : 1 / k - 1 / (1 + k * a) - a / (1 + a) =
      (1 - k) * (1 + a + k * a ^ 2) / (k * (1 + k * a) * (1 + a)) := by
    field_simp
    ring
  have hnonneg : 0 ≤ 1 / k - 1 / (1 + k * a) - a / (1 + a) := by
    rw [heq]
    positivity
  have h2 := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnonneg
  ring_nf at h2 ⊢
  linarith

theorem entropyVariance_pos_large {k a C : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hC : 1 + k * a ≤ C)
    (hlarge : (1 + k) * a ^ 3 / 3 ≤ (C - (1 + k * a)) ^ 2) :
    0 < entropyVarianceSlack k (1 - a) C := by
  let Δ := C - (1 + k * a)
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr hC
  have hΔsq : a ^ 3 / 3 ≤ Δ ^ 2 := by
    dsimp [Δ]
    have hp := mul_nonneg hk0.le (pow_nonneg ha0.le 3)
    nlinarith
  have hΔlower : a ^ 2 / 2 < Δ := by
    by_contra h
    have hle : Δ ≤ a ^ 2 / 2 := le_of_not_gt h
    have hsq := mul_self_le_mul_self hΔ hle
    have hp := mul_pos (pow_pos ha0 3) (show 0 < 4 - 3 * a by linarith)
    nlinarith
  have hlinslope : a ≤ 2 * a / (1 + a) := by
    rw [le_div_iff₀ (show 0 < 1 + a by positivity)]
    nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr ha1.le)]
  have hlinear : a ^ 3 / 2 < entropyVarianceSlope k (1 - a) (1 + k * a) * Δ := by
    have hprod := mul_le_mul_of_nonneg_right
      (hlinslope.trans (entropyVarianceSlope_at_base_lower hk0 hk1 ha0.le)) hΔ
    have hstrict := mul_lt_mul_of_pos_left hΔlower ha0
    nlinarith
  have ht := entropyVariance_taylor_lower (B := 1 - a) hk0 hk1
    (show 0 < 1 + k * a by positivity) hC
  have hb := entropyVariance_at_base_lower hk0 hk1 ha0.le
  change entropyVarianceSlack k (1 - a) (1 + k * a) +
    entropyVarianceSlope k (1 - a) (1 + k * a) * Δ + Δ ^ 2 / 2 ≤ _ at ht
  linarith

theorem entropy_transport_complete_square {k B C u : ℝ} (hk : 0 < k) :
    u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u -
      (C - B) ^ 2 / (2 * (1 + k)) =
    entropySlack B u - (C - B - (1 + k) * u) ^ 2 / (2 * (1 + k)) := by
  unfold entropySlack
  field_simp
  ring

theorem entropy_scalar_optimization {k B C R : ℝ} (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hB0 : 0 < B) (hB1 : B < 1) (hR : 0 ≤ R)
    (htransport : ∀ u < 1, u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u ≤ R)
    (hvariance : 1 < C → C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * R) :
    (C - B) ^ 2 / (2 * (1 + k)) ≤ R ∧
      (C ≠ B → (C - B) ^ 2 / (2 * (1 + k)) < R) := by
  have hkp : 0 < 1 + k := by linarith
  have hstrict (hCB : C ≠ B) : (C - B) ^ 2 / (2 * (1 + k)) < R := by
    let a := 1 - B
    have ha0 : 0 < a := sub_pos.mpr hB1
    have ha1 : a < 1 := by dsimp [a]; linarith
    by_cases hsmall : (C - B) / (1 + k) ≤ a
    · let u := (C - B) / (1 + k)
      have hu1 : u < 1 := hsmall.trans_lt ha1
      have hu0 : u ≠ 0 := div_ne_zero (sub_ne_zero.mpr hCB) hkp.ne'
      have hs := entropySlack_pos hB0.le hB1 hsmall hu1 hu0
      have ht := htransport u hu1
      have he := entropy_transport_complete_square (B := B) (C := C) (u := u) hk0
      have hzero : C - B - (1 + k) * u = 0 := by dsimp [u]; field_simp; ring
      rw [hzero] at he
      norm_num at he
      linarith
    · have hC : 1 + k * a < C := by
        have ht := (lt_div_iff₀ hkp).mp (lt_of_not_ge hsmall)
        dsimp [a] at *
        nlinarith
      by_cases hlarge : (1 + k) * a ^ 3 / 3 ≤ (C - (1 + k * a)) ^ 2
      · have hf := entropyVariance_pos_large hk0 hk1 ha0 ha1 hC.le hlarge
        have hv := hvariance (by have hp := mul_pos hk0 ha0; linarith)
        have hB : 1 - a = B := by dsimp [a]; ring
        rw [hB] at hf
        unfold entropyVarianceSlack at hf
        have he : (C - B) ^ 2 / (1 + k) = 2 * ((C - B) ^ 2 / (2 * (1 + k))) := by field_simp
        rw [he] at hf
        linarith
      · have hs := entropySlack_cubic_lower ha0.le ha1
        have hB : 1 - a = B := by dsimp [a]; ring
        rw [hB] at hs
        have ht := htransport a ha1
        have he := entropy_transport_complete_square (B := B) (C := C) (u := a) hk0
        have hdelta : C - B - (1 + k) * a = C - (1 + k * a) := by dsimp [a]; ring
        rw [hdelta] at he
        have hbound : (C - (1 + k * a)) ^ 2 / (2 * (1 + k)) < a ^ 3 / 6 := by
          rw [div_lt_iff₀ (by positivity : 0 < 2 * (1 + k))]
          linarith [lt_of_not_ge hlarge]
        linarith
  refine ⟨?_, hstrict⟩
  by_cases hCB : C = B
  · simpa [hCB] using hR
  · exact (hstrict hCB).le

theorem entropy_variance_function_mono {w v : ℝ} (hw : 1 ≤ w) (hv : w ≤ v) :
    w - 1 - log w ≤ v - 1 - log v := by
  apply value_le_of_deriv_nonneg hv
    (g := fun x => 1 - 1 / x)
  · intro x hx
    have hxp : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hw.trans hx.1)
    convert! ((hasDerivAt_id x).sub_const 1).sub ((hasDerivAt_id x).log hxp.ne') using 1
  · intro x hx
    have hx1 : 1 ≤ x := hw.trans hx.1
    rw [sub_nonneg, div_le_one (by linarith : 0 < x)]
    exact hx1

theorem entropy_variance_scale {j w : ℝ} (hj0 : 0 < j) (hj1 : j ≤ 1) (hw : 1 ≤ w) :
    w - 1 - log w ≤ j * (w / j - 1 - log (w / j)) := by
  have hwp : 0 < w := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hw
  rw [log_div hwp.ne' hj0.ne']
  have hlog := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hj0) hj0.le
  have hextra := mul_nonneg (sub_nonneg.mpr hj1) (log_nonneg hw)
  have heq : j * (1 - j⁻¹) = j - 1 := by field_simp
  rw [heq] at hlog
  have hcancel : j * (w / j) = w := mul_div_cancel₀ w hj0.ne'
  nlinarith

theorem entropy_variance_scaled_lower {j k C v D : ℝ}
    (hj0 : 0 < j) (hj1 : j ≤ 1) (hk0 : 0 < k) (hk1 : k ≤ 1) (hC : 1 < C)
    (hcv : C ^ 2 / (j * k) ≤ v) (hD : (v - 1 - log v) / 2 ≤ D) :
    C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * (j * D) := by
  have hw : 1 ≤ C ^ 2 / k := by rw [le_div_iff₀ hk0]; nlinarith
  have hwj : 1 ≤ C ^ 2 / (j * k) := by
    rw [le_div_iff₀ (mul_pos hj0 hk0)]
    nlinarith [mul_le_mul_of_nonneg_right hj1 hk0.le]
  have hm := entropy_variance_function_mono hwj hcv
  have hs := entropy_variance_scale hj0 hj1 hw
  have heq : C ^ 2 / k / j = C ^ 2 / (j * k) := by field_simp
  rw [heq] at hs
  have hmj := mul_le_mul_of_nonneg_left hm hj0.le
  have hdj := mul_le_mul_of_nonneg_left hD hj0.le
  linarith

end SKGap

end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarParametersJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

lemma momentCut_nonneg (n : ℕ) (x : ℝ) : 0 ≤ momentCut n x :=
  le_min (Nat.cast_nonneg _) (sq_nonneg _)

lemma momentCut_tendsto (x : ℝ) : Tendsto (fun n => momentCut n x) atTop (𝓝 (x^2)) := by
  have he : ∀ᶠ n : ℕ in atTop, momentCut n x = x^2 := by
    obtain ⟨N,hN⟩ := exists_nat_ge (x^2)
    filter_upwards [eventually_ge_atTop N] with n hn
    exact min_eq_right (hN.trans (by exact_mod_cast hn))
  exact (tendsto_congr' he).2 tendsto_const_nhds

lemma momentBall_iff (R : ℝ) (hR : 0 ≤ R) (P : ProbabilityMeasure ℝ) :
    P ∈ momentBall R ↔ ∀ n, (∫ x, momentCut n x ∂P) ≤ R := by
  constructor
  · intro h n
    apply (ENNReal.ofReal_le_ofReal_iff hR).mp
    rw [ofReal_integral_eq_lintegral_ofReal ((momentCut n).integrable (μ := (P : Measure ℝ)))
      (ae_of_all _ (momentCut_nonneg n))]
    exact (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _))).trans h
  · intro h
    have ht : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (momentCut n x) ∂P) atTop
        (𝓝 (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P)) := by
      apply lintegral_tendsto_of_tendsto_of_monotone
      · intro n; exact (ENNReal.continuous_ofReal.comp (momentCut n).continuous).aemeasurable
      · exact ae_of_all _ (fun x a b hab => ENNReal.ofReal_le_ofReal (min_le_min_right _ (by exact_mod_cast hab)))
      · exact ae_of_all _ (fun x => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (momentCut_tendsto x))
    apply le_of_tendsto ht
    exact Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal ((momentCut n).integrable (μ := (P : Measure ℝ))) (ae_of_all _ (momentCut_nonneg n))]
      exact ENNReal.ofReal_le_ofReal (h n))

lemma isClosed_momentBall (R : ℝ) : IsClosed (momentBall R) := by
  have he : momentBall R = momentBall (max 0 R) := by simp only [momentBall, ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_right (show (0:ℝ≥0∞) ≤ ENNReal.ofReal R from bot_le)]
  rw [he]
  have hR : 0 ≤ max 0 R := le_max_left _ _
  have hes : momentBall (max 0 R) = ⋂ n, {P : ProbabilityMeasure ℝ | (∫ x, momentCut n x ∂P) ≤ max 0 R} := by
    ext P; simp only [mem_iInter, mem_ofPred_eq]; exact momentBall_iff _ hR P
  rw [hes]
  exact isClosed_iInter (fun n => isClosed_le (ProbabilityMeasure.continuous_integral_boundedContinuousFunction _) continuous_const)

lemma momentBall_integrable {R : ℝ} {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    Integrable (fun x : ℝ => x^2) (P : Measure ℝ) := by
  refine ⟨(by fun_prop), ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x : ℝ => sq_nonneg x))]
  exact lt_of_le_of_lt hP ENNReal.ofReal_lt_top

lemma momentBall_integral_le {R : ℝ} (hR : 0 ≤ R) {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    (∫ x : ℝ, x^2 ∂P) ≤ R := by
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  rw [ofReal_integral_eq_lintegral_ofReal (momentBall_integrable hP) (ae_of_all _ (fun x : ℝ => sq_nonneg x))]
  exact hP

lemma momentBall_tail {R K : ℝ} (hK : 0 < K) {P : ProbabilityMeasure ℝ}
    (hP : P ∈ momentBall R) :
    (P : Measure ℝ) (Metric.closedBall 0 K)ᶜ ≤ ENNReal.ofReal R / ENNReal.ofReal (K^2) := by
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (x^2)) := by fun_prop
  calc
    _ ≤ (P : Measure ℝ) {x : ℝ | ENNReal.ofReal (K^2) ≤ ENNReal.ofReal (x^2)} := by
      apply measure_mono
      intro x hx
      have hx' : K < |x| := by simpa only [mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] using hx
      apply ENNReal.ofReal_le_ofReal
      nlinarith [sq_abs x]
    _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂P) / ENNReal.ofReal (K^2) :=
      meas_ge_le_lintegral_div hmeas.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hK)) ENNReal.ofReal_ne_top
    _ ≤ _ := ENNReal.div_le_div_right hP _

lemma isTight_momentBall (R : ℝ) :
    IsTightMeasureSet {((P : ProbabilityMeasure ℝ) : Measure ℝ) | P ∈ momentBall R} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, _, hδ, hδε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hd : 0 < δ := ENNReal.ofReal_pos.mp hδ
  let K := max 0 R / δ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Metric.closedBall 0 K, isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨P,hP,rfl⟩
  calc
    _ ≤ ENNReal.ofReal R / ENNReal.ofReal (K^2) := momentBall_tail hK hP
    _ ≤ ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hK)]
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ (sq_pos_of_pos hK)]
      have hK1 : 1 ≤ K := by dsimp [K]; linarith [div_nonneg (le_max_left 0 R) hd.le]
      have he : δ * (K-1) = max 0 R := by dsimp [K]; field_simp; ring
      have hab : 0 ≤ (K-1)^2 := sq_nonneg _
      nlinarith [le_max_right 0 R, mul_nonneg hd.le hab]
    _ ≤ ε := hδε.le

lemma isCompact_momentBall (R : ℝ) : IsCompact (momentBall R) := by
  have h := isCompact_closure_of_isTightMeasureSet (isTight_momentBall R)
  simpa only [(isClosed_momentBall R).closure_eq] using h

lemma integrable_of_linear_bound {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun x : ℝ => x^2) P) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, |f x| ≤ C*(1+|x|)) : Integrable f P := by
  apply (((integrable_const (2:ℝ)).add hP).const_mul C).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs]
    have hx : |x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
    exact (hb x).trans (mul_le_mul_of_nonneg_left (by change 1+|x| ≤ 2+x^2; linarith) hC))

lemma momentClip_error {n : ℕ} (hn : 0 < n) (x : ℝ) :
    |x - max (-(n:ℝ)) (min (n:ℝ) x)| ≤ x^2/(n:ℝ) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hn']
  by_cases hx : x ≤ (n:ℝ)
  · rw [min_eq_right hx]
    by_cases hx' : -(n:ℝ) ≤ x
    · rw [max_eq_right hx', sub_self, abs_zero, zero_mul]; positivity
    · rw [max_eq_left (le_of_not_ge hx'), abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg (x+(n:ℝ))]
  · rw [min_eq_left (le_of_not_ge hx), max_eq_right (by linarith), abs_of_nonneg (by linarith)]
    nlinarith [sq_nonneg (x-(n:ℝ))]

lemma moment_integral_approx {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C*(1+|x|))
    {n : ℕ} (hn : 0 < n) {P : ProbabilityMeasure ℝ} (hP : P ∈ momentBall R) :
    |(∫ x, f x ∂P) - (∫ x, momentClip hf n x ∂P)| ≤ 2*C^2*(1+R)/(n:ℝ) := by
  have hpi := momentBall_integrable hP
  have hfi := integrable_of_linear_bound hpi hf hC hb
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [← integral_sub hfi ((momentClip hf n).integrable (μ := (P : Measure ℝ))), ← Real.norm_eq_abs]
  have hbound : ∀ x, ‖f x - momentClip hf n x‖ ≤ (2*C^2/(n:ℝ))*(1+x^2) := by
    intro x
    rw [Real.norm_eq_abs]
    change |f x - max (-(n:ℝ)) (min (n:ℝ) (f x))| ≤ _
    apply (momentClip_error hn (f x)).trans
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hn']
    have hsq : (f x)^2 ≤ (C*(1+|x|))^2 := by
      have h := mul_self_le_mul_self (abs_nonneg (f x)) (hb x)
      simpa only [← sq, sq_abs] using h
    have hs : (1+|x|)^2 ≤ 2*(1+x^2) := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
    calc
      _ ≤ (C*(1+|x|))^2 := hsq
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg C)]
  have he := norm_integral_le_of_norm_le
    (((integrable_const (1:ℝ)).add hpi).const_mul (2*C^2/(n:ℝ))) (ae_of_all _ hbound)
  calc
    _ ≤ ∫ x, (2*C^2/(n:ℝ))*(1+x^2) ∂P := he
    _ = (2*C^2/(n:ℝ))*(1+∫ x : ℝ, x^2 ∂P) := by
      rw [integral_const_mul, integral_add (integrable_const 1) hpi]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ (2*C^2/(n:ℝ))*(1+R) := mul_le_mul_of_nonneg_left
      (by linarith [momentBall_integral_le hR hP]) (by positivity)
    _ = _ := by ring

lemma continuousOn_integral_of_linear_bound {R C : ℝ} (hR : 0 ≤ R) (hC : 0 ≤ C)
    {f : ℝ → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C*(1+|x|)) :
    ContinuousOn (fun P : ProbabilityMeasure ℝ => ∫ x, f x ∂P) (momentBall R) := by
  have ht : TendstoUniformlyOn (fun n (P : ProbabilityMeasure ℝ) => ∫ x, momentClip hf n x ∂P)
      (fun P : ProbabilityMeasure ℝ => ∫ x, f x ∂P) atTop (momentBall R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he := (tendsto_const_div_atTop_nhds_zero_nat (2*C^2*(1+R))).eventually (gt_mem_nhds hε)
    filter_upwards [he, eventually_gt_atTop 0] with n hn hn0
    intro P hP
    rw [Real.dist_eq]
    exact (moment_integral_approx hR hC hf hb hn0 hP).trans_lt hn
  apply ht.continuousOn
  exact Frequently.of_forall (fun n => (ProbabilityMeasure.continuous_integral_boundedContinuousFunction (momentClip hf n)).continuousOn)

end SKGap

namespace SKGap

lemma continuous_scalarM : Continuous scalarM := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup tanh continuous_tanh 1
    (fun x => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

lemma continuous_scalarQMoment : Continuous scalarQMoment := by
  let f : ℝ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup (fun x => tanh x^2) (by fun_prop) 1
    (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le)
  exact ProbabilityMeasure.continuous_integral_boundedContinuousFunction f

lemma continuous_scalarD (j : ℝ) : Continuous (scalarD j) :=
  (continuous_fst.comp continuous_snd).add (continuous_const.mul (continuous_scalarM.comp continuous_fst))

lemma continuous_scalarS (j : ℝ) : Continuous (scalarS j) :=
  ((continuous_fst.comp continuous_snd).add ((continuous_snd.comp continuous_snd).pow 2)).add
    (continuous_const.mul (continuous_scalarQMoment.comp continuous_fst))

lemma scalarQMoment_bounds (P : ProbabilityMeasure ℝ) : 0 ≤ scalarQMoment P ∧ scalarQMoment P ≤ 1 := by
  refine ⟨integral_nonneg (fun x => sq_nonneg _), ?_⟩
  have hi : Integrable (fun x : ℝ => tanh x^2) (P : Measure ℝ) := Integrable.of_bound
    (by fun_prop) 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh x))] using (tanh_sq_lt_one x).le))
  have h := integral_mono hi (integrable_const (1:ℝ)) (fun x => (tanh_sq_lt_one x).le)
  simpa only [scalarQMoment, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

lemma scalarM_bounds (P : ProbabilityMeasure ℝ) : |scalarM P| ≤ 1 := by
  have h := norm_integral_le_of_norm_le (μ := (P : Measure ℝ)) (f := tanh) (integrable_const (1:ℝ))
    (ae_of_all _ (fun x : ℝ => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le))
  simpa only [scalarM, Real.norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul] using h

lemma continuousOn_scalarA {R : ℝ} (hR : 0 ≤ R) (j : ℝ) :
    ContinuousOn (scalarA j) (scalarMomentDomain R) := by
  have hi := continuousOn_integral_of_linear_bound hR (C := 1) zero_le_one
    (show Continuous (fun x : ℝ => x*tanh x) by fun_prop) (fun x => by
      rw [abs_mul, one_mul]
      have hm := mul_le_mul_of_nonneg_left (abs_tanh_lt_one x).le (abs_nonneg x)
      linarith)
  have hc : ContinuousOn (fun p : ScalarPoint => ∫ x, x*tanh x ∂p.1) (scalarMomentDomain R) :=
    hi.comp continuous_fst.continuousOn (fun p hp => hp.1)
  exact hc.sub ((continuous_scalarD j).mul (continuous_scalarM.comp continuous_fst)).continuousOn

lemma scalarA_eq {R : ℝ} {p : ScalarPoint} (hp : p ∈ scalarMomentDomain R) (j : ℝ) :
    scalarA j p = ∫ x, (x-scalarD j p)*tanh x ∂p.1 := by
  have hi := integrable_of_linear_bound (momentBall_integrable hp.1)
    (show Continuous (fun x : ℝ => x*tanh x) by fun_prop) zero_le_one (fun x => by
      rw [abs_mul, one_mul]
      have hm := mul_le_mul_of_nonneg_left (abs_tanh_lt_one x).le (abs_nonneg x)
      linarith)
  have ht : Integrable tanh (p.1 : Measure ℝ) := Integrable.of_bound
    continuous_tanh.aestronglyMeasurable 1 (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using (abs_tanh_lt_one x).le))
  simp_rw [sub_mul]
  rw [integral_sub hi (ht.const_mul _), integral_const_mul]
  rfl

lemma continuousOn_scalarPsi {R : ℝ} (hR : 0 ≤ R) (j : ℝ) :
    ContinuousOn (scalarPsi j) (scalarMomentDomain R ∩ {p | scalarS j p ≠ 0 ∧ scalarS j p+j*scalarQMoment p.1 ≠ 0}) := by
  unfold scalarPsi
  apply ContinuousOn.div
  · exact continuousOn_const.mul ((((continuousOn_scalarA hR j).mono inter_subset_left).sub
      ((continuous_scalarS j).continuousOn.mul (continuousOn_const.sub (continuous_scalarQMoment.comp continuous_fst).continuousOn))).pow 2)
  · exact (continuous_const.mul (continuous_scalarS j)).continuousOn.mul
      ((continuous_scalarS j).add (continuous_const.mul (continuous_scalarQMoment.comp continuous_fst))).continuousOn
  · intro p hp; exact mul_ne_zero (mul_ne_zero (by norm_num) hp.2.1) hp.2.2

lemma continuous_scalarLogMoment (f : ℝ →ᵇ ℝ) :
    Continuous (fun p : ℝ×ℝ => scalarLogMoment f p.1 p.2) := by
  have hc := continuous_gaussianAverage (continuous_exp.comp f.continuous)
    (C := exp ‖f‖) (fun x => by
      simp only [Function.comp_def]; rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x)))
  apply hc.log
  intro p
  apply ne_of_gt
  exact integral_pos_iff_support_of_nonneg (fun _ => (exp_pos _).le)
    (integrable_gaussian_comp_of_bound (continuous_exp.comp f.continuous)
      (C := exp ‖f‖) (fun x => by
        simp only [Function.comp_def]; rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))) p.1 p.2) |>.mpr
      (by simp [Function.support, (exp_pos _).ne'])

lemma scalarLogMoment_eq (f : ℝ →ᵇ ℝ) (d : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    scalarLogMoment f d s = log (∫ x, exp (f x) ∂gaussianReal d s.toNNReal) := by
  unfold scalarLogMoment
  congr 1
  exact gaussianAverage_eq_integral (continuous_exp.comp f.continuous) d hs

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarFixedPointJoined
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal

namespace SKGap
open Filter
open scoped Topology

lemma gaussianAverage_hasDerivAt_mean {f f' : ℝ → ℝ} (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ y, HasDerivAt f (f' y) y) {C C' : ℝ}
    (hb : ∀ y, ‖f y‖ ≤ C) (hb' : ∀ y, ‖f' y‖ ≤ C') (d s : ℝ) :
    HasDerivAt (fun d => gaussianAverage f d s) (gaussianAverage f' d s) d := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := gaussianReal 0 1) (s := univ) (x₀ := d)
    (F := fun d x => f (d+sqrt s*x)) (F' := fun d x => f' (d+sqrt s*x))
    (bound := fun _ => C') univ_mem
    (Eventually.of_forall (fun d => (by fun_prop : Continuous (fun x : ℝ => f (d+sqrt s*x))).aestronglyMeasurable))
    (integrable_gaussian_comp_of_bound hf hb d s)
    (by fun_prop)
    (ae_of_all _ (fun x d _ => hb' _))
    (integrable_const _)
    (ae_of_all _ (fun x d _ => by
      convert! (hd (d+sqrt s*x)).comp d ((hasDerivAt_id d).add_const (sqrt s*x)) using 1
      all_goals try with_reducible_and_instances rfl
      simp))).2

lemma gaussianAverage_tanh_mean_deriv (d s : ℝ) :
    HasDerivAt (fun d => gaussianAverage tanh d s)
      (gaussianAverage (fun y => 1-tanh y^2) d s) d := by
  apply gaussianAverage_hasDerivAt_mean continuous_tanh (by fun_prop) hasDerivAt_tanh
    (C := 1) (C' := 1)
  · intro y; simpa using (abs_tanh_lt_one y).le
  · intro y
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [tanh_sq_lt_one y, sq_nonneg (tanh y)]

lemma gaussianAverage_tanh_diff_deriv (d s : ℝ) :
    HasDerivAt (fun d => gaussianAverage (fun y => tanh y-tanh y^2) d s)
      (gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s) d := by
  apply gaussianAverage_hasDerivAt_mean (by fun_prop) (by fun_prop)
    (C := 2) (C' := 3)
  · intro y
    convert! (hasDerivAt_tanh y).sub ((hasDerivAt_tanh y).pow 2) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · intro y
    calc
      ‖tanh y-tanh y^2‖ ≤ ‖tanh y‖+‖tanh y^2‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (tanh y))]
        linarith [(abs_tanh_lt_one y).le, (tanh_sq_lt_one y).le]
  · intro y
    rw [norm_mul]
    have h1 : ‖1-tanh y^2‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith [tanh_sq_lt_one y, sq_nonneg (tanh y)]
    have h2 : ‖1-2*tanh y‖ ≤ 3 := by
      have ht := (abs_le.mp (abs_tanh_lt_one y).le)
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    exact (mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussianF_zero : gaussianF 0 = 0 := by simp [gaussianF, gaussianAverage]

end SKGap

namespace SKGap
open Filter
open scoped Topology

lemma gaussianF_le_self {s : ℝ} (hs : 0 ≤ s) : gaussianF s ≤ s := by
  have h := gaussianF_lipschitz.dist_le_mul s hs 0 (by simp)
  rw [gaussianF_zero, dist_zero_right, NNReal.coe_one, one_mul, dist_zero_right,
    Real.norm_eq_abs, abs_of_nonneg (gaussianF_nonneg hs), Real.norm_eq_abs, abs_of_nonneg hs] at h
  exact h

lemma gaussian_mean_lipschitz (s : ℝ) : LipschitzWith 1 (fun d => gaussianAverage tanh d s) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun d => (gaussianAverage_tanh_mean_deriv d s).differentiableAt)
  intro d
  rw [(gaussianAverage_tanh_mean_deriv d s).deriv]
  have hm (y : ℝ) : 0 ≤ 1-tanh y^2 ∧ 1-tanh y^2 ≤ 1 :=
    ⟨sub_nonneg.mpr (tanh_sq_lt_one y).le, by nlinarith [sq_nonneg (tanh y)]⟩
  have hlo : 0 ≤ gaussianAverage (fun y => 1-tanh y^2) d s :=
    MeasureTheory.integral_nonneg (f := fun x => 1-tanh (d+sqrt s*x)^2) (fun x => (hm _).1)
  have hhi : gaussianAverage (fun y => 1-tanh y^2) d s ≤ 1 := by
    have hi := integrable_gaussian_comp_of_bound (f := fun y => 1-tanh y^2) (by fun_prop)
      (C := 1) (fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hm y).1]; exact (hm y).2) d s
    have h := integral_mono hi (integrable_const 1) (fun x => (hm _).2)
    simpa [gaussianAverage] using h
  exact_mod_cast (show ‖gaussianAverage (fun y => 1-tanh y^2) d s‖ ≤ 1 by
    rw [Real.norm_eq_abs, abs_of_nonneg hlo]; exact hhi)

lemma gaussian_mean_zero (s : ℝ) : gaussianAverage tanh 0 s = 0 := by
  have hn : HasLaw (fun x : ℝ => -x) (gaussianReal 0 1) (gaussianReal 0 1) := by
    simpa only [neg_zero, Pi.neg_def, id_eq] using gaussianReal_neg (HasLaw.id (μ := gaussianReal 0 1))
  have h := hn.integral_comp (f := fun x => tanh (sqrt s*x)) (by fun_prop)
  simp only [Function.comp_def, mul_neg, tanh_neg, integral_neg] at h
  dsimp [gaussianAverage]
  simp only [zero_add]
  linarith

lemma gaussian_mean_fixed_nonneg {j t d s : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t)
    (hd : d = t+j*gaussianAverage tanh d s) : 0 ≤ d := by
  by_contra hh
  have hdneg : d < 0 := lt_of_not_ge hh
  have h := (gaussian_mean_lipschitz s).dist_le_mul d 0
  rw [gaussian_mean_zero, dist_zero_right, NNReal.coe_one, one_mul, dist_zero_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg hdneg] at h
  have hm := (abs_le.mp h).1
  have hmul := mul_le_mul_of_nonneg_left hm hj.le
  nlinarith

lemma gaussian_H_derivative_bounds {d s : ℝ} (hd : 0 ≤ d) (hs : 0 ≤ s) :
    -1 ≤ gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s ∧
      gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s ≤ 1 := by
  rw [gaussianAverage_eq_integral (by fun_prop) d hs]
  have he (y : ℝ) : (1-tanh y^2)*(1-2*tanh y) = (1-tanh y^2)-2*oddVariance y := by
    dsimp [oddVariance]; ring
  have hi : Integrable (fun y => (1-tanh y^2)*(1-2*tanh y)) (gaussianReal d s.toNNReal) := by
    simp_rw [he]
    exact ((integrable_const 1).sub integrable_tanh_sq).sub (integrable_oddVariance.const_mul 2)
  constructor
  · have hp (y : ℝ) : -1 ≤ (1-tanh y^2)*(1-2*tanh y) := by
      have hm := (abs_le.mp (abs_tanh_lt_one y).le)
      have hv : 0 ≤ 1-tanh y^2 := sub_nonneg.mpr (tanh_sq_lt_one y).le
      have h1 : -1 ≤ 1-2*tanh y := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hv
      nlinarith [sq_nonneg (tanh y)]
    have h := integral_mono (integrable_const (-1)) hi hp
    simpa using h
  · simp_rw [he]
    rw [integral_sub (f := fun y => 1-tanh y^2) (g := fun y => 2*oddVariance y)
      ((integrable_const 1).sub (integrable_tanh_sq (P := gaussianReal d s.toNNReal)))
      (integrable_oddVariance.const_mul 2),
      integral_sub (integrable_const 1) (integrable_tanh_sq (P := gaussianReal d s.toNNReal)),
      integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have ho := gaussian_odd_sign hd s.toNNReal
    have hq : 0 ≤ ∫ y, tanh y^2 ∂gaussianReal d s.toNNReal :=
      MeasureTheory.integral_nonneg (f := fun y => tanh y^2) (fun y => sq_nonneg _)
    linarith

lemma gaussian_H_lipschitz {s : ℝ} (hs : 0 ≤ s) :
    LipschitzOnWith 1 (fun d => gaussianAverage (fun y => tanh y-tanh y^2) d s) (Ici 0) := by
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun d _ => (gaussianAverage_tanh_diff_deriv d s).differentiableAt) _ (convex_Ici 0)
  intro d hd
  rw [(gaussianAverage_tanh_diff_deriv d s).deriv]
  exact_mod_cast (show ‖gaussianAverage (fun y => (1-tanh y^2)*(1-2*tanh y)) d s‖ ≤ 1 by
    rw [Real.norm_eq_abs, abs_le]; exact gaussian_H_derivative_bounds hd hs)

lemma gaussian_H_diagonal_zero {s : ℝ} (hs : 0 ≤ s) :
    gaussianAverage (fun y => tanh y-tanh y^2) s s = 0 := by
  rw [gaussianAverage_eq_integral (by fun_prop) s hs,
    integral_sub integrable_tanh integrable_tanh_sq]
  have he := gaussian_nishimori s.toNNReal
  rw [Real.coe_toNNReal _ hs] at he
  exact sub_eq_zero.mpr he

lemma consistent_gaussian_diagonal {j t d : ℝ} {s : ℝ≥0}
    (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t)
    (hd : d = t+j*(∫ y, tanh y ∂gaussianReal d s))
    (hs : (s:ℝ) = t+j*(∫ y, tanh y^2 ∂gaussianReal d s)) : d = s := by
  have he (f : ℝ → ℝ) (hf : Continuous f) : gaussianAverage f d s = ∫ y, f y ∂gaussianReal d s := by
    simpa only [Real.toNNReal_coe] using gaussianAverage_eq_integral hf d s.coe_nonneg
  have hd0 := gaussian_mean_fixed_nonneg hj hj1 ht (hd.trans (by rw [he tanh continuous_tanh]))
  have h := (gaussian_H_lipschitz s.coe_nonneg).dist_le_mul d hd0 s s.coe_nonneg
  rw [gaussian_H_diagonal_zero s.coe_nonneg, dist_zero_right, NNReal.coe_one, one_mul,
    Real.norm_eq_abs, Real.dist_eq] at h
  have hdiff : d-(s:ℝ) = j*gaussianAverage (fun y => tanh y-tanh y^2) d s := by
    rw [he _ (by fun_prop), integral_sub integrable_tanh integrable_tanh_sq]
    linarith
  have ha := congrArg abs hdiff
  rw [abs_mul, abs_of_pos hj] at ha
  have hh : |gaussianAverage (fun y => tanh y-tanh y^2) d s| = 0 := by
    nlinarith [abs_nonneg (gaussianAverage (fun y => tanh y-tanh y^2) d s)]
  have hz := abs_eq_zero.mp hh
  rw [hz, mul_zero] at hdiff
  exact sub_eq_zero.mp hdiff

end SKGap

namespace SKGap

lemma scalarFixedPoint_spec {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    0 ≤ scalarFixedPoint j t ∧ scalarFixedPoint j t = t+j*gaussianF (scalarFixedPoint j t) := by
  simp only [scalarFixedPoint, dite_eq_left (show 0 < j ∧ j < 1 ∧ 0 ≤ t from ⟨hj, hj1, ht⟩)]
  exact (exists_gaussian_fixed hj hj1 ht).choose_spec.1

lemma scalarFixedPoint_bounds {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    t ≤ scalarFixedPoint j t ∧ scalarFixedPoint j t ≤ t/(1-j) := by
  obtain ⟨hs, he⟩ := scalarFixedPoint_spec hj hj1 ht
  constructor
  · nlinarith [gaussianF_nonneg hs]
  · apply (le_div_iff₀ (by linarith : 0 < 1-j)).mpr
    nlinarith [gaussianF_le_self hs]

lemma consistent_gaussian_unique {j t d : ℝ} {s : ℝ≥0}
    (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t)
    (hd : d = t+j*(∫ y, tanh y ∂gaussianReal d s))
    (hs : (s:ℝ) = t+j*(∫ y, tanh y^2 ∂gaussianReal d s)) :
    d = scalarFixedPoint j t ∧ (s:ℝ) = scalarFixedPoint j t := by
  have hds := consistent_gaussian_diagonal hj hj1 ht hd hs
  have he : (s:ℝ) = t+j*gaussianF s := by
    rw [hds] at hd
    rw [gaussianF, gaussianAverage_eq_integral continuous_tanh _ s.coe_nonneg,
      Real.toNNReal_coe]
    exact hd
  have hroot := scalarFixedPoint_spec hj hj1 ht
  have hh := gaussian_fixed_unique hj hj1 s.coe_nonneg hroot.1 he hroot.2
  exact ⟨hds.trans hh, hh⟩

lemma scalarQ_spec {j t : ℝ} (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ t) :
    scalarQ j t = (∫ y, tanh y^2 ∂gaussianReal (scalarFixedPoint j t) (scalarFixedPoint j t).toNNReal) ∧
      scalarQ j t = (scalarFixedPoint j t-t)/j ∧ scalarQ j t ≤ t/(1-j) := by
  obtain ⟨hs, he⟩ := scalarFixedPoint_spec hj hj1 ht
  refine ⟨?_, ?_, ?_⟩
  · exact (gaussianF_eq_square hs).trans (gaussianAverage_eq_integral (by fun_prop) _ hs)
  · dsimp [scalarQ]; apply (eq_div_iff hj.ne').mpr; nlinarith
  · exact (gaussianF_le_self hs).trans (scalarFixedPoint_bounds hj hj1 ht).2

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_EntropyTransport
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
namespace SKGap

theorem entropyTransport_hasDerivAt (u y : ℝ) :
    HasDerivAt (entropyTransport u) (entropyTransportDeriv u y) y := by
  exact (hasDerivAt_id y).sub ((hasDerivAt_tanh y).const_mul u)

theorem entropyTransportDeriv_pos {u : ℝ} (hu : u < 1) (y : ℝ) :
    0 < entropyTransportDeriv u y := by
  have hm := tanh_sq_lt_one y
  have hm0 := sq_nonneg (tanh y)
  dsimp [entropyTransportDeriv]
  by_cases hu0 : 0 ≤ u
  · nlinarith
  · nlinarith

theorem entropyTransport_strictMono {u : ℝ} (hu : u < 1) :
    StrictMono (entropyTransport u) :=
  strictMono_of_hasDerivAt_pos (entropyTransport_hasDerivAt u) (entropyTransportDeriv_pos hu)

theorem entropyTransport_continuous (u : ℝ) : Continuous (entropyTransport u) :=
  continuous_iff_continuousAt.mpr (fun y => (entropyTransport_hasDerivAt u y).continuousAt)

theorem entropyTransport_sub_abs_le (u y : ℝ) : |entropyTransport u y - y| ≤ |u| := by
  calc
    _ = |u| * |tanh y| := by simp [entropyTransport, abs_mul]
    _ ≤ |u| * 1 := mul_le_mul_of_nonneg_left (abs_tanh_lt_one y).le (abs_nonneg _)
    _ = _ := mul_one _

theorem entropyTransport_surjective (u : ℝ) : Function.Surjective (entropyTransport u) := by
  apply (entropyTransport_continuous u).surjective
  · apply tendsto_atTop_mono' atTop (Eventually.of_forall (fun y => ?_))
      (tendsto_atTop_add_const_right atTop (-|u|) tendsto_id)
    have h := (abs_le.mp (entropyTransport_sub_abs_le u y)).1
    dsimp [id]
    linarith
  · apply tendsto_atBot_mono' atBot (Eventually.of_forall (fun y => ?_))
      (tendsto_atBot_add_const_right atBot |u| tendsto_id)
    have h := (abs_le.mp (entropyTransport_sub_abs_le u y)).2
    dsimp [id]
    linarith

theorem log_entropyTransportDeriv_lower {u : ℝ} (hu : u < 1) (y : ℝ) :
    (1 - tanh y ^ 2) * log (1 - u) ≤ log (entropyTransportDeriv u y) := by
  have hm0 := sq_nonneg (tanh y)
  have hm1 := (tanh_sq_lt_one y).le
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (show 0 < (1 : ℝ) by norm_num)
    (show 0 < 1 - u by linarith) hm0 (sub_nonneg.mpr hm1)
    (show tanh y ^ 2 + (1 - tanh y ^ 2) = 1 by ring)
  simp only [smul_eq_mul, log_one, mul_zero, zero_add] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  dsimp [entropyTransportDeriv]
  ring

theorem entropyTransportDeriv_bounds {u : ℝ} (_hu : u < 1) (y : ℝ) :
    min 1 (1 - u) ≤ entropyTransportDeriv u y ∧
      entropyTransportDeriv u y ≤ max 1 (1 - u) := by
  have hm0 := sq_nonneg (tanh y)
  have hm1 := (tanh_sq_lt_one y).le
  dsimp [entropyTransportDeriv]
  by_cases hu0 : 0 ≤ u
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    constructor <;> nlinarith
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    constructor <;> nlinarith

theorem integrable_log_entropyTransportDeriv {P : Measure ℝ} [IsFiniteMeasure P]
    {u : ℝ} (hu : u < 1) : Integrable (fun y => log (entropyTransportDeriv u y)) P := by
  have hm : Continuous (fun y => log (entropyTransportDeriv u y)) := by
    apply Continuous.log
    · unfold entropyTransportDeriv
      fun_prop
    · exact fun y => (entropyTransportDeriv_pos hu y).ne'
  apply Integrable.of_bound hm.aestronglyMeasurable
    (|log (min 1 (1 - u))| + |log (max 1 (1 - u))|)
  apply ae_of_all
  intro y
  have hp : 0 < min 1 (1 - u) := lt_min (by norm_num) (by linarith)
  have hlo := log_le_log hp (entropyTransportDeriv_bounds hu y).1
  have hhi := log_le_log (entropyTransportDeriv_pos hu y)
    (entropyTransportDeriv_bounds hu y).2
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (log (min 1 (1 - u))),
    le_abs_self (log (max 1 (1 - u))), abs_nonneg (log (min 1 (1 - u))),
    abs_nonneg (log (max 1 (1 - u)))]

theorem integrable_sub_mul_tanh {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable id P) (d : ℝ) : Integrable (fun y => (y - d) * tanh y) P := by
  simpa only [Pi.sub_apply, id_eq, mul_comm] using
    (hP.sub (integrable_const d)).bdd_mul continuous_tanh.aestronglyMeasurable
      (ae_of_all _ (fun y => by simpa using (abs_tanh_lt_one y).le))

theorem integrable_entropyTransportLog {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable id P) {u : ℝ} (hu : u < 1) (d s : ℝ) :
    Integrable (entropyTransportLog u d s) P :=
  (((integrable_sub_mul_tanh hP d).const_mul (u / s)).sub
    (integrable_tanh_sq.const_mul (u ^ 2 / (2 * s)))).add
      (integrable_log_entropyTransportDeriv hu)

theorem gaussianPDF_mul_exp_transport {u d : ℝ} {s : ℝ≥0} (hu : u < 1) (y : ℝ) :
    gaussianPDFReal d s y * exp (entropyTransportLog u d s y) =
      entropyTransportDeriv u y * gaussianPDFReal d s (entropyTransport u y) := by
  unfold gaussianPDFReal entropyTransportLog
  rw [exp_add, exp_log (entropyTransportDeriv_pos hu y)]
  calc
    _ = entropyTransportDeriv u y * (1 / sqrt (2 * π * (s : ℝ))) *
      (exp (-(y - d) ^ 2 / (2 * (s : ℝ))) *
       exp (u / (s : ℝ) * ((y - d) * tanh y) - u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2)) := by ring
    _ = _ := by
      rw [← exp_add]
      rw [mul_assoc]
      have he : -(y - d) ^ 2 / (2 * (s : ℝ)) +
        (u / (s : ℝ) * ((y - d) * tanh y) - u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2) =
        -(entropyTransport u y - d) ^ 2 / (2 * (s : ℝ)) := by
          unfold entropyTransport
          ring
      rw [he]
      simp only [one_div]

theorem integrable_exp_entropyTransportLog {u d : ℝ} {s : ℝ≥0}
    (hu : u < 1) (hs : s ≠ 0) :
    Integrable (fun y => exp (entropyTransportLog u d s y)) (gaussianReal d s) := by
  rw [integrable_gaussian_iff hs]
  simp_rw [gaussianPDF_mul_exp_transport hu]
  have heq : entropyTransport u '' univ = univ := (by rw [Set.image_univ, Set.range_eq_univ.mpr (entropyTransport_surjective u)] : entropyTransport u '' univ = univ)
  have h := (integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun x _ => (entropyTransport_hasDerivAt u x).hasDerivWithinAt)
    ((entropyTransport_strictMono hu).monotone.monotoneOn univ) (gaussianPDFReal d s)).mp
  rw [heq, integrableOn_univ, integrableOn_univ] at h
  simpa only [smul_eq_mul] using h (integrable_gaussianPDFReal d s)

theorem integral_exp_entropyTransportLog {u d : ℝ} {s : ℝ≥0}
    (hu : u < 1) (hs : s ≠ 0) :
    (∫ y, exp (entropyTransportLog u d s y) ∂gaussianReal d s) = 1 := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  simp_rw [gaussianPDF_mul_exp_transport hu]
  have h := integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
    (fun x _ => (entropyTransport_hasDerivAt u x).hasDerivWithinAt)
    ((entropyTransport_strictMono hu).monotone.monotoneOn univ) (gaussianPDFReal d s)
  rw [(by rw [Set.image_univ, Set.range_eq_univ.mpr (entropyTransport_surjective u)] : entropyTransport u '' univ = univ)] at h
  simp only [Measure.restrict_univ, smul_eq_mul, integral_gaussianPDFReal_eq_one d hs] at h
  exact h.symm

theorem log_gaussianPDFReal {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0) (y : ℝ) :
    log (gaussianPDFReal d s y) = -log (2 * π * (s : ℝ)) / 2 -
      (y - d) ^ 2 / (2 * (s : ℝ)) := by
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hp : 0 < 2 * π * (s : ℝ) := by positivity
  unfold gaussianPDFReal
  rw [log_mul (by positivity) (exp_pos _).ne', log_inv, log_sqrt hp.le, log_exp]
  ring

theorem gaussianRatioLog_formula {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) (y : ℝ) :
    gaussianRatioLog d s r y = (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (y - d) ^ 2 := by
  have hsp : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  have hrp : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hr
  rw [gaussianRatioLog, log_gaussianPDFReal hr, log_gaussianPDFReal hs,
    log_mul (by positivity : (2 : ℝ) * π ≠ 0) hrp,
    log_mul (by positivity : (2 : ℝ) * π ≠ 0) hsp]
  ring

theorem gaussianPDF_mul_exp_ratio {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) (y : ℝ) :
    gaussianPDFReal d s y * exp (gaussianRatioLog d s r y) = gaussianPDFReal d r y := by
  rw [gaussianRatioLog, exp_sub, exp_log (gaussianPDFReal_pos d r y hr),
    exp_log (gaussianPDFReal_pos d s y hs)]
  exact mul_div_cancel₀ _ (gaussianPDFReal_pos d s y hs).ne'

theorem integrable_gaussianRatioLog {P : Measure ℝ} [IsFiniteMeasure P]
    {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P) : Integrable (gaussianRatioLog d s r) P := by
  change Integrable (fun y => gaussianRatioLog d s r y) P
  simp_rw [gaussianRatioLog_formula hs hr]
  exact (integrable_const ((log (s : ℝ) - log (r : ℝ)) / 2)).add (hP.const_mul _)

theorem integrable_exp_gaussianRatioLog {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) :
    Integrable (fun y => exp (gaussianRatioLog d s r y)) (gaussianReal d s) := by
  rw [integrable_gaussian_iff hs]
  simp_rw [gaussianPDF_mul_exp_ratio hs hr]
  exact integrable_gaussianPDFReal d r

theorem integral_exp_gaussianRatioLog {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) :
    (∫ y, exp (gaussianRatioLog d s r y) ∂gaussianReal d s) = 1 := by
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  simp_rw [gaussianPDF_mul_exp_ratio hs hr]
  exact integral_gaussianPDFReal_eq_one d hr

theorem secondMoment_integrable {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P) : Integrable id P := by
  exact ((memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable id P)).mpr hP).integrable (by norm_num)

theorem centered_secondMoment_integrable {P : Measure ℝ} [IsFiniteMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P) (d : ℝ) :
    Integrable (fun y => (y - d) ^ 2) P := by
  have hm : MemLp id 2 P := (memLp_two_iff_integrable_sq (by fun_prop)).mpr hP
  exact (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable (fun y : ℝ => y - d) P)).mp
    (hm.sub (memLp_const d))

theorem entropy_q_lt_one {P : Measure ℝ} [IsProbabilityMeasure P] :
    (∫ y, tanh y ^ 2 ∂P) < 1 := by
  have hi : Integrable (fun y : ℝ => 1 - tanh y ^ 2) P := (integrable_const 1).sub integrable_tanh_sq
  have hsupp : Function.support (fun y : ℝ => 1 - tanh y ^ 2) = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (sub_pos.mpr (tanh_sq_lt_one y)).ne'
  have hp := (integral_pos_iff_support_of_nonneg (fun y => (sub_pos.mpr (tanh_sq_lt_one y)).le) hi).mpr
    (by rw [hsupp]; simp)
  rw [integral_sub (integrable_const 1) integrable_tanh_sq] at hp
  simpa using hp

theorem entropy_moment_cauchy {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P) (d : ℝ)
    (hq : 0 < ∫ y, tanh y ^ 2 ∂P) :
    (∫ y, (y - d) * tanh y ∂P) ^ 2 ≤
      (∫ y, tanh y ^ 2 ∂P) * (∫ y, (y - d) ^ 2 ∂P) := by
  let a := ∫ y, (y - d) * tanh y ∂P
  let q := ∫ y, tanh y ^ 2 ∂P
  have hp : 0 ≤ ∫ y : ℝ, ((y - d) - (a / q) * tanh y) ^ 2 ∂P :=
    integral_nonneg (fun y => sq_nonneg _)
  have he (y : ℝ) : ((y - d) - (a / q) * tanh y) ^ 2 =
      (y - d) ^ 2 - (2 * a / q) * ((y - d) * tanh y) + (a / q) ^ 2 * tanh y ^ 2 := by ring
  simp_rw [he] at hp
  have hv := centered_secondMoment_integrable hP d
  have ha := integrable_sub_mul_tanh (secondMoment_integrable hP) d
  rw [integral_add (f := fun y => (y - d) ^ 2 - (2 * a / q) * ((y - d) * tanh y))
      (hv.sub (ha.const_mul (2 * a / q))) (integrable_tanh_sq.const_mul ((a / q) ^ 2)),
    integral_sub hv (ha.const_mul (2 * a / q)), integral_const_mul, integral_const_mul] at hp
  change 0 ≤ (∫ y, (y - d) ^ 2 ∂P) - 2 * a / q * a + (a / q) ^ 2 * q at hp
  have hqp : 0 < q := hq
  have hm := mul_nonneg hp hqp.le
  field_simp at hm
  dsimp [a, q] at hm
  nlinarith

end SKGap

end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_ScalarEntropyTarget
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set

noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

lemma realClip_abs (n : ℕ) (x : ℝ) : |realClip n x| ≤ |x| := by
  rw [abs_le]
  constructor
  · exact le_sup_of_le_right (le_min (by linarith [abs_nonneg x]) (neg_abs_le x))
  · exact sup_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))

lemma realClip_le (n : ℕ) (x : ℝ) : realClip n x ≤ max 0 x :=
  max_le (by linarith [le_max_left (0:ℝ) x]) ((min_le_right _ _).trans (le_max_right _ _))

lemma tendsto_realClip (x : ℝ) : Tendsto (fun n : ℕ => realClip n x) atTop (𝓝 x) := by
  have he : ∀ᶠ n : ℕ in atTop, realClip n x = x := by
    obtain ⟨N, hN⟩ := exists_nat_ge |x|
    filter_upwards [eventually_ge_atTop N] with n hn
    have hb : |x| ≤ (n:ℝ) := hN.trans (by exact_mod_cast hn)
    have hx := abs_le.mp hb
    simp only [realClip, min_eq_right hx.2, max_eq_right hx.1]
  exact (tendsto_congr' he).2 tendsto_const_nhds

lemma entropyTestBound_continuous {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {D : ℝ} (hD : EntropyTestBound P Q D)
    {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f P)
    (he : Integrable (fun x => exp (f x)) Q) :
    (∫ x, f x ∂P) - log (∫ x, exp (f x) ∂Q) ≤ D := by
  have hP : Tendsto (fun n => ∫ x, clippedBC hf n x ∂P) atTop (𝓝 (∫ x, f x ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
    · intro n; exact (clippedBC hf n).continuous.aestronglyMeasurable
    · exact hi.abs
    · intro n; exact ae_of_all _ (fun x => by
        change ‖realClip n (f x)‖ ≤ |f x|
        rw [Real.norm_eq_abs]; exact realClip_abs n (f x))
    · exact ae_of_all _ (fun x => tendsto_realClip (f x))
  have hQ : Tendsto (fun n => ∫ x, exp (clippedBC hf n x) ∂Q) atTop (𝓝 (∫ x, exp (f x) ∂Q)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 1+exp (f x))
    · intro n; exact (by fun_prop : Continuous (fun x => exp (clippedBC hf n x))).aestronglyMeasurable
    · exact (integrable_const 1).add he
    · intro n; exact ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        calc
          _ ≤ exp (max 0 (f x)) := exp_le_exp.mpr (realClip_le n (f x))
          _ ≤ 1+exp (f x) := by
            by_cases hx : 0 ≤ f x
            · rw [max_eq_right hx]; linarith
            · rw [max_eq_left (le_of_not_ge hx), exp_zero]; linarith [exp_pos (f x)])
    · exact ae_of_all _ (fun x => continuous_exp.continuousAt.tendsto.comp (tendsto_realClip (f x)))
  have hpos : 0 < ∫ x, exp (f x) ∂Q := integral_pos_iff_support_of_nonneg
    (fun x => (exp_pos (f x)).le) he |>.mpr (by simp [Function.support, (exp_pos _).ne'])
  exact le_of_tendsto (hP.sub ((continuousAt_log hpos.ne').tendsto.comp hQ))
    (Eventually.of_forall (fun n => hD (clippedBC hf n)))

lemma entropyTestBound_normalized {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {D : ℝ} (hD : EntropyTestBound P Q D)
    {f : ℝ → ℝ} (hf : Continuous f) (hi : Integrable f P)
    (he : Integrable (fun x => exp (f x)) Q) (hZ : ∫ x, exp (f x) ∂Q = 1) :
    (∫ x, f x ∂P) ≤ D := by
  simpa only [hZ, log_one, sub_zero] using entropyTestBound_continuous hD hf hi he

lemma integrable_exp_boundedContinuous {Q : Measure ℝ} [IsFiniteMeasure Q] (f : ℝ →ᵇ ℝ) (t : ℝ) :
    Integrable (fun x => exp (t*f x)) Q := by
  apply Integrable.of_bound (by fun_prop) (exp (|t| * ‖f‖))
  exact ae_of_all _ (fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      t*f x ≤ |t*f x| := le_abs_self _
      _ = |t| * |f x| := abs_mul _ _
      _ ≤ |t| * ‖f‖ := mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (abs_nonneg _))

lemma boundedContinuous_mgf_deriv {Q : Measure ℝ} [IsProbabilityMeasure Q] (f : ℝ →ᵇ ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, exp (t*f x) ∂Q) (∫ x, f x ∂Q) 0 := by
  have hset : integrableExpSet (fun x => f x) Q = univ := by
    ext t; exact iff_true_intro (integrable_exp_boundedContinuous f t)
  have h := hasDerivAt_mgf (X := fun x => f x) (μ := Q) (t := 0) (by simp [hset])
  convert! h using 1; simp

lemma entropyTestBound_zero_eq {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hD : EntropyTestBound P Q 0) : P = Q := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let g : ℝ → ℝ := fun t => log (∫ x, exp (t*f x) ∂Q) - t*(∫ x, f x ∂P)
  have hg0 : g 0 = 0 := by simp [g]
  have hmin : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h := hD (t • f)
    simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul, integral_const_mul] at h
    rw [hg0]
    dsimp [g]
    exact (show 0 ≤ log (∫ x, exp (t*f x) ∂Q)-t*(∫ x, f x ∂P) by linarith)
  have hder : HasDerivAt g ((∫ x, f x ∂Q)-(∫ x, f x ∂P)) 0 := by
    have h := (boundedContinuous_mgf_deriv (Q := Q) f).log (by simp)
    convert! h.sub ((hasDerivAt_id (0:ℝ)).mul_const (∫ x, f x ∂P)) using 1; simp
  have hz := hmin.hasDerivAt_eq_zero hder
  linarith

lemma entropyTestBound_nonneg {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {D : ℝ} (hD : EntropyTestBound P Q D) : 0 ≤ D := by
  simpa using hD 0

end SKGap

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_EntropyTestBoundQPos
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
namespace SKGap

lemma entropyTestBound_q_pos {P : Measure ℝ} [IsProbabilityMeasure P]
    {d D : ℝ} {s : ℝ≥0} (hs : s ≠ 0) (hD : EntropyTestBound P (gaussianReal d s) D) :
    0 < ∫ y, tanh y^2 ∂P := by
  have hn : 0 ≤ ∫ y, tanh y^2 ∂P := integral_nonneg (fun y => sq_nonneg (tanh y))
  by_contra hh
  have hzero : (∫ y, tanh y^2 ∂P) = 0 := le_antisymm (le_of_not_gt hh) hn
  let F : ℕ → ℝ → ℝ := fun n y => exp (-(n:ℝ)*tanh y^2)
  have hFn (n : ℕ) (y : ℝ) : ‖F n y‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (sq_nonneg _))
  have hFi (n : ℕ) : Integrable (F n) (gaussianReal d s) :=
    Integrable.of_bound (by dsimp [F]; fun_prop) 1 (ae_of_all _ (hFn n))
  have h_lower (n : ℕ) : exp (-D) ≤ ∫ y, F n y ∂gaussianReal d s := by
    have h := entropyTestBound_continuous hD (f := fun y => -(n:ℝ)*tanh y^2)
      (by fun_prop) (integrable_tanh_sq.const_mul _) (hFi n)
    rw [integral_const_mul, hzero, mul_zero, zero_sub] at h
    have hz := integral_exp_pos (hFi n)
    calc
      _ ≤ exp (log (∫ y, F n y ∂gaussianReal d s)) := exp_le_exp.mpr (by linarith)
      _ = _ := exp_log hz
  have := nullSingletonClass_gaussianReal (μ := d) hs
  have hlim : Tendsto (fun n => ∫ y, F n y ∂gaussianReal d s) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => ∫ y, F n y ∂gaussianReal d s) atTop
        (𝓝 (∫ _ : ℝ, (0:ℝ) ∂gaussianReal d s)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
      · intro n; exact (hFi n).aestronglyMeasurable
      · exact integrable_const 1
      · intro n; exact ae_of_all _ (hFn n)
      · filter_upwards [(gaussianReal d s).ae_ne 0] with y hy
        have hm : tanh y ≠ 0 := fun hz => hy (tanh_injective (by simpa only [tanh_zero] using hz))
        have hc : 0 < tanh y^2 := sq_pos_of_ne_zero hm
        have hnat : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
        have hneg := tendsto_neg_atTop_atBot.comp (hnat.atTop_mul_const hc)
        exact tendsto_exp_atBot.comp (by simpa only [Function.comp_def, neg_mul] using hneg)
    simpa using hh
  have hle := ge_of_tendsto hlim (Eventually.of_forall h_lower)
  exact (not_le_of_gt (exp_pos (-D))) hle

@[fun_prop] lemma continuous_entropyTransportLog {u d s : ℝ} (hu : u < 1) :
    Continuous (entropyTransportLog u d s) := by
  have hc : Continuous (entropyTransportDeriv u) := by unfold entropyTransportDeriv; fun_prop
  have hl := hc.log (fun y => (entropyTransportDeriv_pos hu y).ne')
  unfold entropyTransportLog
  exact ((continuous_const.mul ((continuous_id.sub continuous_const).mul continuous_tanh)).sub
    (continuous_const.mul (continuous_tanh.pow 2))).add hl

theorem test_transport_lower {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable id P) {u d : ℝ} {s : ℝ≥0} (hu : u < 1) (hs : s ≠ 0)
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) :
    u / (s : ℝ) * (∫ y, (y - d) * tanh y ∂P) -
      u ^ 2 / (2 * (s : ℝ)) * (∫ y, tanh y ^ 2 ∂P) +
      (1 - ∫ y, tanh y ^ 2 ∂P) * log (1 - u) ≤ D := by
  have hlog := integral_mono
    (((integrable_const (1 : ℝ)).sub integrable_tanh_sq).mul_const (log (1 - u)))
    (integrable_log_entropyTransportDeriv (P := P) hu) (log_entropyTransportDeriv_lower hu)
  simp only [Pi.sub_apply] at hlog
  rw [integral_mul_const, integral_sub (integrable_const 1) integrable_tanh_sq,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at hlog
  have h := entropyTestBound_normalized hD (continuous_entropyTransportLog hu) (integrable_entropyTransportLog hP hu d s)
    (integrable_exp_entropyTransportLog hu hs) (integral_exp_entropyTransportLog hu hs)
  unfold entropyTransportLog at h
  rw [integral_add (f := fun y => u / (s : ℝ) * ((y - d) * tanh y) -
      u ^ 2 / (2 * (s : ℝ)) * tanh y ^ 2)
      (((integrable_sub_mul_tanh hP d).const_mul _).sub (integrable_tanh_sq.const_mul _))
      (integrable_log_entropyTransportDeriv hu),
    integral_sub ((integrable_sub_mul_tanh hP d).const_mul _) (integrable_tanh_sq.const_mul _),
    integral_const_mul, integral_const_mul] at h
  linarith

lemma continuous_gaussianRatioLog {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0) :
    Continuous (gaussianRatioLog d s r) := by
  have he : gaussianRatioLog d s r = fun y => (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (y - d)^2 := funext (gaussianRatioLog_formula hs hr)
  rw [he]; fun_prop

theorem test_variance_comparison {P : Measure ℝ} [IsProbabilityMeasure P]
    {d : ℝ} {s r : ℝ≥0} (hs : s ≠ 0) (hr : r ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P)
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) :
    (log (s : ℝ) - log (r : ℝ)) / 2 +
      (1 / (2 * (s : ℝ)) - 1 / (2 * (r : ℝ))) * (∫ y, (y - d) ^ 2 ∂P) ≤
      D := by
  have h := entropyTestBound_normalized hD (continuous_gaussianRatioLog hs hr) (integrable_gaussianRatioLog hs hr hP)
    (integrable_exp_gaussianRatioLog hs hr) (integral_exp_gaussianRatioLog hs hr)
  simp_rw [gaussianRatioLog_formula hs hr] at h
  rw [integral_add (integrable_const _) (hP.const_mul _), integral_const_mul] at h
  simpa using h

theorem test_variance_lower {P : Measure ℝ} [IsProbabilityMeasure P]
    {d : ℝ} {s : ℝ≥0} (hs : s ≠ 0)
    (hP : Integrable (fun y => (y - d) ^ 2) P)
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) {v : ℝ} (hv : 0 < v)
    (hvar : ∫ y, (y - d) ^ 2 ∂P = (s : ℝ) * v) :
    (v - 1 - log v) / 2 ≤ D := by
  let r : ℝ≥0 := s * ⟨v, hv.le⟩
  have hr : r ≠ 0 := mul_ne_zero hs (NNReal.coe_ne_zero.mp hv.ne')
  have h := test_variance_comparison hs hr hP hD
  change (log (s : ℝ) - log ((s : ℝ) * v)) / 2 +
    (1 / (2 * (s : ℝ)) - 1 / (2 * ((s : ℝ) * v))) *
      (∫ y, (y - d) ^ 2 ∂P) ≤ _ at h
  have hsp : (s : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hs
  rw [log_mul hsp hv.ne', hvar] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  field_simp
  ring

theorem test_scalar_inequality {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y ^ 2) P)
    {j d : ℝ} {s : ℝ≥0} (hj0 : 0 < j) (hj1 : j < 1) (hs : s ≠ 0)
    (hcons : j * (∫ y, tanh y ^ 2 ∂P) ≤ (s : ℝ))
    {D : ℝ} (hD : EntropyTestBound P (gaussianReal d s) D) :
    let q := ∫ y, tanh y ^ 2 ∂P
    let a := ∫ y, (y - d) * tanh y ∂P
    let T := j * (a - (s : ℝ) * (1 - q)) ^ 2 / (2 * (s : ℝ) * ((s : ℝ) + j * q))
    T ≤ D ∧
      (a ≠ (s : ℝ) * (1 - q) → T < D) := by
  dsimp only
  let q := ∫ y, tanh y ^ 2 ∂P
  let a := ∫ y, (y - d) * tanh y ∂P
  let k := j * q / (s : ℝ)
  let B := j * (1 - q)
  let C := j * a / (s : ℝ)
  have hsp : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hq0 : 0 < q := entropyTestBound_q_pos hs hD
  have hq1 : q < 1 := entropy_q_lt_one
  have hk0 : 0 < k := div_pos (mul_pos hj0 hq0) hsp
  have hk1 : k ≤ 1 := (div_le_one hsp).mpr hcons
  have hB0 : 0 < B := mul_pos hj0 (sub_pos.mpr hq1)
  have hB1 : B < 1 := by dsimp [B]; nlinarith
  have htransport (u : ℝ) (hu : u < 1) :
      u * (C - B) - k * u ^ 2 / 2 - B * entropyEll u ≤ j * D := by
    have h := mul_le_mul_of_nonneg_left (test_transport_lower (secondMoment_integrable hP) hu hs hD) hj0.le
    change j * (u / (s : ℝ) * a - u ^ 2 / (2 * (s : ℝ)) * q + (1 - q) * log (1 - u)) ≤ j * D at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [k, B, C, entropyEll]
    field_simp
    ring
  have hvariance (hC : 1 < C) : C ^ 2 / k - 1 - log (C ^ 2 / k) ≤ 2 * (j * D) := by
    let v := (∫ y, (y - d) ^ 2 ∂P) / (s : ℝ)
    have hcauchy := entropy_moment_cauchy hP d hq0
    have hcv : C ^ 2 / (j * k) ≤ v := by
      have heq : C ^ 2 / (j * k) * (s : ℝ) = a ^ 2 / q := by
        dsimp [C, k]
        field_simp
      dsimp [v]
      rw [le_div_iff₀ hsp, heq, div_le_iff₀ hq0]
      simpa only [q, a, mul_comm] using hcauchy
    have hv : 0 < v := (div_pos (pow_pos (by linarith : 0 < C) 2) (mul_pos hj0 hk0)).trans_le hcv
    have hvar : (∫ y, (y - d) ^ 2 ∂P) = (s : ℝ) * v := by dsimp [v]; field_simp
    have hbound := test_variance_lower hs (centered_secondMoment_integrable hP d) hD hv hvar
    exact entropy_variance_scaled_lower hj0 hj1.le hk0 hk1 hC hcv hbound
  have hopt := entropy_scalar_optimization hk0 hk1 hB0 hB1
    (mul_nonneg hj0.le (entropyTestBound_nonneg hD)) htransport hvariance
  have heq : (C - B) ^ 2 / (2 * (1 + k)) =
      j * (j * (a - (s : ℝ) * (1 - q)) ^ 2 / (2 * (s : ℝ) * ((s : ℝ) + j * q))) := by
    dsimp [C, B, k]
    field_simp
  rw [heq] at hopt
  refine ⟨le_of_mul_le_mul_left hopt.1 hj0, ?_⟩
  intro ha
  have hCB : C ≠ B := by
    intro h
    apply ha
    dsimp [C, B] at h
    have he := (div_eq_iff hsp.ne').mp h
    nlinarith
  exact lt_of_mul_lt_mul_left (hopt.2 hCB) hj0.le

theorem scalar_strict_witness {P : Measure ℝ} [IsProbabilityMeasure P]
    (hP : Integrable (fun y : ℝ => y^2) P)
    {j d : ℝ} {s : ℝ≥0} (hj : 0 < j) (hj1 : j < 1) (hs : s ≠ 0)
    (hcons : j * (∫ y, tanh y^2 ∂P) ≤ (s:ℝ)) (hne : P ≠ gaussianReal d s) :
    ∃ f : ℝ →ᵇ ℝ, scalarEntropyTarget P j d s <
      (∫ y, f y ∂P) - log (∫ y, exp (f y) ∂gaussianReal d s) := by
  by_contra h
  push Not at h
  have hD : EntropyTestBound P (gaussianReal d s) (scalarEntropyTarget P j d s) := h
  have hop := test_scalar_inequality hP hj hj1 hs hcons hD
  have he : (∫ y, (y-d)*tanh y ∂P) = (s:ℝ)*(1-∫ y, tanh y^2 ∂P) := by
    by_contra hh
    exact lt_irrefl _ (hop.2 hh)
  have hzero : scalarEntropyTarget P j d s = 0 := by simp [scalarEntropyTarget, he]
  rw [hzero] at hD
  exact hne (entropyTestBound_zero_eq hD)

end SKGap

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ProductGaussianDensity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal
namespace SKGap.GaussianDensity
variable {ι : Type*} [Fintype ι]

theorem pi_gaussian_density (m : ι → ℝ) (v : ι → ℝ≥0) (hv : ∀ i,v i ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) (v i)) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (∏ i,gaussianPDFReal (m i) (v i) (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun x : ι → ℝ => ∏ i,gaussianPDFReal (m i) (v i) (x i))
      (volume.restrict (Set.univ.pi s)) := by
    exact (Integrable.fintype_prod (fun i => integrable_gaussianPDFReal (m i) (v i))).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun x => Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)))]
  change ENNReal.ofReal (∫ x, (∏ i,gaussianPDFReal (m i) (v i) (x i))
    ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s))=_
  rw [Measure.restrict_pi_pi,integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [gaussianReal_of_var_ne_zero _ (hv i),withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal (m i) (v i)).restrict
    (Filter.Eventually.of_forall (gaussianPDFReal_nonneg _ _))

lemma measurable_productPDF (m : ι → ℝ) (v : ι → ℝ≥0) :
    Measurable (fun x : ι → ℝ => ENNReal.ofReal (∏ i,gaussianPDFReal (m i) (v i) (x i))) := by
  fun_prop

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_EqualityCurve
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianDensity

lemma map_withDensity_leftInverse {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} {g : β → α} (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) (d : α → ℝ≥0∞) (hd : Measurable d) :
    (μ.withDensity d).map f=(μ.map f).withDensity (d ∘ g) := by
  ext s hs
  rw [Measure.map_apply hf hs,withDensity_apply _ (hf hs),withDensity_apply _ hs,
    setLIntegral_map hs (hd.comp hg) hf]
  apply lintegral_congr
  intro x
  simp only [Function.comp_apply]
  rw [hgf x]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_map_gaussian_density (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x => A*ᵥx) =
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal
        (|A.det⁻¹| *∏ i,gaussianPDFReal 0 1 ((A⁻¹*ᵥx) i))) := by
  have hm (B : Matrix ι ι ℝ) : Measurable (fun x => B*ᵥx) := by fun_prop
  have hleft : Function.LeftInverse (fun x => A⁻¹*ᵥx) (fun x => A*ᵥx) := by
    intro x
    change A⁻¹*ᵥ(A*ᵥx)=x
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec]
  rw [pi_gaussian_density (fun _ : ι => 0) (fun _ => 1) (fun _ => one_ne_zero),
    map_withDensity_leftInverse _ (hm A) (hm A⁻¹) hleft _ (measurable_productPDF _ _)]
  have hvol : (volume : Measure (ι → ℝ)).map (fun x => A*ᵥx)=
      ENNReal.ofReal |A.det⁻¹| • volume := Real.map_matrix_volume_pi_eq_smul_volume_pi hA
  rw [hvol,withDensity_smul_measure,← withDensity_smul _ ((measurable_productPDF _ _).comp (hm A⁻¹))]
  congr 1
  ext x
  simp only [Pi.smul_apply,Function.comp_apply,smul_eq_mul,ENNReal.ofReal_mul (abs_nonneg _)]

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarConsistency
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction

namespace SKGap

lemma scalar_consistency {j : ℝ} {p : ScalarPoint} (ht : 0 ≤ p.2.1) :
    j*scalarQMoment p.1 ≤ scalarS j p := by
  unfold scalarS
  nlinarith [sq_nonneg p.2.2]

lemma scalarPsi_eq_entropy {R j : ℝ} {p : ScalarPoint}
    (hp : p ∈ scalarMomentDomain R) (hs : 0 ≤ scalarS j p) :
    scalarPsi j p = scalarEntropyTarget (p.1 : Measure ℝ) j (scalarD j p) (scalarS j p).toNNReal := by
  simp only [scalarPsi, scalarEntropyTarget, Real.coe_toNNReal _ hs, scalarA_eq hp, scalarQMoment]

lemma scalar_strict_test {R j : ℝ} {p : ScalarPoint}
    (hp : p ∈ scalarMomentDomain R) (hj : 0 < j) (hj1 : j < 1)
    (ht : 0 ≤ p.2.1) (hs : 0 < scalarS j p)
    (hne : (p.1 : Measure ℝ) ≠ gaussianReal (scalarD j p) (scalarS j p).toNNReal) :
    ∃ f : ℝ →ᵇ ℝ, scalarPsi j p-(∫ y, f y ∂p.1)+
      log (∫ y, exp (f y) ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) < 0 := by
  have hcons : j * (∫ y, tanh y^2 ∂p.1) ≤ ((scalarS j p).toNNReal : ℝ) := by
    rw [Real.coe_toNNReal _ hs.le]
    exact scalar_consistency ht
  obtain ⟨f,hf⟩ := scalar_strict_witness (momentBall_integrable hp.1) hj hj1
    (ne_of_gt (Real.toNNReal_pos.mpr hs)) hcons hne
  rw [← scalarPsi_eq_entropy hp hs.le] at hf
  exact ⟨f, by linarith⟩

lemma scalar_gaussian_curve {j : ℝ} {p : ScalarPoint}
    (hj : 0 < j) (hj1 : j < 1) (ht : 0 ≤ p.2.1)
    (hσ : p.2.2 = 0) (hs : 0 ≤ scalarS j p)
    (hP : (p.1 : Measure ℝ) = gaussianReal (scalarD j p) (scalarS j p).toNNReal) :
    p.1 = scalarCurve j p.2.1 := by
  have hd : scalarD j p = p.2.1+j*(∫ y, tanh y ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) := by
    rw [← hP]
    rfl
  have hv : ((scalarS j p).toNNReal : ℝ) =
      p.2.1+j*(∫ y, tanh y^2 ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) := by
    rw [Real.coe_toNNReal _ hs, ← hP]
    simp [scalarS, scalarQMoment, hσ]
  obtain ⟨hd',hs'⟩ := consistent_gaussian_unique hj hj1 ht hd hv
  rw [Real.coe_toNNReal _ hs] at hs'
  apply ProbabilityMeasure.toMeasure_injective
  change (p.1 : Measure ℝ) = gaussianReal (scalarFixedPoint j p.2.1) (scalarFixedPoint j p.2.1).toNNReal
  rw [hP, hd', hs']

lemma continuousOn_scalar_test {R j : ℝ} (hR : 0 ≤ R) (hj : 0 ≤ j)
    (f : ℝ →ᵇ ℝ) : ContinuousOn (fun p : ScalarPoint =>
      scalarPsi j p-(∫ y, f y ∂p.1)+scalarLogMoment f (scalarD j p) (scalarS j p))
      (scalarMomentDomain R ∩ {p | 0 < scalarS j p}) := by
  have hψ : ContinuousOn (scalarPsi j)
      (scalarMomentDomain R ∩ {p | 0 < scalarS j p}) := (continuousOn_scalarPsi hR j).mono (by
        intro p hp
        refine ⟨hp.1,hp.2.ne',ne_of_gt ?_⟩
        exact add_pos_of_pos_of_nonneg hp.2 (mul_nonneg hj (scalarQMoment_bounds p.1).1))
  exact (hψ.sub ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp
    continuous_fst).continuousOn).add
    ((continuous_scalarLogMoment f).comp ((continuous_scalarD j).prodMk (continuous_scalarS j))).continuousOn

end SKGap

noncomputable section
open Set Filter Topology
namespace SKGap

lemma finite_pos_lower_bound {X : Type*} (C : Finset X) (a : X → ℝ)
    (ha : ∀ x ∈ C, 0 < a x) : ∃ ε > 0, ∀ x ∈ C, ε ≤ a x := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | insert x C hx ih =>
    obtain ⟨ε,hε,he⟩ := ih (fun y hy => ha y (Finset.mem_insert_of_mem hy))
    refine ⟨min (a x) ε, lt_min (ha x (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (he y hy)

theorem compact_strict_witness {X F : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (w : F → X → ℝ) (hw : ∀ f, ContinuousOn (w f) K)
    (hW : ∀ x ∈ K, ∃ f, w f x < 0) :
    ∃ a > 0, ∀ x ∈ K, ∃ f, w f x < -a := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose f hf using fun x : K => hW x.1 x.2
  let a (x : K) := -(w (f x) x)/2
  have ha (x : K) : 0 < a x := by dsimp [a]; linarith [hf x]
  let U (x : K) : Set K := {z | w (f x) z < -a x}
  have hU (x : K) : IsOpen (U x) := isOpen_lt (hw (f x)).domRestrict continuous_const
  have hcov : (univ : Set K) ⊆ ⋃ x, U x := by
    intro x _
    apply mem_iUnion.mpr
    refine ⟨x,?_⟩
    change w (f x) x < -a x
    dsimp [a]
    linarith [hf x]
  obtain ⟨C,hC⟩ := isCompact_univ.elim_finite_subcover U hU hcov
  obtain ⟨ε,hε,he⟩ := finite_pos_lower_bound C a (fun x _ => ha x)
  refine ⟨ε,hε,?_⟩
  intro z hz
  obtain ⟨x,hx⟩ := mem_iUnion.mp (hC (mem_univ (⟨z,hz⟩ : K)))
  obtain ⟨hxC,hxz⟩ := mem_iUnion.mp hx
  refine ⟨f x,?_⟩
  change w (f x) z < -a x at hxz
  linarith [he x hxC]

lemma compact_zero_fiber_neighborhood {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {σ : X → ℝ} (hσ : Continuous σ) (hnn : ∀ x, 0 ≤ σ x)
    {U : Set X} (hU : IsOpen U) (hzero : ∀ x, σ x = 0 → x ∈ U) :
    ∃ δ > 0, ∀ x, σ x ≤ δ → x ∈ U := by
  by_cases he : Uᶜ = ∅
  · refine ⟨1,by norm_num,?_⟩
    intro x _
    by_contra hx
    have hx' : x ∈ Uᶜ := hx
    simp only [he, mem_empty_iff_false] at hx'
  obtain ⟨x,hx,hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn (nonempty_iff_ne_empty.mpr he) hσ.continuousOn
  have hxpos : 0 < σ x := lt_of_le_of_ne (hnn x) (by
    intro hh
    exact hx (hzero x hh.symm))
  refine ⟨σ x/2,by positivity,?_⟩
  intro y hy
  by_contra hny
  have h : σ x ≤ σ y := hmin hny
  linarith

theorem compact_small_noise_witness {X F : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (w : F → X → ℝ) (hw : ∀ f, ContinuousOn (w f) K)
    {σ : X → ℝ} (hσ : ContinuousOn σ K) (hnn : ∀ x ∈ K, 0 ≤ σ x)
    (hW : ∀ x ∈ K, σ x = 0 → ∃ f, w f x < 0) :
    ∃ a > 0, ∃ δ > 0, ∀ x ∈ K, σ x ≤ δ → ∃ f, w f x < -a := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Z : Set K := {x | σ x = 0}
  have hZ : IsCompact Z := (isClosed_eq hσ.domRestrict continuous_const).isCompact
  obtain ⟨a,ha,hA⟩ := compact_strict_witness hZ (fun f (x : K) => w f x)
    (fun f => (hw f).domRestrict.continuousOn) (fun x hx => hW x.1 x.2 hx)
  let U : Set K := {x | ∃ f, w f x < -(a/2)}
  have hU : IsOpen U := by
    have hu : U = ⋃ f : F, {x : K | w f x < -(a/2)} := by ext x; simp [U]
    rw [hu]
    exact isOpen_iUnion (fun f => isOpen_lt (hw f).domRestrict continuous_const)
  have hzU (x : K) (hx : σ x = 0) : x ∈ U := by
    obtain ⟨f,hf⟩ := hA x hx
    exact ⟨f,by linarith⟩
  obtain ⟨δ,hδ,hd⟩ := compact_zero_fiber_neighborhood hσ.domRestrict
    (fun x : K => hnn x.1 x.2) hU hzU
  exact ⟨a/2,by positivity,δ,hδ,fun x hx hσx => hd ⟨x,hx⟩ hσx⟩

end SKGap

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarSmallNoiseTests
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
namespace SKGap

lemma scalar_small_noise_tests {j R : ℝ} (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hK : IsCompact K)
    (hmom : K ⊆ scalarMomentDomain R) (ht : ∀ p ∈ K, 0 ≤ p.2.1)
    (hσ : ∀ p ∈ K, 0 ≤ p.2.2) (hs : ∀ p ∈ K, 0 < scalarS j p)
    (hne : ∀ p ∈ K, p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∀ p ∈ K, p.2.2 ≤ δ → ∃ f : ℝ →ᵇ ℝ,
      scalarPsi j p-(∫ y, f y ∂p.1)+
        log (∫ y, exp (f y) ∂gaussianReal (scalarD j p) (scalarS j p).toNNReal) < -a := by
  have hw (f : ℝ →ᵇ ℝ) : ContinuousOn (fun p : ScalarPoint =>
      scalarPsi j p-(∫ y, f y ∂p.1)+scalarLogMoment f (scalarD j p) (scalarS j p)) K :=
    (continuousOn_scalar_test hR hj.le f).mono (fun p hp => ⟨hmom hp,hs p hp⟩)
  have hW (p : ScalarPoint) (hp : p ∈ K) (hz : p.2.2 = 0) :
      ∃ f : ℝ →ᵇ ℝ, scalarPsi j p-(∫ y, f y ∂p.1)+scalarLogMoment f (scalarD j p) (scalarS j p) < 0 := by
    have hng : (p.1 : Measure ℝ) ≠ gaussianReal (scalarD j p) (scalarS j p).toNNReal := by
      intro he
      exact hne p hp hz (scalar_gaussian_curve hj hj1 (ht p hp) hz (hs p hp).le he)
    obtain ⟨f,hf⟩ := scalar_strict_test (hmom hp) hj hj1 (ht p hp) (hs p hp) hng
    rw [← scalarLogMoment_eq f _ (hs p hp).le] at hf
    exact ⟨f,hf⟩
  obtain ⟨a,ha,δ,hδ,hall⟩ := compact_small_noise_witness hK _ hw
    (σ := fun p : ScalarPoint => p.2.2) (by fun_prop) hσ hW
  refine ⟨a,ha,δ,hδ,?_⟩
  intro p hp hδp
  obtain ⟨f,hf⟩ := hall p hp hδp
  rw [scalarLogMoment_eq f _ (hs p hp).le] at hf
  exact ⟨f,hf⟩

lemma continuousOn_scalarPsi_of_pos {j R : ℝ} (hj : 0 ≤ j) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hmom : K ⊆ scalarMomentDomain R) (hs : ∀ p ∈ K, 0 < scalarS j p) :
    ContinuousOn (scalarPsi j) K := (continuousOn_scalarPsi hR j).mono (by
      intro p hp
      exact ⟨hmom hp,(hs p hp).ne',ne_of_gt (add_pos_of_pos_of_nonneg (hs p hp)
        (mul_nonneg hj (scalarQMoment_bounds p.1).1))⟩)

theorem scalar_compact_isolation {j R : ℝ} (hj : 0 < j) (hj1 : j < 1) (hR : 0 ≤ R)
    {K : Set ScalarPoint} (hK : IsCompact K)
    (hmom : K ⊆ scalarMomentDomain R) (ht : ∀ p ∈ K, 0 ≤ p.2.1)
    (hσ : ∀ p ∈ K, 0 ≤ p.2.2) (hs : ∀ p ∈ K, 0 < scalarS j p)
    (hne : ∀ p ∈ K, p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n,
      ∀ z : (Fin n → ℝ) → ScalarPoint, ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, z y ∈ K ∧ (z y).2.2 ≤ δ) →
      (∀ y ∈ E, (z y).1 = @empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y) →
      (∀ y ∈ E, ∑ i, (y i)^2 ≤ (n:ℝ)*R) →
      (∫⁻ y in E, ENNReal.ofReal (exp ((n:ℝ)*scalarPsi j (z y))*
        productNormal (scalarD j (z y)) (scalarS j (z y)) y)) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨a,ha,δ,hδ,hW⟩ := scalar_small_noise_tests hj hj1 hR hK hmom ht hσ hs hne
  let K' := K ∩ {p : ScalarPoint | p.2.2 ≤ δ}
  have hK' : IsCompact K' := hK.inter_right (isClosed_le (by fun_prop) continuous_const)
  have hmom' : K' ⊆ scalarMomentDomain R := fun _ hp => hmom hp.1
  have hs' : ∀ p ∈ K', 0 < scalarS j p := fun p hp => hs p hp.1
  obtain ⟨N,hN⟩ := gaussian_compact_rate hK' (P := fun p : ScalarPoint => p.1)
    continuous_fst.continuousOn (continuous_scalarD j).continuousOn (continuous_scalarS j).continuousOn
    (continuousOn_scalarPsi_of_pos hj.le hR hmom' hs') hs' R (-a)
    (fun p hp => hW p hp.1 hp.2) (half_pos ha)
  refine ⟨a/2,half_pos ha,δ,hδ,N,?_⟩
  intro n hn hn' z E hE hz hemp hmomE
  have hh := hN n hn hn' z E hE hz hemp hmomE
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring_nf

end SKGap
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap

lemma scalar_quadratic_envelope {j q a s Q : ℝ} (hj : 0 ≤ j) (hq : 0 ≤ q)
    (hq1 : q ≤ 1) (hs : 0 < s) (hc : j*q ≤ s) (hQ : 0 ≤ Q) (ha : a^2 ≤ q*Q) :
    j*(a-s*(1-q))^2/(2*s*(s+j*q)) ≤ 3*Q/(8*s)+3*j/2 := by
  have hS : 0 < s+j*q := add_pos_of_pos_of_nonneg hs (mul_nonneg hj hq)
  have hsq : (a-s*(1-q))^2 ≤ 3/2*a^2+3*(s*(1-q))^2 := by
    nlinarith [sq_nonneg (a+2*s*(1-q))]
  have hb : (1-q)^2 ≤ 1 := by nlinarith
  have hb' := mul_le_mul_of_nonneg_left hb (sq_nonneg s)
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 3/2*j by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc hQ
  have hss := mul_nonneg hs.le (mul_nonneg hj hq)
  have hsqj := mul_le_mul_of_nonneg_left hsq hj
  have hb'' := mul_le_mul_of_nonneg_left hb' (show 0 ≤ 3*j by positivity)
  apply (div_le_iff₀ (by positivity : 0 < 2*s*(s+j*q))).mpr
  have he : (3*Q/(8*s)+3*j/2)*(2*s*(s+j*q)) = 3/4*Q*(s+j*q)+3*j*s*(s+j*q) := by
    field_simp
    ring
  rw [he]
  have hjs := mul_nonneg hj hss
  nlinarith

lemma sum_centered_sq_lower {ι : Type*} [Fintype ι] (y : ι → ℝ) (d : ℝ) :
    (∑ i, (y i)^2)/2-(Fintype.card ι:ℝ)*d^2 ≤ ∑ i, (y i-d)^2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    show (y i)^2/2-d^2 ≤ (y i-d)^2 by nlinarith [sq_nonneg (y i-2*d)])
  simpa only [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] using h

lemma multiple_gaussian_integrable {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ι → ℝ => exp (-c*∑ i, (y i)^2)) := by
  have h := Integrable.fintype_prod (fun _ : ι => integrable_exp_neg_mul_sq hc)
  simpa only [volume_pi, ← exp_sum, ← Finset.mul_sum] using h

lemma multiple_gaussian_integral {ι : Type*} [Fintype ι] {c : ℝ} (hc : 0 < c) :
    (∫ y : ι → ℝ, exp (-c*∑ i, (y i)^2)) = exp ((Fintype.card ι:ℝ)*log (sqrt (Real.pi/c))) := by
  have he (y : ι → ℝ) : exp (-c*∑ i, (y i)^2) = ∏ i, exp (-c*(y i)^2) := by
    rw [Finset.mul_sum, exp_sum]
  simp_rw [he]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => exp (-c*x^2)), integral_gaussian]
  rw [exp_nat_mul, exp_log (sqrt_pos.mpr (div_pos Real.pi_pos hc))]

theorem quadratic_envelope_tail {ι : Type*} [Fintype ι] {c C R : ℝ} (hc : 0 < c)
    {E : Set (ι → ℝ)} (hE : MeasurableSet E) (f : (ι → ℝ) → ℝ)
    (hf : ∀ y ∈ E, f y ≤ exp ((Fintype.card ι:ℝ)*C-c*∑ i, (y i)^2))
    (htail : ∀ y ∈ E, (Fintype.card ι:ℝ)*R ≤ ∑ i, (y i)^2) :
    (∫⁻ y in E, ENNReal.ofReal (f y)) ≤ ENNReal.ofReal
      (exp ((Fintype.card ι:ℝ)*(C-c*R/2+log (sqrt (Real.pi/(c/2)))))) := by
  let g (y : ι → ℝ) := exp ((Fintype.card ι:ℝ)*(C-c*R/2))*exp (-(c/2)*∑ i, (y i)^2)
  have hg : Integrable g := (multiple_gaussian_integrable (half_pos hc)).const_mul _
  have hgnn (y : ι → ℝ) : 0 ≤ g y := mul_nonneg (exp_pos _).le (exp_pos _).le
  have hdom (y : ι → ℝ) (hy : y ∈ E) : f y ≤ g y := by
    refine (hf y hy).trans ?_
    dsimp [g]
    rw [← exp_add]
    apply exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (htail y hy) hc.le
    nlinarith
  calc
    _ ≤ ∫⁻ y in E, ENNReal.ofReal (g y) := lintegral_mono_ae
      ((ae_restrict_mem hE).mono (fun y hy => ENNReal.ofReal_le_ofReal (hdom y hy)))
    _ ≤ ∫⁻ y, ENNReal.ofReal (g y) := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
    _ = ENNReal.ofReal (∫ y, g y) := (ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hgnn)).symm
    _ = _ := by
      congr 1
      dsimp [g]
      rw [integral_const_mul, multiple_gaussian_integral (half_pos hc), ← exp_add]
      congr 1
      ring

lemma choose_quadratic_tail_radius {c C : ℝ} (hc : 0 < c) (L : ℝ) :
    ∃ R > 0, C-c*R/2+log (sqrt (Real.pi/(c/2))) ≤ -L := by
  let R := max 1 (2*(C+log (sqrt (Real.pi/(c/2)))+L)/c)
  refine ⟨R, (by dsimp [R]; exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  have h : 2*(C+log (sqrt (Real.pi/(c/2)))+L)/c ≤ R := le_max_right _ _
  rw [div_le_iff₀ hc] at h
  nlinarith

end SKGap

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_NormalLogDensityCentered
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap
lemma normalLogDensity_centered (d s x : ℝ) :
    normalLogDensity d s x = -log (sqrt (2*Real.pi*s))-(x-d)^2/(2*s) := by
  unfold normalLogDensity normalLogConst
  ring

lemma gaussian_pointwise_envelope {ι : Type*} [Fintype ι] (y : ι → ℝ)
    {d s j D smin smax ψ : ℝ} (hsmin : 0 < smin) (hsl : smin ≤ s) (hsu : s ≤ smax)
    (hd : d^2 ≤ D^2)
    (hψ : (Fintype.card ι:ℝ)*ψ ≤ 3/(8*s)*(∑ i, (y i-d)^2)+3*(Fintype.card ι:ℝ)*j/2) :
    exp ((Fintype.card ι:ℝ)*ψ)*productNormal d s y ≤
      exp ((Fintype.card ι:ℝ)*(|log (sqrt (2*Real.pi*smin))|+3*j/2+D^2/(8*smin))-
        (1/(16*smax))*∑ i, (y i)^2) := by
  have hs : 0 < s := hsmin.trans_le hsl
  have hmax : 0 < smax := hs.trans_le hsu
  have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hQ : 0 ≤ ∑ i, (y i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hc := sum_centered_sq_lower y d
  have hnd := mul_le_mul_of_nonneg_left hd hn
  have h1 : -(∑ i, (y i-d)^2)/(8*s) ≤
      -(∑ i, (y i)^2)/(16*s)+(Fintype.card ι:ℝ)*D^2/(8*s) := by
    have he : -(∑ i, (y i)^2)/(16*s)+(Fintype.card ι:ℝ)*D^2/(8*s) =
        (-(∑ i, (y i)^2)/2+(Fintype.card ι:ℝ)*D^2)/(8*s) := by ring
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 8*s)
    linarith
  have h2 : -(∑ i, (y i)^2)/(16*s) ≤ -(∑ i, (y i)^2)/(16*smax) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr
  have h3 : (Fintype.card ι:ℝ)*D^2/(8*s) ≤ (Fintype.card ι:ℝ)*D^2/(8*smin) := by
    gcongr
  have hp : 0 < sqrt (2*Real.pi*smin) := sqrt_pos.mpr (by positivity)
  have hlog : log (sqrt (2*Real.pi*smin)) ≤ log (sqrt (2*Real.pi*s)) :=
    log_le_log hp (sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
  have hlog' : -log (sqrt (2*Real.pi*s)) ≤ |log (sqrt (2*Real.pi*smin))| :=
    (neg_le_neg hlog).trans (neg_le_abs _)
  have hnlog := mul_le_mul_of_nonneg_left hlog' hn
  have he : (∑ i, normalLogDensity d s (y i)) =
      -(Fintype.card ι:ℝ)*log (sqrt (2*Real.pi*s))-(∑ i, (y i-d)^2)/(2*s) := by
    simp only [normalLogDensity_centered, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Finset.sum_div]
    ring
  rw [productNormal_eq_exp _ hs, ← exp_add, he]
  apply exp_le_exp.mpr
  calc
    _ ≤ 3/(8*s)*(∑ i, (y i-d)^2)+3*(Fintype.card ι:ℝ)*j/2+
        (-(Fintype.card ι:ℝ)*log (sqrt (2*Real.pi*s))-(∑ i, (y i-d)^2)/(2*s)) :=
      by linarith only [hψ]
    _ = (Fintype.card ι:ℝ)*(-log (sqrt (2*Real.pi*s)))+3*(Fintype.card ι:ℝ)*j/2+
        (-(∑ i, (y i-d)^2)/(8*s)) := by ring
    _ ≤ (Fintype.card ι:ℝ)*|log (sqrt (2*Real.pi*smin))|+3*(Fintype.card ι:ℝ)*j/2+
        (-(∑ i, (y i)^2)/(16*smax)+(Fintype.card ι:ℝ)*D^2/(8*smin)) :=
      add_le_add (by linarith only [hnlog]) (h1.trans (add_le_add h2 h3))
    _ = _ := by ring

end SKGap

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarEmpirical
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma scalarA_empirical (y : ι → ℝ) (j t σ : ℝ) :
    scalarA j (scalarEmpirical y t σ) = (Fintype.card ι:ℝ)⁻¹ *
      ∑ i, (y i-scalarD j (scalarEmpirical y t σ))*tanh (y i) := by
  unfold scalarA scalarM scalarEmpirical
  simp only [integral_empiricalLaw, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma empirical_scalar_cauchy (y : ι → ℝ) (j t σ : ℝ) :
    (scalarA j (scalarEmpirical y t σ))^2 ≤ scalarQMoment (empiricalLaw y)*
      ((Fintype.card ι:ℝ)⁻¹ * ∑ i, (y i-scalarD j (scalarEmpirical y t σ))^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => y i-scalarD j (scalarEmpirical y t σ)) (fun i => tanh (y i))
  have hh := mul_le_mul_of_nonneg_left h (sq_nonneg (Fintype.card ι:ℝ)⁻¹)
  rw [scalarA_empirical, scalarQMoment, integral_empiricalLaw]
  nlinarith only [hh]

lemma scalar_empirical_quadratic_envelope (y : ι → ℝ) {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hs : 0 < scalarS j (scalarEmpirical y t σ)) :
    (Fintype.card ι:ℝ)*scalarPsi j (scalarEmpirical y t σ) ≤
      3/(8*scalarS j (scalarEmpirical y t σ)) *
        (∑ i, (y i-scalarD j (scalarEmpirical y t σ))^2)+3*(Fintype.card ι:ℝ)*j/2 := by
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
  have h := scalar_quadratic_envelope hj (scalarQMoment_bounds (empiricalLaw y)).1
    (scalarQMoment_bounds (empiricalLaw y)).2 hs (scalar_consistency (p := scalarEmpirical y t σ) ht)
    (show 0 ≤ (Fintype.card ι:ℝ)⁻¹*∑ i, (y i-scalarD j (scalarEmpirical y t σ))^2 by positivity)
    (empirical_scalar_cauchy y j t σ)
  have hh := mul_le_mul_of_nonneg_left h hn.le
  change (Fintype.card ι:ℝ)*scalarPsi j (scalarEmpirical y t σ) ≤ _ at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

lemma scalar_empirical_parameter_bounds (y : ι → ℝ) {j t σ T : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (htT : t ≤ T) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    |scalarD j (scalarEmpirical y t σ)| ≤ T+j ∧ scalarS j (scalarEmpirical y t σ) ≤ T+1+j := by
  have hM := scalarM_bounds (empiricalLaw y)
  have hq := (scalarQMoment_bounds (empiricalLaw y)).2
  constructor
  · unfold scalarD scalarEmpirical
    dsimp only
    calc
      |t+j*scalarM (empiricalLaw y)| ≤ |t|+|j*scalarM (empiricalLaw y)| := abs_add_le _ _
      _ ≤ T+j := by
        rw [abs_of_nonneg ht, abs_mul, abs_of_nonneg hj]
        nlinarith
  · unfold scalarS scalarEmpirical
    dsimp only
    have hsq : σ^2 ≤ 1 := by nlinarith
    nlinarith

theorem scalar_integrand_envelope {j T smin : ℝ} (hj : 0 ≤ j) (hT : 0 ≤ T) (hsmin : 0 < smin)
    (y : ι → ℝ) {t σ : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hsl : smin ≤ scalarS j (scalarEmpirical y t σ)) :
    scalarIntegrand j t σ y ≤
      exp ((Fintype.card ι:ℝ)*(|log (sqrt (2*Real.pi*smin))|+3*j/2+(T+j)^2/(8*smin))-
        (1/(16*(T+1+j)))*∑ i, (y i)^2) := by
  have hb := scalar_empirical_parameter_bounds y hj ht htT hσ hσ1
  have hd : (scalarD j (scalarEmpirical y t σ))^2 ≤ (T+j)^2 := by
    have hD : 0 ≤ T+j := add_nonneg hT hj
    have hsq := (sq_le_sq₀ (abs_nonneg _) hD).mpr hb.1
    simpa only [sq_abs] using hsq
  exact gaussian_pointwise_envelope y hsmin hsl hb.2 hd
    (scalar_empirical_quadratic_envelope y hj ht (hsmin.trans_le hsl))

end SKGap

namespace SKGap

lemma empirical_momentBall {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → ℝ) {R : ℝ} (_hR : 0 ≤ R)
    (h : ∑ i, (y i)^2 ≤ (Fintype.card ι:ℝ)*R) : empiricalLaw y ∈ momentBall R := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (x^2) ∂empiricalLaw y) ≤ ENNReal.ofReal R
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_empiricalLaw y _) (ae_of_all _ sq_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_empiricalLaw]
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast (Fintype.card_pos (α := ι))
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hn.le)
  simpa only [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] using hh

lemma isCompact_scalarBox (j R T smin : ℝ) : IsCompact (scalarBox j R T smin) :=
  ((isCompact_momentBall R).prod (isCompact_Icc.prod isCompact_Icc)).inter_right
    (isClosed_le continuous_const (continuous_scalarS j))

theorem scalar_uniform_tail {j T smin : ℝ} (hj : 0 ≤ j) (hT : 0 ≤ T) (hsmin : 0 < smin)
    (L : ℝ) : ∃ R > 0, ∀ n : ℕ, ∀ hn : 0 < n,
      ∀ t ∈ Icc 0 T, ∀ σ ∈ Icc 0 1, ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, smin ≤ scalarS j (@scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ)) →
      (∀ y ∈ E, (n:ℝ)*R ≤ ∑ i, (y i)^2) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-L*(n:ℝ))) := by
  let c := 1/(16*(T+1+j))
  let C := |log (sqrt (2*Real.pi*smin))|+3*j/2+(T+j)^2/(8*smin)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨R,hR,hrate⟩ := choose_quadratic_tail_radius (C := C) hc L
  refine ⟨R,hR,?_⟩
  intro n hn t ht σ hσ E hE hs htE
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have he := quadratic_envelope_tail (C := C) hc hE (scalarIntegrand j t σ)
    (fun y hy => scalar_integrand_envelope hj hT hsmin y ht.1 ht.2 hσ.1 hσ.2 (hs y hy))
    (by simpa only [Fintype.card_fin] using htE)
  simp only [Fintype.card_fin] at he
  refine he.trans (ENNReal.ofReal_le_ofReal (exp_le_exp.mpr ?_))
  have h := mul_le_mul_of_nonneg_left hrate (show (0:ℝ) ≤ n from Nat.cast_nonneg _)
  nlinarith only [h]

lemma lintegral_split_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ≥0∞) (E B : Set α) :
    (∫⁻ x in E, f x ∂μ) ≤ (∫⁻ x in E ∩ B, f x ∂μ)+(∫⁻ x in E ∩ Bᶜ, f x ∂μ) := by
  have h : E = (E ∩ B) ∪ (E ∩ Bᶜ) := by aesop
  conv_lhs => rw [h]
  exact lintegral_union_le _ _ _

end SKGap

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianRegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianRegression

theorem law_eq_of_mean_covariance {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} {P' : Measure Ω'} {X : Ω → ι → ℝ} {Y : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y P')
    (hm : ∀ i, (∫ w, X w i ∂P) = ∫ w, Y w i ∂P')
    (hc : ∀ i k, cov[fun w => X w i, fun w => X w k; P] =
      cov[fun w => Y w i, fun w => Y w k; P']) :
    P.map X = P'.map Y := by
  classical
  have := hX.isProbabilityMeasure
  have := hY.isProbabilityMeasure
  apply Measure.ext_of_charFunDual
  ext L
  rw [hX.charFunDual_map_eq,hY.charFunDual_map_eq]
  let c : ι → ℝ := fun i => L (fun k => if i=k then 1 else 0)
  have hL (x : ι → ℝ) : L x = ∑ i, x i * c i := by
    simpa only [c, smul_eq_mul, ContinuousLinearMap.coe_coe] using L.toLinearMap.pi_apply_eq_sum_univ x
  have hLX : L ∘ X = fun w => ∑ i, X w i*c i := funext (fun w => hL (X w))
  have hLY : L ∘ Y = fun w => ∑ i, Y w i*c i := funext (fun w => hL (Y w))
  have hiX (i : ι) := (hX.eval i).memLp_two
  have hiY (i : ι) := (hY.eval i).memLp_two
  have hem : (∫ w, (L ∘ X) w ∂P) = ∫ w, (L ∘ Y) w ∂P' := by
    rw [hLX,hLY]
    rw [integral_finsetSum _ (fun i _ => ((hX.eval i).integrable.mul_const _)),
      integral_finsetSum _ (fun i _ => ((hY.eval i).integrable.mul_const _))]
    simp only [integral_mul_const,hm]
  have hev : Var[L ∘ X; P] = Var[L ∘ Y; P'] := by
    rw [← covariance_self (hX.map L).aemeasurable,
      ← covariance_self (hY.map L).aemeasurable]
    rw [hLX,hLY]
    rw [covariance_fun_sum_fun_sum (fun i => (hiX i).mul_const _) (fun i => (hiX i).mul_const _),
      covariance_fun_sum_fun_sum (fun i => (hiY i).mul_const _) (fun i => (hiY i).mul_const _)]
    simp only [covariance_mul_const_left,covariance_mul_const_right,hc]
  rw [hev,hem]

theorem residual_independent {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ)
    (hcov : ∀ i k, cov[fun w => X w i, fun w => Y w k; P] =
      ∑ l, K i l * cov[fun w => Y w l,fun w => Y w k; P]) :
    IndepFun (fun w => X w-K*ᵥ Y w) Y P := by
  have := hXY.isProbabilityMeasure
  have hR : HasGaussianLaw (fun w => (X w-K*ᵥ Y w,Y w)) P := by
    exact hXY.map_fun (((ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ))-
      (matrixCLM K).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).prod
      (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))
  apply hR.indepFun_of_covariance_eval
  intro i k
  change cov[fun w => X w i-∑ l, K i l*Y w l,fun w => Y w k; P]=0
  have hK : MemLp (fun w => ∑ l, K i l*Y w l) 2 P :=
    ((hXY.snd.map (matrixCLM K)).eval i).memLp_two
  rw [covariance_fun_sub_left (hXY.fst.eval i).memLp_two hK (hXY.snd.eval k).memLp_two]
  rw [covariance_fun_sum_left (fun l => (hXY.snd.eval l).memLp_two.const_mul _)
    (hXY.snd.eval k).memLp_two]
  simp only [covariance_const_mul_left,hcov,sub_self]

end SKGap.GaussianRegression
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

lemma coordinate_hasLaw {κ : Type*} [Fintype κ] (i : κ) :
    HasLaw (fun g : κ → ℝ => g i) (gaussianReal 0 1) (gaussianCoordinates κ) :=
  ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) i).map_eq⟩

lemma coordinates_gaussian {κ : Type*} [Fintype κ] :
    HasGaussianLaw (fun g : κ → ℝ => g) (gaussianCoordinates κ) :=
  (iIndepFun_pi (fun _ : κ => aemeasurable_id)).hasGaussianLaw
    (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (i k : κ) :
    cov[fun g : κ → ℝ => g i,fun g : κ → ℝ => g k;gaussianCoordinates κ] =
      if i=k then 1 else 0 := by
  by_cases h : i=k
  · subst k
    rw [ite_eq_left rfl,covariance_self (measurable_pi_apply i).aemeasurable,
      (coordinate_hasLaw i).variance_eq]
    simp
  · rw [ite_eq_right h]
    exact ((iIndepFun_pi (fun _ : κ => aemeasurable_id)).indepFun h).covariance_eq_zero
      (coordinate_hasLaw i).hasGaussianLaw.memLp_two (coordinate_hasLaw k).hasGaussianLaw.memLp_two

lemma linear_gaussian_mean {κ : Type*} [Fintype κ] (a : κ → ℝ) :
    (∫ g, ∑ i, a i*g i ∂gaussianCoordinates κ) = 0 := by
  rw [integral_finsetSum _ (fun i _ => (coordinate_hasLaw i).hasGaussianLaw.integrable.const_mul _)]
  simp [integral_const_mul,(coordinate_hasLaw _).integral_eq]

lemma linear_gaussian_covariance {κ : Type*} [Fintype κ] [DecidableEq κ] (a b : κ → ℝ) :
    cov[fun g => ∑ i, a i*g i,fun g => ∑ i, b i*g i;gaussianCoordinates κ] =
      ∑ i, a i*b i := by
  rw [covariance_fun_sum_fun_sum
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)
    (fun i => (coordinate_hasLaw i).hasGaussianLaw.memLp_two.const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,coordinate_covariance]
  simp [mul_comm]

lemma matrix_sample_gaussian {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    HasGaussianLaw (fun g => A*ᵥg) (gaussianCoordinates κ) :=
  coordinates_gaussian.map_fun (GaussianRegression.matrixCLM A)

lemma matrix_sample_covariance {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (i k : ι) :
    cov[fun g => (A*ᵥg) i,fun g => (A*ᵥg) k;gaussianCoordinates κ] = (A*Aᵀ) i k :=
  linear_gaussian_covariance (A i) (A k)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianDisintegration
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal
namespace SKGap.GaussianRegression

lemma residual_joint_gaussian {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ) :
    HasGaussianLaw (fun w => (X w-K*ᵥ Y w,Y w)) P :=
  hXY.map_fun (((ContinuousLinearMap.fst ℝ (ι → ℝ) (κ → ℝ))-
    (matrixCLM K).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ))).prod
    (ContinuousLinearMap.snd ℝ (ι → ℝ) (κ → ℝ)))

theorem regression_joint_law {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Fintype κ] {P : Measure Ω} {X : Ω → ι → ℝ} {Y : Ω → κ → ℝ}
    (hXY : HasGaussianLaw (fun w => (X w,Y w)) P) (K : Matrix ι κ ℝ)
    (hcov : ∀ i k, cov[fun w => X w i, fun w => Y w k; P] =
      ∑ l, K i l * cov[fun w => Y w l,fun w => Y w k; P]) :
    P.map (fun w => (X w,Y w)) =
      ((P.map (fun w => X w-K*ᵥ Y w)).prod (P.map Y)).map
        (fun z : (ι → ℝ) × (κ → ℝ) => (z.1+K*ᵥ z.2,z.2)) := by
  have := hXY.isProbabilityMeasure
  have hR := residual_joint_gaussian hXY K
  have hi := residual_independent hXY K hcov
  rw [← hi.map_prod_eq_prod_map_map hR.fst.aemeasurable hR.snd.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hR.aemeasurable]
  congr 1
  funext w
  simp only [Function.comp_apply,sub_add_cancel]

end SKGap.GaussianRegression
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_RankCovariance
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rankOneCovarianceInverse_mul (s r : ℝ) (m : ι → ℝ)
    (hs : s ≠ 0) (hS : s+r*(m⬝ᵥm) ≠ 0) :
    rankOneCovarianceInverse s r m * rankOneCovariance s r m=1 := by
  simp only [rankOneCovarianceInverse,rankOneCovariance,Matrix.sub_mul,Matrix.mul_add,
    Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,Matrix.mul_one,
    Matrix.vecMulVec_mul_vecMulVec]
  ext i k
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.vecMulVec_apply,Pi.smul_apply]
  field_simp [hs,hS]
  ring

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma rankOneCovariance_det {s : ℝ} (hs : s ≠ 0) (r : ℝ) (m : ι → ℝ) :
    (rankOneCovariance s r m).det=s^(Fintype.card ι)*(1+(r/s)*(m⬝ᵥm)) := by
  have he : rankOneCovariance s r m=s • (1+vecMulVec ((r/s) • m) m) := by
    ext i k
    simp only [rankOneCovariance,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.vecMulVec_apply,Pi.smul_apply]
    field_simp
  rw [he,Matrix.det_smul,Matrix.vecMulVec_eq Unit,Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct_smul,smul_eq_mul]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma rankOneTransform_transpose (a b : ℝ) (u : ι → ℝ) :
    (rankOneTransform a b u)ᵀ=rankOneTransform a b u := by
  ext i k
  simp [rankOneTransform,Matrix.one_apply,Matrix.vecMulVec_apply,eq_comm,mul_comm]

lemma rankOneTransform_mul {u : ι → ℝ} (hu : u⬝ᵥu=1) (a b c d : ℝ) :
    rankOneTransform a b u *rankOneTransform c d u =rankOneTransform (a*c) (b*d) u := by
  simp only [rankOneTransform,Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.one_mul,Matrix.mul_one,Matrix.vecMulVec_mul_vecMulVec,hu]
  ext i k
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.vecMulVec_apply,Pi.smul_apply]
  ring

lemma rankOneTransform_det {a : ℝ} (ha : a ≠ 0) (b : ℝ) {u : ι → ℝ} (hu : u⬝ᵥu=1) :
    (rankOneTransform a b u).det=a^(Fintype.card ι)*(b/a) := by
  have he : rankOneTransform a b u=rankOneCovariance a (b-a) u := rfl
  rw [he,rankOneCovariance_det ha,hu,mul_one]
  congr 1
  field_simp
  ring

lemma rankOneTransform_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) :
    (rankOneTransform a b u)⁻¹=rankOneTransform a⁻¹ b⁻¹ u := by
  apply Matrix.inv_eq_left_inv
  rw [rankOneTransform_mul hu,inv_mul_cancel₀ ha,inv_mul_cancel₀ hb]
  simp [rankOneTransform]

lemma rankOneTransform_mulVec (a b : ℝ) (u x : ι → ℝ) :
    rankOneTransform a b u*ᵥx=a • x+((b-a)*(u⬝ᵥx)) • u := by
  ext i
  simp only [rankOneTransform,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec,Pi.add_apply,Pi.smul_apply,smul_eq_mul,op_smul_eq_smul]
  ring

lemma rankOneTransform_norm_sq {u : ι → ℝ} (hu : u⬝ᵥu=1) (a b : ℝ) (x : ι → ℝ) :
    (rankOneTransform a b u*ᵥx)⬝ᵥ(rankOneTransform a b u*ᵥx)=
      a^2*(x⬝ᵥx)+(b^2-a^2)*(u⬝ᵥx)^2 := by
  rw [rankOneTransform_mulVec]
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,hu]
  rw [dotProduct_comm x u]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianLinearDensity
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → ι → ℝ}

theorem gaussian_density_of_matrix (hX : HasGaussianLaw X P) (A : Matrix ι ι ℝ) (hA : A.det ≠ 0)
    (hm : ∀ i,(∫ w,X w i ∂P)=0)
    (hc : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=(A*Aᵀ) i k) :
    P.map X=(volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal
      (|A.det⁻¹| *∏ i,gaussianPDFReal 0 1 ((A⁻¹*ᵥx) i))) := by
  have hl : P.map X=(gaussianCoordinates ι).map (fun x => A*ᵥx) := by
    apply GaussianRegression.law_eq_of_mean_covariance hX (matrix_sample_gaussian A)
    · intro i
      rw [hm]
      exact (linear_gaussian_mean (A i)).symm
    · intro i k
      rw [hc,matrix_sample_covariance]
  rw [hl]
  exact matrix_map_gaussian_density A hA

lemma gaussian_rankOne_density (hX : HasGaussianLaw X P) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (hm : ∀ i,(∫ w,X w i ∂P)=0)
    (hc : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=
      rankOneTransform (a^2) (b^2) u i k) :
    P.map X=(volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal
      ((a^(Fintype.card ι)*(b/a))⁻¹*∏ i,gaussianPDFReal 0 1
        ((rankOneTransform a⁻¹ b⁻¹ u*ᵥx) i))) := by
  have hd : 0 < (rankOneTransform a b u).det := by
    rw [rankOneTransform_det ha.ne' b hu]
    positivity
  have hc' : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=
      (rankOneTransform a b u*(rankOneTransform a b u)ᵀ) i k := by
    intro i k
    rw [hc,rankOneTransform_transpose,rankOneTransform_mul hu]
    simp only [← pow_two]
  rw [gaussian_density_of_matrix hX _ hd.ne' hm hc',
    rankOneTransform_inv ha.ne' hb.ne' hu,abs_of_pos (inv_pos.mpr hd),rankOneTransform_det ha.ne' b hu]

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma product_gaussianPDF_formula (v : ℝ≥0) (x : ι → ℝ) :
    (∏ i,gaussianPDFReal 0 v (x i))=(sqrt (2*Real.pi*v))⁻¹^(Fintype.card ι)*
      exp (-(x⬝ᵥx)/(2*v)) := by
  simp only [gaussianPDFReal,sub_zero,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,← exp_sum,← Finset.sum_div,← Finset.sum_neg_distrib,dotProduct,← pow_two]

omit [DecidableEq ι] in
lemma product_gaussianPDF_radial {a : ℝ} (ha : 0 ≤ a) (x : ι → ℝ) :
    (∏ i,gaussianPDFReal 0 (NNReal.mk (a^2) (sq_nonneg a)) (x i))=radialDensity a x := by
  rw [product_gaussianPDF_formula]
  simp only [NNReal.coe_mk,radialDensity,sqrt_mul (by positivity : 0 ≤ 2*Real.pi),sqrt_sq ha]

lemma rankOne_density_radial {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {u : ι → ℝ} (hu : u⬝ᵥu=1) (x : ι → ℝ) :
    (a^(Fintype.card ι)*(b/a))⁻¹*(∏ i,gaussianPDFReal 0 1
      ((rankOneTransform a⁻¹ b⁻¹ u*ᵥx) i)) =
    (a/b)*radialDensity a x*exp ((b^2-a^2)/(2*a^2*b^2)*(u⬝ᵥx)^2) := by
  rw [product_gaussianPDF_formula,rankOneTransform_norm_sq hu]
  simp only [NNReal.coe_one,mul_one]
  have he : -(a⁻¹^2*(x⬝ᵥx)+(b⁻¹^2-a⁻¹^2)*(u⬝ᵥx)^2)/2 =
      -(x⬝ᵥx)/(2*a^2)+(b^2-a^2)/(2*a^2*b^2)*(u⬝ᵥx)^2 := by
    field_simp
    ring
  rw [he,exp_add]
  unfold radialDensity
  have hc : (a^(Fintype.card ι)*(b/a))⁻¹*(sqrt (2*Real.pi))⁻¹^(Fintype.card ι)=
      (a/b)*((sqrt (2*Real.pi)*a)⁻¹)^(Fintype.card ι) := by
    simp only [_root_.mul_inv_rev,mul_pow,inv_pow,inv_inv,div_eq_mul_inv]
    ring
  rw [← mul_assoc,← mul_assoc,hc]
  ring

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {X : Ω → ι → ℝ}

omit [Fintype ι] in
lemma rankOne_scaled_covariance (s r c : ℝ) (u : ι → ℝ) :
    rankOneCovariance s r (c • u)=rankOneTransform s (s+r*c^2) u := by
  ext i k
  simp only [rankOneCovariance,rankOneTransform,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.vecMulVec_apply,Pi.smul_apply]
  ring

lemma scaled_unit_exists [Nonempty ι] (m : ι → ℝ) :
    ∃ (c : ℝ) (u : ι → ℝ), 0 ≤ c ∧ u⬝ᵥu=1 ∧ m=c • u := by
  by_cases hm : m=0
  · let i : ι := Classical.choice inferInstance
    refine ⟨0,Pi.single i 1,le_rfl,?_,by simp [hm]⟩
    simp [dotProduct,Pi.single_apply]
  · have hq : 0 < m⬝ᵥm := lt_of_le_of_ne
      (Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i)))
      (Ne.symm (mt dotProduct_self_eq_zero.mp hm))
    have hc : 0 < sqrt (m⬝ᵥm) := sqrt_pos.mpr hq
    refine ⟨sqrt (m⬝ᵥm),(sqrt (m⬝ᵥm))⁻¹ • m,hc.le,?_,?_⟩
    · simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
      have hh := sq_sqrt hq.le
      field_simp
      nlinarith
    · simp [smul_smul,hc.ne']

theorem gaussian_rankOne_covariance_density [Nonempty ι]
    (hX : HasGaussianLaw X P) {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r)
    (m : ι → ℝ) (hm : ∀ i,(∫ w,X w i ∂P)=0)
    (hc : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=rankOneCovariance s r m i k) :
    P.map X=(volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (rankOneDensity s r m x)) := by
  obtain ⟨c,u,hcpos,hu,rfl⟩ := scaled_unit_exists m
  have hS : 0 < s+r*c^2 := add_pos_of_pos_of_nonneg hs (mul_nonneg hr (sq_nonneg c))
  have ha : 0 < sqrt s := sqrt_pos.mpr hs
  have hb : 0 < sqrt (s+r*c^2) := sqrt_pos.mpr hS
  have hc' : ∀ i k,cov[fun w => X w i,fun w => X w k;P]=
      rankOneTransform ((sqrt s)^2) ((sqrt (s+r*c^2))^2) u i k := by
    intro i k
    rw [sq_sqrt hs.le,sq_sqrt hS.le,hc,rankOne_scaled_covariance]
  rw [gaussian_rankOne_density hX ha hb hu hm hc']
  congr 1
  ext x
  rw [rankOne_density_radial ha.ne' hb.ne' hu x]
  simp only [rankOneDensity,smul_dotProduct,dotProduct_smul,smul_eq_mul,hu,mul_one,
    sq_sqrt hs.le,sq_sqrt hS.le]
  have hq : c*c=c^2 := by ring
  rw [hq]
  have hpref : sqrt s/sqrt (s+r*c^2)=sqrt (s/(s+r*c^2)) := (sqrt_div hs.le _).symm
  rw [hpref]
  congr 2
  congr 1
  field_simp
  ring

end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_MatrixCoordinates
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
namespace SKGap

variable {ι : Type*}

variable [Fintype ι]

lemma rawCoordinateMatrix_norm (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖rawCoordinateMatrix g‖ ≤ ‖g‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _)
  simp only [← sq]
  rw [Matrix.frobenius_norm_def,← Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity),
    EuclideanSpace.norm_sq_eq]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs,Fintype.sum_sum_type,Fintype.sum_prod_type,
    rawCoordinateMatrix]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma goeMatrix_norm (r : ℝ) (g : EuclideanSpace ℝ (MatrixCoordinates ι)) :
    ‖goeMatrix r g‖ ≤ sqrt (2*r)*‖g‖ := by
  have he : goeMatrix r g = (sqrt (2*r)/2) •
      (rawCoordinateMatrix g+(rawCoordinateMatrix g)ᵀ) := by ext; rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (sqrt (2*r)/2)*(‖rawCoordinateMatrix g‖+‖(rawCoordinateMatrix g)ᵀ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = sqrt (2*r)*‖rawCoordinateMatrix g‖ := by rw [Matrix.frobenius_norm_transpose]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (rawCoordinateMatrix_norm g) (sqrt_nonneg _)

omit [Fintype ι] in
lemma goeMatrix_sub (r : ℝ) (g h : MatrixCoordinates ι → ℝ) :
    goeMatrix r (g-h) = goeMatrix r g-goeMatrix r h := by
  ext i k; simp only [goeMatrix,Pi.sub_apply,Matrix.sub_apply]; ring

lemma goeMatrix_L2_lipschitz (r : ℝ) :
    LipschitzWith ⟨sqrt (2*r),sqrt_nonneg _⟩
      (fun g : EuclideanSpace ℝ (MatrixCoordinates ι) => goeMatrix r g) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simpa only [dist_eq_norm,← goeMatrix_sub] using! goeMatrix_norm r (g-h)

lemma goeMatrix_pi_lipschitz (r : ℝ) :
    LipschitzWith (⟨sqrt (2*r),sqrt_nonneg _⟩ *
      (Fintype.card (MatrixCoordinates ι) : ℝ≥0) ^ (1/(2:ℝ≥0∞)).toReal)
      (goeMatrix (ι := ι) r) := by
  exact (goeMatrix_L2_lipschitz (ι := ι) r).comp
    (PiLp.lipschitzWith_toLp 2 (fun _ : MatrixCoordinates ι => ℝ))

end SKGap

end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GOEGaussian
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goeEntryCoeff_sample (r : ℝ) (g : MatrixCoordinates ι → ℝ) (i k : ι) :
    (goeEntryCoeff r*ᵥg) (i,k) = goeMatrix r g i k := by
  simp only [mulVec,dotProduct,goeEntryCoeff,mul_assoc,add_mul]
  rw [← Finset.mul_sum,Finset.sum_add_distrib]
  simp [goeMatrix]

lemma goe_matrix_gaussian (r : ℝ) :
    HasGaussianLaw (fun (g : MatrixCoordinates ι → ℝ) (p : ι × ι) => goeMatrix r g p.1 p.2) (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := matrix_sample_gaussian (goeEntryCoeff (ι := ι) r)
  simpa only [show (fun g => goeEntryCoeff (ι := ι) r*ᵥg) =
    (fun g p => goeMatrix r g p.1 p.2) from funext (fun g => funext (fun p => goeEntryCoeff_sample r g p.1 p.2))] using hh

lemma goe_entry_cov {r : ℝ} (hr : 0 ≤ r) (i k l m : ι) :
    cov[fun g => goeMatrix r g i k,fun g => goeMatrix r g l m;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then 1 else 0)*(if k=m then 1 else 0)+
       (if i=m then 1 else 0)*(if k=l then 1 else 0)) := by
  let μ := gaussianCoordinates (MatrixCoordinates ι)
  have hm (a : MatrixCoordinates ι) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  change cov[fun g : MatrixCoordinates ι → ℝ => sqrt (2*r)/2*(g (.inl (i,k))+g (.inl (k,i))),
    fun g => sqrt (2*r)/2*(g (.inl (l,m))+g (.inl (m,l))); μ]=_
  rw [covariance_const_mul_left,covariance_const_mul_right]
  change sqrt (2*r)/2*(sqrt (2*r)/2*cov[(fun g => g (.inl (i,k))) + (fun g => g (.inl (k,i))),
    (fun g => g (.inl (l,m))) + (fun g => g (.inl (m,l)));gaussianCoordinates (MatrixCoordinates ι)]) = _
  rw [covariance_add_left (hm _) (hm _) ((hm _).add (hm _)),
    covariance_add_right (hm _) (hm _) (hm _),
    covariance_add_right (hm _) (hm _) (hm _)]
  simp only [coordinate_covariance,Sum.inl.injEq,Prod.mk.injEq]
  have hs : (sqrt (2*r)/2)^2=r/2 := by rw [div_pow,sq_sqrt (by positivity)]; ring
  have hs' : sqrt (2*r)/2*(sqrt (2*r)/2)=r/2 := by nlinarith only [hs]
  rw [← mul_assoc,hs']
  have hind (p q : Prop) [Decidable p] [Decidable q] :
      (if p ∧ q then (1:ℝ) else 0)=(if p then 1 else 0)*(if q then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [hind]
  ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_GOEObservation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma observationCoeff_sample (r v : ℝ) (m : ι → ℝ) (g : MatrixCoordinates ι → ℝ) :
    observationCoeff r v m*ᵥg=goeObservation r v m g := by
  ext i
  change (∑ a, ((∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0))*g a)=
    (∑ k, goeMatrix r g i k*m k)+sqrt v*g (.inr i)
  rw [show (∑ a, ((∑ k, m k*goeEntryCoeff r (i,k) a)+sqrt v*(if a=Sum.inr i then 1 else 0))*g a)=
    (∑ a, (∑ k, m k*goeEntryCoeff r (i,k) a)*g a)+sqrt v*g (.inr i) by
      simp [add_mul,Finset.sum_add_distrib]]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have hh := goeEntryCoeff_sample r g i k
  change (∑ a, m k*goeEntryCoeff r (i,k) a*g a)=goeMatrix r g i k*m k
  rw [show (∑ a, m k*goeEntryCoeff r (i,k) a*g a)=m k*((goeEntryCoeff r*ᵥg) (i,k)) by
    simp only [mulVec,dotProduct,Finset.mul_sum,mul_assoc]]
  rw [hh,mul_comm]

lemma goe_observation_joint_gaussian (r v : ℝ) (m : ι → ℝ) :
    HasGaussianLaw (fun g => ((fun p : ι × ι => goeMatrix r g p.1 p.2),goeObservation r v m g))
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := coordinates_gaussian.map_fun
    ((GaussianRegression.matrixCLM (goeEntryCoeff (ι := ι) r)).prod
      (GaussianRegression.matrixCLM (observationCoeff r v m)))
  apply hh.congr
  filter_upwards [] with g
  simp only [ContinuousLinearMap.prod_apply,GaussianRegression.matrixCLM_apply,
    observationCoeff_sample]
  congr 1
  funext p
  exact goeEntryCoeff_sample r g p.1 p.2

lemma goe_noise_cov (r : ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0 := by
  have hm (a : MatrixCoordinates ι) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  change cov[fun g : MatrixCoordinates ι → ℝ => sqrt (2*r)/2*(g (.inl (i,k))+g (.inl (k,i))),
    fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0
  rw [covariance_const_mul_left]
  change sqrt (2*r)/2*cov[(fun g => g (.inl (i,k)))+(fun g => g (.inl (k,i))),
    fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0
  rw [covariance_add_left (hm _) (hm _) (hm _)]
  simp [coordinate_covariance]

lemma goe_mulVec_memLp (r : ℝ) (m : ι → ℝ) (i : ι) :
    MemLp (fun g => (goeMatrix r g*ᵥm) i) 2 (gaussianCoordinates (MatrixCoordinates ι)) := by
  have hh := memLp_finsetSum (Finset.univ : Finset ι)
    (fun k _ => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (m k))
  simpa only [mulVec,dotProduct] using hh

lemma goe_entry_observation_cov {r : ℝ} (hr : 0 ≤ r) (v : ℝ) (m : ι → ℝ) (i k l : ι) :
    cov[fun g => goeMatrix r g i k,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then m k else 0)+(if k=l then m i else 0)) := by
  have hW := (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two
  have hM := goe_mulVec_memLp r m l
  have hN := (coordinate_hasLaw (Sum.inr l : MatrixCoordinates ι)).hasGaussianLaw.memLp_two.const_mul (sqrt v)
  change cov[fun g => goeMatrix r g i k,(fun g => (goeMatrix r g*ᵥm) l)+
    (fun g => sqrt v*g (.inr l));gaussianCoordinates (MatrixCoordinates ι)] = _
  rw [covariance_add_right hW hM hN,covariance_const_mul_right,goe_noise_cov,mul_zero,add_zero]
  change cov[fun g => goeMatrix r g i k,fun g => ∑ a, goeMatrix r g l a*m a;_]=_
  rw [covariance_fun_sum_right (fun a => (goe_matrix_gaussian (ι := ι) r).eval (l,a) |>.memLp_two.mul_const (m a)) hW]
  simp only [covariance_mul_const_right,goe_entry_cov hr]
  by_cases hil : i=l <;> by_cases hkl : k=l <;>
    simp [hil,hkl,mul_add,add_mul,Finset.sum_add_distrib]

lemma goe_mulVec_noise_cov (r : ℝ) (m : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥm) i,fun g => g (.inr l);gaussianCoordinates (MatrixCoordinates ι)]=0 := by
  change cov[fun g => ∑ a, goeMatrix r g i a*m a,fun g => g (.inr l);_]=_
  rw [covariance_fun_sum_left
    (fun a => (goe_matrix_gaussian (ι := ι) r).eval (i,a) |>.memLp_two.mul_const (m a))
    (coordinate_hasLaw (Sum.inr l : MatrixCoordinates ι)).hasGaussianLaw.memLp_two]
  simp [covariance_mul_const_left,goe_noise_cov]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_mulVec_cov {r : ℝ} (hr : 0 ≤ r) (m : ι → ℝ) (i l : ι) :
    cov[fun g => (goeMatrix r g*ᵥm) i,fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    r*((if i=l then ∑ k, m k^2 else 0)+m i*m l) := by
  have hc (k : ι) : cov[fun g => goeMatrix r g i k,fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      r*((if i=l then m k else 0)+(if k=l then m i else 0)) := by
    simpa only [goeObservation,sqrt_zero,zero_mul,add_zero] using
      goe_entry_observation_cov hr 0 m i k l
  change cov[fun g => ∑ k, goeMatrix r g i k*m k,fun g => (goeMatrix r g*ᵥm) l;_]=_
  rw [covariance_fun_sum_left
    (fun k => (goe_matrix_gaussian (ι := ι) r).eval (i,k) |>.memLp_two.mul_const (m k))
    (goe_mulVec_memLp r m l)]
  simp only [covariance_mul_const_left,hc]
  by_cases h : i=l
  · subst l
    simp [mul_add,add_mul,mul_assoc,← pow_two,Finset.sum_add_distrib,← Finset.mul_sum]
  · simp [h,mul_ite,ite_mul]
    ring

lemma goe_observation_mean (r v : ℝ) (m : ι → ℝ) (i : ι) :
    (∫ g, goeObservation r v m g i ∂gaussianCoordinates (MatrixCoordinates ι))=0 := by
  simpa only [← observationCoeff_sample,mulVec,dotProduct] using
    linear_gaussian_mean (observationCoeff r v m i)

lemma goe_observation_cov {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v) (m : ι → ℝ) (i l : ι) :
    cov[fun g => goeObservation r v m g i,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
      (r*(∑ k,m k^2)+v)*(if i=l then 1 else 0)+r*m i*m l := by
  have hm (k : ι) := goe_mulVec_memLp r m k
  have hn (k : ι) := (coordinate_hasLaw (Sum.inr k : MatrixCoordinates ι)).hasGaussianLaw.memLp_two
  change cov[(fun g => (goeMatrix r g*ᵥm) i)+(fun g => sqrt v*g (.inr i)),
    (fun g => (goeMatrix r g*ᵥm) l)+(fun g => sqrt v*g (.inr l));_]=_
  rw [covariance_add_left (hm i) ((hn i).const_mul _) ((hm l).add ((hn l).const_mul _)),
    covariance_add_right (hm i) (hm l) ((hn l).const_mul _),
    covariance_add_right ((hn i).const_mul _) (hm l) ((hn l).const_mul _)]
  have hback : cov[fun g => g (.inr i),fun g => (goeMatrix r g*ᵥm) l;
      gaussianCoordinates (MatrixCoordinates ι)]=0 := by
    rw [covariance_comm,goe_mulVec_noise_cov]
  rw [covariance_const_mul_right,goe_mulVec_noise_cov,mul_zero,add_zero,
    covariance_const_mul_left,hback,mul_zero,
    covariance_const_mul_left,covariance_const_mul_right,coordinate_covariance,
    goe_mulVec_cov hr]
  simp only [Sum.inr.injEq]
  by_cases hil : i=l
  · simp only [hil,ite_true,mul_one]
    rw [mul_self_sqrt hv]
    ring
  · simp only [hil,ite_false,mul_zero,zero_add,add_zero]
    ring

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Matrix_GOERegression
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma goe_observation_cov_matrix {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v) (m : ι → ℝ) :
    (fun i l => cov[fun g => goeObservation r v m g i,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)])=rankOneCovariance (r*(m⬝ᵥm)+v) r m := by
  ext i l
  rw [goe_observation_cov hr hv]
  simp only [rankOneCovariance,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.vecMulVec_apply,dotProduct,← pow_two]
  ring

lemma goe_regression_covariance {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m : ι → ℝ)
    (p : ι × ι) (l : ι) :
    cov[fun g => goeMatrix r g p.1 p.2,fun g => goeObservation r v m g l;
      gaussianCoordinates (MatrixCoordinates ι)] =
    ∑ k, goeRegressionCoefficient r v m p k *
      cov[fun g => goeObservation r v m g k,fun g => goeObservation r v m g l;
        gaussianCoordinates (MatrixCoordinates ι)] := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun k _ => mul_self_nonneg (m k))
  have hs : 0 < r*(m⬝ᵥm)+v := add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv
  have hS : 0 < r*(m⬝ᵥm)+v+r*(m⬝ᵥm) := add_pos_of_pos_of_nonneg hs (mul_nonneg hr hq)
  have hmat := goe_observation_cov_matrix hr hv.le m
  rw [goe_entry_observation_cov hr]
  change goeCrossCovariance r m p l =
    (goeRegressionCoefficient r v m * (show Matrix ι ι ℝ from fun k l => cov[fun g => goeObservation r v m g k,
      fun g => goeObservation r v m g l;gaussianCoordinates (MatrixCoordinates ι)])) p l
  rw [hmat,goeRegressionCoefficient,Matrix.mul_assoc,
    rankOneCovarianceInverse_mul _ _ _ hs.ne' hS.ne',Matrix.mul_one]

end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real GaussianDensity
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma radialDensity_pos {a : ℝ} (ha : 0 < a) (x : ι → ℝ) : 0 < radialDensity a x := by
  unfold radialDensity
  positivity

omit [DecidableEq ι] in
lemma radialDensity_le {a : ℝ} (ha : 0 < a) (x : ι → ℝ) :
    radialDensity a x ≤ ((sqrt (2*Real.pi)*a)⁻¹)^(Fintype.card ι) := by
  unfold radialDensity
  apply mul_le_of_le_one_right (by positivity)
  apply exp_le_one_iff.mpr
  have hx : 0 ≤ x⬝ᵥx := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) (by positivity)

omit [DecidableEq ι] in
lemma continuous_rankOneDensity (s r : ℝ) (m : ι → ℝ) :
    Continuous (rankOneDensity s r m) := by
  unfold rankOneDensity radialDensity dotProduct
  fun_prop

omit [DecidableEq ι] in
lemma rankOneDensity_pos {s r : ℝ} (hs : 0 < s) (hr : 0 ≤ r) (m x : ι → ℝ) :
    0 < rankOneDensity s r m x := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i))
  have hS : 0 < s+r*(m⬝ᵥm) := add_pos_of_pos_of_nonneg hs (mul_nonneg hr hq)
  unfold rankOneDensity
  exact mul_pos (mul_pos (sqrt_pos.mpr (div_pos hs hS)) (radialDensity_pos (sqrt_pos.mpr hs) x)) (exp_pos _)

theorem goe_observation_density [Nonempty ι] {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m : ι → ℝ) :
    (gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v m)=
      (volume : Measure (ι → ℝ)).withDensity (fun x =>
        ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m x)) := by
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i))
  apply gaussian_rankOne_covariance_density (goe_observation_joint_gaussian r v m).snd
    (add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv) hr m (goe_observation_mean r v m)
  intro i k
  exact congrFun (congrFun (goe_observation_cov_matrix hr hv.le m) i) k

lemma goe_noise_density [Nonempty ι] {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) :
    (gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v 0)=
      (volume : Measure (ι → ℝ)).withDensity (fun x => ENNReal.ofReal (radialDensity (sqrt v) x)) := by
  rw [goe_observation_density hr hv]
  congr 1
  ext x
  simp [rankOneDensity,hv.ne']

lemma goe_noise_independent (r v : ℝ) :
    IndepFun (fun g (p : ι × ι) => goeMatrix r g p.1 p.2) (goeObservation r v 0)
      (gaussianCoordinates (MatrixCoordinates ι)) := by
  apply (goe_observation_joint_gaussian r v 0).indepFun_of_covariance_eval
  intro p i
  have he (g : MatrixCoordinates ι → ℝ) : goeObservation r v 0 g i=sqrt v*g (.inr i) := by
    simp [goeObservation]
  simp only [he,covariance_const_mul_right,goe_noise_cov,mul_zero]

lemma goe_joint_noise_law (r v : ℝ) (m : ι → ℝ) :
    (((gaussianCoordinates (MatrixCoordinates ι)).map (fun g (p : ι × ι) => goeMatrix r g p.1 p.2)).prod
      ((gaussianCoordinates (MatrixCoordinates ι)).map (goeObservation r v 0))).map
      (fun z : ((ι × ι) → ℝ) × (ι → ℝ) => (z.1,(fun i => ∑ k, z.1 (i,k)*m k)+z.2)) =
      (gaussianCoordinates (MatrixCoordinates ι)).map (fun g =>
        ((fun p : ι × ι => goeMatrix r g p.1 p.2),goeObservation r v m g)) := by
  have hXY := goe_observation_joint_gaussian (ι := ι) r v 0
  rw [← (goe_noise_independent (ι := ι) r v).map_prod_eq_prod_map_map hXY.fst.aemeasurable hXY.snd.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) hXY.aemeasurable]
  apply congrArg (fun f => (gaussianCoordinates (MatrixCoordinates ι)).map f)
  funext g
  apply Prod.ext
  · rfl
  ext i
  simp [goeObservation,mulVec,dotProduct]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_ScalarGaussianReductionAlgebra
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

lemma radialDensity_translate (a c : ℝ) (x m : ι → ℝ) :
    radialDensity a (x+c • m)=radialDensity a x*
      exp (-(2*c*(x⬝ᵥm)+c^2*(m⬝ᵥm))/(2*a^2)) := by
  unfold radialDensity
  simp only [add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm m x]
  have he : -(x⬝ᵥx+c*(x⬝ᵥm)+c*(x⬝ᵥm+c*(m⬝ᵥm)))/(2*a^2)=
      -(x⬝ᵥx)/(2*a^2)+(-(2*c*(x⬝ᵥm)+c^2*(m⬝ᵥm))/(2*a^2)) := by ring
  rw [he,exp_add]
  ring

lemma gaussian_density_shift (d : ℝ) {s : ℝ} (hs : 0 ≤ s) (y : ι → ℝ) :
    (∏ i,gaussianPDFReal d (NNReal.mk s hs) (y i))=
      radialDensity (sqrt s) (fun i => y i-d) := by
  have he (i : ι) : gaussianPDFReal d (NNReal.mk s hs) (y i)=
      gaussianPDFReal 0 (NNReal.mk s hs) (y i-d) := by simp [gaussianPDFReal]
  simp only [he]
  have hv : NNReal.mk s hs=NNReal.mk ((sqrt s)^2) (sq_nonneg (sqrt s)) := by
    ext
    exact (sq_sqrt hs).symm
  rw [hv,product_gaussianPDF_radial (sqrt_nonneg _)]

lemma scalar_gaussian_exponent {n s S j q b a : ℝ} (hn : n ≠ 0) (hs : s ≠ 0)
    (hS : S ≠ 0) (hSq : S=s+j*q) :
    -(2*(j*b)*(n*a)+(j*b)^2*(n*q))/(2*s)+
      (j/n)/(2*s*S)*(n*a+j*b*(n*q))^2+n*j*b^2/2 =
      n*j*(a-s*b)^2/(2*s*S) := by
  subst S
  field_simp
  ring

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

theorem rankOneDensity_cancellation {n s S j q b a : ℝ} (hn : n ≠ 0)
    (hs : 0 < s) (hS : S ≠ 0) (hSq : S=s+j*q)
    (x m : ι → ℝ) (hm : m⬝ᵥm=n*q) (hx : x⬝ᵥm=n*a) :
    rankOneDensity s (j/n) m (x+(j*b) • m)*exp (n*j*b^2/2) =
    sqrt (s/S)*radialDensity (sqrt s) x*exp (n*j*(a-s*b)^2/(2*s*S)) := by
  have he : s+(j/n)*(m⬝ᵥm)=S := by rw [hm,hSq]; field_simp
  rw [rankOneDensity,he,radialDensity_translate,sq_sqrt hs.le,hm,hx]
  simp only [dotProduct_add,dotProduct_smul,smul_eq_mul]
  rw [dotProduct_comm m x,hm,hx]
  have hE := scalar_gaussian_exponent hn hs.ne' hS hSq (j := j) (q := q) (b := b) (a := a)
  calc
    _ = sqrt (s/S)*radialDensity (sqrt s) x*
        exp (-(2*(j*b)*(n*a)+(j*b)^2*(n*q))/(2*s)+
          (j/n)/(2*s*S)*(n*a+j*b*(n*q))^2+n*j*b^2/2) := by rw [exp_add,exp_add]; ring
    _ = _ := by rw [hE]

end SKGap.GaussianDensity
end
end

section
noncomputable section
namespace SKGap.GaussianDensity
open MeasureTheory ProbabilityTheory Matrix Real Set
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι]

lemma pi_gaussian_convolution (m₁ m₂ : ι → ℝ) (v₁ v₂ : ι → ℝ≥0) :
    ((Measure.pi (fun i=>gaussianReal (m₁ i) (v₁ i))).prod
      (Measure.pi (fun i=>gaussianReal (m₂ i) (v₂ i)))).map (fun p=>p.1+p.2)=
    Measure.pi (fun i=>gaussianReal (m₁ i+m₂ i) (v₁ i+v₂ i)) := by
  have h := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun i=>gaussianReal (m₁ i) (v₁ i)) (fun i=>gaussianReal (m₂ i) (v₂ i))).map_eq
  rw [← h,Measure.map_map (by fun_prop) (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).measurable]
  change (Measure.pi (fun i=>(gaussianReal (m₁ i) (v₁ i)).prod (gaussianReal (m₂ i) (v₂ i)))).map
    (fun x i=> (x i).1+(x i).2)=_
  have (i : ι) : IsProbabilityMeasure (((gaussianReal (m₁ i) (v₁ i)).prod
      (gaussianReal (m₂ i) (v₂ i))).map (fun p : ℝ×ℝ=>p.1+p.2)) :=
    (by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability))
  rw [Measure.pi_map_pi (f := fun (_ : ι) (p : ℝ×ℝ)=>p.1+p.2) (fun _=>by fun_prop)]
  congr 1
  funext i
  exact gaussianReal_conv_gaussianReal

theorem continuous_convolution_density (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    {φ p : (ι → ℝ) → ℝ} (hφ : Continuous φ) (hp : Continuous p)
    (hφpos : ∀ x,0 ≤ φ x)
    {C : ℝ} (hφC : ∀ x,φ x ≤ C)
    (hconv : (μ.prod ((volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (φ x)))).map
      (fun q=>q.1+q.2)=(volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (p x)))
    (z : ι → ℝ) :
    (∫⁻ x, ENNReal.ofReal (φ (z-x)) ∂μ)=ENNReal.ofReal (p z) := by
  let K : (ι → ℝ) → ℝ≥0∞ := fun y=>∫⁻ x,ENNReal.ofReal (φ (y-x)) ∂μ
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hae : K=ᵐ[volume] (fun y=>ENNReal.ofReal (p y)) := by
    apply (withDensity_eq_iff_of_sigmaFinite hK.aemeasurable hp.measurable.ennreal_ofReal.aemeasurable).mp
    ext s hs
    rw [withDensity_apply _ hs,withDensity_apply _ hs]
    let F : (ι → ℝ) × (ι → ℝ) → ℝ≥0∞ := fun q=>s.indicator (fun _=>1) q.2
    have hF : Measurable F := measurable_const.indicator (hs.preimage measurable_snd)
    have hh := additive_noise_lintegral μ (fun x=>ENNReal.ofReal (φ x))
      hφ.measurable.ennreal_ofReal id measurable_id F hF
    have hm : Measurable (s.indicator (fun _=> (1 : ℝ≥0∞))) := measurable_const.indicator hs
    have he := congrArg (fun ν=>∫⁻ y,s.indicator (fun _=> (1 : ℝ≥0∞)) y ∂ν) hconv
    rw [lintegral_map hm (by fun_prop),lintegral_withDensity_eq_lintegral_mul _
      hp.measurable.ennreal_ofReal hm] at he
    change (∫⁻ q,F (q.1,id q.1+q.2) ∂μ.prod (volume.withDensity (fun x=>ENNReal.ofReal (φ x))))=_ at he
    rw [hh] at he
    have hleft (y : ι → ℝ) : (∫⁻ x, ENNReal.ofReal (φ (y-id x))*F (x,y) ∂μ)=s.indicator K y := by
      by_cases hy : y∈s <;> simp [F,K,hy]
    have hright (y : ι → ℝ) : ENNReal.ofReal (p y)*s.indicator (fun _=>(1 : ℝ≥0∞)) y=
        s.indicator (fun y=>ENNReal.ofReal (p y)) y := by by_cases hy : y∈s <;> simp [hy]
    simp only [Pi.mul_apply,hleft,hright,lintegral_indicator hs] at he
    exact he
  have hi (y : ι → ℝ) : Integrable (fun x=>φ (y-x)) μ :=
    integrable_bounded μ (by fun_prop) (fun x=>by rw [norm_eq_abs,abs_of_nonneg (hφpos _)]; exact hφC _)
  have hc : Continuous (fun y : ι → ℝ=>∫ x,φ (y-x) ∂μ) := by
    apply continuous_of_dominated (bound := fun _=>C)
    · intro y; exact (hi y).aestronglyMeasurable
    · intro y; exact Filter.Eventually.of_forall (fun x=>by rw [norm_eq_abs,abs_of_nonneg (hφpos _)]; exact hφC _)
    · exact integrable_const C
    · exact Filter.Eventually.of_forall (fun x=>by fun_prop)
  have he (y : ι → ℝ) : K y=ENNReal.ofReal (∫ x,φ (y-x) ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal (hi y) (Filter.Eventually.of_forall (fun x=>hφpos _))).symm
  have hcont : Continuous K := by rw [show K=(fun y=>ENNReal.ofReal (∫ x,φ (y-x) ∂μ)) from funext he]; exact ENNReal.continuous_ofReal.comp hc
  exact congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (ι → ℝ)) hcont
    (ENNReal.continuous_ofReal.comp hp)).mp hae) z

theorem gaussian_radial_convolution {t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ) (z : ι → ℝ) :
    (∫⁻ x, ENNReal.ofReal (radialDensity σ (z-x))
      ∂Measure.pi (fun _ : ι=>gaussianReal 0 t.toNNReal))=
    ENNReal.ofReal (radialDensity (sqrt (t+σ^2)) z) := by
  classical
  have hv : 0 < t+σ^2 := add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)
  have hnoise : Measure.pi (fun _ : ι=>gaussianReal 0 (NNReal.mk (σ^2) (sq_nonneg σ)))=
      (volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (radialDensity σ x)) := by
    rw [pi_gaussian_density _ _ (fun _=>by intro hh; have hh' := congrArg (fun r : ℝ≥0=>(r:ℝ)) hh; exact (sq_pos_of_pos hσ).ne' hh')]
    congr 1; funext x; rw [product_gaussianPDF_radial hσ.le]
  have hout : Measure.pi (fun _ : ι=>gaussianReal 0 (t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)))=
      (volume : Measure (ι → ℝ)).withDensity (fun x=>ENNReal.ofReal (radialDensity (sqrt (t+σ^2)) x)) := by
    rw [pi_gaussian_density _ _ (fun _=>by
      have he : (↑(t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)):ℝ)=t+σ^2 := by simp [Real.coe_toNNReal _ ht]
      exact_mod_cast (show (↑(t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)):ℝ)≠0 by rw [he]; exact hv.ne'))]
    congr 1; funext x
    have he : t.toNNReal+NNReal.mk (σ^2) (sq_nonneg σ)=NNReal.mk ((sqrt (t+σ^2))^2) (sq_nonneg _) := by
      ext; simp [Real.coe_toNNReal _ ht,sq_sqrt hv.le]
    rw [he,product_gaussianPDF_radial (sqrt_nonneg _)]
  apply continuous_convolution_density _ (continuous_radialDensity σ)
    (continuous_radialDensity _) (fun x=>(radialDensity_pos hσ x).le)
    (radialDensity_le hσ)
  rw [← hnoise,pi_gaussian_convolution]
  simpa only [zero_add] using hout
end SKGap.GaussianDensity
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_ConditionalObservationData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarA_empirical_sum {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    ∑ i,tanh (y i)*(y i-scalarD j (empiricalLaw y,t,σ))=
      (n:ℝ)*scalarA j (empiricalLaw y,t,σ) := by
  simp only [scalarA,scalarM,integral_empiricalLaw,Fintype.card_fin]
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  rw [mul_sub,← mul_assoc,mul_inv_cancel₀ hn,one_mul]
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _; ring
  · rw [← Finset.sum_mul]
    field_simp

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Posterior_GOEPointwisePosterior
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct _root_.OAI.SKGap.conditionalGoeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Matrix Real GaussianDensity GaussianRegression
open scoped BigOperators ENNReal NNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem goe_pointwise_posterior {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (m z : ι → ℝ) :
    (goeLaw (ι := ι) r).withDensity (fun W => ENNReal.ofReal
      (radialDensity (sqrt v) (z-(fun i => ∑ k, W (i,k)*m k)))) =
    ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m z) • conditionalGoeLaw r v m z := by
  have hXY := goe_observation_joint_gaussian r v m
  let : IsProbabilityMeasure (goeLaw (ι := ι) r) :=
    Measure.isProbabilityMeasure_map (measurable_pi_lambda _ fun p => by unfold goeMatrix; fun_prop).aemeasurable
  let ρ := (gaussianCoordinates (MatrixCoordinates ι)).map (goeRegressionResidual r v m)
  have hreg := regression_joint_law hXY (goeRegressionCoefficient r v m) (goe_regression_covariance hr hv m)
  have hj := goe_joint_noise_law r v m
  rw [goe_noise_density hr hv] at hj
  rw [goe_observation_density hr hv m] at hreg
  have hjoint : ((goeLaw (ι := ι) r).prod ((volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (radialDensity (sqrt v) x)))).map
      (fun q => (q.1,(fun i => ∑ k, q.1 (i,k)*m k)+q.2)) =
    (ρ.prod ((volume : Measure (ι → ℝ)).withDensity
      (fun x => ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m x)))).map
      (fun q => (q.1+goeRegressionCoefficient r v m*ᵥq.2,q.2)) := hj.trans hreg
  have hq : 0 ≤ m⬝ᵥm := Finset.sum_nonneg (fun i _ => mul_self_nonneg (m i))
  have hs := add_pos_of_nonneg_of_pos (mul_nonneg hr hq) hv
  exact continuous_kernel_posterior (goeLaw (ι := ι) r) ρ (continuous_radialDensity _)
    (continuous_rankOneDensity _ _ m) (fun x => (radialDensity_pos (sqrt_pos.mpr hv) x).le)
    (fun x => (rankOneDensity_pos hs hr m x).le) (by positivity)
    (radialDensity_le (sqrt_pos.mpr hv)) (by fun_prop) (by fun_prop) hjoint z

theorem goe_pointwise_conditional_integral {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v)
    (m z : ι → ℝ) (f : ((ι × ι) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, ENNReal.ofReal (radialDensity (sqrt v) (z-goeMatrix r g*ᵥm))*
      f (fun p => goeMatrix r g p.1 p.2) ∂gaussianCoordinates (MatrixCoordinates ι)) =
    ENNReal.ofReal (rankOneDensity (r*(m⬝ᵥm)+v) r m z)*
      (∫⁻ W, f W ∂conditionalGoeLaw r v m z) := by
  have hh := congrArg (fun ν => ∫⁻ W, f W ∂ν) (goe_pointwise_posterior hr hv m z)
  have hφ : Measurable (fun W : (ι × ι) → ℝ => ENNReal.ofReal (radialDensity (sqrt v) (z-(fun i => ∑ k, W (i,k)*m k)))) :=
    ((continuous_radialDensity _).comp (by fun_prop)).measurable.ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hφ hf,lintegral_smul_measure] at hh
  rw [goeLaw,lintegral_map (hφ.mul hf) (by unfold goeMatrix; fun_prop)] at hh
  exact hh

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalHessianLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Frobenius

lemma scalarQMoment_empirical_overlap {n : ℕ} [NeZero n] (y : Fin n → ℝ) :
    scalarQMoment (empiricalLaw y)=overlap y := by
  simp only [scalarQMoment,integral_empiricalLaw,Fintype.card_fin,overlap,magnetization,
    div_eq_mul_inv,mul_comm]

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Gaussian_GaussianReductionPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma tapField_planted_observation {n : ℕ} [NeZero n] (j t σ : ℝ)
    (y x : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) :
    tapField j (plantedInteraction j W) (fun i=>t+x i) y=
      empiricalObservation j t σ y-W*ᵥmagnetization y-x := by
  ext i
  simp only [tapField,plantedInteraction,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,vecMulVec_apply,mul_one,add_mul,Finset.sum_add_distrib,
    ← Finset.mul_sum,empiricalObservation,scalarD,scalarM,integral_empiricalLaw,
    Fintype.card_fin,scalarBMoment,scalarQMoment_empirical_overlap,onsager,
    magnetization,Pi.sub_apply,Matrix.mulVec,dotProduct]
  ring

lemma scalar_density_cancellation {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (y : Fin n → ℝ) :
    rankOneDensity ((j/(n:ℝ))*(magnetization y⬝ᵥmagnetization y)+(t+σ^2))
      (j/(n:ℝ)) (magnetization y) (empiricalObservation j t σ y)*
      exp ((n:ℝ)*j*(1-overlap y)^2/2)=
    sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y := by
  let p := scalarEmpirical y t σ
  let q := scalarQMoment (empiricalLaw y)
  let s := scalarS j p
  let S := s+j*q
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hq : 0 ≤ q := (scalarQMoment_bounds _).1
  have hs : 0 < s := add_pos_of_pos_of_nonneg (add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)) (mul_nonneg hj hq)
  have hS : 0 < S := add_pos_of_pos_of_nonneg hs (mul_nonneg hj hq)
  have hm : magnetization y⬝ᵥmagnetization y=(n:ℝ)*q := by
    dsimp [q]
    rw [scalarQMoment_empirical_overlap]
    simp only [overlap,magnetization,dotProduct,← pow_two]
    field_simp
  have hx : (fun i=>y i-scalarD j p)⬝ᵥmagnetization y=(n:ℝ)*scalarA j p := by
    rw [dotProduct_comm]
    exact scalarA_empirical_sum j t σ y
  have hs' : (j/(n:ℝ))*(magnetization y⬝ᵥmagnetization y)+(t+σ^2)=s := by
    rw [hm]; dsimp [s,scalarS,p,scalarEmpirical,q]; field_simp; ring
  rw [hs']
  have hobs : empiricalObservation j t σ y=(fun i=>y i-scalarD j p)+(j*(1-q)) • magnetization y := rfl
  rw [hobs]
  have hc := rankOneDensity_cancellation hn hs hS.ne' (rfl : S=s+j*q)
    (fun i=>y i-scalarD j p) (magnetization y) hm hx (b := 1-q)
  have hb : 1-overlap y=1-q := by rw [← scalarQMoment_empirical_overlap]
  rw [hb,hc]
  have hd : productNormal (scalarD j p) s y=radialDensity (sqrt s) (fun i=>y i-scalarD j p) := by
    unfold productNormal
    rw [show s.toNNReal=NNReal.mk s hs.le from by ext; exact Real.coe_toNNReal _ hs.le]
    exact gaussian_density_shift _ hs.le y
  rw [scalarIntegrand,show scalarEmpirical y t σ=p from rfl,hd]
  simp only [Fintype.card_fin]
  have he : (n:ℝ)*j*(scalarA j p-s*(1-q))^2/(2*s*S)=(n:ℝ)*scalarPsi j p := by
    dsimp [S,s,q,p,scalarPsi,scalarEmpirical]
    ring
  rw [he]
  ring
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldIntegralReduction
attribute [-instance] _root_.OAI.SKGap.conditionalGoeLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal
attribute [local fun_prop] continuous_radialDensity

lemma continuous_fieldMollifier {n : ℕ} (j σ : ℝ) :
    Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × ((Fin n → ℝ) × (Fin n → ℝ))=>
      fieldMollifier j σ p.1 p.2.1 p.2.2) := by
  unfold fieldMollifier tapField onsager overlap magnetization
  exact ((continuous_radialDensity σ).comp (by fun_prop)).mul (by fun_prop)

lemma field_noise_convolution {n : ℕ} [NeZero n] {j t σ : ℝ} (ht : 0 ≤ t) (hσ : 0 < σ)
    (y : Fin n → ℝ) (f : ((Fin n×Fin n) → ℝ) → ℝ≥0∞) (g : MatrixCoordinates (Fin n) → ℝ) :
      (∫⁻ x, ENNReal.ofReal (fieldMollifier j σ
        (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) (fun i=>t+x i) y)*
        f (fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2)
        ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal))=
      ENNReal.ofReal (exp ((n:ℝ)*j*(1-overlap y)^2/2))*
        (ENNReal.ofReal (radialDensity (sqrt (t+σ^2))
          (empiricalObservation j t σ y-goeMatrix (j/(n:ℝ)) g*ᵥmagnetization y))*
            f (fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2)) := by
    simp only [fieldMollifier,tapField_planted_observation j t σ,
      ENNReal.ofReal_mul (radialDensity_pos hσ _).le]
    rw [lintegral_mul_const _ (by fun_prop),lintegral_mul_const _ (by fun_prop),gaussian_radial_convolution ht hσ]
    ring

theorem field_reduction_fixed {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (hE : MeasurableSet E) (y : Fin n → ℝ) :
    (∫⁻ g, ∫⁻ x, ENNReal.ofReal (fieldMollifier j σ
        (plantedInteraction j (goeMatrix (j/(n:ℝ)) g)) (fun i=>t+x i) y)*
        E.indicator (fun _=>1) ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=
    ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*
      conditionalFieldWeight j t σ E y := by
  let f : ((Fin n×Fin n) → ℝ) → ℝ≥0∞ := fun W=>E.indicator (fun _=>1) (W,y)
  have hf : Measurable f := measurable_const.indicator (hE.preimage (by fun_prop))
  change (∫⁻ g, ∫⁻ x, ENNReal.ofReal (fieldMollifier j σ _ _ y)*f _ ∂_ ∂_)=_
  simp_rw [field_noise_convolution ht hσ y f]
  have hgf : Measurable (fun g : MatrixCoordinates (Fin n) → ℝ => f (fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2)) := hf.comp (by unfold goeMatrix; fun_prop)
  have hgr : Measurable (fun g : MatrixCoordinates (Fin n) → ℝ => ENNReal.ofReal
      (radialDensity (sqrt (t+σ^2)) (empiricalObservation j t σ y-goeMatrix (j/(n:ℝ)) g*ᵥmagnetization y))) := by
    apply Measurable.ennreal_ofReal
    apply (continuous_radialDensity _).measurable.comp
    unfold Matrix.mulVec dotProduct goeMatrix
    fun_prop
  erw [lintegral_const_mul _ (hgr.mul hgf),goe_pointwise_conditional_integral
    (div_nonneg hj (Nat.cast_nonneg n)) (add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)) _ _ f hf]
  have hfi : (∫⁻ W,f W ∂conditionalGoeLaw (j/(n:ℝ)) (t+σ^2) (magnetization y)
      (empiricalObservation j t σ y))=conditionalFieldWeight j t σ E y := by
    change (∫⁻ W, {W | (W,y)∈E}.indicator (fun _=>(1 : ℝ≥0∞)) W ∂_)=_
    have hset : MeasurableSet {W : (Fin n×Fin n) → ℝ | (W,y)∈E} := hE.preimage (by fun_prop)
    rw [lintegral_indicator hset,lintegral_const]
    simp [conditionalFieldWeight]
  rw [hfi,← mul_assoc,← ENNReal.ofReal_mul (exp_pos _).le]
  congr 1
  congr 1
  rw [mul_comm,scalar_density_cancellation hj ht hσ y]
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ConditionalWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma scalar_density_prefactor_le_one {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (y : Fin n → ℝ) :
    sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y))) ≤ 1 := by
  have hq : 0 ≤ j*scalarQMoment (empiricalLaw y) := mul_nonneg hj (scalarQMoment_bounds _).1
  have hs : 0 < scalarS j (scalarEmpirical y t σ) := add_pos_of_pos_of_nonneg
    (add_pos_of_nonneg_of_pos ht (sq_pos_of_pos hσ)) hq
  exact sqrt_le_one.mpr ((div_le_one (add_pos_of_pos_of_nonneg hs hq)).mpr (le_add_of_nonneg_right hq))

lemma scalarIntegrand_nonneg {n : ℕ} [NeZero n] (j t σ : ℝ) (y : Fin n → ℝ) :
    0 ≤ scalarIntegrand j t σ y := mul_nonneg (exp_pos _).le
      (Finset.prod_nonneg (fun i _=>gaussianPDFReal_nonneg _ _ (y i)))

lemma scalar_weighted_density_bound {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (y : Fin n → ℝ) {w b : ℝ≥0∞}
    (hw : w ≤ b) :
    ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*w ≤
    ENNReal.ofReal (scalarIntegrand j t σ y)*b := by
  apply mul_le_mul' _ hw
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_left (scalarIntegrand_nonneg j t σ y) (scalar_density_prefactor_le_one hj ht hσ y)

end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Localization_ScalarClosedIsolation
attribute [-instance] _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
open Real Set
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open Set Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Real
open scoped NNReal ENNReal
namespace SKGap

theorem scalar_closed_isolation {j T smin : ℝ} (hj : 0 < j) (hj1 : j < 1)
    (hT : 0 ≤ T) (hsmin : 0 < smin) {C : Set ScalarPoint} (hC : IsClosed C)
    (hne : ∀ p ∈ C, p.2.1 ∈ Icc 0 T → p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) :
    ∃ a > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n, ∀ t ∈ Icc 0 T,
      ∀ σ ∈ Icc 0 (min δ 1), ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, @scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ ∈ C) →
      (∀ y ∈ E, smin ≤ scalarS j (@scalarEmpirical (Fin n) _ ⟨⟨0,hn⟩⟩ y t σ)) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨R,hR,hTail⟩ := scalar_uniform_tail hj.le hT hsmin 1
  let K := scalarBox j R T smin ∩ C
  have hK : IsCompact K := (isCompact_scalarBox j R T smin).inter_right hC
  have hmom : K ⊆ scalarMomentDomain R := fun p hp => ⟨hp.1.1.1,mem_univ _⟩
  obtain ⟨a,ha,δ,hδ,N,hN⟩ := scalar_compact_isolation hj hj1 hR.le hK hmom
    (fun p hp => hp.1.1.2.1.1) (fun p hp => hp.1.1.2.2.1)
    (fun p hp => hsmin.trans_le hp.1.2) (fun p hp hz => hne p hp.2 hp.1.1.2.1 hz)
  let b := min a 1
  have hb : 0 < b := lt_min ha zero_lt_one
  obtain ⟨M,hM⟩ := absorb_finite_exponential_factor 2 (half_pos hb)
  refine ⟨b/2,half_pos hb,δ,hδ,max N M,?_⟩
  intro n hn hn' t ht σ hσ E hE hforbid hs
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  have hσ' : σ ∈ Icc (0:ℝ) 1 := ⟨hσ.1,hσ.2.trans (min_le_right _ _)⟩
  let B : Set (Fin n → ℝ) := {y | ∑ i, (y i)^2 ≤ (n:ℝ)*R}
  have hB : MeasurableSet B := isClosed_le (by fun_prop) continuous_const |>.measurableSet
  have hc := hN n (le_trans (le_max_left _ _) hn) hn' (fun y => scalarEmpirical y t σ)
    (E ∩ B) (hE.inter hB) (fun y hy => ⟨⟨⟨⟨empirical_momentBall y hR.le
      (by simpa only [Fintype.card_fin] using (show ∑ i, (y i)^2 ≤ (n:ℝ)*R from hy.2)),ht,hσ'⟩,
      hs y hy.1⟩,hforbid y hy.1⟩,hσ.2.trans (min_le_left _ _)⟩)
    (fun _ _ => rfl) (fun _ hy => hy.2)
  have hc' : (∫⁻ y in E ∩ B, ENNReal.ofReal (scalarIntegrand j t σ y)) ≤
      ENNReal.ofReal (exp (-b*(n:ℝ))) := by
    have hab : exp (-a*(n:ℝ)) ≤ exp (-b*(n:ℝ)) := exp_le_exp.mpr (by
      have hh := mul_le_mul_of_nonneg_right (min_le_left a 1) (Nat.cast_nonneg (α := ℝ) n)
      dsimp [b]; linarith only [hh])
    simpa only [scalarIntegrand, Fintype.card_fin] using hc.trans (ENNReal.ofReal_le_ofReal hab)
  have htail := hTail n hn' t ht σ hσ' (E ∩ Bᶜ) (hE.inter hB.compl)
    (fun y hy => hs y hy.1) (fun y hy => le_of_lt (not_le.mp hy.2))
  have he : exp (-(1:ℝ)*(n:ℝ)) ≤ exp (-b*(n:ℝ)) := exp_le_exp.mpr (by
    have hh := mul_le_mul_of_nonneg_right (min_le_right a 1) (Nat.cast_nonneg (α := ℝ) n)
    dsimp [b]; linarith only [hh])
  have htotal := (lintegral_split_le volume (fun y => ENNReal.ofReal (scalarIntegrand j t σ y)) E B).trans
    (add_le_add hc' (htail.trans (ENNReal.ofReal_le_ofReal he)))
  have hadd : ENNReal.ofReal (exp (-b*(n:ℝ)))+ENNReal.ofReal (exp (-b*(n:ℝ))) =
      ENNReal.ofReal (2*exp ((n:ℝ)*(-b))) := by
    rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]
    congr 1
    ring_nf
  rw [hadd] at htotal
  refine htotal.trans (ENNReal.ofReal_le_ofReal ?_)
  convert hM n (le_trans (le_max_right _ _) hn) (-b) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma scalar_smalltime_forbidden {j q₀ : ℝ} (hj : 0 < j) (hj1 : j < 1) (hq : 0 < q₀) :
    ∃ T > 0, IsClosed {p : ScalarPoint | q₀ ≤ scalarQMoment p.1} ∧
      (∀ p ∈ {p : ScalarPoint | q₀ ≤ scalarQMoment p.1}, p.2.1 ∈ Icc 0 T →
        p.2.2 = 0 → p.1 ≠ scalarCurve j p.2.1) ∧
      (∀ p ∈ {p : ScalarPoint | q₀ ≤ scalarQMoment p.1}, 0 ≤ p.2.1 →
        j*q₀ ≤ scalarS j p) := by
  let T := q₀*(1-j)/4
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T,hT,isClosed_le continuous_const (continuous_scalarQMoment.comp continuous_fst),?_,?_⟩
  · intro p hp ht _ he
    have hqspec := scalarQ_spec hj hj1 ht.1
    have heq : scalarQMoment p.1 = scalarQ j p.2.1 := by
      rw [he]
      exact hqspec.1.symm
    have hsmall : p.2.1/(1-j) ≤ q₀/4 := by
      apply (div_le_iff₀ (by linarith : 0 < 1-j)).mpr
      dsimp [T] at ht
      linarith only [ht.2]
    change q₀ ≤ scalarQMoment p.1 at hp
    rw [heq] at hp
    have hh := hqspec.2.2.trans hsmall
    change q₀ ≤ scalarQ j p.2.1 at hp
    linarith
  · intro p hp ht
    exact (mul_le_mul_of_nonneg_left hp hj.le).trans (scalar_consistency ht)

end SKGap

namespace SKGap

theorem scalar_rate_iii {j q₀ : ℝ} (hj : 0 < j) (hj1 : j < 1) (hq₀ : 0 < q₀) :
    ∃ t₀ > 0, ∃ δ > 0, ∃ a > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ hn : 0 < n,
      ∀ t ∈ Icc 0 t₀, ∀ σ ∈ Icc 0 (min δ 1),
      ∀ E : Set (Fin n → ℝ), MeasurableSet E →
      (∀ y ∈ E, q₀ ≤ scalarQMoment (@empiricalLaw (Fin n) _ ⟨⟨0,hn⟩⟩ y)) →
      (∫⁻ y in E, ENNReal.ofReal (@scalarIntegrand (Fin n) _ ⟨⟨0,hn⟩⟩ j t σ y)) ≤
        ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨T,hT,hC,hne,hfloor⟩ := scalar_smalltime_forbidden hj hj1 hq₀
  obtain ⟨a,ha,δ,hδ,N,hN⟩ := scalar_closed_isolation hj hj1 hT.le (mul_pos hj hq₀) hC hne
  refine ⟨T,hT,δ,hδ,a,ha,N,?_⟩
  intro n hn hn' t ht σ hσ E hE hbad
  let : Nonempty (Fin n) := ⟨⟨0,hn'⟩⟩
  exact hN n hn hn' t ht σ hσ E hE hbad (fun y hy => hfloor (scalarEmpirical y t σ) (hbad y hy) ht.1)

end SKGap

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Stability_FieldTonelli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma fieldIntegral_indicator {n : ℕ} (j σ : ℝ) (J : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin n → ℝ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    fieldIntegral j σ J h E=∫⁻ y, ENNReal.ofReal (fieldMollifier j σ J h y)*E.indicator (fun _=>1) y := by
  rw [fieldIntegral,← lintegral_indicator hE]
  apply lintegral_congr
  intro y
  by_cases hy : y∈E <;> simp [hy]

theorem field_integral_gaussian_reduction {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ)
    (E : Set (((Fin n×Fin n) → ℝ) × (Fin n → ℝ))) (hE : MeasurableSet E) :
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E}
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n)))=
    ∫⁻ y, ENNReal.ofReal (sqrt (scalarS j (scalarEmpirical y t σ)/
      (scalarS j (scalarEmpirical y t σ)+j*scalarQMoment (empiricalLaw y)))*scalarIntegrand j t σ y)*
      conditionalFieldWeight j t σ E y := by
  let μ := gaussianCoordinates (MatrixCoordinates (Fin n))
  let ν := Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
  let H : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) → ℝ≥0∞ :=
    fun p=>ENNReal.ofReal (fieldMollifier j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1))
      (fun i=>t+p.1.2 i) p.2)* E.indicator (fun _=>1) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)
  have hsJ : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1)) :=
    ((goeMatrix_pi_lipschitz (j/(n:ℝ))).continuous.comp (continuous_fst.comp continuous_fst)).add continuous_const
  have htime : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (fun i=>t+p.1.2 i)) := by
    apply continuous_pi
    intro i
    exact continuous_const.add ((continuous_apply i).comp (continuous_snd.comp continuous_fst))
  have hmap : Continuous (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      (plantedInteraction j (goeMatrix (j/(n:ℝ)) p.1.1),((fun i=>t+p.1.2 i),p.2))) :=
    hsJ.prodMk (htime.prodMk continuous_snd)
  have hφ := ((continuous_fieldMollifier j σ).comp hmap).measurable.ennreal_ofReal
  have hI : Measurable (fun p : ((MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ) =>
      E.indicator (fun _=>(1 : ℝ≥0∞)) ((fun q=>goeMatrix (j/(n:ℝ)) p.1.1 q.1 q.2),p.2)) := by
    apply (measurable_const.indicator hE).comp
    unfold goeMatrix
    fun_prop
  have hH : Measurable H := hφ.mul hI
  have he (g : MatrixCoordinates (Fin n) → ℝ) (x : Fin n → ℝ) :
      fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E}=
      ∫⁻ y,H ((g,x),y) := by
    have hs : MeasurableSet {y : Fin n → ℝ | ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E} := hE.preimage (by fun_prop)
    erw [fieldIntegral_indicator _ _ _ _ _ hs]
    apply lintegral_congr
    intro y
    dsimp [H]
    by_cases hy : ((fun p=>goeMatrix (j/(n:ℝ)) g p.1 p.2),y)∈E <;> simp [hy]
  simp_rw [he]
  change (∫⁻ g,∫⁻ x,∫⁻ y,H ((g,x),y) ∂volume ∂ν ∂μ)=_
  rw [← lintegral_prod _ hH.lintegral_prod_right'.aemeasurable,
    lintegral_lintegral_swap hH.aemeasurable]
  apply lintegral_congr
  intro y
  have hh : Measurable (fun p : (MatrixCoordinates (Fin n) → ℝ) × (Fin n → ℝ) => H (p,y)) := hH.comp (by fun_prop)
  rw [lintegral_prod _ hh.aemeasurable]
  exact field_reduction_fixed hj ht hσ E hE y
end SKGap
end
end

end OAI
end

section
-- module Solutions.OAIQ072_SK.SKGap_Entropy_BadIntegralEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory GaussianDensity
open scoped BigOperators Matrix.Norms.Frobenius ENNReal

lemma conditionalFieldWeight_cylinder {n : ℕ} [NeZero n] (j t σ : ℝ)
    (E : Set (Fin n → ℝ)) (y : Fin n → ℝ) :
    conditionalFieldWeight j t σ (Set.univ ×ˢ E) y=E.indicator (fun _=>1) y := by
  by_cases hy : y∈E <;> simp [conditionalFieldWeight,hy]

lemma field_integral_scalar_bound {n : ℕ} [NeZero n] {j t σ : ℝ}
    (hj : 0 ≤ j) (ht : 0 ≤ t) (hσ : 0 < σ) (E : Set (Fin n → ℝ)) (hE : MeasurableSet E) :
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) E
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n))) ≤
    ∫⁻ y in E, ENNReal.ofReal (scalarIntegrand j t σ y) := by
  have hh := field_integral_gaussian_reduction hj ht hσ (Set.univ ×ˢ E) (MeasurableSet.univ.prod hE)
  simp only [mem_prod,mem_univ,true_and,ofPred_mem_eq,conditionalFieldWeight_cylinder] at hh
  rw [hh,← lintegral_indicator hE]
  apply lintegral_mono
  intro y
  by_cases hy : y∈E
  · simp only [indicator_of_mem hy,mul_one]
    simpa only [mul_one] using (scalar_weighted_density_bound hj ht hσ y (le_rfl (a := (1:ℝ≥0∞))))
  · simp [hy]

theorem smalltime_bad_integral_oai {j q₀ : ℝ} (hj : 0 < j) (hj1 : j < 1) (hq₀ : 0 < q₀) :
    ∃ t₀ σ₀ a : ℝ, 0 < t₀ ∧ 0 < σ₀ ∧ 0 < a ∧ ∃ N : ℕ,
    ∀ (n : ℕ) [NeZero n],N ≤ n → ∀ t ∈ Icc 0 t₀,∀ σ ∈ Ioc 0 σ₀,
    (∫⁻ g, ∫⁻ x, fieldIntegral j σ (plantedInteraction j (goeMatrix (j/(n:ℝ)) g))
        (fun i=>t+x i) {y | q₀ ≤ overlap y}
      ∂Measure.pi (fun _ : Fin n=>gaussianReal 0 t.toNNReal)
      ∂gaussianCoordinates (MatrixCoordinates (Fin n))) ≤ ENNReal.ofReal (exp (-a*(n:ℝ))) := by
  obtain ⟨t₀,ht₀,δ,hδ,a,ha,N,hN⟩ := scalar_rate_iii hj hj1 hq₀
  refine ⟨t₀,min δ 1,a,ht₀,lt_min hδ zero_lt_one,ha,N,?_⟩
  intro n _ hn t ht σ hσ
  have hE : MeasurableSet {y : Fin n → ℝ | q₀ ≤ overlap y} :=
    (isClosed_le continuous_const (by unfold overlap magnetization;fun_prop)).measurableSet
  apply (field_integral_scalar_bound hj.le ht.1 hσ.1 _ hE).trans
  exact hN n hn (NeZero.pos n) t ht σ ⟨hσ.1.le,hσ.2⟩ _ hE
    (fun y hy=>by rw [scalarQMoment_empirical_overlap];exact hy)

end SKGap
end
end

end OAI
end

theorem solution : type_of% @OAI.SKGap.smalltime_bad_integral_oai := @OAI.SKGap.smalltime_bad_integral_oai
