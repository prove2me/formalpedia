-- Prove2me | solution 1 for OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:43:19.603967+00:00
-- url     : https://prove2.me/submissions/5acb2721-b163-4f75-87ad-1c24f6ce185d

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Definitions.Def_OAIQ067A001
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_datumRoot_conditional_replacement_firstMoment_sat
import Theorems.Thm_OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_upperPoisson_cavity_separable_sat

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)

variable {n : ℕ}

theorem logMean_mono {m : ℝ} (hm : 0 < m) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    P.logMean m f ≤ P.logMean m g := by
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (P.expMoment_pos _ _)
  exact P.expect_mono (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (h x) hm.le))

/-- Root-measurable uniform bounds pass unchanged through each power mean. -/
theorem logMean_stability {m c : ℝ} (hm : 0 < m) {f g : Ω → ℝ}
    (h : ∀ x, |f x - g x| ≤ c) : |P.logMean m f - P.logMean m g| ≤ c := by
  have hfg : P.logMean m f ≤ P.logMean m g + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).2; linarith)
  have hgf : P.logMean m g ≤ P.logMean m f + c := by
    rw [← P.logMean_add (ne_of_gt hm)]
    exact P.logMean_mono hm (fun x => by have hx := (abs_le.mp (h x)).1; linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Finite independence identity, valid for arbitrary and distinct kernels. -/
theorem expect_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (Q : (i : ι) → FiniteLaw (α i)) (f : (i : ι) → α i → ℝ) :
    (pi Q).expect (fun x => ∏ i, f i (x i)) = ∏ i, (Q i).expect (f i) := by
  simp only [expect, pi, ← Finset.prod_mul_distrib, Fintype.prod_sum]

end FiniteLaw
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_KernelTower
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

namespace KernelTower

variable {Ω : Type} [Fintype Ω]

theorem backwardLog_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, m i ≠ 0) (c : ℝ) : backwardLog n T m (fun _ => c) = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [backwardLog]
    have heq : (fun x => backwardLog n (T.2 x) (fun j => m j.succ) (fun _ => c)) =
        (fun _ => c) := by
      funext x
      exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ)
    rw [heq, FiniteLaw.logMean_const _ (hm 0)]

/-- The uniform insertion bound, with full arbitrary depth-dependent priors. -/
theorem backwardLog_stability (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f g : FinitePath Ω n → ℝ} {c : ℝ}
    (hfg : ∀ x, |f x - g x| ≤ c) :
    |backwardLog n T m f - backwardLog n T m g| ≤ c := by
  induction n with
  | zero => exact hfg ()
  | succ n ih =>
    apply T.1.logMean_stability (hm 0)
    intro x
    exact ih (T.2 x) (fun j => m j.succ) (fun j => hm j.succ) (fun y => hfg (x,y))

/-- Pointwise bounds survive every backward step, uniformly in depth. -/
theorem backwardLog_bound (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ i, 0 < m i) {f : FinitePath Ω n → ℝ} {c : ℝ}
    (hf : ∀ x, |f x| ≤ c) : |backwardLog n T m f| ≤ c := by
  have h := backwardLog_stability n T m hm (g := fun _ => 0)
    (fun x => by simpa only [sub_zero] using hf x)
  rwa [backwardLog_const n T m (fun i => ne_of_gt (hm i)), sub_zero] at h

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkedPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

theorem poissonWeight_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonWeight r (n+1) * (n+1 : ℕ) = (r : ℝ) * poissonWeight r n := by
  unfold poissonWeight
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn1 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- Poisson add-one (the count part of pert:palm), including zero rate. -/
theorem poisson_add_one (r : ℝ≥0) (f : ℕ → ℝ)
    (hf : Integrable (fun n => f (n+1)) (poissonMeasure r)) :
    (∫ n : ℕ, (n : ℝ) * f n ∂poissonMeasure r) =
      (r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r := by
  have hs := (hasSum_integral_poissonMeasure hf).mul_left (r : ℝ)
  simp only [smul_eq_mul] at hs
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ) * f (n+1))
      ((r : ℝ) * ∫ n : ℕ, f (n+1) ∂poissonMeasure r) := by
    simp_rw [poissonWeight_succ_mul]
    simpa only [poissonWeight, mul_assoc] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ) * f n) ht
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add] at ht'
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul, ← mul_assoc, poissonWeight] using ht'.tsum_eq

/-- Integrability of the count is proved from the same add-one recurrence. -/
theorem poisson_integrable_count (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hs := (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  have ht : HasSum (fun n => poissonWeight r (n+1) * ((n+1 : ℕ) : ℝ)) r := by
    simp_rw [poissonWeight_succ_mul]
    unfold poissonWeight
    simpa only [mul_one] using hs
  have ht' := HasSum.zero_add (f := fun n => poissonWeight r n * (n : ℝ)) ht
  simp only [Nat.cast_zero, mul_zero, zero_add] at ht'
  simpa only [Real.norm_natCast, poissonWeight] using ht'.summable

@[simp] theorem poisson_mean (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = r := by
  simpa using poisson_add_one r (fun _ => 1) (integrable_const 1)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonVariance
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge

namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem logMean_uniform [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).logMean 1 f =
      Real.log (∑ a, Real.exp (f a))-Real.log (Fintype.card Ω) := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)
  have hsum : 0 < ∑ a, Real.exp (f a) := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [logMean,expMoment,expect,uniform,one_mul,div_one,← Finset.mul_sum]
  rw [Real.log_mul (inv_ne_zero hcard) (ne_of_gt hsum),Real.log_inv]
  ring
end FiniteLaw

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MixtureMeasures
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
namespace DilutedSpinGlass

variable {I : Type*} {X : I → Type*} [MeasurableSpace I]
  [∀ i, MeasurableSpace (X i)]

omit [MeasurableSpace I] in
theorem measurable_sigmaUncurry {Y : Type*} [MeasurableSpace Y] {f : (i : I) → X i → Y}
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x : Sigma X => f x.1 x.2) := by
  rw [measurable_iff_comap_le]
  apply le_iInf
  intro i
  rw [← MeasurableSpace.comap_le_iff_le_map]
  rw [MeasurableSpace.comap_comp]
  exact (hf i).comap_le

end DilutedSpinGlass

namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
variable {I : Type*} {X : I → Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [∀ i, MeasurableSpace (X i)]
    (μ : Measure I) (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]

/-- Sufficient integrability on the genuine disjoint-union root law. -/
theorem familyLaw_integrable_bound (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i)) {B : I → ℝ} (hB : Integrable B μ)
    (hb : ∀ i x, |f i x| ≤ B i) :
    Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) := by
  let F : Sigma X → ℝ := fun z => f z.1 z.2
  have hm : Measurable F := measurable_sigmaUncurry hf
  have hi (i : I) : Integrable (f i) (ν i) :=
    Integrable.of_bound (hf i).aestronglyMeasurable (B i) (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using hb i x))
  have hi' (i : I) : Integrable F (familyKernel ν i) := by
    change Integrable F ((ν i).map (Sigma.mk i))
    exact (integrable_map_measure hm.aestronglyMeasurable (measurable_sigmaMk i).aemeasurable).mpr (hi i)
  apply (Measure.integrable_comp_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hi', ?_⟩
  apply hB.mono' Measurable.of_discrete.aestronglyMeasurable
  apply ae_of_all
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  change (∫ z, ‖F z‖ ∂(ν i).map (Sigma.mk i)) ≤ B i
  rw [integral_map (measurable_sigmaMk i).aemeasurable hm.norm.aestronglyMeasurable]
  have hh := integral_mono (hi i).norm (integrable_const (B i))
    (fun x => by simpa only [Real.norm_eq_abs] using hb i x)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

omit [∀ i, IsProbabilityMeasure (ν i)] in
 
theorem integral_familyLaw (f : (i : I) → X i → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hi : Integrable (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν)) :
    (∫ z : Sigma X, f z.1 z.2 ∂familyLaw μ ν) = ∫ i, ∫ x, f i x ∂ν i ∂μ := by
  unfold familyLaw at hi ⊢
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi]
  change (∫ i, ∫ z : Sigma X, f z.1 z.2 ∂(ν i).map (Sigma.mk i) ∂μ) = _
  apply integral_congr_ae
  apply ae_of_all
  intro i
  exact integral_map (measurable_sigmaMk i).aemeasurable
    (measurable_sigmaUncurry hf).aestronglyMeasurable

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_AnchorExtension
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
@[simp] theorem tilt_const (n : ℕ) (T : KernelTower Ω n) (m : Fin n → ℝ)
    (hm : ∀ j, m j ≠ 0) (c : ℝ) : tilt n T m (fun _ => c) = T := by
  induction n with
  | zero =>
    change () = T
    cases T
    rfl
  | succ n ih =>
    simp only [tilt, backwardLog_const n _ _ (fun j => hm j.succ),
      FiniteLaw.tilt_const, ih _ _ (fun j => hm j.succ)]
    cases T
    rfl
end DilutedSpinGlass.KernelTower

open Filter Set
open scoped Topology BigOperators

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CompoundPoisson
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma charFunDual_iid_sum (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (L : StrongDual ℝ E) :
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L =
      charFunDual μ L ^ n := by
  rw [charFunDual_apply,integral_map (by fun_prop) (by fun_prop)]
  simp_rw [map_sum,Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun _ : Fin n => fun x : E => Complex.exp ((L x : ℂ)*Complex.I))]
  simp only [charFunDual_apply,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma charFunDual_compoundPoisson (r : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : StrongDual ℝ E) :
    charFunDual (compoundPoisson r μ) L = Complex.exp ((r:ℂ)*(charFunDual μ L-1)) := by
  have hi : Integrable (fun x : E => Complex.exp ((L x:ℂ)*Complex.I)) (compoundPoisson r μ) := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  change (∫ x, Complex.exp ((L x:ℂ)*Complex.I) ∂compoundPoisson r μ) = _
  rw [compoundPoisson,integral_sum_measure hi]
  have hw (n : ℕ) : 0 ≤ Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial := by positivity
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal (hw _)]
  change (∑' n : ℕ, (Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial) •
    charFunDual (Measure.map (fun x : Fin n → E => ∑ i,x i) (Measure.pi (fun _ : Fin n => μ))) L) = _
  simp_rw [charFunDual_iid_sum,Complex.real_smul]
  have hh := (NormedSpace.expSeries_div_hasSum_exp ((r:ℂ)*charFunDual μ L)).mul_left
    (Complex.exp (-(r:ℂ)))
  have he : (fun n : ℕ => ((Real.exp (-(r:ℝ))*(r:ℝ)^n/n.factorial:ℝ):ℂ)*charFunDual μ L^n) =
      (fun n : ℕ => Complex.exp (-(r:ℂ))*(((r:ℂ)*charFunDual μ L)^n/n.factorial)) := by
    funext n
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,
      Complex.ofReal_exp,Complex.ofReal_neg,mul_pow]
    ring
  rw [he,hh.tsum_eq]
  rw [← Complex.exp_eq_exp_ℂ,← Complex.exp_add]
  congr 1
  ring
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ConcentrationRate
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.MeasureTheory

namespace MeasureTheory
open scoped _root_.MeasureTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : _root_.MeasureTheory.Measure X) (ν : _root_.MeasureTheory.Measure Y) (ρ : _root_.MeasureTheory.Measure Z) [_root_.MeasureTheory.SFinite μ] [_root_.MeasureTheory.SFinite ν] [_root_.MeasureTheory.SFinite ρ]

lemma integrable_triple_rotate (F : (X×Y)×Z → ℝ) (hF : _root_.MeasureTheory.Integrable F ((μ.prod ν).prod ρ)) :
    _root_.MeasureTheory.Integrable (fun yz : Y×Z => ∫ x,F ((x,yz.1),yz.2) ∂μ) (ν.prod ρ) := by
  let G := F ∘ (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm
  have hG : _root_.MeasureTheory.Integrable G (μ.prod (ν.prod ρ)) :=
    (_root_.MeasureTheory.measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc |>.integrable_comp_of_integrable hF
  exact hG.integral_prod_right

lemma integrable_triple_middle_swap (F : X×(Y×Z) → ℝ) (hF : _root_.MeasureTheory.Integrable F (μ.prod (ν.prod ρ))) :
    _root_.MeasureTheory.Integrable (fun xz : X×Z => ∫ y,F (xz.1,(y,xz.2)) ∂ν) (μ.prod ρ) := by
  have hid : _root_.MeasureTheory.MeasurePreserving (id : X → X) μ μ := ⟨measurable_id,_root_.MeasureTheory.Measure.map_id⟩
  have hG : _root_.MeasureTheory.Integrable (fun a : X×(Z×Y) => F (a.1,(a.2.2,a.2.1))) (μ.prod (ρ.prod ν)) :=
    (hid.prod (_root_.MeasureTheory.Measure.measurePreserving_swap (μ := ρ) (ν := ν))).integrable_comp_of_integrable hF
  have hH := (_root_.MeasureTheory.measurePreserving_prodAssoc μ ρ ν).integrable_comp_of_integrable hG
  exact hH.integral_prod_left

lemma integral_triple_rotate (F : (X×Y)×Z → ℝ) (hF : _root_.MeasureTheory.Integrable F ((μ.prod ν).prod ρ)) :
    (∫ a,∫ z,F (a,z) ∂ρ ∂μ.prod ν) =
      ∫ y,∫ z,∫ x,F ((x,y),z) ∂μ ∂ρ ∂ν := by
  let G := F ∘ (MeasurableEquiv.prodAssoc (α := X) (β := Y) (γ := Z)).symm
  have hG : _root_.MeasureTheory.Integrable G (μ.prod (ν.prod ρ)) :=
    (_root_.MeasureTheory.measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc |>.integrable_comp_of_integrable hF
  rw [← _root_.MeasureTheory.integral_prod _ hF]
  have he := (_root_.MeasureTheory.measurePreserving_prodAssoc μ ν ρ).integral_comp' G
  change (∫ a,G (MeasurableEquiv.prodAssoc a) ∂(μ.prod ν).prod ρ)=_
  rw [he,_root_.MeasureTheory.integral_prod _ hG]
  rw [_root_.MeasureTheory.integral_integral_swap (f := fun x yz => G (x,yz)) hG]
  exact _root_.MeasureTheory.integral_prod _ hG.integral_prod_right

lemma integral_triple_middle_swap (F : X×(Y×Z) → ℝ) (hF : _root_.MeasureTheory.Integrable F (μ.prod (ν.prod ρ))) :
    (∫ x,∫ a,F (x,a) ∂ν.prod ρ ∂μ) =
      ∫ x,∫ z,∫ y,F (x,(y,z)) ∂ν ∂ρ ∂μ := by
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards [hF.prod_right_ae] with x hx
  rw [_root_.MeasureTheory.integral_prod _ hx,_root_.MeasureTheory.integral_integral_swap hx]

end MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteProjection
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open scoped BigOperators

namespace FiniteLaw
variable {Ω Λ Γ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ]

theorem Projects.logMean {P : FiniteLaw Ω} {Q : FiniteLaw Λ} {π : Ω → Λ}
    (h : Projects P Q π) (m : ℝ) (f : Λ → ℝ) :
    P.logMean m (fun x => f (π x)) = Q.logMean m f := by
  unfold FiniteLaw.logMean FiniteLaw.expMoment
  rw [h (fun y => Real.exp (m*f y))]

lemma uniform_expect [Nonempty Ω] (f : Ω → ℝ) :
    (uniform : FiniteLaw Ω).expect f = (∑ x, f x)/(Fintype.card Ω) := by
  simp only [expect,uniform,← Finset.mul_sum]
  ring

end FiniteLaw

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

theorem backwardLog_of_projects {π : Ω → Λ} (n : ℕ) {T : KernelTower Ω n} {U : KernelTower Λ n}
    (h : Projects π n T U) (m : Fin n → ℝ) (f : FinitePath Λ n → ℝ) :
    backwardLog n T m (fun y => f (pathMap π n y)) = backwardLog n U m f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change T.1.logMean (m 0) (fun a => backwardLog n (T.2 a) (fun j => m j.succ)
      (fun y => f (π a,pathMap π n y))) = _
    have heq : (fun a => backwardLog n (T.2 a) (fun j => m j.succ)
        (fun y => f (π a,pathMap π n y))) =
      (fun a => backwardLog n (U.2 (π a)) (fun j => m j.succ) (fun y => f (π a,y))) := by
      funext a
      exact ih (h.2 a) (fun j => m j.succ) (fun y => f (π a,y))
    rw [heq]
    exact h.1.logMean (m 0) (fun b => backwardLog n (U.2 b) (fun j => m j.succ) (fun y => f (b,y)))

end KernelTower
end DilutedSpinGlass
end

end

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

lemma expect_comm {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]
    (P : FiniteLaw Ω) (Q : FiniteLaw Λ) (f : Ω → Λ → ℝ) :
    P.expect (fun x => Q.expect (f x)) = Q.expect (fun y => P.expect (fun x => f x y)) := by
  simp only [expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FinitePiInjective
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι κ : Type*} {α : κ → Type*}

attribute [local instance] OAI.DilutedSpinGlass.FiniteLaw.instDecidable
lemma injectionFactor_apply (e : ι → κ) (he : Function.Injective e)
    (g : (i : ι) → α (e i) → ℝ) (i : ι) (x : α (e i)) :
    injectionFactor e g (e i) x = g i x := by
  classical
  unfold injectionFactor
  have h : ∃ j, e j = e i := ⟨i,rfl⟩
  rw [dite_eq_left h]
  have ht : ∀ (j : ι) (hj : e j = e i), g j (hj.symm ▸ x) = g i x := by
    intro j hj
    have hji := he hj
    subst j
    rfl
  exact ht _ (Classical.choose_spec h)

lemma injectionFactor_outside (e : ι → κ) (g : (i : ι) → α (e i) → ℝ)
    (j : κ) (h : j ∉ Set.range e) (x : α j) : injectionFactor e g j x = 1 := by
  classical
  exact dite_eq_right h

variable [Fintype ι] [Fintype κ] [DecidableEq κ] [∀ i, Fintype (α i)]

/-- A finite family of distinct child coordinates has the corresponding
product law, regardless of the unused coordinates in the full old tree. -/
lemma expect_pi_injective_product (P : (j : κ) → FiniteLaw (α j))
    (e : ι → κ) (he : Function.Injective e) (g : (i : ι) → α (e i) → ℝ) :
    (pi P).expect (fun x => ∏ i, g i (x (e i))) = ∏ i, (P (e i)).expect (g i) := by
  have hx (x : (j : κ) → α j) : (∏ i, g i (x (e i))) =
      ∏ j, injectionFactor e g j (x j) :=
    Fintype.prod_of_injective e he _ _ (fun j hj => injectionFactor_outside e g j hj (x j))
      (fun i => (injectionFactor_apply e he g i (x (e i))).symm)
  rw [(pi P).expect_congr hx,expect_pi_product]
  symm
  apply Fintype.prod_of_injective e he
  · intro j hj
    exact ((P j).expect_congr (fun x => injectionFactor_outside e g j hj x)).trans
      ((P j).expect_const 1)
  · intro i
    exact (P (e i)).expect_congr (fun x => (injectionFactor_apply e he g i x).symm)

lemma product_point_indicator {β : ι → Type*} (x y : (i : ι) → β i) :
    (∏ i, (if x i = y i then (1:ℝ) else 0)) = (if x = y then 1 else 0) := by
  classical
  by_cases h : x = y
  · subst y; simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by
      by_contra hh
      exact h (funext (fun i => not_not.mp (not_exists.mp hh i)))
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma finite_indicator_expansion {β : ι → Type*} [∀ i, Fintype (β i)]
    (H : ((i : ι) → β i) → ℝ) (x : (i : ι) → β i) :
    H x = ∑ y, H y * ∏ i, (if x i = y i then (1:ℝ) else 0) := by
  classical
  simp_rw [product_point_indicator]
  simp

variable [DecidableEq ι]

lemma expect_pi_injective (P : (j : κ) → FiniteLaw (α j))
    (e : ι → κ) (he : Function.Injective e) (H : ((i : ι) → α (e i)) → ℝ) :
    (pi P).expect (fun x => H (fun i => x (e i))) = (pi (fun i => P (e i))).expect H := by
  classical
  have hl : (pi P).expect (fun x => H (fun i => x (e i))) =
      ∑ y, H y * ∏ i, (P (e i)).expect (fun x => if x = y i then (1:ℝ) else 0) := by
    rw [(pi P).expect_congr (fun x => finite_indicator_expansion H (fun i => x (e i)))]
    simp only [expect_fintype_sum,expect_mul_left]
    apply Finset.sum_congr (by ext; simp)
    intro y _
    exact congrArg (H y * ·) (expect_pi_injective_product P e he
      (fun i x => if x = y i then (1:ℝ) else 0))
  have hr : (pi (fun i => P (e i))).expect H =
      ∑ y, H y * ∏ i, (P (e i)).expect (fun x => if x = y i then (1:ℝ) else 0) := by
    rw [(pi (fun i => P (e i))).expect_congr (finite_indicator_expansion H)]
    simp only [expect_fintype_sum,expect_mul_left]
    apply Finset.sum_congr (by ext; simp)
    intro y _
    exact congrArg (H y * ·) (expect_pi_product (fun i => P (e i))
      (fun i x => if x = y i then (1:ℝ) else 0))
  exact hl.trans hr.symm

end DilutedSpinGlass.FiniteLaw
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_GeneralRootArrayLaw
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.UniversalDictionary.reservoirLaw_prob _root_.OAI.DilutedSpinGlass.compoundRootLaw_prob _root_.OAI.DilutedSpinGlass.fullRootLaw_prob _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory

variable {X : Type} [MeasurableSpace X]

lemma rootArrayEquiv_apply (n : ℕ) (x : RootPath X n) : rootArrayEquiv (X := X) n x = rootArray n x := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    change Fin.insertNth 0 x.1 (rootArrayEquiv (X := X) n x.2) =
      Fin.cons (α := fun _ : Fin (n+1) => X) x.1 (rootArray n x.2)
    rw [Fin.insertNth_zero', ih]


/-- Exact law identification for arbitrary measurable disorder alphabets,
including the continuous physical interaction tables and external fields. -/
theorem measurePreserving_rootArray (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (rootArrayEquiv (X := X) n) (rootLaw n (fun _ => μ))
      (Measure.pi (fun _ : Fin n => μ)) := by
  induction n with
  | zero =>
    refine ⟨(rootArrayEquiv 0).measurable, ?_⟩
    rw [rootLaw,Measure.map_dirac' (rootArrayEquiv 0).measurable,Measure.pi_of_empty]
    congr 1
  | succ n ih =>
    exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm.comp
      ((MeasurePreserving.id μ).prod ih)

theorem integral_rootArray_eq_pi (μ : Measure X) [IsProbabilityMeasure μ]
    (n : ℕ) (f : (Fin n → X) → ℝ) :
    (∫ x, f (rootArray n x) ∂rootLaw n (fun _ => μ)) =
      ∫ x, f x ∂Measure.pi (fun _ : Fin n => μ) := by
  simpa only [rootArrayEquiv_apply] using (measurePreserving_rootArray μ n).integral_comp' f

end DilutedSpinGlass
end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_SpinBaseComparison
attribute [-instance] _root_.OAI.DilutedSpinGlass.ConcreteReservoir.siteNeZero _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace DilutedSpinGlass.FiniteLaw

lemma expect_uniform {B : Type} [Fintype B] [Nonempty B] (f : B → ℝ) :
    (uniform : FiniteLaw B).expect f = (∑ x, f x)/(Fintype.card B) := by
  simp only [expect,uniform,← Finset.mul_sum,div_eq_mul_inv]
  ring

end DilutedSpinGlass.FiniteLaw

end

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RealEncoding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Set TopologicalSpace
open scoped BigOperators NNReal
attribute [local instance] OAI.DilutedSpinGlass.realEncodingMeasurableSpace
local instance realEncodingBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

namespace KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

attribute [local instance] OAI.DilutedSpinGlass.realEncodingMeasurableSpace
lemma backwardLog_realEncode {ι : Type} [Fintype ι] [DecidableEq ι]
    {α : ι → Type} [∀ i,Fintype (α i)] (r : ℕ)
    (T : (i : ι) → KernelTower (α i) r) (V : (i : ι) → FinitePath (α i) r → ℝ)
    (F : (ι → ℝ) → ℝ) (m : Fin r → ℝ) :
    backwardLog r (pi r T) m (fun y => F (fun i => V i (FinitePath.proj r y i))) =
      DilutedSpinGlass.logMean r F m (fun i => realEncode r (T i) (V i)) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (i : ι) → FiniteLaw (α i) × (α i → KernelTower (α i) r) at T
    change (i : ι) → (α i × FinitePath (α i) r) → ℝ at V
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun a => backwardLog r (pi r (fun i => (T i).2 (a i))) (fun j => m j.succ)
        (fun y => F (fun i => V i (a i,FinitePath.proj r y i)))) =
      Real.log (∫ x, Real.exp (m 0 * DilutedSpinGlass.logMean r F (fun j => m j.succ) x)
        ∂Measure.pi (fun i => ((T i).1.asProbability
          (fun a => realEncode r ((T i).2 a) (fun y => V i (a,y)))).toMeasure)) / m 0
    have hc (a : (i : ι) → α i) := ih (fun i => (T i).2 (a i))
      (fun i y => V i (a i,y)) (fun j => m j.succ)
    simp_rw [hc]
    change Real.log ((FiniteLaw.pi (fun i => (T i).1)).expect (fun a =>
      Real.exp (m 0 * DilutedSpinGlass.logMean r F (fun j => m j.succ)
        (fun i => realEncode r ((T i).2 (a i)) (fun y => V i (a i,y)))))) / m 0 =
      Real.log (∫ x, Real.exp (m 0 * DilutedSpinGlass.logMean r F (fun j => m j.succ) x)
        ∂Measure.pi (fun i => ((T i).1.asProbability
          (fun a => realEncode r ((T i).2 a) (fun y => V i (a,y)))).toMeasure)) / m 0
    rw [FiniteLaw.integral_pi_asProbability]

end KernelTower

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_InsertionStability
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma map_familyLaw_sum {I : Type*} [MeasurableSpace I] [DiscreteMeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    {Y : Type*} [MeasurableSpace Y] (μ : Measure I) (ν : ∀ i, Measure (X i))
    (f : (i : I) → X i → Y) (hf : ∀ i, Measurable (f i)) :
    Measure.map (fun z : Sigma X => f z.1 z.2) (familyLaw μ ν) =
      Measure.sum (fun i => μ {i} • Measure.map (f i) (ν i)) := by
  rw [familyLaw,Measure.comp_eq_sum_of_countable]
  rw [Measure.map_sum (measurable_sigmaUncurry hf).aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul]
  change μ {i} • Measure.map (fun z : Sigma X => f z.1 z.2)
    (Measure.map (Sigma.mk i) (ν i)) = _
  rw [Measure.map_map (measurable_sigmaUncurry hf) (measurable_sigmaMk i)]
  rfl

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FinitePoissonSplit
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma integral_finiteUniform {A E : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : A → E) :
    (∫ x, f x ∂finiteUniform A) = ((Fintype.card A:ℝ)⁻¹) • ∑ x,f x := by
  rw [finiteUniform,PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    Finset.smul_sum]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityRateLimits
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory

lemma appendSpin_castSucc {q : ℕ} (s : Fin q → Spin) (ε : Spin) (i : Fin q) :
    appendSpin (p := q+1) s ε i.castSucc = s i := by
  simp only [appendSpin,Nat.add_sub_cancel,Fin.val_castSucc,dite_eq_left i.isLt]
  rfl

lemma appendSpin_last {q : ℕ} (s : Fin q → Spin) (ε : Spin) :
    appendSpin (p := q+1) s ε (Fin.last q) = ε := by
  simp [appendSpin]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProductLaw
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma finiteUniform_pi {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    Measure.pi (fun _ : ι => finiteUniform J) = finiteUniform (ι → J) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton,finiteUniform,PMF.uniformOfFintype_apply,ENNReal.inv_pow]

lemma integral_root_prod {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (n : ℕ) (F : (Fin n → X) × (Fin n → Y) → ℝ)
    (hF : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => ν)))) :
    (∫ z : RootPath (X×Y) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod ν)) =
      ∫ x : Fin n → X,∫ y : Fin n → Y,F (x,y)
        ∂Measure.pi (fun _ : Fin n => ν) ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_rootArray_eq_pi (μ.prod ν) n (fun z : Fin n → X×Y => F ((fun i => (z i).1),(fun i => (z i).2)))]
  have he := (measurePreserving_arrowProdEquivProdArrow X Y (Fin n)
    (fun _ => μ) (fun _ => ν)).integral_comp' F
  exact he.trans (integral_prod F hF)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MarkSiteCoupling
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L : ℕ}

lemma measurable_indexedPotential (theta : X → InteractionSample p)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) :
    Measurable (indexedPotential (N := N) theta) := by
  apply Measurable.of_eval
  intro σ
  apply measurable_from_prod_countable_left
  intro j
  simpa only [indexedPotential] using hθ (fun q => σ (j q))

end DilutedSpinGlass.PhysicalRoot

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonCountThinning
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

lemma compoundPoisson_dirac_one (r : ℝ≥0) :
    compoundPoisson r (Measure.dirac (1:ℝ)) = Measure.map (fun n : ℕ => (n:ℝ)) (poissonMeasure r) := by
  rw [compoundPoisson,poissonMeasure,Measure.map_sum (measurable_of_countable _).aemeasurable]
  congr 1
  funext n
  rw [Measure.map_smul,
    Measure.map_dirac' (measurable_of_countable _)]
  congr 1
  have ha : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => Measure.dirac (1:ℝ)),∀ i,x i=1 :=
    Filter.eventually_all.mpr (fun i => (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin n => Measure.dirac (1:ℝ)) (i := i)).eventually (show ∀ᵐ x ∂Measure.dirac (1:ℝ),x=1 from by simp))
  rw [Measure.map_congr (ha.mono (fun x hx => show (∑ i,x i)=(n:ℝ) by simp [hx]))]
  simp

/-- Poisson thinning for independent uniform categorical choices. -/
lemma compoundPoisson_uniform_indicator (r : ℝ≥0) (p : ℕ) [NeZero p] :
    compoundPoisson r (Measure.map (fun a : Fin p => if a=0 then (1:ℝ) else 0)
      (finiteUniform (Fin p))) = compoundPoisson (r/p) (Measure.dirac (1:ℝ)) := by
  classical
  let : IsProbabilityMeasure (Measure.map (fun a : Fin p => if a=0 then (1:ℝ) else 0)
      (finiteUniform (Fin p))) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).mpr inferInstance
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_compoundPoisson,charFunDual_compoundPoisson]
  congr 1
  rw [charFunDual_apply,integral_map (measurable_of_countable _).aemeasurable (by fun_prop),
    integral_finiteUniform,charFunDual_apply,integral_dirac]
  have hp : (p:ℂ)≠0 := by exact_mod_cast (NeZero.ne p)
  have hs : (∑ a : Fin p,Complex.exp ((L (if a=0 then (1:ℝ) else 0):ℂ)*Complex.I)) =
      Complex.exp ((L 1:ℂ)*Complex.I)+(p-1:ℕ) := by
    have he (a : Fin p) : Complex.exp ((L (if a=0 then (1:ℝ) else 0):ℂ)*Complex.I)=
        (if a=0 then Complex.exp ((L 1:ℂ)*Complex.I)-1 else 0)+1 := by
      split_ifs <;> simp
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    have hpn : ((p-1:ℕ):ℂ)=(p:ℂ)-1 := by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]
    rw [hpn]; ring
  rw [hs]
  simp only [Fintype.card_fin,NNReal.coe_div,NNReal.coe_natCast,Complex.ofReal_div,Complex.ofReal_natCast,Complex.real_smul,Complex.ofReal_inv]
  rw [show ((p-1:ℕ):ℂ)=(p:ℂ)-1 by rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]]
  field_simp
  ring

lemma map_poisson_successCount (r : ℝ≥0) (p : ℕ) [NeZero p] :
    Measure.map (fun z : (k : ℕ) × (Fin k → Fin p) => successCount z.2)
      (familyLaw (poissonMeasure r) (fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin p)))) =
      poissonMeasure (r/p) := by
  classical
  have he : MeasurableEmbedding (fun n : ℕ => (n:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).measurableEmbedding Nat.cast_injective
  apply he.map_injective
  rw [Measure.map_map (measurable_of_countable _) (measurable_sigmaUncurry (fun k => measurable_of_countable (fun a : Fin k → Fin p => successCount a))),
    ← compoundPoisson_dirac_one,← compoundPoisson_uniform_indicator r p]
  simp only [Function.comp_def]
  rw [map_familyLaw_sum _ _ (fun k (a : Fin k → Fin p) => (successCount a:ℝ))
    (fun k => measurable_of_countable _)]
  unfold compoundPoisson
  congr 1
  funext k
  rw [poissonMeasure_singleton,← Measure.pi_map_pi (fun _ : Fin k => (measurable_of_countable
    (fun a : Fin p => if a=0 then (1:ℝ) else 0)).aemeasurable),
    Measure.map_map (by fun_prop) (measurable_of_countable _)]
  congr 2
  funext a
  simp [successCount]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TowerPadding
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma backwardLog_pad (a : Ω) (n : ℕ) (T : KernelTower Ω n)
    (m : Fin (n+1) → ℝ) (hm : m (Fin.last n)≠0) (f : FinitePath Ω n → ℝ) :
    backwardLog (n+1) (pad a n T) m (fun y => f (pathPrefix n y))=
      backwardLog n T (fun j => m j.castSucc) f := by
  induction n with
  | zero =>
      change (FiniteLaw.point a).logMean (m 0) (fun _ => f ())=f ()
      exact FiniteLaw.logMean_const _ hm _
  | succ n ih =>
      simp only [pad,backwardLog,pathPrefix]
      congr 1
      funext x
      exact ih (T.2 x) (fun j => m j.succ) hm (fun y => f (x,y))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CommonTreeSample
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
namespace KernelTower
variable {Ω Λ Ω' Λ' : Type} [Fintype Ω] [Fintype Λ] [Fintype Ω'] [Fintype Λ']

lemma Projects.refl (n : ℕ) (T : KernelTower Ω n) : Projects id n T T := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨fun _ => rfl,fun a => ih (T.2 a)⟩

lemma Projects.comp {π : Ω → Λ} {ρ : Λ → Ω'} (n : ℕ)
    {T : KernelTower Ω n} {U : KernelTower Λ n} {V : KernelTower Ω' n}
    (h : Projects π n T U) (g : Projects ρ n U V) : Projects (ρ ∘ π) n T V := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (h.2 a) (g.2 (π a))⟩
    intro f
    exact (h.1 (f ∘ ρ)).trans (g.1 f)

lemma Projects.prod {π : Ω → Ω'} {ρ : Λ → Λ'} (n : ℕ)
    {T : KernelTower Ω n} {T' : KernelTower Ω' n}
    {U : KernelTower Λ n} {U' : KernelTower Λ' n}
    (h : Projects π n T T') (g : Projects ρ n U U') :
    Projects (fun z : Ω×Λ => (π z.1,ρ z.2)) n (prod n T U) (prod n T' U') := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (h.2 a.1) (g.2 a.2)⟩
    intro f
    change (T.1.bind (fun _ => U.1)).expect (fun z => f (π z.1,ρ z.2)) =
      (T'.1.bind (fun _ => U'.1)).expect f
    rw [FiniteLaw.expect_bind,FiniteLaw.expect_bind]
    have he : (fun a => U.1.expect (fun b => f (π a,ρ b)))=
        (fun a => U'.1.expect (fun b => f (π a,b))) := by
      funext a
      exact g.1 (fun b => f (π a,b))
    rw [he]
    exact h.1 (fun a => U'.1.expect (fun b => f (a,b)))

omit [Fintype Ω] [Fintype Λ] [Fintype Ω'] in
lemma pathMap_comp (π : Ω → Λ) (ρ : Λ → Ω') (n : ℕ) (y : FinitePath Ω n) :
    pathMap (ρ ∘ π) n y=pathMap ρ n (pathMap π n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_MixedEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory Filter
open scoped BigOperators Topology

lemma mixedEnergy_bound {p : ℕ} (z : InteractionSample p)
    (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    |mixedEnergy z sel s x|≤‖z.1‖ := by
  have h := (mixedSpinLaw sel s x).logMean_stability (m := 1) zero_lt_one
    (f := z.1) (g := fun _ => 0) (c := ‖z.1‖)
    (fun σ => by simpa only [sub_zero,Real.norm_eq_abs] using norm_le_pi_norm z.1 σ)
  simpa only [mixedEnergy,FiniteLaw.logMean_const _ one_ne_zero,sub_zero] using h

lemma measurable_mixedEnergy {p : ℕ} (sel : Fin p → Bool) (s : Fin p → Spin) (x : Fin p → ℝ) :
    Measurable (fun z : InteractionSample p => mixedEnergy z sel s x) :=
  FiniteLaw.measurable_logMean _ _ (fun σ => by fun_prop)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperInsertion
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators

lemma mixedEnergy_last {q : ℕ} (z : InteractionSample (q+1))
    (s : Fin (q+1) → Spin) (x : Fin (q+1) → ℝ) :
    mixedEnergy z (fun a => decide (a=Fin.last q)) s x=
      message z.1 (fun i => x i.castSucc) (s (Fin.last q)) := by
  classical
  unfold mixedEnergy mixedSpinLaw FiniteLaw.logMean FiniteLaw.expMoment
  simp only [one_mul,div_one]
  apply congrArg Real.log
  unfold FiniteLaw.expect FiniteLaw.pi
  rw [← (Fin.snocEquiv (fun _ : Fin (q+1) => Spin)).sum_comp]
  simp only [Fintype.sum_prod_type,Fin.snocEquiv_apply,Fin.prod_univ_castSucc,
    Fin.snoc_castSucc,Fin.snoc_last,Fin.castSucc_ne_last,decide_false,Bool.false_eq_true,
    ↓reduceIte,decide_true,FiniteLaw.point]
  simp only [Finset.sum_ite_irrel,mul_ite,ite_mul,zero_mul,mul_zero,mul_one,
    Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  have he : (Fin.snocEquiv (fun _ : Fin (q+1) => Spin)) (s (Fin.last q),a)=
      appendSpin (p := q+1) a (s (Fin.last q)) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snocEquiv_apply,Fin.snoc_last] using (appendSpin_last a (s (Fin.last q))).symm
    · simpa only [Fin.snocEquiv_apply,Fin.snoc_castSucc] using (appendSpin_castSucc a (s (Fin.last q)) j).symm
  simp only [he,qLaw,mul_comm]
  rfl

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_InsertionPoissonAlgebra
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

lemma poisson_average_integrable (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : Integrable f (poissonMeasure ρ) := by
  apply ((integrable_const B).add ((poisson_integrable_count ρ).const_mul D)).mono'
    (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_apply] using h k)

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TowerArraySplit
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma splitFirst_projects (n l : ℕ) (T : KernelTower Ω n) (U : Fin (l+1) → KernelTower Λ n) :
    Projects (splitFirst l) n (prod n T (pi n U))
      (prod n (prod n T (pi n (fun i => U i.succ))) (U 0)) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (T.2 a.1) (fun i => (U i).2 (a.2 i))⟩
    intro f
    change (T.1.bind (fun _ => FiniteLaw.pi (fun i => (U i).1))).expect (fun z => f (splitFirst l z)) =
      ((T.1.bind (fun _ => FiniteLaw.pi (fun i : Fin l => (U i.succ).1))).bind (fun _ => (U 0).1)).expect f
    simp only [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    rw [FiniteLaw.expect_pi_cons]
    rw [FiniteLaw.expect_comm]
    apply FiniteLaw.expect_congr
    intro b
    apply FiniteLaw.expect_congr
    intro c
    simp only [splitFirst,Fin.cons_zero,Fin.cons_succ]

lemma prod_empty_projects (n : ℕ) (T : KernelTower Ω n) (U : Fin 0 → KernelTower Λ n) :
    Projects Prod.fst n (prod n T (pi n U)) T := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (T.2 a.1) (fun i => (U i).2 (a.2 i))⟩
    intro f
    change (T.1.bind (fun _ => FiniteLaw.pi (fun i => (U i).1))).expect (fun a => f a.1)=T.1.expect f
    simp only [FiniteLaw.expect_bind,FiniteLaw.expect_const]

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TowerTerminalPad
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
lemma logMean_bind_point (P : FiniteLaw Ω) (a : Λ) (m : ℝ) (f : Ω×Λ → ℝ) :
    (P.bind (fun _ => point a)).logMean m f=P.logMean m (fun s => f (s,a)) := by
  simp only [logMean,expMoment,expect_bind,expect_point]
lemma logMean_point_bind (a : Ω) (Q : FiniteLaw Λ) (m : ℝ) (f : Ω×Λ → ℝ) :
    ((point a).bind (fun _ => Q)).logMean m f=Q.logMean m (fun s => f (a,s)) := by
  simp only [logMean,expMoment,expect_bind,expect_point]
end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

lemma backwardLog_terminal_pad (a : Ω) (b : Λ) (P : FiniteLaw Ω)
    (r : ℕ) (U : KernelTower Λ r) (m : Fin (r+1) → ℝ) (F : Ω → FinitePath Λ r → ℝ) :
    backwardLog (r+1) (prod (r+1) (terminalTower a P r) (pad b r U)) m
      (fun y => F (terminalState r (pathFst (r+1) y)) (pathPrefix r (pathSnd (r+1) y))) =
      backwardLog r U (fun d => m d.castSucc)
        (fun y => P.logMean (m (Fin.last r)) (fun s => F s y)) := by
  induction r with
  | zero =>
    change (P.bind (fun _ => FiniteLaw.point b)).logMean (m 0) (fun z => F z.1 ()) =
      P.logMean (m (Fin.last 0)) (fun s => F s ())
    exact FiniteLaw.logMean_bind_point P b _ _
  | succ r ih =>
    simp only [backwardLog,prod,terminalTower,pad,pathFst,pathSnd,terminalState,pathPrefix]
    rw [FiniteLaw.logMean_point_bind]
    apply congrArg (U.1.logMean (m 0))
    funext z
    exact ih (U.2 z) (fun d => m d.succ) (fun s y => F s (z,y))

end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityProxy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
namespace FiniteLaw
lemma pi_point {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ i,Fintype (α i)] (a : (i : ι) → α i) :
    pi (fun i => point (a i))=point a := by
  classical
  apply ext
  intro b
  by_cases h : a=b
  · subst b; simp [pi,point]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [pi,point,ite_eq_right (Ne.symm h)]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right (Ne.symm hi))
end FiniteLaw

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperTrial
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
attribute [local instance] OAI.DilutedSpinGlass.upperTrialMeasurableSpace
local instance upperTrialBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
namespace KernelTower
variable {Ω : Type} [Fintype Ω]
omit [Fintype Ω] in
lemma pathMap_pathPrefix {Λ : Type} (g : Ω → Λ) (n : ℕ) (y : FinitePath Ω (n+1)) :
    pathMap g n (pathPrefix n y)=pathPrefix n (pathMap g (n+1) y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (g y.1,pathMap g n (pathPrefix n y.2))=(g y.1,pathPrefix n (pathMap g (n+1) y.2))
      rw [ih]

lemma piTower_eq_pi {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (T : ι → KernelTower Ω n) : piTower n T=pi n T := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (_,fun (x : ι → Ω) => piTower n (fun i => (T i).2 (x i)))=(_,fun (x : ι → Ω) => pi n (fun i => (T i).2 (x i)))
      congr 1
      funext x
      exact ih _

lemma piTower_pad {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : Ω) (n : ℕ) (T : ι → KernelTower Ω n) :
    piTower (n+1) (fun i => pad a n (T i))=pad (fun _ : ι => a) n (piTower n T) := by
  induction n with
  | zero =>
      change (FiniteLaw.pi (fun _ : ι => FiniteLaw.point a),fun _ => ())=(FiniteLaw.point (fun _ : ι => a),fun _ => ())
      rw [FiniteLaw.pi_point]
  | succ n ih =>
      change (FiniteLaw.pi (fun i => (T i).1),fun (x : ι → Ω) => piTower (n+1) (fun i => pad a n ((T i).2 (x i))))=
        (FiniteLaw.pi (fun i => (T i).1),fun (x : ι → Ω) => pad (fun _ : ι => a) n (piTower n (fun i => (T i).2 (x i))))
      congr 1
      funext x
      exact ih _

omit [Fintype Ω] in
lemma proj_eq_pathMap {ι : Type} (n : ℕ) (y : FinitePath (ι → Ω) n) (i : ι) :
    FinitePath.proj n y i=pathMap (fun a : ι → Ω => a i) n y := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (y.1 i,FinitePath.proj n y.2 i)=(y.1 i,pathMap (fun a : ι → Ω => a i) n y.2)
      rw [ih]
end KernelTower

namespace PrescribedTree
variable {Λ R : Type} [Fintype Λ] [Fintype R]

attribute [local instance] OAI.DilutedSpinGlass.upperTrialMeasurableSpace
lemma finite_trialLog {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (F : (ι → ℝ) → ℝ) :
    trialLog r (finiteTrialLaw r Q U x) m F =
      (FiniteLaw.pi (fun _ : ι => Q)).expect (fun a =>
        KernelTower.backwardLog r (KernelTower.piTower r (fun i => U (a i))) m
          (fun y => F (fun i => x (a i) (KernelTower.pathMap (fun b : ι → Λ => b i) r y)))) := by
  unfold trialLog finiteTrialLaw
  rw [FiniteLaw.integral_pi_asProbability]
  apply FiniteLaw.expect_congr
  intro a
  rw [KernelTower.piTower_eq_pi]
  exact (KernelTower.backwardLog_realEncode r (fun i => U (a i)) (fun i => x (a i)) F m).symm.trans
    (by congr 1; funext y; simp only [KernelTower.proj_eq_pathMap])

lemma edgeRoot_pad (r : ℕ) (a : Λ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ) (hend : m (Fin.last r)≠0)
    {p : ℕ} (z : InteractionSample p) :
    edgeRoot (Λ := Λ) (R := R) (n := r+1) (p := p) Q (fun b : R => KernelTower.pad a r (U b))
      (fun (b : R) (y : FinitePath Λ (r+1)) => x b (KernelTower.pathPrefix r y)) m z =
      trialLog (ι := Fin p) r (finiteTrialLaw r Q U x) (fun j => m j.castSucc) (fun y => Real.log (edge z.1 y)) := by
  refine Eq.trans ?_ (finite_trialLog r Q U x (fun j => m j.castSucc) (fun y => Real.log (edge z.1 y))).symm
  change (FiniteLaw.pi (fun _ : Fin p => Q)).expect _ =
    (FiniteLaw.pi (fun _ : Fin p => Q)).expect _
  apply FiniteLaw.expect_congr
  intro b
  rw [KernelTower.piTower_pad a r (fun i : Fin p => U (b i))]
  have he (y : FinitePath (Fin p → Λ) (r+1)) :
      (fun j => x (b j) (KernelTower.pathPrefix r (KernelTower.pathMap (fun a : Fin p → Λ => a j) (r+1) y)))=
      (fun j => x (b j) (KernelTower.pathMap (fun a : Fin p → Λ => a j) r (KernelTower.pathPrefix r y))) := by
    funext j
    rw [KernelTower.pathMap_pathPrefix]
  simp only [he]
  exact KernelTower.backwardLog_pad (fun _ : Fin p => a) r
    (KernelTower.piTower r (fun i : Fin p => U (b i))) m hend
    (fun y : FinitePath (Fin p → Λ) r => Real.log (edge z.1
      (fun j => x (b j) (KernelTower.pathMap (fun c : Fin p → Λ => c j) r y))))

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TerminalMeanField
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open scoped BigOperators
namespace FiniteLaw
variable {ι κ Ω : Type} [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
lemma expect_pi_curry (Q : ι → κ → FiniteLaw Ω) (f : (ι×κ → Ω) → ℝ) :
    (pi (fun i => pi (Q i))).expect (fun x => f (fun z => x z.1 z.2))=
      (pi (fun z : ι×κ => Q z.1 z.2)).expect f := by
  classical
  symm
  unfold expect
  apply Fintype.sum_equiv (Equiv.curry ι κ Ω)
  intro x
  simp only [pi,Equiv.curry_apply,Function.curry,Fintype.prod_prod_type]

end FiniteLaw
namespace KernelTower
variable {ι κ Ω : Type} [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
lemma pi_curry_projects (n : ℕ) (T : ι → κ → KernelTower Ω n) :
    Projects (fun x : ι → κ → Ω => fun z : ι×κ => x z.1 z.2) n
      (pi n (fun i => pi n (T i))) (pi n (fun z : ι×κ => T z.1 z.2)) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨FiniteLaw.expect_pi_curry (fun i j => (T i j).1),fun a => ih (fun i j => (T i j).2 (a i j))⟩

lemma pi_injective_projects (e : ι → κ) (he : Function.Injective e) (n : ℕ) (T : κ → KernelTower Ω n) :
    Projects (fun x : κ → Ω => fun i => x (e i)) n
      (pi n T) (pi n (fun i => T (e i))) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨FiniteLaw.expect_pi_injective (fun j => (T j).1) e he,fun a => ih (fun j => (T j).2 (a j))⟩

lemma pi_rect_castSucc_projects (n k q : ℕ) (T : Fin k → Fin (q+1) → KernelTower Ω n) :
    Projects (fun x : Fin k → Fin (q+1) → Ω => fun z : Fin k×Fin q => x z.1 z.2.castSucc) n
      (pi n (fun i => piTower n (T i)))
      (piTower n (fun z : Fin k×Fin q => T z.1 z.2.castSucc)) := by
  simp only [piTower_eq_pi]
  exact (pi_curry_projects n T).comp n
    (pi_injective_projects (fun z : Fin k×Fin q => (z.1,z.2.castSucc))
      (by
        intro a b h
        apply Prod.ext
        · exact congrArg (fun z : Fin k×Fin (q+1) => z.1) h
        · exact (Fin.castSucc_injective q) (congrArg (fun z : Fin k×Fin (q+1) => z.2) h)) n _)
end KernelTower
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperCountState
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators

variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma cavityEnergy_bound (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (l : ℕ) (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) (y : FinitePath (CavityState Ω Λ p l) n) :
    |cavityEnergy V x j l r i z f y|≤B+∑ a,‖(rootArray l z a).1‖ := by
  induction l with
  | zero => simpa [cavityEnergy] using hf y
  | succ l ih =>
    apply (abs_add_le _ _).trans
    calc
      _ ≤ (B+∑ a,‖(rootArray l z.2 a).1‖)+‖z.1.1‖ :=
        add_le_add (ih r.2 i.2 z.2 (pathFst n y)) (mixedEnergy_bound z.1 (fun a => decide (a=j)) _ _)
      _ = _ := by simp only [rootArray,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]; ring

omit [Fintype R] [NeZero N] in
lemma cavityRoot_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |cavityRoot T U V x m j l r i z f|≤B+∑ a,‖(rootArray l z a).1‖ :=
  backwardLog_bound n _ m hm (cavityEnergy_bound V x j l r i z f hf)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperDatum
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

lemma rootArray_rootMap {X Y : Type} (f : X → Y) (k : ℕ) (z : RootPath X k) (i : Fin k) :
    rootArray k (rootMap f k z) i=f (rootArray k z i) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    refine Fin.cases rfl (fun i => ?_) i
    exact ih z.2 i

lemma measurable_rootMap {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (k : ℕ) : Measurable (rootMap f k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact (hf.comp measurable_fst).prodMk (ih.comp measurable_snd)

namespace PrescribedTree
variable {Ω Λ R X : Type} [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace X]
    {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma measurable_cavityEnergy (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : X → RootPath (InteractionSample p) l) (hz : Measurable z)
    (f : X → FinitePath Ω n → ℝ) (hf : ∀ y,Measurable (fun a => f a y))
    (y : FinitePath (CavityState Ω Λ p l) n) :
    Measurable (fun a => cavityEnergy V x j l r i (z a) (f a) y) := by
  induction l with
  | zero => exact hf y
  | succ l ih =>
    apply (ih r.2 i.2 (fun a => (z a).2) (measurable_snd.comp hz) (KernelTower.pathFst n y)).add
    exact (measurable_mixedEnergy _ _ _).comp (measurable_fst.comp hz)

omit [Fintype R] [NeZero N] in
lemma measurable_cavityRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : X → RootPath (InteractionSample p) l) (hz : Measurable z)
    (f : X → FinitePath Ω n → ℝ) (hf : ∀ y,Measurable (fun a => f a y)) :
    Measurable (fun a => cavityRoot T U V x m j l r i (z a) (f a)) :=
  KernelTower.measurable_backwardLog n _ m (measurable_cavityEnergy V x j l r i z hz f hf)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootMapLaw
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
lemma measurePreserving_rootMap {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (k : ℕ) :
    MeasurePreserving (rootMap f k) (rootLaw k (fun _ => μ)) (rootLaw k (fun _ => ν)) := by
  induction k with
  | zero => exact MeasurePreserving.id _
  | succ k ih => exact hf.prod ih

lemma integral_rootMap {μ : Measure X} {ν : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f : X → Y}
    (hf : MeasurePreserving f μ ν) (k : ℕ) (F : RootPath Y k → ℝ)
    (hF : Measurable F) :
    (∫ z,F (rootMap f k z) ∂rootLaw k (fun _ => μ))=∫ w,F w ∂rootLaw k (fun _ => ν) :=
by
  rw [← (measurePreserving_rootMap hf k).map_eq,
    integral_map (measurable_rootMap f hf.measurable k).aemeasurable hF.aestronglyMeasurable]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullRootIncrement
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]

omit [Fintype Ω] [Fintype Λ] in
lemma pathMap_fst (n : ℕ) (y : FinitePath (Ω×Λ) n) :
    pathMap Prod.fst n y=pathFst n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)
end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityPack
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

omit [Fintype R] in
lemma cavityPack_projects (T : KernelTower Ω n) (U : R → KernelTower Λ n) (l : ℕ)
    (r : RootPath (Fin p → R) l) :
    Projects (cavityPack l) n
      (prod n T (pi n (fun i : Fin l => piTower n (fun j => U (rootArray l r i j)))))
      (cavityTower T U l r) := by
  induction l with
  | zero => exact prod_empty_projects n T _
  | succ l ih =>
    have hg := splitFirst_projects n l T (fun i => piTower n (fun j => U (rootArray (l+1) r i j)))
    have hh := (ih r.2).prod n (Projects.refl n (piTower n (fun j => U (r.1 j))))
    exact hg.comp n hh

omit [Fintype Ω] [Fintype Λ] in
lemma cavityProject_pack (l : ℕ) (z : Ω × (Fin l → Fin p → Λ)) :
    cavityProject l (cavityPack l z)=z.1 := by
  induction l with
  | zero => rfl
  | succ l ih => exact ih (z.1,fun i => z.2 i.succ)

omit [Fintype Ω] [Fintype Λ] in
lemma pathFst_pack (l : ℕ) (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    pathFst n (pathMap (cavityPack (l+1)) n y)=
      pathMap (cavityPack l) n (pathMap (fun z : Ω × (Fin (l+1) → Fin p → Λ) => (z.1,fun i => z.2 i.succ)) n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathSnd_pack (l : ℕ) (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    pathSnd n (pathMap (cavityPack (l+1)) n y)=
      pathMap (fun z : Ω × (Fin (l+1) → Fin p → Λ) => z.2 0) n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathProject_pack (l : ℕ) (y : FinitePath (Ω × (Fin l → Fin p → Λ)) n) :
    pathMap (cavityProject l) n (pathMap (cavityPack l) n y)=pathFst n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_pack l y.1) (ih y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityOldNewMean
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

omit [Fintype Ω] [Fintype Λ] in
lemma pathFst_tail (l : ℕ) (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    pathFst n (pathMap (fun z : Ω × (Fin (l+1) → Fin p → Λ) => (z.1,fun i : Fin l => z.2 i.succ)) n y)=pathFst n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma singleBlockEnergy_pack (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (j : Fin p) (l : ℕ) (r : Fin p → R) (z : InteractionSample p)
    (y : FinitePath (Ω × (Fin (l+1) → Fin p → Λ)) n) :
    singleBlockEnergy V x j l r z (pathMap (cavityPack (l+1)) n y)=
      mixedEnergy z (fun a => decide (a=j)) (fun _ => V (pathFst n y))
        (fun a => x (r a) (pathMap (fun b : Ω × (Fin (l+1) → Fin p → Λ) => b.2 0 a) n y)) := by
  unfold singleBlockEnergy
  rw [pathFst_pack,pathProject_pack,pathFst_tail,pathSnd_pack]
  simp only [← pathMap_comp,Function.comp_def]

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma activeEnergy_pack (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (j : Fin p) (l : ℕ) (r : RootPath (Fin p → R) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (Ω × (Fin l → Fin p → Λ)) n) :
    activeEnergy V x j l r z f (pathMap (cavityPack l) n y)=
      f (pathFst n y)+∑ i,mixedEnergy (rootArray l z i) (fun a => decide (a=j))
        (fun _ => V (pathFst n y))
        (fun a => x (rootArray l r i a) (pathMap (fun b : Ω × (Fin l → Fin p → Λ) => b.2 i a) n y)) := by
  induction l with
  | zero =>
    change f (pathMap Prod.fst n y)=f (pathFst n y)+∑ i : Fin 0,_
    simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero,pathMap_fst]
  | succ l ih =>
    change activeEnergy V x j l r.2 z.2 f (pathFst n (pathMap (cavityPack (l+1)) n y))+
      singleBlockEnergy V x j l r.1 z.1 (pathMap (cavityPack (l+1)) n y)=_
    rw [pathFst_pack,ih,singleBlockEnergy_pack,pathFst_tail,Fin.sum_univ_succ]
    simp only [rootArray,Fin.cons_zero,Fin.cons_succ,←pathMap_comp,Function.comp_def]
    ring

omit [Fintype R] in
lemma activeRoot_flat (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ) :
    backwardLog n (cavityTower T U l r) m (activeEnergy V x j l r z f)=
      backwardLog n (prod n T (pi n (fun i : Fin l => piTower n (fun a => U (rootArray l r i a))))) m
        (fun y => f (pathFst n y)+∑ i,mixedEnergy (rootArray l z i) (fun a => decide (a=j))
          (fun _ => V (pathFst n y))
          (fun a => x (rootArray l r i a) (pathMap (fun b : Ω × (Fin l → Fin p → Λ) => b.2 i a) n y))) := by
  rw [←backwardLog_of_projects n (cavityPack_projects T U l r)]
  congr 1
  funext y
  exact activeEnergy_pack V x j l r z f y

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonReplacement
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

lemma successCount_le {p k : ℕ} [NeZero p] (a : Fin k → Fin p) : successCount a ≤ k := by
  unfold successCount
  apply (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin k))) =>
    show (if a i=0 then 1 else 0)≤1 by split_ifs <;> omega)).trans_eq
  simp

lemma successCount_cons {p k : ℕ} [NeZero p] (a : Fin p) (x : Fin k → Fin p) :
    successCount (Fin.cons a x)=(if a=0 then 1 else 0)+successCount x := by
  simp only [successCount,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

lemma uniform_indicator_expect (p : ℕ) [NeZero p] (f : ℕ → ℝ) (n : ℕ) :
    (FiniteLaw.uniform : FiniteLaw (Fin p)).expect (fun a => f (n+if a=0 then 1 else 0)) =
      (f (n+1)+((p-1:ℕ):ℝ)*f n)/p := by
  classical
  rw [FiniteLaw.uniform_expect,Fintype.card_fin]
  congr 1
  have he (a : Fin p) : f (n+if a=0 then 1 else 0)=
      (if a=0 then f (n+1)-f n else 0)+f n := by split_ifs <;> simp
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [Nat.cast_sub (NeZero.pos p),Nat.cast_one]
  ring

/-- Finite independent replacement of real-or-null interactions by cavity
interactions. The error has its exact extensive coefficient. -/
lemma finite_count_replacement (p : ℕ) [NeZero p] (f : ℕ → ℕ → ℝ) (c : ℝ)
    (h : ∀ n l,f (n+1) l+((p-1:ℕ):ℝ)*f n l ≤ (p:ℝ)*(f n (l+1)-c))
    (k n l : ℕ) :
    (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
      (fun a => f (n+successCount a) l) ≤ f n (l+k)-(k:ℝ)*c := by
  induction k generalizing l with
  | zero => simp [FiniteLaw.expect,FiniteLaw.pi,successCount]
  | succ k ih =>
      rw [FiniteLaw.expect_pi_cons]
      simp only [successCount_cons]
      rw [FiniteLaw.expect_comm]
      calc
        _ ≤ (FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
            (fun a => f (n+successCount a) (l+1)-c) := by
          apply FiniteLaw.expect_mono
          intro a
          have hn : ∀ b : Fin p,n+((if b=0 then 1 else 0)+successCount a)=
              (n+successCount a)+(if b=0 then 1 else 0) := by intro b; omega
          simp_rw [hn]
          rw [uniform_indicator_expect p (fun k => f k l)]
          exact (div_le_iff₀ (by exact_mod_cast NeZero.pos p)).mpr (by
            simpa only [mul_comm (p:ℝ)] using h (n+successCount a) l)
        _ ≤ f n ((l+1)+k)-(k:ℝ)*c-c := by
          rw [FiniteLaw.expect_sub,FiniteLaw.expect_const]
          exact sub_le_sub_right (ih (l+1)) c
        _ = _ := by rw [show (l+1)+k=l+(k+1) by omega,Nat.cast_add,Nat.cast_one]; ring

lemma integral_poisson_thinning (r : ℝ≥0) (p : ℕ) [NeZero p]
    (f : ℕ → ℝ) {B D : ℝ} (hD : 0≤D) (hf : ∀ n,|f n|≤B+D*n) :
    (∫ k,(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
      (fun a => f (successCount a)) ∂poissonMeasure r) =
    ∫ n,f n ∂poissonMeasure (r/p) := by
  let ν := fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin p))
  have hi : Integrable (fun z : (k : ℕ) × (Fin k → Fin p) => f (successCount z.2))
      (familyLaw (poissonMeasure r) ν) := by
    apply familyLaw_integrable_bound (poissonMeasure r) ν
      (fun k (a : Fin k → Fin p) => f (successCount a)) (fun _ => measurable_of_countable _)
      ((integrable_const B).add ((poisson_integrable_count r).const_mul D))
    intro k a
    exact (hf _).trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (show (successCount a:ℝ)≤k by exact_mod_cast successCount_le a) hD) B)
  rw [← map_poisson_successCount r p]
  rw [integral_map (measurable_sigmaUncurry (fun k => measurable_of_countable (fun a : Fin k → Fin p => successCount a))).aemeasurable
    (measurable_of_countable f).aestronglyMeasurable]
  rw [integral_familyLaw (poissonMeasure r) ν (fun k (a : Fin k → Fin p) => f (successCount a))
    (fun _ => measurable_of_countable _) hi]
  apply integral_congr_ae
  filter_upwards [] with k
  dsimp only [ν]
  rw [finiteUniform_pi,integral_finiteUniform]
  have hh : FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p))) =
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p)) := by
    apply FiniteLaw.ext
    intro a
    simp [FiniteLaw.pi,FiniteLaw.uniform]
  rw [hh,FiniteLaw.uniform_expect]
  simp [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- Uniformized Poisson interpolation endpoint. The sole local input is the
conditional cavity replacement inequality, at ALL old real/cavity counts. -/
lemma poisson_count_replacement (r : ℝ≥0) (p : ℕ) [NeZero p]
    (f : ℕ → ℕ → ℝ) (c : ℝ) {B D : ℝ} (hD : 0≤D)
    (hf : ∀ n l,|f n l|≤B+D*(n+l))
    (h : ∀ n l,f (n+1) l+((p-1:ℕ):ℝ)*f n l ≤ (p:ℝ)*(f n (l+1)-c)) :
    (∫ n,f n 0 ∂poissonMeasure (r/p))+(r:ℝ)*c ≤ ∫ l,f 0 l ∂poissonMeasure r := by
  rw [← integral_poisson_thinning r p (fun n => f n 0) hD (by simpa using fun n => hf n 0)]
  have hb (k : ℕ) : |(FiniteLaw.pi (fun _ : Fin k => (FiniteLaw.uniform : FiniteLaw (Fin p)))).expect
      (fun a => f (successCount a) 0)|≤B+D*k := by
    apply FiniteLaw.abs_expect_le
    intro a
    exact (hf _ 0).trans (by simpa only [Nat.cast_zero,add_zero] using (add_le_add_right (mul_le_mul_of_nonneg_left (show (successCount a:ℝ)≤k by exact_mod_cast successCount_le a) hD) B))
  have hi := poisson_average_integrable r _ hb
  have hj := poisson_average_integrable r (fun k => f 0 k) (by simpa using fun k => hf 0 k)
  have hh := integral_mono hi (hj.sub ((poisson_integrable_count r).mul_const c))
    (fun k => by simpa only [zero_add,Pi.sub_apply] using finite_count_replacement p f c h k 0 0)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hj ((poisson_integrable_count r).mul_const c),integral_mul_const,poisson_mean] at hh
  linarith

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperCountMean
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [NeZero N] in
lemma measurable_datumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ) :
    Measurable (fun z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
      datumRoot T U V x m j f k l z.1 z.2) := by
  let F := fun z : (RootPath (InteractionSample p) k × RootPath (InteractionSample p) l) ×
      (RootPath (Fin p → Fin N) k × RootPath (Fin p → Fin N) l × RootPath (Fin p → R) l) =>
    cavityRoot T U V x m j l z.2.2.2 z.2.2.1 z.1.2 (realCountEnergy V k z.2.1 z.1.1 f)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    apply measurable_cavityRoot
    · exact measurable_snd
    · intro y
      apply measurable_const.add
      exact Finset.measurable_sum _ (fun a _ =>
        (measurable_pi_apply _).comp (measurable_fst.comp ((measurable_rootArray k a).comp measurable_fst)))
  exact hF.comp
    ((((measurable_rootMap Prod.fst measurable_fst k).comp measurable_fst).prodMk
      ((measurable_rootMap Prod.fst measurable_fst l).comp measurable_snd)).prodMk
      (((measurable_rootMap (fun a : UpperDatum p N R => a.2.1) measurable_snd.fst k).comp measurable_fst).prodMk
        (((measurable_rootMap (fun a : UpperDatum p N R => a.2.1) measurable_snd.fst l).comp measurable_snd).prodMk
          ((measurable_rootMap (fun a : UpperDatum p N R => a.2.2) measurable_snd.snd l).comp measurable_snd))))

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperRealEndpoint
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory KernelTower
open scoped BigOperators ENNReal

lemma FiniteLaw.uniform_asProbability {J : Type} [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    ((FiniteLaw.uniform : FiniteLaw J).asProbability id).toMeasure=finiteUniform J := by
  apply Measure.ext_of_singleton
  intro j
  rw [FiniteLaw.asProbability_id_singleton]
  change ENNReal.ofReal ((Fintype.card J : ℝ)⁻¹)=(PMF.uniformOfFintype J).toMeasure {j}
  rw [PMF.toMeasure_apply_singleton,PMF.uniformOfFintype_apply,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card J))]
  · simp
  · exact measurableSet_singleton j


namespace PrescribedTree
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperDatum_real_projection (M : Model p) (Q : FiniteLaw R) :
    MeasurePreserving (fun a : UpperDatum p N R => (a.1,a.2.1))
      (upperDatumLaw M Q) (M.disorder.toMeasure.prod (finiteUniform (Fin p → Fin N))) := by
  unfold upperDatumLaw
  rw [FiniteLaw.pi_uniform,FiniteLaw.uniform_asProbability]
  exact (MeasurePreserving.id _).prod measurePreserving_fst

end PrescribedTree
end DilutedSpinGlass

end

section
namespace DilutedSpinGlass.KernelTower
variable {Ω : Type} [Fintype Ω]
lemma pi_pad {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : Ω) (n : ℕ) (T : ι → KernelTower Ω n) :
    pi (n+1) (fun i => pad a n (T i))=pad (fun _ : ι => a) n (pi n T) := by
  simp_rw [←piTower_eq_pi]
  exact piTower_pad a n T
omit [Fintype Ω] in
lemma pathMap_snd {Λ : Type} (n : ℕ) (y : FinitePath (Ω×Λ) n) :
    pathMap Prod.snd n y=pathSnd n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)
end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open KernelTower
open scoped BigOperators
variable {Λ R : Type} [Fintype Λ] [Fintype R]
omit [Fintype R] in
lemma activeRoot_site (a : Λ) (r : ℕ) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ) (hend : m (Fin.last r)=1)
    (q k : ℕ) (b : RootPath (Fin (q+1) → R) k) (z : RootPath (InteractionSample (q+1)) k) (h : ℝ) :
    backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k b) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k b z
        (fun y => h*spin (terminalState r y))) =
      backwardLog r (piTower r (fun c : Fin k×Fin q => U (rootArray k b c.1 c.2.castSucc)))
        (fun d => m d.castSucc) (fun y => siteLog (rootArray k z) h
          (fun c => x (rootArray k b c.1 c.2.castSucc)
            (pathMap (fun w : Fin k×Fin q → Λ => w c) r y))) := by
  rw [activeRoot_flat]
  simp_rw [piTower_pad a r]
  rw [pi_pad (fun _ : Fin (q+1) => a) r]
  let F := fun (s : Spin) (y : FinitePath (Fin k → Fin (q+1) → Λ) r) =>
    h*spin s+∑ i,message (rootArray k z i).1
      (fun j => x (rootArray k b i j.castSucc)
        (pathMap (fun w : Fin k → Fin (q+1) → Λ => w i j.castSucc) r y)) s
  have he : (fun y : FinitePath (Spin × (Fin k → Fin (q+1) → Λ)) (r+1) =>
      h*spin (terminalState r (pathFst (r+1) y))+
        ∑ i,mixedEnergy (rootArray k z i) (fun j => decide (j=Fin.last q))
          (fun _ => terminalState r (pathFst (r+1) y))
          (fun j => x (rootArray k b i j) (pathPrefix r
            (pathMap (fun w : Spin × (Fin k → Fin (q+1) → Λ) => w.2 i j) (r+1) y)))) =
      fun y => F (terminalState r (pathFst (r+1) y)) (pathPrefix r (pathSnd (r+1) y)) := by
    funext y
    simp only [mixedEnergy_last,F]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext j
    congr 1
    rw [pathMap_pathPrefix]
    rw [←pathMap_snd,←pathMap_comp]
    rfl
  rw [he,backwardLog_terminal_pad,hend]
  have hs (y : FinitePath (Fin k → Fin (q+1) → Λ) r) :
      (FiniteLaw.uniform : FiniteLaw Spin).logMean 1 (fun s => F s y)=
      siteLog (rootArray k z) h (fun c : Fin k×Fin q => x (rootArray k b c.1 c.2.castSucc)
        (pathMap (fun w : Fin k → Fin (q+1) → Λ => w c.1 c.2.castSucc) r y)) := by
    simp only [FiniteLaw.logMean,FiniteLaw.expMoment,one_mul,div_one,FiniteLaw.expect,
      FiniteLaw.uniform,Fintype.card_bool,Nat.cast_ofNat,inv_mul_eq_div,
      siteLog,F,Finset.sum_div]
  simp only [hs]
  rw [←backwardLog_of_projects r (pi_rect_castSucc_projects r k q (fun i j => U (rootArray k b i j)))]
  congr 1
  funext y
  congr 1
  funext c
  congr 1
  rw [←pathMap_comp]
  rfl

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavitySiteMean
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
namespace FiniteLaw
variable {R : Type} [Fintype R]
lemma expect_rect_castSucc (Q : FiniteLaw R) (k q : ℕ) (F : (Fin k×Fin q → R) → ℝ) :
    (pi (fun _ : Fin k => pi (fun _ : Fin (q+1) => Q))).expect
      (fun x => F (fun c => x c.1 c.2.castSucc))=
      (pi (fun _ : Fin k×Fin q => Q)).expect F := by
  apply (expect_pi_curry (fun (_ : Fin k) (_ : Fin (q+1)) => Q)
    (fun y : Fin k×Fin (q+1) → R => F (fun c => y (c.1,c.2.castSucc)))).trans
  exact expect_pi_injective (fun _ : Fin k×Fin (q+1) => Q)
    (fun z : Fin k×Fin q => (z.1,z.2.castSucc)) (by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun z : Fin k×Fin (q+1) => z.1) h
      · exact (Fin.castSucc_injective q) (congrArg (fun z : Fin k×Fin (q+1) => z.2) h)) F
end FiniteLaw
namespace PrescribedTree
open KernelTower
variable {Λ R : Type} [Fintype Λ] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R]
lemma activeRoot_site_mean (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ) (hend : m (Fin.last r)=1)
    (q k : ℕ) (z : RootPath (InteractionSample (q+1)) k) (h : ℝ) :
    (∫ b : RootPath (Fin (q+1) → R) k,backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k b) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k b z
        (fun y => h*spin (terminalState r y)))
      ∂rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog (rootArray k z) h) := by
  simp_rw [activeRoot_site a r U x m hend q k]
  let F := fun b : Fin k → Fin (q+1) → R =>
    backwardLog r (piTower r (fun c : Fin k×Fin q => U (b c.1 c.2.castSucc)))
      (fun d => m d.castSucc) (fun y => siteLog (rootArray k z) h
        (fun c => x (b c.1 c.2.castSucc) (pathMap (fun w : Fin k×Fin q → Λ => w c) r y)))
  change (∫ b,F (rootArray k b) ∂rootLaw k (fun _ =>
    ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=_
  rw [integral_rootArray_eq_pi _ k F]
  rw [FiniteLaw.integral_pi_asProbability]
  rw [finite_trialLog]
  exact FiniteLaw.expect_rect_castSucc Q k q (fun b =>
    backwardLog r (piTower r (fun c => U (b c))) (fun d => m d.castSucc)
      (fun y => siteLog (rootArray k z) h (fun c => x (b c) (pathMap (fun w : Fin k×Fin q → Λ => w c) r y))))
end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FirstMomentUpper
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators

lemma integrable_rootArray_sum {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Integrable g μ) (k : ℕ) :
    Integrable (fun z : RootPath X k => ∑ a,g (rootArray k z a)) (rootLaw k (fun _ => μ)) := by
  apply integrable_finsetSum
  intro a _
  simpa only [Function.comp_def, rootArrayEquiv_apply] using
    (measurePreserving_rootArray μ k).integrable_comp_of_integrable
      (integrable_comp_eval (μ := fun _ : Fin k => μ) (i := a) hg)

lemma integral_rootArray_sum {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (g : X → ℝ) (hg : Integrable g μ) (k : ℕ) :
    (∫ z : RootPath X k,∑ a,g (rootArray k z a) ∂rootLaw k (fun _ => μ))=k*∫ x,g x ∂μ := by
  rw [integral_rootArray_eq_pi μ k (fun z => ∑ a,g (z a)),
    integral_finsetSum _ (fun a _ => integrable_comp_eval (μ := fun _ : Fin k => μ) (i := a) hg)]
  have he (a : Fin k) : (∫ z : Fin k → X,g (z a) ∂Measure.pi (fun _ => μ))=∫ x,g x ∂μ :=
    integral_comp_eval (μ := fun _ : Fin k => μ) (i := a) hg.aestronglyMeasurable
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

namespace PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma datumRoot_norm_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) (z : RootPath (UpperDatum p N R) k) (w : RootPath (UpperDatum p N R) l)
    {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |datumRoot T U V x m j f k l z w|≤B+(∑ a,‖(rootArray k z a).1.1‖)+(∑ a,‖(rootArray l w a).1.1‖) := by
  have hbase (y : FinitePath Ω n) :
      |realCountEnergy V k (rootMap (fun a => a.2.1) k z) (rootMap Prod.fst k z) f y|≤B+∑ a,‖(rootArray k z a).1.1‖ := by
    apply (abs_add_le _ _).trans
    apply add_le_add (hf y)
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun a _ => by simpa only [rootArray_rootMap,Real.norm_eq_abs] using norm_le_pi_norm (rootArray k z a).1.1 _)
  simpa only [rootArray_rootMap,datumRoot] using cavityRoot_bound T U V x m hm j l
    (rootMap (fun a => a.2.2) l w) (rootMap (fun a => a.2.1) l w) (rootMap Prod.fst l w) _ hbase

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PhysicalReservoirIncrement
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory

namespace PrescribedTree
open KernelTower
open scoped BigOperators
variable {Ω Λ R X : Type} [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace X]
    {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma measurable_activeEnergy (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ) (r : RootPath (Fin p → R) l)
    (z : X → RootPath (InteractionSample p) l) (hz : Measurable z)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (CavityState Ω Λ p l) n) :
    Measurable (fun a => activeEnergy V x j l r (z a) f y) := by
  induction l with
  | zero => exact measurable_const
  | succ l ih =>
    apply (ih r.2 (fun a => (z a).2) (measurable_snd.comp hz) (pathFst n y)).add
    exact (measurable_mixedEnergy _ _ _).comp (measurable_fst.comp hz)

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma activeEnergy_bound (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ) (r : RootPath (Fin p → R) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) (y : FinitePath (CavityState Ω Λ p l) n) :
    |activeEnergy V x j l r z f y|≤B+∑ i,‖(rootArray l z i).1‖ := by
  induction l with
  | zero => simpa [activeEnergy] using hf y
  | succ l ih =>
    apply (abs_add_le _ _).trans
    have h := add_le_add (ih r.2 z.2 (pathFst n y))
      (mixedEnergy_bound z.1 (fun a => decide (a=j))
        (fun _ => V (pathMap (cavityProject l) n (pathFst n y)))
        (fun a => x (r.1 a) (pathMap (fun b : Fin p → Λ => b a) n (pathSnd n y))))
    simpa only [singleBlockEnergy,Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ,add_assoc,add_comm,add_left_comm] using h

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootSplit
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory

lemma measurePreserving_rootSplit {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν] (k : ℕ) :
    MeasurePreserving (fun z : RootPath (X×Y) k => (rootMap Prod.fst k z,rootMap Prod.snd k z))
      (rootLaw k (fun _ => μ.prod ν)) ((rootLaw k (fun _ => μ)).prod (rootLaw k (fun _ => ν))) := by
  have h := ((MeasurePreserving.symm (rootArrayEquiv k) (measurePreserving_rootArray μ k)).prod
    (MeasurePreserving.symm (rootArrayEquiv k) (measurePreserving_rootArray ν k))).comp
    ((measurePreserving_arrowProdEquivProdArrow X Y (Fin k) (fun _ => μ) (fun _ => ν)).comp
      (measurePreserving_rootArray (μ.prod ν) k))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  apply Prod.ext
  · apply (rootArrayEquiv (X := X) k).injective
    dsimp only [Function.comp_apply,Prod.map,Prod.fst]
    rw [MeasurableEquiv.apply_symm_apply]
    funext i
    simp only [rootArrayEquiv_apply,rootArray_rootMap]
    rfl
  · apply (rootArrayEquiv (X := Y) k).injective
    dsimp only [Function.comp_apply,Prod.map,Prod.snd]
    rw [MeasurableEquiv.apply_symm_apply]
    funext i
    simp only [rootArrayEquiv_apply,rootArray_rootMap]
    rfl

lemma integral_rootSplit {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (k : ℕ) (F : RootPath X k × RootPath Y k → ℝ) (hF : Measurable F)
    (hi : Integrable F ((rootLaw k (fun _ => μ)).prod (rootLaw k (fun _ => ν)))) :
    (∫ z,F (rootMap Prod.fst k z,rootMap Prod.snd k z) ∂rootLaw k (fun _ => μ.prod ν))=
      ∫ x,∫ y,F (x,y) ∂rootLaw k (fun _ => ν) ∂rootLaw k (fun _ => μ) := by
  have hp := measurePreserving_rootSplit μ ν k
  rw [← integral_prod F hi,←hp.map_eq,
    integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FirstMomentFresh
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
lemma integral_root_prod_finite_integrable {X J : Type} [MeasurableSpace X]
    [Fintype J] [Nonempty J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin n → X) × (Fin n → J) → ℝ) (_hF : Measurable F)
    (hi : Integrable F ((Measure.pi (fun _ : Fin n => μ)).prod
      (Measure.pi (fun _ : Fin n => finiteUniform J)))) :
    (∫ z : RootPath (X×J) n,F ((fun i => (rootArray n z i).1),(fun i => (rootArray n z i).2))
      ∂rootLaw n (fun _ => μ.prod (finiteUniform J))) =
      ∫ x : Fin n → X,(FiniteLaw.uniform : FiniteLaw (Fin n → J)).expect (fun j => F (x,j))
        ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_root_prod μ (finiteUniform J) n F hi]
  simp only [finiteUniform_pi]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_finiteUniform,FiniteLaw.expect_uniform]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_ExtendedExponents
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
lemma snoc_exponents_pos {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    ∀ i : Fin (r+1),0 < Fin.snoc (α := fun _ => ℝ) m (1:ℝ) i := by
  intro i
  exact Fin.lastCases (by simp) (fun j => by simpa using (hm.2 j).1) i
lemma snoc_exponents_mono {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    Monotone (Fin.snoc (α := fun _ => ℝ) m (1:ℝ)) := by
  intro i j hij
  induction j using Fin.lastCases with
  | last =>
    simpa only [Fin.snoc_last] using
      (Fin.lastCases (by simp) (fun a => by simpa using (hm.2 a).2.le) i : Fin.snoc (α := fun _ => ℝ) m (1:ℝ) i≤1)
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last j)) hij)
    | cast i =>
      simpa only [Fin.snoc_castSucc] using hm.1.monotone (show i≤j from hij)
lemma cons_snoc_exponents_mono {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    Monotone (Fin.cons (α := fun _ => ℝ) (0:ℝ) (Fin.snoc (α := fun _ => ℝ) m (1:ℝ))) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact le_refl _
    | succ j => simpa using (snoc_exponents_pos hm j).le
  | succ i =>
    induction j using Fin.cases with
    | zero => exact False.elim ((not_le_of_gt (Fin.succ_pos i)) hij)
    | succ j =>
      simpa only [Fin.cons_succ] using snoc_exponents_mono hm (show i≤j from Fin.succ_le_succ_iff.mp hij)
lemma cons_snoc_exponents_nonneg {r : ℕ} {m : Fin r → ℝ} (hm : Exponents m) :
    ∀ i,0 ≤ Fin.cons (α := fun _ => ℝ) (0:ℝ) (Fin.snoc (α := fun _ => ℝ) m (1:ℝ)) i := by
  intro i
  exact Fin.cases (by simp) (fun j => by simpa using (snoc_exponents_pos hm j).le) i
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TerminalPiRoot
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]
lemma backwardLog_pi_terminal (a : ι → Ω) (P : ι → FiniteLaw Ω) (r : ℕ)
    (m : Fin (r+1) → ℝ) (hm : ∀ d,m d≠0) (f : (ι → Ω) → ℝ) :
    backwardLog (r+1) (pi (r+1) (fun i => terminalTower (a i) (P i) r)) m
      (fun y => f (fun i => terminalState r (FinitePath.proj (r+1) y i)))=
      (FiniteLaw.pi P).logMean (m (Fin.last r)) f := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change (FiniteLaw.pi (fun i => FiniteLaw.point (a i))).logMean (m 0)
      (fun _ => backwardLog (r+1) (pi (r+1) (fun i => terminalTower (a i) (P i) r))
        (fun d => m d.succ) (fun y => f (fun i => terminalState r (FinitePath.proj (r+1) y i))))=_
    rw [ih (fun d => m d.succ) (fun d => hm d.succ)]
    exact FiniteLaw.logMean_const _ (hm 0) _
end DilutedSpinGlass.KernelTower

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.SATComputability_InterpolationUpper
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open DilutedSpinGlass DilutedSpinGlass.PrescribedTree DilutedSpinGlass.KernelTower
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Topology

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperDatum_integrable_norm (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R) :
    Integrable (fun a : UpperDatum p N R => ‖a.1.1‖) (upperDatumLaw (N := N) M Q) :=
  measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma datumRoot_integrable_firstMoment (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    Integrable (fun z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
      datumRoot T U V x m j f k l z.1 z.2)
      ((rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) := by
  have hk := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) (fun a => ‖a.1.1‖) (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperDatum_integrable_norm M hM Q) k
  have hl := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) (fun a => ‖a.1.1‖) (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperDatum_integrable_norm M hM Q) l
  apply ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))).add (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q))) |>.mono'
    (measurable_datumRoot T U V x m j f k l).aestronglyMeasurable
  exact ae_of_all _ (fun z => datumRoot_norm_bound T U V x m hm j f k l z.1 z.2 hf)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperCountMean_bound_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (f : FinitePath Ω n → ℝ)
    (k l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |upperCountMean M T Q U V x m j f k l|≤B+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*(k+l) := by
  let g := fun a : UpperDatum p N R => ‖a.1.1‖
  have hg := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperDatum_integrable_norm (N := N) M hM Q
  have hk := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) g hg k
  have hl := integrable_rootArray_sum (upperDatumLaw (N := N) M Q) g hg l
  have hB := ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))).add (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q)))
  unfold upperCountMean
  rw [← integral_prod _ (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x m hm j f k l hf)]
  apply (abs_integral_le_integral_abs).trans
  apply (integral_mono (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x m hm j f k l hf).abs hB
    (fun z => datumRoot_norm_bound T U V x m hm j f k l z.1 z.2 hf)).trans_eq
  change (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      (B + ∑ a, g (rootArray k z.1 a)) + ∑ a, g (rootArray l z.2 a)
      ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) = _
  have he1 := integral_add ((integrable_const B).add (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))) (hl.comp_snd (rootLaw k (fun _ => upperDatumLaw (N := N) M Q)))
  have he2 := integral_add (integrable_const B) (hk.comp_fst (rootLaw l (fun _ => upperDatumLaw (N := N) M Q)))
  simp only [Pi.add_apply] at he1 he2
  rw [he1,he2]
  have hek : (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      ∑ a,g (rootArray k z.1 a) ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod
        (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) =
      ∫ z : RootPath (UpperDatum p N R) k,∑ a,g (rootArray k z a) ∂rootLaw k (fun _ => upperDatumLaw (N := N) M Q) :=
    by simpa only [probReal_univ,one_smul] using (integral_fun_fst (μ := rootLaw k (fun _ => upperDatumLaw (N := N) M Q)) (ν := rootLaw l (fun _ => upperDatumLaw (N := N) M Q)) (fun z => ∑ a,g (rootArray k z a)))
  have hel : (∫ z : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l,
      ∑ a,g (rootArray l z.2 a) ∂(rootLaw k (fun _ => upperDatumLaw (N := N) M Q)).prod
        (rootLaw l (fun _ => upperDatumLaw (N := N) M Q))) =
      ∫ z : RootPath (UpperDatum p N R) l,∑ a,g (rootArray l z a) ∂rootLaw l (fun _ => upperDatumLaw (N := N) M Q) :=
    by simpa only [probReal_univ,one_smul] using (integral_fun_snd (μ := rootLaw k (fun _ => upperDatumLaw (N := N) M Q)) (ν := rootLaw l (fun _ => upperDatumLaw (N := N) M Q)) (fun z => ∑ a,g (rootArray l z a)))
  rw [hek,hel,integral_rootArray_sum _ g hg k,integral_rootArray_sum _ g hg l]
  have he : (∫ a,g a ∂upperDatumLaw (N := N) M Q)=∫ a,‖a.1‖ ∂M.disorder.toMeasure := by
    simpa only [g,upperDatumLaw,probReal_univ,one_smul] using (integral_fun_fst (μ := M.disorder.toMeasure) (ν := ((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)))).asProbability id).toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) (fun a : InteractionSample p => ‖a.1‖))
  rw [he]
  simp only [integral_const,probReal_univ,one_smul]
  ring

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperCountMean_replacement_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k l : ℕ)
    :
    upperCountMean M T Q U V x (fun d => m d.succ) j f (k+1) l+
      ((p-1:ℕ):ℝ)*upperCountMean M T Q U V x (fun d => m d.succ) j f k l ≤
      (p:ℝ)*upperCountMean M T Q U V x (fun d => m d.succ) j f k (l+1)-
      ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) := by
  let D := upperDatumLaw (N := N) M Q
  let μ := rootLaw k (fun _ => D)
  let ν := rootLaw l (fun _ => D)
  let F := fun zw : RootPath (UpperDatum p N R) k × RootPath (UpperDatum p N R) l =>
    datumRoot T U V x (fun d => m d.succ) j f k l zw.1 zw.2
  let G := fun azw : (UpperDatum p N R × RootPath (UpperDatum p N R) k) × RootPath (UpperDatum p N R) l =>
    datumRoot T U V x (fun d => m d.succ) j f (k+1) l azw.1 azw.2
  let H := fun zaw : RootPath (UpperDatum p N R) k × (UpperDatum p N R × RootPath (UpperDatum p N R) l) =>
    datumRoot T U V x (fun d => m d.succ) j f k (l+1) zaw.1 zaw.2
  have hF : Integrable F (μ.prod ν) :=
    FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x _ hstrict j f k l (fun y => norm_le_pi_norm f y)
  have hG : Integrable G ((D.prod μ).prod ν) :=
    FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x _ hstrict j f (k+1) l (fun y => norm_le_pi_norm f y)
  have hH : Integrable H (μ.prod (D.prod ν)) :=
    FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_integrable_firstMoment M hM Q T U V x _ hstrict j f k (l+1) (fun y => norm_le_pi_norm f y)
  have ig := integrable_triple_rotate D μ ν G hG
  have ih := integrable_triple_middle_swap μ D ν H hH
  let e := ((p-1:ℕ):ℝ)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure)
  have hg := integral_mono (ig.add (hF.const_mul ((p-1:ℕ):ℝ))) ((ih.const_mul p).sub (integrable_const e))
    (fun zw => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.datumRoot_conditional_replacement_firstMoment_sat M hM T Q U V x m hm hpos hstrict hroot hend j f k l zw.1 zw.2)
  simp only [Pi.add_apply,Pi.sub_apply] at hg
  rw [integral_add ig (hF.const_mul _),integral_sub (ih.const_mul _) (integrable_const e),
    integral_const_mul,integral_const_mul] at hg
  have he : ∫ _zw,e ∂μ.prod ν=e := by
    have := rootLawProbability k (fun _ => D)
    have := rootLawProbability l (fun _ => D)
    simp
  rw [he,integral_prod _ ig,integral_prod _ ih,integral_prod _ hF,
    ← integral_triple_rotate D μ ν G hG,← integral_triple_middle_swap μ D ν H hH] at hg
  exact hg

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperPoissonCount_bound_firstMoment (M : Model p) (hM : InterpolationAdmissible M)
    (T : KernelTower Ω n) (Q : FiniteLaw R) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin (n+1) → ℝ) (hm : Monotone m) (hpos : ∀ d,0 ≤ m d)
    (hstrict : ∀ d : Fin n,0 < m d.succ) (hroot : m 0=0) (hend : m (Fin.last n)=1)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (r : ℝ≥0)
    :
    (∫ k,upperCountMean M T Q U V x (fun d => m d.succ) j f k 0 ∂poissonMeasure (r/p))+
      (r:ℝ)*(((p-1:ℕ):ℝ)/p)*(∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure) ≤
    ∫ l,upperCountMean M T Q U V x (fun d => m d.succ) j f 0 l ∂poissonMeasure r := by
  have hp : 0 < p := by have := hM.arity; omega
  let : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have hpR : (p:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hp
  let e := ∫ a,edgeRoot Q U x (fun d => m d.succ) a ∂M.disorder.toMeasure
  have hh := poisson_count_replacement r p
    (upperCountMean M T Q U V x (fun d => m d.succ) j f)
    ((((p-1:ℕ):ℝ)/p)*e) (show 0 ≤ ∫ a : InteractionSample p, ‖a.1‖ ∂M.disorder.toMeasure from
      integral_nonneg (fun a => norm_nonneg a.1))
    (fun k l => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_bound_firstMoment M hM T Q U V x _ hstrict j f k l
      (fun y => norm_le_pi_norm f y))
    (fun k l => ?_)
  · simpa only [mul_assoc] using hh
  · have h := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_replacement_firstMoment M hM T Q U V x m hm hpos hstrict hroot hend j f k l
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [e]
    field_simp

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperCountMean_real_firstMoment (M : Model p) (hM : InterpolationAdmissible M) (T : KernelTower Ω n) (Q : FiniteLaw R)
    (U : R → KernelTower Λ n) (V : FinitePath Ω n → Fin N → Spin)
    (x : R → FinitePath Λ n → ℝ) (m : Fin n → ℝ) (hm : ∀ d,0 < m d)
    (j : Fin p) (f : FinitePath Ω n → ℝ) (k : ℕ) :
    upperCountMean M T Q U V x m j f k 0 =
      ∫ z : Fin k → InteractionSample p,
       (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
        (fun i => backwardLog n T m (fun y => f y+∑ a,(z a).1 (fun b => V y (i a b))))
          ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  let F : RootPath (InteractionSample p × (Fin p → Fin N)) k → ℝ := fun z =>
    backwardLog n T m (fun y => f y+∑ a,(rootArray k z a).1.1 (fun b => V y ((rootArray k z a).2 b)))
  have hFm : Measurable F := by
    apply measurable_backwardLog
    intro y
    apply measurable_const.add
    apply Finset.measurable_sum
    intro a _
    exact (measurable_pi_apply (V y)).comp ((PhysicalRoot.measurable_indexedPotential (fun x : InteractionSample p => x)
      (fun σ => (measurable_pi_apply σ).comp measurable_fst)).comp (measurable_rootArray k a))
  have he : upperCountMean M T Q U V x m j f k 0 =
      ∫ z,F (rootMap (fun a : UpperDatum p N R => (a.1,a.2.1)) k z)
        ∂rootLaw k (fun _ => upperDatumLaw M Q) := by
    let : IsProbabilityMeasure (rootLaw 0 (fun _ : Fin 0 => upperDatumLaw (N := N) M Q)) := Measure.dirac.isProbabilityMeasure
    unfold upperCountMean
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [datumRoot,cavityRoot,cavityTower,cavityEnergy,realCountEnergy,
      rootArray_rootMap,F]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    rfl
  rw [he,integral_rootMap (upperDatum_real_projection M Q) k F hFm]
  apply integral_root_prod_finite_integrable M.disorder.toMeasure k
    (fun z : (Fin k → InteractionSample p) × (Fin k → Fin p → Fin N) => backwardLog n T m (fun y => f y+∑ a,(z.1 a).1 (fun b => V y (z.2 a b))))
  · apply measurable_from_prod_countable_left
    intro i
    apply measurable_backwardLog
    intro y
    change Measurable (fun z : Fin k → InteractionSample p => f y+∑ a,(z a).1 (fun b => V y (i a b)))
    exact measurable_const.add (Finset.measurable_sum _ (fun a _ =>
      (measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply a))))
  · apply ((integrable_const ‖f‖).add ((integrable_finsetSum Finset.univ
        (fun (a : Fin k) _ => integrable_comp_eval (μ := fun _ : Fin k => M.disorder.toMeasure) (i := a)
          hM.interaction_integrable)).comp_fst (Measure.pi (fun _ : Fin k => finiteUniform (Fin p → Fin N))))).mono'
    · apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_left
      intro i
      apply measurable_backwardLog
      intro y
      change Measurable (fun z : Fin k → InteractionSample p => f y+∑ a,(z a).1 (fun b => V y (i a b)))
      exact measurable_const.add (Finset.measurable_sum _ (fun a _ =>
        (measurable_pi_apply _).comp (measurable_fst.comp (measurable_pi_apply a))))
    · exact ae_of_all _ (fun z => backwardLog_bound n T m hm (fun y =>
        (abs_add_le _ _).trans (add_le_add (norm_le_pi_norm f y)
          ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum (fun a _ => norm_le_pi_norm (z.1 a).1 _))))))

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperCountMean_real_terminal (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (r : ℕ) (U : R → KernelTower Λ (r+1)) (x : R → FinitePath Λ (r+1) → ℝ)
    (m : Fin (r+1) → ℝ) (hm : ∀ d,0 < m d) (hend : m (Fin.last r)=1)
    (j : Fin p) (h : Fin N → ℝ) (k : ℕ) :
    upperCountMean M (KernelTower.pi (r+1) (fun _ : Fin N =>
      terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)) Q U
      (fun y s => terminalState r (FinitePath.proj (r+1) y s)) x m j
      (fun y => ∑ s,h s*spin (terminalState r (FinitePath.proj (r+1) y s))) k 0=
      ∫ z : Fin k → InteractionSample p,
        (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
          (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  rw [FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_real_firstMoment M hM]
  · apply integral_congr_ae
    filter_upwards [] with z
    apply FiniteLaw.expect_congr
    intro i
    rw [backwardLog_pi_terminal (fun _ : Fin N => false)
      (fun _ => (FiniteLaw.uniform : FiniteLaw Spin)) r m (fun d => (hm d).ne')
      (fun σ => (∑ s,h s*spin (σ s))+∑ a,(z a).1 (fun b => σ (i a b))),hend,FiniteLaw.pi_uniform,
      FiniteLaw.logMean_uniform]
    unfold logPartition
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro σ _
      congr 1
      unfold logWeight
      ring
    · simp [Real.log_pow]
  · exact hm

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma activeCountMean_site (q : ℕ) (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin (r+1) → ℝ)
    (hm : ∀ d,0 < m d) (hend : m (Fin.last r)=1) (k : ℕ) (h : ℝ) :
    activeCountMean M Q (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
      (fun b => pad a r (U b)) (terminalState r)
      (fun b y => x b (pathPrefix r y)) m (Fin.last q)
      (fun y => h*spin (terminalState r y)) k=
    ∫ z : Fin k → InteractionSample (q+1),
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog z h)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) := by
  let F := fun z : RootPath (InteractionSample (q+1)) k × RootPath (Fin (q+1) → R) k =>
    backwardLog (r+1)
      (cavityTower (terminalTower false (FiniteLaw.uniform : FiniteLaw Spin) r)
        (fun b => pad a r (U b)) k z.2) m
      (activeEnergy (terminalState r) (fun b y => x b (pathPrefix r y)) (Fin.last q) k z.2 z.1
        (fun y => h*spin (terminalState r y)))
  have hFm : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    exact measurable_backwardLog (r+1) _ m (measurable_activeEnergy (terminalState r)
      (fun b y => x b (pathPrefix r y)) (Fin.last q) k b id measurable_id
      (fun y => h*spin (terminalState r y)))
  have hB (z : RootPath (InteractionSample (q+1)) k × RootPath (Fin (q+1) → R) k) :
      |F z|≤|h|+∑ i,‖(rootArray k z.1 i).1‖ := by
    apply backwardLog_bound _ _ _ hm
    intro y
    apply activeEnergy_bound _ _ _ _ _ _ _ _ y
    intro y
    simp only [abs_mul,abs_spin,mul_one]
    exact le_refl _
  have hi : Integrable F ((rootLaw k (fun _ => M.disorder.toMeasure)).prod
      (rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))) := by
    exact ((integrable_const |h|).add ((integrable_rootArray_sum M.disorder.toMeasure
      (fun a => ‖a.1‖) hM.interaction_integrable k).comp_fst _)).mono'
        hFm.aestronglyMeasurable (ae_of_all _ hB)
  unfold activeCountMean activeDatumRoot
  change (∫ z,F (rootMap Prod.fst k z,rootMap Prod.snd k z) ∂rootLaw k (fun _ => _))=_
  rw [integral_rootSplit _ _ k F hFm hi]
  have he (z : RootPath (InteractionSample (q+1)) k) :
      (∫ b,F (z,b) ∂rootLaw k (fun _ => ((FiniteLaw.pi (fun _ : Fin (q+1) => Q)).asProbability id).toMeasure))=
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog (rootArray k z) h) :=
    activeRoot_site_mean a r Q U x m hend q k z h
  simp only [he]
  exact integral_rootArray_eq_pi M.disorder.toMeasure k
    (fun z : Fin k → InteractionSample (q+1) =>
      trialLog r (finiteTrialLaw r Q U x) (fun d => m d.castSucc) (siteLog z h))

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma finiteTrial_upper_fixedField_sat_oai (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) (h : Fin N → ℝ) :
    (∫ k,∫ z : Fin k → InteractionSample (q+1),
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (q+1) → Fin N)).expect
        (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*N))+
      (M.alpha:ℝ)*N*q*(∫ z,trialLog r (finiteTrialLaw r Q U x) m
        (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure) ≤
      ∑ s : Fin N,∫ k,∫ z : Fin k → InteractionSample (q+1),
        trialLog r (finiteTrialLaw r Q U x) m (siteLog z (h s))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*(q+1)) := by
  let m' : Fin (r+1) → ℝ := Fin.snoc m 1
  let m₀ : Fin (r+2) → ℝ := Fin.cons 0 m'
  have hpos : ∀ d,0 < m' d := snoc_exponents_pos hm
  have hend : m' (Fin.last r)=1 := Fin.snoc_last _ _
  have hend₀ : m₀ (Fin.last (r+1))=1 := by
    change Fin.cons (α := fun _ => ℝ) 0 m' (Fin.last r).succ=1
    simpa only [Fin.cons_succ] using hend
  let T : Fin N → KernelTower Spin (r+1) := fun _ => terminalTower false FiniteLaw.uniform r
  let V : Fin N → FinitePath Spin (r+1) → Spin := fun _ => terminalState r
  let f : Fin N → FinitePath Spin (r+1) → ℝ := fun s y => h s*spin (terminalState r y)
  let Up : R → KernelTower Λ (r+1) := fun b => pad a r (U b)
  let xp : R → FinitePath Λ (r+1) → ℝ := fun b y => x b (pathPrefix r y)
  have hx := FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoissonCount_bound_firstMoment M hM (KernelTower.pi (r+1) T) Q Up
    (fun y s => V s (FinitePath.proj (r+1) y s)) xp m₀
    (cons_snoc_exponents_mono hm) (cons_snoc_exponents_nonneg hm)
    (fun d => hpos d) rfl hend₀ (Fin.last q)
    (fun y => ∑ s,f s (FinitePath.proj (r+1) y s)) (M.alpha*(q+1)*N)
  have hr : (M.alpha*(q+1)*N:ℝ≥0)/(q+1)=M.alpha*N := by
    have hp : (q+1:ℝ≥0)≠0 := by positivity
    field_simp
  have hs : (M.alpha*(q+1)*N:ℝ≥0)/N=M.alpha*(q+1) := by
    have hN : (N:ℝ≥0)≠0 := by exact_mod_cast NeZero.ne N
    exact mul_div_cancel_right₀ _ hN
  simp only [m₀,Fin.cons_succ,Nat.cast_add,Nat.cast_one] at hx
  change (∫ k,upperCountMean M (KernelTower.pi (r+1) T) Q Up
      (fun y s => V s (FinitePath.proj (r+1) y s)) xp m' (Fin.last q)
      (fun y => ∑ s,f s (FinitePath.proj (r+1) y s)) k 0 ∂poissonMeasure ((M.alpha*(q+1)*N)/(q+1)))+
      ((M.alpha*(q+1)*N:ℝ≥0):ℝ)*(((q+1-1:ℕ):ℝ)/(q+1))*
        (∫ z,edgeRoot Q Up xp m' z ∂M.disorder.toMeasure) ≤ _ at hx
  rw [hr,FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable_sat M hM Q T Up V xp m' hpos (Fin.last q) f,hs] at hx
  dsimp only [T,V,f,Up,xp] at hx
  simp_rw [FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_real_terminal M hM Q r _ _ m' hpos hend,
    FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.activeCountMean_site q M hM a r Q U x m' hpos hend,
    edgeRoot_pad r a Q U x m' (by rw [hend]; norm_num)] at hx
  have he : (fun d : Fin r => m' d.castSucc)=m := by funext d; exact Fin.snoc_castSucc _ _ d
  rw [he] at hx
  have hc : ((M.alpha*(q+1)*N:ℝ≥0):ℝ)*(((q+1-1:ℕ):ℝ)/(q+1))=(M.alpha:ℝ)*N*q := by
    simp only [Nat.add_sub_cancel,NNReal.coe_mul,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one]
    have hp : (q:ℝ)+1≠0 := by positivity
    field_simp
  rwa [hc] at hx

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

end

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat_oai := @OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat_oai
