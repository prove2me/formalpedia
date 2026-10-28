-- Prove2me | solution 1 for OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable_sat
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:45:32.058643+00:00
-- url     : https://prove2.me/submissions/73d5f875-b9ff-415b-857c-37be2c266f7c

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A000
import Definitions.Def_OAIQ067A001

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_FiniteProducts
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
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators

/-- Fubini at an arbitrary coordinate, retaining dependent finite sample types. -/
theorem expect_pi_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (Q : (i : ι) → FiniteLaw (α i))
    (i : ι) (H : ((i : ι) → α i) → ℝ) :
    (pi Q).expect H = (Q i).expect (fun a =>
      (pi (fun j : {j // j ≠ i} => Q j)).expect
        (fun rest => H ((Equiv.piSplitAt i α).symm (a,rest)))) := by
  classical
  have hprod (x : (i : ι) → α i) :
      (∏ j, (Q j).weight (x j)) =
        (Q i).weight (x i) * ∏ j : {j // j ≠ i}, (Q j).weight (x j) := by
    let : Fintype {j : ι // j = i} := Subtype.fintype (fun j => j = i)
    have hh := Fintype.prod_subtype_mul_prod_subtype (fun j => j = i)
      (fun j => (Q j).weight (x j))
    rw [Fintype.prod_subsingleton _ ⟨i,rfl⟩] at hh
    exact hh.symm
  simp only [expect, pi]
  rw [← (Equiv.piSplitAt i α).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [hprod]
  have hh : (∏ j : {j // j ≠ i}, (Q j).weight
      ((Equiv.piSplitAt i α).symm (a,rest) j)) =
      ∏ j : {j // j ≠ i}, (Q j).weight (rest j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [Equiv.piSplitAt_symm_apply, dite_eq_right j.property]
  rw [hh]
  simp only [Equiv.piSplitAt_symm_apply, dite_true]
  ring

end DilutedSpinGlass.FiniteLaw

namespace DilutedSpinGlass.FiniteLaw

theorem expect_pi_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (P : (i : ι) → FiniteLaw (α i))
    (i : ι) (f : α i → ℝ) : (pi P).expect (fun x => f (x i)) = (P i).expect f := by
  erw [expect_pi_split P i]
  simp! only [Equiv.piSplitAt_symm_apply, dite_true, expect_const]

end DilutedSpinGlass.FiniteLaw

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_InsertionStability
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
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
open _root_.MeasureTheory ProbabilityTheory
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_RootProductLaw
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators

lemma finiteUniform_pi {ι J : Type} [Fintype ι] [DecidableEq ι] [Fintype J] [Nonempty J]
    [MeasurableSpace J] [MeasurableSingletonClass J] :
    Measure.pi (fun _ : ι => finiteUniform J) = finiteUniform (ι → J) := by
  classical
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton,finiteUniform,PMF.uniformOfFintype_apply,ENNReal.inv_pow]

end DilutedSpinGlass

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
open _root_.MeasureTheory ProbabilityTheory
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

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_InsertionPoint
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.FiniteLaw
open scoped BigOperators
variable {ι α β : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]

lemma expect_pi_bind (P : ι → FiniteLaw α) (Q : ι → α → FiniteLaw β)
    (f : (ι → α×β) → ℝ) :
    (pi (fun i => (P i).bind (Q i))).expect f =
      (pi P).expect (fun a => (pi (fun i => Q i (a i))).expect (fun b => f (fun i => (a i,b i)))) := by
  classical
  let e : (ι → α×β) ≃ (ι → α)×(ι → β) :=
    ⟨fun x => (fun i => (x i).1,fun i => (x i).2),fun x i => (x.1 i,x.2 i),
      fun x => rfl,fun x => rfl⟩
  unfold expect
  rw [show (∑ x, (pi (fun i => (P i).bind (Q i))).weight x*f x)=
      ∑ x : (ι → α)×(ι → β),(∏ i,(P i).weight (x.1 i))*(∏ i,(Q i (x.1 i)).weight (x.2 i))*f (fun i => (x.1 i,x.2 i)) from
    Fintype.sum_equiv e _ _ (fun x => by
      simp only [e,Equiv.coe_fn_mk,pi,bind,Finset.prod_mul_distrib])]
  simp only [Fintype.sum_prod_type,pi,Finset.mul_sum,mul_assoc]

end DilutedSpinGlass.FiniteLaw

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_TowerSum
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : ι → Type} [∀ i,Fintype (A i)]
lemma logMean_pi_sum (Q : (i : ι) → FiniteLaw (A i)) (m : ℝ)
    (f : (i : ι) → A i → ℝ) :
    (pi Q).logMean m (fun x => ∑ i,f i (x i))=∑ i,(Q i).logMean m (f i) := by
  classical
  unfold logMean expMoment
  simp_rw [Finset.mul_sum,Real.exp_sum]
  rw [expect_pi_product Q (fun i x => Real.exp (m*f i x)),Real.log_prod]
  · simp only [Finset.sum_div]
  · intro i _
    exact (expMoment_pos (Q i) m (f i)).ne'
end FiniteLaw

namespace KernelTower
variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [Fintype A]
lemma backwardLog_pi_sum (n : ℕ) (T : (i : ι) → KernelTower A n)
    (m : Fin n → ℝ) (f : (i : ι) → FinitePath A n → ℝ) :
    backwardLog n (pi n T) m (fun y => ∑ i,f i (FinitePath.proj n y i))=
      ∑ i,backwardLog n (T i) m (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ι → FiniteLaw A × (A → KernelTower A n) at T
    change ι → A × FinitePath A n → ℝ at f
    change (FiniteLaw.pi (fun i => (T i).1)).logMean (m 0)
      (fun x => backwardLog n (pi n (fun i => (T i).2 (x i))) (fun j => m j.succ)
        (fun y => ∑ i,f i (x i,FinitePath.proj n y i))) =
      ∑ i,(T i).1.logMean (m 0) (fun a => backwardLog n ((T i).2 a) (fun j => m j.succ) (fun y => f i (a,y)))
    have he : (fun x : ι → A => backwardLog n (pi n (fun i => (T i).2 (x i))) (fun j => m j.succ)
        (fun y => ∑ i,f i (x i,FinitePath.proj n y i))) =
      (fun x => ∑ i,backwardLog n ((T i).2 (x i)) (fun j => m j.succ) (fun y => f i (x i,y))) := by
      funext x
      exact ih (fun i => (T i).2 (x i)) (fun j => m j.succ) (fun i y => f i (x i,y))
    rw [he]
    exact FiniteLaw.logMean_pi_sum (fun i => (T i).1) (m 0)
      (fun i x => backwardLog n ((T i).2 x) (fun j => m j.succ) (fun y => f i (x,y)))
end KernelTower
end DilutedSpinGlass

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

lemma pi_prod_projects {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (T : ι → KernelTower Ω n) (U : ι → KernelTower Λ n) (c : ι) :
    Projects (fun z : ι → Ω×Λ => (fun i => (z i).1,(z c).2)) n
      (pi n (fun i => prod n (T i) (U i))) (prod n (pi n T) (U c)) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (fun i => (T i).2 (a i).1) (fun i => (U i).2 (a i).2)⟩
    intro f
    change (FiniteLaw.pi (fun i => (T i).1.bind (fun _ => (U i).1))).expect
      (fun z => f (fun i => (z i).1,(z c).2)) =
      ((FiniteLaw.pi (fun i => (T i).1)).bind (fun _ => (U c).1)).expect f
    rw [FiniteLaw.expect_pi_bind]
    rw [FiniteLaw.expect_bind]
    apply FiniteLaw.expect_congr
    intro a
    exact FiniteLaw.expect_pi_marginal (fun i => (U i).1) c (fun b => f (a,b))

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
open _root_.MeasureTheory Filter
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
open _root_.MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

lemma abs_integral_le_bound_ae {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] {f : X → ℝ} {B : ℝ}
    (h : ∀ᵐ x ∂μ, |f x|≤B) : |∫ x,f x ∂μ|≤B := by
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := B)
      (h.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx))

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open scoped BigOperators

lemma mixedSpinLaw_single {p : ℕ} (j : Fin p) (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedSpinLaw (fun a => decide (a=j)) s x=
      mixedSpinLaw (fun a => decide (a=j)) (fun _ => s j) x := by
  unfold mixedSpinLaw
  congr 1
  funext a
  by_cases h : a=j
  · subst a; rfl
  · simp [h]

lemma mixedEnergy_single {p : ℕ} (z : InteractionSample p) (j : Fin p)
    (s : Fin p → Spin) (x : Fin p → ℝ) :
    mixedEnergy z (fun a => decide (a=j)) s x=
      mixedEnergy z (fun a => decide (a=j)) (fun _ => s j) x := by
  unfold mixedEnergy
  rw [mixedSpinLaw_single]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperCountState
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
open scoped BigOperators

variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] in
lemma pathMap_id (n : ℕ) (y : FinitePath Ω n) : pathMap id n y=y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityAllocation
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {ι Ω Λ R : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

omit [Fintype R] in
lemma cavityJoin_projects (T : ι → KernelTower Ω n) (U : R → KernelTower Λ n)
    (l : ℕ) (r : RootPath (Fin p → R) l) (c : RootPath ι l) :
    KernelTower.Projects (cavityJoin l c) n
      (KernelTower.pi n (fun i => cavityTower (T i) U l r))
      (cavityTower (KernelTower.pi n T) U l r) := by
  induction l with
  | zero => exact KernelTower.Projects.refl n _
  | succ l ih =>
    have h := KernelTower.pi_prod_projects n (fun i => cavityTower (T i) U l r.2)
      (fun _ : ι => piTower n (fun j => U (r.1 j))) c.1
    have g := KernelTower.Projects.prod n (ih r.2 c.2)
      (KernelTower.Projects.refl n (piTower n (fun j => U (r.1 j))))
    exact KernelTower.Projects.comp n h g

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma pathFst_cavityJoin (l : ℕ) (c : RootPath ι (l+1))
    (y : FinitePath (ι → CavityState Ω Λ p (l+1)) n) :
    pathFst n (pathMap (cavityJoin (Ω := Ω) (Λ := Λ) (p := p) (l+1) c) n y)=
      pathMap (cavityJoin l c.2) n (pathMap (fun a i => (a i).1) n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma pathSnd_cavityJoin (l : ℕ) (c : RootPath ι (l+1))
    (y : FinitePath (ι → CavityState Ω Λ p (l+1)) n) :
    pathSnd n (pathMap (cavityJoin (Ω := Ω) (Λ := Λ) (p := p) (l+1) c) n y)=
      pathSnd n (FinitePath.proj n y c.1) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] [Fintype Λ] in
lemma cavityProject_join (l : ℕ) (c : RootPath ι l)
    (a : ι → CavityState Ω Λ p l) (i : ι) :
    cavityProject l (cavityJoin l c a) i=cavityProject l (a i) := by
  induction l with
  | zero => rfl
  | succ l ih => exact ih c.2 (fun i => (a i).1)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_UpperDatum
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
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
open _root_.MeasureTheory
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
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavitySeparable
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
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] [NeZero N] in
lemma path_proj_fst (l : ℕ)
    (y : FinitePath (Fin N → CavityState Ω Λ p (l+1)) n) (i : Fin N) :
    FinitePath.proj n (pathMap (fun a s => (a s).1) n y) i=
      pathFst n (FinitePath.proj n y i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [NeZero N] in
lemma path_proj_join (l : ℕ) (c : RootPath (Fin N) l)
    (y : FinitePath (Fin N → CavityState Ω Λ p l) n) (i : Fin N) :
    FinitePath.proj n (pathMap (cavityProject l) n (pathMap (cavityJoin l c) n y)) i=
      pathMap (cavityProject l) n (FinitePath.proj n y i) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_join l c y.1 i) (ih y.2)

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma cavityEnergy_join (V : Fin N → FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (l : ℕ) (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : Fin N → FinitePath Ω n → ℝ)
    (y : FinitePath (Fin N → CavityState Ω Λ p l) n) :
    cavityEnergy (fun y s => V s (FinitePath.proj n y s)) x j l r i z
      (fun y => ∑ s,f s (FinitePath.proj n y s))
      (pathMap (cavityJoin l (rootMap (fun a => a j) l i)) n y)=
      ∑ s,allocatedEnergy (V s) x j s l r (rootMap (fun a => a j) l i) z (f s)
        (FinitePath.proj n y s) := by
  induction l with
  | zero =>
    change (∑ s,f s (FinitePath.proj n (pathMap id n y) s))=∑ s,f s (FinitePath.proj n y s)
    rw [pathMap_id]
  | succ l ih =>
    simp only [cavityEnergy,allocatedEnergy,rootMap,pathFst_cavityJoin]
    rw [ih]
    simp only [path_proj_fst,Finset.sum_add_distrib]
    congr 1
    unfold mixedTreeEnergy
    rw [mixedEnergy_single]
    simp only [pathFst_cavityJoin,pathSnd_cavityJoin,path_proj_join,path_proj_fst]
    simp only [singleBlockEnergy]
    rw [Finset.sum_eq_single (i.1 j)]
    · simp only [ite_true]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

omit [Fintype R] [NeZero N] in
lemma cavityRoot_separable (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (l : ℕ)
    (r : RootPath (Fin p → R) l) (i : RootPath (Fin p → Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : Fin N → FinitePath Ω n → ℝ) :
    cavityRoot (KernelTower.pi n T) U (fun y s => V s (FinitePath.proj n y s)) x m j l r i z
      (fun y => ∑ s,f s (FinitePath.proj n y s))=
      ∑ s,backwardLog n (cavityTower (T s) U l r) m
        (allocatedEnergy (V s) x j s l r (rootMap (fun a => a j) l i) z (f s)) := by
  unfold cavityRoot
  rw [← backwardLog_of_projects n (cavityJoin_projects T U l r (rootMap (fun a => a j) l i))]
  simp_rw [cavityEnergy_join]
  exact backwardLog_pi_sum _ _ _ _

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_EnergyInsertionMean
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory

lemma measurePreserving_selectRoot {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (l : ℕ) (b : RootPath Bool l) :
    MeasurePreserving (selectRoot (X := X) l b) (rootLaw l (fun _ => μ))
      (rootLaw (selectedCount l b) (fun _ => μ)) := by
  induction l with
  | zero => exact MeasurePreserving.id _
  | succ l ih =>
    cases b with | mk a b =>
      cases a
      · change MeasurePreserving (fun z : X×RootPath X l => selectRoot l b z.2)
          (μ.prod (rootLaw l (fun _ => μ))) (rootLaw (selectedCount l b) (fun _ => μ))
        exact (ih b).comp (measurePreserving_snd (μ := μ) (ν := rootLaw l (fun _ => μ)))
      · change MeasurePreserving (fun z : X×RootPath X l => (z.1,selectRoot l b z.2))
          (μ.prod (rootLaw l (fun _ => μ))) (μ.prod (rootLaw (selectedCount l b) (fun _ => μ)))
        exact (MeasurePreserving.id μ).prod (ih b)

lemma integral_selectRoot {X : Type} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (l : ℕ) (b : RootPath Bool l)
    (F : RootPath X (selectedCount l b) → ℝ) (hF : Measurable F) :
    (∫ z,F (selectRoot l b z) ∂rootLaw l (fun _ => μ))=
      ∫ z,F z ∂rootLaw (selectedCount l b) (fun _ => μ) := by
  have h := measurePreserving_selectRoot μ l b
  rw [← h.map_eq,integral_map h.measurable.aemeasurable hF.aestronglyMeasurable]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_FullRootIncrement
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.KernelTower
variable {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
lemma Projects.prod_fst (n : ℕ) (T : KernelTower Ω n) (U : KernelTower Λ n) :
    Projects Prod.fst n (KernelTower.prod n T U) T := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨?_,fun a => ih (T.2 a.1) (U.2 a.2)⟩
    intro f
    change (T.1.bind (fun _ => U.1)).expect (fun z => f z.1)=T.1.expect f
    simp only [FiniteLaw.expect_bind,FiniteLaw.expect_const]

end DilutedSpinGlass.KernelTower

namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p : ℕ}

omit [Fintype R] in
lemma selectCavity_projects (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (l : ℕ) (b : RootPath Bool l) (r : RootPath (Fin p → R) l) :
    Projects (selectCavity (Ω := Ω) (Λ := Λ) (p := p) l b) n
      (cavityTower T U l r) (cavityTower T U (selectedCount l b) (selectRoot l b r)) := by
  induction l with
  | zero => exact Projects.refl n T
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v
    · change Projects (fun z : CavityState Ω Λ p l × (Fin p → Λ) => selectCavity l b z.1) n
        (KernelTower.prod n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j))))
        (cavityTower T U (selectedCount l b) (selectRoot l b r.2))
      exact Projects.comp n (Projects.prod_fst n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j)))) (ih b r.2)
    · change Projects (fun z : CavityState Ω Λ p l × (Fin p → Λ) => (selectCavity l b z.1,id z.2)) n
        (KernelTower.prod n (cavityTower T U l r.2) (piTower n (fun j => U (r.1 j))))
        (KernelTower.prod n (cavityTower T U (selectedCount l b) (selectRoot l b r.2)) (piTower n (fun j => U (r.1 j))))
      exact Projects.prod n (ih b r.2) (Projects.refl n (piTower n (fun j => U (r.1 j))))

omit [Fintype Ω] [Fintype Λ] in
lemma cavityProject_select (l : ℕ) (b : RootPath Bool l) (a : CavityState Ω Λ p l) :
    cavityProject (selectedCount l b) (selectCavity l b a)=cavityProject l a := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v <;> simpa only [selectCavity,selectedCount,Bool.false_eq_true,↓reduceDIte,↓reduceIte,cavityProject] using ih b a.1

omit [Fintype Ω] [Fintype Λ] in
lemma cavityProject_pathSelect (l : ℕ) (b : RootPath Bool l) (y : FinitePath (CavityState Ω Λ p l) n) :
    pathMap (cavityProject (selectedCount l b)) n (pathMap (selectCavity l b) n y)=
      pathMap (cavityProject l) n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext (cavityProject_select l b y.1) (ih y.2)

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityMaskEnergy
attribute [-instance] _root_.OAI.DilutedSpinGlass.PrescribedTree.upperDatumLaw_probability _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open KernelTower
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R] {n p N : ℕ} [NeZero N]

omit [Fintype Ω] [Fintype Λ] in
lemma pathFst_select_true (l : ℕ) (b : RootPath Bool l)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathFst n (pathMap (selectCavity (l+1) (true,b)) n y)=
      pathMap (selectCavity l b) n (pathFst n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma pathSnd_select_true (l : ℕ) (b : RootPath Bool l)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathSnd n (pathMap (selectCavity (l+1) (true,b)) n y)=pathSnd n y := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] in
lemma path_select_false (l : ℕ) (b : RootPath Bool l)
    (y : FinitePath (CavityState Ω Λ p (l+1)) n) :
    pathMap (selectCavity (l+1) (false,b)) n y=
      pathMap (selectCavity l b) n (pathFst n y) := by
  induction n with
  | zero => rfl
  | succ n ih => exact Prod.ext rfl (ih y.2)

omit [Fintype Ω] [Fintype Λ] [Fintype R] in
lemma activeEnergy_select (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (l : ℕ)
    (b : RootPath Bool l) (r : RootPath (Fin p → R) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (CavityState Ω Λ p l) n) :
    activeEnergy V x j (selectedCount l b) (selectRoot l b r) (selectRoot l b z) f
      (pathMap (selectCavity l b) n y)=maskedEnergy V x j l b r z f y := by
  induction l with
  | zero => exact congrArg f (pathMap_id n (show FinitePath Ω n from y))
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v
    · change activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f
        (pathMap (selectCavity (l+1) (false,b)) n y)=maskedEnergy V x j l b r.2 z.2 f (pathFst n y)+0
      exact (congrArg (activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f)
        (path_select_false l b y)).trans ((ih b r.2 z.2 (pathFst n y)).trans (add_zero _).symm)
    · change activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f
          (pathFst n (pathMap (selectCavity (l+1) (true,b)) n y))+
        singleBlockEnergy V x j (selectedCount l b) r.1 z.1 (pathMap (selectCavity (l+1) (true,b)) n y)=
        maskedEnergy V x j l b r.2 z.2 f (pathFst n y)+singleBlockEnergy V x j l r.1 z.1 y
      apply congrArg₂ (fun a b : ℝ => a+b)
      · exact (congrArg (activeEnergy V x j (selectedCount l b) (selectRoot l b r.2) (selectRoot l b z.2) f)
          (pathFst_select_true l b y)).trans (ih b r.2 z.2 (pathFst n y))
      · unfold singleBlockEnergy
        have hfst := pathFst_select_true l b y
        have hsnd := pathSnd_select_true l b y
        have hpjs := cavityProject_pathSelect l b (pathFst n y)
        apply congrArg₂ (mixedEnergy z.1 (fun a => decide (a=j)))
        · funext a
          exact congrArg V ((congrArg (pathMap (cavityProject (selectedCount l b)) n) hfst).trans hpjs)
        · funext a
          exact congrArg (fun w => x (r.1 a) (pathMap (fun b : Fin p → Λ => b a) n w)) hsnd

omit [Fintype Ω] [Fintype Λ] [Fintype R] [NeZero N] in
lemma allocatedEnergy_mask (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (s : Fin N) (l : ℕ)
    (r : RootPath (Fin p → R) l) (c : RootPath (Fin N) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) (y : FinitePath (CavityState Ω Λ p l) n) :
    allocatedEnergy V x j s l r c z f y=
      maskedEnergy V x j l (rootMap (fun a => decide (a=s)) l c) r z f y := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [allocatedEnergy,maskedEnergy,rootMap,decide_eq_true_eq,ih]

omit [Fintype R] [NeZero N] in
lemma allocatedRoot_selected (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ) (j : Fin p)
    (m : Fin n → ℝ) (s : Fin N) (l : ℕ)
    (r : RootPath (Fin p → R) l) (c : RootPath (Fin N) l) (z : RootPath (InteractionSample p) l)
    (f : FinitePath Ω n → ℝ) :
    backwardLog n (cavityTower T U l r) m (allocatedEnergy V x j s l r c z f)=
      backwardLog n (cavityTower T U (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        (selectRoot l (rootMap (fun a => decide (a=s)) l c) r)) m
        (activeEnergy V x j (selectedCount l (rootMap (fun a => decide (a=s)) l c))
          (selectRoot l (rootMap (fun a => decide (a=s)) l c) r)
          (selectRoot l (rootMap (fun a => decide (a=s)) l c) z) f) := by
  rw [← backwardLog_of_projects n (selectCavity_projects T U l (rootMap (fun a => decide (a=s)) l c) r)]
  congr 1
  funext y
  rw [activeEnergy_select,allocatedEnergy_mask]

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
open _root_.MeasureTheory KernelTower
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
open _root_.MeasureTheory
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
open _root_.MeasureTheory
lemma rootMap_selectRoot {X Y : Type} (f : X → Y) (l : ℕ) (b : RootPath Bool l) (z : RootPath X l) :
    rootMap f (selectedCount l b) (selectRoot l b z)=selectRoot l b (rootMap f l z) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    rcases b with ⟨v,b⟩
    cases v
    · exact ih b z.2
    · exact Prod.ext rfl (ih b z.2)

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

lemma measurable_activeDatumRoot [MeasurableSpace R] [MeasurableSingletonClass R]
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Measurable (activeDatumRoot T U V x m j f l) := by
  let F := fun z : RootPath (InteractionSample p) l × RootPath (Fin p → R) l =>
    backwardLog n (cavityTower T U l z.2) m (activeEnergy V x j l z.2 z.1 f)
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro b
    dsimp only [F]
    exact measurable_backwardLog n _ m (measurable_activeEnergy V x j l b id measurable_id f)
  exact hF.comp ((measurable_rootMap Prod.fst measurable_fst l).prodMk
    (measurable_rootMap Prod.snd measurable_snd l))

omit [NeZero N] in
lemma allocatedMean_selected [MeasurableSpace R] [MeasurableSingletonClass R]
    (M : Model p) (Q : FiniteLaw R) (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (s : Fin N) (l : ℕ)
    (c : RootPath (Fin N) l) :
    (∫ z : RootPath (InteractionSample p × (Fin p → R)) l,
      backwardLog n (cavityTower T U l (rootMap Prod.snd l z)) m
        (allocatedEnergy V x j s l (rootMap Prod.snd l z) c (rootMap Prod.fst l z) f)
      ∂rootLaw l (fun _ => M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure))=
    ∫ z,activeDatumRoot T U V x m j f (selectedCount l (rootMap (fun a => decide (a=s)) l c)) z
      ∂rootLaw (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        (fun _ => M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) := by
  simp_rw [allocatedRoot_selected,←rootMap_selectRoot]
  exact integral_selectRoot _ l _ _ (measurable_activeDatumRoot T U V x m j f _)

end PrescribedTree
end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityDatumProjection
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory
lemma measurable_selectRoot {X : Type} [MeasurableSpace X] (l : ℕ) (b : RootPath Bool l) :
    Measurable (selectRoot (X := X) l b) := by
  induction l with
  | zero => exact measurable_id
  | succ l ih =>
    cases b with | mk a b =>
      cases a
      · exact (ih b).comp measurable_snd
      · exact measurable_fst.prodMk ((ih b).comp measurable_snd)
namespace PrescribedTree
open _root_.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperDatum_site_projection (M : Model p) (Q : FiniteLaw R) (j : Fin p) :
    MeasurePreserving (fun a : UpperDatum p N R => (a.2.1 j,(a.1,a.2.2)))
      (upperDatumLaw M Q) ((finiteUniform (Fin N)).prod
        (M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)) := by
  unfold upperDatumLaw
  rw [FiniteLaw.pi_uniform,FiniteLaw.uniform_asProbability,←finiteUniform_pi]
  exact ((measurePreserving_eval (fun _ : Fin p => finiteUniform (Fin N)) j).prod
    (MeasurePreserving.id _)).comp
    ((measurePreserving_prodAssoc _ _ _).comp
      (((Measure.measurePreserving_swap : MeasurePreserving Prod.swap
        (M.disorder.toMeasure.prod (Measure.pi (fun _ : Fin p => finiteUniform (Fin N))))
        ((Measure.pi (fun _ : Fin p => finiteUniform (Fin N))).prod M.disorder.toMeasure)).prod
        (MeasurePreserving.id _)).comp (MeasurePreserving.symm MeasurableEquiv.prodAssoc
          (measurePreserving_prodAssoc _ _ _))))

omit [Fintype Ω] [Fintype Λ] [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma allocatedEnergy_bound (V : FinitePath Ω n → Spin)
    (x : R → FinitePath Λ n → ℝ) (j : Fin p) (s : Fin N) (l : ℕ)
    (r : RootPath (Fin p → R) l) (c : RootPath (Fin N) l)
    (z : RootPath (InteractionSample p) l) (f : FinitePath Ω n → ℝ)
    {B : ℝ} (hf : ∀ y,|f y|≤B) (y : FinitePath (CavityState Ω Λ p l) n) :
    |allocatedEnergy V x j s l r c z f y|≤B+∑ i,‖(rootArray l z i).1‖ := by
  induction l with
  | zero => simpa [allocatedEnergy] using hf y
  | succ l ih =>
    apply (abs_add_le _ _).trans
    have he : |if c.1=s then singleBlockEnergy V x j l r.1 z.1 y else 0|≤‖z.1.1‖ := by
      split_ifs
      · exact mixedEnergy_bound _ _ _ _
      · simp
    have h := add_le_add (ih r.2 c.2 z.2 (pathFst n y)) he
    simpa only [Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ,add_assoc,add_comm,add_left_comm] using h

omit [NeZero N] in
lemma measurable_allocatedDatumRoot (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (s : Fin N) (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Measurable (fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
      allocatedDatumRoot T U V x m j s f l z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro c
  simp only [allocatedDatumRoot,allocatedRoot_selected,←rootMap_selectRoot]
  exact (measurable_activeDatumRoot T U V x m j f _).comp
    (measurable_selectRoot l (rootMap (fun a => decide (a=s)) l c))

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
open _root_.MeasureTheory
lemma rootMap_comp {X Y Z : Type} (f : X → Y) (g : Y → Z) (k : ℕ) (z : RootPath X k) :
    rootMap g k (rootMap f k z)=rootMap (g ∘ f) k z := by
  induction k with
  | zero => rfl
  | succ k ih => exact Prod.ext rfl (ih z.2)

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
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityAllocatedMean
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [Fintype R] [MeasurableSpace R] [MeasurableSingletonClass R] [NeZero N] in
lemma allocatedDatumRoot_bound (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) (c : RootPath (Fin N) l)
    (z : RootPath (InteractionSample p × (Fin p → R)) l) :
    |allocatedDatumRoot T U V x m j s f l c z|≤‖f‖+∑ a,‖(rootArray l z a).1.1‖ := by
  apply backwardLog_bound n _ m hm
  intro y
  simpa only [rootArray_rootMap] using allocatedEnergy_bound V x j s l
    (rootMap Prod.snd l z) c (rootMap Prod.fst l z) f (fun w => norm_le_pi_norm f w) y

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_CavityEndpointCount
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory KernelTower
open scoped BigOperators
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {n p N : ℕ} [NeZero N]

omit [MeasurableSingletonClass R] in
lemma upperCountMean_cavity (M : Model p) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Fin N → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (j : Fin p) (f : FinitePath Ω n → ℝ) (l : ℕ) :
    upperCountMean M T Q U V x m j f 0 l=
      ∫ z : RootPath (UpperDatum p N R) l,
        cavityRoot T U V x m j l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1) l z) (rootMap Prod.fst l z) f
        ∂rootLaw l (fun _ => upperDatumLaw M Q) := by
  unfold upperCountMean datumRoot realCountEnergy
  simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  change (∫ _ : Unit, _ ∂Measure.dirac ())=_
  simp only [integral_dirac]

end DilutedSpinGlass.PrescribedTree

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonSiteThinning
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

/-- Poisson thinning for independent uniform categorical choices. -/
lemma compoundPoisson_uniform_indicator_at (r : ℝ≥0) (p : ℕ) [NeZero p] (s : Fin p) :
    compoundPoisson r (Measure.map (fun a : Fin p => if a=s then (1:ℝ) else 0)
      (finiteUniform (Fin p))) = compoundPoisson (r/p) (Measure.dirac (1:ℝ)) := by
  classical
  haveI : IsProbabilityMeasure (Measure.map (fun a : Fin p => if a=s then (1:ℝ) else 0) (finiteUniform (Fin p))) := Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_compoundPoisson,charFunDual_compoundPoisson]
  congr 1
  rw [charFunDual_apply,integral_map (measurable_of_countable _).aemeasurable (by fun_prop),
    integral_finiteUniform,charFunDual_apply,integral_dirac]
  have hp : (p:ℂ)≠0 := by exact_mod_cast (NeZero.ne p)
  have hs : (∑ a : Fin p,Complex.exp ((L (if a=s then (1:ℝ) else 0):ℂ)*Complex.I)) =
      Complex.exp ((L 1:ℂ)*Complex.I)+(p-1:ℕ) := by
    have he (a : Fin p) : Complex.exp ((L (if a=s then (1:ℝ) else 0):ℂ)*Complex.I)=
        (if a=s then Complex.exp ((L 1:ℂ)*Complex.I)-1 else 0)+1 := by
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

lemma map_poisson_successCountAt (r : ℝ≥0) (p : ℕ) [NeZero p] (s : Fin p) :
    Measure.map (fun z : (k : ℕ) × (Fin k → Fin p) => successCountAt s z.2)
      (familyLaw (poissonMeasure r) (fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin p)))) =
      poissonMeasure (r/p) := by
  classical
  have he : MeasurableEmbedding (fun n : ℕ => (n:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).measurableEmbedding Nat.cast_injective
  apply he.map_injective
  rw [Measure.map_map (measurable_of_countable _) (measurable_sigmaUncurry (fun k => measurable_of_countable (fun a : Fin k → Fin p => successCountAt s a))),
    ← compoundPoisson_dirac_one,← compoundPoisson_uniform_indicator_at r p s]
  simp only [Function.comp_def]
  rw [map_familyLaw_sum _ _ (fun k (a : Fin k → Fin p) => (successCountAt s a:ℝ))
    (fun k => measurable_of_countable _)]
  unfold compoundPoisson
  congr 1
  funext k
  rw [poissonMeasure_singleton,← Measure.pi_map_pi (fun _ : Fin k => (measurable_of_countable
    (fun a : Fin p => if a=s then (1:ℝ) else 0)).aemeasurable),
    Measure.map_map (by fun_prop) (measurable_of_countable _)]
  congr 2
  funext a
  simp [successCountAt]

lemma selectedCount_eq_successCountAt {p : ℕ} [NeZero p] (s : Fin p) (k : ℕ)
    (c : RootPath (Fin p) k) :
    selectedCount k (rootMap (fun a => decide (a=s)) k c)=successCountAt s (rootArray k c) := by
  induction k with
  | zero => simp [selectedCount,successCountAt]
  | succ k ih =>
    simp only [rootMap,successCountAt,Fin.sum_univ_succ,rootArray,Fin.cons_zero,Fin.cons_succ]
    split_ifs with h
    · simp [h,selectedCount,ih,successCountAt,Nat.add_comm]
    · simp [h,selectedCount,ih,successCountAt]

end DilutedSpinGlass

end

end OAI
end

section
-- module Solutions.OAIQ067_SAT.DilutedSpin_PoissonRootSelection
attribute [-instance] _root_.OAI.RapidForcing.EffectiveArithmetic.ratPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
lemma successCountAt_le {p k : ℕ} [NeZero p] (s : Fin p) (a : Fin k → Fin p) :
    successCountAt s a≤k := by
  unfold successCountAt
  apply (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin k))) =>
    show (if a i=s then 1 else 0)≤1 by split_ifs <;> omega)).trans_eq
  simp

lemma integral_poisson_rootSelection (r : ℝ≥0) (N : ℕ) [NeZero N] (s : Fin N)
    (f : ℕ → ℝ) {B D : ℝ} (hD : 0≤D) (hf : ∀ n,|f n|≤B+D*n) :
    (∫ k,∫ c,f (selectedCount k (rootMap (fun a => decide (a=s)) k c))
      ∂rootLaw k (fun _ => finiteUniform (Fin N)) ∂poissonMeasure r)=
      ∫ n,f n ∂poissonMeasure (r/N) := by
  let ν := fun k => Measure.pi (fun _ : Fin k => finiteUniform (Fin N))
  have hi : Integrable (fun z : (k : ℕ) × (Fin k → Fin N) => f (successCountAt s z.2))
      (familyLaw (poissonMeasure r) ν) := by
    apply familyLaw_integrable_bound (poissonMeasure r) ν
      (fun k (a : Fin k → Fin N) => f (successCountAt s a)) (fun _ => measurable_of_countable _)
      ((integrable_const B).add ((poisson_integrable_count r).const_mul D))
    intro k a
    exact (hf _).trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (show (successCountAt s a:ℝ)≤k by exact_mod_cast successCountAt_le s a) hD) B)
  rw [←map_poisson_successCountAt r N s,
    integral_map (measurable_sigmaUncurry (fun k => measurable_of_countable
      (fun a : Fin k → Fin N => successCountAt s a))).aemeasurable
      (measurable_of_countable f).aestronglyMeasurable,
    integral_familyLaw (poissonMeasure r) ν (fun k (a : Fin k → Fin N) => f (successCountAt s a))
      (fun _ => measurable_of_countable _) hi]
  apply integral_congr_ae
  filter_upwards [] with k
  simp_rw [selectedCount_eq_successCountAt]
  exact integral_rootArray_eq_pi _ k (fun c => f (successCountAt s c))

end DilutedSpinGlass

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
open _root_.MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Topology

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma allocatedDatumRoot_integrable (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Integrable (fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
      allocatedDatumRoot T U V x m j s f l z.1 z.2)
      ((rootLaw l (fun _ => finiteUniform (Fin N))).prod
        (rootLaw l (fun _ => M.disorder.toMeasure.prod
          ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure))) := by
  have hi : Integrable (fun z : InteractionSample p × (Fin p → R) => ‖z.1.1‖)
      (M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure) :=
    measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable
  apply ((integrable_const ‖f‖).add ((integrable_rootArray_sum _ _ hi l).comp_snd
    (rootLaw l (fun _ => finiteUniform (Fin N))))).mono'
    (measurable_allocatedDatumRoot T U V x m j s f l).aestronglyMeasurable
  exact ae_of_all _ (fun z => allocatedDatumRoot_bound T U V x m hm j s f l z.1 z.2)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperAllocated_integrable (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    Integrable (fun z : RootPath (UpperDatum p N R) l =>
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f))
      (rootLaw l (fun _ => upperDatumLaw M Q)) := by
  have h := ((measurePreserving_rootSplit _ _ l).comp
    (measurePreserving_rootMap (upperDatum_site_projection M Q j) l)).integrable_comp_of_integrable
      (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.allocatedDatumRoot_integrable M hM Q T U V x m hm j s f l)
  simpa only [Function.comp_def,allocatedDatumRoot,rootMap_comp] using h

omit [MeasurableSingletonClass R] in

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperAllocatedMean (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    (∫ z : RootPath (UpperDatum p N R) l,
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f)
        ∂rootLaw l (fun _ => upperDatumLaw M Q))=
      ∫ c,activeCountMean M Q T U V x m j f
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N)) := by
  let F := fun z : RootPath (Fin N) l × RootPath (InteractionSample p × (Fin p → R)) l =>
    allocatedDatumRoot T U V x m j s f l z.1 z.2
  have hFm := measurable_allocatedDatumRoot T U V x m j s f l
  have he : (fun z : RootPath (UpperDatum p N R) l =>
      backwardLog n (cavityTower T U l (rootMap (fun a => a.2.2) l z)) m
        (allocatedEnergy V x j s l (rootMap (fun a => a.2.2) l z)
          (rootMap (fun a => a.2.1 j) l z) (rootMap Prod.fst l z) f))=
      fun z => F (rootMap Prod.fst l (rootMap (fun a => (a.2.1 j,(a.1,a.2.2))) l z),
        rootMap Prod.snd l (rootMap (fun a => (a.2.1 j,(a.1,a.2.2))) l z)) := by
    funext z
    simp only [F,allocatedDatumRoot,rootMap_comp,Function.comp_def]
  rw [he]
  apply (integral_rootMap (upperDatum_site_projection M Q j) l
    (fun z => F (rootMap Prod.fst l z,rootMap Prod.snd l z))
    (hFm.comp ((measurable_rootMap Prod.fst measurable_fst l).prodMk
      (measurable_rootMap Prod.snd measurable_snd l)))).trans
  rw [integral_rootSplit _ _ l F hFm (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.allocatedDatumRoot_integrable M hM Q T U V x m hm j s f l)]
  apply integral_congr_ae
  filter_upwards [] with c
  exact allocatedMean_selected M Q T U V x m j f s l c

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperCountMean_separable (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : Fin N → FinitePath Ω n → ℝ) (l : ℕ) :
    upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
      (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l=
      ∑ s : Fin N,∫ c,activeCountMean M Q (T s) U (V s) x m j (f s)
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N)) := by
  rw [upperCountMean_cavity]
  simp_rw [cavityRoot_separable,rootMap_comp,Function.comp_def]
  rw [integral_finsetSum _ (fun s _ => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperAllocated_integrable M hM Q (T s) U (V s) x m hm j s (f s) l)]
  exact Finset.sum_congr rfl (fun s _ => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperAllocatedMean M hM Q (T s) U (V s) x m hm j s (f s) l)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma activeCountMean_bound (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : FinitePath Ω n → ℝ) (l : ℕ) {B : ℝ} (hf : ∀ y,|f y|≤B) :
    |activeCountMean M Q T U V x m j f l|≤B+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*l := by
  let ν := M.disorder.toMeasure.prod ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure
  have hi : Integrable (fun z : InteractionSample p × (Fin p → R) => ‖z.1.1‖) ν :=
    measurePreserving_fst.integrable_comp_of_integrable hM.interaction_integrable
  have hs := integrable_rootArray_sum ν (fun z => ‖z.1.1‖) hi l
  have hB (z : RootPath (InteractionSample p × (Fin p → R)) l) :
      |activeDatumRoot T U V x m j f l z|≤B+∑ i,‖(rootArray l z i).1.1‖ := by
    apply backwardLog_bound n _ m hm
    intro y
    simpa only [rootArray_rootMap] using activeEnergy_bound V x j l
      (rootMap Prod.snd l z) (rootMap Prod.fst l z) f hf y
  have hF : Integrable (activeDatumRoot T U V x m j f l) (rootLaw l (fun _ => ν)) :=
    ((integrable_const B).add hs).mono'
      (measurable_activeDatumRoot T U V x m j f l).aestronglyMeasurable (ae_of_all _ hB)
  unfold activeCountMean
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono hF.abs ((integrable_const B).add hs) hB).trans_eq
  simp only [Pi.add_apply]
  rw [integral_add (integrable_const B) hs,integral_rootArray_sum ν _ hi l]
  have he : (∫ a : InteractionSample p × (Fin p → R),‖a.1.1‖ ∂ν)=
      ∫ a : InteractionSample p,‖a.1‖ ∂M.disorder.toMeasure := by
    simpa only [ν,probReal_univ,one_smul] using
      (integral_fun_fst (μ := M.disorder.toMeasure)
        (ν := ((FiniteLaw.pi (fun _ : Fin p => Q)).asProbability id).toMeasure)
        (fun a : InteractionSample p => ‖a.1‖))
  rw [he]
  simp only [integral_const,probReal_univ,one_smul,mul_comm]

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperSelectedCountMean_bound (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p) (s : Fin N)
    (f : FinitePath Ω n → ℝ) (l : ℕ) :
    |∫ c,activeCountMean M Q T U V x m j f
        (selectedCount l (rootMap (fun a => decide (a=s)) l c))
        ∂rootLaw l (fun _ => finiteUniform (Fin N))|≤
      ‖f‖+(∫ a,‖a.1‖ ∂M.disorder.toMeasure)*l := by
  apply abs_integral_le_bound_ae
  apply ae_of_all
  intro c
  apply (FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.activeCountMean_bound M hM Q T U V x m hm j f _ (fun y => norm_le_pi_norm f y)).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg (fun a => norm_nonneg a.1))
  rw [selectedCount_eq_successCountAt]
  exact_mod_cast successCountAt_le s (rootArray l c)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma upperPoisson_cavity_separable_sat_oai (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : Fin N → FinitePath Ω n → ℝ) (r : ℝ≥0) :
    (∫ l,upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
      (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l ∂poissonMeasure r)=
      ∑ s : Fin N,∫ k,activeCountMean M Q (T s) U (V s) x m j (f s) k
        ∂poissonMeasure (r/N) := by
  simp_rw [FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperCountMean_separable M hM Q T U V x m hm j f]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    exact integral_poisson_rootSelection r N s _ (integral_nonneg (fun a : InteractionSample p => norm_nonneg a.1))
      (fun l => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.activeCountMean_bound M hM Q (T s) U (V s) x m hm j (f s) l
        (fun y => norm_le_pi_norm (f s) y))
  · intro s _
    apply ((integrable_const ‖f s‖).add ((poisson_integrable_count r).const_mul
      (∫ a,‖a.1‖ ∂M.disorder.toMeasure))).mono' (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun l => FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperSelectedCountMean_bound M hM Q (T s) U (V s) x m hm j s (f s) l)

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

end

end OAI
end

theorem solution : type_of% @OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable_sat_oai := @OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable_sat_oai
