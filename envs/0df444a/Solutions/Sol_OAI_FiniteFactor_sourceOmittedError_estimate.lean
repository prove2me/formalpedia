-- Prove2me | solution 1 for OAI.FiniteFactor.sourceOmittedError_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:37:58.906267+00:00
-- url     : https://prove2.me/submissions/fd323513-abca-42a5-8aaf-05862d71e381

import Mathlib
import Definitions.Def_OAIQ3Ff002

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Density
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

omit [MeasurableSpace X] in
theorem intervalDensity_le [MeasurableSpace X] {U : Set X} {l : ℝ} (hl : 0 ≤ l) (x : X) :
    intervalDensity U l x ≤ l⁻¹ := by
  classical
  by_cases hx : x ∈ U <;> simp [intervalDensity, hx, inv_nonneg.mpr hl]

theorem intervalDensity_sq_integrable {U : Set X} (hU : MeasurableSet U) (l : ℝ) :
    Integrable (fun x => intervalDensity U l x ^ 2) μ := by
  have heq : (fun x => intervalDensity U l x ^ 2) = U.indicator (fun _ => (l⁻¹)^2) := by
    funext x
    by_cases hx : x ∈ U <;> simp [intervalDensity, hx]
  rw [heq]
  exact (integrable_const _).indicator hU

omit [IsProbabilityMeasure μ] in
theorem intervalDensity_sq_integral [IsProbabilityMeasure μ] {U : Set X} (hU : MeasurableSet U)
    {l : ℝ} (hl : 0 < l) (hm : μ.real U = l) :
    ∫ x, intervalDensity U l x ^ 2 ∂μ = l⁻¹ := by
  have heq : (fun x => intervalDensity U l x ^ 2) = U.indicator (fun _ => (l⁻¹)^2) := by
    funext x
    by_cases hx : x ∈ U <;> simp [intervalDensity, hx]
  rw [heq, integral_indicator hU, setIntegral_const, smul_eq_mul, hm]
  field_simp

/-- The mass-one identity cancels the linear term exactly. -/
theorem density_energy_identity {h : X → ℝ} (hh : Integrable h μ)
    (hh2 : Integrable (fun x => h x ^ 2) μ) (hm : ∫ x, h x ∂μ = 1) :
    (∫ x, (h x - 1)^2 ∂μ) = (∫ x, h x ^ 2 ∂μ) - 1 := by
  have heq : (fun x => (h x - 1)^2) = fun x => h x ^ 2 - 2*h x + 1 := by
    funext x; ring
  have h₁ := integral_add (hh2.sub (hh.const_mul 2)) (integrable_const (1 : ℝ))
  have h₂ := integral_sub hh2 (hh.const_mul 2)
  dsimp only [Pi.sub_apply, Pi.add_apply] at h₁ h₂
  rw [heq, h₁, h₂, integral_const_mul, hm]
  simp
  ring

/-- Each normalized interval perturbation has energy exactly 1/length - 1. -/
theorem intervalDensity_energy {U : Set X} (hU : MeasurableSet U)
    {l : ℝ} (hl : 0 < l) (hm : μ.real U = l) :
    (∫ x, (intervalDensity U l x - 1)^2 ∂μ) = l⁻¹ - 1 := by
  rw [density_energy_identity (intervalDensity_integrable hU l)
    (intervalDensity_sq_integrable hU l) (intervalDensity_integral hU hl hm),
    intervalDensity_sq_integral hU hl hm]

/-- Finite product estimate used in uniform-product-density; the bound has
no dependence on the choice of endpoint orientation. -/
theorem product_energy_le_exp {ι : Type*} [Fintype ι]
    (A e : ι → ℝ) (hA0 : ∀ i, 0 ≤ A i) (hA : ∀ i, A i ≤ 1 + e i) :
    (∏ i, A i) ≤ Real.exp (∑ i, e i) := by
  calc
    (∏ i, A i) ≤ ∏ i, Real.exp (e i) := by
      apply Finset.prod_le_prod (fun i _ => hA0 i)
      intro i _
      exact (hA i).trans (by linarith [Real.add_one_le_exp (e i)])
    _ = _ := (Real.exp_sum _ _).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Parameters
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.coupling_probability _root_.OAI.FiniteFactor.CouplingParameters.endpointComponentLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.labelledCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.pairComponentLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.posteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

namespace CouplingParameters
variable (p : CouplingParameters)

theorem rho_div_width_le (i : Fin 2) : p.rho i / p.width i ≤ p.kappa :=
  (div_le_iff₀ (p.width_pos i)).2 (p.rho_le i)

theorem rho_energy (i : Fin 2) : (p.rho i)^2 / p.width i = p.kappa^2 / p.m := by
  rw [rho, mul_pow, Real.sq_sqrt (div_nonneg (p.width_pos i).le p.m_pos.le)]
  field_simp [p.m_pos.ne', (p.width_pos i).ne']

theorem diagonalMass_le : p.diagonalMass ≤ 1 := by
  unfold diagonalMass
  linarith [p.rho_nonneg 0, p.rho_nonneg 1, p.tagMass_nonneg]

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Mixture
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.coupling_probability _root_.OAI.FiniteFactor.CouplingParameters.endpointComponentLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.labelledCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.pairComponentLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.posteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι]

theorem mixtureDensity_memLp (q : ℝ) (π : ι → ℝ) (d : ι → X → ℝ)
    (hd : ∀ i, MemLp (d i) 2 μ) : MemLp (mixtureDensity q π d) 2 μ :=
  (memLp_const q).add (memLp_finsetSum Finset.univ (fun i _ => (hd i).const_mul (π i)))

theorem mixtureDensity_integral (q : ℝ) (π : ι → ℝ) (d : ι → X → ℝ)
    (hd : ∀ i, Integrable (d i) μ) (hm : ∀ i, ∫ x, d i x ∂μ = 1)
    (hπ : q + ∑ i, π i = 1) : ∫ x, mixtureDensity q π d x ∂μ = 1 := by
  have hi := integral_add (integrable_const q)
    (integrable_finsetSum Finset.univ (fun i _ => (hd i).const_mul (π i)))
  unfold mixtureDensity
  rw [hi, integral_finsetSum Finset.univ (fun i _ => (hd i).const_mul (π i))]
  simp_rw [integral_const_mul, hm, mul_one]
  simpa using hπ

theorem mixtureDensity_energy_le (q : ℝ) (π : ι → ℝ) (d : ι → X → ℝ)
    (hd : ∀ i, MemLp (d i) 2 μ) (hm : ∀ i, ∫ x, d i x ∂μ = 1)
    (hπ : q + ∑ i, π i = 1) (E : ι → ℝ)
    (hE : ∀ i, (∫ x, (d i x - 1)^2 ∂μ) ≤ E i) :
    (∫ x, mixtureDensity q π d x ^ 2 ∂μ) ≤
      1 + (Fintype.card ι : ℝ) * ∑ i, (π i)^2 * E i := by
  classical
  have hd1 (i) : Integrable (d i) μ := (hd i).integrable (by norm_num)
  have hh := mixtureDensity_memLp q π d hd
  have hm' := mixtureDensity_integral q π d hd1 hm hπ
  have heq (x : X) : mixtureDensity q π d x - 1 = ∑ i, π i * (d i x - 1) := by
    simp only [mixtureDensity, mul_sub, mul_one, Finset.sum_sub_distrib]
    linarith
  have hbound (x : X) : (mixtureDensity q π d x - 1)^2 ≤
      (Fintype.card ι : ℝ) * ∑ i, (π i)^2 * (d i x - 1)^2 := by
    rw [heq]
    simpa [mul_pow] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => π i * (d i x - 1)))
  have hsub (i) : MemLp (fun x => d i x - 1) 2 μ := (hd i).sub (memLp_const 1)
  have his (i) : Integrable (fun x => (π i)^2 * (d i x - 1)^2) μ :=
    (hsub i).integrable_sq.const_mul _
  have hi := integral_mono ((hh.sub (memLp_const 1)).integrable_sq)
    ((integrable_finsetSum Finset.univ (fun i _ => his i)).const_mul (Fintype.card ι : ℝ)) hbound
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => his i)] at hi
  simp_rw [integral_const_mul] at hi
  have hsum : (∑ i, (π i)^2 * ∫ x, (d i x - 1)^2 ∂μ) ≤ ∑ i, (π i)^2 * E i := by
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hE i) (sq_nonneg _)
  have he := density_energy_identity (hh.integrable (by norm_num)) hh.integrable_sq hm'
  have hc := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
  dsimp only [Pi.sub_apply] at hi
  linarith

namespace CouplingParameters
variable (p : CouplingParameters)

theorem endpointDensity_memLp (right : Bool) : MemLp (p.endpointDensity right) 2 unitIntervalMeasure := by
  apply mixtureDensity_memLp
  intro i
  exact (memLp_const _).indicator (p.endpointInterval_measurable right i)

theorem endpointDensity_integral (right : Bool) :
    ∫ t, p.endpointDensity right t ∂unitIntervalMeasure = 1 := by
  apply mixtureDensity_integral
  · intro i
    exact intervalDensity_integrable (p.endpointInterval_measurable right i) _
  · intro i
    exact intervalDensity_integral (p.endpointInterval_measurable right i)
      (p.endpointLength_pos right i) (p.endpointInterval_mass right i)
  · exact p.mass_sum

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Bounds
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.coupling_probability _root_.OAI.FiniteFactor.CouplingParameters.endpointComponentLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.labelledCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.pairComponentLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.posteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

theorem minimumLength_pos (i : Fin 5) : 0 < p.minimumLength i := by
  have h₀ := p.width_pos 0
  have h₁ := p.width_pos 1
  fin_cases i <;> simp [minimumLength] <;> linarith [p.m_pos]

theorem minimumLength_le (right : Bool) (i : Fin 5) :
    p.minimumLength i ≤ p.endpointLength right i := by
  have h₀ := p.width_upper 0
  have h₁ := p.width_upper 1
  cases right <;> fin_cases i <;>
    simp [minimumLength, endpointLength, leftLength, rightLength] <;> linarith

theorem weighted_minimumLength_le (i : Fin 5) :
    p.replacementMass i / p.minimumLength i ≤ ![2*p.kappa, 2*p.kappa, 2*p.kappa, 2*p.kappa, 1] i := by
  have h₀ := p.rho_div_width_le 0
  have h₁ := p.rho_div_width_le 1
  have he (w r : ℝ) : r / (w/2) = 2*(r/w) := by ring
  fin_cases i <;> dsimp [replacementMass, minimumLength]
  all_goals try { rw [he]; linarith }
  unfold tagMass
  split
  · rw [div_self (ne_of_gt (one_div_pos.mpr p.m_pos))]
  · simp

theorem weighted_inverse_length_le (right : Bool) (i : Fin 5) :
    p.replacementMass i * (p.endpointLength right i)⁻¹ ≤
      ![2*p.kappa, 2*p.kappa, 2*p.kappa, 2*p.kappa, 1] i := by
  rw [← div_eq_mul_inv]
  exact (div_le_div_of_nonneg_left (p.replacementMass_nonneg i)
    (p.minimumLength_pos i) (p.minimumLength_le right i)).trans
    (p.weighted_minimumLength_le i)

theorem endpointDensity_upper (right : Bool) (t : ℝ) :
    p.endpointDensity right t ≤ 2+8*p.kappa := by
  have hb : (∑ i, p.replacementMass i * p.endpointComponentDensity right i t) ≤
      ∑ i : Fin 5, ![2*p.kappa, 2*p.kappa, 2*p.kappa, 2*p.kappa, 1] i := by
    apply Finset.sum_le_sum
    intro i _
    exact (mul_le_mul_of_nonneg_left (intervalDensity_le (p.endpointLength_pos right i).le t)
      (p.replacementMass_nonneg i)).trans (p.weighted_inverse_length_le right i)
  simp [Fin.sum_univ_succ] at hb
  change p.diagonalMass + _ ≤ _
  simp [Fin.sum_univ_succ]
  linarith [p.diagonalMass_le]

theorem endpointDensity_lt_ten (right : Bool) (t : ℝ) :
    p.endpointDensity right t < 10 := by
  linarith [p.endpointDensity_upper right t, p.kappa_le]

theorem weighted_minimumLength_energy (i : Fin 5) :
    (p.replacementMass i)^2 / p.minimumLength i =
      ![2*p.kappa^2/p.m, 2*p.kappa^2/p.m, 2*p.kappa^2/p.m, 2*p.kappa^2/p.m, p.tagMass] i := by
  have he (w r : ℝ) : r^2 / (w/2) = 2*(r^2/w) := by ring
  fin_cases i <;> dsimp [replacementMass, minimumLength]
  all_goals try { rw [he, p.rho_energy]; ring }
  unfold tagMass
  split
  · field_simp
  · simp

theorem endpointDensity_energy (right : Bool) :
    (∫ t, p.endpointDensity right t ^ 2 ∂unitIntervalMeasure) ≤
      1 + 40*p.kappa^2/p.m + 5*p.tagMass := by
  have hbase := mixtureDensity_energy_le p.diagonalMass p.replacementMass
    (p.endpointComponentDensity right)
    (fun i => (memLp_const _).indicator (p.endpointInterval_measurable right i))
    (fun i => intervalDensity_integral (p.endpointInterval_measurable right i)
      (p.endpointLength_pos right i) (p.endpointInterval_mass right i))
    p.mass_sum (fun i => (p.endpointLength right i)⁻¹)
    (fun i => by
      unfold endpointComponentDensity
      rw [intervalDensity_energy (p.endpointInterval_measurable right i)
        (p.endpointLength_pos right i) (p.endpointInterval_mass right i)]
      linarith)
  have hb : (∑ i, p.replacementMass i ^ 2 * (p.endpointLength right i)⁻¹) ≤
      ∑ i : Fin 5, ![2*p.kappa^2/p.m, 2*p.kappa^2/p.m, 2*p.kappa^2/p.m, 2*p.kappa^2/p.m, p.tagMass] i := by
    apply Finset.sum_le_sum
    intro i _
    rw [← div_eq_mul_inv, ← p.weighted_minimumLength_energy i]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (p.minimumLength_pos i) (p.minimumLength_le right i)
  simp only [Fintype.card_fin] at hbase
  simp [Fin.sum_univ_succ] at hb
  change (∫ t, p.endpointDensity right t ^ 2 ∂unitIntervalMeasure) ≤ _ at hbase
  simp [Fin.sum_univ_succ] at hbase
  ring_nf at hbase hb ⊢
  linarith

theorem endpointDensity_source_energy (right : Bool) :
    (∫ t, p.endpointDensity right t ^ 2 ∂unitIntervalMeasure) ≤
      1 + 20*(2*p.kappa^2/p.m + p.tagMass) := by
  have := p.endpointDensity_energy right
  have hn := p.tagMass_nonneg
  ring_nf at this ⊢
  linarith

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Law
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

namespace CouplingParameters
variable (p : CouplingParameters)

theorem endpointComponentLaw_eq (right : Bool) (i : Fin 5) :
    p.endpointComponentLaw right i = ENNReal.ofReal ((p.endpointLength right i)⁻¹) •
      unitIntervalMeasure.restrict (p.endpointInterval right i) := by
  unfold endpointComponentLaw endpointComponentDensity intervalDensity
  have heq : (fun t => ENNReal.ofReal ((p.endpointInterval right i).indicator
      (fun _ => (p.endpointLength right i)⁻¹) t)) =
      (p.endpointInterval right i).indicator (fun _ => ENNReal.ofReal ((p.endpointLength right i)⁻¹)) := by
    funext t
    by_cases ht : t ∈ p.endpointInterval right i <;> simp [ht]
  rw [heq, withDensity_indicator (p.endpointInterval_measurable right i), withDensity_const]

theorem endpointComponentLaw_of_contains (right : Bool) (i : Fin 5) {S : Set ℝ}
    (hS : p.endpointInterval right i ⊆ S) : p.endpointComponentLaw right i S = 1 := by
  have hu := measure_univ (μ := p.endpointComponentLaw right i)
  rw [p.endpointComponentLaw_eq, Measure.smul_apply,
    Measure.restrict_apply' (p.endpointInterval_measurable right i), Set.univ_inter] at hu
  rw [p.endpointComponentLaw_eq, Measure.smul_apply,
    Measure.restrict_apply' (p.endpointInterval_measurable right i), Set.inter_eq_right.mpr hS]
  exact hu

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Marginals
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem withDensity_finite_sum {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (f : ι → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    μ.withDensity (fun x => ∑ i, f i x) = ∑ i, μ.withDensity (f i) := by
  ext S hS
  rw [withDensity_apply _ hS, Measure.finsetSum_apply,
    lintegral_finsetSum Finset.univ (fun i _ => hf i)]
  simp_rw [withDensity_apply _ hS]

theorem mixture_withDensity {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (q : ℝ) (π : ι → ℝ) (d : ι → X → ℝ)
    (hq : 0 ≤ q) (hπ : ∀ i, 0 ≤ π i) (hd : ∀ i x, 0 ≤ d i x)
    (hmd : ∀ i, Measurable (d i)) :
    μ.withDensity (fun x => ENNReal.ofReal (mixtureDensity q π d x)) =
      ENNReal.ofReal q • μ + ∑ i, ENNReal.ofReal (π i) •
        μ.withDensity (fun x => ENNReal.ofReal (d i x)) := by
  have heq : (fun x => ENNReal.ofReal (mixtureDensity q π d x)) =
      fun x => ENNReal.ofReal q + ∑ i, ENNReal.ofReal (π i) * ENNReal.ofReal (d i x) := by
    funext x
    rw [mixtureDensity, ENNReal.ofReal_add hq (Finset.sum_nonneg (fun i _ => mul_nonneg (hπ i) (hd i x))),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hπ i) (hd i x))]
    simp_rw [ENNReal.ofReal_mul (hπ _)]
  have hadd := withDensity_add_left (μ := μ)
    (f := fun _ : X => ENNReal.ofReal q) measurable_const
    (fun x => ∑ i, ENNReal.ofReal (π i) * ENNReal.ofReal (d i x))
  change μ.withDensity (fun x => ENNReal.ofReal q + ∑ i, ENNReal.ofReal (π i) * ENNReal.ofReal (d i x)) = _ at hadd
  rw [heq, hadd, withDensity_const,
    withDensity_finite_sum μ (fun i x => ENNReal.ofReal (π i) * ENNReal.ofReal (d i x))
      (fun i => measurable_const.mul (hmd i).ennreal_ofReal)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact withDensity_smul (ENNReal.ofReal (π i)) (hmd i).ennreal_ofReal

namespace CouplingParameters
variable (p : CouplingParameters)

theorem coupling_eq_sum : p.coupling = ∑ i, ENNReal.ofReal (p.labelMass i) • p.pairComponentLaw i := by
  unfold coupling labelledCoupling
  rw [Measure.map_finset_sum' measurable_snd.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  have hm : Measurable (fun xy : ℝ × ℝ => (i,xy)) := measurable_const.prodMk measurable_id
  rw [Measure.map_smul, Measure.map_map measurable_snd hm]
  simp [Function.comp_def]

theorem pairComponentLaw_endpoint (right : Bool) (i : Fin 6) :
    (p.pairComponentLaw i).map (endpoint right) =
      (Fin.cons unitIntervalMeasure (p.endpointComponentLaw right) : Fin 6 → Measure ℝ) i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · change (unitIntervalMeasure.map (fun t => (t,t))).map (endpoint right) = _
    have hm : Measurable (fun t : ℝ => (t,t)) := measurable_id.prodMk measurable_id
    rw [Measure.map_map (endpoint_measurable right) hm]
    cases right <;> simp [endpoint, Function.comp_def]
  · change ((p.endpointComponentLaw false k).prod (p.endpointComponentLaw true k)).map (endpoint right) = _
    cases right
    · change Measure.map Prod.fst _ = _
      simp
    · change Measure.map Prod.snd _ = _
      simp

/-- Identification of the actual pair law's two endpoint densities. -/
theorem coupling_endpoint_density (right : Bool) :
    p.coupling.map (endpoint right) =
      unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (p.endpointDensity right t)) := by
  rw [p.coupling_eq_sum, Measure.map_finset_sum' (endpoint_measurable right).aemeasurable]
  simp_rw [Measure.map_smul,
    p.pairComponentLaw_endpoint]
  rw [Fin.sum_univ_succ]
  change ENNReal.ofReal p.diagonalMass • unitIntervalMeasure +
      ∑ i, ENNReal.ofReal (p.replacementMass i) • p.endpointComponentLaw right i = _
  exact (mixture_withDensity unitIntervalMeasure p.diagonalMass p.replacementMass
    (p.endpointComponentDensity right) p.diagonalMass_pos.le p.replacementMass_nonneg
    (fun i => intervalDensity_nonneg (p.endpointLength_pos right i).le)
    (p.endpointComponentDensity_measurable right)).symm

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Infinite
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

theorem labelled_endpoint_density (p : CouplingParameters) (right : Bool) :
    p.labelledCoupling.map (fun z => endpoint right z.2) =
      unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (p.endpointDensity right t)) := by
  rw [← p.coupling_endpoint_density]
  unfold coupling
  rw [Measure.map_map (endpoint_measurable right) measurable_snd]
  rfl

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Crossing
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

theorem crossingLabel_mass (right : Bool) (w : Fin 2) :
    p.replacementMass (crossingLabel right w) = p.rho w := by
  cases right <;> fin_cases w <;> simp [crossingLabel, replacementMass]

theorem crossingLabel_length (right : Bool) (w : Fin 2) :
    p.endpointLength right (crossingLabel right w) = 1-p.width w/2 := by
  cases right <;> fin_cases w <;>
    simp [crossingLabel, endpointLength, leftLength, rightLength]

theorem crossingLabel_interval (right : Bool) (w : Fin 2) :
    p.endpointInterval right (crossingLabel right w) =
      if right then Set.Ico (p.width w/2) 1 else Set.Ico 0 (1-p.width w/2) := by
  cases right <;> fin_cases w <;>
    simp [crossingLabel, endpointInterval, leftLength, rightLength]

theorem crossingLabel_opposite_interval (right : Bool) (w : Fin 2) :
    p.endpointInterval (!right) (crossingLabel right w) =
      if right then Set.Ico 0 (p.width w/2) else Set.Ico (1-p.width w/2) 1 := by
  cases right <;> fin_cases w <;>
    simp [crossingLabel, endpointInterval, leftLength, rightLength]

theorem crossing_component_density_ge_one (right : Bool) (w : Fin 2)
    {t u : ℝ} (ht : t ∈ Set.Ico 0 1) (hu : p.width w ≤ u ∧ u ≤ 1-p.width w)
    (heligible : if right then u ≤ t else t < u) :
    1 ≤ p.endpointComponentDensity right (crossingLabel right w) t := by
  have hw := p.width_pos w
  have hupp := p.width_upper w
  have hmem : t ∈ p.endpointInterval right (crossingLabel right w) := by
    rw [p.crossingLabel_interval]
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at *
    · exact ⟨ht.1, by linarith [hu.2]⟩
    · exact ⟨by linarith [hu.1], ht.2⟩
  unfold endpointComponentDensity intervalDensity
  rw [Set.indicator_of_mem hmem, p.crossingLabel_length]
  exact (one_le_inv₀ (by linarith : 0 < 1-p.width w/2)).2 (by linarith)

theorem crossing_posterior_lower (right : Bool) (w : Fin 2)
    {t u : ℝ} (ht : t ∈ Set.Ico 0 1) (hu : p.width w ≤ u ∧ u ≤ 1-p.width w)
    (heligible : if right then u ≤ t else t < u) :
    p.rho w / 10 ≤ p.posteriorMass right t (crossingLabel right w) := by
  have hh := p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)
  have hd := p.crossing_component_density_ge_one right w ht hu heligible
  unfold posteriorMass
  rw [p.crossingLabel_mass]
  calc
    p.rho w / 10 ≤ p.rho w / p.endpointDensity right t :=
      div_le_div_of_nonneg_left (p.rho_nonneg w) hh (p.endpointDensity_lt_ten right t).le
    _ ≤ _ := div_le_div_of_nonneg_right
      (by simpa using mul_le_mul_of_nonneg_left hd (p.rho_nonneg w)) hh.le

/-- The opposite endpoint of the selected label crosses the threshold surely. -/
theorem crossing_partner_interval (right : Bool) (w : Fin 2) {u : ℝ}
    (hu : p.width w ≤ u ∧ u ≤ 1-p.width w) :
    p.endpointInterval (!right) (crossingLabel right w) ⊆
      if right then Set.Iio u else Set.Ici u := by
  rw [p.crossingLabel_opposite_interval]
  have hw := p.width_pos w
  cases right <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · intro z hz
    exact (by linarith [hz.1, hu.2] : u ≤ z)
  · intro z hz
    exact (by linarith [hz.2, hu.1] : z < u)

theorem posteriorLaw_component_le (right : Bool) (t : ℝ) (i : Fin 5) (S : Set ℝ) :
    ENNReal.ofReal (p.posteriorMass right t i) * p.endpointComponentLaw (!right) i S ≤
      p.posteriorLaw right t S := by
  rw [posteriorLaw, Measure.add_apply, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  apply le_trans _ (le_add_left le_rfl)
  exact Finset.single_le_sum (f := fun j => ENNReal.ofReal (p.posteriorMass right t j) *
    p.endpointComponentLaw (!right) j S) (fun j _ => zero_le) (Finset.mem_univ i)

/-- Both orientations of the actual posterior crossing estimate, with the
source constant 1/10 and no assumptions on a candidate projection. -/
theorem posteriorLaw_crossing_lower (right : Bool) (w : Fin 2)
    {t u : ℝ} (ht : t ∈ Set.Ico 0 1) (hu : p.width w ≤ u ∧ u ≤ 1-p.width w)
    (heligible : if right then u ≤ t else t < u) :
    ENNReal.ofReal (p.rho w / 10) ≤
      p.posteriorLaw right t (if right then Set.Iio u else Set.Ici u) := by
  have hcomp := p.endpointComponentLaw_of_contains (!right) (crossingLabel right w)
    (p.crossing_partner_interval right w hu)
  have hterm := p.posteriorLaw_component_le right t (crossingLabel right w)
    (if right then Set.Iio u else Set.Ici u)
  rw [hcomp, mul_one] at hterm
  exact (ENNReal.ofReal_le_ofReal (p.crossing_posterior_lower right w ht hu heligible)).trans hterm

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Bayes
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

theorem posteriorLaw_weighted (right : Bool) (t : ℝ) (S : Set ℝ) :
    ENNReal.ofReal (p.endpointDensity right t) * p.posteriorLaw right t S =
      ENNReal.ofReal p.diagonalMass * Measure.dirac t S +
        ∑ i, ENNReal.ofReal (p.replacementMass i) *
          ENNReal.ofReal (p.endpointComponentDensity right i t) * p.endpointComponentLaw (!right) i S := by
  have hh := p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)
  have hc (a : ℝ) : p.endpointDensity right t * (a / p.endpointDensity right t) = a := by
    field_simp [hh.ne']
  simp only [posteriorLaw, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    mul_add, Finset.mul_sum]
  congr 1
  · rw [← mul_assoc, ← ENNReal.ofReal_mul hh.le, hc]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, ← ENNReal.ofReal_mul hh.le, posteriorMass, hc,
      ENNReal.ofReal_mul (p.replacementMass_nonneg i)]

theorem coupling_rectangle {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    p.coupling (A ×ˢ B) = ENNReal.ofReal p.diagonalMass * unitIntervalMeasure (A ∩ B) +
      ∑ i, ENNReal.ofReal (p.replacementMass i) *
        p.endpointComponentLaw false i A * p.endpointComponentLaw true i B := by
  have hm : Measurable (fun t : ℝ => (t,t)) := measurable_id.prodMk measurable_id
  have hdiag : (unitIntervalMeasure.map (fun t => (t,t))) (A ×ˢ B) =
      unitIntervalMeasure (A ∩ B) := by
    rw [Measure.map_apply hm (hA.prod hB)]
    rfl
  simp [p.coupling_eq_sum, Fin.sum_univ_succ, labelMass,
    pairComponentLaw, smul_eq_mul, hdiag, Measure.prod_prod, mul_assoc]

/-- The posterior formula satisfies the defining conditional-law identity on
all measurable rectangles, in either endpoint orientation. -/
theorem posterior_rectangle_integral (right : Bool) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ t in A, p.posteriorLaw right t B ∂(p.coupling.map (endpoint right))) =
      ENNReal.ofReal p.diagonalMass * unitIntervalMeasure (A ∩ B) +
        ∑ i, ENNReal.ofReal (p.replacementMass i) *
          p.endpointComponentLaw right i A * p.endpointComponentLaw (!right) i B := by
  have hk : Measurable (fun t => p.posteriorLaw right t B) :=
    (Measure.measurable_coe hB).comp (p.posteriorKernel right).measurable
  rw [p.coupling_endpoint_density,
    setLIntegral_withDensity_eq_setLIntegral_mul unitIntervalMeasure
      (p.endpointDensity_measurable right).ennreal_ofReal hk hA]
  change (∫⁻ t in A, ENNReal.ofReal (p.endpointDensity right t) * p.posteriorLaw right t B
    ∂unitIntervalMeasure) = _
  simp_rw [p.posteriorLaw_weighted]
  have hd : Measurable (fun t : ℝ => Measure.dirac t B) :=
    (Measure.measurable_coe hB).comp Measure.measurable_dirac
  rw [lintegral_add_left
    (f := fun t => ENNReal.ofReal p.diagonalMass * Measure.dirac t B)
    (g := fun t => ∑ i, ENNReal.ofReal (p.replacementMass i) *
      ENNReal.ofReal (p.endpointComponentDensity right i t) * p.endpointComponentLaw (!right) i B)
    (measurable_const.mul hd),
    lintegral_finsetSum (f := fun i t => ENNReal.ofReal (p.replacementMass i) *
      ENNReal.ofReal (p.endpointComponentDensity right i t) * p.endpointComponentLaw (!right) i B)
      Finset.univ (fun i _ =>
      (measurable_const.mul (p.endpointComponentDensity_measurable right i).ennreal_ofReal).mul measurable_const)]
  congr 1
  · rw [lintegral_const_mul _ hd]
    simp only [Measure.dirac_apply' _ hB]
    rw [lintegral_indicator hB]
    simp [Measure.restrict_apply hB, Set.inter_comm]
  · apply Finset.sum_congr rfl
    intro i _
    have hi := (p.endpointComponentDensity_measurable right i).ennreal_ofReal
    rw [lintegral_mul_const (p.endpointComponentLaw (!right) i B)
      (f := fun t => ENNReal.ofReal (p.replacementMass i) * ENNReal.ofReal (p.endpointComponentDensity right i t))
      (measurable_const.mul hi), lintegral_const_mul _ hi]
    simp only [endpointComponentLaw]
    rw [withDensity_apply _ hA]

/-- Genuine forward disintegration of the constructed coupling. -/
theorem conditional_given_x {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ t in A, p.posteriorKernel false t B ∂(p.coupling.map Prod.fst)) = p.coupling (A ×ˢ B) := by
  rw [p.coupling_rectangle hA hB]
  exact p.posterior_rectangle_integral false hA hB

/-- Genuine reverse disintegration of the same coupling. -/
theorem conditional_given_y {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫⁻ t in A, p.posteriorKernel true t B ∂(p.coupling.map Prod.snd)) = p.coupling (B ×ˢ A) := by
  rw [p.coupling_rectangle hB hA]
  have hi := p.posterior_rectangle_integral true hA hB
  simp only [Bool.not_true] at hi
  change (∫⁻ t in A, p.posteriorLaw true t B ∂(p.coupling.map (endpoint true))) = _
  rw [hi, Set.inter_comm A B]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Products
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem sourceKappa_sq_summable : Summable (fun s => sourceKappa s ^ 2) := by
  have hs : Summable (fun s : ℕ => 1/(s : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs' := (summable_nat_add_iff 1).2 hs
  have heq (s : ℕ) : sourceKappa s ^ 2 = (1/10000 : ℝ) * (1/((s+1 : ℕ) : ℝ)^2) := by
    simp only [sourceKappa, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  simp_rw [heq]
  exact hs'.mul_left _

namespace CouplingParameters

theorem block_energy_cancellation (p : CouplingParameters) :
    p.m * (2*p.kappa^2/p.m + p.tagMass) = 2*p.kappa^2 + if p.tagged then 1 else 0 := by
  unfold tagMass
  split <;> field_simp [p.m_pos.ne']
  simp

/-- The sum over arbitrary finite sets of whole blocks is uniformly bounded.
The unique tagged block contributes at most one, even when it is absent. -/
theorem uniform_block_budget (p : ℕ → CouplingParameters) (j : ℕ)
    (htag : ∀ s, (p s).tagged = decide (s=j))
    (hκ : Summable (fun s => (p s).kappa^2)) (B : Finset ℕ) :
    (∑ s ∈ B, (p s).m * (2*(p s).kappa^2/(p s).m + (p s).tagMass)) ≤
      2*(∑' s, (p s).kappa^2) + 1 := by
  simp_rw [block_energy_cancellation, htag, decide_eq_true_eq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs := hκ.sum_le_tsum B (fun s _ => sq_nonneg ((p s).kappa))
  have ht : (∑ s ∈ B, if s=j then (1 : ℝ) else 0) ≤ 1 := by
    simp only [Finset.sum_ite_eq']
    split <;> norm_num
  linarith

theorem selectedDensity_nonneg (p : CouplingParameters) (enabled right : Bool) (t : ℝ) :
    0 ≤ p.selectedDensity enabled right t := by
  cases enabled
  · exact zero_le_one
  · exact (p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)).le

theorem selectedDensity_le_ten (p : CouplingParameters) (enabled right : Bool) (t : ℝ) :
    p.selectedDensity enabled right t ≤ 10 := by
  cases enabled
  · norm_num [selectedDensity]
  · exact (p.endpointDensity_lt_ten right t).le

theorem selectedDensity_measurable (p : CouplingParameters) (enabled right : Bool) :
    Measurable (p.selectedDensity enabled right) := by
  cases enabled
  · exact measurable_const
  · exact p.endpointDensity_measurable right

theorem selectedDensity_memLp (p : CouplingParameters) (enabled right : Bool) :
    MemLp (p.selectedDensity enabled right) 2 unitIntervalMeasure := by
  cases enabled
  · exact memLp_const 1
  · exact p.endpointDensity_memLp right

theorem selectedDensity_integral (p : CouplingParameters) (enabled right : Bool) :
    ∫ t, p.selectedDensity enabled right t ∂unitIntervalMeasure = 1 := by
  cases enabled
  · simp [selectedDensity]
  · exact p.endpointDensity_integral right

theorem finiteProductDensity_measurable {ι : Type*} [Fintype ι]
    (p : ι → CouplingParameters) (enabled right : ι → Bool) :
    Measurable (finiteProductDensity p enabled right) := by
  exact Finset.measurable_prod _ fun i _ =>
    ((p i).selectedDensity_measurable (enabled i) (right i)).comp (measurable_pi_apply i)

/-- Membership in L2 is proved, so the uniform square-integral bound is not
an assertion about a Bochner integral of a nonintegrable function. -/
theorem finiteProductDensity_memLp {ι : Type*} [Fintype ι]
    (p : ι → CouplingParameters) (enabled right : ι → Bool) :
    MemLp (finiteProductDensity p enabled right) 2 (Measure.pi (fun _ : ι => unitIntervalMeasure)) := by
  apply MemLp.of_bound (finiteProductDensity_measurable p enabled right).aestronglyMeasurable
    ((10 : ℝ)^(Fintype.card ι))
  apply Filter.Eventually.of_forall
  intro x
  have hnon : 0 ≤ finiteProductDensity p enabled right x :=
    Finset.prod_nonneg fun i _ => (p i).selectedDensity_nonneg (enabled i) (right i) (x i)
  rw [Real.norm_of_nonneg hnon]
  unfold finiteProductDensity
  calc
    _ ≤ ∏ _i : ι, (10 : ℝ) := Finset.prod_le_prod
      (fun i _ => (p i).selectedDensity_nonneg (enabled i) (right i) (x i))
      (fun i _ => (p i).selectedDensity_le_ten (enabled i) (right i) (x i))
    _ = _ := by simp

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_FiniteLaw
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

instance selectedLaw_probability (p : CouplingParameters) (enabled right : Bool) :
    IsProbabilityMeasure (p.selectedLaw enabled right) :=
  densityMeasure_probability ((p.selectedDensity_memLp enabled right).integrable (by norm_num))
    (p.selectedDensity_nonneg enabled right) (p.selectedDensity_integral enabled right)

theorem selectedLaw_endpoint (p : CouplingParameters) (right : Bool) :
    p.selectedLaw true right = p.coupling.map (endpoint right) :=
  (p.coupling_endpoint_density right).symm

theorem selectedLaw_apply_integral (p : CouplingParameters) (enabled right : Bool)
    {S : Set ℝ} (hS : MeasurableSet S) :
    p.selectedLaw enabled right S = ENNReal.ofReal (∫ t in S, p.selectedDensity enabled right t ∂unitIntervalMeasure) := by
  rw [selectedLaw, withDensity_apply _ hS]
  exact (ofReal_integral_eq_lintegral_ofReal
    (((p.selectedDensity_memLp enabled right).integrable (by norm_num)).restrict)
    (Filter.Eventually.of_forall (p.selectedDensity_nonneg enabled right))).symm

/-- The actual finite product law has the product density with the established L2 bounds.
This identifies measures on every measurable set. -/
theorem finiteProductLaw_density {ι : Type*} [Fintype ι]
    (p : ι → CouplingParameters) (enabled right : ι → Bool) :
    Measure.pi (fun i => (p i).selectedLaw (enabled i) (right i)) =
      (Measure.pi (fun _ : ι => unitIntervalMeasure)).withDensity
        (fun x => ENNReal.ofReal (finiteProductDensity p enabled right x)) := by
  classical
  apply Measure.pi_eq
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
  have hnon (x : ι → ℝ) : 0 ≤ finiteProductDensity p enabled right x :=
    Finset.prod_nonneg fun i _ => (p i).selectedDensity_nonneg (enabled i) (right i) (x i)
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((finiteProductDensity_memLp p enabled right).integrable (by norm_num)).restrict
    (Filter.Eventually.of_forall hnon)]
  rw [Measure.restrict_pi_pi]
  unfold finiteProductDensity
  rw [integral_fintype_prod_eq_prod (fun i => (p i).selectedDensity (enabled i) (right i))]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
    ((p i).selectedDensity_nonneg (enabled i) (right i)))]
  apply Finset.prod_congr rfl
  intro i _
  exact ((p i).selectedLaw_apply_integral (enabled i) (right i) (hS i)).symm

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_ProductKernel
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Finset MeasurableSpace
open scoped ENNReal
noncomputable section

theorem independentKernel_pi {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (κ i)]
    (x : ∀ i, X i) (I : Finset ι) (S : ∀ i, Set (Y i))
    (hS : ∀ i ∈ I, MeasurableSet (S i)) :
    independentKernel κ x (Set.pi (I : Set ι) S) = ∏ i ∈ I, κ i (x i) (S i) :=
  Measure.infinitePi_pi _ hS

theorem lintegral_infinitePi_finset_prod {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i ∈ I, f i (x i) ∂Measure.infinitePi μ) = ∏ i ∈ I, ∫⁻ t, f i t ∂μ i := by
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun I
    (fun (i : ι) (x : ∀ i, X i) => f i (x i)) (iIndepFun_infinitePi (P := μ) (X := f) hf)
    (fun i => (hf i).comp (measurable_pi_apply i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (measurePreserving_eval_infinitePi μ i).lintegral_comp (hf i)

/-- Full-vector disintegration commutes with an arbitrary independent product.
The equality is of measures on all measurable sets, not just rectangles. -/
theorem independentKernel_compProd {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (κ : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    ((Measure.infinitePi μ) ⊗ₘ (independentKernel κ)).map
      (fun z i => (z.1 i, z.2 i)) = Measure.infinitePi (fun i => (μ i) ⊗ₘ (κ i)) := by
  have hm : Measurable (fun z : (∀ i, X i) × (∀ i, Y i) => fun i => (z.1 i, z.2 i)) := by
    fun_prop
  apply Measure.eq_infinitePi
  intro I S hS
  rw [Measure.map_apply hm (MeasurableSet.pi I.countable_toSet (fun i _ => hS i)),
    Measure.compProd_apply (hm (MeasurableSet.pi I.countable_toSet (fun i _ => hS i)))]
  have he (x : ∀ i, X i) : Prod.mk x ⁻¹' ((fun (z : (∀ i, X i) × (∀ i, Y i)) i => (z.1 i, z.2 i)) ⁻¹' Set.pi (I : Set ι) S) =
      Set.pi (I : Set ι) (fun i => Prod.mk (x i) ⁻¹' S i) := rfl
  simp_rw [he, independentKernel_pi κ _ I _ (fun i _ => measurable_prodMk_left (hS i))]
  rw [lintegral_infinitePi_finset_prod μ I
    (fun i t => κ i t (Prod.mk t ⁻¹' S i)) (fun i => Kernel.measurable_kernel_prodMk_left (hS i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (Measure.compProd_apply (hS i)).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_VectorBayes
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
noncomputable section
namespace CouplingParameters

theorem orientPair_measurable (right : Bool) : Measurable (orientPair right) :=
  (endpoint_measurable right).prodMk (endpoint_measurable (!right))

theorem posterior_compProd (p : CouplingParameters) (right : Bool) :
    (p.selectedLaw true right) ⊗ₘ (p.posteriorKernel right) =
      p.coupling.map (orientPair right) := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.compProd_apply_prod hA hB, selectedLaw_endpoint,
    Measure.map_apply (orientPair_measurable right) (hA.prod hB)]
  cases right
  · exact p.conditional_given_x hA hB
  · have he : orientPair true ⁻¹' (A ×ˢ B) = B ×ˢ A := by
      ext z
      simp [orientPair, endpoint, and_comm]
    rw [he]
    exact p.conditional_given_y hA hB

theorem vectorEndpoint_law {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool) :
    (vectorCoupling p).map (vectorEndpoint right) =
      Measure.infinitePi (fun i => (p i).selectedLaw true (right i)) := by
  unfold vectorCoupling vectorEndpoint
  rw [Measure.infinitePi_map_pi _
    (f := fun i (z : Fin 6 × (ℝ × ℝ)) => endpoint (right i) z.2)
    (fun i => (endpoint_measurable (right i)).comp measurable_snd)]
  simp_rw [labelled_endpoint_density]
  rfl

/-- The product posterior is the conditional law given the entire selected
endpoint vector. This identity holds for the actual augmented product law. -/
theorem vectorPosterior_disintegration {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool) :
    ((vectorCoupling p).map (vectorEndpoint right)) ⊗ₘ (vectorPosterior p right) =
      (vectorCoupling p).map (fun ω => (vectorEndpoint right ω, vectorEndpoint (fun i => !right i) ω)) := by
  rw [vectorEndpoint_law]
  have hh := independentKernel_compProd (fun i => (p i).selectedLaw true (right i))
    (fun i => (p i).posteriorKernel (right i))
  simp_rw [posterior_compProd] at hh
  let zip : (ι → ℝ) × (ι → ℝ) → (ι → ℝ × ℝ) := fun z i => (z.1 i, z.2 i)
  let unzip : (ι → ℝ × ℝ) → (ι → ℝ) × (ι → ℝ) := fun z => (fun i => (z i).1, fun i => (z i).2)
  have hz : Measurable zip := by fun_prop
  have hu : Measurable unzip := by fun_prop
  have hleft := congrArg (fun ν : Measure (ι → ℝ × ℝ) => ν.map unzip) hh
  rw [Measure.map_map hu hz] at hleft
  have hid : unzip ∘ zip = id := rfl
  rw [hid, Measure.map_id] at hleft
  change _ = (Measure.infinitePi (fun i => (p i).coupling.map (orientPair (right i)))).map unzip at hleft
  unfold vectorPosterior
  rw [hleft]
  have hp : (vectorCoupling p).map (fun ω i => orientPair (right i) (ω i).2) =
      Measure.infinitePi (fun i => (p i).coupling.map (orientPair (right i))) := by
    unfold vectorCoupling
    rw [Measure.infinitePi_map_pi _
      (f := fun i (z : Fin 6 × (ℝ × ℝ)) => orientPair (right i) z.2)
      (fun i => (orientPair_measurable (right i)).comp measurable_snd)]
    congr 1
    funext i
    unfold coupling
    rw [Measure.map_map (orientPair_measurable (right i)) measurable_snd]
    rfl
  have hv : Measurable (fun (ω : ι → Fin 6 × (ℝ × ℝ)) i => orientPair (right i) (ω i).2) :=
    Measurable.of_eval (fun i => (orientPair_measurable (right i)).comp
      (measurable_snd.comp (measurable_pi_apply i)))
  rw [← hp, Measure.map_map hu hv]
  rfl

/-- Full-vector conditional independence, including both endpoint orientations.
Together with vectorPosterior_disintegration this is independence under the
actual conditional law, not a statement about a separately chosen product. -/
theorem vectorPosterior_independence {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool)
    (x : ι → ℝ) (I : Finset ι) (S : ι → Set ℝ) (hS : ∀ i ∈ I, MeasurableSet (S i)) :
    vectorPosterior p right x (Set.pi (I : Set ι) S) =
      ∏ i ∈ I, (p i).posteriorKernel (right i) (x i) (S i) :=
  independentKernel_pi _ x I S hS

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_ProductDensityLimit
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

/-- Nested orthogonal projections with bounded squared norms converge strongly.
For product densities, normalization supplies the displayed inner identity. -/
theorem exists_limit_of_nested_inner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : ℕ → E) (C : ℝ)
    (hbound : ∀ n, ‖f n‖ ^ 2 ≤ C)
    (hinner : ∀ n m, n ≤ m → inner ℝ (f n) (f m) = ‖f n‖ ^ 2) :
    ∃ g : E, Tendsto f atTop (𝓝 g) ∧ ‖g‖ ^ 2 ≤ C := by
  have hdist (n m : ℕ) (hnm : n ≤ m) :
      ‖f m - f n‖ ^ 2 = ‖f m‖ ^ 2 - ‖f n‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm, hinner n m hnm]
    ring
  have hmono : Monotone (fun n => ‖f n‖ ^ 2) := by
    intro n m hnm
    have := sq_nonneg ‖f m - f n‖
    rw [hdist n m hnm] at this
    linarith
  have hbdd : BddAbove (Set.range (fun n => ‖f n‖ ^ 2)) := ⟨C, by
    rintro _ ⟨n, rfl⟩; exact hbound n⟩
  have hc := (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  have hf : CauchySeq f := by
    rw [Metric.cauchySeq_iff] at hc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε^2) (sq_pos_of_pos hε)
    refine ⟨N, fun n hn m hm => ?_⟩
    have hh := hN n hn m hm
    rw [Real.dist_eq] at hh
    rw [dist_eq_norm]
    rcases le_total n m with hnm | hmn
    · have hd := hdist n m hnm
      rw [norm_sub_rev] at hd
      have hle := le_abs_self (‖f m‖ ^ 2 - ‖f n‖ ^ 2)
      rw [abs_sub_comm] at hh
      nlinarith [norm_nonneg (f n - f m)]
    · have hd := hdist m n hmn
      have hle := le_abs_self (‖f n‖ ^ 2 - ‖f m‖ ^ 2)
      nlinarith [norm_nonneg (f n - f m)]
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hf
  exact ⟨g, hg, le_of_tendsto (hg.norm.pow 2) (Eventually.of_forall hbound)⟩

theorem l2_norm_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Lp ℝ 2 μ) : ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, sq]

theorem l2_inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]

theorem l2_tendsto_setIntegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ}
    (h : Tendsto f atTop (𝓝 g)) {S : Set Ω} (hS : MeasurableSet S) :
    Tendsto (fun n => ∫ x in S, f n x ∂μ) atTop (𝓝 (∫ x in S, g x ∂μ)) := by
  have ht := tendsto_const_nhds.inner h
    (𝕜 := ℝ) (x := indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℝ))
  simpa only [L2.inner_indicatorConstLp_eq_setIntegral_inner,
    RCLike.inner_apply, conj_trivial, mul_one] using ht

/-- An actual nonnegative L2 function, obtained by completeness, with convergence
of integrals on every measurable set. No limiting density is assumed. -/
theorem exists_nonneg_L2_limit {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (f : ℕ → Ω → ℝ) (hf : ∀ n, MemLp (f n) 2 μ)
    (hnon : ∀ n, ∀ᵐ x ∂μ, 0 ≤ f n x) (C : ℝ)
    (hbound : ∀ n, (∫ x, f n x ^ 2 ∂μ) ≤ C)
    (hinner : ∀ n m, n ≤ m → (∫ x, f n x * f m x ∂μ) = ∫ x, f n x ^ 2 ∂μ) :
    ∃ g : Ω → ℝ, MemLp g 2 μ ∧ (∀ᵐ x ∂μ, 0 ≤ g x) ∧
      (∫ x, g x ^ 2 ∂μ) ≤ C ∧
      ∀ S, MeasurableSet S →
        Tendsto (fun n => ∫ x in S, f n x ∂μ) atTop (𝓝 (∫ x in S, g x ∂μ)) := by
  let F (n : ℕ) := (hf n).toLp (f n)
  have hsq (n : ℕ) : ‖F n‖ ^ 2 = ∫ x, f n x ^ 2 ∂μ := by
    rw [l2_norm_sq]
    exact integral_congr_ae ((hf n).coeFn_toLp.mono fun x hx => congrArg (fun r : ℝ => r^2) hx)
  obtain ⟨g, hg, hgb⟩ := exists_limit_of_nested_inner F C
    (fun n => (hsq n).trans_le (hbound n)) (fun n m hnm => by
      rw [l2_inner_toLp, hinner n m hnm, hsq n])
  have hsets (S : Set Ω) (hS : MeasurableSet S) :
      Tendsto (fun n => ∫ x in S, f n x ∂μ) atTop (𝓝 (∫ x in S, g x ∂μ)) := by
    have heq (n : ℕ) : (∫ x in S, F n x ∂μ) = ∫ x in S, f n x ∂μ :=
      setIntegral_congr_ae hS ((hf n).coeFn_toLp.mono fun x hx _ => hx)
    simpa only [heq] using l2_tendsto_setIntegral hg hS
  refine ⟨g, (Lp.memLp g), ?_, (l2_norm_sq g) ▸ hgb, hsets⟩
  exact ae_nonneg_of_forall_setIntegral_nonneg ((Lp.memLp g).integrable (by norm_num))
    (fun S hS _ => ge_of_tendsto (hsets S hS)
      (Eventually.of_forall fun n => integral_nonneg_of_ae (ae_restrict_of_ae (hnon n))))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Prefix
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

/-- Finite-coordinate factorization under the actual infinite product measure. -/
theorem integral_infinitePi_finset_prod {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (I : Finset ι) (f : ∀ i, X i → ℝ) (hf : ∀ i, Measurable (f i)) :
    (∫ x, ∏ i ∈ I, f i (x i) ∂Measure.infinitePi μ) = ∏ i ∈ I, ∫ t, f i t ∂μ i := by
  classical
  have he (x : ∀ i, X i) : (∏ i ∈ I, f i (x i)) = ∏ i : I, f i (x i) :=
    (Finset.prod_coe_sort I (fun i => f i (x i))).symm
  simp_rw [he]
  change (∫ x, (∏ i : I, f i (I.restrict x i)) ∂Measure.infinitePi μ) = _
  rw [integral_restrict_infinitePi μ
    (f := fun x : ∀ i : I, X i => ∏ i : I, f i (x i))
    ((Finset.measurable_prod _ fun (i : I) _ => (hf i).comp (measurable_pi_apply i)).aestronglyMeasurable)]
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_coe_sort I (fun i => ∫ t, f i t ∂μ i)

namespace CouplingParameters
variable {ι : Type*}

theorem prefixDensity_measurable (p : ι → CouplingParameters) (right : ι → Bool) (I : Finset ι) :
    Measurable (prefixDensity p right I) :=
  Finset.measurable_prod _ fun i _ => ((p i).endpointDensity_measurable (right i)).comp (measurable_pi_apply i)

theorem prefixDensity_nonneg (p : ι → CouplingParameters) (right : ι → Bool)
    (I : Finset ι) (x : ι → ℝ) : 0 ≤ prefixDensity p right I x :=
  Finset.prod_nonneg fun i _ => ((p i).diagonalMass_pos.trans_le ((p i).endpointDensity_lower (right i) (x i))).le

theorem prefixDensity_memLp (p : ι → CouplingParameters) (right : ι → Bool) (I : Finset ι) :
    MemLp (prefixDensity p right I) 2 (Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) := by
  apply MemLp.of_bound (prefixDensity_measurable p right I).aestronglyMeasurable (10 ^ I.card)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (prefixDensity_nonneg p right I x)]
  calc
    _ ≤ ∏ i ∈ I, (10 : ℝ) := Finset.prod_le_prod
      (fun i _ => ((p i).diagonalMass_pos.trans_le ((p i).endpointDensity_lower (right i) (x i))).le)
      (fun i _ => ((p i).endpointDensity_lt_ten (right i) (x i)).le)
    _ = _ := by simp

theorem prefixDensity_sq_integral (p : ι → CouplingParameters) (right : ι → Bool) (I : Finset ι) :
    (∫ x, prefixDensity p right I x ^ 2 ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) =
      ∏ i ∈ I, ∫ t, (p i).endpointDensity (right i) t ^ 2 ∂unitIntervalMeasure := by
  simp only [prefixDensity, ← Finset.prod_pow]
  exact integral_infinitePi_finset_prod _ _ _ (fun i => ((p i).endpointDensity_measurable (right i)).pow_const 2)

theorem prefixDensity_energy (p : ι → CouplingParameters) (right : ι → Bool) (I : Finset ι) :
    (∫ x, prefixDensity p right I x ^ 2 ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) ≤
      Real.exp (∑ i ∈ I, 20*(2*(p i).kappa^2/(p i).m + (p i).tagMass)) := by
  classical
  rw [prefixDensity_sq_integral, ← Finset.prod_coe_sort I,
    ← Finset.sum_coe_sort I]
  exact product_energy_le_exp _ _ (fun i => integral_nonneg (fun _ => sq_nonneg _))
    (fun i => (p i).endpointDensity_source_energy (right i))

/-- Exact orthogonality identity for nested finite product densities. -/
theorem prefixDensity_inner (p : ι → CouplingParameters) (right : ι → Bool)
    {I J : Finset ι} (hIJ : I ⊆ J) :
    (∫ x, prefixDensity p right I x * prefixDensity p right J x
      ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) =
    ∫ x, prefixDensity p right I x ^ 2 ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure) := by
  classical
  have he (x : ι → ℝ) : prefixDensity p right I x * prefixDensity p right J x =
      ∏ i ∈ J, if i ∈ I then (p i).endpointDensity (right i) (x i)^2
        else (p i).endpointDensity (right i) (x i) := by
    have hi : prefixDensity p right I x = ∏ i ∈ J,
        if i ∈ I then (p i).endpointDensity (right i) (x i) else 1 := by
      rw [← Finset.prod_subset hIJ]
      · apply Finset.prod_congr rfl
        intro i hi
        simp [hi]
      · intro i _ hi
        simp [hi]
    rw [hi, prefixDensity, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    split <;> simp_all [sq]
  simp_rw [he]
  rw [integral_infinitePi_finset_prod (fun _ : ι => unitIntervalMeasure) J
    (fun i t => if i ∈ I then (p i).endpointDensity (right i) t ^ 2
      else (p i).endpointDensity (right i) t) (fun i => by
    split
    · exact ((p i).endpointDensity_measurable (right i)).pow_const 2
    · exact (p i).endpointDensity_measurable (right i)), prefixDensity_sq_integral]
  calc
    _ = ∏ i ∈ I, ∫ t, (if i ∈ I then (p i).endpointDensity (right i) t ^ 2
        else (p i).endpointDensity (right i) t) ∂unitIntervalMeasure := by
      symm
      apply Finset.prod_subset hIJ
      intro i _ hi
      simp [hi, endpointDensity_integral]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [hi]

/-- The lifted prefix density has exactly the finite endpoint law on every
Borel cylinder at that prefix. -/
theorem prefixDensity_cylinder (p : ι → CouplingParameters) (right : ι → Bool)
    (I : Finset ι) {S : Set (I → ℝ)} (hS : MeasurableSet S) :
    ENNReal.ofReal (∫ x in (I.restrict (π := fun _ : ι => ℝ)) ⁻¹' S, prefixDensity p right I x
      ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) =
      Measure.pi (fun i : I => (p i).selectedLaw true (right i)) S := by
  classical
  rw [finiteProductLaw_density, withDensity_apply _ hS]
  rw [← Measure.infinitePi_map_restrict (fun _ : ι => unitIntervalMeasure),
    setLIntegral_map hS (finiteProductDensity_measurable
      (fun i : I => p i) (fun _ => true) (fun i => right i)).ennreal_ofReal (measurable_restrict I)]
  have he (x : ι → ℝ) : finiteProductDensity (fun i : I => p i)
      (fun _ => true) (fun i => right i) ((I.restrict (π := fun _ : ι => ℝ)) x) = prefixDensity p right I x := by
    exact Finset.prod_coe_sort I (fun i => (p i).endpointDensity (right i) (x i))
  simp_rw [he]
  exact ofReal_integral_eq_lintegral_ofReal
    ((prefixDensity_memLp p right I).integrable (by norm_num)).restrict
    (Eventually.of_forall (prefixDensity_nonneg p right I))

/-- Enlarging the prefix does not change any earlier cylinder law. -/
theorem prefixDensity_cylinder_of_subset (p : ι → CouplingParameters) (right : ι → Bool)
    {J I : Finset ι} (hJI : J ⊆ I) {S : Set (J → ℝ)} (hS : MeasurableSet S) :
    ENNReal.ofReal (∫ x in (J.restrict (π := fun _ : ι => ℝ)) ⁻¹' S, prefixDensity p right I x
      ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) =
      Measure.pi (fun i : J => (p i).selectedLaw true (right i)) S := by
  have he : (J.restrict (π := fun _ : ι => ℝ)) ⁻¹' S = (I.restrict (π := fun _ : ι => ℝ)) ⁻¹' ((Finset.restrict₂ (π := fun _ : ι => ℝ) hJI : (I → ℝ) → (J → ℝ)) ⁻¹' S) := by
    rw [← Set.preimage_comp, Finset.restrict₂_comp_restrict hJI]
  rw [he, prefixDensity_cylinder p right I (hS.preimage (measurable_restrict₂ hJI))]
  have hh := congrArg (fun ν : Measure (J → ℝ) => ν S)
    (isProjectiveMeasureFamily_pi (fun i => (p i).selectedLaw true (right i)) I J hJI)
  rw [Measure.map_apply (show Measurable (Finset.restrict₂ (π := fun _ : ι => ℝ) hJI) from measurable_restrict₂ hJI) hS] at hh
  exact hh.symm

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Limit
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section
namespace CouplingParameters

/-- Uniformly square-integrable finite endpoint densities produce an actual
infinite-product density, with the same square-integral bound. -/
theorem infiniteEndpoint_density_of_prefix_bound {ι : Type*}
    (p : ι → CouplingParameters) (right : ι → Bool) (I : ℕ → Finset ι)
    (hmono : Monotone I) (hcover : ∀ J : Finset ι, ∃ n, J ⊆ I n)
    (C : ℝ) (hb : ∀ n, (∫ x, prefixDensity p right (I n) x ^ 2
      ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) ≤ C) :
    ∃ g : (ι → ℝ) → ℝ,
      MemLp g 2 (Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) ∧
      (∀ᵐ x ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure), 0 ≤ g x) ∧
      (∫ x, g x ^ 2 ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) ≤ C ∧
      Measure.infinitePi (fun i => (p i).selectedLaw true (right i)) =
        (Measure.infinitePi (fun _ : ι => unitIntervalMeasure)).withDensity
          (fun x => ENNReal.ofReal (g x)) := by
  let μ := Measure.infinitePi (fun _ : ι => unitIntervalMeasure)
  obtain ⟨g, hg, hnon, hgb, hsets⟩ := exists_nonneg_L2_limit
    (fun n => prefixDensity p right (I n))
    (fun n => prefixDensity_memLp p right (I n))
    (fun n => Eventually.of_forall (prefixDensity_nonneg p right (I n))) C hb
    (fun n m hnm => prefixDensity_inner p right (hmono hnm))
  refine ⟨g, hg, hnon, hgb, ?_⟩
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (p i).selectedLaw true (right i))).unique
  intro J
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_restrict J) hS,
    withDensity_apply _ (hS.preimage (measurable_restrict J)),
    ← ofReal_integral_eq_lintegral_ofReal (hg.integrable (by norm_num)).restrict
      (ae_restrict_of_ae hnon)]
  obtain ⟨N, hN⟩ := hcover J
  have he : ∀ n ≥ N, ENNReal.ofReal (∫ x in (J.restrict (π := fun _ : ι => ℝ)) ⁻¹' S,
      prefixDensity p right (I n) x ∂μ) =
      Measure.pi (fun i : J => (p i).selectedLaw true (right i)) S := by
    intro n hn
    exact prefixDensity_cylinder_of_subset p right (hN.trans (hmono hn)) hS
  have ht := (ENNReal.continuous_ofReal.tendsto _).comp
    (hsets ((J.restrict (π := fun _ : ι => ℝ)) ⁻¹' S) (hS.preimage (measurable_restrict J)))
  exact tendsto_nhds_unique ht (tendsto_atTop_of_eventually_const he)

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_BlockLimit
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section
namespace CouplingParameters

theorem mem_blockPrefix (m : ℕ → ℕ) (n : ℕ) (i : BlockCoordinate m) :
    i ∈ blockPrefix m n ↔ i.1 < n := by simp [blockPrefix]

theorem blockPrefix_mono (m : ℕ → ℕ) : Monotone (blockPrefix m) := by
  intro n k hnk i hi
  exact (mem_blockPrefix m k i).2 (lt_of_lt_of_le ((mem_blockPrefix m n i).1 hi) hnk)

theorem blockPrefix_cover (m : ℕ → ℕ) (J : Finset (BlockCoordinate m)) :
    ∃ n, J ⊆ blockPrefix m n := by
  refine ⟨J.sup (fun i => i.1) + 1, fun i hi => ?_⟩
  exact (mem_blockPrefix m _ i).2 (Nat.lt_succ_of_le (Finset.le_sup (f := fun i => i.1) hi))

theorem blockPrefix_energy (p : ℕ → CouplingParameters) (m : ℕ → ℕ)
    (hm : ∀ s, (p s).m = (m s : ℝ)) (j : ℕ)
    (htag : ∀ s, (p s).tagged = decide (s=j))
    (hκ : Summable (fun s => (p s).kappa^2))
    (right : BlockCoordinate m → Bool) (n : ℕ) :
    (∫ x, prefixDensity (fun i : BlockCoordinate m => p i.1) right (blockPrefix m n) x ^ 2
      ∂Measure.infinitePi (fun _ : BlockCoordinate m => unitIntervalMeasure)) ≤
      Real.exp (20*(2*(∑' s, (p s).kappa^2)+1)) := by
  apply (prefixDensity_energy _ right _).trans
  apply Real.exp_le_exp.mpr
  have heq : (∑ i ∈ blockPrefix m n, 20*(2*(p i.1).kappa^2/(p i.1).m + (p i.1).tagMass)) =
      20 * ∑ s ∈ Finset.range n, (p s).m * (2*(p s).kappa^2/(p s).m + (p s).tagMass) := by
    rw [blockPrefix, Finset.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [hm s]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (uniform_block_budget p j htag hκ (Finset.range n)) (by norm_num)

theorem infinite_block_source_density (p : ℕ → CouplingParameters) (m : ℕ → ℕ)
    (hm : ∀ s, (p s).m = (m s : ℝ)) (j : ℕ)
    (htag : ∀ s, (p s).tagged = decide (s=j))
    (hκ : ∀ s, (p s).kappa = sourceKappa s) (right : BlockCoordinate m → Bool) :
    ∃ g : (BlockCoordinate m → ℝ) → ℝ,
      MemLp g 2 (Measure.infinitePi (fun _ : BlockCoordinate m => unitIntervalMeasure)) ∧
      (∀ᵐ x ∂Measure.infinitePi (fun _ : BlockCoordinate m => unitIntervalMeasure), 0 ≤ g x) ∧
      (∫ x, g x ^ 2 ∂Measure.infinitePi (fun _ : BlockCoordinate m => unitIntervalMeasure)) ≤
        Real.exp (20*(2*(∑' s, sourceKappa s ^ 2)+1)) ∧
      Measure.infinitePi (fun i : BlockCoordinate m => (p i.1).selectedLaw true (right i)) =
        (Measure.infinitePi (fun _ : BlockCoordinate m => unitIntervalMeasure)).withDensity
          (fun x => ENNReal.ofReal (g x)) := by
  apply infiniteEndpoint_density_of_prefix_bound _ right (blockPrefix m)
    (blockPrefix_mono m) (blockPrefix_cover m)
  intro n
  have hs : Summable (fun s => (p s).kappa^2) := by simpa only [hκ] using sourceKappa_sq_summable
  simpa only [hκ] using blockPrefix_energy p m hm j htag hs right n

theorem blockProductEndpoint_law (p : ℕ → CouplingParameters) (m : ℕ → ℕ)
    (right : BlockCoordinate m → Bool) :
    (blockProductCoupling p m).map (blockProductEndpoint right) =
      Measure.infinitePi (fun i : BlockCoordinate m => (p i.1).selectedLaw true (right i)) := by
  unfold blockProductCoupling blockProductEndpoint
  rw [Measure.infinitePi_map_pi _ (f := fun (i : BlockCoordinate m) (z : Fin 6 × (ℝ × ℝ)) => endpoint (right i) z.2)
    (fun i => (endpoint_measurable (right i)).comp measurable_snd)]
  simp_rw [labelled_endpoint_density]
  rfl

/-- The density belongs to the actual law of the selected endpoint map, rather
than only to an abstract measure with matching finite moments. -/
theorem blockProductEndpoint_L2_density (p : ℕ → CouplingParameters) (m : ℕ → ℕ)
    (hm : ∀ s, (p s).m = (m s : ℝ)) (j : ℕ)
    (htag : ∀ s, (p s).tagged = decide (s=j))
    (hκ : ∀ s, (p s).kappa = sourceKappa s) (right : BlockCoordinate m → Bool) :
    ∃ g : (BlockCoordinate m → ℝ) → ℝ,
      MemLp g 2 (Measure.infinitePi (fun _ : BlockCoordinate m => unitIntervalMeasure)) ∧
      (∀ᵐ x ∂Measure.infinitePi (fun _ : BlockCoordinate m => unitIntervalMeasure), 0 ≤ g x) ∧
      (∫ x, g x ^ 2 ∂Measure.infinitePi (fun _ : BlockCoordinate m => unitIntervalMeasure)) ≤
        Real.exp (20*(2*(∑' s, sourceKappa s ^ 2)+1)) ∧
      (blockProductCoupling p m).map (blockProductEndpoint right) =
        (Measure.infinitePi (fun _ : BlockCoordinate m => unitIntervalMeasure)).withDensity
          (fun x => ENNReal.ofReal (g x)) := by
  rw [blockProductEndpoint_law]
  exact infinite_block_source_density p m hm j htag hκ right

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_StageCoupling
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal
noncomputable section

/-- Actual infinite endpoint densities for the recursively constructed source
coupling. There are no assumed scale, width, or density hypotheses. -/
theorem stagedCoupling_endpoint_L2_density (j : ℕ) (right : SourceCoordinate → Bool) :
    ∃ g : (SourceCoordinate → ℝ) → ℝ,
      MemLp g 2 (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ∧
      (∀ᵐ x ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure), 0 ≤ g x) ∧
      (∫ x, g x ^ 2 ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)) ≤
        Real.exp (20*(2*(∑' s, sourceKappa s ^ 2)+1)) ∧
      (CouplingParameters.blockProductCoupling (stagedCouplingParameters j) sourceBlockSize).map
          (CouplingParameters.blockProductEndpoint right) =
        (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)).withDensity
          (fun x => ENNReal.ofReal (g x)) :=
  CouplingParameters.blockProductEndpoint_L2_density (stagedCouplingParameters j) sourceBlockSize
    (fun _ => rfl) j (fun _ => rfl) (fun _ => rfl) right

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_Measures
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal Topology
noncomputable section

/-- A nonnegative measurable version of each actual marginal density. -/
theorem sourceBiasedEndpoint_density (j : ℕ) (r : SourceCoordinate → Bool) :
    ∃ g : (SourceCoordinate → ℝ) → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      MemLp g 2 sourceSamplingHaar ∧
      (sourceBiasedLaw j).map (sourceBiasedEndpoint r) =
        sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      (∫ x, g x^2 ∂sourceSamplingHaar) ≤ Real.exp (20*(2*(∑' s,sourceKappa s^2)+1)) := by
  obtain ⟨f,hf,hf0,hfC,hfm⟩ := stagedCoupling_endpoint_L2_density j r
  let g := fun x => max (hf.aestronglyMeasurable.mk f x) 0
  have hg : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max measurable_const
  have he : f =ᵐ[sourceSamplingHaar] g := by
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk,hf0] with x hx h0
    simp only [g,← hx,max_eq_left h0]
  refine ⟨g,hg,fun _ => le_max_right _ _,(memLp_congr_ae he).mp hf,?_,?_⟩
  · exact hfm.trans (withDensity_congr_ae (he.fun_comp ENNReal.ofReal))
  · exact (integral_congr_ae (he.mono fun x hx => congrArg (fun t : ℝ => t^2) hx)).symm.trans_le hfC

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BoundedMatrixOperator
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal Topology
noncomputable section

theorem fiberFiniteEmbedding_single (n : ℤ) (c : ℂ) :
    fiberFiniteEmbedding (Finsupp.single n c) = lp.single 2 n c := by
  simp [fiberFiniteEmbedding, ← lp.single_smul]

theorem fiberFiniteEmbedding_sum (a : ℤ →₀ ℂ) :
    fiberFiniteEmbedding a = ∑ n ∈ a.support, lp.single 2 n (a n) := by
  simp [fiberFiniteEmbedding, Finsupp.linearCombination_apply, Finsupp.sum, ← lp.single_smul]

theorem fiberFiniteEmbedding_norm_sq (a : ℤ →₀ ℂ) :
    ‖fiberFiniteEmbedding a‖ ^ 2 = ∑ n ∈ a.support, ‖a n‖ ^ 2 := by
  rw [fiberFiniteEmbedding_sum]
  simpa using lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num) a a.support

theorem fiberFiniteEmbedding_dense : DenseRange fiberFiniteEmbedding := by
  intro x
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ n ∈ s, Finsupp.single n (x n), ?_⟩
  simp [fiberFiniteEmbedding_single]

/-- Every bounded operator is determined by its coordinate matrix. -/
theorem fiberOperator_ext {A B : SourceFiberHilbert →L[ℂ] SourceFiberHilbert}
    (h : ∀ k n : ℤ, (A (lp.single 2 n (1 : ℂ))) k = (B (lp.single 2 n (1 : ℂ))) k) : A = B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  intro n
  apply ContinuousLinearMap.ext
  intro c
  apply Subtype.ext
  funext k
  change (A (lp.single 2 n c)) k = (B (lp.single 2 n c)) k
  have he : lp.single 2 n c = c • (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) := by
    simp [← lp.single_smul]
  rw [he, map_smul, map_smul]
  change c * (A (lp.single 2 n 1)) k = c * (B (lp.single 2 n 1)) k
  rw [h]

theorem fiberOperator_hasSum (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (v : SourceFiberHilbert) :
    HasSum (fun n : ℤ => v n • A (lp.single 2 n (1 : ℂ))) (A v) := by
  convert (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) v).map A A.continuous using 1
  funext n
  have he : lp.single 2 n (v n) = v n • (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) := by
    simp [← lp.single_smul]
  change v n • A (lp.single 2 n (1 : ℂ)) = A (lp.single 2 n (v n))
  rw [he, map_smul]

theorem fiberOperator_action (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (v : SourceFiberHilbert) (k : ℤ) :
    (A v) k = ∑' n : ℤ, (A (lp.single 2 n (1 : ℂ))) k * v n := by
  have h := (fiberOperator_hasSum A v).map
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k) (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous
  have he := h.tsum_eq.symm
  change (A v) k = ∑' n : ℤ, v n * (A (lp.single 2 n (1 : ℂ))) k at he
  simpa only [mul_comm] using he

variable (m : ℤ → ℤ → ℂ) (C : ℝ)
variable (hb : ∀ (s t : Finset ℤ) (a : ℤ → ℂ),
  (∑ k ∈ t, ‖∑ n ∈ s, a n * m k n‖ ^ 2) ≤ C ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2)

theorem fiberMatrixFinite_norm_le (hC : 0 ≤ C) (a : ℤ →₀ ℂ) :
    ‖fiberMatrixFinite m C hb a‖ ≤ C * ‖fiberFiniteEmbedding a‖ := by
  have he : ‖fiberMatrixFinite m C hb a‖ ^ 2 =
      ∑' k, ‖fiberMatrixLinear m a k‖ ^ 2 := by
    simpa [fiberMatrixFinite] using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
      (fiberMatrixFinite m C hb a)
  have hsum : (∑' k, ‖fiberMatrixLinear m a k‖ ^ 2) ≤
      C ^ 2 * ∑ n ∈ a.support, ‖a n‖ ^ 2 := by
    apply Real.tsum_le_of_sum_le
    · intro k; positivity
    · intro t; simpa [fiberMatrixLinear_apply] using hb a.support t a
  rw [← he, ← fiberFiniteEmbedding_norm_sq] at hsum
  have hpos := mul_nonneg hC (norm_nonneg (fiberFiniteEmbedding a))
  nlinarith [norm_nonneg (fiberMatrixFinite m C hb a)]

theorem boundedMatrixOperator_entry (hC : 0 ≤ C) (k n : ℤ) :
    (boundedMatrixOperator m C hb (lp.single 2 n (1 : ℂ))) k = m k n := by
  rw [← fiberFiniteEmbedding_single n 1]
  change ((fiberMatrixFinite m C hb).extendOfNorm fiberFiniteEmbedding
    (fiberFiniteEmbedding (Finsupp.single n 1))) k = _
  rw [LinearMap.extendOfNorm_eq fiberFiniteEmbedding_dense
    ⟨C, fiberMatrixFinite_norm_le m C hb hC⟩]
  change fiberMatrixLinear m (Finsupp.single n 1) k = _
  simp [fiberMatrixLinear]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiberSeparable
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Set TopologicalSpace
noncomputable section

/-- Separability of the actual l2(Z) fiber, from its countable coordinate basis. -/
instance sourceFiber_separable : TopologicalSpace.SeparableSpace SourceFiberHilbert := by
  let b : ℤ → SourceFiberHilbert := fun n => lp.single 2 n (1 : ℂ)
  let S := Submodule.span ℂ (Set.range b)
  have hmem (a : ℤ →₀ ℂ) : fiberFiniteEmbedding a ∈ S := by
    change (∑ n ∈ a.support, a n • b n) ∈ S
    exact Submodule.sum_mem S fun n _ => Submodule.smul_mem S (a n) (Submodule.subset_span ⟨n,rfl⟩)
  have hd : Dense (S : Set SourceFiberHilbert) := by
    intro x
    exact closure_mono (by rintro _ ⟨a,rfl⟩; exact hmem a) (fiberFiniteEmbedding_dense x)
  have hs : IsSeparable (closure (S : Set SourceFiberHilbert)) :=
    (Set.countable_range b).isSeparable.span.closure
  rw [hd.closure_eq] at hs
  exact isSeparable_univ_iff.mp hs

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Entries
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A product almost-everywhere identity holds on every integer fiber. -/
theorem source_ae_all_fibers {p : (SourceCoordinate → ℝ) × ℤ → Prop}
    (hp : ∀ᵐ z ∂sourceMeasure SourceCoordinate, p z) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ, p (x,n) := by
  exact (Measure.ae_ae_of_ae_prod hp).mono fun x hx => Measure.ae_count_iff.mp hx

theorem sourceBasis_coe (n : ℤ) : sourceBasis n =ᵐ[sourceMeasure SourceCoordinate]
    fun z => if z.2 = n then 1 else 0 := by
  filter_upwards [sourceFiberIndicator_coe Set.univ MeasurableSet.univ n] with z hz
  rw [show (sourceBasis n) z = _ from hz]
  by_cases hn : z.2 = n <;> simp [hn]

theorem sourceScalar_apply_ae (g : SourceBaseFunction) (f : SourceHilbert SourceCoordinate) :
    sourceScalar g f =ᵐ[sourceMeasure SourceCoordinate] fun z => g.toFun z.1 * f z := by
  filter_upwards [sourcePi_apply_ae (fun _ => 0) g f, sourceHilbert_cube] with z hz hc
  change (sourcePi (fun _ => 0) g f) z = _
  rw [hz]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) z.2 z.1 = z.1 := by
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  simp [sourcePiSymbol, he]

theorem sourceScalar_indicator_basis (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (n : ℤ) : sourceScalar (sourceBaseIndicator A hA) (sourceBasis n) =
      sourceFiberIndicator A hA n := by
  apply Lp.ext
  filter_upwards [sourceScalar_apply_ae (sourceBaseIndicator A hA) (sourceBasis n),
    sourceBasis_coe n, sourceFiberIndicator_coe A hA n] with z hs hb hi
  rw [hs, hb, hi]
  by_cases ha : z.1 ∈ A <;> by_cases hn : z.2 = n <;> simp [sourceBaseIndicator, ha, hn]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiberEnergy
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem source_norm_sq_integrable (f : SourceHilbert SourceCoordinate) :
    Integrable (fun z => ‖f z‖ ^ 2) (sourceMeasure SourceCoordinate) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

theorem sourceFiberEnergy_integrable (f : SourceHilbert SourceCoordinate) :
    Integrable (sourceFiberEnergy f) sourceBaseMeasure :=
  (source_norm_sq_integrable f).integral_prod_left

theorem source_norm_sq_integral (f : SourceHilbert SourceCoordinate) :
    ‖f‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂sourceMeasure SourceCoordinate := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := InnerProductSpace.norm_sq_eq_re_inner f
    _ = ∫ z, RCLike.re (inner ℂ (f z) (f z)) ∂sourceMeasure SourceCoordinate :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) f f)).symm
    _ = _ := by simp_rw [← InnerProductSpace.norm_sq_eq_re_inner]

theorem source_norm_sq_energy (f : SourceHilbert SourceCoordinate) :
    ‖f‖ ^ 2 = ∫ x, sourceFiberEnergy f x ∂sourceBaseMeasure := by
  rw [source_norm_sq_integral, integral_prod _ (source_norm_sq_integrable f)]
  rfl

/-- Measurable localization commutes with taking the squared fiber norm. -/
theorem sourceFiberEnergy_indicator (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (f : SourceHilbert SourceCoordinate) :
    sourceFiberEnergy (sourceScalar (sourceBaseIndicator A hA) f) =ᵐ[sourceBaseMeasure]
      A.indicator (sourceFiberEnergy f) := by
  filter_upwards [source_ae_all_fibers
    (sourceScalar_apply_ae (sourceBaseIndicator A hA) f)] with x hx
  unfold sourceFiberEnergy
  by_cases ha : x ∈ A
  · simp only [Set.indicator_of_mem ha]
    apply integral_congr_ae
    exact Eventually.of_forall fun n => by dsimp only; rw [hx]; simp [sourceBaseIndicator, ha]
  · simp only [Set.indicator_of_notMem ha]
    have he : (fun n : ℤ => ‖(sourceScalar (sourceBaseIndicator A hA) f) (x,n)‖ ^ 2) =
        fun _ => (0 : ℝ) := by
      funext n
      rw [hx]
      simp [sourceBaseIndicator, ha]
    rw [he, integral_zero]

theorem sourceScalar_indicator_norm_sq (A : Set (SourceCoordinate → ℝ))
    (hA : MeasurableSet A) (f : SourceHilbert SourceCoordinate) :
    ‖sourceScalar (sourceBaseIndicator A hA) f‖ ^ 2 =
      ∫ x in A, sourceFiberEnergy f x ∂sourceBaseMeasure := by
  rw [source_norm_sq_energy, integral_congr_ae (sourceFiberEnergy_indicator A hA f),
    integral_indicator hA]

theorem sourceAlgebra_fiberEnergy_le (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberEnergy (H f) x ≤ ‖H‖ ^ 2 * sourceFiberEnergy f x := by
  apply ae_le_of_forall_setIntegral_le (sourceFiberEnergy_integrable (H f))
    ((sourceFiberEnergy_integrable f).const_mul (‖H‖ ^ 2))
  intro A hA _
  rw [← sourceScalar_indicator_norm_sq A hA, integral_const_mul,
    ← sourceScalar_indicator_norm_sq A hA]
  have he : sourceScalar (sourceBaseIndicator A hA) (H f) =
      H (sourceScalar (sourceBaseIndicator A hA) f) :=
    congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate => T f)
      (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))
  rw [he]
  have hb := H.le_opNorm (sourceScalar (sourceBaseIndicator A hA) f)
  have hn := norm_nonneg (H (sourceScalar (sourceBaseIndicator A hA) f))
  have hp := mul_nonneg (norm_nonneg H)
    (norm_nonneg (sourceScalar (sourceBaseIndicator A hA) f))
  nlinarith [sq_nonneg (‖H‖ * ‖sourceScalar (sourceBaseIndicator A hA) f‖ -
    ‖H (sourceScalar (sourceBaseIndicator A hA) f)‖)]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiniteVectors
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceHilbert_sum_coe {ι : Type*} (s : Finset ι)
    (f : ι → SourceHilbert SourceCoordinate) :
    ⇑(∑ i ∈ s, f i : SourceHilbert SourceCoordinate) =ᵐ[sourceMeasure SourceCoordinate] fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℂ 2 (sourceMeasure SourceCoordinate)] with z hz
    exact hz
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with z ha hs
    simp only [ha, Pi.add_apply, hs]

theorem sourceFiniteVector_coe (s : Finset ℤ) (a : ℤ → ℂ) :
    sourceFiniteVector s a =ᵐ[sourceMeasure SourceCoordinate]
      fun z => if z.2 ∈ s then a z.2 else 0 := by
  have hs : ∀ᵐ z ∂sourceMeasure SourceCoordinate, ∀ n : ℤ,
      (a n • sourceBasis n) z = a n * (if z.2 = n then 1 else 0) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (a n) (sourceBasis n), sourceBasis_coe n] with z hc hb
    simp only [hc, Pi.smul_apply, smul_eq_mul, hb]
  filter_upwards [sourceHilbert_sum_coe s (fun n => a n • sourceBasis n), hs] with z hz hs
  change (∑ n ∈ s, a n • sourceBasis n) z = _
  rw [hz]
  simp_rw [hs, mul_ite, mul_one, mul_zero]
  simp

theorem sourceFiniteVector_image_coe
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (s : Finset ℤ) (a : ℤ → ℂ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      (H (sourceFiniteVector s a)) (x,k) = ∑ n ∈ s, a n * sourceMatrixEntry H k n x := by
  have hs : ∀ᵐ z ∂sourceMeasure SourceCoordinate, ∀ n : ℤ,
      (a n • H (sourceBasis n)) z = a n * (H (sourceBasis n)) z := by
    rw [ae_all_iff]
    intro n
    exact Lp.coeFn_smul (a n) (H (sourceBasis n))
  have he : H (sourceFiniteVector s a) = ∑ n ∈ s, a n • H (sourceBasis n) := by
    simp [sourceFiniteVector]
  rw [he]
  filter_upwards [source_ae_all_fibers (sourceHilbert_sum_coe s (fun n => a n • H (sourceBasis n))),
    source_ae_all_fibers hs] with x he hs k
  rw [he]
  exact Finset.sum_congr rfl fun n _ => hs k n

theorem sourceFiniteVector_energy (s : Finset ℤ) (a : ℤ → ℂ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberEnergy (sourceFiniteVector s a) x = ∑ n ∈ s, ‖a n‖ ^ 2 := by
  filter_upwards [source_ae_all_fibers (sourceFiniteVector_coe s a)] with x hx
  unfold sourceFiberEnergy
  have he : (fun n : ℤ => ‖(sourceFiniteVector s a) (x,n)‖ ^ 2) =
      (s : Set ℤ).indicator (fun n => ‖a n‖ ^ 2) := by
    funext n
    rw [hx]
    by_cases hn : n ∈ s <;> simp [hn]
  rw [he, integral_indicator s.measurableSet, setIntegral_finset]
  · simp [measureReal_def]
  · rw [← (s : Set ℤ).biUnion_of_singleton]
    simp [integrableOn_finset_iUnion, integrableOn_singleton_iff]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Bounds
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Continuity in a separable parameter lets a countable dense family of
almost-everywhere inequalities determine every parameter on one conull set. -/
theorem ae_forall_le_of_continuous {X E : Type*} [MeasurableSpace X]
    (μ : Measure X) [TopologicalSpace E] [TopologicalSpace.SeparableSpace E]
    (f g : E → X → ℝ) (hf : ∀ x, Continuous (fun e => f e x))
    (hg : ∀ x, Continuous (fun e => g e x))
    (h : ∀ e, ∀ᵐ x ∂μ, f e x ≤ g e x) :
    ∀ᵐ x ∂μ, ∀ e, f e x ≤ g e x := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense E
  have hs : ∀ᵐ x ∂μ, ∀ e ∈ s, f e x ≤ g e x :=
    (ae_ball_iff hsc).mpr fun e _ => h e
  filter_upwards [hs] with x hx e
  exact le_on_closure hx (hf x).continuousOn (hg x).continuousOn (hsd e)

theorem sourceFiberEnergy_finite_le (f : SourceHilbert SourceCoordinate) (s : Finset ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∑ n ∈ s, ‖f (x,n)‖ ^ 2 ≤ sourceFiberEnergy f x := by
  filter_upwards [(source_norm_sq_integrable f).prod_right_ae] with x hx
  have h := setIntegral_le_integral (μ := Measure.count) (s := (s : Set ℤ))
    hx (Eventually.of_forall fun n => sq_nonneg ‖f (x,n)‖)
  rw [setIntegral_finset s hx.integrableOn] at h
  simpa [measureReal_def, sourceFiberEnergy] using h

/-- Each finite scalar matrix compression satisfies the actual operator norm bound. -/
theorem sourceMatrix_finite_bound (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (s t : Finset ℤ) (a : ℤ → ℂ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2) ≤
        ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  filter_upwards [sourceFiniteVector_image_coe H s a,
    sourceFiniteVector_energy s a,
    sourceFiberEnergy_finite_le (H (sourceFiniteVector s a)) t,
    sourceAlgebra_fiberEnergy_le θ hH (sourceFiniteVector s a)] with x hc he hf hh
  calc
    _ = ∑ k ∈ t, ‖(H (sourceFiniteVector s a)) (x,k)‖ ^ 2 := by simp_rw [hc]
    _ ≤ sourceFiberEnergy (H (sourceFiniteVector s a)) x := hf
    _ ≤ ‖H‖ ^ 2 * sourceFiberEnergy (sourceFiniteVector s a) x := hh
    _ = _ := by rw [he]

/-- One conull set works for every complex finite input vector and every finite
output truncation. No field or boundedness hypothesis has been substituted. -/
theorem sourceMatrix_finite_bound_all (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ (s t : Finset ℤ) (a : ℤ → ℂ),
      (∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2) ≤
        ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  rw [ae_all_iff]
  intro s
  rw [ae_all_iff]
  intro t
  apply ae_forall_le_of_continuous (E := ℤ → ℂ) sourceBaseMeasure
    (fun a x => ∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2)
    (fun a _ => ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2)
  · intro x; fun_prop
  · intro x; fun_prop
  · exact sourceMatrix_finite_bound θ hH s t

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Integrals
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem source_fiber_restrict (A : Set (SourceCoordinate → ℝ)) (n : ℤ) :
    (sourceMeasure SourceCoordinate).restrict (A ×ˢ {n}) =
      (sourceBaseMeasure.restrict A).map (fun x => (x,n)) := by
  rw [← Measure.prod_restrict]
  simp only [Measure.restrict_singleton, Measure.count_singleton, one_smul]
  exact Measure.prod_dirac _

theorem source_fiber_integral (f : SourceHilbert SourceCoordinate)
    (A : Set (SourceCoordinate → ℝ)) (n : ℤ) :
    ∫ z in A ×ˢ {n}, f z ∂sourceMeasure SourceCoordinate =
      ∫ x in A, f (x,n) ∂sourceBaseMeasure := by
  rw [source_fiber_restrict]
  exact integral_map (measurable_id.prodMk measurable_const).aemeasurable
    (Lp.stronglyMeasurable f).aestronglyMeasurable

theorem source_fiber_integrable (f : SourceHilbert SourceCoordinate) (n : ℤ) :
    Integrable (fun x => f (x,n)) sourceBaseMeasure := by
  have hi := integrableOn_Lp_of_measure_ne_top f (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (sourceFiberMeasure_ne_top Set.univ n)
  rw [IntegrableOn, source_fiber_restrict, Measure.restrict_univ] at hi
  exact (integrable_map_measure (Lp.stronglyMeasurable f).aestronglyMeasurable
    (measurable_id.prodMk measurable_const).aemeasurable).mp hi

theorem sourceMatrixEntry_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Measurable (sourceMatrixEntry H k n) :=
  (Lp.stronglyMeasurable (H (sourceBasis n))).measurable.comp
    (measurable_id.prodMk measurable_const)

theorem sourceMatrixEntry_integrable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Integrable (sourceMatrixEntry H k n) sourceBaseMeasure :=
  source_fiber_integrable _ _

theorem sourceMatrixEntry_setIntegral
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (k n : ℤ) :
    ∫ x in A, sourceMatrixEntry H k n x ∂sourceBaseMeasure =
      inner ℂ (sourceFiberIndicator A hA k) (H (sourceBasis n)) := by
  rw [sourceFiberIndicator, L2.inner_indicatorConstLp_one, source_fiber_integral]
  rfl

/-- Adjoint matrix coefficients agree almost everywhere, on the actual source base. -/
theorem sourceMatrixEntry_star (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (k n : ℤ) :
    sourceMatrixEntry (star H) k n =ᵐ[sourceBaseMeasure]
      fun x => star (sourceMatrixEntry H n k x) := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (sourceMatrixEntry_integrable _ _ _)
    (Complex.conjCLE.integrable_comp_iff.mpr (sourceMatrixEntry_integrable H n k))
  intro A hA _
  change (∫ x in A, sourceMatrixEntry (star H) k n x ∂sourceBaseMeasure) =
    ∫ x in A, conj (sourceMatrixEntry H n k x) ∂sourceBaseMeasure
  rw [sourceMatrixEntry_setIntegral _ A hA, integral_conj, sourceMatrixEntry_setIntegral _ A hA,
    inner_conj_symm]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have he : H (sourceFiberIndicator A hA k) =
      sourceScalar (sourceBaseIndicator A hA) (H (sourceBasis k)) := by
    rw [← sourceScalar_indicator_basis]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis k)) (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))).symm
  rw [he]
  have hs : star (sourceScalar (sourceBaseIndicator A hA)) =
      sourceScalar (sourceBaseIndicator A hA) := by
    rw [sourceScalar_star]
    congr 1
    unfold sourceBaseStar sourceBaseIndicator
    congr 1
    funext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    hs, sourceScalar_indicator_basis]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OperatorField
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceFieldGoodSet_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    MeasurableSet (sourceFieldGoodSet H) := (measurableSet_toMeasurable _ _).compl

theorem sourceFieldGoodSet_ae (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) : ∀ᵐ x ∂sourceBaseMeasure, x ∈ sourceFieldGoodSet H := by
  have hb : ∀ᵐ x ∂sourceBaseMeasure, sourceMatrixGood H x := sourceMatrix_finite_bound_all θ hH
  rw [ae_iff] at hb ⊢
  simpa [sourceFieldGoodSet, measure_toMeasurable] using hb

theorem sourceOperatorField_entry
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) (x) :
    (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k =
      (sourceFieldGoodSet H).indicator (sourceMatrixEntry H k n) x := by
  classical
  unfold sourceOperatorField
  split_ifs with hx
  · rw [Set.indicator_of_mem hx]
    exact boundedMatrixOperator_entry _ _ _ (norm_nonneg H) k n
  · simp [hx]

theorem sourceOperatorField_entry_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Measurable (fun x => (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k) := by
  simp_rw [sourceOperatorField_entry]
  exact (sourceMatrixEntry_measurable H k n).indicator (sourceFieldGoodSet_measurable H)

/-- Field entries recover the original coefficients on one conull set. -/
theorem sourceOperatorField_entries_ae (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k n : ℤ,
      (sourceOperatorField H x (lp.single 2 n (1 : ℂ))) k = sourceMatrixEntry H k n x := by
  filter_upwards [sourceFieldGoodSet_ae θ hH] with x hx k n
  rw [sourceOperatorField_entry, Set.indicator_of_mem hx]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Action
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceFiberInner_integrable (f g : SourceHilbert SourceCoordinate) :
    Integrable (sourceFiberInner f g) sourceBaseMeasure :=
  (L2.integrable_inner (𝕜 := ℂ) f g).integral_prod_left

theorem source_inner_fiber (f g : SourceHilbert SourceCoordinate) :
    inner ℂ f g = ∫ x, sourceFiberInner f g x ∂sourceBaseMeasure :=
  integral_prod _ (L2.integrable_inner (𝕜 := ℂ) f g)

theorem sourceScalar_indicator_inner (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A)
    (f g : SourceHilbert SourceCoordinate) :
    inner ℂ (sourceScalar (sourceBaseIndicator A hA) f) g =
      ∫ x in A, sourceFiberInner f g x ∂sourceBaseMeasure := by
  rw [source_inner_fiber, ← integral_indicator hA]
  apply integral_congr_ae
  filter_upwards [source_ae_all_fibers (sourceScalar_apply_ae (sourceBaseIndicator A hA) f)] with x hx
  unfold sourceFiberInner
  by_cases ha : x ∈ A
  · simp only [Set.indicator_of_mem ha]
    apply integral_congr_ae
    exact Eventually.of_forall fun n => by dsimp only; rw [hx]; simp [sourceBaseIndicator, ha]
  · simp only [Set.indicator_of_notMem ha]
    have he : (fun n : ℤ => inner ℂ ((sourceScalar (sourceBaseIndicator A hA) f) (x,n)) (g (x,n))) =
        fun _ => (0 : ℂ) := by
      funext n
      rw [hx]
      simp [sourceBaseIndicator, ha]
    rw [he, integral_zero]

/-- The scalar distribution identity determining every output coordinate of H. -/
theorem source_coordinate_action_inner (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    (fun x => (H f) (x,k)) =ᵐ[sourceBaseMeasure]
      sourceFiberInner ((star H) (sourceBasis k)) f := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (source_fiber_integrable _ _)
    (sourceFiberInner_integrable _ _)
  intro A hA _
  rw [← source_fiber_integral, ← L2.inner_indicatorConstLp_one]
  change inner ℂ (sourceFiberIndicator A hA k) (H f) = _
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint]
  have he : (star H) (sourceFiberIndicator A hA k) =
      sourceScalar (sourceBaseIndicator A hA) ((star H) (sourceBasis k)) := by
    rw [← sourceScalar_indicator_basis]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis k)) (sourceAlgebra_commutes_scalar θ (star_mem hH)
      (sourceBaseIndicator A hA))).symm
  rw [he, sourceScalar_indicator_inner]

/-- Actual action on arbitrary L2 input, expressed through the constructed
matrix entries. The counting integral is an absolutely convergent series a.e. -/
theorem sourceMatrix_action (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    (fun x => (H f) (x,k)) =ᵐ[sourceBaseMeasure]
      fun x => ∫ n : ℤ, sourceMatrixEntry H k n x * f (x,n) ∂Measure.count := by
  have hs : ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ,
      sourceMatrixEntry (star H) n k x = star (sourceMatrixEntry H k n x) := by
    rw [ae_all_iff]
    intro n
    exact sourceMatrixEntry_star θ hH n k
  filter_upwards [source_coordinate_action_inner θ hH f k, hs] with x hx hs
  rw [hx]
  unfold sourceFiberInner
  apply integral_congr_ae
  exact Eventually.of_forall fun n => by
    change inner ℂ (sourceMatrixEntry (star H) n k x) (f (x,n)) = _
    rw [hs]
    simp [RCLike.inner_apply, mul_comm]

/-- The matrix action is absolutely integrable over the counting measure. -/
theorem sourceMatrix_action_integrable (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      Integrable (fun n : ℤ => sourceMatrixEntry H k n x * f (x,n)) Measure.count := by
  have hs : ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ,
      sourceMatrixEntry (star H) n k x = star (sourceMatrixEntry H k n x) := by
    rw [ae_all_iff]
    intro n
    exact sourceMatrixEntry_star θ hH n k
  filter_upwards [(L2.integrable_inner (𝕜 := ℂ) ((star H) (sourceBasis k)) f).prod_right_ae,
    hs] with x hi hs
  apply hi.congr
  exact Eventually.of_forall fun n => by
    change inner ℂ (sourceMatrixEntry (star H) n k x) (f (x,n)) = _
    rw [hs]
    simp [RCLike.inner_apply, mul_comm]

theorem sourceMatrix_action_tsum (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) (k : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (H f) (x,k) = ∑' n : ℤ, sourceMatrixEntry H k n x * f (x,n) := by
  filter_upwards [sourceMatrix_action θ hH f k, sourceMatrix_action_integrable θ hH f k]
    with x hx hi
  rw [hx, integral_countable hi]
  simp [measureReal_def]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FieldRepresentation
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Fubini puts almost every actual L2 section in l2(Z). -/
theorem source_fiber_memℓp (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure, Memℓp (fun n : ℤ => f (x,n)) 2 := by
  filter_upwards [(source_norm_sq_integrable f).prod_right_ae] with x hx
  apply memℓp_gen
  have hs := integrable_count_iff.mp hx
  simpa only [norm_pow, norm_norm, ENNReal.toReal_ofNat, Real.rpow_two] using hs

theorem sourceFiberVector_coe (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ n : ℤ, sourceFiberVector f x n = f (x,n) := by
  filter_upwards [source_fiber_memℓp f] with x hx n
  simp [sourceFiberVector, hx]

/-- The constructed field acts as the original operator on every source L2
vector. Neither decomposability nor a replacement representation is assumed. -/
theorem sourceOperatorField_represents (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (f : SourceHilbert SourceCoordinate) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceFiberVector (H f) x = sourceOperatorField H x (sourceFiberVector f x) := by
  have ha : ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      (H f) (x,k) = ∑' n : ℤ, sourceMatrixEntry H k n x * f (x,n) := by
    rw [ae_all_iff]
    exact sourceMatrix_action_tsum θ hH f
  filter_upwards [sourceFiberVector_coe f, sourceFiberVector_coe (H f),
    sourceOperatorField_entries_ae θ hH, ha] with x hf hHf he ha
  apply Subtype.ext
  funext k
  rw [hHf, fiberOperator_action]
  simp_rw [he, hf]
  exact ha k

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FieldAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceFiberVector_basis (n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceFiberVector (sourceBasis n) x = lp.single 2 n (1 : ℂ) := by
  filter_upwards [sourceFiberVector_coe (sourceBasis n), source_ae_all_fibers (sourceBasis_coe n)]
    with x hf hb
  apply Subtype.ext
  funext k
  rw [hf, hb]
  by_cases hk : k = n
  · subst k; simp [lp.single_apply]
  · simp [lp.single_apply, hk]

theorem sourceOperatorField_mul (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A * B) x = sourceOperatorField A x * sourceOperatorField B x := by
  have h (n : ℤ) : ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A * B) x (lp.single 2 n (1 : ℂ)) =
        sourceOperatorField A x (sourceOperatorField B x (lp.single 2 n (1 : ℂ))) := by
    filter_upwards [sourceOperatorField_represents θ (mul_mem hA hB) (sourceBasis n),
      sourceOperatorField_represents θ hA (B (sourceBasis n)),
      sourceOperatorField_represents θ hB (sourceBasis n), sourceFiberVector_basis n]
      with x hab ha hb he
    rw [he] at hab hb
    change sourceFiberVector (A (B (sourceBasis n))) x = _ at hab
    rw [ha, hb] at hab
    exact hab.symm
  filter_upwards [ae_all_iff.mpr h] with x hx
  apply fiberOperator_ext
  intro k n
  exact congrArg (fun v : SourceFiberHilbert => v k) (hx n)

theorem fiberOperator_star_entry (A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (k n : ℤ) :
    ((star A) (lp.single 2 n (1 : ℂ))) k = star ((A (lp.single 2 k (1 : ℂ))) n) := by
  calc
    _ = inner ℂ (lp.single 2 k (1 : ℂ)) ((star A) (lp.single 2 n (1 : ℂ))) := by
      rw [lp.inner_single_left]; simp
    _ = inner ℂ (A (lp.single 2 k (1 : ℂ))) (lp.single 2 n (1 : ℂ)) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = _ := by rw [lp.inner_single_right]; simp [RCLike.inner_apply]

theorem sourceOperatorField_star (θ : SourceCoordinate → ℝ)
    {A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField (star A) x = star (sourceOperatorField A x) := by
  have hs : ∀ᵐ x ∂sourceBaseMeasure, ∀ k n : ℤ,
      sourceMatrixEntry (star A) k n x = star (sourceMatrixEntry A n k x) := by
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    exact sourceMatrixEntry_star θ hA k
  filter_upwards [sourceOperatorField_entries_ae θ hA,
    sourceOperatorField_entries_ae θ (star_mem hA), hs] with x ha hstar hs
  apply fiberOperator_ext
  intro k n
  rw [hstar, fiberOperator_star_entry, ha, hs]

/-- Every projection in the source algebra yields an actual measurable
orthogonal-projection field. -/
theorem sourceOperatorField_projection (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) :
    ∀ᵐ x ∂sourceBaseMeasure, IsStarProjection (sourceOperatorField p x) := by
  filter_upwards [sourceOperatorField_mul θ hp hp, sourceOperatorField_star θ hp] with x hm hs
  refine ⟨?_, ?_⟩
  · change sourceOperatorField p x * sourceOperatorField p x = sourceOperatorField p x
    rw [← hm, hproj.isIdempotentElem]
  · change star (sourceOperatorField p x) = sourceOperatorField p x
    rw [← hs, hproj.isSelfAdjoint.star_eq]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_TailEstimate
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A conditional probability bound controls any nonnegative integrable weight
measurable with respect to the conditioning sigma algebra. -/
theorem conditional_mask_integral_le [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ} {H : Set Ω} {δ : ℝ}
    (hf : Integrable f μ) (hfm : StronglyMeasurable[m] f)
    (hf0 : 0 ≤ᵐ[μ] f) (hH : @MeasurableSet Ω mΩ H)
    (hcond : ∀ᵐ ω ∂μ, μ[H.indicator (fun _ => (1 : ℝ)) | m] ω ≤ δ) :
    ∫ ω in H, f ω ∂μ ≤ δ * ∫ ω, f ω ∂μ := by
  let g : Ω → ℝ := H.indicator (fun _ => 1)
  have hg : Integrable g μ := (integrable_const (1 : ℝ)).indicator hH
  have heq : f * g = H.indicator f := by
    ext ω
    by_cases h : ω ∈ H <;> simp [g, h]
  have hfg : Integrable (f * g) μ := heq.symm ▸ hf.indicator hH
  have hout : μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
    condExp_mul_of_stronglyMeasurable_left hfm hfg hg
  have hi : Integrable (f * μ[g | m]) μ := integrable_condExp.congr hout
  calc
    ∫ ω in H, f ω ∂μ = ∫ ω, (f * g) ω ∂μ := by
      rw [heq, integral_indicator hH]
    _ = ∫ ω, μ[f * g | m] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, f ω * μ[g | m] ω ∂μ := integral_congr_ae hout
    _ ≤ ∫ ω, f ω * δ ∂μ := by
      apply integral_mono_ae hi (hf.mul_const δ)
      filter_upwards [hf0, hcond] with ω hfω hcω
      exact mul_le_mul_of_nonneg_left hcω hfω
    _ = δ * ∫ ω, f ω ∂μ := by rw [integral_mul_const]; exact mul_comm _ _

/-- Cauchy–Schwarz in the integral form used on Ω × ℤ. -/
theorem integral_mul_le_sqrt_squares {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ ω, f ω * g ω ∂μ ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hh : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hh hf0 hg0
    (by simpa using hf) (by simpa using hg)
  simpa [Real.sqrt_eq_rpow] using h

/-- A masked L² mass at most δ and an unmasked mass at most one yield √δ.
The ambient measure can be probability times counting measure, so this is
not restricted to a finite coefficient set. -/
theorem integral_mul_le_sqrt_of_square_bounds {f g : Ω → ℝ} {δ : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hδ : ∫ ω, f ω ^ 2 ∂μ ≤ δ) (hg1 : ∫ ω, g ω ^ 2 ∂μ ≤ 1) :
    ∫ ω, f ω * g ω ∂μ ≤ Real.sqrt δ := by
  calc
    ∫ ω, f ω * g ω ∂μ ≤
        Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) :=
      integral_mul_le_sqrt_squares hf hg hf0 hg0
    _ ≤ Real.sqrt δ * Real.sqrt 1 :=
      mul_le_mul (Real.sqrt_le_sqrt hδ) (Real.sqrt_le_sqrt hg1)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt δ := by simp

/-- Countably many masks, each with a conditional probability bound.
The sum is genuinely infinite; no bound on the union of the events is used.
Apply to f_v=|ξ_v(x)|² or f_v=|γ_{n+v}(y)|² in the two orientations. -/
theorem conditional_mask_tsum_integral_le [IsFiniteMeasure μ]
    {ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f : ι → Ω → ℝ} {H : ι → Set Ω} {δ : ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hfm : ∀ i, StronglyMeasurable[m] (f i))
    (hf0 : ∀ i ω, 0 ≤ f i ω) (hH : ∀ i, @MeasurableSet Ω mΩ (H i))
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => f i ω))
    (hint : Integrable (fun ω => ∑' i, f i ω) μ)
    (hcond : ∀ i, ∀ᵐ ω ∂μ,
      μ[(H i).indicator (fun _ => (1 : ℝ)) | m] ω ≤ δ) :
    ∫ ω, (∑' i, (H i).indicator (f i) ω) ∂μ ≤
      δ * ∫ ω, (∑' i, f i ω) ∂μ := by
  classical
  have hmask0 : ∀ i ω, 0 ≤ (H i).indicator (f i) ω := by
    intro i ω
    by_cases h : ω ∈ H i <;> simp [h, hf0]
  have hmaskle : ∀ i ω, (H i).indicator (f i) ω ≤ f i ω := by
    intro i ω
    by_cases h : ω ∈ H i <;> simp [h, hf0]
  have hmaskSum : ∀ᵐ ω ∂μ, Summable (fun i => (H i).indicator (f i) ω) := by
    filter_upwards [hsum] with ω hω
    exact hω.of_nonneg_of_le (fun i => hmask0 i ω) (fun i => hmaskle i ω)
  have horig := hasSum_integral_of_dominated_convergence f
    (fun i => (hf i).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall fun ω => (Real.norm_of_nonneg (hf0 i ω)).le)
    hsum hint (hsum.mono fun _ h => h.hasSum)
  have hmasked := hasSum_integral_of_dominated_convergence f
    (fun i => ((hf i).indicator (hH i)).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hmask0 i ω)]
      exact hmaskle i ω)
    hsum hint (hmaskSum.mono fun _ h => h.hasSum)
  calc
    ∫ ω, (∑' i, (H i).indicator (f i) ω) ∂μ =
        ∑' i, ∫ ω, (H i).indicator (f i) ω ∂μ := hmasked.tsum_eq.symm
    _ ≤ ∑' i, δ * ∫ ω, f i ω ∂μ := by
      apply Summable.tsum_le_tsum _ hmasked.summable (horig.summable.mul_left δ)
      intro i
      rw [integral_indicator (hH i)]
      exact conditional_mask_integral_le hm (hf i) (hfm i)
        (Filter.Eventually.of_forall (hf0 i)) (hH i) (hcond i)
    _ = δ * ∫ ω, (∑' i, f i ω) ∂μ := by rw [tsum_mul_left, horig.tsum_eq]

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_ProjectionDiagonal
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section

/-- The diagonal of an orthogonal projection is the square norm of its column. -/
theorem fiberProjection_diagonal_inner (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) :
    P (lp.single 2 k (1 : ℂ)) k =
      inner ℂ (P (lp.single 2 k (1 : ℂ))) (P (lp.single 2 k (1 : ℂ))) := by
  let e : SourceFiberHilbert := lp.single 2 k (1 : ℂ)
  have hi : P (P e) = P e := congrArg (fun A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert => A e)
    hp.isIdempotentElem
  calc
    _ = inner ℂ e (P e) := by simp [e,lp.inner_single_left]
    _ = inner ℂ e (star P (P e)) := by rw [hp.isSelfAdjoint.star_eq,hi]
    _ = _ := by rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

theorem fiberProjection_diagonal_bounds (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) :
    0 ≤ (P (lp.single 2 k (1 : ℂ)) k).re ∧
    (P (lp.single 2 k (1 : ℂ)) k).re ≤ 1 ∧
    (P (lp.single 2 k (1 : ℂ)) k).im = 0 := by
  have hr : (P (lp.single 2 k (1 : ℂ)) k).re = ‖P (lp.single 2 k (1 : ℂ))‖ ^ 2 := by
    rw [fiberProjection_diagonal_inner P hp]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  have hb : 1 - (P (lp.single 2 k (1 : ℂ)) k).re = ‖(1-P) (lp.single 2 k (1 : ℂ))‖ ^ 2 := by
    have h := congrArg Complex.re (fiberProjection_diagonal_inner (1-P) hp.one_sub k)
    change ((lp.single 2 k (1 : ℂ) : SourceFiberHilbert) k - P (lp.single 2 k (1 : ℂ)) k).re = _ at h
    simpa only [lp.single_apply,Pi.single_eq_same,Complex.sub_re,Complex.one_re,
      show ∀ v : SourceFiberHilbert, (inner ℂ v v).re = ‖v‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ)] using h
  refine ⟨by rw [hr]; positivity,by nlinarith [sq_nonneg ‖(1-P) (lp.single 2 k (1 : ℂ))‖],?_⟩
  rw [fiberProjection_diagonal_inner P hp]
  exact inner_self_im (𝕜 := ℂ) _

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_RealIdentity
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Almost-everywhere original-base properties transfer to every actual mixed endpoint. -/
theorem sourceBiasedEndpoint_ae (j : ℕ) (r : SourceCoordinate → Bool)
    {P : (SourceCoordinate → ℝ) → Prop} (hP : ∀ᵐ x ∂sourceBaseMeasure, P x) :
    ∀ᵐ ω ∂sourceBiasedLaw j, P (sourceBiasedEndpoint r ω) := by
  obtain ⟨g,_,_,_,hm,_⟩ := sourceBiasedEndpoint_density j r
  have ha : (sourceBiasedLaw j).map (sourceBiasedEndpoint r) ≪ sourceSamplingHaar := by
    rw [hm]
    exact withDensity_absolutelyContinuous _ _
  exact ae_of_ae_map (sourceBiasedEndpoint_measurable r).aemeasurable (ha.ae_le hP)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CountableMaskedError
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Cauchy--Schwarz for genuinely infinite nonnegative coefficient series. -/
theorem nonnegative_series_cauchy_schwarz {ι : Type*} (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable (fun i => f i^2)) (hgs : Summable (fun i => g i^2)) :
    Summable (fun i => f i*g i) ∧
    (∑' i, f i*g i) ≤ Real.sqrt (∑' i, f i^2)*Real.sqrt (∑' i, g i^2) := by
  have hp : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have hF : 0 ≤ ∑' i, f i^2 := tsum_nonneg (fun i => sq_nonneg _)
  have hG : 0 ≤ ∑' i, g i^2 := tsum_nonneg (fun i => sq_nonneg _)
  have hsf : HasSum (fun i => f i^(2 : ℝ)) ((Real.sqrt (∑' i, f i^2))^(2 : ℝ)) := by
    simpa only [Real.rpow_two,Real.sq_sqrt hF] using hfs.hasSum
  have hsg : HasSum (fun i => g i^(2 : ℝ)) ((Real.sqrt (∑' i, g i^2))^(2 : ℝ)) := by
    simpa only [Real.rpow_two,Real.sq_sqrt hG] using hgs.hasSum
  obtain ⟨C,_,hC,hs⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hp
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hf hg hsf hsg
  exact ⟨hs.summable,hs.tsum_eq ▸ hC⟩

/-- Probability-space Cauchy--Schwarz after the pointwise series estimate.
Equivalent to the product-with-counting-measure argument; no independence or
finite truncation is assumed. -/
theorem countable_error_integral_le {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f g : ι → Ω → ℝ) (δ : ℝ)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hf0 : ∀ i ω, 0 ≤ f i ω) (hg0 : ∀ i ω, 0 ≤ g i ω)
    (hfs : ∀ᵐ ω ∂μ, Summable (fun i => f i ω^2))
    (hgs : ∀ᵐ ω ∂μ, Summable (fun i => g i ω^2))
    (hfi : Integrable (fun ω => ∑' i, f i ω^2) μ)
    (hfm : (∫ ω, (∑' i, f i ω^2) ∂μ) ≤ δ)
    (hg1 : ∀ᵐ ω ∂μ, (∑' i, g i ω^2) ≤ 1) :
    Integrable (fun ω => ∑' i, f i ω*g i ω) μ ∧
    (∫ ω, (∑' i, f i ω*g i ω) ∂μ) ≤ Real.sqrt δ := by
  let F := fun ω => ∑' i, f i ω^2
  let S := fun ω => ∑' i, f i ω*g i ω
  have hF0 (ω) : 0 ≤ F ω := tsum_nonneg (fun i => sq_nonneg _)
  have hFm : Measurable F := Measurable.tsum (fun i => (hf i).pow_const 2)
  have hSm : Measurable S := Measurable.tsum (fun i => (hf i).mul (hg i))
  have hS0 (ω) : 0 ≤ S ω := tsum_nonneg (fun i => mul_nonneg (hf0 i ω) (hg0 i ω))
  have hFroot : MemLp (fun ω => Real.sqrt (F ω)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hFm.sqrt.aestronglyMeasurable)).mpr
    simpa only [Real.sq_sqrt (hF0 _)] using hfi
  have hS : ∀ᵐ ω ∂μ, S ω ≤ Real.sqrt (F ω) := by
    filter_upwards [hfs,hgs,hg1] with ω hs ht h1
    have hh := (nonnegative_series_cauchy_schwarz (fun i => f i ω) (fun i => g i ω)
      (fun i => hf0 i ω) (fun i => hg0 i ω) hs ht).2
    apply hh.trans
    simpa only [Real.sqrt_one,mul_one] using
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (Real.sqrt_nonneg (F ω))
  have hSi : Integrable S μ := (hFroot.integrable (by norm_num)).mono'
    hSm.aestronglyMeasurable (hS.mono fun ω h => by rwa [Real.norm_of_nonneg (hS0 ω)])
  refine ⟨hSi,?_⟩
  have hh := integral_mul_le_sqrt_of_square_bounds hFroot (memLp_const (1 : ℝ))
    (Eventually.of_forall fun ω => Real.sqrt_nonneg (F ω)) (Eventually.of_forall fun _ => zero_le_one)
    (by simpa only [Real.sq_sqrt (hF0 _)] using hfm)
    (by simp : (∫ _ω : Ω, (1 : ℝ)^2 ∂μ) ≤ 1)
  apply (integral_mono_ae hSi (hFroot.integrable (by norm_num)) hS).trans
  simpa only [mul_one] using hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Noncrossing
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal
noncomputable section
namespace CouplingParameters

theorem crossingPartner_measurable (right : Bool) (u : ℝ) : MeasurableSet (crossingPartner right u) := by
  cases right
  · exact measurableSet_Ici
  · exact measurableSet_Iio

theorem posterior_noncrossing_le_exp (p : CouplingParameters) (right : Bool) (w : Fin 2)
    {t u : ℝ} (ht : t ∈ Set.Ico 0 1) (hu : p.width w ≤ u ∧ u ≤ 1-p.width w)
    (heligible : if right then u ≤ t else t < u) :
    p.posteriorKernel right t (crossingPartner right u)ᶜ ≤
      ENNReal.ofReal (Real.exp (-(p.rho w / 10))) := by
  have hlo := p.posteriorLaw_crossing_lower right w ht hu heligible
  change ENNReal.ofReal (p.rho w / 10) ≤ p.posteriorKernel right t (crossingPartner right u) at hlo
  rw [measure_compl (crossingPartner_measurable right u) (measure_ne_top _ _), measure_univ]
  calc
    1 - p.posteriorKernel right t (crossingPartner right u) ≤ 1 - ENNReal.ofReal (p.rho w / 10) :=
      tsub_le_tsub_left hlo 1
    _ = ENNReal.ofReal (1 - p.rho w / 10) := by rw [ENNReal.ofReal_sub 1 (div_nonneg (p.rho_nonneg w) (by norm_num)), ENNReal.ofReal_one]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (-(p.rho w / 10))])

/-- Simultaneous noncrossing of any fixed eligible coordinates, conditional on
the entire endpoint vector. The exponent is the sum of their actual biases. -/
theorem vectorPosterior_noncrossing_le_exp {ι : Type*}
    (p : ι → CouplingParameters) (right : ι → Bool) (w : ι → Fin 2)
    (x u : ι → ℝ) (I : Finset ι)
    (hx : ∀ i ∈ I, x i ∈ Set.Ico 0 1)
    (hu : ∀ i ∈ I, (p i).width (w i) ≤ u i ∧ u i ≤ 1-(p i).width (w i))
    (heligible : ∀ i ∈ I, if right i then u i ≤ x i else x i < u i) :
    vectorPosterior p right x (Set.pi (I : Set ι) (fun i => (crossingPartner (right i) (u i))ᶜ)) ≤
      ENNReal.ofReal (Real.exp (-(∑ i ∈ I, (p i).rho (w i) / 10))) := by
  rw [vectorPosterior_independence _ _ _ _ _ (fun i _ => (crossingPartner_measurable (right i) (u i)).compl)]
  calc
    _ ≤ ∏ i ∈ I, ENNReal.ofReal (Real.exp (-((p i).rho (w i) / 10))) := by
      apply Finset.prod_le_prod'
      intro i hi
      exact (p i).posterior_noncrossing_le_exp (right i) (w i) (hx i hi) (hu i hi) (heligible i hi)
    _ = _ := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
      simp only [Finset.sum_neg_distrib]

theorem vectorPosterior_noncrossing_source_bound {ι : Type*}
    (p : ι → CouplingParameters) (right : ι → Bool) (w : ι → Fin 2)
    (x u : ι → ℝ) (I : Finset ι) (m ρ L : ℝ)
    (hx : ∀ i ∈ I, x i ∈ Set.Ico 0 1)
    (hu : ∀ i ∈ I, (p i).width (w i) ≤ u i ∧ u i ≤ 1-(p i).width (w i))
    (heligible : ∀ i ∈ I, if right i then u i ≤ x i else x i < u i)
    (hρ : ∀ i ∈ I, (p i).rho (w i) = ρ)
    (hρ0 : 0 ≤ ρ) (hcard : m / 40 ≤ (I.card : ℝ)) (hL : L ≤ m*ρ) :
    vectorPosterior p right x (Set.pi (I : Set ι) (fun i => (crossingPartner (right i) (u i))ᶜ)) ≤
      ENNReal.ofReal (Real.exp (-L/400)) := by
  apply (vectorPosterior_noncrossing_le_exp p right w x u I hx hu heligible).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have he : (∑ i ∈ I, (p i).rho (w i)/10) = I.card * (ρ/10) := by
    calc
      _ = ∑ i ∈ I, ρ/10 := Finset.sum_congr rfl (fun i hi => by rw [hρ i hi])
      _ = _ := by simp
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hcard hρ0
  nlinarith

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Conditioning
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- Identification with mathlib's regular conditional distribution. -/
theorem vectorPosterior_eq_condDistrib {ι : Type*} [Countable ι]
    (p : ι → CouplingParameters) (right : ι → Bool) :
    condDistrib (vectorEndpoint (fun i => !right i)) (vectorEndpoint right) (vectorCoupling p)
      =ᵐ[(vectorCoupling p).map (vectorEndpoint right)] vectorPosterior p right :=
  condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (vectorEndpoint_measurable right) (vectorEndpoint_measurable (fun i => !right i))
    (vectorPosterior_disintegration p right).symm

/-- A bound on the proved full-vector posterior is a conditional-expectation
bound on the original augmented probability space. -/
theorem vector_condExp_event_le {ι : Type*} [Countable ι]
    (p : ι → CouplingParameters) (right : ι → Bool)
    {B : Set ((ι → ℝ) × (ι → ℝ))} (hB : MeasurableSet B) {δ : ℝ}
    (hb : ∀ᵐ x ∂(vectorCoupling p).map (vectorEndpoint right),
      (vectorPosterior p right x).real (Prod.mk x ⁻¹' B) ≤ δ) :
    ∀ᵐ ω ∂vectorCoupling p,
      (vectorCoupling p)[
        (fun ω => B.indicator (fun _ => (1 : ℝ))
          (vectorEndpoint right ω, vectorEndpoint (fun i => !right i) ω)) |
        (inferInstance : MeasurableSpace (ι → ℝ)).comap (vectorEndpoint right)] ω ≤ δ := by
  have hX := vectorEndpoint_measurable right
  have hY := vectorEndpoint_measurable (fun i => !right i)
  have hint : Integrable (B.indicator (fun _ => (1 : ℝ)))
      ((vectorCoupling p).map (fun ω => (vectorEndpoint right ω, vectorEndpoint (fun i => !right i) ω))) :=
    (integrable_const _).indicator hB
  have hc := condExp_prod_ae_eq_integral_condDistrib' hX hY.aemeasurable hint
  have hk := ae_eq_comp hX.aemeasurable (vectorPosterior_eq_condDistrib p right)
  have hb' := ae_of_ae_map hX.aemeasurable hb
  filter_upwards [hc, hk, hb'] with ω hcω hkω hbω
  simp only [Function.comp_apply] at hkω
  rw [hcω, hkω]
  have he : (fun y => B.indicator (fun _ => (1 : ℝ)) (vectorEndpoint right ω, y)) =
      (Prod.mk (vectorEndpoint right ω) ⁻¹' B).indicator (fun _ => (1 : ℝ)) := rfl
  rw [he, integral_indicator (measurable_prodMk_left hB), setIntegral_const]
  simpa using hbω

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_BadEvents
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal
noncomputable section
namespace CouplingParameters

theorem eligible_measurable (right : Bool) (u : ℝ) : MeasurableSet {x : ℝ | eligible right x u} := by
  cases right
  · exact measurableSet_Iio
  · exact measurableSet_Ici

theorem eligible_count_measurable {ι : Type*} (right : ι → Bool) (u : ι → ℝ) (I : Finset ι) :
    Measurable (fun x : ι → ℝ => (eligibleIndices right x u I).card) := by
  unfold eligibleIndices
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite ((eligible_measurable (right i) (u i)).preimage (measurable_pi_apply i))
    measurable_const measurable_const

theorem badHalfEvent_measurable {ι : Type*} (right : ι → Bool) (u : ι → ℝ) (I : Finset ι) (q : ℝ) :
    MeasurableSet (badHalfEvent right u I q) := by
  have hcount : Measurable (fun z : (ι → ℝ) × (ι → ℝ) =>
      ((eligibleIndices right z.1 u I).card : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp
      ((eligible_count_measurable right u I).comp measurable_fst)
  have hq : MeasurableSet {z : (ι → ℝ) × (ι → ℝ) | q/2 ≤ ((eligibleIndices right z.1 u I).card : ℝ)} :=
    measurableSet_le measurable_const hcount
  have hi (i : I) : MeasurableSet {z : (ι → ℝ) × (ι → ℝ) |
      ¬(eligible (right i) (z.1 i) (u i) ∧ z.2 i ∈ crossingPartner (right i) (u i))} :=
    (((eligible_measurable (right i) (u i)).preimage
      ((measurable_pi_apply (i : ι)).comp measurable_fst)).inter
      ((crossingPartner_measurable (right i) (u i)).preimage
        ((measurable_pi_apply (i : ι)).comp measurable_snd))).compl
  convert hq.inter (MeasurableSet.iInter hi) using 1
  ext z
  simp [badHalfEvent]

theorem badHalfEvent_section {ι : Type*} (right : ι → Bool) (x u : ι → ℝ)
    (I : Finset ι) (q : ℝ) (hq : q/2 ≤ ((eligibleIndices right x u I).card : ℝ)) :
    Prod.mk x ⁻¹' badHalfEvent right u I q =
      Set.pi (eligibleIndices right x u I : Set ι) (fun i => (crossingPartner (right i) (u i))ᶜ) := by
  ext y
  simp only [Set.mem_preimage, badHalfEvent, Set.mem_ofPred_eq, Set.mem_pi,
    Finset.mem_coe, eligibleIndices, Finset.mem_filter, Set.mem_compl_iff]
  constructor
  · intro h i hi
    exact fun hy => h.2 ⟨i, hi.1⟩ ⟨hi.2, hy⟩
  · intro h
    refine ⟨hq, fun i hi => ?_⟩
    exact h i ⟨i.2, hi.1⟩ hi.2

theorem vectorPosterior_badHalf_bound {ι : Type*}
    (p : ι → CouplingParameters) (right : ι → Bool) (w : ι → Fin 2)
    (x u : ι → ℝ) (I : Finset ι) (q m ρ L : ℝ)
    (hx : ∀ i ∈ I, x i ∈ Set.Ico 0 1)
    (hu : ∀ i ∈ I, (p i).width (w i) ≤ u i ∧ u i ≤ 1-(p i).width (w i))
    (hρ : ∀ i ∈ I, (p i).rho (w i) = ρ)
    (hρ0 : 0 ≤ ρ) (hq : m/20 ≤ q) (hL : L ≤ m*ρ) :
    vectorPosterior p right x (Prod.mk x ⁻¹' badHalfEvent right u I q) ≤
      ENNReal.ofReal (Real.exp (-L/400)) := by
  by_cases hn : q/2 ≤ ((eligibleIndices right x u I).card : ℝ)
  · rw [badHalfEvent_section right x u I q hn]
    apply vectorPosterior_noncrossing_source_bound p right w x u (eligibleIndices right x u I) m ρ L
    · intro i hi
      exact hx i (Finset.mem_filter.mp hi).1
    · intro i hi
      exact hu i (Finset.mem_filter.mp hi).1
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · intro i hi
      exact hρ i (Finset.mem_filter.mp hi).1
    · exact hρ0
    · linarith
    · exact hL
  · have he : Prod.mk x ⁻¹' badHalfEvent right u I q = ∅ := by
      ext y
      simp [badHalfEvent, hn]
    rw [he, measure_empty]
    exact zero_le

theorem vectorEndpoint_unitCube {ι : Type*} [Countable ι]
    (p : ι → CouplingParameters) (right : ι → Bool) :
    ∀ᵐ x ∂(vectorCoupling p).map (vectorEndpoint right), ∀ i, x i ∈ Set.Ico 0 1 := by
  rw [vectorEndpoint_law, ae_all_iff]
  intro i
  have hi : ∀ᵐ t ∂(p i).selectedLaw true (right i), t ∈ Set.Ico 0 1 :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ico)
  have hh := Measure.infinitePi_map_eval (fun i => (p i).selectedLaw true (right i)) i
  rw [← hh] at hi
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hi

/-- Actual conditional bound for each oriented bad event, ready for the
countably infinite masked-sum theorem. No conditional-independence assumption
or posterior bound is an input. -/
theorem badHalf_condExp_bound {ι : Type*} [Countable ι]
    (p : ι → CouplingParameters) (right : ι → Bool) (w : ι → Fin 2)
    (u : ι → ℝ) (I : Finset ι) (q m ρ L : ℝ)
    (hu : ∀ i ∈ I, (p i).width (w i) ≤ u i ∧ u i ≤ 1-(p i).width (w i))
    (hρ : ∀ i ∈ I, (p i).rho (w i) = ρ)
    (hρ0 : 0 ≤ ρ) (hq : m/20 ≤ q) (hL : L ≤ m*ρ) :
    ∀ᵐ ω ∂vectorCoupling p,
      (vectorCoupling p)[
        (fun ω => (badHalfEvent right u I q).indicator (fun _ => (1 : ℝ))
          (vectorEndpoint right ω, vectorEndpoint (fun i => !right i) ω)) |
        (inferInstance : MeasurableSpace (ι → ℝ)).comap (vectorEndpoint right)] ω ≤ Real.exp (-L/400) := by
  apply vector_condExp_event_le p right (badHalfEvent_measurable right u I q)
  filter_upwards [vectorEndpoint_unitCube p right] with x hx
  have hh := vectorPosterior_badHalf_bound p right w x u I q m ρ L (fun i _ => hx i) hu hρ hρ0 hq hL
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  simpa only [measureReal_def, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hh'

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CouplingBudget
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceStage_L_mono : Monotone (fun s => (sourceStage s).L) := by
  apply monotone_nat_of_le_succ
  intro s
  exact (sourceStage (s+1)).L_ge

theorem staged_rho_first (j s : ℕ) :
    (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho 0 =
      sourceKappa s*Real.sqrt (sourceStageState s).G := by
  have hm := sourceBlockSize_pos s
  have hG : 0 ≤ (sourceStageState s).G := zero_le_one.trans (sourceStageState s).G_ge
  change (sourceBlockSize s : ℝ)*(sourceKappa s*
    Real.sqrt (((sourceStageState s).G/(sourceBlockSize s : ℝ))/(sourceBlockSize s : ℝ))) = _
  rw [div_div, Real.sqrt_div hG, Real.sqrt_mul_self hm.le]
  field_simp

theorem staged_rho_second (j s : ℕ) :
    (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho 1 =
      sourceKappa s*(sourceBlockSize s : ℝ)^(1/40 : ℝ) := by
  have hm := sourceBlockSize_pos s
  change (sourceBlockSize s : ℝ)*(sourceKappa s*
    Real.sqrt (((sourceBlockSize s : ℝ)^(-19/20 : ℝ))/(sourceBlockSize s : ℝ))) = _
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one,
    ← Real.rpow_add hm, ← Real.rpow_mul hm.le]
  have he : ((-19/20 : ℝ)+(-1))*(1/2) = -39/40 := by ring
  rw [he]
  calc
    _ = sourceKappa s*((sourceBlockSize s : ℝ)^(1 : ℝ)*(sourceBlockSize s : ℝ)^(-39/40 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hm]; norm_num

/-- Both conditional crossing budgets now follow from the numerical source
construction. The tag location j does not affect these two mixture weights. -/
theorem staged_rho_budget (j s : ℕ) (hjs : j ≤ s) (w : Fin 2) (hw : w = 0 → j < s) :
    (sourceStage j).L ≤ (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho w := by
  fin_cases w
  · change (sourceStage j).L ≤ (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho 0
    obtain ⟨p,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by have := hw rfl; omega)
    rw [staged_rho_first]
    have hh := (sourceStage p).next_budget
    exact (sourceStage_L_mono (by have := hw rfl; omega : j ≤ p)).trans hh
  · change (sourceStage j).L ≤ (sourceBlockSize s : ℝ)*(stagedCouplingParameters j s).rho 1
    rw [staged_rho_second]
    exact (sourceStage_L_mono hjs).trans (sourceStage s).current_budget

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_AssignedBadEvents
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

namespace SourcePhaseAssignment
variable {θ : SourceCoordinate → ℝ} {j : ℕ} {k : ℤ}

theorem badEvent_measurable (a : SourcePhaseAssignment θ j k) (b : Bool) :
    MeasurableSet (a.badEvent b) :=
  (badHalfEvent_measurable ..).preimage
    ((sourceBiasedEndpoint_measurable _).prodMk (sourceBiasedEndpoint_measurable _))

/-- Both conditional estimates use the actual full-vector posterior and the
constructed numerical budget. The assignment has no sample argument. -/
theorem badEvent_condExp (a : SourcePhaseAssignment θ j k) (b : Bool) :
    ∀ᵐ ω ∂sourceBiasedLaw j,
      (sourceBiasedLaw j)[(a.badEvent b).indicator (fun _ => (1 : ℝ)) |
        (inferInstance : MeasurableSpace (SourceCoordinate → ℝ)).comap
          (sourceBiasedEndpoint (fun _ => b))] ω ≤ Real.exp (-(sourceStage j).L/400) := by
  have hi (i : SourceCoordinate) (h : i ∈ a.indices) : i.1 = a.block :=
    mem_sourceBlockCoordinates (a.subset h)
  have hh := badHalf_condExp_bound (fun i : SourceCoordinate => stagedCouplingParameters j i.1)
    (fun _ => b) (fun _ => a.width) (fun i => 1-Int.fract ((k : ℝ)*θ i)) a.indices
    a.indices.card (sourceBlockSize a.block) ((stagedCouplingParameters j a.block).rho a.width)
    (sourceStage j).L
    (fun i h => by simpa only [stagedCouplingParameters,hi i h,Set.mem_Icc] using a.threshold i h)
    (fun i h => by rw [hi i h])
    ((stagedCouplingParameters j a.block).rho_nonneg a.width)
    a.card_lower (staged_rho_budget j a.block a.later a.width a.first_later)
  have he : (a.badEvent b).indicator (fun _ => (1 : ℝ)) =
      fun ω => (badHalfEvent (fun _ => b) (fun i => 1-Int.fract ((k : ℝ)*θ i))
        a.indices a.indices.card).indicator (fun _ => (1 : ℝ))
        (sourceBiasedEndpoint (fun _ => b) ω,sourceBiasedEndpoint (fun _ => !b) ω) := by
    funext ω
    by_cases h : (sourceBiasedEndpoint (fun _ => b) ω,sourceBiasedEndpoint (fun _ => !b) ω) ∈
        badHalfEvent (fun _ => b) (fun i => 1-Int.fract ((k : ℝ)*θ i)) a.indices a.indices.card
    · have hp : ω ∈ a.badEvent b := h
      rw [Set.indicator_of_mem hp,Set.indicator_of_mem h]
    · have hp : ω ∉ a.badEvent b := h
      rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem h]
  rw [he]
  exact hh

end SourcePhaseAssignment
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionColumns
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ComplexConjugate
noncomputable section

theorem fiberProjection_column_norm_le_one
    (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (hP : IsStarProjection P) (k : ℤ) :
    ‖P (lp.single 2 k (1 : ℂ))‖ ≤ 1 := by
  have hd := (fiberProjection_diagonal_bounds P hP k).2.1
  have he := congrArg Complex.re (fiberProjection_diagonal_inner P hP k)
  rw [show ∀ v : SourceFiberHilbert, (inner ℂ v v).re = ‖v‖^2 from inner_self_eq_norm_sq (𝕜 := ℂ)] at he
  nlinarith [norm_nonneg (P (lp.single 2 k (1 : ℂ)))]

theorem sourceProjection_columns_norm (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) :
    ∀ᵐ x ∂sourceBaseMeasure, ‖sourceProjectionColumn p x‖ ≤ 1 ∧ ‖sourceComplementColumn p x‖ ≤ 1 := by
  filter_upwards [sourceOperatorField_projection θ hp hproj] with x hx
  exact ⟨fiberProjection_column_norm_le_one _ hx 0,fiberProjection_column_norm_le_one _ hx.one_sub 0⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ColumnSquareMass
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceColumn_coordinate_measurable
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (b : Bool) (k : ℤ) :
    Measurable (fun x => sourceColumn p b x k) := by
  cases b
  · exact sourceOperatorField_entry_measurable p k 0
  · exact measurable_const.sub (sourceOperatorField_entry_measurable p k 0)

theorem sourceColumn_square_hasSum
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (b : Bool) (x : SourceCoordinate → ℝ) (n : ℤ) :
    HasSum (fun k : ℤ => ‖sourceColumn p b x (n+k)‖^2) (‖sourceColumn p b x‖^2) := by
  have h : HasSum (fun k : ℤ => ‖sourceColumn p b x k‖^2) (‖sourceColumn p b x‖^2) := by
    simpa using lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (sourceColumn p b x)
  exact (Equiv.addLeft n).hasSum_iff.mpr h

/-- Actual endpoint square mass: integrable, and at most one. The shift is a
bijection of all integers; no finite coefficient cutoff is introduced. -/
theorem sourceColumn_square_mass (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (j : ℕ) (b : Bool) (n : ℤ) :
    Integrable (fun ω => ∑' k : ℤ,
      ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (n+k)‖^2) (sourceBiasedLaw j) ∧
    (∫ ω, (∑' k : ℤ, ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (n+k)‖^2)
      ∂sourceBiasedLaw j) ≤ 1 := by
  let f := fun ω => ∑' k : ℤ, ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (n+k)‖^2
  have hm : Measurable f := Measurable.tsum (fun k =>
    (((sourceColumn_coordinate_measurable p b (n+k)).comp (sourceBiasedEndpoint_measurable _)).norm.pow_const 2))
  have h0 : ∀ ω, 0 ≤ f ω := fun ω => tsum_nonneg (fun _ => sq_nonneg _)
  have h1 : ∀ᵐ ω ∂sourceBiasedLaw j, f ω ≤ 1 := by
    filter_upwards [sourceBiasedEndpoint_ae j (fun _ => b) (sourceProjection_columns_norm θ hp hproj)] with ω hω
    have hn : ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω)‖ ≤ 1 := by
      cases b <;> simp only [sourceColumn,Bool.false_eq_true,↓reduceIte] <;> tauto
    rw [show f ω = ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω)‖^2 from
      (sourceColumn_square_hasSum p b _ n).tsum_eq]
    nlinarith [norm_nonneg (sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω))]
  have hi : Integrable f (sourceBiasedLaw j) := (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    (h1.mono fun ω h => by rwa [Real.norm_of_nonneg (h0 ω)])
  refine ⟨hi,?_⟩
  simpa using integral_mono_ae hi (integrable_const (1 : ℝ)) h1

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OmittedBadEvents
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceOmittedBadEvent_measurable (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n v : ℤ) (b : Bool) :
    MeasurableSet (sourceOmittedBadEvent θ hθ j hphase n v b) := by
  unfold sourceOmittedBadEvent
  split_ifs
  · exact SourcePhaseAssignment.badEvent_measurable _ _
  · exact MeasurableSet.empty

/-- All actual omitted masks obey the same conditional bound, in each
orientation and simultaneously over every integer shift and coefficient. -/
theorem sourceOmittedBadEvent_condExp (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ∀ (n v : ℤ) (b : Bool),
      (sourceBiasedLaw j)[(sourceOmittedBadEvent θ hθ j hphase n v b).indicator (fun _ => (1 : ℝ)) |
        (inferInstance : MeasurableSpace (SourceCoordinate → ℝ)).comap
          (sourceBiasedEndpoint (fun _ => b))] ω ≤ Real.exp (-(sourceStage j).L/400) := by
  simp only [ae_all_iff]
  intro n v b
  unfold sourceOmittedBadEvent
  split_ifs
  · exact SourcePhaseAssignment.badEvent_condExp _ b
  · filter_upwards [] with ω
    simp only [Set.indicator_empty]
    change (sourceBiasedLaw j)[(0 : SourceBiasedSample → ℝ) | _] ω ≤ _
    rw [condExp_zero]
    exact (Real.exp_pos _).le

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_MaskedSquareMass
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The actual source columns and deterministic omitted-index masks satisfy
the infinite conditional square estimate in both orientations. -/
theorem sourceOmitted_masked_square (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n r : ℤ) (b : Bool) :
    (∫ ω, (∑' k : ℤ, (sourceOmittedBadEvent θ hθ j hphase n k b).indicator
      (fun ω => ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (r+k)‖^2) ω)
      ∂sourceBiasedLaw j) ≤ Real.exp (-(sourceStage j).L/400) := by
  let f := fun k ω => ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (r+k)‖^2
  have hfm (k : ℤ) : Measurable (f k) :=
    (((sourceColumn_coordinate_measurable p b (r+k)).comp (sourceBiasedEndpoint_measurable _)).norm.pow_const 2)
  have h0 (k : ℤ) (ω) : 0 ≤ f k ω := sq_nonneg _
  have hs (ω) : Summable (fun k => f k ω) := (sourceColumn_square_hasSum p b _ r).summable
  obtain ⟨hint,hbound⟩ := sourceColumn_square_mass θ hp hproj j b r
  have hf (k : ℤ) : Integrable (f k) (sourceBiasedLaw j) := by
    apply hint.mono' (hfm k).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (h0 k ω)]
      exact (hs ω).le_tsum k (fun i _ => h0 i ω)
  have hcond (k : ℤ) := (sourceOmittedBadEvent_condExp θ hθ j hphase).mono
    (fun ω h => h n k b)
  let m := (inferInstance : MeasurableSpace (SourceCoordinate → ℝ)).comap
    (sourceBiasedEndpoint (fun _ => b))
  have hstrong (k : ℤ) : StronglyMeasurable[m] (f k) := by
    have hh : Measurable[m] (f k) :=
      ((sourceColumn_coordinate_measurable p b (r+k)).norm.pow_const 2).comp
        (comap_measurable (sourceBiasedEndpoint (fun _ => b)))
    exact hh.stronglyMeasurable
  have hh := conditional_mask_tsum_integral_le
    (sourceBiasedEndpoint_measurable (fun _ => b)).comap_le hf hstrong
    h0 (fun k => sourceOmittedBadEvent_measurable θ hθ j hphase n k b)
    (Eventually.of_forall hs) hint hcond
  apply hh.trans
  exact (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans_eq (mul_one _)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_MaskedError
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Both source expected-error estimates for the full infinite coefficient
sum. b=false,r=0,s=n gives the first orientation; b=true,r=n,s=0 gives the
second, after commuting the scalar product. -/
theorem sourceOmitted_masked_error (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n r s : ℤ) (b : Bool) :
    let error := fun ω => ∑' k : ℤ, (sourceOmittedBadEvent θ hθ j hphase n k b).indicator
      (fun ω => ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (r+k)‖ *
        ‖sourceColumn p (!b) (sourceBiasedEndpoint (fun _ => !b) ω) (s+k)‖) ω
    Integrable error (sourceBiasedLaw j) ∧
      (∫ ω, error ω ∂sourceBiasedLaw j) ≤ Real.exp (-(sourceStage j).L/800) := by
  let H := fun k => sourceOmittedBadEvent θ hθ j hphase n k b
  let u := fun k ω => ‖sourceColumn p b (sourceBiasedEndpoint (fun _ => b) ω) (r+k)‖
  let g := fun k ω => ‖sourceColumn p (!b) (sourceBiasedEndpoint (fun _ => !b) ω) (s+k)‖
  let f := fun k => (H k).indicator (u k)
  have hu (k) : Measurable (u k) :=
    ((sourceColumn_coordinate_measurable p b (r+k)).comp (sourceBiasedEndpoint_measurable _)).norm
  have hg (k) : Measurable (g k) :=
    ((sourceColumn_coordinate_measurable p (!b) (s+k)).comp (sourceBiasedEndpoint_measurable _)).norm
  have hH (k) : MeasurableSet (H k) := sourceOmittedBadEvent_measurable θ hθ j hphase n k b
  have hf (k) : Measurable (f k) := (hu k).indicator (hH k)
  have hf0 (k ω) : 0 ≤ f k ω := by
    by_cases h : ω ∈ H k <;> simp [f,h,u]
  have hule (k ω) : (f k ω)^2 ≤ (u k ω)^2 := by
    by_cases h : ω ∈ H k <;> simp [f,h,sq_nonneg]
  have hhe (k ω) : (f k ω)^2 = (H k).indicator (fun ω => (u k ω)^2) ω := by
    by_cases h : ω ∈ H k <;> simp [f,h]
  have hus (ω) : Summable (fun k => (u k ω)^2) := (sourceColumn_square_hasSum p b _ r).summable
  have hfs (ω) : Summable (fun k => (f k ω)^2) :=
    (hus ω).of_nonneg_of_le (fun k => sq_nonneg _) (fun k => hule k ω)
  have hsumle (ω) : (∑' k, (f k ω)^2) ≤ ∑' k, (u k ω)^2 :=
    (hfs ω).tsum_le_tsum (fun k => hule k ω) (hus ω)
  have hfi : Integrable (fun ω => ∑' k, (f k ω)^2) (sourceBiasedLaw j) := by
    apply (sourceColumn_square_mass θ hp hproj j b r).1.mono'
      (Measurable.tsum (fun k => (hf k).pow_const 2)).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (tsum_nonneg (fun k => sq_nonneg _))]
      exact hsumle ω
  have hfm : (∫ ω, (∑' k, (f k ω)^2) ∂sourceBiasedLaw j) ≤ Real.exp (-(sourceStage j).L/400) := by
    simp_rw [hhe]
    exact sourceOmitted_masked_square θ hθ hp hproj j hphase n r b
  have hg1 : ∀ᵐ ω ∂sourceBiasedLaw j, (∑' k, (g k ω)^2) ≤ 1 := by
    filter_upwards [sourceBiasedEndpoint_ae j (fun _ => !b) (sourceProjection_columns_norm θ hp hproj)] with ω hω
    have hn : ‖sourceColumn p (!b) (sourceBiasedEndpoint (fun _ => !b) ω)‖ ≤ 1 := by
      cases b <;> simp only [Bool.not_false,Bool.not_true,sourceColumn,Bool.false_eq_true,↓reduceIte] <;> tauto
    rw [(sourceColumn_square_hasSum p (!b) _ s).tsum_eq]
    nlinarith [norm_nonneg (sourceColumn p (!b) (sourceBiasedEndpoint (fun _ => !b) ω))]
  obtain ⟨hi,hb⟩ := countable_error_integral_le f g (Real.exp (-(sourceStage j).L/400))
    hf hg hf0 (fun k ω => norm_nonneg _) (Eventually.of_forall hfs)
    (Eventually.of_forall fun ω => (sourceColumn_square_hasSum p (!b) _ s).summable) hfi hfm hg1
  have he (k ω) : f k ω*g k ω = (H k).indicator (fun ω => u k ω*g k ω) ω := by
    by_cases h : ω ∈ H k <;> simp [f,h]
  simp_rw [he] at hi hb
  refine ⟨hi,hb.trans_eq ?_⟩
  rw [Real.sqrt_eq_rpow,← Real.exp_mul]
  congr 1
  ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionErrors
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Both actual infinite error sums are integrable and have the source bound. -/
theorem sourceOmittedError_estimate_oai (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℤ) (b : Bool) :
    Integrable (sourceOmittedError θ hθ p j hphase n b) (sourceBiasedLaw j) ∧
      (∫ ω, sourceOmittedError θ hθ p j hphase n b ω ∂sourceBiasedLaw j) ≤ Real.exp (-(sourceStage j).L/800) := by
  unfold sourceOmittedError
  cases b
  · simpa only [sourceOmittedError,sourceColumn,Bool.false_eq_true,↓reduceIte,Bool.not_false,zero_add] using
      sourceOmitted_masked_error θ hθ hp hproj j hphase n 0 n false
  · simpa only [sourceOmittedError,sourceColumn,Bool.false_eq_true,↓reduceIte,Bool.not_true,zero_add,mul_comm] using
      sourceOmitted_masked_error θ hθ hp hproj j hphase n n 0 true

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceOmittedError_estimate_oai := @OAI.FiniteFactor.sourceOmittedError_estimate_oai
