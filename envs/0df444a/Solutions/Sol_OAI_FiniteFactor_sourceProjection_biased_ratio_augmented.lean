-- Prove2me | solution 1 for OAI.FiniteFactor.sourceProjection_biased_ratio_augmented
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:43:16.67399+00:00
-- url     : https://prove2.me/submissions/974e494b-d802-485d-992e-d9dc3285aeba

import Mathlib
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_sourceProjection_biased_prefix_pairs

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
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Order
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

theorem orderedPairs_measurable : MeasurableSet orderedPairs :=
  measurableSet_le measurable_fst measurable_snd

theorem componentPair_ordered (i : Fin 6) : p.pairComponentLaw i orderedPairs = 1 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · change (unitIntervalMeasure.map (fun t => (t,t))) orderedPairs = 1
    have hm : Measurable (fun t : ℝ => (t,t)) := measurable_id.prodMk measurable_id
    rw [Measure.map_apply hm orderedPairs_measurable]
    simp [orderedPairs]
  · change ((p.endpointComponentLaw false k).prod (p.endpointComponentLaw true k)) orderedPairs = 1
    have hU := p.endpointComponentLaw_of_contains false k (Set.Subset.refl _)
    have hV := p.endpointComponentLaw_of_contains true k (Set.Subset.refl _)
    have hsub : (p.endpointInterval false k ×ˢ p.endpointInterval true k) ⊆ orderedPairs := by
      intro xy hxy
      have h₁ : xy.1 < p.leftLength k := hxy.1.2
      have h₂ : 1-p.rightLength k ≤ xy.2 := hxy.2.1
      have hlen := p.lengths_sum_le k
      change xy.1 ≤ xy.2
      linarith
    apply le_antisymm prob_le_one
    have h := measure_mono (μ := (p.endpointComponentLaw false k).prod (p.endpointComponentLaw true k)) hsub
    rw [Measure.prod_prod, hU, hV, mul_one] at h
    exact h

theorem coupling_ordered : p.coupling orderedPairs = 1 := by
  rw [p.coupling_eq_sum, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, p.componentPair_ordered, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.labelMass_nonneg i), p.labelMass_sum]
  simp

theorem labelledCoupling_ordered : p.labelledCoupling {z | z.2.1 ≤ z.2.2} = 1 := by
  have h := p.coupling_ordered
  rw [coupling, Measure.map_apply measurable_snd orderedPairs_measurable] at h
  exact h

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
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FloorSupport
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

/-- A uniform coordinate crosses the cut under translation by a with
probability at most |a|, valid for either sign and any size of translation. -/
theorem unitInterval_floor_exception (a : ℝ) :
    unitIntervalMeasure {t : ℝ | Int.floor (t+a) ≠ 0} ≤ ENNReal.ofReal |a| := by
  have hm : MeasurableSet {t : ℝ | Int.floor (t+a) ≠ 0} :=
    (measurableSet_eq_fun (Int.measurable_floor.comp (measurable_id.add_const a)) measurable_const).compl
  by_cases ha : |a| < 1
  · rw [unitIntervalMeasure, Measure.restrict_apply hm]
    rcases le_total 0 a with hpos | hneg
    · have hsub : {t : ℝ | Int.floor (t+a) ≠ 0} ∩ Set.Ico 0 1 ⊆ Set.Ico (1-a) 1 := by
        intro t ht
        have hn : ¬ (t+a ∈ Set.Ico (0 : ℝ) 1) := by
          exact fun h => ht.1 (Int.floor_eq_zero_iff.mpr h)
        have hlow : 0 ≤ t+a := add_nonneg ht.2.1 hpos
        exact ⟨by by_contra h; apply hn; exact ⟨hlow, by linarith⟩, ht.2.2⟩
      apply (measure_mono hsub).trans
      simp [Real.volume_Ico, abs_of_nonneg hpos]
    · have hsub : {t : ℝ | Int.floor (t+a) ≠ 0} ∩ Set.Ico 0 1 ⊆ Set.Ico 0 (-a) := by
        intro t ht
        have hn : ¬ (t+a ∈ Set.Ico (0 : ℝ) 1) := by
          exact fun h => ht.1 (Int.floor_eq_zero_iff.mpr h)
        have hupp : t+a < 1 := by linarith [ht.2.2]
        exact ⟨ht.2.1, by by_contra h; apply hn; exact ⟨by linarith, hupp⟩⟩
      apply (measure_mono hsub).trans
      simp [Real.volume_Ico, abs_of_nonpos hneg]
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal (le_of_not_gt ha))

/-- Borel--Cantelli proves that every integer-time floor sum has only finitely
many nonzero terms, simultaneously. This is the source's conull domain for F_k. -/
theorem ae_finiteFloorSupport {ι : Type*} [Countable ι]
    (θ : ι → ℝ) (hθ : Summable (fun i => |θ i|)) :
    ∀ᵐ x ∂Measure.infinitePi (fun _ : ι => unitIntervalMeasure), finiteFloorSupport θ x := by
  rw [show (fun x : ι → ℝ => finiteFloorSupport θ x) =
      (fun x => ∀ k : ℤ, (Function.support (coordinateFloor θ k x)).Finite) from rfl, ae_all_iff]
  intro k
  let μ := Measure.infinitePi (fun _ : ι => unitIntervalMeasure)
  let E (i : ι) : Set (ι → ℝ) := {x | coordinateFloor θ k x i ≠ 0}
  have hb (i : ι) : μ (E i) ≤ ENNReal.ofReal (|(k : ℝ)| * |θ i|) := by
    have hm : MeasurableSet {t : ℝ | Int.floor (t+(k : ℝ)*θ i) ≠ 0} :=
      (measurableSet_eq_fun (Int.measurable_floor.comp
        (measurable_id.add_const ((k : ℝ)*θ i))) measurable_const).compl
    have he := congrArg (fun ν : Measure ℝ => ν {t : ℝ | Int.floor (t+(k : ℝ)*θ i) ≠ 0})
      (Measure.infinitePi_map_eval (fun _ : ι => unitIntervalMeasure) i)
    rw [Measure.map_apply (measurable_pi_apply i) hm] at he
    change μ (E i) = _ at he
    rw [he, ← abs_mul]
    exact unitInterval_floor_exception _
  have hs : (∑' i, μ (E i)) ≠ ∞ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hb)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (hθ.mul_left |(k : ℝ)|)]
    exact ENNReal.ofReal_lt_top
  exact ae_finite_setOfPred_mem hs

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Cocycle
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

theorem sourceLog_summable {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k : ℤ) :
    Summable (fun i => c i * (coordinateFloor θ k x i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  apply (hx k).subset
  intro i hi
  simp only [Function.mem_support] at *
  intro hz
  apply hi
  simp [hz]

/-- Ordered endpoints give the ratio bound for every integer, including
negative integers. Both infinite sums are justified by finite support. -/
theorem sourceCocycle_ordered {ι : Type*} (θ c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) {x y : ι → ℝ}
    (hx : finiteFloorSupport θ x) (hy : finiteFloorSupport θ y)
    (hxy : ∀ i, x i ≤ y i) (k : ℤ) : sourceCocycle θ c k y ≤ sourceCocycle θ c k x := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  exact Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left
    (by
      have hh : coordinateFloor θ k x i ≤ coordinateFloor θ k y i :=
        Int.floor_mono (add_le_add (hxy i) le_rfl)
      exact_mod_cast hh) (hc i))
    (sourceLog_summable θ c hx k) (sourceLog_summable θ c hy k)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_StageOperator
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

theorem sourceCutoff_ge_pow (s : ℕ) : 2^s ≤ (sourceStageState s).K := by
  induction s with
  | zero => exact (sourceStageState 0).K_ge
  | succ s ih =>
    rw [pow_succ]
    have hh : 2^s*2 ≤ 2*(sourceStageState s).K := by simpa [mul_comm] using Nat.mul_le_mul_left 2 ih
    exact hh.trans (sourceStage_cutoff_growth s).le

theorem sourceCutoff_reciprocal_summable : Summable (fun s => 1/((sourceStageState s).K : ℝ)) := by
  apply (summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).of_nonneg_of_le
  · intro s; positivity
  · intro s
    have hpow : (2 : ℝ)^s ≤ (sourceStageState s).K := by exact_mod_cast sourceCutoff_ge_pow s
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ)^s) hpow
    simpa [one_div_pow] using hh

/-- The source interval bounds imply actual angle summability for every
realization, with the recursively constructed sizes and cutoffs. -/
theorem SourceAngles.summable {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) :
    Summable (fun i => |θ i|) := by
  have hs : Summable θ := by
    rw [summable_sigma_of_nonneg hθ.nonneg]
    refine ⟨fun s => (hasSum_fintype (fun t => θ ⟨s,t⟩)).summable, ?_⟩
    apply (sourceCutoff_reciprocal_summable.mul_left 2).of_nonneg_of_le
    · intro s; exact tsum_nonneg (fun t => hθ.nonneg ⟨s,t⟩)
    · intro s
      rw [tsum_fintype]
      have hh := Finset.sum_le_sum (fun (i : Fin (sourceBlockSize s)) (_ : i ∈ Finset.univ) => (hθ ⟨s,i⟩).2)
      have he : (∑ _i : Fin (sourceBlockSize s), 2/((sourceBlockSize s : ℝ)*(sourceStageState s).K)) =
          2*(1/((sourceStageState s).K : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [(sourceBlockSize_pos s).ne', (sourceCutoff_pos s).ne']
      exact hh.trans_eq he
  simpa only [abs_of_nonneg (hθ.nonneg _)] using hs

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
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Measures
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

theorem sourceSamplingHaar_cube : ∀ᵐ x ∂sourceSamplingHaar,
    ∀ i : SourceCoordinate, x i ∈ Set.Ico (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  have hh : ∀ᵐ t ∂sourceSamplingHaar.map (fun x => x i), t ∈ Set.Ico (0 : ℝ) 1 := by
    rw [Measure.infinitePi_map_eval]
    exact ae_restrict_mem measurableSet_Ico
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ico).mp hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TestedMarginals
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal
noncomputable section

theorem sourceSamplingEndpoint_measurable (r : Bool) : Measurable (sourceSamplingEndpoint r) := by
  cases r
  · exact measurable_fst
  · exact measurable_snd

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CompactTorus
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingTorusMap_continuous : Continuous sourceSamplingTorusMap := by
  exact (continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_apply i).comp continuous_fst))).prodMk
    (continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp continuous_snd)))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusModel
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

theorem sourceTorusQuotient_preserving : MeasurePreserving sourceTorusQuotient sourceSamplingHaar sourceTorusHaar := by
  refine ⟨Measurable.of_eval (fun i => sourceCircle_mk_preserving.measurable.comp (measurable_pi_apply i)),?_⟩
  unfold sourceTorusQuotient
  rw [Measure.infinitePi_map_pi _ (fun _ => sourceCircle_mk_preserving.measurable)]
  simp only [sourceCircle_mk_preserving.map_eq]

theorem sourceTorusRepresentative_preserving :
    MeasurePreserving sourceTorusRepresentative sourceTorusHaar sourceSamplingHaar := by
  refine ⟨Measurable.of_eval (fun i => sourceCircleRepresentative_measurable.comp (measurable_pi_apply i)),?_⟩
  unfold sourceTorusRepresentative
  rw [Measure.infinitePi_map_pi _ (fun _ => sourceCircleRepresentative_measurable)]
  simp only [sourceCircleRepresentative_preserving.map_eq]

theorem sourceTorusRepresentative_quotient (x : SourceCoordinate → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    sourceTorusRepresentative (sourceTorusQuotient x) = x := by
  funext i
  exact (sourceCircleRepresentative_coe (x i)).trans (Int.fract_eq_self.mpr (hx i))

/-- Change of variables for actual weighted laws across the real
representatives and compact torus, with the inverse needed only almost everywhere. -/
theorem sourceTorusQuotient_withDensity (w : (SourceCoordinate → ℝ) → ℝ≥0∞) (hw : Measurable w) :
    (sourceSamplingHaar.withDensity w).map sourceTorusQuotient =
      sourceTorusHaar.withDensity (fun z => w (sourceTorusRepresentative z)) := by
  ext A hA
  have hQ := sourceTorusQuotient_preserving
  have hR := sourceTorusRepresentative_preserving
  rw [Measure.map_apply hQ.measurable hA,withDensity_apply _ (hQ.measurable hA),withDensity_apply _ hA,
    ← lintegral_indicator (hQ.measurable hA),← lintegral_indicator hA]
  have hm := (hw.comp hR.measurable).indicator hA
  calc
    _ = ∫⁻ x, A.indicator (fun z => w (sourceTorusRepresentative z)) (sourceTorusQuotient x) ∂sourceSamplingHaar := by
      apply lintegral_congr_ae
      filter_upwards [sourceSamplingHaar_cube] with x hx
      change (if sourceTorusQuotient x ∈ A then w x else 0) =
        (if sourceTorusQuotient x ∈ A then w (sourceTorusRepresentative (sourceTorusQuotient x)) else 0)
      rw [sourceTorusRepresentative_quotient x hx]
    _ = _ := hQ.lintegral_comp hm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TorusMarginals
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceTorusEndpoint_measurable (r : Bool) : Measurable (sourceTorusEndpoint r) := by
  cases r
  · exact measurable_fst
  · exact measurable_snd

theorem sourceSamplingTorus_marginal_transport (μ : Measure SourceSamplingPair) (r : Bool)
    (g : (SourceCoordinate → ℝ) → ℝ) (hg : Measurable g)
    (hm : μ.map (sourceSamplingEndpoint r) = sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (g x))) :
    (μ.map sourceSamplingTorusMap).map (sourceTorusEndpoint r) =
      sourceTorusHaar.withDensity (fun z => ENNReal.ofReal (g (sourceTorusRepresentative z))) := by
  have he : sourceTorusEndpoint r ∘ sourceSamplingTorusMap = sourceTorusQuotient ∘ sourceSamplingEndpoint r := by
    funext p
    cases r <;> rfl
  rw [Measure.map_map (sourceTorusEndpoint_measurable r) sourceSamplingTorusMap_continuous.measurable,he,
    ← Measure.map_map sourceTorusQuotient_preserving.measurable (sourceSamplingEndpoint_measurable r),hm]
  exact sourceTorusQuotient_withDensity _ hg.ennreal_ofReal

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

theorem sourceBiasedRealMeasure_marginal (j : ℕ) (r : SourceCoordinate → Bool) (b : Bool) :
    (sourceBiasedRealMeasure j r).map (sourceSamplingEndpoint b) =
      (sourceBiasedLaw j).map (sourceBiasedEndpoint (if b then r else fun _ => false)) := by
  rw [sourceBiasedRealMeasure,Measure.map_map (sourceSamplingEndpoint_measurable b)
    (sourceBiasedPair_measurable r)]
  cases b <;> rfl

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

/-- Both mixed torus marginals have the same actual uniform L2 bound. -/
theorem sourceBiasedTorusMeasure_density (j : ℕ) (r : SourceCoordinate → Bool) (b : Bool) :
    ∃ g : SourceTorus → ℝ, Measurable g ∧ (∀ z, 0 ≤ g z) ∧
      MemLp g 2 sourceTorusHaar ∧
      (sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus).map (sourceTorusEndpoint b) =
        sourceTorusHaar.withDensity (fun z => ENNReal.ofReal (g z)) ∧
      (∫ z, g z^2 ∂sourceTorusHaar) ≤ Real.exp (20*(2*(∑' s,sourceKappa s^2)+1)) := by
  obtain ⟨f,hf,hf0,hflp,hfm,hfC⟩ := sourceBiasedEndpoint_density j (if b then r else fun _ => false)
  have hm : (sourceBiasedRealMeasure j r).map (sourceSamplingEndpoint b) =
      sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (f x)) :=
    (sourceBiasedRealMeasure_marginal j r b).trans hfm
  refine ⟨f ∘ sourceTorusRepresentative,hf.comp sourceTorusRepresentative_preserving.measurable,
    fun z => hf0 _,hflp.comp_measurePreserving sourceTorusRepresentative_preserving,
    sourceSamplingTorus_marginal_transport _ b f hf hm,?_⟩
  have he : (∫ z, (f (sourceTorusRepresentative z))^2 ∂sourceTorusHaar) =
      ∫ x, f x^2 ∂sourceSamplingHaar := by
    rw [← sourceTorusRepresentative_preserving.map_eq]
    exact (integral_map sourceTorusRepresentative_preserving.measurable.aemeasurable
      (hf.pow_const 2).aestronglyMeasurable).symm
  exact he.trans_le hfC

/-- Every endpoint of every mixed-prefix or full biased law belongs to any
prescribed Haar-conull Borel set. -/
theorem sourceBiasedTorusMeasure_marginal_ac (j : ℕ) (r : SourceCoordinate → Bool) (b : Bool) :
    (sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus).map (sourceTorusEndpoint b) ≪ sourceTorusHaar := by
  obtain ⟨g,_,_,_,hm,_⟩ := sourceBiasedTorusMeasure_density j r b
  rw [hm]
  exact withDensity_absolutelyContinuous _ _

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CompactZeroTransfer
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

/-- Compact subsets carrying uniformly almost all approximating mass carry
all limiting mass as their uniform losses tend to zero. -/
theorem finiteMeasure_ae_of_compact_approximation {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (μ : ℕ → FiniteMeasure X) (ν : FiniteMeasure X)
    (hlim : Tendsto μ atTop (𝓝 ν)) (Z : Set X) (hZ : MeasurableSet Z)
    (hcompact : ∀ ε : ℝ≥0, 0 < ε → ∃ K, IsCompact K ∧ K ⊆ Z ∧
      ∀ n, (μ n : Measure X) Kᶜ ≤ ε) :
    ∀ᵐ x ∂(ν : Measure X), x ∈ Z := by
  have hmass : Tendsto (fun n => (μ n : Measure X) Set.univ) atTop
      (𝓝 ((ν : Measure X) Set.univ)) := by
    simpa only [Function.comp_def, FiniteMeasure.ennreal_mass] using
      (ENNReal.continuous_coe.tendsto ν.mass).comp hlim.mass
  have hfull : (ν : Measure X) Set.univ ≤ (ν : Measure X) Z := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨K,hK,hKZ,hbound⟩ := hcompact ε hε
    have hle : ∀ n, (μ n : Measure X) Set.univ ≤ (μ n : Measure X) K + ε := by
      intro n
      rw [← measure_add_measure_compl hK.isClosed.measurableSet]
      exact add_le_add le_rfl (hbound n)
    have hsup := Filter.limsup_le_limsup (f := atTop) (Eventually.of_forall hle)
    rw [hmass.limsup_eq, limsup_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault)] at hsup
    exact hsup.trans (add_le_add
      ((FiniteMeasure.limsup_measure_closed_le_of_tendsto hlim hK.isClosed).trans
        (measure_mono hKZ)) le_rfl)
  rw [ae_iff]
  change (ν : Measure X) Zᶜ = 0
  rw [measure_compl hZ (by finiteness), tsub_eq_zero_of_le hfull]

/-- The loss outside a product compact set is bounded by its two marginal
losses. The identity set itself may only be Borel. -/
theorem measure_pair_compact_loss {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × X)) (Q : Set X) (hQ : MeasurableSet Q)
    (Z : Set (X × X)) (hZ : ∀ᵐ z ∂μ, z ∈ Z) :
    μ ((Q ×ˢ Q) ∩ Z)ᶜ ≤ (μ.map Prod.fst) Qᶜ + (μ.map Prod.snd) Qᶜ := by
  have he : (((Q ×ˢ Q) ∩ Z)ᶜ : Set (X × X)) =ᵐ[μ] ((Q ×ˢ Q)ᶜ : Set (X × X)) := by
    filter_upwards [hZ] with z hz
    apply propext
    change (¬ (z ∈ Q ×ˢ Q ∧ z ∈ Z)) ↔ ¬ z ∈ Q ×ˢ Q
    simp [hz]
  rw [measure_congr he]
  have hs : (Q ×ˢ Q)ᶜ = (Prod.fst ⁻¹' Qᶜ) ∪ (Prod.snd ⁻¹' Qᶜ) := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_prod, Set.mem_union, Set.mem_preimage]
    tauto
  rw [hs, Measure.map_apply measurable_fst hQ.compl,
    Measure.map_apply measurable_snd hQ.compl]
  exact measure_union_le _ _

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CompactGraphLusin
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

/-- A function whose graph is compact above Q is continuous on Q. -/
theorem continuousOn_of_compact_graph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] {f : X → Y} {K : Set (X × Y)} (hK : IsCompact K)
    (hgraph : ∀ z ∈ K, f z.1 = z.2) : ContinuousOn f (Prod.fst '' K) := by
  let Q := Prod.fst '' K
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let g : K → X := fun z => z.1.1
  have hg : Continuous g := continuous_fst.comp continuous_subtype_val
  have hi : Function.Injective g := by
    intro z w h
    apply Subtype.ext
    apply Prod.ext h
    exact (hgraph z.1 z.2).symm.trans ((congrArg f h).trans (hgraph w.1 w.2))
  have hmem (x : Q) : (x.1, f x.1) ∈ K := by
    obtain ⟨z,hz,hx⟩ := x.2
    have he : (x.1, f x.1) = z := by
      apply Prod.ext hx.symm
      simpa only [← hx] using hgraph z hz
    rwa [he]
  let inv : Q → K := fun x => ⟨(x.1, f x.1), hmem x⟩
  have hinv : Continuous inv :=
    (hg.isClosedEmbedding hi).isEmbedding.isInducing.continuous_iff.mpr continuous_subtype_val
  exact continuousOn_iff_continuous_domRestrict.mpr
    (continuous_snd.comp (continuous_subtype_val.comp hinv))

/-- Lusin's theorem on Polish spaces, obtained from compact subsets of the
measurable graph. The compact set can be required to lie in a prescribed
Borel conull set. -/
theorem exists_compact_lusin {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → Y} (hf : Measurable f) {s : Set X} (hs : MeasurableSet s)
    (hfull : ∀ᵐ x ∂μ, x ∈ s) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q, Q ⊆ s ∧ IsCompact Q ∧ μ Qᶜ < ε ∧ ContinuousOn f Q := by
  let graph : X → X × Y := fun x => (x,f x)
  have hgraph : Measurable graph := measurable_id.prodMk hf
  let G : Set (X × Y) := {z | z.1 ∈ s ∧ f z.1 = z.2}
  have hG : MeasurableSet G :=
    (hs.preimage measurable_fst).inter (measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd)
  let ν := μ.map graph
  obtain ⟨K,hKG,hK,hsmall⟩ := hG.exists_isCompact_sdiff_lt (μ := ν) (measure_ne_top _ _) hε
  let Q : Set X := Prod.fst '' K
  have hQ : IsCompact Q := hK.image continuous_fst
  have hQs : Q ⊆ s := by
    rintro x ⟨z,hz,rfl⟩
    exact (hKG hz).1
  have hmem (x : X) : graph x ∈ K ↔ x ∈ Q := by
    constructor
    · intro hx; exact ⟨graph x,hx,rfl⟩
    · rintro ⟨z,hz,hx⟩
      have he : graph x = z := by
        apply Prod.ext hx.symm
        simpa only [graph, ← hx] using (hKG hz).2
      rwa [he]
  have hpre : graph ⁻¹' (G \ K) = s \ Q := by
    ext x
    change ((x ∈ s ∧ f x = f x) ∧ graph x ∉ K) ↔ (x ∈ s ∧ x ∉ Q)
    rw [hmem]
    simp
  have hsmall' : μ (s \ Q) < ε := by
    have he : ν (G \ K) = μ (s \ Q) := by
      rw [Measure.map_apply hgraph (hG.diff hK.isClosed.measurableSet), hpre]
    rwa [he] at hsmall
  have heq : μ (s \ Q) = μ Qᶜ := by
    apply measure_congr
    filter_upwards [hfull] with x hx
    apply propext
    change (x ∈ s ∧ x ∉ Q) ↔ x ∉ Q
    simp [hx]
  refine ⟨Q,hQs,hQ,heq ▸ hsmall',?_⟩
  exact continuousOn_of_compact_graph hK (fun z hz => (hKG hz).2)

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

theorem boundedMatrixOperator_norm (hC : 0 ≤ C) : ‖boundedMatrixOperator m C hb‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le fiberFiniteEmbedding_dense hC
    (fiberMatrixFinite_norm_le m C hb hC)

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

theorem sourceMatrixEntry_measurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (k n : ℤ) :
    Measurable (sourceMatrixEntry H k n) :=
  (Lp.stronglyMeasurable (H (sourceBasis n))).measurable.comp
    (measurable_id.prodMk measurable_const)

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

theorem sourceOperatorField_norm
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (x) :
    ‖sourceOperatorField H x‖ ≤ ‖H‖ := by
  classical
  unfold sourceOperatorField
  split_ifs
  · exact boundedMatrixOperator_norm _ _ _ (norm_nonneg H)
  · simp

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

/-- Coordinate measurability suffices for strong measurability in l2(Z). -/
theorem fiberCoordinates_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (f : X → SourceFiberHilbert) (hf : ∀ n : ℤ, Measurable (fun x => f x n)) :
    StronglyMeasurable f := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ n ∈ s, lp.single 2 n (f x n))
  · intro s
    have h (n : ℤ) : StronglyMeasurable (fun x => (lp.single 2 n (f x n) : SourceFiberHilbert)) :=
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp_stronglyMeasurable
        (hf n).stronglyMeasurable
    convert Finset.stronglyMeasurable_sum s (fun n _ => h n) using 1
    funext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (f x)

/-- Every basis column of the actual field is a strongly measurable l2 vector. -/
theorem sourceOperatorField_basis_stronglyMeasurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (n : ℤ) :
    StronglyMeasurable (fun x => sourceOperatorField H x (lp.single 2 n (1 : ℂ))) :=
  fiberCoordinates_stronglyMeasurable _ (fun k => sourceOperatorField_entry_measurable H k n)

theorem sourceOperatorField_stronglyMeasurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (v : SourceFiberHilbert) : StronglyMeasurable (fun x => sourceOperatorField H x v) := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ n ∈ s, v n • sourceOperatorField H x (lp.single 2 n (1 : ℂ)))
  · intro s
    have h (n : ℤ) : StronglyMeasurable (fun x => v n • sourceOperatorField H x (lp.single 2 n (1 : ℂ))) :=
      (sourceOperatorField_basis_stronglyMeasurable H n).const_smul (v n)
    convert Finset.stronglyMeasurable_sum s (fun n _ => h n) using 1
    funext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact fiberOperator_hasSum (sourceOperatorField H x) v

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusOperatorField
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceTorusOperatorField_stronglyMeasurable
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (v : SourceFiberHilbert) :
    StronglyMeasurable (fun z => sourceTorusOperatorField H z v) :=
  (sourceOperatorField_stronglyMeasurable H v).comp_measurable sourceTorusRepresentative_preserving.measurable

theorem sourceTorusOperatorField_norm
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (z : SourceTorus) :
    ‖sourceTorusOperatorField H z‖ ≤ ‖H‖ := sourceOperatorField_norm H _

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_LusinCompact
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- All cocycles and all vector columns of the actual operator field are
continuous on one compact subset of any prescribed Borel conull set. -/
theorem exists_source_lusin_compact (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    {s : Set SourceTorus} (hs : MeasurableSet s) (hfull : ∀ᵐ z ∂sourceTorusHaar, z ∈ s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q, Q ⊆ s ∧ IsCompact Q ∧ sourceTorusHaar Qᶜ < ε ∧
      (∀ k : ℤ, ContinuousOn
        (fun z => sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z)) Q) ∧
      (∀ k : ℤ, ContinuousOn
        (fun z => sourceTorusOperatorField H z (lp.single 2 k (1 : ℂ))) Q) := by
  borelize (↥SourceFiberHilbert)
  let f : SourceTorus → (ℤ → ℝ × SourceFiberHilbert) := fun z k =>
    (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z),
      sourceTorusOperatorField H z (lp.single 2 k (1 : ℂ)))
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro k
    exact ((sourceCocycle_measurable θ sourceLogWeight k).comp
      sourceTorusRepresentative_preserving.measurable).prodMk
        (sourceTorusOperatorField_stronglyMeasurable H (lp.single 2 k (1 : ℂ))).measurable
  obtain ⟨Q,hQs,hQ,hμQ,hfQ⟩ := exists_compact_lusin sourceTorusHaar hf hs hfull hε
  refine ⟨Q,hQs,hQ,hμQ,?_,?_⟩
  · intro k
    exact continuous_fst.comp_continuousOn ((continuous_apply k).comp_continuousOn hfQ)
  · intro k
    exact continuous_snd.comp_continuousOn ((continuous_apply k).comp_continuousOn hfQ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_StrongContinuity
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped Topology
noncomputable section

/-- A uniformly bounded field is strongly continuous wherever all its basis
columns are continuous. No norm-continuity of the field is required. -/
theorem fiberField_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (Q : Set X)
    (C : ℝ) (hC : ∀ x ∈ Q, ‖A x‖ ≤ C)
    (hb : ∀ k : ℤ, ContinuousOn (fun x => A x (lp.single 2 k (1 : ℂ))) Q)
    (v : SourceFiberHilbert) : ContinuousOn (fun x => A x v) Q := by
  classical
  let w : Finset ℤ → SourceFiberHilbert := fun s => ∑ k ∈ s, lp.single 2 k (v k)
  have hw : Tendsto w atTop (𝓝 v) := lp.hasSum_single (by norm_num) v
  have he : Tendsto (fun s => C * ‖v - w s‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := v)).sub hw).norm.const_mul C
  have hu : TendstoUniformlyOn (fun s x => A x (w s)) (fun x => A x v) atTop Q := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp he).2 ε hε] with s hs x hx
    rw [dist_eq_norm, ← map_sub]
    exact ((A x).le_opNorm (v - w s)).trans_lt
      ((mul_le_mul_of_nonneg_right (hC x hx) (norm_nonneg _)).trans_lt hs)
  apply hu.continuousOn
  apply Filter.Eventually.frequently
  apply Eventually.of_forall
  intro s
  have hh : (fun x => A x (w s)) =
      fun x => ∑ k ∈ s, (v k) • A x (lp.single 2 k (1 : ℂ)) := by
    funext x
    simp only [w, map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show lp.single 2 k (v k) = (v k) • (lp.single 2 k (1 : ℂ) : SourceFiberHilbert) by
      simp [← lp.single_smul], map_smul]
  rw [hh]
  exact continuousOn_finsetSum s (fun k _ => (hb k).const_smul (v k))

/-- Evaluation on a varying continuous vector preserves strong continuity
under a uniform operator bound. -/
theorem fiberField_continuousOn_apply {X : Type*} [TopologicalSpace X]
    (A : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (Q : Set X)
    (C : ℝ) (hC : ∀ x ∈ Q, ‖A x‖ ≤ C)
    (hA : ∀ v, ContinuousOn (fun x => A x v) Q)
    (v : X → SourceFiberHilbert) (hv : ContinuousOn v Q) :
    ContinuousOn (fun x => A x (v x)) Q := by
  intro x hx
  have he : Tendsto (fun y => C * ‖v y - v x‖) (𝓝[Q] x) (𝓝 0) := by
    simpa using ((hv x hx).sub_const (v x)).norm.const_mul C
  have hzero : Tendsto (fun y => A y (v y - v x)) (𝓝[Q] x) (𝓝 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((A y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _))
  have ht := hzero.add (hA (v x) x hx)
  change Tendsto _ _ _
  simpa only [map_sub, sub_add_cancel, zero_add] using ht

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_Diagonal
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem fiberDiagonal_norm (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) :
    ‖fiberDiagonal d hd‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem fiberDiagonal_single (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) (n : ℤ) :
    fiberDiagonal d hd (lp.single 2 n (1 : ℂ)) = d n • lp.single 2 n (1 : ℂ) := by
  classical
  apply Subtype.ext
  funext k
  change d k * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) k =
    d n * (lp.single 2 n (1 : ℂ) : SourceFiberHilbert) k
  by_cases h : n = k
  · subst k; rfl
  · simp [lp.single_apply, h]

theorem fiberDiagonal_continuousOn {X : Type*} [TopologicalSpace X]
    (d : X → ℤ → ℂ) (hd : ∀ x k, ‖d x k‖ ≤ 1) (Q : Set X)
    (hc : ∀ k, ContinuousOn (fun x => d x k) Q) (v : SourceFiberHilbert) :
    ContinuousOn (fun x => fiberDiagonal (d x) (hd x) v) Q := by
  apply fiberField_continuousOn _ Q 1 (fun x _ => fiberDiagonal_norm _ _) _ v
  intro k
  simp_rw [fiberDiagonal_single]
  exact (hc k).smul continuousOn_const

theorem fiberDiagonal_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (d : X → ℤ → ℂ) (hd : ∀ x k, ‖d x k‖ ≤ 1)
    (hm : ∀ k, Measurable (fun x => d x k)) (v : SourceFiberHilbert) :
    StronglyMeasurable (fun x => fiberDiagonal (d x) (hd x) v) := by
  apply fiberCoordinates_stronglyMeasurable
  intro k
  exact (hm k).mul_const (v k)

/-- Applying a measurable field to a measurable vector uses finite coordinate
approximations, without measurability in the operator norm topology. -/
theorem fiberField_stronglyMeasurable_apply {X : Type*} [MeasurableSpace X]
    (A : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hA : ∀ v, StronglyMeasurable (fun x => A x v))
    (v : X → SourceFiberHilbert) (hv : StronglyMeasurable v) :
    StronglyMeasurable (fun x => A x (v x)) := by
  classical
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ k ∈ s, (v x k) • A x (lp.single 2 k (1 : ℂ)))
  · intro s
    have h (k : ℤ) : StronglyMeasurable (fun x => (v x k) • A x (lp.single 2 k (1 : ℂ))) :=
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous.comp_stronglyMeasurable hv).smul
        (hA (lp.single 2 k (1 : ℂ))))
    convert Finset.stronglyMeasurable_sum s (fun k _ => h k) using 1
    ext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact fiberOperator_hasSum (A x) (v x)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_PairZeroSet
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem fiberPairResidual_eq_zero_iff {X : Type*}
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1) (z : X × X) :
    fiberPairResidual P d hd z = 0 ↔
      ∀ k : ℤ, fiberPairResidual P d hd z (lp.single 2 k (1 : ℂ)) = 0 := by
  constructor
  · intro h k; rw [h]; rfl
  · intro h
    apply fiberOperator_ext
    intro k n
    rw [h n]
    rfl

theorem fiberPairResidual_continuousOn {X : Type*} [TopologicalSpace X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (Q : Set X) (C : ℝ) (hC : ∀ x ∈ Q, ‖P x‖ ≤ C)
    (hP : ∀ k : ℤ, ContinuousOn (fun x => P x (lp.single 2 k (1 : ℂ))) Q)
    (hdc : ∀ k, ContinuousOn (fun z => d z k) (Q ×ˢ Q)) (v : SourceFiberHilbert) :
    ContinuousOn (fun z => fiberPairResidual P d hd z v) (Q ×ˢ Q) := by
  have hPs (w : SourceFiberHilbert) := fiberField_continuousOn P Q C hC hP w
  have hx (w : SourceFiberHilbert) : ContinuousOn (fun z : X × X => P z.1 w) (Q ×ˢ Q) :=
    (hPs w).comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hy (w : SourceFiberHilbert) : ContinuousOn (fun z : X × X => P z.2 w) (Q ×ˢ Q) :=
    (hPs w).comp continuous_snd.continuousOn (fun z hz => hz.2)
  have hD (w : SourceFiberHilbert) := fiberDiagonal_continuousOn d hd (Q ×ˢ Q) hdc w
  have hv := fiberField_continuousOn_apply (fun z => fiberDiagonal (d z) (hd z))
    (Q ×ˢ Q) 1 (fun z _ => fiberDiagonal_norm _ _) hD (fun z => P z.1 v) (hx v)
  have hpv := fiberField_continuousOn_apply (fun z : X × X => P z.2)
    (Q ×ˢ Q) C (fun z hz => hC z.2 hz.2) hy _ hv
  exact hv.sub hpv

theorem fiberPairResidual_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (hP : ∀ v, StronglyMeasurable (fun x => P x v))
    (hdm : ∀ k, Measurable (fun z => d z k)) (v : SourceFiberHilbert) :
    StronglyMeasurable (fun z => fiberPairResidual P d hd z v) := by
  have hv := fiberField_stronglyMeasurable_apply (fun z => fiberDiagonal (d z) (hd z))
    (fun w => fiberDiagonal_stronglyMeasurable d hd hdm w)
    (fun z => P z.1 v) ((hP v).comp_measurable measurable_fst)
  have hpv := fiberField_stronglyMeasurable_apply (fun z : X × X => P z.2)
    (fun w => (hP w).comp_measurable measurable_snd) _ hv
  exact hv.sub hpv

theorem fiberPairZeroSet_measurable {X : Type*} [MeasurableSpace X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (hP : ∀ v, StronglyMeasurable (fun x => P x v))
    (hdm : ∀ k, Measurable (fun z => d z k)) :
    MeasurableSet {z | fiberPairResidual P d hd z = 0} := by
  borelize (↥SourceFiberHilbert)
  simp_rw [fiberPairResidual_eq_zero_iff, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun k => measurableSet_eq_fun
    (fiberPairResidual_stronglyMeasurable P d hd hP hdm _).measurable measurable_const)

theorem fiberPairZeroSet_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1)
    (Q : Set X) (hQ : IsCompact Q) (C : ℝ) (hC : ∀ x ∈ Q, ‖P x‖ ≤ C)
    (hP : ∀ k : ℤ, ContinuousOn (fun x => P x (lp.single 2 k (1 : ℂ))) Q)
    (hdc : ∀ k, ContinuousOn (fun z => d z k) (Q ×ˢ Q)) :
    IsCompact ((Q ×ˢ Q) ∩ {z | fiberPairResidual P d hd z = 0}) := by
  have he : ((Q ×ˢ Q) ∩ {z | fiberPairResidual P d hd z = 0}) =
      ⋂ k : ℤ, ((Q ×ˢ Q) ∩ {z | fiberPairResidual P d hd z (lp.single 2 k (1 : ℂ)) = 0}) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter,
      fiberPairResidual_eq_zero_iff]
    constructor
    · rintro ⟨hz,h⟩ k; exact ⟨hz,h k⟩
    · intro h; exact ⟨(h 0).1,fun k => (h k).2⟩
  apply (hQ.prod hQ).of_isClosed_subset _ Set.inter_subset_left
  rw [he]
  apply isClosed_iInter
  intro k
  exact (fiberPairResidual_continuousOn P d hd Q C hC hP hdc _).preimage_isClosed_of_isClosed
    (hQ.prod hQ).isClosed isClosed_singleton

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CappedPair
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

theorem sourceCappedRatio_measurable (θ : SourceCoordinate → ℝ) (k : ℤ) :
    Measurable (fun z => sourceCappedRatio θ z k) := by
  apply Complex.measurable_ofReal.comp
  apply Measurable.min _ measurable_const
  exact (((sourceCocycle_measurable θ sourceLogWeight k).comp
    sourceTorusRepresentative_preserving.measurable).comp measurable_snd).div
    (((sourceCocycle_measurable θ sourceLogWeight k).comp
      sourceTorusRepresentative_preserving.measurable).comp measurable_fst)

theorem sourceCappedRatio_continuousOn (θ : SourceCoordinate → ℝ) (Q : Set SourceTorus)
    (hF : ∀ k : ℤ, ContinuousOn
      (fun z => sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z)) Q) (k : ℤ) :
    ContinuousOn (fun z => sourceCappedRatio θ z k) (Q ×ˢ Q) := by
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.inf _ continuousOn_const
  exact ((hF k).comp continuous_snd.continuousOn (fun z hz => hz.2)).div
    ((hF k).comp continuous_fst.continuousOn (fun z hz => hz.1))
    (fun z _ => ne_of_gt (sourceCocycle_pos ..))

theorem sourceCappedPairZeroSet_measurable (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    MeasurableSet (sourceCappedPairZeroSet θ H) :=
  fiberPairZeroSet_measurable _ _ _ (sourceTorusOperatorField_stronglyMeasurable H)
    (sourceCappedRatio_measurable θ)

/-- The compact zero sets needed for Portmanteau are constructed from the
actual field and original cocycles, with arbitrarily small Haar loss. -/
theorem exists_source_capped_compact (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    {s : Set SourceTorus} (hs : MeasurableSet s) (hfull : ∀ᵐ z ∂sourceTorusHaar, z ∈ s)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q, Q ⊆ s ∧ IsCompact Q ∧ sourceTorusHaar Qᶜ < ε ∧
      IsCompact ((Q ×ˢ Q) ∩ sourceCappedPairZeroSet θ H) := by
  obtain ⟨Q,hQs,hQ,hμQ,hF,hP⟩ := exists_source_lusin_compact θ H hs hfull hε
  exact ⟨Q,hQs,hQ,hμQ,fiberPairZeroSet_compact _ _ _ Q hQ ‖H‖
    (fun z _ => sourceTorusOperatorField_norm H z) hP
      (sourceCappedRatio_continuousOn θ Q hF)⟩

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

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_L2UniformAbsoluteContinuity
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

/-- Cauchy--Schwarz bounds the mass of any Borel set under an actual L2
density, in terms of the original reference measure of the set. -/
theorem withDensity_L2_set_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (g : X → ℝ)
    (hg : MemLp g 2 μ) (hg0 : ∀ x, 0 ≤ g x)
    (A : Set X) (hA : MeasurableSet A) (C : ℝ) (hC : (∫ x, g x ^ 2 ∂μ) ≤ C) :
    (μ.withDensity (fun x => ENNReal.ofReal (g x))) A ≤
      ENNReal.ofReal (Real.sqrt C * Real.sqrt ((μ A).toReal)) := by
  have hi : MemLp (A.indicator (fun _ : X => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hA
  have hcs := integral_mul_le_sqrt_squares hg hi
    (Eventually.of_forall hg0)
    (Eventually.of_forall (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
  have hint : (∫ x, g x * A.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = ∫ x in A, g x ∂μ := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ A <;> simp [hx]
  have hsquare : (∫ x, (A.indicator (fun _ : X => (1 : ℝ)) x) ^ 2 ∂μ) = (μ A).toReal := by
    have he : (fun x => (A.indicator (fun _ : X => (1 : ℝ)) x) ^ 2) =
        A.indicator (fun _ : X => (1 : ℝ)) := by
      funext x; by_cases hx : x ∈ A <;> simp [hx]
    rw [he, integral_indicator hA]
    simp [measureReal_def]
  rw [hint, hsquare] at hcs
  rw [withDensity_apply _ hA, ← ofReal_integral_eq_lintegral_ofReal
    (hg.integrable (by norm_num)).restrict (Eventually.of_forall hg0)]
  exact ENNReal.ofReal_le_ofReal (hcs.trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hC) (Real.sqrt_nonneg _)))

/-- Uniform L2 density bounds imply uniform absolute continuity, with no
measurable-selection premise for the densities. -/
theorem uniformAC_of_L2_densities {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ℕ → Measure X) (C : ℝ)
    (hν : ∀ n, ∃ g : X → ℝ, MemLp g 2 μ ∧ (∀ x, 0 ≤ g x) ∧
      ν n = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧ (∫ x, g x^2 ∂μ) ≤ C)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ A, MeasurableSet A → μ A < δ → ∀ n, ν n A ≤ ε := by
  let r : ℝ := (ε : ℝ) / (Real.sqrt C + 1)
  have hr : 0 < r := div_pos (by exact_mod_cast hε) (by positivity)
  refine ⟨ENNReal.ofReal (r^2), ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr), ?_⟩
  intro A hA hμ n
  obtain ⟨g,hg,hg0,he,hgC⟩ := hν n
  rw [he]
  apply (withDensity_L2_set_le μ g hg hg0 A hA C hgC).trans
  have hreal : (μ A).toReal ≤ r^2 := by
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hμ.le)
  have hs : Real.sqrt ((μ A).toReal) ≤ r := by
    exact (Real.sqrt_le_sqrt hreal).trans_eq (Real.sqrt_sq hr.le)
  have hmul : Real.sqrt C * r ≤ (ε : ℝ) := by
    have heq : r * (Real.sqrt C + 1) = (ε : ℝ) := div_mul_cancel₀ _ (by positivity)
    nlinarith [Real.sqrt_nonneg C]
  exact (ENNReal.ofReal_le_ofReal
    ((mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg C)).trans hmul)).trans_eq (by simp)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_UncappedPairIdentity
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceCappedRatio_eq_ratio (θ : SourceCoordinate → ℝ) (z : SourceSamplingTorus)
    (hx : finiteFloorSupport θ (sourceTorusRepresentative z.1))
    (hy : finiteFloorSupport θ (sourceTorusRepresentative z.2))
    (hord : ∀ i, sourceTorusRepresentative z.1 i ≤ sourceTorusRepresentative z.2 i) (k : ℤ) :
    sourceCappedRatio θ z k =
      (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.2) /
        sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.1) : ℝ) := by
  unfold sourceCappedRatio
  rw [min_eq_left ((div_le_one (sourceCocycle_pos ..)).mpr
    (sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hx hy hord k))]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_Conull
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

theorem sourceBiasedEndpoint_cube (j : ℕ) (r : SourceCoordinate → Bool) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ∀ i, sourceBiasedEndpoint r ω i ∈ Set.Ico (0 : ℝ) 1 := by
  obtain ⟨g,_,_,_,hm,_⟩ := sourceBiasedEndpoint_density j r
  have ha : (sourceBiasedLaw j).map (sourceBiasedEndpoint r) ≪ sourceSamplingHaar := by
    rw [hm]
    exact withDensity_absolutelyContinuous _ _
  exact ae_of_ae_map (sourceBiasedEndpoint_measurable r).aemeasurable
    (ha.ae_le sourceSamplingHaar_cube)

theorem sourceBiasedLaw_ordered (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ∀ i, (ω i).2.1 ≤ (ω i).2.2 := by
  apply ae_all_iff.mpr
  intro i
  have ha : ∀ᵐ z ∂(stagedCouplingParameters j i.1).labelledCoupling, z.2.1 ≤ z.2.2 := by
    rw [ae_iff]
    change (stagedCouplingParameters j i.1).labelledCoupling {z | z.2.1 ≤ z.2.2}ᶜ = 0
    have hmeas : MeasurableSet {z : Fin 6 × (ℝ × ℝ) | z.2.1 ≤ z.2.2} :=
      measurableSet_le (by fun_prop) (by fun_prop)
    rw [measure_compl hmeas (measure_ne_top _ _),
      measure_univ,labelledCoupling_ordered,tsub_self]
  exact (measurePreserving_eval_infinitePi
    (fun i : SourceCoordinate => (stagedCouplingParameters j i.1).labelledCoupling) i).quasiMeasurePreserving.ae ha

/-- Every mixed law, including nu_j, is carried by the actual ordered representatives. -/
theorem sourceBiasedTorusMeasure_ordered (j : ℕ) (r : SourceCoordinate → Bool) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus),
      ∀ i, sourceTorusRepresentative z.1 i ≤ sourceTorusRepresentative z.2 i := by
  have hm : MeasurableSet {z : SourceSamplingTorus | ∀ i,
      sourceTorusRepresentative z.1 i ≤ sourceTorusRepresentative z.2 i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_fst))
      ((measurable_pi_apply i).comp (sourceTorusRepresentative_preserving.measurable.comp measurable_snd))
  apply (ae_map_iff sourceSamplingTorusMap_continuous.measurable.aemeasurable hm).mpr
  apply (ae_map_iff (sourceBiasedPair_measurable r).aemeasurable
    (hm.preimage sourceSamplingTorusMap_continuous.measurable)).mpr
  filter_upwards [sourceBiasedEndpoint_cube j (fun _ => false),sourceBiasedEndpoint_cube j r,
    sourceBiasedLaw_ordered j] with ω hx hy hord
  change ∀ i, sourceTorusRepresentative (sourceTorusQuotient (sourceBiasedEndpoint (fun _ => false) ω)) i ≤
    sourceTorusRepresentative (sourceTorusQuotient (sourceBiasedEndpoint r ω)) i
  rw [sourceTorusRepresentative_quotient _ hx,sourceTorusRepresentative_quotient _ hy]
  intro i
  cases hr : r i
  · simp [sourceBiasedEndpoint,blockProductEndpoint,endpoint,hr]
  · simpa [sourceBiasedEndpoint,blockProductEndpoint,endpoint,hr] using hord i

/-- The same Borel conull set works for both endpoints of every actual biased
or mixed-prefix coupling; there is no new null-set choice for each identity. -/
theorem sourceBiasedTorusMeasure_endpoints_conull (j : ℕ) (r : SourceCoordinate → Bool)
    (Q : Set SourceTorus) (hQ : ∀ᵐ z ∂sourceTorusHaar, z ∈ Q) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus), z.1 ∈ Q ∧ z.2 ∈ Q :=
  (ae_of_ae_map (sourceTorusEndpoint_measurable false).aemeasurable
    ((sourceBiasedTorusMeasure_marginal_ac j r false).ae_le hQ)).and
  (ae_of_ae_map (sourceTorusEndpoint_measurable true).aemeasurable
    ((sourceBiasedTorusMeasure_marginal_ac j r true).ae_le hQ))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_PrefixLimit
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

theorem sourceBiasedPrefixPair_tendsto (ω : SourceBiasedSample) :
    Tendsto (fun n => sourceBiasedPair (sourceBiasedPrefixMask n) ω) atTop
      (𝓝 (sourceBiasedPair (fun _ => true) ω)) := by
  apply Tendsto.prodMk_nhds tendsto_const_nhds
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i.1] with n hn
  simp [sourceBiasedEndpoint,CouplingParameters.blockProductEndpoint,
    sourceBiasedPrefixMask,hn]

/-- The actual beta_n converge weakly to the actual full biased law nu_j. -/
theorem sourceBiasedPrefix_weak (j : ℕ) :
    Tendsto (fun n => sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n)) atTop
      (𝓝 (sourceBiasedTorusMeasure j (fun _ => true))) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hmap (r : SourceCoordinate → Bool) :
      (∫ z, f z ∂(sourceBiasedTorusMeasure j r : Measure SourceSamplingTorus)) =
        ∫ ω, f (sourceSamplingTorusMap (sourceBiasedPair r ω)) ∂sourceBiasedLaw j := by
    change (∫ z, f z ∂((sourceBiasedLaw j).map (sourceBiasedPair r)).map sourceSamplingTorusMap) = _
    rw [integral_map sourceSamplingTorusMap_continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
    exact integral_map (sourceBiasedPair_measurable r).aemeasurable
        (f.continuous.comp sourceSamplingTorusMap_continuous).aestronglyMeasurable
  simp_rw [hmap]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact ((f.continuous.comp sourceSamplingTorusMap_continuous).measurable.comp
      (sourceBiasedPair_measurable _)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun ω => f.norm_coe_le_norm _
  · apply Eventually.of_forall
    intro ω
    exact (f.continuous.comp sourceSamplingTorusMap_continuous).continuousAt.tendsto.comp
      (sourceBiasedPrefixPair_tendsto ω)

/-- Uniform absolute continuity covers every prefix and both endpoint choices. -/
theorem sourceBiasedPrefix_uniformAC (j : ℕ) (b : Bool) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ A, MeasurableSet A → sourceTorusHaar A < δ → ∀ n,
      ((sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n) : Measure SourceSamplingTorus).map
        (sourceTorusEndpoint b)) A ≤ ε := by
  apply uniformAC_of_L2_densities sourceTorusHaar _
    (Real.exp (20*(2*(∑' s,sourceKappa s^2)+1))) _ ε hε
  intro n
  obtain ⟨g,_hg,hg0,hglp,hm,hC⟩ := sourceBiasedTorusMeasure_density j (sourceBiasedPrefixMask n) b
  exact ⟨g,hglp,hg0,hm,hC⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_PairIdentity
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

/-- Weak transfer to the actual full biased law. Uniform absolute continuity
and the common compact zero sets have all been proved for these actual laws. -/
theorem sourceProjection_biased_pairs (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j (fun _ => true) : Measure SourceSamplingTorus),
      z ∈ sourceCappedPairZeroSet θ p := by
  apply finiteMeasure_ae_of_compact_approximation _ _ (sourceBiasedPrefix_weak j) _
    (sourceCappedPairZeroSet_measurable θ p)
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨δ₁,hδ₁,h₁⟩ := sourceBiasedPrefix_uniformAC j false (ε / 2) hhalf
  obtain ⟨δ₂,hδ₂,h₂⟩ := sourceBiasedPrefix_uniformAC j true (ε / 2) hhalf
  obtain ⟨Q,_,hQ,hμQ,hK⟩ := exists_source_capped_compact θ p
    MeasurableSet.univ (Eventually.of_forall (fun _ => Set.mem_univ _))
    (ne_of_gt (lt_min hδ₁ hδ₂))
  refine ⟨(Q ×ˢ Q) ∩ sourceCappedPairZeroSet θ p,hK,Set.inter_subset_right,?_⟩
  intro n
  have hb₁ := h₁ Qᶜ hQ.isClosed.measurableSet.compl
    (hμQ.trans_le (min_le_left _ _)) n
  have hb₂ := h₂ Qᶜ hQ.isClosed.measurableSet.compl
    (hμQ.trans_le (min_le_right _ _)) n
  have hb := add_le_add hb₁ hb₂
  have he : (↑(ε / 2) : ℝ≥0∞) + ↑(ε / 2) = ε := by
    rw [← ENNReal.coe_add,add_halves]
  rw [he] at hb
  exact (measure_pair_compact_loss _ Q hQ.isClosed.measurableSet _
    (sourceProjection_biased_prefix_pairs θ hθ hs hp hproj hinv j n)).trans hb

/-- Both endpoints of every actual biased law have finite floor support. -/
theorem sourceBiased_endpoints_finiteFloor (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j (fun _ => true) : Measure SourceSamplingTorus),
      finiteFloorSupport θ (sourceTorusRepresentative z.1) ∧
      finiteFloorSupport θ (sourceTorusRepresentative z.2) := by
  have hf := sourceTorusRepresentative_preserving.quasiMeasurePreserving.ae
    (ae_finiteFloorSupport θ hθ.summable)
  exact sourceBiasedTorusMeasure_endpoints_conull j (fun _ => true) _ hf

/-- The full uncapped invariant-projection identity under the constructed nu_j.
The bounded diagonal acts by the original cocycle ratio on every l2 vector. -/
theorem sourceProjection_biased_ratio_identity (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) :
    ∀ᵐ z ∂(sourceBiasedTorusMeasure j (fun _ => true) : Measure SourceSamplingTorus),
      ∃ D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert,
        ‖D‖ ≤ 1 ∧
        (∀ (v : SourceFiberHilbert) (k : ℤ), D v k =
          (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.2) /
            sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.1) : ℂ) * v k) ∧
        (1-sourceTorusOperatorField p z.2)*D*sourceTorusOperatorField p z.1 = 0 := by
  filter_upwards [sourceProjection_biased_pairs θ hθ hs hp hproj hinv j,
    sourceBiased_endpoints_finiteFloor θ hθ j,sourceBiasedTorusMeasure_ordered j (fun _ => true)]
    with z hz hf hord
  refine ⟨fiberDiagonal (sourceCappedRatio θ z) (sourceCappedRatio_norm θ z),
    fiberDiagonal_norm _ _,?_,hz⟩
  intro v k
  rw [fiberDiagonal_apply,sourceCappedRatio_eq_ratio θ z hf.1 hf.2 hord k,Complex.ofReal_div]

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

/-- The full uncapped pair identity on the actual augmented probability space,
with the original real endpoints and original operator fields. -/
theorem sourceProjection_biased_ratio_augmented_oai (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j,
      ∃ D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert,
        ‖D‖ ≤ 1 ∧
        (∀ (v : SourceFiberHilbert) (k : ℤ), D v k =
          (sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
            sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) : ℂ) * v k) ∧
        (1-sourceOperatorField p (sourceBiasedEndpoint (fun _ => true) ω))*D*
          sourceOperatorField p (sourceBiasedEndpoint (fun _ => false) ω) = 0 := by
  have ht := sourceProjection_biased_ratio_identity θ hθ hs hp hproj hinv j
  have hr := ae_of_ae_map sourceSamplingTorusMap_continuous.measurable.aemeasurable ht
  have ha := ae_of_ae_map (sourceBiasedPair_measurable (fun _ => true)).aemeasurable hr
  filter_upwards [ha,sourceBiasedEndpoint_cube j (fun _ => false),
    sourceBiasedEndpoint_cube j (fun _ => true)] with ω hω hx hy
  obtain ⟨D,hDn,hDa,hD⟩ := hω
  have hxe : sourceTorusRepresentative
      (sourceSamplingTorusMap (sourceBiasedPair (fun _ => true) ω)).1 =
        sourceBiasedEndpoint (fun _ => false) ω := sourceTorusRepresentative_quotient _ hx
  have hye : sourceTorusRepresentative
      (sourceSamplingTorusMap (sourceBiasedPair (fun _ => true) ω)).2 =
        sourceBiasedEndpoint (fun _ => true) ω := sourceTorusRepresentative_quotient _ hy
  refine ⟨D,hDn,?_,?_⟩
  · simpa only [hxe,hye] using hDa
  · simpa only [sourceTorusOperatorField,hxe,hye] using hD

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceProjection_biased_ratio_augmented_oai := @OAI.FiniteFactor.sourceProjection_biased_ratio_augmented_oai
