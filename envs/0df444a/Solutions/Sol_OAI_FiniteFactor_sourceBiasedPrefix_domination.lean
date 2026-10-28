-- Prove2me | solution 1 for OAI.FiniteFactor.sourceBiasedPrefix_domination
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:36:04.145738+00:00
-- url     : https://prove2.me/submissions/39855bc4-a8bd-4f80-9140-1c0b6342f2cd

import Mathlib
import Definitions.Def_OAIQ3Ff002

section
-- module Solutions.OAIQ3_FF.Compat
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

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
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_LimitMeasure
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingLimitMap_measurable (I : Finset SourceCoordinate) :
    Measurable (sourceSamplingLimitMap I) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval (fun i => measurable_fst.comp (measurable_pi_apply i))
  · apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ I
    · simpa only [hi,ite_true,Function.comp_def] using measurable_snd.comp (measurable_pi_apply i)
    · simpa only [hi,ite_false,Function.comp_def] using measurable_fst.comp (measurable_pi_apply i)

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
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_OrderedRestriction
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

theorem sourceSamplingOrdered_measurable : MeasurableSet sourceSamplingOrdered := by
  simp only [sourceSamplingOrdered,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le
    ((measurable_pi_apply i).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd))

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

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_FiniteProductAbsoluteContinuity
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal
noncomputable section

/-- Replacing one independent coordinate is a measurable pushforward of a
single fresh draw and the original full product. -/
theorem infinitePi_update_law {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    (i : ι) (ν : Measure X) [IsProbabilityMeasure ν] :
    (ν.prod (Measure.infinitePi μ)).map (fun z : X × (ι → X) => Function.update z.2 i z.1) =
      Measure.infinitePi (Function.update μ i ν) := by
  let : ∀ k, IsProbabilityMeasure (Function.update μ i ν k) := fun k => by
    by_cases hk : k = i
    · subst k; simpa using (inferInstance : IsProbabilityMeasure ν)
    · simpa [Function.update_of_ne hk] using (inferInstance : IsProbabilityMeasure (μ k))
  have hm : Measurable (fun z : X × (ι → X) => Function.update z.2 i z.1) := by
    apply Measurable.of_eval
    intro k
    by_cases hk : k = i
    · subst k; simpa using (measurable_fst : Measurable (Prod.fst : X × (ι → X) → X))
    · simpa [Function.update_of_ne hk,Function.comp_def] using (measurable_pi_apply k).comp
        (measurable_snd : Measurable (Prod.snd : X × (ι → X) → (ι → X)))
  apply Measure.eq_infinitePi
  intro S A hA
  rw [Measure.map_apply hm (MeasurableSet.pi S.countable_toSet (fun k _ => hA k))]
  by_cases hi : i ∈ S
  · have he : (fun z : X × (ι → X) => Function.update z.2 i z.1) ⁻¹' Set.pi (S : Set ι) A =
        A i ×ˢ Set.pi (↑(S.erase i) : Set ι) A := by
      ext z
      simp only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,mem_erase]
      constructor
      · intro hz
        refine ⟨by simpa using hz i hi,?_⟩
        intro k hk
        simpa [Function.update_of_ne hk.1] using hz k hk.2
      · rintro ⟨hz,hrest⟩ k hk
        by_cases hki : k = i
        · subst k; simpa using hz
        · simpa [Function.update_of_ne hki] using hrest k ⟨hki,hk⟩
    rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun k _ => hA k)]
    rw [← Finset.mul_prod_erase S (fun k => Function.update μ i ν k (A k)) hi]
    simp only [Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (mem_erase.mp hk).1]
  · have he : (fun z : X × (ι → X) => Function.update z.2 i z.1) ⁻¹' Set.pi (S : Set ι) A =
        Set.univ ×ˢ Set.pi (S : Set ι) A := by
      ext z
      simp only [Set.mem_preimage,Set.mem_pi,Finset.mem_coe,Set.mem_prod,Set.mem_univ,true_and]
      apply forall_congr'
      intro k
      constructor <;> intro h hk
      · simpa [Function.update_of_ne (show k ≠ i from fun he => hi (he ▸ hk))] using h hk
      · simpa [Function.update_of_ne (show k ≠ i from fun he => hi (he ▸ hk))] using h hk
    rw [he,Measure.prod_prod,measure_univ,one_mul,Measure.infinitePi_pi _ (fun k _ => hA k)]
    exact Finset.prod_congr rfl fun k hk => by
      rw [Function.update_of_ne (show k ≠ i from fun he => hi (he ▸ hk))]

/-- Absolute continuity survives finitely many coordinate changes. No assertion
about arbitrary infinite families of absolutely continuous marginals is used. -/
theorem infinitePi_ac_of_finite_changes {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (μ ν : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] (F : Finset ι)
    (hac : ∀ i ∈ F, ν i ≪ μ i) (heq : ∀ i ∉ F, ν i = μ i) :
    Measure.infinitePi ν ≪ Measure.infinitePi μ := by
  induction F using Finset.induction_on generalizing ν with
  | empty =>
    have h : ν = μ := funext fun i => heq i (by simp)
    rw [h]
  | @insert i F hi ih =>
    let σ := Function.update ν i (μ i)
    let : ∀ k, IsProbabilityMeasure (σ k) := fun k => by
      by_cases hk : k = i
      · subst k; simpa [σ] using (inferInstance : IsProbabilityMeasure (μ i))
      · simpa [σ,Function.update_of_ne hk] using (inferInstance : IsProbabilityMeasure (ν k))
    have hσ : Measure.infinitePi σ ≪ Measure.infinitePi μ := by
      apply ih σ
      · intro k hk
        have hki : k ≠ i := fun h => hi (h ▸ hk)
        simpa [σ,Function.update_of_ne hki] using hac k (mem_insert_of_mem hk)
      · intro k hk
        by_cases hki : k = i
        · subst k; simp [σ]
        · simpa [σ,Function.update_of_ne hki] using heq k (by simp [hki,hk])
    have hupdate : Function.update σ i (ν i) = ν := by
      ext k
      by_cases hk : k = i <;> simp [σ,hk,Function.update_of_ne]
    have hsame : Function.update σ i (μ i) = σ := by simp [σ]
    have hprod := (hac i (mem_insert_self i F)).prod
      (Measure.AbsolutelyContinuous.rfl : Measure.infinitePi σ ≪ Measure.infinitePi σ)
    have hmap : ((ν i).prod (Measure.infinitePi σ)).map (fun z : X × (ι → X) => Function.update z.2 i z.1) ≪
        ((μ i).prod (Measure.infinitePi σ)).map (fun z : X × (ι → X) => Function.update z.2 i z.1) := by
      apply hprod.map
      apply Measurable.of_eval
      intro k
      by_cases hk : k = i
      · subst k; simpa using (measurable_fst : Measurable (Prod.fst : X × (ι → X) → X))
      · simpa [Function.update_of_ne hk,Function.comp_def] using (measurable_pi_apply k).comp
          (measurable_snd : Measurable (Prod.snd : X × (ι → X) → (ι → X)))
    rw [infinitePi_update_law,infinitePi_update_law,hupdate,hsame] at hmap
    exact hmap.trans hσ

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_FinitePosteriorAC
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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

/-- Every coordinate posterior has an absolutely continuous off-diagonal part.
The diagonal atom is retained explicitly in the reference measure. -/
theorem posteriorKernel_ac_diagonalHaar (p : CouplingParameters) (right : Bool) (t : ℝ) :
    p.posteriorKernel right t ≪ diagonalHaarReference t := by
  apply Measure.AbsolutelyContinuous.smul_right _ (by norm_num)
  apply Measure.AbsolutelyContinuous.mk
  intro S hS hzero
  have hz : Measure.dirac t S = 0 ∧ unitIntervalMeasure S = 0 := by
    simpa only [Measure.add_apply,add_eq_zero] using hzero
  have hc (i : Fin 5) : p.endpointComponentLaw (!right) i S = 0 :=
    withDensity_absolutelyContinuous _ _ hz.2
  change p.posteriorLaw right t S = 0
  simp [posteriorLaw,Measure.add_apply,Measure.finsetSum_apply,Measure.smul_apply,hz.1,hc]

/-- Full conditional law with only F resampled, given the entire original
endpoint vector. The coordinates outside F are exactly fixed. -/
theorem vectorPosterior_finite_map {ι : Type*} [DecidableEq ι]
    (p : ι → CouplingParameters) (F : Finset ι) (x : ι → ℝ) :
    (vectorPosterior p (fun _ => false) x).map
      (fun y i => if i ∈ F then y i else x i) =
      Measure.infinitePi (fun i => if i ∈ F then (p i).posteriorKernel false (x i)
        else Measure.dirac (x i)) := by
  change (Measure.infinitePi (fun i => (p i).posteriorKernel false (x i))).map _ = _
  rw [Measure.infinitePi_map_pi _ (f := fun i y => if i ∈ F then y else x i)
    (fun i => by split_ifs <;> fun_prop)]
  congr 1
  funext i
  by_cases hi : i ∈ F
  · simp [hi]
  · simp [hi,Measure.map_const]

/-- Absolute continuity of the actual full-vector conditional law after a
finite replacement. This uses finitely many coordinate changes only. -/
theorem vectorPosterior_finite_ac {ι : Type*} [DecidableEq ι]
    (p : ι → CouplingParameters) (F : Finset ι) (x : ι → ℝ) :
    (vectorPosterior p (fun _ => false) x).map
      (fun y i => if i ∈ F then y i else x i) ≪
      Measure.infinitePi (fun i => if i ∈ F then diagonalHaarReference (x i)
        else Measure.dirac (x i)) := by
  rw [vectorPosterior_finite_map]
  let μ := fun i => if i ∈ F then diagonalHaarReference (x i) else Measure.dirac (x i)
  let ν := fun i => if i ∈ F then (p i).posteriorKernel false (x i) else Measure.dirac (x i)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => by dsimp [μ]; split_ifs <;> infer_instance
  let : ∀ i, IsProbabilityMeasure (ν i) := fun i => by dsimp [ν]; split_ifs <;> infer_instance
  apply infinitePi_ac_of_finite_changes μ ν F
  · intro i hi
    simpa [μ,ν,hi] using (p i).posteriorKernel_ac_diagonalHaar false (x i)
  · intro i hi
    simp [μ,ν,hi]

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_FiniteDisintegration
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.sourceUnitCircle_probability
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

theorem mixedCoordinate_compProd (p : CouplingParameters) (r : Bool) :
    p.selectedLaw true false ⊗ₘ (if r then p.posteriorKernel false else Kernel.id) =
      p.labelledCoupling.map (fun ω => (endpoint false ω.2,endpoint r ω.2)) := by
  cases r
  · simp only [Bool.false_eq_true,ite_false]
    rw [Measure.compProd_id,selectedLaw_endpoint]
    unfold coupling
    rw [Measure.map_map (endpoint_measurable false) measurable_snd,
      Measure.map_map (by fun_prop) ((endpoint_measurable false).comp measurable_snd)]
    rfl
  · simp only [ite_true]
    rw [posterior_compProd]
    unfold coupling
    rw [Measure.map_map (orientPair_measurable false) measurable_snd]
    rfl

/-- Disintegration of every mixed endpoint pair under the actual augmented
product law, conditioned on the entire original x vector. -/
theorem mixedPosterior_disintegration {ι : Type*} (p : ι → CouplingParameters) (r : ι → Bool) :
    ((vectorCoupling p).map (vectorEndpoint (fun _ => false))) ⊗ₘ (mixedPosteriorKernel p r) =
      (vectorCoupling p).map (fun ω => (vectorEndpoint (fun _ => false) ω,vectorEndpoint r ω)) := by
  rw [vectorEndpoint_law]
  let κ := fun i => if r i then (p i).posteriorKernel false else Kernel.id
  let : ∀ i, IsMarkovKernel (κ i) := fun i => by dsimp [κ]; split_ifs <;> infer_instance
  have hh := independentKernel_compProd (fun i => (p i).selectedLaw true false) κ
  dsimp [κ] at hh
  simp_rw [mixedCoordinate_compProd] at hh
  let zip : (ι → ℝ) × (ι → ℝ) → (ι → ℝ × ℝ) := fun z i => (z.1 i,z.2 i)
  let unzip : (ι → ℝ × ℝ) → (ι → ℝ) × (ι → ℝ) := fun z => (fun i => (z i).1,fun i => (z i).2)
  have hz : Measurable zip := by fun_prop
  have hu : Measurable unzip := by fun_prop
  have hleft := congrArg (fun ν : Measure (ι → ℝ × ℝ) => ν.map unzip) hh
  rw [Measure.map_map hu hz] at hleft
  have hid : unzip ∘ zip = id := rfl
  rw [hid,Measure.map_id] at hleft
  unfold mixedPosteriorKernel
  rw [hleft]
  have hp : (vectorCoupling p).map (fun ω i => (endpoint false (ω i).2,endpoint (r i) (ω i).2)) =
      Measure.infinitePi (fun i => (p i).labelledCoupling.map
        (fun ω => (endpoint false ω.2,endpoint (r i) ω.2))) := by
    unfold vectorCoupling
    exact Measure.infinitePi_map_pi _ (f := fun i (ω : Fin 6 × (ℝ × ℝ)) =>
      (endpoint false ω.2,endpoint (r i) ω.2)) (fun i =>
        ((endpoint_measurable false).comp measurable_snd).prodMk
          ((endpoint_measurable (r i)).comp measurable_snd))
  have hv : Measurable (fun (ω : ι → Fin 6 × (ℝ × ℝ)) i =>
      (endpoint false (ω i).2,endpoint (r i) (ω i).2)) := by
    apply Measurable.of_eval
    intro i
    exact ((endpoint_measurable false).comp (measurable_snd.comp (measurable_pi_apply i))).prodMk
      ((endpoint_measurable (r i)).comp (measurable_snd.comp (measurable_pi_apply i)))
  rw [← hp,Measure.map_map hu hv]
  rfl

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_ReferenceDomination
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory CouplingParameters
open scoped ENNReal
noncomputable section

/-- The mixed prefix posterior is dominated for every full conditioning vector. -/
theorem sourceMixedPosterior_ac (j : ℕ) (F : Finset SourceCoordinate) (x : SourceCoordinate → ℝ) :
    mixedPosteriorKernel (fun i : SourceCoordinate => stagedCouplingParameters j i.1)
      (fun i => decide (i ∈ F)) x ≪ sourceFiniteReferenceKernel F x := by
  have hh := vectorPosterior_finite_ac
    (fun i : SourceCoordinate => stagedCouplingParameters j i.1) F x
  rw [vectorPosterior_finite_map] at hh
  convert hh using 1 <;>
    dsimp [mixedPosteriorKernel,sourceFiniteReferenceKernel,independentKernel] <;>
    congr 1 <;> funext i <;> by_cases hi : i ∈ F <;>
      simp [hi,sourceDiagonalHaarKernel] <;> rfl

/-- Actual prefix-pair domination after integrating the full x marginal.
The x marginal is replaced by Haar only through its proved density, so the
infinite diagonal tail is not assumed Haar-distributed. -/
theorem sourceBiasedPrefix_ac_reference (j n : ℕ) :
    sourceBiasedRealMeasure j (sourceBiasedPrefixMask n) ≪
      sourceSamplingHaar ⊗ₘ sourceFiniteReferenceKernel (blockPrefix sourceBlockSize n) := by
  let p := fun i : SourceCoordinate => stagedCouplingParameters j i.1
  have he : (fun i : SourceCoordinate => decide (i ∈ blockPrefix sourceBlockSize n)) =
      sourceBiasedPrefixMask n := by
    funext i
    simp [sourceBiasedPrefixMask,mem_blockPrefix]
  have hdis := mixedPosterior_disintegration p (sourceBiasedPrefixMask n)
  have hbase : (vectorCoupling p).map (vectorEndpoint (fun _ => false)) ≪ sourceSamplingHaar := by
    obtain ⟨g,_,_,_,hg,_⟩ := sourceBiasedEndpoint_density j (fun _ => false)
    change (sourceBiasedLaw j).map (sourceBiasedEndpoint (fun _ => false)) ≪ sourceSamplingHaar
    rw [hg]
    exact withDensity_absolutelyContinuous _ _
  have hcond : ∀ᵐ x ∂((vectorCoupling p).map (vectorEndpoint (fun _ => false))),
      mixedPosteriorKernel p (sourceBiasedPrefixMask n) x ≪
        sourceFiniteReferenceKernel (blockPrefix sourceBlockSize n) x := by
    apply Filter.Eventually.of_forall
    intro x
    rw [← he]
    exact sourceMixedPosterior_ac j _ x
  have hh := hbase.compProd hcond
  rw [hdis] at hh
  exact hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_FiniteMixtureAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal
noncomputable section

theorem measurable_coordinateUpdate {ι X : Type*} [DecidableEq ι] [MeasurableSpace X] (i : ι) :
    Measurable (fun z : X × (ι → X) => Function.update z.2 i z.1) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : k = i
  · subst k; simpa using (measurable_fst : Measurable (Prod.fst : X × (ι → X) → X))
  · simpa [Function.update_of_ne hk,Function.comp_def] using (measurable_pi_apply k).comp
      (measurable_snd : Measurable (Prod.snd : X × (ι → X) → (ι → X)))

theorem coordinateUpdateLaw_add_right {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (i : ι) (μ : Measure X) (ν η : Measure (ι → X))
    [SFinite μ] [SFinite ν] [SFinite η] :
    coordinateUpdateLaw i μ (ν+η) = coordinateUpdateLaw i μ ν + coordinateUpdateLaw i μ η := by
  rw [coordinateUpdateLaw,Measure.prod_add,Measure.map_add _ _ (measurable_coordinateUpdate i)]
  rfl

theorem coordinateUpdateLaw_average {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (i : ι) (μ ν : Measure X) (η : Measure (ι → X))
    [SFinite μ] [SFinite ν] [SFinite η] :
    coordinateUpdateLaw i (probabilityAverage μ ν) η =
      (2 : ℝ≥0∞)⁻¹ • (coordinateUpdateLaw i μ η + coordinateUpdateLaw i ν η) := by
  unfold coordinateUpdateLaw probabilityAverage
  rw [Measure.prod_smul_left,Measure.add_prod,
    Measure.map_smul,
    Measure.map_add _ _ (measurable_coordinateUpdate i)]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_FiniteProductMixture
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
variable {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]

variable (μ ν : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]

theorem finiteChoiceLaw_update_base (I : Finset ι) (i : ι) (hi : i ∉ I) :
    coordinateUpdateLaw i (μ i) (finiteChoiceLaw μ ν I) = finiteChoiceLaw μ ν I := by
  unfold coordinateUpdateLaw finiteChoiceLaw
  rw [infinitePi_update_law]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k; simp [hi]
  · simp [Function.update_of_ne hk]

theorem finiteChoiceLaw_update_replace (I : Finset ι) (i : ι) :
    coordinateUpdateLaw i (ν i) (finiteChoiceLaw μ ν I) = finiteChoiceLaw μ ν (insert i I) := by
  unfold coordinateUpdateLaw finiteChoiceLaw
  rw [infinitePi_update_law]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k; simp
  · simp [hk]

theorem finiteAverageLaw_insert (F : Finset ι) (i : ι) :
    finiteAverageLaw μ ν (insert i F) =
      coordinateUpdateLaw i (probabilityAverage (μ i) (ν i)) (finiteAverageLaw μ ν F) := by
  unfold coordinateUpdateLaw finiteAverageLaw
  rw [infinitePi_update_law]
  congr 1
  funext k
  by_cases hk : k = i
  · subst k; simp
  · simp [hk]

variable {μ ν}

theorem coordinateUpdateLaw_smul_right (i : ι) (μ : Measure X) (ν : Measure (ι → X))
    [SFinite μ] [SFinite ν] (c : ℝ≥0∞) :
    coordinateUpdateLaw i μ (c • ν) = c • coordinateUpdateLaw i μ ν := by
  unfold coordinateUpdateLaw
  rw [Measure.prod_smul_right,
    Measure.map_smul]

theorem coordinateUpdateLaw_finset_sum {A : Type*} (i : ι) (μ : Measure X)
    (ν : A → Measure (ι → X)) [SFinite μ] [∀ a, IsFiniteMeasure (ν a)] (S : Finset A) :
    coordinateUpdateLaw i μ (∑ a ∈ S, ν a) = ∑ a ∈ S, coordinateUpdateLaw i μ (ν a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [coordinateUpdateLaw]
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha,coordinateUpdateLaw_add_right,Finset.sum_insert ha,ih]

/-- The finite independent diagonal-or-replacement mixture is an exact finite
sum of the laws for each replacement pattern. -/
theorem finiteAverageLaw_eq_sum (μ ν : ι → Measure X)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] (F : Finset ι) :
    finiteAverageLaw μ ν F = ((2 : ℝ≥0∞)⁻¹)^F.card •
      ∑ I ∈ F.powerset, finiteChoiceLaw μ ν I := by
  induction F using Finset.induction_on with
  | empty => simp [finiteAverageLaw,finiteChoiceLaw]
  | @insert i F hi ih =>
    rw [finiteAverageLaw_insert,coordinateUpdateLaw_average,ih,
      coordinateUpdateLaw_smul_right,coordinateUpdateLaw_smul_right,
      coordinateUpdateLaw_finset_sum,coordinateUpdateLaw_finset_sum]
    have hb : (∑ I ∈ F.powerset, coordinateUpdateLaw i (μ i) (finiteChoiceLaw μ ν I)) =
        ∑ I ∈ F.powerset, finiteChoiceLaw μ ν I := by
      apply Finset.sum_congr rfl
      intro I hI
      apply finiteChoiceLaw_update_base
      exact fun h => hi ((Finset.mem_powerset.mp hI) h)
    simp_rw [finiteChoiceLaw_update_replace]
    rw [hb,← smul_add,smul_smul,Finset.sum_powerset_insert hi,
      Finset.card_insert_of_notMem hi,pow_succ]
    rw [mul_comm]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ReferenceMixture
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory CouplingParameters Finset
open scoped ENNReal
noncomputable section

theorem sourceResamplingKernel_apply (I : Finset SourceCoordinate) (x : SourceCoordinate → ℝ) :
    sourceResamplingKernel I x = finiteChoiceLaw (fun i => Measure.dirac (x i))
      (fun _ => unitIntervalMeasure) I := by
  dsimp [sourceResamplingKernel,independentKernel,finiteChoiceLaw]
  congr 1
  funext i
  by_cases hi : i ∈ I <;> simp [hi]; rfl

theorem sourceFiniteReferenceKernel_apply (F : Finset SourceCoordinate) (x : SourceCoordinate → ℝ) :
    sourceFiniteReferenceKernel F x = finiteAverageLaw (fun i => Measure.dirac (x i))
      (fun _ => unitIntervalMeasure) F := by
  dsimp [sourceFiniteReferenceKernel,independentKernel,finiteAverageLaw]
  congr 1
  funext i
  by_cases hi : i ∈ F
  · simp only [ite_eq_left hi]
    rfl
  · simp only [ite_eq_right hi]
    rfl

/-- The exact finite replacement-pattern expansion of the reference kernel. -/
theorem sourceFiniteReferenceKernel_mixture (F : Finset SourceCoordinate) (x : SourceCoordinate → ℝ) :
    sourceFiniteReferenceKernel F x = ((2 : ℝ≥0∞)⁻¹)^F.card •
      ∑ I ∈ F.powerset, sourceResamplingKernel I x := by
  rw [sourceFiniteReferenceKernel_apply,finiteAverageLaw_eq_sum]
  simp_rw [sourceResamplingKernel_apply]

/-- Integrating over the actual Haar base preserves the finite mixture formula. -/
theorem sourceFiniteReference_compProd_mixture (F : Finset SourceCoordinate) :
    sourceSamplingHaar ⊗ₘ sourceFiniteReferenceKernel F =
      ((2 : ℝ≥0∞)⁻¹)^F.card •
        ∑ I ∈ F.powerset, sourceSamplingHaar ⊗ₘ sourceResamplingKernel I := by
  apply Measure.ext
  intro S hS
  rw [Measure.compProd_apply hS,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul]
  simp_rw [sourceFiniteReferenceKernel_mixture,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun I _ =>
      Kernel.measurable_kernel_prodMk_left hS),
    lintegral_finsetSum F.powerset (fun I _ => Kernel.measurable_kernel_prodMk_left hS)]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  exact (Measure.compProd_apply hS).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ResamplingLaw
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory CouplingParameters
open scoped ENNReal
noncomputable section

theorem sourceResampling_coordinate_compProd (I : Finset SourceCoordinate) (i : SourceCoordinate) :
    unitIntervalMeasure ⊗ₘ (if i ∈ I then Kernel.const ℝ unitIntervalMeasure else Kernel.id) =
      (unitIntervalMeasure.prod unitIntervalMeasure).map
        (fun z : ℝ × ℝ => (z.1,if i ∈ I then z.2 else z.1)) := by
  by_cases hi : i ∈ I
  · simp [hi,Measure.compProd_const]
  · simp only [ite_eq_right hi,Measure.compProd_id]
    have hf : (unitIntervalMeasure.prod unitIntervalMeasure).map Prod.fst = unitIntervalMeasure :=
      measurePreserving_fst.map_eq
    conv_lhs => rw [← hf]
    rw [Measure.map_map (by fun_prop) measurable_fst]
    rfl

/-- Each replacement pattern is exactly the unrestricted source pair law. -/
theorem sourceResampling_compProd_eq_map (I : Finset SourceCoordinate) :
    sourceSamplingHaar ⊗ₘ sourceResamplingKernel I =
      sourceSamplingPairHaar.map (sourceSamplingLimitMap I) := by
  let κ := fun i : SourceCoordinate => if i ∈ I then Kernel.const ℝ unitIntervalMeasure else Kernel.id
  let : ∀ i, IsMarkovKernel (κ i) := fun i => by dsimp [κ]; split_ifs <;> infer_instance
  have hh := independentKernel_compProd (fun _ : SourceCoordinate => unitIntervalMeasure) κ
  dsimp [κ] at hh
  simp_rw [sourceResampling_coordinate_compProd] at hh
  let zip : SourceSamplingPair → (SourceCoordinate → ℝ × ℝ) := fun z i => (z.1 i,z.2 i)
  let unzip : (SourceCoordinate → ℝ × ℝ) → SourceSamplingPair := fun z => (fun i => (z i).1,fun i => (z i).2)
  have hz : Measurable zip := by fun_prop
  have hu : Measurable unzip := by fun_prop
  have hleft := congrArg (fun ν : Measure (SourceCoordinate → ℝ × ℝ) => ν.map unzip) hh
  rw [Measure.map_map hu hz] at hleft
  have hid : unzip ∘ zip = id := rfl
  rw [hid,Measure.map_id] at hleft
  unfold sourceResamplingKernel
  rw [hleft]
  have hm (i : SourceCoordinate) : Measurable (fun z : ℝ × ℝ => (z.1,if i ∈ I then z.2 else z.1)) := by
    by_cases hi : i ∈ I <;> simp only [hi,ite_true,ite_false] <;> fun_prop
  have hp : sourceSamplingPairHaar.map
      (fun z i => ((z i).1,if i ∈ I then (z i).2 else (z i).1)) =
      Measure.infinitePi (fun i : SourceCoordinate => (unitIntervalMeasure.prod unitIntervalMeasure).map
        (fun z : ℝ × ℝ => (z.1,if i ∈ I then z.2 else z.1))) :=
    Measure.infinitePi_map_pi _ hm
  have hmap : Measurable (fun z : SourceCoordinate → ℝ × ℝ =>
      fun i => ((z i).1,if i ∈ I then (z i).2 else (z i).1)) :=
    Measurable.of_eval fun i => (hm i).comp (measurable_pi_apply i)
  rw [← hp,Measure.map_map hu hmap]
  rfl

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ReferenceOrdered
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter ProbabilityTheory CouplingParameters
open scoped ENNReal
noncomputable section

/-- The independent Haar pair has no equality boundary at any coordinate. -/
theorem sourceSamplingPairHaar_coordinate_ne :
    ∀ᵐ z ∂sourceSamplingPairHaar, ∀ i, (z i).1 ≠ (z i).2 := by
  let : NullSingletonClass unitIntervalMeasure := by unfold unitIntervalMeasure; infer_instance
  apply ae_all_iff.mpr
  intro i
  have hp : ∀ᵐ z ∂unitIntervalMeasure.prod unitIntervalMeasure, z.1 ≠ z.2 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    apply Eventually.of_forall
    intro x
    have hh : ∀ᵐ y ∂unitIntervalMeasure, y ≠ x := by
      rw [ae_iff]
      simp
    exact hh.mono fun y hy => hy.symm
  exact (measurePreserving_eval_infinitePi
    (fun _ : SourceCoordinate => unitIntervalMeasure.prod unitIntervalMeasure) i).quasiMeasurePreserving.ae hp

/-- Strict and non-strict order coincide for the replacement coordinates. -/
theorem sourceSamplingLimit_order_event (I : Finset SourceCoordinate) :
    (sourceSamplingLimitMap I ⁻¹' sourceSamplingOrdered) =ᵐ[sourceSamplingPairHaar]
      sourceSamplingTriangleSet I := by
  filter_upwards [sourceSamplingPairHaar_coordinate_ne] with z hz
  apply propext
  change (∀ i, (z i).1 ≤ if i ∈ I then (z i).2 else (z i).1) ↔
    (∀ i ∈ I, (z i).1 < (z i).2)
  constructor
  · intro h i hi
    exact lt_of_le_of_ne (by simpa [hi] using h i) (hz i)
  · intro h i
    by_cases hi : i ∈ I
    · simpa [hi] using (h i hi).le
    · simp [hi]

theorem sourceResampling_ordered_restriction (I : Finset SourceCoordinate) :
    (sourceSamplingHaar ⊗ₘ sourceResamplingKernel I).restrict sourceSamplingOrdered =
      sourceSamplingLambda I := by
  rw [sourceResampling_compProd_eq_map,
    Measure.restrict_map (sourceSamplingLimitMap_measurable I) sourceSamplingOrdered_measurable,
    Measure.restrict_congr_set (sourceSamplingLimit_order_event I)]
  rfl

/-- Exact finite-prefix reference mixture after imposing global order. -/
theorem sourceFiniteReference_ordered_mixture (F : Finset SourceCoordinate) :
    (sourceSamplingHaar ⊗ₘ sourceFiniteReferenceKernel F).restrict sourceSamplingOrdered =
      ((2 : ℝ≥0∞)⁻¹)^F.card • ∑ I ∈ F.powerset, sourceSamplingLambda I := by
  have hs : (∑ I ∈ F.powerset, sourceSamplingHaar ⊗ₘ sourceResamplingKernel I).restrict sourceSamplingOrdered =
      ∑ I ∈ F.powerset, (sourceSamplingHaar ⊗ₘ sourceResamplingKernel I).restrict sourceSamplingOrdered :=
    map_sum (Measure.restrictₗ sourceSamplingOrdered) _ _
  rw [sourceFiniteReference_compProd_mixture,Measure.restrict_smul,hs]
  simp_rw [sourceResampling_ordered_restriction]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_PrefixDomination
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter ProbabilityTheory CouplingParameters Finset
open scoped ENNReal
noncomputable section

theorem sourceBiasedRealMeasure_ordered (j : ℕ) (r : SourceCoordinate → Bool) :
    ∀ᵐ z ∂sourceBiasedRealMeasure j r, z ∈ sourceSamplingOrdered := by
  apply (ae_map_iff (sourceBiasedPair_measurable r).aemeasurable sourceSamplingOrdered_measurable).mpr
  filter_upwards [sourceBiasedLaw_ordered j] with ω hω
  intro i
  cases hr : r i
  · simp [sourceBiasedPair,sourceBiasedEndpoint,blockProductEndpoint,endpoint,hr]
  · simpa [sourceBiasedPair,sourceBiasedEndpoint,blockProductEndpoint,endpoint,hr] using hω i

theorem sourceBiasedPrefix_domination_real (j n : ℕ) :
    sourceBiasedRealMeasure j (sourceBiasedPrefixMask n) ≪
      ∑ I ∈ (blockPrefix sourceBlockSize n).powerset, sourceSamplingLambda I := by
  have hh := (sourceBiasedPrefix_ac_reference j n).restrict sourceSamplingOrdered
  rw [Measure.restrict_eq_self_of_ae_mem (sourceBiasedRealMeasure_ordered j _),
    sourceFiniteReference_ordered_mixture] at hh
  exact hh.trans Measure.smul_absolutelyContinuous

/-- Finite-prefix domination by the actual lambda_I measures on the same torus
used for the uncapped invariant-projection identity and weak limits. -/
theorem sourceBiasedPrefix_domination_oai (j n : ℕ) :
    (sourceBiasedTorusMeasure j (sourceBiasedPrefixMask n) : Measure SourceSamplingTorus) ≪
      ∑ I ∈ (blockPrefix sourceBlockSize n).powerset,
        (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus) := by
  have hh := (sourceBiasedPrefix_domination_real j n).map sourceSamplingTorusMap_continuous.measurable
  change _ ≪ _ at hh
  have hm : (∑ I ∈ (blockPrefix sourceBlockSize n).powerset, sourceSamplingLambda I).map sourceSamplingTorusMap =
      ∑ I ∈ (blockPrefix sourceBlockSize n).powerset,
        (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus) := by
    let F := (blockPrefix sourceBlockSize n).powerset
    change (∑ I ∈ F, sourceSamplingLambda I).map sourceSamplingTorusMap =
      ∑ I ∈ F, (sourceSamplingLambdaTorus I : Measure SourceSamplingTorus)
    induction F using Finset.induction_on with
    | empty => simp
    | @insert I F hi ih =>
      rw [Finset.sum_insert hi,Measure.map_add _ _ sourceSamplingTorusMap_continuous.measurable,
        Finset.sum_insert hi,ih]
      rfl
  rw [hm] at hh
  exact hh

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceBiasedPrefix_domination_oai := @OAI.FiniteFactor.sourceBiasedPrefix_domination_oai
