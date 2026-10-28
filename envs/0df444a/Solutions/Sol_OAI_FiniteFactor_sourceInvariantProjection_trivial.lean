-- Prove2me | solution 1 for OAI.FiniteFactor.sourceInvariantProjection_trivial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:37:57.0444+00:00
-- url     : https://prove2.me/submissions/a64a033d-0d29-4f0c-b33b-4d9e53f806c0

import Mathlib
import Definitions.Def_OAIQ3Ff001
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_sourceProjectionEvent_mass_upper

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

theorem coordinateFloor_add {ι : Type*} (θ : ι → ℝ) (x : ι → ℝ) (k n : ℤ) (i : ι) :
    coordinateFloor θ (k+n) x i = coordinateFloor θ k x i +
      coordinateFloor θ n (coordinateRotate θ k x) i := by
  unfold coordinateFloor coordinateRotate
  have he : x i + ((k+n : ℤ) : ℝ)*θ i =
      (Int.fract (x i+(k : ℝ)*θ i)+(n : ℝ)*θ i) + (Int.floor (x i+(k : ℝ)*θ i) : ℝ) := by
    rw [Int.fract]
    push_cast
    ring
  rw [he, Int.floor_add_intCast]
  omega

theorem finiteFloorSupport_rotate {ι : Type*} (θ : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k : ℤ) : finiteFloorSupport θ (coordinateRotate θ k x) := by
  intro n
  apply ((hx (k+n)).union (hx k)).subset
  intro i hi
  by_contra hn
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
  have he := coordinateFloor_add θ x k n i
  rw [hn.1, hn.2, zero_add] at he
  exact hi he.symm

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

theorem sourceLog_add {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k n : ℤ) :
    sourceLog θ c (k+n) x = sourceLog θ c k x + sourceLog θ c n (coordinateRotate θ k x) := by
  unfold sourceLog
  simp_rw [coordinateFloor_add, Int.cast_add, mul_add]
  exact (sourceLog_summable θ c hx k).tsum_add
    (sourceLog_summable θ c (finiteFloorSupport_rotate θ hx k) n)

/-- The actual cocycle identity, proved on the conull domain supplied by
Borel--Cantelli. The rotation and sums are explicit. -/
theorem sourceCocycle_add {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : finiteFloorSupport θ x) (k n : ℤ) :
    sourceCocycle θ c (k+n) x = sourceCocycle θ c n (coordinateRotate θ k x) * sourceCocycle θ c k x := by
  rw [sourceCocycle, sourceLog_add θ c hx, neg_add, Real.exp_add]
  exact mul_comm _ _

theorem sourceCocycle_zero {ι : Type*} (θ c : ι → ℝ) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico 0 1) : sourceCocycle θ c 0 x = 1 := by
  have hzero (i : ι) : coordinateFloor θ 0 x i = 0 := by
    simpa [coordinateFloor] using Int.floor_eq_zero_iff.mpr (hx i)
  simp [sourceCocycle, sourceLog, hzero]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Operator
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceMultiplication_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (f : SourceHilbert ι) :
    sourceMultiplication θ c hθ hc f =ᵐ[sourceMeasure ι] fun z => sourceDiagonal θ c z * f z := by
  have hh := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((sourceDiagonal_memLp θ c hθ hc).toLp (sourceDiagonal θ c)) f (r := 2)
  filter_upwards [hh, (sourceDiagonal_memLp θ c hθ hc).coeFn_toLp] with z hz hw
  simpa [sourceMultiplication, hw] using hz

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Powers
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceShiftNIndex_preserving (ι : Type*) (n : ℕ) :
    MeasurePreserving (sourceShiftNIndex (ι := ι) n) (sourceMeasure ι) (sourceMeasure ι) := by
  induction n with
  | zero =>
    have he : sourceShiftNIndex (ι := ι) 0 = id := by funext z; simp [sourceShiftNIndex]
    rw [he]
    exact MeasurePreserving.id _
  | succ n ih =>
    convert ih.comp (sourceShiftIndex_preserving ι) using 1
    funext z
    simp [sourceShiftNIndex, sourceShiftIndex, sub_sub, add_comm]

theorem sourceOperator_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (f : SourceHilbert ι) :
    sourceOperator θ c hθ hc f =ᵐ[sourceMeasure ι] fun z =>
      sourceDiagonal θ c (sourceShiftIndex z) * f (sourceShiftIndex z) := by
  have he := Lp.coeFn_compMeasurePreserving (sourceMultiplication θ c hθ hc f)
    (sourceShiftIndex_preserving ι)
  have hm := (sourceShiftIndex_preserving ι).quasiMeasurePreserving.ae
    (sourceMultiplication_apply_ae θ c hθ hc f)
  exact he.trans hm

/-- The actual powers of the constructed weighted shift, on the conull
finite-floor-support domain. No power formula is assumed. -/
theorem sourceOperator_pow_apply_ae {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hs : Summable (fun i => |θ i|)) (n : ℕ) (f : SourceHilbert ι) :
    (sourceOperator θ c hθ hc ^ n) f =ᵐ[sourceMeasure ι] fun z =>
      (sourceCocycle θ c n (coordinateRotate θ (z.2-(n : ℤ)) z.1) : ℂ) *
        f (sourceShiftNIndex n z) := by
  induction n with
  | zero =>
    apply Eventually.of_forall
    intro z
    have hzero : sourceCocycle θ c 0 (coordinateRotate θ z.2 z.1) = 1 :=
      sourceCocycle_zero θ c (fun i => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)
    simp [sourceShiftNIndex, hzero]
  | succ n ih =>
    have hfs : ∀ᵐ z ∂sourceMeasure ι, finiteFloorSupport θ z.1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_finiteFloorSupport θ hs)
    have hih := (sourceShiftIndex_preserving ι).quasiMeasurePreserving.ae ih
    have he := sourceOperator_apply_ae θ c hθ hc ((sourceOperator θ c hθ hc ^ n) f)
    have hpow : (sourceOperator θ c hθ hc ^ (n+1)) f =
        sourceOperator θ c hθ hc ((sourceOperator θ c hθ hc ^ n) f) := by
      rw [pow_succ']
      rfl
    rw [hpow]
    filter_upwards [he, hih, hfs] with z hz hi hx
    rw [hz, hi]
    have hrot : coordinateRotate θ (n : ℤ) (coordinateRotate θ (z.2-((n+1 : ℕ) : ℤ)) z.1) =
        coordinateRotate θ (z.2-1) z.1 := by
      rw [coordinateRotate_add]
      congr 1
      push_cast
      omega
    have hcoe := sourceCocycle_add θ c (finiteFloorSupport_rotate θ hx (z.2-((n+1 : ℕ) : ℤ)))
      (n : ℤ) 1
    rw [hrot] at hcoe
    have hind : sourceShiftNIndex n (sourceShiftIndex z) = sourceShiftNIndex (n+1) z := by
      simp [sourceShiftNIndex, sourceShiftIndex, sub_sub, add_comm]
    have hidx : (sourceShiftIndex z).2-(n : ℤ) = z.2-((n+1 : ℕ) : ℤ) := by
      simp [sourceShiftIndex]
      omega
    simp only [sourceDiagonal, sourceShiftIndex] at *
    rw [show z.2-1-(n : ℤ) = z.2-((n+1 : ℕ) : ℤ) from hidx, hind]
    simp only [Nat.cast_add, Nat.cast_one] at hcoe ⊢
    rw [hcoe, Complex.ofReal_mul]
    exact (mul_assoc _ _ _).symm

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

theorem sourceTorusRepresentative_preserving :
    MeasurePreserving sourceTorusRepresentative sourceTorusHaar sourceSamplingHaar := by
  refine ⟨Measurable.of_eval (fun i => sourceCircleRepresentative_measurable.comp (measurable_pi_apply i)),?_⟩
  unfold sourceTorusRepresentative
  rw [Measure.infinitePi_map_pi _ (fun _ => sourceCircleRepresentative_measurable)]
  simp only [sourceCircleRepresentative_preserving.map_eq]

theorem sourceTorusQuotient_representative (z : SourceTorus) :
    sourceTorusQuotient (sourceTorusRepresentative z) = z := by
  funext i
  exact (AddCircle.equivIco 1 0).symm_apply_apply (z i)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Tail
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology
noncomputable section

theorem sourceCutoff_ge_shift (s n : ℕ) :
    2^n * (sourceStageState s).K ≤ (sourceStageState (s+n)).K := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := sourceStage_cutoff_growth (s+n)
    rw [pow_succ, Nat.add_succ]
    nlinarith

/-- The exact geometric tail estimate used in scales and tail trimming. -/
theorem sourceCutoff_tail_bound (s : ℕ) :
    (∑' n : ℕ, 1 / ((sourceStageState (s+n)).K : ℝ)) ≤
      2 / ((sourceStageState s).K : ℝ) := by
  let b (n : ℕ) : ℝ := (1 / ((sourceStageState s).K : ℝ)) * (1/2 : ℝ)^n
  have hb : Summable b := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_left _
  have hle (n : ℕ) : 1 / ((sourceStageState (s+n)).K : ℝ) ≤ b n := by
    have hh : (2 : ℝ)^n * (sourceStageState s).K ≤ (sourceStageState (s+n)).K :=
      by exact_mod_cast sourceCutoff_ge_shift s n
    have hp : (0 : ℝ) < 2^n * (sourceStageState s).K := mul_pos (by positivity) (sourceCutoff_pos s)
    have ht := one_div_le_one_div_of_le hp hh
    simpa [b, one_div_pow, mul_comm, mul_left_comm] using ht
  calc
    _ ≤ ∑' n, b n := (hb.of_nonneg_of_le (fun _ => by positivity) hle).tsum_le_tsum hle hb
    _ = 2 / ((sourceStageState s).K : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)]
      ring

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
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_CoordinateMass
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorKernel_markov _root_.OAI.FiniteFactor.CouplingParameters.posteriorLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.selectedLaw_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Endpoint tails of the original Haar representative have at most their
interval length; the endpoint singleton conventions cause no extra mass. -/
theorem unitIntervalMeasure_right_tail (a : ℝ) :
    unitIntervalMeasure (Set.Ici (1-a)) ≤ ENNReal.ofReal a := by
  rw [unitIntervalMeasure,Measure.restrict_apply measurableSet_Ici]
  have hs : Set.Ici (1-a) ∩ Set.Ico (0 : ℝ) 1 ⊆ Set.Icc (1-a) 1 :=
    fun _ h => ⟨h.1,h.2.2.le⟩
  exact (measure_mono hs).trans_eq (by simp [Real.volume_Icc])

theorem unitIntervalMeasure_left_tail (a : ℝ) :
    unitIntervalMeasure (Set.Iic a) ≤ ENNReal.ofReal a := by
  rw [unitIntervalMeasure,Measure.restrict_apply measurableSet_Iic]
  have hs : Set.Iic a ∩ Set.Ico (0 : ℝ) 1 ⊆ Set.Icc 0 a :=
    fun _ h => ⟨h.2.1,h.1⟩
  exact (measure_mono hs).trans_eq (by simp [Real.volume_Icc])

namespace CouplingParameters

theorem labelledCoupling_label (p : CouplingParameters) (l : Fin 6) :
    p.labelledCoupling {z | z.1 = l} = ENNReal.ofReal (p.labelMass l) := by
  have hm : MeasurableSet {z : Fin 6 × (ℝ × ℝ) | z.1 = l} :=
    (measurableSet_singleton l).preimage measurable_fst
  have hi (i : Fin 6) : ((p.pairComponentLaw i).map (fun xy => (i,xy))) {z | z.1 = l} =
      if i = l then 1 else 0 := by
    have hmeas : Measurable (fun xy : ℝ × ℝ => (i,xy)) := measurable_const.prodMk measurable_id
    rw [Measure.map_apply hmeas hm]
    by_cases h : i = l <;> simp [h]
  rw [labelledCoupling,Measure.finsetSum_apply]
  simp only [Measure.smul_apply,smul_eq_mul,hi]
  simp

/-- The actual one-coordinate endpoint law is dominated by ten times Haar. -/
theorem labelledEndpoint_set_le_ten (p : CouplingParameters) (b : Bool)
    (A : Set ℝ) (hA : MeasurableSet A) :
    p.labelledCoupling ((fun z => endpoint b z.2) ⁻¹' A) ≤ 10*unitIntervalMeasure A := by
  have hmeas : Measurable (fun z : Fin 6 × (ℝ × ℝ) => endpoint b z.2) :=
    (endpoint_measurable b).comp measurable_snd
  rw [← Measure.map_apply hmeas hA,labelled_endpoint_density]
  change (unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (p.endpointDensity b t))) A ≤ _
  rw [withDensity_apply _ hA]
  have hh := lintegral_mono (μ := unitIntervalMeasure.restrict A)
    (fun t => ENNReal.ofReal_le_ofReal ((p.endpointDensity_lt_ten b t).le))
  simpa only [ENNReal.ofReal_ofNat,lintegral_const,Measure.restrict_apply_univ] using hh

theorem labelledCoupling_right_tail (p : CouplingParameters) (a : ℝ) :
    p.labelledCoupling {z | 1-a ≤ z.2.1} ≤ ENNReal.ofReal (10*a) := by
  have hh := p.labelledEndpoint_set_le_ten false (Set.Ici (1-a)) measurableSet_Ici
  apply hh.trans
  exact (mul_le_mul le_rfl (unitIntervalMeasure_right_tail a) zero_le zero_le).trans_eq
    (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]; simp)

theorem labelledCoupling_left_tail (p : CouplingParameters) (a : ℝ) :
    p.labelledCoupling {z | z.2.2 ≤ a} ≤ ENNReal.ofReal (10*a) := by
  have hh := p.labelledEndpoint_set_le_ten true (Set.Iic a) measurableSet_Iic
  apply hh.trans
  exact (mul_le_mul le_rfl (unitIntervalMeasure_left_tail a) zero_le zero_le).trans_eq
    (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]; simp)

end CouplingParameters
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
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_GeneratedAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Pointwise
noncomputable section

theorem mem_sourceGeneratedVonNeumann {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set (H →L[ℂ] H)) {T : H →L[ℂ] H} (hT : T ∈ S) :
    T ∈ sourceGeneratedVonNeumann S := by
  have he : (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier =
      Set.centralizer (Set.centralizer (S ∪ star S)) :=
    StarSubalgebra.coe_centralizer_centralizer ℂ S
  change T ∈ (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier
  rw [he]
  exact Set.subset_centralizer_centralizer (Or.inl hT)

theorem sourcePi_mem (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    sourcePi θ g ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inr ⟨g,rfl⟩)

theorem sourceShift_mem (θ : SourceCoordinate → ℝ) :
    sourceShift SourceCoordinate ∈ sourceAlgebra θ :=
  mem_sourceGeneratedVonNeumann _ (Or.inl rfl)

theorem sourceMultiplication_eq_pi (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceMultiplication θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg =
      sourcePi θ (sourceWeightBase θ hθ) := rfl

/-- Actual membership of the already verified staged operator in its generated
von Neumann algebra, without an assumed operator-membership hypothesis. -/
theorem staged_sourceOperator_mem (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ∈ sourceAlgebra θ := by
  change sourceShift SourceCoordinate * sourceMultiplication θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ∈ _
  rw [sourceMultiplication_eq_pi θ hθ]
  exact mul_mem (sourceShift_mem θ) (sourcePi_mem θ (sourceWeightBase θ hθ))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_VacuumFunctional
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

theorem sourceVacuumFunctional_square
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional (star T*T) = inner ℂ (T sourceVacuum) (T sourceVacuum) :=
  ContinuousLinearMap.adjoint_inner_right T sourceVacuum (T sourceVacuum)

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

/-- The displayed trace integral is the actual previously proved normal state. -/
theorem sourceVacuumFunctional_matrixIntegral
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    sourceVacuumFunctional H = ∫ x, sourceMatrixEntry H 0 0 x ∂sourceBaseMeasure := by
  rw [← setIntegral_univ, sourceMatrixEntry_setIntegral H Set.univ MeasurableSet.univ]
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

theorem sourceOperatorField_one (θ : SourceCoordinate → ℝ) :
    ∀ᵐ x ∂sourceBaseMeasure, sourceOperatorField (1 : SourceHilbert SourceCoordinate →L[ℂ]
      SourceHilbert SourceCoordinate) x = 1 := by
  have h (n : ℤ) : ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (1 : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
        x (lp.single 2 n (1 : ℂ)) = lp.single 2 n 1 := by
    filter_upwards [sourceOperatorField_represents θ (one_mem (sourceAlgebra θ)) (sourceBasis n),
      sourceFiberVector_basis n] with x hi he
    change sourceFiberVector (sourceBasis n) x = _ at hi
    rw [he] at hi
    exact hi.symm
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

theorem sourceOperatorField_zero (x : SourceCoordinate → ℝ) :
    sourceOperatorField (0 : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) x = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using sourceOperatorField_norm 0 x) (norm_nonneg _)

theorem sourceOperatorField_sub (θ : SourceCoordinate → ℝ)
    {A B : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hA : A ∈ sourceAlgebra θ) (hB : B ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure,
      sourceOperatorField (A - B) x = sourceOperatorField A x - sourceOperatorField B x := by
  have hsub : ∀ᵐ x ∂sourceBaseMeasure, ∀ n k : ℤ,
      sourceMatrixEntry (A-B) k n x = sourceMatrixEntry A k n x - sourceMatrixEntry B k n x := by
    rw [ae_all_iff]
    intro n
    exact source_ae_all_fibers (Lp.coeFn_sub (A (sourceBasis n)) (B (sourceBasis n)))
  filter_upwards [sourceOperatorField_entries_ae θ hA, sourceOperatorField_entries_ae θ hB,
    sourceOperatorField_entries_ae θ (sub_mem hA hB), hsub] with x ha hb hab hs
  apply fiberOperator_ext
  intro k n
  change (sourceOperatorField (A-B) x (lp.single 2 n (1 : ℂ))) k =
    (sourceOperatorField A x (lp.single 2 n (1 : ℂ))) k -
      (sourceOperatorField B x (lp.single 2 n (1 : ℂ))) k
  rw [hab, ha, hb, hs]

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

/-- The original invariant-projection equation holds fiberwise for the actual
operator and projection fields. -/
theorem sourceOperatorField_invariant (θ : SourceCoordinate → ℝ)
    {p T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hT : T ∈ sourceAlgebra θ)
    (hinv : (1-p)*T*p = 0) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (1-sourceOperatorField p x)*sourceOperatorField T x*sourceOperatorField p x = 0 := by
  have hsub := sub_mem (one_mem (sourceAlgebra θ)) hp
  filter_upwards [sourceOperatorField_mul θ (mul_mem hsub hT) hp,
    sourceOperatorField_mul θ hsub hT, sourceOperatorField_sub θ (one_mem (sourceAlgebra θ)) hp,
    sourceOperatorField_one θ] with x hab ha hs h1
  rw [hinv, sourceOperatorField_zero, ha, hs, h1] at hab
  exact hab.symm

/-- The normal trace already proved is exactly the field-integral formula. -/
theorem sourceVacuumFunctional_fieldIntegral (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    sourceVacuumFunctional H = ∫ x,
      (sourceOperatorField H x (lp.single 2 0 (1 : ℂ))) 0 ∂sourceBaseMeasure := by
  rw [sourceVacuumFunctional_matrixIntegral]
  apply integral_congr_ae
  filter_upwards [sourceOperatorField_entries_ae θ hH] with x hx
  exact (hx 0 0).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Covariance
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceCommutantRotation_basis (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    sourceCommutantRotation θ n (sourceBasis m) = sourceBasis (m+n) := by
  apply Lp.ext
  have hb := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae
    (sourceBasis_coe m)
  filter_upwards [sourceTransport_apply_ae θ n n (sourceBasis m), hb,
    sourceBasis_coe (m+n)] with z ht hb he
  change (sourceTransport θ n n (sourceBasis m)) z = _
  rw [ht, hb, he]
  simp only [sourceTransportIndex]
  simp only [sub_eq_iff_eq_add]

/-- Matrix form of H(sigma^r x) = S^(-r) H(x) S^r, for the original
regular representation and every integer power of the base rotation. -/
theorem sourceMatrixEntry_covariance (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (r n : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry H k n (coordinateRotate θ r x) =
        sourceMatrixEntry H (k+r) (n+r) x := by
  have he : H (sourceBasis (n+r)) = sourceCommutantRotation θ r (H (sourceBasis n)) := by
    rw [← sourceCommutantRotation_basis θ r n]
    exact (congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
      T (sourceBasis n)) (sourceAlgebra_commutes_rotation θ hH r)).symm
  have ht := source_ae_all_fibers (sourceTransport_apply_ae θ r r (H (sourceBasis n)))
  filter_upwards [ht] with x hx k
  unfold sourceMatrixEntry
  rw [he]
  change _ = (sourceTransport θ r r (H (sourceBasis n))) (x,k+r)
  rw [hx]
  simp [sourceTransportIndex]

/-- All countably many covariance identities hold on one conull base set. -/
theorem sourceMatrixEntry_covariance_all (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ r n k : ℤ,
      sourceMatrixEntry H k n (coordinateRotate θ r x) =
        sourceMatrixEntry H (k+r) (n+r) x := by
  rw [ae_all_iff]
  intro r
  rw [ae_all_iff]
  exact sourceMatrixEntry_covariance θ hH r

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_WeightedShiftField
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

theorem sourceMatrixEntry_sourceOperator_pow (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (q : ℕ) (m : ℤ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ k : ℤ,
      sourceMatrixEntry (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ^ q) k m x =
        if k = m + (q : ℤ) then
          (sourceCocycle θ sourceLogWeight q (coordinateRotate θ m x) : ℂ) else 0 := by
  have hb := (sourceShiftNIndex_preserving SourceCoordinate q).quasiMeasurePreserving.ae
    (sourceBasis_coe m)
  filter_upwards [source_ae_all_fibers (sourceOperator_pow_apply_ae θ sourceLogWeight hθ.nonneg
    sourceLogWeight_nonneg hθ.summable q (sourceBasis m)), source_ae_all_fibers hb] with x hp hb k
  unfold sourceMatrixEntry
  rw [hp, hb]
  simp only [sourceShiftNIndex]
  by_cases hk : k = m + (q : ℤ)
  · simp [hk]
  · have he : k - (q : ℤ) ≠ m := by omega
    simp [he, hk]

/-- The field of each power of the original quasinilpotent operator acts by
its verified source cocycle, simultaneously on every l2 vector. -/
theorem sourceOperatorField_sourceOperator_pow (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (q : ℕ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ (v : SourceFiberHilbert) (k : ℤ),
      (sourceOperatorField
        (sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg ^ q) x v) k =
        (sourceCocycle θ sourceLogWeight q (coordinateRotate θ (k - (q : ℤ)) x) : ℂ) *
          v (k - (q : ℤ)) := by
  have hm := ae_all_iff.mpr (sourceMatrixEntry_sourceOperator_pow θ hθ q)
  filter_upwards [sourceOperatorField_entries_ae θ (pow_mem (staged_sourceOperator_mem θ hθ) q),
    hm] with x he hm v k
  rw [fiberOperator_action]
  simp_rw [he, hm]
  have ht (n : ℤ) :
      (if k = n + (q : ℤ) then
        (sourceCocycle θ sourceLogWeight q (coordinateRotate θ n x) : ℂ) else 0) * v n =
      if n = k - (q : ℤ) then
        (sourceCocycle θ sourceLogWeight q (coordinateRotate θ (k - (q : ℤ)) x) : ℂ) *
          v (k - (q : ℤ)) else 0 := by
    by_cases hn : n = k - (q : ℤ)
    · have hk : k = n + (q : ℤ) := by omega
      rw [ite_eq_left hk, ite_eq_left hn, hn]
    · have hk : k ≠ n + (q : ℤ) := by omega
      rw [ite_eq_right hk, ite_eq_right hn, zero_mul]
  simp_rw [ht]
  simp

/-- Covariance for the actual field's matrix, with all integer indices on one
conull set. This is the coordinate form of conjugation by the fiber shift. -/
theorem sourceOperatorField_covariance (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    ∀ᵐ x ∂sourceBaseMeasure, ∀ r n k : ℤ,
      (sourceOperatorField H (coordinateRotate θ r x) (lp.single 2 n (1 : ℂ))) k =
        (sourceOperatorField H x (lp.single 2 (n+r) (1 : ℂ))) (k+r) := by
  have he : ∀ᵐ x ∂sourceBaseMeasure, ∀ r : ℤ, ∀ k n : ℤ,
      (sourceOperatorField H (coordinateRotate θ r x) (lp.single 2 n (1 : ℂ))) k =
        sourceMatrixEntry H k n (coordinateRotate θ r x) := by
    rw [ae_all_iff]
    intro r
    exact (coordinateRotate_preserving θ r).quasiMeasurePreserving.ae
      (sourceOperatorField_entries_ae θ hH)
  filter_upwards [he, sourceOperatorField_entries_ae θ hH,
    sourceMatrixEntry_covariance_all θ hH] with x he hx hc r n k
  rw [he, hx, hc]

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

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_Shift
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal
noncomputable section

theorem fiberShift_single (n m : ℤ) (c : ℂ) :
    fiberShift n (lp.single 2 m c) = lp.single 2 (m+n) c := by
  classical
  apply Subtype.ext
  funext k
  change (lp.single 2 m c : SourceFiberHilbert) (k-n) =
    (lp.single 2 (m+n) c : SourceFiberHilbert) k
  by_cases h : m = k-n
  · simp [lp.single_apply, h]
  · have hh : m+n ≠ k := by omega
    simp [lp.single_apply, h, hh]

theorem fiber_covariance_operator
    (A B : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (n : ℤ)
    (h : ∀ k m : ℤ, (B (lp.single 2 m (1 : ℂ))) k =
      (A (lp.single 2 (m+n) (1 : ℂ))) (k+n)) :
    fiberShift (-n) * A = B * fiberShift (-n) := by
  apply fiberOperator_ext
  intro k m
  change (A (lp.single 2 m (1 : ℂ))) (k-(-n)) =
    (B (fiberShift (-n) (lp.single 2 m (1 : ℂ)))) k
  rw [fiberShift_single, h]
  simp

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OrbitNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Covariance and invariance give the rotated range inclusion after removing
the shift. This is an identity of bounded operators, not a range assumption. -/
theorem fiber_rotated_invariant
    (A B W : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (n : ℤ)
    (hc : fiberShift (-n) * A = B * fiberShift (-n))
    (hi : (1-A)*W*A = 0) :
    (1-B)*(fiberShift (-n)*W)*A = 0 := by
  have he : (1-B)*fiberShift (-n) = fiberShift (-n)*(1-A) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hc]
  calc
    _ = ((1-B)*fiberShift (-n))*W*A := by simp only [mul_assoc]
    _ = (fiberShift (-n)*(1-A))*W*A := by rw [he]
    _ = fiberShift (-n)*((1-A)*W*A) := by simp only [mul_assoc]
    _ = 0 := by rw [hi, mul_zero]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CentralScalarField
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem sourceCentralCoefficient_measurable
    (A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    Measurable (sourceCentralCoefficient A) := sourceOperatorField_entry_measurable A 0 0

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusCharacters
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set Algebra Submodule
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceCharacterAlgebra_span :
    sourceCharacterAlgebra.toSubalgebra.toSubmodule = span ℂ (range sourceCharacter) := by
  apply adjoin_eq_span_of_subset
  refine .trans (fun x => Submonoid.closure_induction (fun _ => id) ⟨0,sourceCharacter_zero⟩ ?_) subset_span
  rintro _ _ _ _ ⟨v,rfl⟩ ⟨w,rfl⟩
  exact ⟨v+w,sourceCharacter_add v w⟩

theorem sourceCharacter_single (i : SourceCoordinate) (x : SourceTorus) :
    sourceCharacter (Finsupp.single i 1) x = fourier 1 (x i) := by
  simp [sourceCharacter, Finsupp.sum_single_index]

theorem sourceCharacterAlgebra_separates : sourceCharacterAlgebra.SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_,⟨sourceCharacter (Finsupp.single i 1),subset_adjoin ⟨_,rfl⟩,rfl⟩,?_⟩
  dsimp only
  rw [sourceCharacter_single,sourceCharacter_single,fourier_one,fourier_one,Ne,Circle.coe_inj]
  exact fun he => hi (AddCircle.injective_toCircle one_ne_zero he)

/-- Uniform density on the full countable product, with no finite-dimensional truncation assumption. -/
theorem sourceCharacter_span_dense :
    (span ℂ (range sourceCharacter)).topologicalClosure = ⊤ := by
  rw [← sourceCharacterAlgebra_span]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      sourceCharacterAlgebra_separates)

theorem sourceCharacterL2_span_dense :
    (span ℂ (range sourceCharacterL2)).topologicalClosure = ⊤ := by
  simpa only [map_span,ContinuousLinearMap.coe_coe,← range_comp,Function.comp_def] using
    (ContinuousMap.toLp_denseRange ℂ sourceTorusHaar ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).topologicalClosure_map_submodule
      sourceCharacter_span_dense

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusRotation
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceCharacter_translate (v : SourceCoordinate →₀ ℤ) (x y : SourceTorus) :
    sourceCharacter v (x+y) = sourceCharacter v x * sourceCharacter v y := by
  simp only [sourceCharacter, ContinuousMap.coe_mk,Pi.add_apply,smul_add,Finsupp.sum,
    Finset.sum_add_distrib]
  simp [fourier,AddCircle.toCircle_add]

/-- Rational independence rules out every nonconstant character eigenvalue 1. -/
theorem sourceCharacter_nonresonant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (v : SourceCoordinate →₀ ℤ) (hv : v ≠ 0) :
    sourceCharacter v (sourceTorusQuotient θ) ≠ 1 := by
  intro h
  have hz : v.sum (fun i n => n • (θ i : UnitAddCircle)) = 0 := by
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    simpa [sourceCharacter,fourier,sourceTorusQuotient] using h
  have he : ((v.sum fun i n => (n : ℝ)*θ i : ℝ) : UnitAddCircle) =
      v.sum (fun i n => n • (θ i : UnitAddCircle)) := by
    unfold Finsupp.sum
    induction v.support using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi,AddCircle.coe_add,ih]
      congr 1
      simpa only [zsmul_eq_mul] using (AddCircle.coe_zsmul (1 : ℝ) (n := v i) (x := θ i))
  rw [← he,AddCircle.coe_eq_zero_iff] at hz
  obtain ⟨c,hc⟩ := hz
  exact hv (hr v c (by simpa using hc.symm)).1

theorem sourceCharacterL2_rotation (θ : SourceCoordinate → ℝ) (v : SourceCoordinate →₀ ℤ) :
    Lp.compMeasurePreserving (sourceTorusRotationStep θ) (sourceTorusRotationStep_preserving θ)
      (sourceCharacterL2 v) = sourceCharacter v (sourceTorusQuotient θ) • sourceCharacterL2 v := by
  apply Lp.ext
  have he := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ℝ≥0∞)) sourceTorusHaar (sourceCharacter v)
  filter_upwards [Lp.coeFn_compMeasurePreserving (sourceCharacterL2 v) (sourceTorusRotationStep_preserving θ),
    (sourceTorusRotationStep_preserving θ).quasiMeasurePreserving.ae he,he,
    Lp.coeFn_smul (sourceCharacter v (sourceTorusQuotient θ)) (sourceCharacterL2 v)]
    with x hc ht hx hs
  rw [hc,Function.comp_apply,ht,hs,Pi.smul_apply,smul_eq_mul,hx]
  exact (sourceCharacter_translate v x (sourceTorusQuotient θ)).trans (mul_comm _ _)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusErgodic
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set Submodule
open scoped ENNReal ComplexConjugate
noncomputable section

theorem sourceCharacterL2_zero_inner :
    inner ℂ (sourceCharacterL2 0) (sourceCharacterL2 0) = 1 := by
  rw [ContinuousMap.inner_toLp]
  simp [sourceCharacter_zero]

theorem sourceRotationL2_zero_character (θ : SourceCoordinate → ℝ) :
    sourceRotationL2 θ (sourceCharacterL2 0) = sourceCharacterL2 0 := by
  change Lp.compMeasurePreserving _ _ _ = _
  rw [sourceCharacterL2_rotation,sourceCharacter_zero]
  simp

/-- An invariant vector orthogonal to the constant character is zero. -/
theorem sourceRotationL2_fixed_orthogonal_zero (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (f : Lp ℂ 2 sourceTorusHaar)
    (hf : sourceRotationL2 θ f = f) (h0 : inner ℂ (sourceCharacterL2 0) f = 0) : f = 0 := by
  have hchar (v : SourceCoordinate →₀ ℤ) : inner ℂ f (sourceCharacterL2 v) = 0 := by
    by_cases hv : v = 0
    · subst v
      exact inner_eq_zero_symm.mpr h0
    · have he := (sourceRotationL2 θ).inner_map_map f (sourceCharacterL2 v)
      rw [hf] at he
      change inner ℂ f (Lp.compMeasurePreserving _ _ _) = _ at he
      rw [sourceCharacterL2_rotation,inner_smul_right] at he
      have hn := sourceCharacter_nonresonant θ hr v hv
      by_contra hz
      exact hn (mul_right_cancel₀ hz (he.trans (one_mul _).symm))
  have hs : span ℂ (range sourceCharacterL2) ≤ (innerSL ℂ f).ker := by
    apply span_le.mpr
    rintro _ ⟨v,rfl⟩
    exact hchar v
  have ht : (span ℂ (range sourceCharacterL2)).topologicalClosure ≤ (innerSL ℂ f).ker :=
    Submodule.topologicalClosure_minimal _ hs (innerSL ℂ f).isClosed_ker
  rw [sourceCharacterL2_span_dense] at ht
  have hh : inner ℂ f f = 0 := ht (show f ∈ (⊤ : Submodule ℂ (Lp ℂ 2 sourceTorusHaar)) from trivial)
  exact inner_self_eq_zero.mp hh

theorem sourceRotationL2_fixed_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) (f : Lp ℂ 2 sourceTorusHaar)
    (hf : sourceRotationL2 θ f = f) :
    ∃ c : ℂ, f = c • sourceCharacterL2 0 := by
  let c := inner ℂ (sourceCharacterL2 0) f
  refine ⟨c,sub_eq_zero.mp (sourceRotationL2_fixed_orthogonal_zero θ hr
    (f-c • sourceCharacterL2 0) ?_ ?_)⟩
  · rw [map_sub,map_smul,hf,sourceRotationL2_zero_character]
  · rw [inner_sub_right,inner_smul_right,sourceCharacterL2_zero_inner,mul_one]
    exact sub_self _

theorem sourceTorus_invariant_memLp_constant (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) {f : SourceTorus → ℂ}
    (hf : MemLp f 2 sourceTorusHaar)
    (hinv : f ∘ sourceTorusRotationStep θ =ᵐ[sourceTorusHaar] f) :
    ∃ c : ℂ, f =ᵐ[sourceTorusHaar] fun _ => c := by
  have hfix : sourceRotationL2 θ (hf.toLp f) = hf.toLp f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hf.toLp f) (sourceTorusRotationStep_preserving θ),
      (sourceTorusRotationStep_preserving θ).quasiMeasurePreserving.ae hf.coeFn_toLp,
      hf.coeFn_toLp,hinv] with x hc ht hx hi
    exact hc.trans (ht.trans (hi.trans hx.symm))
  obtain ⟨c,hc⟩ := sourceRotationL2_fixed_constant θ hr (hf.toLp f) hfix
  refine ⟨c,?_⟩
  have he := ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ℝ≥0∞)) sourceTorusHaar (sourceCharacter 0)
  filter_upwards [hf.coeFn_toLp,Lp.coeFn_smul c (sourceCharacterL2 0),he] with x hx hs he
  rw [hc,hs,Pi.smul_apply,smul_eq_mul,he,sourceCharacter_zero] at hx
  simpa using hx.symm

/-- Ergodicity of the constructed countable-torus rotation itself. -/
theorem sourceTorusRotationStep_ergodic (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) : Ergodic (sourceTorusRotationStep θ) sourceTorusHaar := by
  classical
  refine ⟨sourceTorusRotationStep_preserving θ,⟨fun s hs hi => ?_⟩⟩
  have hm : MemLp (s.indicator (fun _ : SourceTorus => (1 : ℂ))) 2 sourceTorusHaar :=
    (memLp_const (1 : ℂ)).indicator hs
  have hinv : (s.indicator (fun _ : SourceTorus => (1 : ℂ))) ∘ sourceTorusRotationStep θ =ᵐ[sourceTorusHaar]
      s.indicator (fun _ : SourceTorus => (1 : ℂ)) := by
    apply Eventually.of_forall
    intro x
    have hh : sourceTorusRotationStep θ x ∈ s ↔ x ∈ s := by
      change x ∈ (sourceTorusRotationStep θ) ⁻¹' s ↔ x ∈ s
      rw [hi]
    by_cases hx : x ∈ s
    · simp [Function.comp_apply,hx,hh.mpr hx]
    · have ht : sourceTorusRotationStep θ x ∉ s := fun h => hx (hh.mp h)
      simp [Function.comp_apply,hx,ht]
  obtain ⟨c,hc⟩ := sourceTorus_invariant_memLp_constant θ hr hm hinv
  rw [Filter.eventuallyConst_set']
  by_cases h1 : c = 1
  · right
    filter_upwards [hc] with x hx
    apply propext
    show x ∈ s ↔ x ∈ (Set.univ : Set SourceTorus)
    by_cases hxs : x ∈ s
    · simp [hxs]
    · simp [hxs,h1] at hx
  · left
    filter_upwards [hc] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs] at hx
      exact (h1 hx.symm).elim
    · apply propext
      show x ∈ s ↔ x ∈ (∅ : Set SourceTorus)
      simp [hxs]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_RotationErgodic
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceTorusRepresentative_rotationStep (θ : SourceCoordinate → ℝ) (z : SourceTorus) :
    sourceTorusRepresentative (sourceTorusRotationStep θ z) =
      coordinateRotate θ 1 (sourceTorusRepresentative z) := by
  funext i
  have hz : ((sourceTorusRepresentative z i : ℝ) : UnitAddCircle) = z i :=
    congrFun (sourceTorusQuotient_representative z) i
  change sourceCircleRepresentative (z i + (θ i : UnitAddCircle)) =
    Int.fract (sourceTorusRepresentative z i + (1 : ℤ) * θ i)
  rw [← hz,← AddCircle.coe_add,sourceCircleRepresentative_coe]
  norm_num

/-- Ergodicity for the exact real-coordinate model used by the original algebra. -/
theorem coordinateRotate_ergodic (θ : SourceCoordinate → ℝ)
    (hr : SourceRationalIndependent θ) :
    Ergodic (coordinateRotate θ 1) sourceSamplingHaar :=
  sourceTorusRepresentative_preserving.ergodic_of_ergodic_semiconj
    (sourceTorusRotationStep_ergodic θ hr) (coordinateRotate_preserving θ 1).measurable
    (sourceTorusRepresentative_rotationStep θ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_VacuumSeparating
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTorus_borel _root_.OAI.FiniteFactor.sourceSamplingTorus_compact _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- Faithfulness on squares of the actual normal vacuum functional. -/
theorem sourceVacuumFunctional_square_eq_zero_iff (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    sourceVacuumFunctional (star H * H) = 0 ↔ H = 0 := by
  constructor
  · intro hz
    rw [sourceVacuumFunctional_square] at hz
    exact sourceVacuum_separating θ hH (inner_self_eq_zero.mp hz)
  · rintro rfl
    simp [sourceVacuumFunctional]

end
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

theorem fiberProjection_diagonal_zero_iff (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) :
    P (lp.single 2 k (1 : ℂ)) k = 0 ↔ P (lp.single 2 k (1 : ℂ)) = 0 := by
  rw [fiberProjection_diagonal_inner P hp,inner_self_eq_zero]

theorem fiberProjection_diagonal_one_iff (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) :
    P (lp.single 2 k (1 : ℂ)) k = 1 ↔ P (lp.single 2 k (1 : ℂ)) = lp.single 2 k (1 : ℂ) := by
  have he := fiberProjection_diagonal_zero_iff (1-P) hp.one_sub k
  change (lp.single 2 k (1 : ℂ) : SourceFiberHilbert) k - P (lp.single 2 k (1 : ℂ)) k = 0 ↔
    lp.single 2 k (1 : ℂ) - P (lp.single 2 k (1 : ℂ)) = 0 at he
  simp only [lp.single_apply,Pi.single_eq_same] at he
  rw [sub_eq_zero,sub_eq_zero] at he
  simpa only [eq_comm] using he

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

/-- If a diagonal entry is zero, that coordinate annihilates the entire range. -/
theorem fiberProjection_range_coordinate_zero (P : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (k : ℤ) (hz : P (lp.single 2 k (1 : ℂ)) k = 0)
    (v : SourceFiberHilbert) : P v k = 0 := by
  have hzv := (fiberProjection_diagonal_zero_iff P hp k).mp hz
  have he : inner ℂ (lp.single 2 k (1 : ℂ)) (P v) =
      inner ℂ (P (lp.single 2 k (1 : ℂ))) v := by
    rw [← ContinuousLinearMap.adjoint_inner_right P (lp.single 2 k (1 : ℂ)) v,
      ← ContinuousLinearMap.star_eq_adjoint,hp.isSelfAdjoint.star_eq]
  simpa [lp.inner_single_left,hzv] using he

/-- Positivity of the diagonal weight transfers zero backwards and one forwards. -/
theorem fiberProjection_diagonal_implications
    (P Q D : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hp : IsStarProjection P) (hq : IsStarProjection Q)
    (hi : (1-Q)*D*P = 0) (a : ℂ) (ha : a ≠ 0)
    (hd : ∀ v : SourceFiberHilbert, D v 0 = a * v 0)
    (he : D (lp.single 2 0 (1 : ℂ)) = a • lp.single 2 0 (1 : ℂ)) :
    (Q (lp.single 2 0 (1 : ℂ)) 0 = 0 → P (lp.single 2 0 (1 : ℂ)) 0 = 0) ∧
    (P (lp.single 2 0 (1 : ℂ)) 0 = 1 → Q (lp.single 2 0 (1 : ℂ)) 0 = 1) := by
  let e : SourceFiberHilbert := lp.single 2 0 (1 : ℂ)
  have hfix : Q (D (P e)) = D (P e) := by
    have hh := congrArg (fun A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert => A e) hi
    change D (P e) - Q (D (P e)) = 0 at hh
    exact (sub_eq_zero.mp hh).symm
  constructor
  · intro hz
    have hcoord := congrArg (fun v : SourceFiberHilbert => v 0) hfix
    rw [fiberProjection_range_coordinate_zero Q hq 0 hz,hd] at hcoord
    exact (mul_eq_zero.mp hcoord.symm).resolve_left ha
  · intro h1
    have hpfix := (fiberProjection_diagonal_one_iff P hp 0).mp h1
    rw [hpfix,he,map_smul] at hfix
    have hqfix : Q e = e := (smul_right_injective _ ha) hfix
    exact (fiberProjection_diagonal_one_iff Q hq 0).mpr hqfix

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionDiagonal
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceFiniteReferenceKernel_markov _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace _root_.OAI.FiniteFactor.sourceResamplingKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Faithfulness turns a zero diagonal almost everywhere into the zero projection. -/
theorem sourceProjection_zero_of_diagonal_zero (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hz : sourceCentralCoefficient p =ᵐ[sourceBaseMeasure] fun _ => 0) : p = 0 := by
  apply (sourceVacuumFunctional_square_eq_zero_iff θ hp).mp
  rw [hproj.isSelfAdjoint.star_eq,hproj.isIdempotentElem,sourceVacuumFunctional_fieldIntegral θ hp]
  change (∫ x, sourceCentralCoefficient p x ∂sourceBaseMeasure) = 0
  rw [integral_congr_ae hz,integral_zero]

theorem sourceProjection_one_of_diagonal_one (θ : SourceCoordinate → ℝ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hz : sourceCentralCoefficient p =ᵐ[sourceBaseMeasure] fun _ => 1) : p = 1 := by
  have hsub := sub_mem (one_mem (sourceAlgebra θ)) hp
  have hh : sourceCentralCoefficient (1-p) =ᵐ[sourceBaseMeasure] fun _ => 0 := by
    filter_upwards [sourceOperatorField_sub θ (one_mem (sourceAlgebra θ)) hp,
      sourceOperatorField_one θ,hz] with x hs h1 hz
    unfold sourceCentralCoefficient at *
    rw [hs,h1]
    change (lp.single 2 0 (1 : ℂ) : SourceFiberHilbert) 0 - sourceOperatorField p x (lp.single 2 0 (1 : ℂ)) 0 = 0
    simp [hz,lp.single_apply]
  exact (sub_eq_zero.mp (sourceProjection_zero_of_diagonal_zero θ hsub hproj.one_sub hh)).symm

/-- The diagonal's zero event is backwards invariant and its one event forwards
invariant. Both implications follow from the original invariant operator. -/
theorem sourceProjection_diagonal_rotation_implications
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∀ᵐ x ∂sourceBaseMeasure,
      (sourceCentralCoefficient p (coordinateRotate θ 1 x) = 0 → sourceCentralCoefficient p x = 0) ∧
      (sourceCentralCoefficient p x = 1 → sourceCentralCoefficient p (coordinateRotate θ 1 x) = 1) := by
  let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
  have hw := sourceOperatorField_sourceOperator_pow θ hθ 1
  simp only [pow_one,Nat.cast_one] at hw
  filter_upwards [sourceOperatorField_projection θ hp hproj,
    (coordinateRotate_preserving θ 1).quasiMeasurePreserving.ae (sourceOperatorField_projection θ hp hproj),
    sourceOperatorField_invariant θ hp (staged_sourceOperator_mem θ hθ) hinv,
    sourceOperatorField_covariance θ hp,hw] with x hpx hqx hi hc hw
  let P := sourceOperatorField p x
  let Q := sourceOperatorField p (coordinateRotate θ 1 x)
  let D := fiberShift (-1) * sourceOperatorField T x
  have hcov : fiberShift (-1)*P = Q*fiberShift (-1) :=
    fiber_covariance_operator P Q 1 (fun k m => hc 1 m k)
  have hrot : (1-Q)*D*P = 0 := fiber_rotated_invariant P Q _ 1 hcov hi
  have hd (v : SourceFiberHilbert) (k : ℤ) : D v k =
      (sourceCocycle θ sourceLogWeight 1 (coordinateRotate θ k x) : ℂ) * v k := by
    change sourceOperatorField T x v (k-(-1)) = _
    rw [hw]
    simp
  let a : ℂ := sourceCocycle θ sourceLogWeight 1 (coordinateRotate θ 0 x)
  have ha : a ≠ 0 := by
    dsimp [a]
    exact_mod_cast (sourceCocycle_pos θ sourceLogWeight 1 (coordinateRotate θ 0 x)).ne'
  apply fiberProjection_diagonal_implications P Q D hpx hqx hrot a ha (fun v => hd v 0)
  apply Subtype.ext
  funext k
  rw [hd]
  change _ = a * (lp.single 2 0 (1 : ℂ) : SourceFiberHilbert) k
  by_cases hk : k = 0
  · subst k; rfl
  · simp [lp.single_apply,Pi.single_eq_of_ne hk]

theorem sourceProjection_strict_diagonal
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∀ᵐ x ∂sourceBaseMeasure,
      0 < (sourceCentralCoefficient p x).re ∧ (sourceCentralCoefficient p x).re < 1 ∧
      (sourceCentralCoefficient p x).im = 0 := by
  have he := coordinateRotate_ergodic θ hr
  have hm := sourceCentralCoefficient_measurable p
  have hi := sourceProjection_diagonal_rotation_implications θ hθ hp hproj hinv
  have hn0 : ∀ᵐ x ∂sourceBaseMeasure, sourceCentralCoefficient p x ≠ 0 := by
    have hh := he.ae_empty_or_univ_of_preimage_ae_le
      (s := {x | sourceCentralCoefficient p x = 0}) (measurableSet_eq_fun hm measurable_const).nullMeasurableSet
      (hi.mono fun x hx => hx.1)
    rcases hh with hh | hh
    · filter_upwards [hh] with x hx
      change (sourceCentralCoefficient p x = 0) = False at hx
      exact fun h => (Eq.mp hx h).elim
    · exfalso
      apply hp0 (sourceProjection_zero_of_diagonal_zero θ hp hproj ?_)
      filter_upwards [hh] with x hx
      exact Eq.mpr hx trivial
  have hn1 : ∀ᵐ x ∂sourceBaseMeasure, sourceCentralCoefficient p x ≠ 1 := by
    have hh := he.ae_empty_or_univ_of_ae_le_preimage
      (s := {x | sourceCentralCoefficient p x = 1}) (measurableSet_eq_fun hm measurable_const).nullMeasurableSet
      (hi.mono fun x hx => hx.2)
    rcases hh with hh | hh
    · filter_upwards [hh] with x hx
      change (sourceCentralCoefficient p x = 1) = False at hx
      exact fun h => (Eq.mp hx h).elim
    · exfalso
      apply hp1 (sourceProjection_one_of_diagonal_one θ hp hproj ?_)
      filter_upwards [hh] with x hx
      exact Eq.mpr hx trivial
  filter_upwards [sourceOperatorField_projection θ hp hproj,hn0,hn1] with x hx h0 h1
  have hb := fiberProjection_diagonal_bounds _ hx 0
  change 0 ≤ (sourceCentralCoefficient p x).re ∧ (sourceCentralCoefficient p x).re ≤ 1 ∧
    (sourceCentralCoefficient p x).im = 0 at hb
  refine ⟨lt_of_le_of_ne hb.1 ?_,lt_of_le_of_ne hb.2.1 ?_,hb.2.2⟩
  · intro hh
    apply h0
    apply Complex.ext
    · exact hh.symm
    · exact hb.2.2
  · intro hh
    apply h1
    apply Complex.ext
    · exact hh
    · exact hb.2.2

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TagLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

namespace CouplingParameters

theorem tagGood_measurable (p : CouplingParameters) : MeasurableSet p.tagGood := by
  have hlabel : MeasurableSet {z : Fin 6 × (ℝ × ℝ) | z.1 = 5} :=
    (measurableSet_singleton (5 : Fin 6)).preimage measurable_fst
  have hpair : MeasurableSet {z : Fin 6 × (ℝ × ℝ) | z.2.1 < 1/p.m ∧ 1-1/p.m ≤ z.2.2} :=
    (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
    (measurableSet_le measurable_const (measurable_snd.comp measurable_snd))
  convert hlabel.compl.union hpair using 1
  ext z
  simp only [tagGood,Set.mem_ofPred_eq,Set.mem_union,Set.mem_compl_iff,imp_iff_not_or]

theorem labelledCoupling_tag_support (p : CouplingParameters) :
    ∀ᵐ z ∂p.labelledCoupling, z.1 = 5 → z.2.1 < 1/p.m ∧ 1-1/p.m ≤ z.2.2 := by
  have hmap (i : Fin 6) : ((p.pairComponentLaw i).map (fun xy => (i,xy))) p.tagGood = 1 := by
    have hmeas : Measurable (fun xy : ℝ × ℝ => (i,xy)) := measurable_const.prodMk measurable_id
    rw [Measure.map_apply hmeas (tagGood_measurable p)]
    by_cases hi : i = 5
    · subst i
      have hsub : p.endpointInterval false 4 ×ˢ p.endpointInterval true 4 ⊆
          (fun xy : ℝ × ℝ => ((5 : Fin 6),xy)) ⁻¹' p.tagGood := by
        intro xy hxy _
        exact ⟨hxy.1.2,hxy.2.1⟩
      apply le_antisymm prob_le_one
      have hh := measure_mono (μ := p.pairComponentLaw 5) hsub
      have hmass : p.pairComponentLaw 5 (p.endpointInterval false 4 ×ˢ p.endpointInterval true 4) = 1 := by
        change ((p.endpointComponentLaw false 4).prod (p.endpointComponentLaw true 4)) _ = 1
        rw [Measure.prod_prod,p.endpointComponentLaw_of_contains false 4 (Set.Subset.refl _),
          p.endpointComponentLaw_of_contains true 4 (Set.Subset.refl _),mul_one]
      rwa [hmass] at hh
    · have he : (fun xy : ℝ × ℝ => (i,xy)) ⁻¹' p.tagGood = Set.univ := by
        ext xy
        simp [tagGood,hi]
      rw [he,measure_univ]
  have hm : p.labelledCoupling p.tagGood = 1 := by
    rw [labelledCoupling,Measure.finsetSum_apply]
    simp only [Measure.smul_apply,smul_eq_mul,hmap,mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.labelMass_nonneg i),p.labelMass_sum]
    simp
  rw [ae_iff]
  change p.labelledCoupling p.tagGoodᶜ = 0
  rw [measure_compl (tagGood_measurable p) (measure_ne_top _ _),measure_univ,hm,tsub_self]

end CouplingParameters

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_TaggedAdmissibility
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

theorem currentBoundary_measurable (p : CouplingParameters) : MeasurableSet p.currentBoundary :=
  (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
  (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))

theorem currentTag_measurable (p : CouplingParameters) : MeasurableSet p.currentTag :=
  ((measurableSet_singleton (5 : Fin 6)).preimage measurable_fst).inter p.currentBoundary_measurable

theorem currentNonTag_measurable (p : CouplingParameters) : MeasurableSet p.currentNonTag :=
  (((measurableSet_singleton (5 : Fin 6)).preimage measurable_fst).compl).inter p.currentBoundary_measurable

theorem currentTag_mass (p : CouplingParameters) :
    p.labelledCoupling p.currentTag = ENNReal.ofReal p.tagMass := by
  have hsmall : 1/p.m + 2/p.m < 1 := by
    rw [← add_div]
    apply (div_lt_one p.m_pos).mpr
    linarith [p.m_ge]
  have he : p.currentTag =ᵐ[p.labelledCoupling] {z | z.1 = 5} := by
    filter_upwards [p.labelledCoupling_tag_support] with z hz
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      obtain ⟨hx,hy⟩ := hz h
      exact ⟨h,by constructor <;> linarith⟩
  rw [measure_congr he,p.labelledCoupling_label]
  rfl

theorem currentTag_disjoint (p : CouplingParameters) : Disjoint p.currentTag p.currentNonTag := by
  apply Set.disjoint_left.mpr
  intro z ht ha
  exact ha.1 ht.1

/-- The source's one-coordinate nontagged admissible mass, including both
endpoint losses, under the actual labelled coupling. -/
theorem currentNonTag_mass_lower (p : CouplingParameters) :
    ENNReal.ofReal (1-41/p.m) ≤ p.labelledCoupling p.currentNonTag := by
  let L : Set (Fin 6 × (ℝ × ℝ)) := {z | z.1 = 5}
  let X : Set (Fin 6 × (ℝ × ℝ)) := {z | 1-2/p.m ≤ z.2.1}
  let Y : Set (Fin 6 × (ℝ × ℝ)) := {z | z.2.2 ≤ 2/p.m}
  have he : p.currentNonTagᶜ = (L ∪ X) ∪ Y := by
    ext z
    simp only [currentNonTag,currentBoundary,L,X,Y,Set.mem_compl_iff,Set.mem_inter_iff,
      Set.mem_union,Set.mem_ofPred_eq,not_and_or,not_not,not_lt]
    tauto
  have hL : p.labelledCoupling.real L ≤ 1/p.m := by
    rw [measureReal_def,p.labelledCoupling_label]
    change (ENNReal.ofReal p.tagMass).toReal ≤ 1/p.m
    rw [ENNReal.toReal_ofReal p.tagMass_nonneg]
    unfold tagMass
    split_ifs
    · exact le_rfl
    · exact div_nonneg zero_le_one p.m_pos.le
  have hX : p.labelledCoupling.real X ≤ 10*(2/p.m) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) (div_nonneg (by norm_num) p.m_pos.le)) (p.labelledCoupling_right_tail (2/p.m))
  have hY : p.labelledCoupling.real Y ≤ 10*(2/p.m) :=
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg (by norm_num) (div_nonneg (by norm_num) p.m_pos.le)) (p.labelledCoupling_left_tail (2/p.m))
  have hc := (measureReal_union_le (μ := p.labelledCoupling) (L ∪ X) Y).trans
    (add_le_add (measureReal_union_le (μ := p.labelledCoupling) L X) le_rfl)
  rw [← he,measureReal_compl p.currentNonTag_measurable] at hc
  simp only [probReal_univ] at hc
  have hh : 1-41/p.m ≤ p.labelledCoupling.real p.currentNonTag := by
    have hid : 41/p.m = 1/p.m + 10*(2/p.m) + 10*(2/p.m) := by ring
    rw [hid]
    linarith
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (ENNReal.ofReal_toReal (measure_ne_top _ _))

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_BoundaryEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

theorem sourceExclusionWidth_current (j : ℕ) (i : Fin (sourceBlockSize j)) :
    sourceExclusionWidth j ⟨j,i⟩ = 2/(sourceBlockSize j : ℝ) := by
  unfold sourceExclusionWidth
  field_simp [(sourceCutoff_pos j).ne']

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_FiniteSingleTag
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

variable {ι X : Type*} [Countable ι] [MeasurableSpace X]

theorem singleTagCylinder_measurable (F : Finset ι) (T A : ι → Set X)
    (hT : ∀ q ∈ F, MeasurableSet (T q)) (hA : ∀ q ∈ F, MeasurableSet (A q)) (i : ι) :
    MeasurableSet (singleTagCylinder F T A i) := by
  classical
  have he : singleTagCylinder F T A i = ⋂ q, ⋂ (_ : q ∈ F),
      (fun ω : ι → X => ω q) ⁻¹' (if q = i then T q else A q) := by
    ext ω
    simp [singleTagCylinder,Set.mem_pi]
  rw [he]
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.iInter
  intro hq
  by_cases h : q = i
  · simpa only [ite_eq_left h] using (hT q hq).preimage (measurable_pi_apply q)
  · simpa only [ite_eq_right h] using (hA q hq).preimage (measurable_pi_apply q)

/-- Independent finite coordinates with one distinguished tag. The other
coordinates are explicitly nontagged, so these cylinders are disjoint. -/
theorem finite_single_tag_lower (μ : ι → Measure X) [∀ q, IsProbabilityMeasure (μ q)]
    (F : Finset ι) (T A : ι → Set X)
    (hT : ∀ q ∈ F, MeasurableSet (T q)) (hA : ∀ q ∈ F, MeasurableSet (A q))
    (hdisj : ∀ q ∈ F, Disjoint (T q) (A q)) (t a : ℝ≥0∞)
    (hTm : ∀ q ∈ F, t ≤ μ q (T q)) (hAm : ∀ q ∈ F, a ≤ μ q (A q)) :
    (F.card : ℝ≥0∞)*t*a^(F.card-1) ≤
      (Measure.infinitePi μ) (⋃ i ∈ F, singleTagCylinder F T A i) := by
  classical
  have hd : Set.PairwiseDisjoint (F : Set ι) (singleTagCylinder F T A) := by
    intro i hi l hl hil
    apply Set.disjoint_left.mpr
    intro ω hωi hωl
    have ht : ω i ∈ T i := by simpa using (hωi i hi)
    have ha : ω i ∈ A i := by simpa only [ite_eq_right hil] using (hωl i hi)
    exact Set.disjoint_left.mp (hdisj i hi) ht ha
  have hsingle (i : ι) (hi : i ∈ F) : t*a^(F.card-1) ≤
      (Measure.infinitePi μ) (singleTagCylinder F T A i) := by
    have hmeas (q : ι) (hq : q ∈ F) : MeasurableSet (if q = i then T q else A q) := by
      split_ifs <;> first | exact hT q hq | exact hA q hq
    rw [singleTagCylinder,Measure.infinitePi_pi _ hmeas]
    have he : t*a^(F.card-1) = ∏ q ∈ F, if q = i then t else a := by
      rw [← Finset.mul_prod_erase F (fun q => if q = i then t else a) hi,ite_eq_left rfl]
      congr 1
      calc
        a^(F.card-1) = ∏ _q ∈ F.erase i, a := by simp [Finset.card_erase_of_mem hi]
        _ = _ := by
          apply Finset.prod_congr rfl
          intro q hq
          rw [ite_eq_right (Finset.mem_erase.mp hq).1]
    rw [he]
    apply Finset.prod_le_prod'
    intro q hq
    by_cases h : q = i
    · simpa only [ite_eq_left h] using hTm q hq
    · simpa only [ite_eq_right h] using hAm q hq
  rw [measure_biUnion_finset hd (fun i _ => singleTagCylinder_measurable F T A hT hA i)]
  have hh := Finset.sum_le_sum hsingle
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_assoc] using hh

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_TagExponentialLower
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor

/-- The explicit logarithm bound used in the source tag probability. -/
theorem log_one_sub_ge_neg_two {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1/2) :
    -2*t ≤ Real.log (1-t) := by
  have hp : 0 < 1-t := by linarith
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos hp)
  have hh : (1-t)⁻¹ ≤ 1+2*t := by
    rw [← one_div]
    apply (div_le_iff₀ hp).mpr
    nlinarith
  linarith

/-- The source's exactly-one-tag probability has a uniform positive lower
bound, despite the growing block size. -/
theorem tag_probability_exponential_lower (m : ℕ) (hm : 100 ≤ m) :
    Real.exp (-82) ≤ (1-41/(m : ℝ))^(m-1) := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ht0 : 0 ≤ 41/(m : ℝ) := by positivity
  have ht1 : 41/(m : ℝ) ≤ 1/2 := (div_le_iff₀ hm0).mpr (by linarith)
  have hbase : 0 < 1-41/(m : ℝ) := by linarith
  have hlog := log_one_sub_ge_neg_two ht0 ht1
  have hnum : ((m-1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (m-1) : (0 : ℝ) ≤ (m-1 : ℕ))
  have hden : (m : ℝ)*(41/(m : ℝ)) = 41 := by field_simp
  have hsmall := mul_le_mul_of_nonneg_right hnum ht0
  have hh : -82 ≤ ((m-1 : ℕ) : ℝ)*Real.log (1-41/(m : ℝ)) := by nlinarith
  have he : (1-41/(m : ℝ))^(m-1) =
      Real.exp (((m-1 : ℕ) : ℝ)*Real.log (1-41/(m : ℝ))) := by
    rw [Real.exp_nat_mul,Real.exp_log hbase]
  rw [he]
  exact Real.exp_le_exp.mpr hh

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CurrentTaggedEvent
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

/-- The actual current tagged block has mass at least exp(-82). This is a
finite independent exactly-one-tag calculation under sourceBiasedLaw j. -/
theorem sourceCurrentTaggedEvent_mass (j : ℕ) :
    ENNReal.ofReal (Real.exp (-82)) ≤ (sourceBiasedLaw j) (sourceCurrentTaggedEvent j) := by
  let F := sourceBlockCoordinates j
  let p := stagedCouplingParameters j j
  let μ := fun i : SourceCoordinate => (stagedCouplingParameters j i.1).labelledCoupling
  let T := fun _ : SourceCoordinate => p.currentTag
  let A := fun _ : SourceCoordinate => p.currentNonTag
  have hTm (i : SourceCoordinate) (hi : i ∈ F) : μ i (T i) = ENNReal.ofReal (1/(sourceBlockSize j : ℝ)) := by
    have his := mem_sourceBlockCoordinates hi
    change (stagedCouplingParameters j i.1).labelledCoupling p.currentTag = _
    rw [his,currentTag_mass]
    simp [stagedCouplingParameters,tagMass]
  have hAm (i : SourceCoordinate) (hi : i ∈ F) :
      ENNReal.ofReal (1-41/(sourceBlockSize j : ℝ)) ≤ μ i (A i) := by
    have his := mem_sourceBlockCoordinates hi
    change _ ≤ (stagedCouplingParameters j i.1).labelledCoupling p.currentNonTag
    rw [his]
    exact p.currentNonTag_mass_lower
  have hh := finite_single_tag_lower μ F T A
    (fun _ _ => p.currentTag_measurable) (fun _ _ => p.currentNonTag_measurable)
    (fun _ _ => p.currentTag_disjoint) (ENNReal.ofReal (1/(sourceBlockSize j : ℝ)))
    (ENNReal.ofReal (1-41/(sourceBlockSize j : ℝ))) (fun i hi => (hTm i hi).symm.le) hAm
  have hsub : (⋃ i ∈ F, singleTagCylinder F T A i) ⊆ sourceCurrentTaggedEvent j := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω
    obtain ⟨i,hi,hc⟩ := hω
    have his := mem_sourceBlockCoordinates hi
    rcases i with ⟨s,i⟩
    change s = j at his
    subst s
    have ht : ω ⟨j,i⟩ ∈ p.currentTag := by simpa [T] using hc ⟨j,i⟩ hi
    refine ⟨⟨i,ht.1⟩,?_⟩
    intro u
    have hu : (⟨j,u⟩ : SourceCoordinate) ∈ F := by
      exact Finset.mem_map.mpr ⟨u,Finset.mem_univ _,rfl⟩
    have hcu := hc ⟨j,u⟩ hu
    by_cases h : (⟨j,u⟩ : SourceCoordinate) = ⟨j,i⟩
    · have ht : ω ⟨j,u⟩ ∈ p.currentTag := by simpa only [ite_eq_left h] using hcu
      exact ht.2
    · have ha : ω ⟨j,u⟩ ∈ p.currentNonTag := by simpa only [ite_eq_right h] using hcu
      exact ha.2
  have hmt : (sourceBlockSize j : ℝ≥0∞)*ENNReal.ofReal (1/(sourceBlockSize j : ℝ)) = 1 := by
    calc
      _ = ENNReal.ofReal ((sourceBlockSize j : ℝ)*(1/(sourceBlockSize j : ℝ))) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        simp
      _ = 1 := by rw [mul_one_div_cancel (sourceBlockSize_pos j).ne']; simp
  have hbase : 0 ≤ 1-41/(sourceBlockSize j : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_one (sourceBlockSize_pos j)).mpr
    have hm : (100 : ℝ) ≤ sourceBlockSize j := by exact_mod_cast (sourceStage j).m_ge_100
    linarith
  change (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(sourceBlockSize j : ℝ))*
    (ENNReal.ofReal (1-41/(sourceBlockSize j : ℝ)))^(F.card-1) ≤ _ at hh
  rw [show F.card = sourceBlockSize j from sourceBlockCoordinates_card j,hmt,one_mul,
    ← ENNReal.ofReal_pow hbase] at hh
  have hn := ENNReal.ofReal_le_ofReal (tag_probability_exponential_lower (sourceBlockSize j)
    (sourceStage j).m_ge_100)
  exact hn.trans (hh.trans (measure_mono hsub))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_DiagonalLoss
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Positive measurable functions have vanishing mass below the actual
source threshold 1/(j+1), without any quantitative lower bound. -/
theorem positive_small_sets_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (r : X → ℝ) (hr : Measurable r)
    (hpos : ∀ᵐ x ∂μ, 0 < r x) :
    Tendsto (fun j : ℕ => μ.real {x | r x < 1/((j : ℝ)+1)}) atTop (𝓝 0) := by
  let f := fun j : ℕ => {x | r x < 1/((j : ℝ)+1)}.indicator (fun _ => (1 : ℝ))
  have hA (j : ℕ) : MeasurableSet {x | r x < 1/((j : ℝ)+1)} := measurableSet_lt hr measurable_const
  have hm (j : ℕ) : AEStronglyMeasurable (f j) μ := (measurable_const.indicator (hA j)).aestronglyMeasurable
  have hb (j : ℕ) : ∀ᵐ x ∂μ, ‖f j x‖ ≤ (1 : ℝ) := by
    exact Eventually.of_forall fun x => by
      by_cases h : x ∈ {x | r x < 1/((j : ℝ)+1)}
      · simp only [f,Set.indicator_of_mem h,norm_one,le_refl]
      · simp only [f,Set.indicator_of_notMem h,norm_zero,zero_le_one]
  have hl : ∀ᵐ x ∂μ, Tendsto (fun j => f j x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hpos] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hx)] with j hj
    have hnot : x ∉ {x | r x < 1/((j : ℝ)+1)} := not_lt.mpr hj.le
    simp only [f,Set.indicator_of_notMem hnot]
  have ht := tendsto_integral_of_dominated_convergence (fun _ : X => (1 : ℝ)) hm (integrable_const 1) hb hl
  have hi (j) : (∫ x, f j x ∂μ) = μ.real {x | r x < 1/((j : ℝ)+1)} := by
    rw [integral_indicator (hA j)]
    simp [measureReal_def]
  simpa only [hi,integral_zero] using ht

/-- The actual uniformly L2-bounded biased marginals inherit that vanishing
loss even though their full infinite-dimensional densities vary with j. -/
theorem sourceBiased_positive_endpoint_loss (r : (SourceCoordinate → ℝ) → ℝ)
    (hr : Measurable r) (hpos : ∀ᵐ x ∂sourceBaseMeasure, 0 < r x) (b : Bool) :
    Tendsto (fun j : ℕ => (sourceBiasedLaw j).real
      {ω | r (sourceBiasedEndpoint (fun _ => b) ω) < 1/((j : ℝ)+1)}) atTop (𝓝 0) := by
  let C := Real.exp (20*(2*(∑' s,sourceKappa s^2)+1))
  have hbound (j : ℕ) : (sourceBiasedLaw j).real
      {ω | r (sourceBiasedEndpoint (fun _ => b) ω) < 1/((j : ℝ)+1)} ≤
        Real.sqrt C * Real.sqrt (sourceBaseMeasure.real {x | r x < 1/((j : ℝ)+1)}) := by
    obtain ⟨g,hg,hg0,hglp,he,hgC⟩ := sourceBiasedEndpoint_density j (fun _ => b)
    have hA : MeasurableSet {x | r x < 1/((j : ℝ)+1)} := measurableSet_lt hr measurable_const
    have hh := withDensity_L2_set_le sourceSamplingHaar g hglp hg0 _ hA C hgC
    rw [← he,Measure.map_apply (sourceBiasedEndpoint_measurable _) hA] at hh
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hh
  have ht := ((positive_small_sets_tendsto sourceBaseMeasure r hr hpos).sqrt).const_mul (Real.sqrt C)
  apply squeeze_zero (fun j => ENNReal.toReal_nonneg) hbound
  simpa only [Real.sqrt_zero,mul_zero] using ht

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FutureBoundary
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

theorem sourceBiasedCoordinate_measure (j : ℕ) (i : SourceCoordinate)
    (S : Set (Fin 6 × (ℝ × ℝ))) (hS : MeasurableSet S) :
    (sourceBiasedLaw j) ((fun ω : SourceBiasedSample => ω i) ⁻¹' S) =
      (stagedCouplingParameters j i.1).labelledCoupling S := by
  have hm : Measurable (fun ω : SourceBiasedSample => ω i) := measurable_pi_apply i
  rw [← Measure.map_apply hm hS]
  have he : (sourceBiasedLaw j).map (fun ω => ω i) = (stagedCouplingParameters j i.1).labelledCoupling :=
    Measure.infinitePi_map_eval _ _
  rw [he]

/-- The actual one-coordinate contribution to the future union loss. -/
theorem sourceFutureBad_bound (j n : ℕ) (i : Fin (sourceBlockSize (j+1+n))) :
    (sourceBiasedLaw j) (sourceFutureBad j n i) ≤
      ENNReal.ofReal (20*sourceExclusionWidth j ⟨j+1+n,i⟩) := by
  let a := sourceExclusionWidth j ⟨j+1+n,i⟩
  let p := stagedCouplingParameters j (j+1+n)
  have ha : 0 ≤ a := by dsimp [a,sourceExclusionWidth]; positivity
  have hS : MeasurableSet ({z : Fin 6 × (ℝ × ℝ) | 1-a ≤ z.2.1} ∪ {z | z.2.2 ≤ a}) :=
    (measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).union
    (measurableSet_le (measurable_snd.comp measurable_snd) measurable_const)
  change (sourceBiasedLaw j) ((fun ω : SourceBiasedSample => ω ⟨j+1+n,i⟩) ⁻¹'
    ({z | 1-a ≤ z.2.1} ∪ {z | z.2.2 ≤ a})) ≤ ENNReal.ofReal (20*a)
  rw [sourceBiasedCoordinate_measure _ _ _ hS]
  apply (measure_union_le _ _).trans
  apply (add_le_add (p.labelledCoupling_right_tail a) (p.labelledCoupling_left_tail a)).trans_eq
  rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) ha) (mul_nonneg (by norm_num) ha)]
  congr 1
  ring

theorem sourceFutureBoundary_no_bad (j : ℕ) (ω : SourceBiasedSample)
    (h : ω ∈ sourceFutureBoundaryEvent j) (n : ℕ) (i : Fin (sourceBlockSize (j+1+n))) :
    (ω ⟨j+1+n,i⟩).2.1 < 1-sourceExclusionWidth j ⟨j+1+n,i⟩ ∧
      sourceExclusionWidth j ⟨j+1+n,i⟩ < (ω ⟨j+1+n,i⟩).2.2 := by
  have hn : ω ∉ sourceFutureBad j n i := by
    intro hb
    exact h (Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨i,hb⟩⟩)
  exact ⟨lt_of_not_ge (fun hx => hn (Or.inl hx)),lt_of_not_ge (fun hy => hn (Or.inr hy))⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FutureBudget
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

/-- The exact recursive cutoff is at least m_j squared, giving vanishing
future boundary loss rather than merely geometric cutoff growth. -/
theorem sourceNextCutoff_ge_square (m : ℕ) (hm : 100 ≤ m) :
    (m : ℝ)^2 ≤ (sourceNextCutoff m : ℝ) := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (m : ℝ)^2 ≤ (m : ℝ)^((3/4 : ℝ)*(m : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  exact hp.trans (Nat.le_ceil _)

theorem sourceCutoff_ratio_tendsto :
    Tendsto (fun j : ℕ => ((sourceStageState j).K : ℝ)/(sourceStageState (j+1)).K) atTop (𝓝 0) := by
  have hbound (j : ℕ) : ((sourceStageState j).K : ℝ)/(sourceStageState (j+1)).K ≤
      1/(sourceBlockSize j : ℝ) := by
    have hm := sourceBlockSize_pos j
    have hK := sourceCutoff_pos (j+1)
    have hnext : (sourceBlockSize j : ℝ)^2 ≤ (sourceStageState (j+1)).K :=
      sourceNextCutoff_ge_square (sourceBlockSize j) (sourceStage j).m_ge_100
    have hprev : ((sourceStageState j).K : ℝ) ≤ sourceBlockSize j := by exact_mod_cast (sourceStage j).m_ge_K
    apply (div_le_div_iff₀ hK hm).mpr
    nlinarith
  have ht : Tendsto (fun j : ℕ => (sourceBlockSize j : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  apply squeeze_zero (fun j => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hbound
  simpa only [one_div] using ht

theorem sourceFutureBudget_tendsto :
    Tendsto (fun j : ℕ => 80*((sourceStageState j).K : ℝ)/(sourceStageState (j+1)).K) atTop (𝓝 0) := by
  simpa only [mul_div_assoc,mul_zero] using sourceCutoff_ratio_tendsto.const_mul 80

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FutureBoundaryLoss
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceFutureBoundary_loss_bound (j : ℕ) :
    (sourceBiasedLaw j) (sourceFutureBoundaryEvent j)ᶜ ≤
      ENNReal.ofReal (80*((sourceStageState j).K : ℝ)/(sourceStageState (j+1)).K) := by
  have hb (n : ℕ) : (sourceBiasedLaw j) (⋃ i : Fin (sourceBlockSize (j+1+n)), sourceFutureBad j n i) ≤
      ENNReal.ofReal (40*((sourceStageState j).K : ℝ)/(sourceStageState (j+1+n)).K) := by
    apply (measure_iUnion_le _).trans
    rw [tsum_fintype]
    apply (Finset.sum_le_sum (fun i _ => sourceFutureBad_bound j n i)).trans_eq
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by dsimp [sourceExclusionWidth]; positivity)]
    congr 1
    simp only [sourceExclusionWidth,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [(sourceBlockSize_pos (j+1+n)).ne',(sourceCutoff_pos (j+1+n)).ne']
    ring
  have hs : Summable (fun n : ℕ => 1/((sourceStageState (j+1+n)).K : ℝ)) :=
    sourceCutoff_reciprocal_summable.comp_injective (fun a b h => by omega)
  have he (n : ℕ) : 40*((sourceStageState j).K : ℝ)/(sourceStageState (j+1+n)).K =
      (40*((sourceStageState j).K : ℝ))*(1/((sourceStageState (j+1+n)).K : ℝ)) := by ring
  have hss : Summable (fun n : ℕ => 40*((sourceStageState j).K : ℝ)/(sourceStageState (j+1+n)).K) := by
    simp_rw [he]
    exact hs.mul_left _
  rw [sourceFutureBoundaryEvent,compl_compl]
  apply (measure_iUnion_le _).trans
  apply (ENNReal.tsum_le_tsum hb).trans
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hss]
  apply ENNReal.ofReal_le_ofReal
  simp_rw [he]
  rw [tsum_mul_left]
  calc
    _ ≤ (40*((sourceStageState j).K : ℝ))*(2/((sourceStageState (j+1)).K : ℝ)) :=
      mul_le_mul_of_nonneg_left (sourceCutoff_tail_bound (j+1)) (by positivity)
    _ = _ := by ring

theorem sourceFutureBoundary_loss_tendsto :
    Tendsto (fun j : ℕ => (sourceBiasedLaw j).real (sourceFutureBoundaryEvent j)ᶜ) atTop (𝓝 0) := by
  apply squeeze_zero (fun j => ENNReal.toReal_nonneg)
    (fun j => ENNReal.toReal_le_of_le_ofReal (by positivity) (sourceFutureBoundary_loss_bound j))
  exact sourceFutureBudget_tendsto

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_EventLossAssembly
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Current and future exclusions together give exactly the source boundary. -/
theorem sourceCurrentFuture_boundary (j : ℕ) (ω : SourceBiasedSample)
    (hc : ω ∈ sourceCurrentTaggedEvent j) (hf : ω ∈ sourceFutureBoundaryEvent j) :
    ω ∈ sourceBoundaryEvent j := by
  intro i hi
  rcases i with ⟨s,i⟩
  change j ≤ s at hi
  by_cases h : s = j
  · subst s
    rw [sourceExclusionWidth_current]
    exact hc.2 i
  · have hjs : j+1 ≤ s := by omega
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hjs
    exact sourceFutureBoundary_no_bad j ω hf n i

/-- No independence is used between the current block and the three losses. -/
theorem sourceProjectionEvent_mass_losses
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) :
    Real.exp (-82) ≤ (sourceBiasedLaw j).real (sourceProjectionEvent p j) +
      (sourceBiasedLaw j).real (sourceFutureBoundaryEvent j)ᶜ +
      (sourceBiasedLaw j).real (sourceDiagonalLossSet p j false) +
      (sourceBiasedLaw j).real (sourceDiagonalLossSet p j true) := by
  have hsub : sourceCurrentTaggedEvent j ⊆
      ((sourceProjectionEvent p j ∪ (sourceFutureBoundaryEvent j)ᶜ) ∪ sourceDiagonalLossSet p j false) ∪
        sourceDiagonalLossSet p j true := by
    intro ω hc
    by_cases hf : ω ∈ sourceFutureBoundaryEvent j
    · by_cases hx : ω ∈ sourceDiagonalLossSet p j false
      · exact Or.inl (Or.inr hx)
      · by_cases hy : ω ∈ sourceDiagonalLossSet p j true
        · exact Or.inr hy
        · refine Or.inl (Or.inl (Or.inl ⟨⟨hc.1,sourceCurrentFuture_boundary j ω hc hf⟩,?_⟩))
          constructor
          · exact le_of_not_gt hx
          · exact le_of_not_gt hy
    · exact Or.inl (Or.inl (Or.inr hf))
  have hlow : Real.exp (-82) ≤ (sourceBiasedLaw j).real (sourceCurrentTaggedEvent j) := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (sourceCurrentTaggedEvent_mass j)
    simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le,measureReal_def] using hh
  apply hlow.trans ((measureReal_mono hsub).trans ?_)
  apply (measureReal_union_le _ _).trans
  apply add_le_add _ le_rfl
  apply (measureReal_union_le _ _).trans
  exact add_le_add (measureReal_union_le _ _) le_rfl

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_EventPositive
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The actual source E_j has an eventual fixed positive lower bound for
any nontrivial invariant projection of the original algebra. The threshold
may depend on p; the positive lower bound does not. -/
theorem sourceProjectionEvent_eventually_positive
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p) (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    ∀ᶠ j : ℕ in atTop, Real.exp (-82)/2 ≤ (sourceBiasedLaw j).real (sourceProjectionEvent p j) := by
  have hdiag := sourceProjection_strict_diagonal θ hθ hr hp hproj hp0 hp1 hinv
  have hm : Measurable (fun x => (sourceCentralCoefficient p x).re) :=
    Complex.continuous_re.measurable.comp (sourceCentralCoefficient_measurable p)
  have hpos0 : ∀ᵐ x ∂sourceBaseMeasure, 0 < (sourceCentralCoefficient p x).re :=
    hdiag.mono fun _ h => h.1
  have hpos1 : ∀ᵐ x ∂sourceBaseMeasure, 0 < 1-(sourceCentralCoefficient p x).re :=
    hdiag.mono fun _ h => sub_pos.mpr h.2.1
  have ht0 : Tendsto (fun j => (sourceBiasedLaw j).real (sourceDiagonalLossSet p j false)) atTop (𝓝 0) :=
    sourceBiased_positive_endpoint_loss _ hm hpos0 false
  have ht1 : Tendsto (fun j => (sourceBiasedLaw j).real (sourceDiagonalLossSet p j true)) atTop (𝓝 0) :=
    sourceBiased_positive_endpoint_loss _ (measurable_const.sub hm) hpos1 true
  have ht := (sourceFutureBoundary_loss_tendsto.add ht0).add ht1
  simp only [zero_add] at ht
  have he := ht.eventually (gt_mem_nhds (half_pos (Real.exp_pos (-82))))
  filter_upwards [he] with j hj
  have hh := sourceProjectionEvent_mass_losses p j
  linarith

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_InvariantProjection
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The source probability contradiction for the original operator and
original algebra. All event, convolution and error estimates are proved
from this p's actual projection and invariance identities. -/
theorem sourceInvariantProjection_trivial_oai
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (hr : SourceRationalIndependent θ)
    (hs : SourceOrderedTorusSampling θ) (hphase : ∃ J, SourceSecondPhasesFrom θ J)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0) :
    p = 0 ∨ p = 1 := by
  by_cases hp0 : p = 0
  · exact Or.inl hp0
  by_cases hp1 : p = 1
  · exact Or.inr hp1
  exfalso
  have hlow := sourceProjectionEvent_eventually_positive θ hθ hr hp hproj hp0 hp1 hinv
  obtain ⟨J,hJ⟩ := hphase
  have hbound : ∀ᶠ j : ℕ in atTop, Real.exp (-82)/2 ≤ 1/((j : ℝ)+1) := by
    filter_upwards [hlow,eventually_ge_atTop J] with j hj hJj
    have hphasej : SourceSecondPhasesFrom θ j := fun s hjs => hJ s (hJj.trans hjs)
    exact hj.trans (sourceProjectionEvent_mass_upper θ hθ hs hp hproj hinv j hphasej)
  have hzero : Real.exp (-82)/2 ≤ 0 :=
    ge_of_tendsto (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) hbound
  exact (not_le_of_gt (half_pos (Real.exp_pos (-82)))) hzero

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceInvariantProjection_trivial_oai := @OAI.FiniteFactor.sourceInvariantProjection_trivial_oai
