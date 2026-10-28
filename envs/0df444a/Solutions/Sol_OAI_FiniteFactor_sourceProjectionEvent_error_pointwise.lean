-- Prove2me | solution 1 for OAI.FiniteFactor.sourceProjectionEvent_error_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T23:40:37.427989+00:00
-- url     : https://prove2.me/submissions/9a4a3113-85f0-4778-af2d-c5c1f11de7ae

import Mathlib
import Definitions.Def_OAIQ3Ff001
import Definitions.Def_OAIQ3Ff002
import Theorems.Thm_OAI_FiniteFactor_sourceProjection_biased_ratio_augmented

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
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
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Attenuation
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal
noncomputable section

/-- Crossing 1-fract(a) raises the integer floor by exactly one, for either
sign of a. The half-open endpoints match the source's representatives. -/
theorem floor_crossing_gap {x y a : ℝ} (hx : x ∈ Set.Ico 0 1) (hy : y ∈ Set.Ico 0 1)
    (hcross : x < 1-Int.fract a ∧ 1-Int.fract a ≤ y) :
    Int.floor (y+a) = Int.floor (x+a)+1 := by
  have he (t : ℝ) : t+a = (t+Int.fract a)+(Int.floor a : ℝ) := by rw [Int.fract]; ring
  have hxf : Int.floor (x+Int.fract a) = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨add_nonneg hx.1 (Int.fract_nonneg _), by linarith [hcross.1]⟩
  have hyf : Int.floor (y+Int.fract a) = 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · norm_num
      linarith [hcross.2]
    · norm_num
      linarith [hy.2, Int.fract_lt_one a]
  rw [he y, he x, Int.floor_add_intCast, Int.floor_add_intCast, hxf, hyf]
  omega

/-- Every actual threshold crossing supplies the factor exp(-c_i) in the
source cocycle ratio. No attenuation property of an operator is assumed. -/
theorem sourceCocycle_crossing_attenuation {ι : Type*} (θ c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) {x y : ι → ℝ}
    (hx : finiteFloorSupport θ x) (hy : finiteFloorSupport θ y)
    (hxy : ∀ i, x i ≤ y i) (k : ℤ) (i : ι)
    (hxi : x i ∈ Set.Ico 0 1) (hyi : y i ∈ Set.Ico 0 1)
    (hcross : x i < 1-Int.fract ((k : ℝ)*θ i) ∧ 1-Int.fract ((k : ℝ)*θ i) ≤ y i) :
    sourceCocycle θ c k y / sourceCocycle θ c k x ≤ Real.exp (-c i) := by
  have hs := (sourceLog_summable θ c hy k).sub (sourceLog_summable θ c hx k)
  have hnon (j : ι) : 0 ≤ c j * (coordinateFloor θ k y j : ℝ) - c j * (coordinateFloor θ k x j : ℝ) := by
    apply sub_nonneg.mpr
    apply mul_le_mul_of_nonneg_left _ (hc j)
    have hh : coordinateFloor θ k x j ≤ coordinateFloor θ k y j :=
      Int.floor_mono (add_le_add (hxy j) le_rfl)
    exact_mod_cast hh
  have hgap : c i * (coordinateFloor θ k y i : ℝ) - c i * (coordinateFloor θ k x i : ℝ) = c i := by
    have hh := floor_crossing_gap hxi hyi hcross
    change coordinateFloor θ k y i = coordinateFloor θ k x i + 1 at hh
    rw [hh, Int.cast_add, Int.cast_one]
    ring
  have hle := hs.le_tsum i (fun j _ => hnon j)
  rw [hgap, (sourceLog_summable θ c hy k).tsum_sub (sourceLog_summable θ c hx k)] at hle
  rw [sourceCocycle, sourceCocycle, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  change c i ≤ sourceLog θ c k y - sourceLog θ c k x at hle
  linarith

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

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_Shift
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal
noncomputable section

/-- Invariance of a projection range persists under every nonnegative power. -/
theorem invariant_projection_pow {R : Type*} [Ring R] (p T : R)
    (hp : p*p = p) (hinv : (1-p)*T*p = 0) : ∀ n : ℕ, (1-p)*(T^n)*p = 0 := by
  have hTp : T*p = p*T*p := by
    have h := hinv
    rw [sub_mul, one_mul, sub_mul] at h
    exact sub_eq_zero.mp h
  have hfix : ∀ n : ℕ, T^n*p = p*(T^n)*p := by
    intro n
    induction n with
    | zero => simpa using hp.symm
    | succ n ih =>
      calc
        T^(n+1)*p = T*(T^n*p) := by rw [pow_succ', mul_assoc]
        _ = T*(p*T^n*p) := by rw [ih]
        _ = (T*p)*T^n*p := by simp only [mul_assoc]
        _ = (p*T*p)*T^n*p := by rw [hTp]
        _ = p*T*(p*T^n*p) := by simp only [mul_assoc]
        _ = p*T*(T^n*p) := by rw [← ih]
        _ = p*T^(n+1)*p := by rw [pow_succ']; simp only [mul_assoc]
  intro n
  rw [sub_mul, one_mul, sub_mul, hfix n]
  simp only [mul_assoc, sub_self]

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
-- module Solutions.OAIQ3_FF.FiniteFactor_Convolution
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open scoped ComplexConjugate ENNReal

/-- Both cocycle ratio bounds, valid at every integer index. -/
theorem cocycle_two_ratio_bounds {F G : ℤ → ℝ}
    (hF : ∀ k, 0 < F k) (hG : ∀ k, 0 < G k)
    (hFa : Antitone F) (hGa : Antitone G) (hGF : ∀ k, G k ≤ F k)
    {n v : ℤ} (hn : 0 ≤ n) :
    0 < G (n + v) / F v ∧
    G (n + v) / F v ≤ min (G v / F v) (G (n + v) / F (n + v)) ∧
    min (G v / F v) (G (n + v) / F (n + v)) ≤ 1 := by
  have hv : v ≤ n + v := by omega
  refine ⟨div_pos (hG _) (hF _), le_min ?_ ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (hGa hv) (hF v).le
  · exact div_le_div_of_nonneg_left (hG _).le (hF _) (hFa hv)
  · exact (min_le_left _ _).trans ((div_le_one (hF v)).2 (hGF v))

/-- Cauchy--Schwarz with a genuine integer translation of the second vector. -/
theorem shifted_l2_norm_product (ξ γ : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    Summable (fun v => ‖ξ v‖ * ‖γ (n + v)‖) ∧
    (∑' v, ‖ξ v‖ * ‖γ (n + v)‖) ≤ ‖ξ‖ * ‖γ‖ := by
  have hp : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have hξ : HasSum (fun v => ‖ξ v‖ ^ (2 : ℝ)) (‖ξ‖ ^ (2 : ℝ)) := by
    simpa using lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ
  have hγ : HasSum (fun v => ‖γ (n + v)‖ ^ (2 : ℝ)) (‖γ‖ ^ (2 : ℝ)) := by
    have h : HasSum (fun v : ℤ => ‖γ v‖ ^ (2 : ℝ)) (‖γ‖ ^ (2 : ℝ)) := by
      simpa using lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) γ
    exact (Equiv.addLeft n).hasSum_iff.mpr h
  obtain ⟨C, _, hC, hs⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hp
    (norm_nonneg ξ) (norm_nonneg γ) (fun v => norm_nonneg (ξ v))
    (fun v => norm_nonneg (γ (n + v))) hξ hγ
  exact ⟨hs.summable, hs.tsum_eq ▸ hC⟩

/-- The ratio-weighted convolution is absolutely convergent and has the sharp
product-of-L²-norms bound. -/
theorem weighted_convolution_summable (ξ γ : lp (fun _ : ℤ => ℂ) 2)
    (n : ℤ) {r : ℤ → ℝ} (hr0 : ∀ v, 0 ≤ r v) (hr1 : ∀ v, r v ≤ 1) :
    Summable (fun v => ‖(r v : ℂ) * ξ v * conj (γ (n + v))‖) ∧
    (∑' v, ‖(r v : ℂ) * ξ v * conj (γ (n + v))‖) ≤ ‖ξ‖ * ‖γ‖ := by
  obtain ⟨hs, hb⟩ := shifted_l2_norm_product ξ γ n
  have hbound : ∀ v, ‖(r v : ℂ) * ξ v * conj (γ (n + v))‖ ≤
      ‖ξ v‖ * ‖γ (n + v)‖ := by
    intro v
    simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hr0 v)]
    calc
      r v * ‖ξ v‖ * ‖γ (n + v)‖ = r v * (‖ξ v‖ * ‖γ (n + v)‖) := mul_assoc _ _ _
      _ ≤ 1 * (‖ξ v‖ * ‖γ (n + v)‖) := mul_le_mul_of_nonneg_right (hr1 v) (by positivity)
      _ = _ := one_mul _
  have hsum := hs.of_nonneg_of_le (fun v => norm_nonneg _) hbound
  exact ⟨hsum, (hsum.tsum_le_tsum hbound hs).trans hb⟩

theorem cocycle_convolution_term_eq (F G : ℤ → ℝ) (ξ γ : ℤ → ℂ) (n v : ℤ) :
    leftCoefficient F ξ v * rightCoefficient G γ (-n-v) =
      (G (n+v) / F v : ℝ) * ξ v * conj (γ (n+v)) := by
  have hi : -(-n-v) = n+v := by omega
  simp only [leftCoefficient, rightCoefficient, hi, Complex.ofReal_div]
  ring

theorem cocycle_convolution_absolute_convergence
    (ξ γ : lp (fun _ : ℤ => ℂ) 2) {F G : ℤ → ℝ}
    (hF : ∀ k, 0 < F k) (hG : ∀ k, 0 < G k)
    (hFa : Antitone F) (hGa : Antitone G) (hGF : ∀ k, G k ≤ F k)
    {n : ℤ} (hn : 0 ≤ n) :
    Summable (fun v => ‖leftCoefficient F ξ v * rightCoefficient G γ (-n-v)‖) ∧
    (∑' v, ‖leftCoefficient F ξ v * rightCoefficient G γ (-n-v)‖) ≤ ‖ξ‖ * ‖γ‖ := by
  simp only [cocycle_convolution_term_eq]
  apply weighted_convolution_summable
  · intro v
    exact (cocycle_two_ratio_bounds hF hG hFa hGa hGF hn).1.le
  · intro v
    have h := cocycle_two_ratio_bounds hF hG hFa hGa hGF (v := v) hn
    exact h.2.1.trans h.2.2

/-- Reindexing the Hilbert inner product gives the exact convolution from
coordinates of the shifted weighted vector. -/
theorem weighted_shift_convolution_eq_inner
    (ξ γ η : lp (fun _ : ℤ => ℂ) 2) (r : ℤ → ℝ) (n : ℤ)
    (hη : ∀ v, η (n+v) = (r v : ℂ) * ξ v) :
    (∑' v, (r v : ℂ) * ξ v * conj (γ (n+v))) = inner ℂ γ η := by
  rw [lp.inner_eq_tsum]
  rw [← (Equiv.addLeft n).tsum_eq (fun k : ℤ => inner ℂ (γ k) (η k))]
  apply tsum_congr
  intro v
  change (r v : ℂ) * ξ v * conj (γ (n+v)) = inner ℂ (γ (n+v)) (η (n+v))
  rw [hη]
  simp only [RCLike.inner_apply]

/-- Removing any finite part of a zero absolutely convergent series gives its
 exact complementary tail, before applying the triangle inequality. -/
theorem finite_part_eq_neg_tail {t : ℤ → ℂ} (ht : Summable t)
    (hzero : ∑' v, t v = 0) (W : Finset ℤ) :
    (∑ v ∈ W, t v) = -(∑' v : {v : ℤ // v ∉ W}, t v) := by
  have h := ht.sum_add_tsum_subtype_compl W
  rw [hzero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem finite_part_norm_le_tail {t : ℤ → ℂ} (ht : Summable (fun v => ‖t v‖))
    (hzero : ∑' v, t v = 0) (W : Finset ℤ) :
    ‖∑ v ∈ W, t v‖ ≤ ∑' v : {v : ℤ // v ∉ W}, ‖t v‖ := by
  rw [finite_part_eq_neg_tail ht.of_norm hzero W, norm_neg]
  exact norm_tsum_le_tsum_norm (ht.subtype _)

theorem omittedIndex_spec (K : ℕ) (n v : ℤ)
    (h : (K : ℤ) < |v| ∨ (K : ℤ) < |n+v|) :
    (K : ℤ) < |omittedIndex K n v| ∧
    (omittedIndex K n v = v ∨ omittedIndex K n v = n+v) := by
  unfold omittedIndex
  split_ifs with hv
  · exact ⟨hv, Or.inl rfl⟩
  · exact ⟨h.resolve_left hv, Or.inr rfl⟩

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

/-- On ordered noncrossing pairs, the two eligibility counts are complementary.
Thus the strict second half of the source bad event lies in the reverse
badHalfEvent; using a weak inequality there only enlarges that event. -/
theorem noncrossing_eligible_complement {ι : Type*} (x y u : ι → ℝ) (I : Finset ι)
    (hxy : ∀ i ∈ I, x i ≤ y i) (hn : ∀ i ∈ I, ¬(x i < u i ∧ u i ≤ y i)) :
    (eligibleIndices (fun _ => false) x u I).card +
      (eligibleIndices (fun _ => true) y u I).card = I.card := by
  have he : eligibleIndices (fun _ => true) y u I = I.filter (fun i => ¬(x i < u i)) := by
    ext i
    simp only [eligibleIndices, Finset.mem_filter, eligible, ↓reduceIte]
    constructor
    · rintro ⟨hi, hy⟩
      exact ⟨hi, fun hx => hn i hi ⟨hx, hy⟩⟩
    · rintro ⟨hi, hx⟩
      exact ⟨hi, le_trans (le_of_not_gt hx) (hxy i hi)⟩
  rw [he]
  exact Finset.card_filter_add_card_filter_not (fun i => x i < u i)

/-- Exact source second-half event is contained in the reverse event whose
conditional estimate was proved above. All coordinates in I are accounted for. -/
theorem second_bad_half_in_reverse {ι : Type*} (x y u : ι → ℝ) (I : Finset ι)
    (hxy : ∀ i ∈ I, x i ≤ y i)
    (hn : ∀ i ∈ I, ¬(x i < u i ∧ u i ≤ y i))
    (hcount : ((eligibleIndices (fun _ => false) x u I).card : ℝ) < (I.card : ℝ)/2) :
    (y,x) ∈ badHalfEvent (fun _ => true) u I I.card := by
  constructor
  · have he := noncrossing_eligible_complement x y u I hxy hn
    have her : ((eligibleIndices (fun _ => false) x u I).card : ℝ) +
        ((eligibleIndices (fun _ => true) y u I).card : ℝ) = (I.card : ℝ) := by exact_mod_cast he
    linarith
  · intro i hi
    exact hn i i.2 ⟨hi.2, hi.1⟩

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

/-- The source coefficient L_j is bounded by the drop in each assigned block. -/
theorem staged_drop_budget (j s : ℕ) (hjs : j ≤ s) :
    (sourceStage j).L ≤ (sourceStage s).C :=
  (sourceStage_L_mono hjs).trans (le_max_left _ _)

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

/-- At an assigned index, failure of both oriented bad events forces an
actual floor crossing, hence the original uncapped ratio is attenuated. -/
theorem attenuation_or_bad (hθ : SourceAngles θ) (a : SourcePhaseAssignment θ j k) :
    ∀ᵐ ω ∂sourceBiasedLaw j,
      sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) ≤
          Real.exp (-(sourceStage j).L) ∨ ω ∈ a.badEvent false ∨ ω ∈ a.badEvent true := by
  have hcube := vectorEndpoint_unitCube (fun i : SourceCoordinate => stagedCouplingParameters j i.1)
  have hx := ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => false)).aemeasurable
    (hcube (fun _ => false))
  have hy := ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => true)).aemeasurable
    (hcube (fun _ => true))
  filter_upwards [hx,hy,sourceBiasedLaw_ordered j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable)]
    with ω hxc hyc hxy hfx hfy
  let x := sourceBiasedEndpoint (fun _ => false) ω
  let y := sourceBiasedEndpoint (fun _ => true) ω
  let u := fun i => 1-Int.fract ((k : ℝ)*θ i)
  by_cases hc : ∃ i ∈ a.indices, x i < u i ∧ u i ≤ y i
  · obtain ⟨i,hi,hcross⟩ := hc
    apply Or.inl
    have hatt := sourceCocycle_crossing_attenuation θ sourceLogWeight sourceLogWeight_nonneg
      hfx hfy hxy k i (hxc i) (hyc i) hcross
    apply hatt.trans
    apply Real.exp_le_exp.mpr
    have his := mem_sourceBlockCoordinates (a.subset hi)
    change -(sourceStage i.1).C ≤ -(sourceStage j).L
    rw [his]
    exact neg_le_neg (staged_drop_budget j a.block a.later)
  · have hn : ∀ i ∈ a.indices, ¬(x i < u i ∧ u i ≤ y i) := by
      intro i hi hc'; exact hc ⟨i,hi,hc'⟩
    by_cases hcount : (a.indices.card : ℝ)/2 ≤
        ((eligibleIndices (fun _ => false) x u a.indices).card : ℝ)
    · apply Or.inr ∘ Or.inl
      refine ⟨hcount,?_⟩
      intro i hh
      exact hn i i.2 hh
    · apply Or.inr ∘ Or.inr
      exact second_bad_half_in_reverse x y u a.indices (fun i _ => hxy i) hn (lt_of_not_ge hcount)

end SourcePhaseAssignment
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ConvolutionCocycle
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- The actual cocycle is antitone in every integer index, including negative indices. -/
theorem sourceCocycle_antitone {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    {x : ι → ℝ} (hx : finiteFloorSupport θ x) :
    Antitone (fun k : ℤ => sourceCocycle θ c k x) := by
  intro k l hkl
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply (sourceLog_summable θ c hx k).tsum_le_tsum _ (sourceLog_summable θ c hx l)
  intro i
  apply mul_le_mul_of_nonneg_left _ (hc i)
  have hh : coordinateFloor θ k x i ≤ coordinateFloor θ l x i := by
    apply Int.floor_mono
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) (hθ i)
  exact_mod_cast hh

/-- Exact positive-power weight in terms of the two integer cocycle values. -/
theorem sourceCocycle_power_weight {ι : Type*} (θ c : ι → ℝ)
    {x : ι → ℝ} (hx : finiteFloorSupport θ x) (n : ℕ) (k : ℤ) :
    sourceCocycle θ c n (coordinateRotate θ k x) =
      sourceCocycle θ c ((n : ℤ)+k) x / sourceCocycle θ c k x := by
  rw [add_comm (n : ℤ) k,sourceCocycle_add θ c hx]
  exact (mul_div_cancel_right₀ _ (ne_of_gt (sourceCocycle_pos θ c k x))).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TagGeometry
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

theorem SourceAngles.tag_threshold {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ)
    (j : ℕ) (k : ℤ) (hk : ((sourceStageState j).K : ℝ) ≤ |(k : ℝ)|)
    (hhi : |(k : ℝ)| ≤ ((sourceBlockSize j : ℝ)*(sourceStageState j).K)/4)
    (i : Fin (sourceBlockSize j)) :
    1-Int.fract ((k : ℝ)*θ ⟨j,i⟩) ∈ Set.Icc (1/(sourceBlockSize j : ℝ)) (1-1/(sourceBlockSize j : ℝ)) := by
  have hm := sourceBlockSize_pos j
  have hK := sourceCutoff_pos j
  apply phase_threshold_of_abs (one_div_pos.mpr hm)
  · apply (div_le_iff₀ hm).mpr
    have hh : (100 : ℝ) ≤ sourceBlockSize j := by exact_mod_cast (sourceStage j).m_ge_100
    linarith
  · rw [abs_mul,abs_of_nonneg (hθ.nonneg ⟨j,i⟩)]
    calc
      1/(sourceBlockSize j : ℝ) = (sourceStageState j).K *
          (1/((sourceBlockSize j : ℝ)*(sourceStageState j).K)) := by field_simp
      _ ≤ |(k : ℝ)| * θ ⟨j,i⟩ :=
        mul_le_mul hk (hθ ⟨j,i⟩).1 (by positivity) (abs_nonneg _)
  · rw [abs_mul,abs_of_nonneg (hθ.nonneg ⟨j,i⟩)]
    calc
      |(k : ℝ)| * θ ⟨j,i⟩ ≤ (((sourceBlockSize j : ℝ)*(sourceStageState j).K)/4) *
          (2/((sourceBlockSize j : ℝ)*(sourceStageState j).K)) :=
        mul_le_mul hhi (hθ ⟨j,i⟩).2 (hθ.nonneg _) (by positivity)
      _ = 1/2 := by field_simp; norm_num

/-- Actual cocycle attenuation on the endpoint event, simultaneously at all
near-range signed integer indices. No cutoff is applied to the ratio. -/
theorem sourceTagEndpoint_attenuation (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceTagEndpointEvent j → ∀ k : ℤ,
      ((sourceStageState j).K : ℝ) ≤ |(k : ℝ)| →
      |(k : ℝ)| ≤ ((sourceBlockSize j : ℝ)*(sourceStageState j).K)/4 →
      sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) ≤
          Real.exp (-(sourceStage j).L) := by
  have hcube := CouplingParameters.vectorEndpoint_unitCube
    (fun i : SourceCoordinate => stagedCouplingParameters j i.1)
  filter_upwards [
    ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => false)).aemeasurable (hcube (fun _ => false)),
    ae_of_ae_map (sourceBiasedEndpoint_measurable (fun _ => true)).aemeasurable (hcube (fun _ => true)),
    sourceBiasedLaw_ordered j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable)]
    with ω hxc hyc hxy hfx hfy
  rintro ⟨i,hxi,hyi⟩ k hk hhi
  have ht := hθ.tag_threshold j k hk hhi i
  have hatt := sourceCocycle_crossing_attenuation θ sourceLogWeight sourceLogWeight_nonneg
    hfx hfy hxy k ⟨j,i⟩ (hxc _) (hyc _) ⟨hxi.trans_le ht.1,ht.2.trans hyi⟩
  exact hatt.trans (Real.exp_le_exp.mpr (neg_le_neg (le_max_left _ _)))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OmittedRatio
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

/-- The source two-ratio inequality and deterministic omitted-index choice
turn tagged and phase attenuation into the pointwise error majorant. -/
theorem sourceOmitted_ratio_bound (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n v : ℤ) (hn : 0 ≤ n)
    (hv : ((sourceStageState j).K : ℤ) < |v| ∨ ((sourceStageState j).K : ℤ) < |n+v|) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceTagEndpointEvent j →
      sourceCocycle θ sourceLogWeight (n+v) (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight v (sourceBiasedEndpoint (fun _ => false) ω) ≤
          Real.exp (-(sourceStage j).L) +
            (sourceOmittedBadEvent θ hθ j hphase n v false).indicator (fun _ => (1 : ℝ)) ω +
            (sourceOmittedBadEvent θ hθ j hphase n v true).indicator (fun _ => (1 : ℝ)) ω := by
  let k := omittedIndex (sourceStageState j).K n v
  have hk := omittedIndex_spec (sourceStageState j).K n v hv
  have hlarge : ∀ᵐ ω ∂sourceBiasedLaw j,
      sourcePhaseLower j < |(k : ℝ)| →
      sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight k (sourceBiasedEndpoint (fun _ => false) ω) ≤
          Real.exp (-(sourceStage j).L) ∨
        ω ∈ sourceOmittedBadEvent θ hθ j hphase n v false ∨
        ω ∈ sourceOmittedBadEvent θ hθ j hphase n v true := by
    by_cases hh : sourcePhaseLower j < |(k : ℝ)|
    · have ha := (sourceChosenAssignment θ hθ j hphase k hh.le).attenuation_or_bad hθ
      filter_upwards [ha] with ω hω _
      have htest : (((sourceStageState j).K : ℤ) < |v| ∨ ((sourceStageState j).K : ℤ) < |n+v|) ∧
          sourcePhaseLower j < |(omittedIndex (sourceStageState j).K n v : ℝ)| := ⟨hv,hh⟩
      simpa only [sourceOmittedBadEvent,dite_eq_left htest] using hω
    · exact Eventually.of_forall fun ω h => (hh h).elim
  filter_upwards [hlarge,sourceTagEndpoint_attenuation θ hθ j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedLaw_ordered j] with ω hfar htag hfx hfy hxy
  intro he
  let x := sourceBiasedEndpoint (fun _ => false) ω
  let y := sourceBiasedEndpoint (fun _ => true) ω
  have hb := cocycle_two_ratio_bounds
    (fun k => sourceCocycle_pos θ sourceLogWeight k x)
    (fun k => sourceCocycle_pos θ sourceLogWeight k y)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfx)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfy)
    (sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hfx hfy hxy)
    (v := v) hn
  have hratio : sourceCocycle θ sourceLogWeight (n+v) y / sourceCocycle θ sourceLogWeight v x ≤
      sourceCocycle θ sourceLogWeight k y / sourceCocycle θ sourceLogWeight k x := by
    rcases hk.2 with h | h
    · rw [show k = v from h]
      exact hb.2.1.trans (min_le_left _ _)
    · rw [show k = n+v from h]
      exact hb.2.1.trans (min_le_right _ _)
  have h1 := hb.2.1.trans hb.2.2
  have hbad0 (b : Bool) : 0 ≤ (sourceOmittedBadEvent θ hθ j hphase n v b).indicator (fun _ => (1 : ℝ)) ω := by
    by_cases h : ω ∈ sourceOmittedBadEvent θ hθ j hphase n v b <;> simp [h]
  have hpos := (Real.exp_pos (-(sourceStage j).L)).le
  by_cases hh : sourcePhaseLower j < |(k : ℝ)|
  · rcases hfar hh with h | h | h
    · have hle := hratio.trans h
      linarith [hbad0 false,hbad0 true]
    · rw [Set.indicator_of_mem h]
      linarith [hbad0 true]
    · rw [Set.indicator_of_mem h]
      linarith [hbad0 false]
  · have hklo : ((sourceStageState j).K : ℝ) ≤ |(k : ℝ)| := by
      have hki : ((sourceStageState j).K : ℤ) < |k| := hk.1
      exact_mod_cast hki.le
    have hh' := htag he k hklo (le_of_not_gt hh)
    have hle := hratio.trans hh'
    linarith [hbad0 false,hbad0 true]

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
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_TransportConvolution
attribute [-instance] _root_.OAI.FiniteFactor.sourceFiber_separable _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open scoped ComplexConjugate
noncomputable section

/-- Composition of the two genuine range inclusions used in the convolution. -/
theorem invariant_transport_composition {R : Type*} [Ring R] (P Q D W : R)
    (hD : (1-Q)*D*P = 0) (hW : (1-Q)*W*Q = 0) :
    (1-Q)*W*D*P = 0 := by
  have hd : D*P = Q*D*P := by
    apply sub_eq_zero.mp
    simpa only [sub_mul,one_mul] using hD
  calc
    _ = (1-Q)*W*(D*P) := by simp only [mul_assoc]
    _ = (1-Q)*W*(Q*D*P) := by rw [hd]
    _ = ((1-Q)*W*Q)*D*P := by simp only [mul_assoc]
    _ = 0 := by rw [hW,zero_mul,zero_mul]

theorem fiber_complement_inner_zero
    (Q : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (hQ : IsStarProjection Q)
    (u v : SourceFiberHilbert) (hv : (1-Q) v = 0) :
    inner ℂ ((1-Q) u) v = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right (1-Q) u v,
    ← ContinuousLinearMap.star_eq_adjoint,hQ.one_sub.isSelfAdjoint.star_eq,hv,inner_zero_right]

/-- The source convolution vanishes whenever the actual transport and weighted
power identities hold. No square summability of rescaled coefficients is assumed. -/
theorem fiber_transport_convolution_zero
    (P Q D W : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hQ : IsStarProjection Q) (F G : ℤ → ℝ) (hG : ∀ k, G k ≠ 0) (n : ℤ)
    (hD : (1-Q)*D*P = 0) (hW : (1-Q)*W*Q = 0)
    (hDa : ∀ (v : SourceFiberHilbert) (k : ℤ), D v k = (G k / F k : ℂ) * v k)
    (hWa : ∀ (v : SourceFiberHilbert) (k : ℤ), W v (n+k) = (G (n+k) / G k : ℂ) * v k) :
    (∑' k, leftCoefficient F (P (lp.single 2 0 (1 : ℂ))) k *
      rightCoefficient G ((1-Q) (lp.single 2 0 (1 : ℂ))) (-n-k)) = 0 := by
  let ξ := P (lp.single 2 0 (1 : ℂ))
  let γ := (1-Q) (lp.single 2 0 (1 : ℂ))
  let η := W (D ξ)
  have hη : ∀ k, η (n+k) = ((G (n+k) / F k : ℝ) : ℂ) * ξ k := by
    intro k
    dsimp [η]
    rw [hWa,hDa,Complex.ofReal_div]
    have hg : (G k : ℂ) ≠ 0 := by exact_mod_cast hG k
    field_simp
  have hz : (1-Q) η = 0 := by
    exact congrArg (fun A : SourceFiberHilbert →L[ℂ] SourceFiberHilbert => A (lp.single 2 0 (1 : ℂ)))
      (invariant_transport_composition P Q D W hD hW)
  simp only [cocycle_convolution_term_eq]
  rw [weighted_shift_convolution_eq_inner ξ γ η (fun k => G (n+k)/F k) n hη]
  exact fiber_complement_inner_zero Q hQ _ η hz

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionConvolution
attribute [-instance] _root_.OAI.FiniteFactor.sourceHilbert_separable _root_.OAI.FiniteFactor.sourceNormalFunctionalSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_complete _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedGroup _root_.OAI.FiniteFactor.sourceNormalPredualSpace_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ComplexConjugate ENNReal
noncomputable section

/-- The original coefficient sequences satisfy every nonnegative convolution
identity under the actual augmented biased law, with absolute sum at most one.
This instantiates the range and weight hypotheses from the constructed algebra. -/
theorem sourceProjection_convolution (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ∀ n : ℕ,
      (∑' k : ℤ, sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω) k *
        sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω) (-(n : ℤ)-k)) = 0 ∧
      Summable (fun k : ℤ => ‖sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω) k *
        sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω) (-(n : ℤ)-k)‖) ∧
      (∑' k : ℤ, ‖sourceProjectionLeftCoefficient θ p (sourceBiasedEndpoint (fun _ => false) ω) k *
        sourceProjectionRightCoefficient θ p (sourceBiasedEndpoint (fun _ => true) ω) (-(n : ℤ)-k)‖) ≤ 1 := by
  let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
  have hInv : ∀ᵐ y ∂sourceBaseMeasure, ∀ n : ℕ,
      (1-sourceOperatorField p y)*sourceOperatorField (T^n) y*sourceOperatorField p y = 0 := by
    apply ae_all_iff.mpr
    intro n
    exact sourceOperatorField_invariant θ hp (pow_mem (staged_sourceOperator_mem θ hθ) n)
      (invariant_projection_pow p T hproj.isIdempotentElem hinv n)
  have hAct := ae_all_iff.mpr (sourceOperatorField_sourceOperator_pow θ hθ)
  filter_upwards [sourceProjection_biased_ratio_augmented θ hθ hs hp hproj hinv j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedLaw_ordered j,
    sourceBiasedEndpoint_ae j (fun _ => true) (sourceOperatorField_projection θ hp hproj),
    sourceBiasedEndpoint_ae j (fun _ => true) hInv,
    sourceBiasedEndpoint_ae j (fun _ => true) hAct,
    sourceBiasedEndpoint_ae j (fun _ => false) (sourceProjection_columns_norm θ hp hproj),
    sourceBiasedEndpoint_ae j (fun _ => true) (sourceProjection_columns_norm θ hp hproj)]
    with ω hD hfx hfy hord hPy hi ha hnx hny
  intro n
  let x := sourceBiasedEndpoint (fun _ => false) ω
  let y := sourceBiasedEndpoint (fun _ => true) ω
  have hxy : ∀ i, x i ≤ y i := hord
  obtain ⟨D,_hDn,hDa,hd⟩ := hD
  have hz : (∑' k : ℤ, sourceProjectionLeftCoefficient θ p x k *
      sourceProjectionRightCoefficient θ p y (-(n : ℤ)-k)) = 0 := by
    apply fiber_transport_convolution_zero (sourceOperatorField p x) (sourceOperatorField p y) D
      (sourceOperatorField (T^n) y) hPy
      (fun k => sourceCocycle θ sourceLogWeight k x) (fun k => sourceCocycle θ sourceLogWeight k y)
      (fun k => ne_of_gt (sourceCocycle_pos ..)) (n : ℤ) hd (hi n) hDa
    intro v k
    have hk : (n : ℤ)+k-(n : ℤ) = k := by omega
    rw [ha n v ((n : ℤ)+k),hk,sourceCocycle_power_weight θ sourceLogWeight hfy n k,Complex.ofReal_div]
  obtain ⟨habs,hbound⟩ := cocycle_convolution_absolute_convergence
    (sourceProjectionColumn p x) (sourceComplementColumn p y)
    (fun k => sourceCocycle_pos θ sourceLogWeight k x)
    (fun k => sourceCocycle_pos θ sourceLogWeight k y)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfx)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfy)
    (sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hfx hfy hxy)
    (n := (n : ℤ)) (by omega)
  refine ⟨hz,habs,hbound.trans ?_⟩
  exact (mul_le_mul hnx.1 hny.2 (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TagLaw
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

/-- The actual labelled event has the geometric endpoint consequence needed
by every near-range ratio bound, under the original augmented biased law. -/
theorem sourceTaggedEvent_endpoints (j : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceTaggedEvent j → ω ∈ sourceTagEndpointEvent j := by
  have h (i : Fin (sourceBlockSize j)) : ∀ᵐ ω ∂sourceBiasedLaw j,
      (ω ⟨j,i⟩).1 = 5 → (ω ⟨j,i⟩).2.1 < 1/(sourceBlockSize j : ℝ) ∧
        1-1/(sourceBlockSize j : ℝ) ≤ (ω ⟨j,i⟩).2.2 :=
    (measurePreserving_eval_infinitePi
      (fun i : SourceCoordinate => (stagedCouplingParameters j i.1).labelledCoupling) ⟨j,i⟩).quasiMeasurePreserving.ae
      (labelledCoupling_tag_support (stagedCouplingParameters j j))
  filter_upwards [ae_all_iff.mpr h] with ω hω
  rintro ⟨i,hi⟩
  exact ⟨i,hω i hi⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Truncation
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open scoped ComplexConjugate

/-- Sum a row of the Laurent coefficient double sum using its unique possible
second exponent. -/
theorem laurent_row_eq (K : ℕ) (A B : ℤ → ℂ) (r v : ℤ) :
    (∑ j : Fin (2*K+1), if v + ((j.val : ℤ)-K) = r then
      A v * B ((j.val : ℤ)-K) else 0) =
    if -(K : ℤ) ≤ r-v ∧ r-v ≤ K then A v * B (r-v) else 0 := by
  classical
  by_cases hv : -(K : ℤ) ≤ r-v ∧ r-v ≤ K
  · rw [ite_eq_left hv]
    let j : Fin (2*K+1) := ⟨(r-v+K).toNat, by omega⟩
    have hj : (j.val : ℤ)-K = r-v := by dsimp [j]; omega
    rw [Finset.sum_eq_single j]
    · rw [hj, ite_eq_left (by omega)]
    · intro b _ hb
      apply ite_eq_right
      intro he
      apply hb
      apply Fin.ext
      have := b.isLt
      omega
    · simp
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro j _
    apply ite_eq_right
    intro he
    apply hv
    have := j.isLt
    omega

theorem mem_convolutionWindow (K : ℕ) (n v : ℤ) :
    v ∈ convolutionWindow K n ↔ |v| ≤ (K : ℤ) ∧ |n+v| ≤ (K : ℤ) := by
  simp only [convolutionWindow, Finset.mem_filter, Finset.mem_Icc, abs_le]
  omega

theorem not_mem_convolutionWindow (K : ℕ) (n v : ℤ) :
    v ∉ convolutionWindow K n ↔ (K : ℤ) < |v| ∨ (K : ℤ) < |n+v| := by
  rw [mem_convolutionWindow]
  omega

theorem laurent_coefficient_eq_finite_convolution (K : ℕ) (A B : ℤ → ℂ) (n : ℤ) :
    laurentProductCoefficient K A B (-n) =
      ∑ v ∈ convolutionWindow K n, A v * B (-n-v) := by
  classical
  simp only [laurentProductCoefficient, laurent_row_eq]
  rw [convolutionWindow, Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => (i.val : ℤ)-K)
  · intro i _
    simp only [Finset.mem_Icc]
    have := i.isLt
    omega
  · intro i _ j _ hij
    apply Fin.ext
    omega
  · intro v hv
    simp only [Finset.mem_Icc] at hv
    refine ⟨⟨(v+K).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    omega
  · intro i _
    rfl

/-- The corresponding absolute tail bound used in error-pointwise. -/
theorem laurent_coefficient_norm_le_tail (K : ℕ) (A B : ℤ → ℂ) (n : ℤ)
    (hs : Summable (fun v => ‖A v * B (-n-v)‖))
    (hz : ∑' v, A v * B (-n-v) = 0) :
    ‖laurentProductCoefficient K A B (-n)‖ ≤
      ∑' v : {v : ℤ // v ∉ convolutionWindow K n}, ‖A v * B (-n-v)‖ := by
  rw [laurent_coefficient_eq_finite_convolution]
  exact finite_part_norm_le_tail hs hz _

/-- The full pointwise error estimate. The two exceptional masks remain
separate and each is summed over all of ℤ; no union bound is introduced. -/
theorem laurent_error_pointwise (K : ℕ) (n : ℤ)
    (ξ γ : lp (fun _ : ℤ => ℂ) 2) {F G : ℤ → ℝ}
    (hF : ∀ k, 0 < F k) (hG : ∀ k, 0 < G k)
    (hFa : Antitone F) (hGa : Antitone G) (hGF : ∀ k, G k ≤ F k)
    (hn : 0 ≤ n) {H₁ H₂ : Set ℤ} {ε : ℝ} (hε : 0 ≤ ε)
    (hz : ∑' v, leftCoefficient F ξ v * rightCoefficient G γ (-n-v) = 0)
    (hR : ∀ v, v ∉ convolutionWindow K n →
      G (n+v) / F v ≤ ε + H₁.indicator (fun _ => 1) v +
        H₂.indicator (fun _ => 1) v) :
    ‖laurentProductCoefficient K (leftCoefficient F ξ) (rightCoefficient G γ) (-n)‖ ≤
      ε * (‖ξ‖ * ‖γ‖) +
      (∑' v, H₁.indicator (fun v => ‖ξ v‖ * ‖γ (n+v)‖) v) +
      (∑' v, H₂.indicator (fun v => ‖ξ v‖ * ‖γ (n+v)‖) v) := by
  classical
  let p : ℤ → ℝ := fun v => ‖ξ v‖ * ‖γ (n+v)‖
  have hp0 : ∀ v, 0 ≤ p v := fun v => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  obtain ⟨hp, hpbound⟩ := shifted_l2_norm_product ξ γ n
  change Summable p at hp
  change (∑' v, p v) ≤ ‖ξ‖ * ‖γ‖ at hpbound
  have hmask : ∀ H : Set ℤ, Summable (H.indicator p) := by
    intro H
    apply hp.of_nonneg_of_le
    · intro v
      by_cases hv : v ∈ H <;> simp [hv, hp0]
    · intro v
      by_cases hv : v ∈ H <;> simp [hv, hp0]
  let b : ℤ → ℝ := fun v => ε * p v + H₁.indicator p v + H₂.indicator p v
  have hb : Summable b := ((hp.mul_left ε).add (hmask H₁)).add (hmask H₂)
  have hb0 : ∀ v, 0 ≤ b v := by
    intro v
    dsimp [b]
    have h₁ : 0 ≤ H₁.indicator p v := by by_cases hv : v ∈ H₁ <;> simp [hv, hp0]
    have h₂ : 0 ≤ H₂.indicator p v := by by_cases hv : v ∈ H₂ <;> simp [hv, hp0]
    exact add_nonneg (add_nonneg (mul_nonneg hε (hp0 v)) h₁) h₂
  have hterm : ∀ v, v ∉ convolutionWindow K n →
      ‖leftCoefficient F ξ v * rightCoefficient G γ (-n-v)‖ ≤ b v := by
    intro v hv
    rw [cocycle_convolution_term_eq]
    have hr : 0 ≤ G (n+v) / F v := (div_pos (hG _) (hF _)).le
    simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr]
    calc
      G (n+v) / F v * ‖ξ v‖ * ‖γ (n+v)‖ = (G (n+v) / F v) * p v := by dsimp [p]; ring
      _ ≤ (ε + H₁.indicator (fun _ => 1) v + H₂.indicator (fun _ => 1) v) * p v :=
        mul_le_mul_of_nonneg_right (hR v hv) (hp0 v)
      _ = b v := by
        dsimp [b]
        by_cases h₁ : v ∈ H₁ <;> by_cases h₂ : v ∈ H₂ <;> simp [h₁, h₂] <;> ring
  have hs := (cocycle_convolution_absolute_convergence ξ γ hF hG hFa hGa hGF hn).1
  calc
    ‖laurentProductCoefficient K (leftCoefficient F ξ) (rightCoefficient G γ) (-n)‖ ≤
        ∑' v : {v : ℤ // v ∉ convolutionWindow K n},
          ‖leftCoefficient F ξ v * rightCoefficient G γ (-n-v)‖ :=
      laurent_coefficient_norm_le_tail K _ _ n hs hz
    _ ≤ ∑' v : {v : ℤ // v ∉ convolutionWindow K n}, b v :=
      (hs.subtype _).tsum_le_tsum (fun v => hterm v v.property) (hb.subtype _)
    _ ≤ ∑' v, b v := hb.tsum_subtype_le _ _ hb0
    _ = ε * (∑' v, p v) + (∑' v, H₁.indicator p v) + (∑' v, H₂.indicator p v) := by
      change (∑' v, (ε * p v + H₁.indicator p v + H₂.indicator p v)) = _
      rw [Summable.tsum_add ((hp.mul_left ε).add (hmask H₁)) (hmask H₂),
        Summable.tsum_add (hp.mul_left ε) (hmask H₁), tsum_mul_left]
    _ ≤ _ := by
      change ε * (∑' v, p v) + (∑' v, H₁.indicator p v) + (∑' v, H₂.indicator p v) ≤
        ε * (‖ξ‖ * ‖γ‖) + (∑' v, H₁.indicator p v) + (∑' v, H₂.indicator p v)
      linarith [mul_le_mul_of_nonneg_left hpbound hε]

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

/-- Exchange the coefficient and sample viewpoints of the same mask. -/
theorem indicator_swap {ι Ω : Type*} (H : ι → Set Ω) (f : ι → Ω → ℝ) (i : ι) (ω : Ω) :
    {k | ω ∈ H k}.indicator (fun k => f k ω) i = (H i).indicator (f i) ω := by
  classical
  by_cases h : ω ∈ H i
  · rw [Set.indicator_of_mem (show i ∈ {k | ω ∈ H k} from h),Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (show i ∉ {k | ω ∈ H k} from h),Set.indicator_of_notMem h]

theorem sourceProjectionEvent_error_pointwise_oai (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (hs : SourceOrderedTorusSampling θ)
    {p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hp : p ∈ sourceAlgebra θ) (hproj : IsStarProjection p)
    (hinv : (1-p)*sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg*p = 0)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (n : ℕ) :
    ∀ᵐ ω ∂sourceBiasedLaw j, ω ∈ sourceProjectionEvent p j →
      ‖sourceTruncatedCoefficient θ p j n ω‖ ≤ Real.exp (-(sourceStage j).L) +
        sourceOmittedError θ hθ p j hphase n false ω + sourceOmittedError θ hθ p j hphase n true ω := by
  let H := fun b v => sourceOmittedBadEvent θ hθ j hphase (n : ℤ) v b
  have hratio : ∀ᵐ ω ∂sourceBiasedLaw j, ∀ v : ℤ,
      v ∉ convolutionWindow (sourceStageState j).K n → ω ∈ sourceTagEndpointEvent j →
      sourceCocycle θ sourceLogWeight ((n : ℤ)+v) (sourceBiasedEndpoint (fun _ => true) ω) /
        sourceCocycle θ sourceLogWeight v (sourceBiasedEndpoint (fun _ => false) ω) ≤
        Real.exp (-(sourceStage j).L)+(H false v).indicator (fun _ => (1 : ℝ)) ω+
          (H true v).indicator (fun _ => (1 : ℝ)) ω := by
    apply ae_all_iff.mpr
    intro v
    by_cases hv : v ∉ convolutionWindow (sourceStageState j).K n
    · exact (sourceOmitted_ratio_bound θ hθ j hphase n v (by omega)
        ((not_mem_convolutionWindow _ _ _).mp hv)).mono (fun ω h _ => h)
    · exact Eventually.of_forall (fun ω h => (hv h).elim)
  filter_upwards [hratio,sourceProjection_convolution θ hθ hs hp hproj hinv j,
    sourceTaggedEvent_endpoints j,sourceBiasedLaw_ordered j,
    sourceBiasedEndpoint_ae j (fun _ => false) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => true) (ae_finiteFloorSupport θ hθ.summable),
    sourceBiasedEndpoint_ae j (fun _ => false) (sourceProjection_columns_norm θ hp hproj),
    sourceBiasedEndpoint_ae j (fun _ => true) (sourceProjection_columns_norm θ hp hproj)]
    with ω hr hc ht hxy hfx hfy hnx hny
  intro he
  let x := sourceBiasedEndpoint (fun _ => false) ω
  let y := sourceBiasedEndpoint (fun _ => true) ω
  have hind (b : Bool) (v : ℤ) :
      {k | ω ∈ H b k}.indicator (fun _ => (1 : ℝ)) v = (H b v).indicator (fun _ => (1 : ℝ)) ω :=
    indicator_swap (H b) (fun _ _ => (1 : ℝ)) v ω
  have hmask (b : Bool) (v : ℤ) :
      {k | ω ∈ H b k}.indicator
        (fun k => ‖sourceProjectionColumn p x k‖*‖sourceComplementColumn p y ((n : ℤ)+k)‖) v =
      (H b v).indicator (fun ω =>
        ‖sourceProjectionColumn p (sourceBiasedEndpoint (fun _ => false) ω) v‖*
          ‖sourceComplementColumn p (sourceBiasedEndpoint (fun _ => true) ω) ((n : ℤ)+v)‖) ω := by
    by_cases h : ω ∈ H b v
    · rw [Set.indicator_of_mem (show v ∈ {k | ω ∈ H b k} from h),Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (show v ∉ {k | ω ∈ H b k} from h),Set.indicator_of_notMem h]
  have hh := laurent_error_pointwise (sourceStageState j).K (n : ℤ)
    (sourceProjectionColumn p x) (sourceComplementColumn p y)
    (fun k => sourceCocycle_pos θ sourceLogWeight k x) (fun k => sourceCocycle_pos θ sourceLogWeight k y)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfx)
    (sourceCocycle_antitone θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg hfy)
    (sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hfx hfy hxy)
    (by omega : (0 : ℤ) ≤ n) (H₁ := {v | ω ∈ H false v}) (H₂ := {v | ω ∈ H true v})
    (Real.exp_pos (-(sourceStage j).L)).le (hc n).1
    (fun v hv => by rw [hind false v,hind true v]; exact hr v hv (ht he.1.1))
  simp_rw [hmask] at hh
  change ‖sourceTruncatedCoefficient θ p j n ω‖ ≤
    Real.exp (-(sourceStage j).L)*(‖sourceProjectionColumn p x‖*‖sourceComplementColumn p y‖)+
      sourceOmittedError θ hθ p j hphase n false ω+sourceOmittedError θ hθ p j hphase n true ω at hh
  have hnorm : ‖sourceProjectionColumn p x‖*‖sourceComplementColumn p y‖ ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hnx.1 hny.2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hbound := mul_le_mul_of_nonneg_left hnorm (Real.exp_pos (-(sourceStage j).L)).le
  linarith

end
end FiniteFactor

end OAI
end

theorem solution : type_of% @OAI.FiniteFactor.sourceProjectionEvent_error_pointwise_oai := @OAI.FiniteFactor.sourceProjectionEvent_error_pointwise_oai
