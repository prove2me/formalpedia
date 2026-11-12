-- Prove2me | solution 1 for OAI.InvariantIsing.finiteVariational_ne_top_bot
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:26:27.043861+00:00
-- url     : https://prove2.me/submissions/b3961cc1-7f6a-4b5f-9a2b-25dc00040ef9

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258003
import Theorems.Thm_OAI_InvariantIsing_entropyFunctional_zero

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_Field
attribute [-instance] _root_.OAI.InvariantIsing.biasedFieldLevelSpinPair_probability _root_.OAI.InvariantIsing.cavityLinearFieldCoordinateLaw_isProbabilityMeasure _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The one-site Gaussian functional

These are the finite Gaussian recursion and extended-real optimization in
(1.5)--(1.7) of the manuscript. The field supremum stays inside the path
infimum.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace InvariantIsing

lemma entropyFunctional_nonneg (p : OverlapPath) : 0 ≤ entropyFunctional p := by
  have h := le_iSup (fun h : FieldStep =>
    ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)) zeroField
  simpa only [entropyFunctional, fieldValue_zero, Real.cosh_zero, Real.log_one, fieldPairing_zero,
    zero_div, add_zero, EReal.coe_zero] using h

lemma spectralFunctional_constant (a : ℝ) (p : OverlapPath) :
    spectralFunctional (fun _ => a) p = a / 2 := by
  simp [spectralFunctional]
  ring

lemma integrable_spectral_composition (R : ℝ → ℝ) (hR : Continuous R)
    (p : OverlapPath) : Integrable (fun r => R (deficit p r)) pathMeasure := by
  change IntegrableOn (fun r => R (deficit p r)) (Set.Ioo (0 : ℝ) 1)
  exact ((hR.comp (continuous_deficit p)).continuousOn.integrableOn_Icc).mono_set
    Set.Ioo_subset_Icc_self

/-- Section 6's uniform comparison of spectral functionals. -/
lemma abs_spectralFunctional_sub_le (R Q : ℝ → ℝ) (hR : Continuous R) (hQ : Continuous Q)
    (δ : ℝ) (hδ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |R x - Q x| ≤ δ) (p : OverlapPath) :
    |spectralFunctional R p - spectralFunctional Q p| ≤ δ / 2 := by
  have hr : ∀ᵐ r ∂pathMeasure, r ∈ Set.Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have hi := norm_integral_le_of_norm_le_const (μ := pathMeasure)
    (f := fun r => R (deficit p r) - Q (deficit p r)) (C := δ) (by
      filter_upwards [hr] with r hr
      simpa only [Real.norm_eq_abs] using hδ _ (deficit_mem_unit p ⟨hr.1.le, hr.2.le⟩))
  have hib : |∫ r, R (deficit p r) - Q (deficit p r) ∂pathMeasure| ≤ δ := by
    simpa only [Real.norm_eq_abs, measureReal_def, pathMeasure_univ,
      ENNReal.toReal_one, mul_one] using hi
  rw [spectralFunctional, spectralFunctional, ← mul_sub,
    ← integral_sub (integrable_spectral_composition R hR p)
      (integrable_spectral_composition Q hQ p), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2 : ℝ) * δ := mul_le_mul_of_nonneg_left hib (by norm_num)
    _ = δ / 2 := by ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_FiniteVariationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finiteness and finite-entropy approximate minimizers of the finite-spectrum
variational problem. These justify taking the infimum in the pressure bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

theorem finiteSpectralFunctional_abs_le {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (K : ℝ) (heig : ∀ a, |eig a| ≤ K) (p : OverlapPath) :
    |spectralFunctional (finiteR ρ eig hρ hρsum) p| ≤ K / 2 := by
  have hb x : |finiteR ρ eig hρ hρsum x - 0| ≤ K := by
    simpa only [sub_zero] using abs_le.mpr (finiteR_mem_interval ρ eig hρ hρsum
      (fun a => (abs_le.mp (heig a)).1) (fun a => (abs_le.mp (heig a)).2) x)
  simpa only [spectralFunctional_constant, zero_div, sub_zero] using
    abs_spectralFunctional_sub_le (finiteR ρ eig hρ hρsum) (fun _ => 0)
      (continuous_finiteR ρ eig hρ hρsum) continuous_const K (fun x _ => hb x) p

theorem finiteVariational_mem_interval {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (K : ℝ) (heig : ∀ a, |eig a| ≤ K) :
    (-(K / 2) : ℝ) ≤ variationalFunctional (finiteR ρ eig hρ hρsum) ∧
      variationalFunctional (finiteR ρ eig hρ hρsum) ≤ (K / 2 : ℝ) := by
  constructor
  · apply le_iInf
    intro p
    have hs := (abs_le.mp (finiteSpectralFunctional_abs_le ρ eig hρ hρsum K heig p)).1
    have he : ((-(K / 2) : ℝ) : EReal) ≤
        (spectralFunctional (finiteR ρ eig hρ hρsum) p : EReal) := by exact_mod_cast hs
    have hadd := add_le_add (entropyFunctional_nonneg p)
      (le_rfl : (spectralFunctional (finiteR ρ eig hρ hρsum) p : EReal) ≤ _)
    exact he.trans (by simpa only [zero_add] using hadd)
  · let p := constantPath 0 (by constructor <;> norm_num)
    have hi := iInf_le (fun p : OverlapPath => entropyFunctional p +
      (spectralFunctional (finiteR ρ eig hρ hρsum) p : EReal)) p
    have hs := (abs_le.mp (finiteSpectralFunctional_abs_le ρ eig hρ hρsum K heig p)).2
    simp only [p, entropyFunctional_zero, zero_add] at hi
    exact hi.trans (by exact_mod_cast hs)

theorem finiteVariational_ne_top_bot_oai {ι : Type*} [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) :
    variationalFunctional (finiteR ρ eig hρ hρsum) ≠ ⊤ ∧
      variationalFunctional (finiteR ρ eig hρ hρsum) ≠ ⊥ := by
  let K := ∑ a, |eig a|
  have heig a : |eig a| ≤ K := Finset.single_le_sum
    (fun a _ => abs_nonneg (eig a)) (Finset.mem_univ a)
  have hb := finiteVariational_mem_interval ρ eig hρ hρsum K heig
  exact ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hb.2,
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hb.1⟩

end InvariantIsing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.InvariantIsing.finiteVariational_ne_top_bot_oai.{u_1} := @OAI.InvariantIsing.finiteVariational_ne_top_bot_oai.{u_1}
