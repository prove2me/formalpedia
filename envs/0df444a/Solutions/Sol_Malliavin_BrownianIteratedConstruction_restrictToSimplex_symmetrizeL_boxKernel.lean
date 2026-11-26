-- Prove2me | solution 1 for Malliavin.BrownianIteratedConstruction.restrictToSimplex_symmetrizeL_boxKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:19:57.402598+00:00
-- url     : https://prove2.me/submissions/8feebe61-10b2-47d8-aed0-733d674a6194

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Definitions.Def_Malliavin_BrownianMultipleIntegralBox
import Theorems.Thm_Malliavin_coeFn_symmetrizeL
import Theorems.Thm_Malliavin_measurableSet_simplex
import Theorems.Thm_Malliavin_mem_simplex
import Theorems.Thm_Malliavin_perm_eq_of_strictMono_comp
import Theorems.Thm_Malliavin_symmetrize_congr_ae


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin Malliavin.BrownianIteratedConstruction
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}
omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [MeasurableSpace W]
    [BorelSpace W] [SecondCountableTopology W] [IsGaussian P]
namespace Malliavin.BrownianIteratedConstruction
theorem _root_.solution {n : ℕ} (a : OrderedBoxIndex n) :
    restrictToSimplex n
        (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 (boxKernel a.u a.v)) =
      ((n.factorial : ℝ)⁻¹) • orderedBoxSimplexKernel a := by
  apply Lp.ext
  have hbox :
      (boxKernel a.u a.v : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
        (orderedBox a.u a.v).indicator fun _ ↦ (1 : ℝ) := by
    exact indicatorConstLp_coeFn
  have hsymm :
      (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2
          (boxKernel a.u a.v) : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
        symmetrize n ((orderedBox a.u a.v).indicator fun _ ↦ (1 : ℝ)) :=
    (coeFn_symmetrizeL (E := ℝ) (μ := nonnegativeLebesgueMeasure) n 2
      (boxKernel a.u a.v)).trans
        (symmetrize_congr_ae (μ := nonnegativeLebesgueMeasure) hbox)
  have hord :
      (orderedBoxSimplexKernel a : (Fin n → ℝ≥0) → ℝ) =ᵐ[
          (iteratedKernelMeasure n).restrict (simplex ℝ≥0 n)]
        (orderedBox a.u a.v).indicator fun _ ↦ (1 : ℝ) := by
    exact indicatorConstLp_coeFn
  filter_upwards [ae_restrict_mem (measurableSet_simplex n),
    restrictToSimplex_ae n
      (symmetrizeL ℝ (μ := nonnegativeLebesgueMeasure) n 2 (boxKernel a.u a.v)),
    ae_restrict_of_ae hsymm,
    Lp.coeFn_smul ((n.factorial : ℝ)⁻¹) (orderedBoxSimplexKernel a),
    hord]
      with t ht hrestrict hsymm_t hsmul hindicator
  rw [hrestrict, hsymm_t, hsmul, Pi.smul_apply, hindicator]
  rw [symmetrize_apply]
  congr 1
  apply Finset.sum_eq_single 1
  · intro σ _hσmem hσ
    rw [Set.indicator_of_notMem]
    intro hmem
    have hσsimplex : t ∘ σ ∈ simplex ℝ≥0 n := orderedBox_subset_simplex a hmem
    have hEq : σ = 1 :=
      perm_eq_of_strictMono_comp (mem_simplex.mp ht).injective
        (mem_simplex.mp hσsimplex) (by
          have ht_one : t ∘ (1 : Equiv.Perm (Fin n)) = t := by
            funext i
            rfl
          rw [ht_one]
          exact mem_simplex.mp ht)
    exact hσ hEq
  · intro h
    exact (h (Finset.mem_univ (1 : Equiv.Perm (Fin n)))).elim
end Malliavin.BrownianIteratedConstruction
