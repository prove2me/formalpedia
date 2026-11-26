-- Prove2me | solution 1 for Malliavin.mderivClosure_comp_pi_space
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:41.869718+00:00
-- url     : https://prove2.me/submissions/ee315c90-938b-45f9-83e9-b25fda1d2b53

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_coeFn_smulLp
import Theorems.Thm_Malliavin_coe_space_mem_domD12
import Theorems.Thm_Malliavin_constLp_apply


set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  {φ : ℝ → ℝ} {K : ℝ≥0}
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (h : Fin n → Space P) :
    mderivClosure P ((memLp_comp_pi P hf hK fun i ↦ (h i : Lp ℝ 2 P)).toLp _) =
      ∑ i, smulLp (h i) ((memLp_fderiv_pi_comp hf hK (fun i ↦ (h i : Lp ℝ 2 P)) i).toLp _) := by
  rw [(comp_pi_mem_domD12 P hf hK fun i ↦ (coe_space_mem_domD12 P (h i)).1).2]
  have hc : ∀ i, (mderivClosure P (h i : Lp ℝ 2 P) : W → Space P) =ᵐ[P] fun _ ↦ h i := fun i ↦ by
    rw [(coe_space_mem_domD12 P (h i)).2, constLp_apply]
    exact Lp.coeFn_const 2 P (h i)
  apply Lp.ext
  have h4 := ae_all_iff.2 fun i ↦ coeFn_smulLp (h i)
    ((memLp_fderiv_pi_comp hf hK (fun i ↦ (h i : Lp ℝ 2 P)) i).toLp _)
  have h5 := ae_all_iff.2 fun i ↦
    MemLp.coeFn_toLp (memLp_fderiv_pi_comp hf hK (fun i ↦ (h i : Lp ℝ 2 P)) i)
  filter_upwards [MemLp.coeFn_toLp (memLp_grad_smul P hf hK
      (fun i ↦ Lp.aestronglyMeasurable (h i : Lp ℝ 2 P)) fun i ↦ mderivClosure P (h i : Lp ℝ 2 P)),
    Lp.coeFn_finsetSum Finset.univ (fun i ↦ smulLp (h i)
      ((memLp_fderiv_pi_comp hf hK (fun i ↦ (h i : Lp ℝ 2 P)) i).toLp _)),
    ae_all_iff.2 hc, h4, h5] with x h1 h2 h3 h4 h5
  rw [h1, h2, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h4 i, h5 i, h3 i]
end Malliavin
