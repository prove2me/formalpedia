-- Prove2me | solution 1 for Malliavin.mderivClosure_comp_pi_eq_sum_boundedSMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:37.618606+00:00
-- url     : https://prove2.me/submissions/5d993f51-3f07-47ce-9a7c-d1d2c00b8daa

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule
import Theorems.Thm_Malliavin_coeFn_boundedSMul


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
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 P}
    (hF : ∀ i, F i ∈ domD12 P) :
    mderivClosure P ((memLp_comp_pi P hf hK F).toLp _) =
      ∑ i, boundedSMul (G := fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1))
        (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable (C := K)
        (fun _ ↦ abs_fderiv_pi_single_le hK _ i) (mderivClosure P (F i)) := by
  rw [(comp_pi_mem_domD12 P hf hK hF).2]
  apply Lp.ext
  have h2 := ae_all_iff.2 fun i ↦ coeFn_boundedSMul
    (G := fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1))
    (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable (C := K)
    (fun x ↦ abs_fderiv_pi_single_le hK _ i) (mderivClosure P (F i))
  filter_upwards [MemLp.coeFn_toLp (memLp_grad_smul P hf hK
      (fun i ↦ Lp.aestronglyMeasurable (F i)) fun i ↦ mderivClosure P (F i)),
    Lp.coeFn_finsetSum Finset.univ (fun i ↦ boundedSMul
      (G := fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1))
      (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable (C := K)
      (fun x ↦ abs_fderiv_pi_single_le hK _ i) (mderivClosure P (F i))), h2] with x h1 h2 h3
  rw [h1, h2, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ (h3 i).symm
end Malliavin
