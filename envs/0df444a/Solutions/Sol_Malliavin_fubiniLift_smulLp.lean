-- Prove2me | solution 1 for Malliavin.fubiniLift_smulLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:49.324183+00:00
-- url     : https://prove2.me/submissions/c6af99bb-40b3-4787-890a-25cde9913241

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_FubiniLift
import Theorems.Thm_Malliavin_smulLp_indicatorConstLp

set_option autoImplicit false
open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3
open Malliavin
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Malliavin
theorem _root_.solution [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    fubiniLift (smulLp g G) = tensor g G := by
  refine Lp.induction ENNReal.ofNat_ne_top
    (fun G : Lp ℝ 2 μ ↦ fubiniLift (smulLp g G) = tensor g G) ?_ ?_ ?_ G
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, smulLp_indicatorConstLp]
    change fubiniLift (indicatorLp ⟨s, hs, hμs.ne⟩ (c • g)) = _
    rw [fubiniLift_indicatorLp]
    apply Lp.ext
    filter_upwards [coeFn_tensorLp ⟨s, hs, hμs.ne⟩ (c • g),
      coeFn_tensor g (indicatorConstLp 2 hs hμs.ne c),
      Measure.quasiMeasurePreserving_snd.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := c)),
      Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_smul c g)] with p h1 h2 h3 h4
    rw [h1, h2]
    simp only [Function.comp_apply] at h3 h4
    rw [h3, h4, Pi.smul_apply, smul_eq_mul]
    by_cases hp : p.2 ∈ s <;> simp [hp, mul_comm]
  · intro G G' _ _ _ hG hG'
    rw [map_add, map_add, hG, hG', tensor_add]
  · exact isClosed_eq (fubiniLift.continuous.comp (smulLp g).continuous) (tensorL g).continuous
end Malliavin
