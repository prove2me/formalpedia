-- Prove2me | solution 1 for Malliavin.fubiniLift_boundedSMul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:23.942106+00:00
-- url     : https://prove2.me/submissions/d57ddc5f-2ae1-4862-aa49-f25c288f716b

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall
import Definitions.Def_Malliavin_FubiniLift
import Theorems.Thm_Malliavin_coeFn_smulLp
import Theorems.Thm_Malliavin_fubiniLift_smulLp
import Theorems.Thm_Malliavin_coeFn_boundedSMul

set_option autoImplicit false
open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3
open Malliavin
variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
  [SFinite μ] [SFinite ν]
namespace Malliavin
theorem _root_.solution {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp (Lp ℝ 2 ν) 2 μ) :
    fubiniLift (boundedSMul hG hC U) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := ν) hG) (fun p ↦ hC p.2) (fubiniLift U) := by
  refine Lp.induction ENNReal.ofNat_ne_top (fun U : Lp (Lp ℝ 2 ν) 2 μ ↦
    fubiniLift (boundedSMul hG hC U) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := ν) hG) (fun p ↦ hC p.2) (fubiniLift U))
    ?_ ?_ ?_ U
  · intro g s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    change fubiniLift (boundedSMul hG hC (indicatorLp ⟨s, hs, hμs.ne⟩ g)) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := ν) hG) (fun p ↦ hC p.2)
        (fubiniLift (indicatorLp ⟨s, hs, hμs.ne⟩ g))
    rw [fubiniLift_indicatorLp]
    have h1 : boundedSMul hG hC (indicatorLp ⟨s, hs, hμs.ne⟩ g) =
        smulLp g (boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ))) := by
      apply Lp.ext
      filter_upwards [coeFn_boundedSMul hG hC (indicatorLp ⟨s, hs, hμs.ne⟩ g),
        coeFn_smulLp g (boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ))),
        coeFn_boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ)),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := g),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))]
        with x h1 h2 h3 h4 h5
      rw [h1, h2, h3, indicatorLp, h4, h5]
      by_cases hx : x ∈ s <;> simp [hx]
    rw [h1, fubiniLift_smulLp]
    apply Lp.ext
    filter_upwards [coeFn_tensor g (boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ))),
      coeFn_boundedSMul (aestronglyMeasurable_comp_snd (ν := ν) hG) (fun p ↦ hC p.2)
        (tensorLp ⟨s, hs, hμs.ne⟩ g),
      coeFn_tensorLp ⟨s, hs, hμs.ne⟩ g,
      Measure.quasiMeasurePreserving_snd.ae_eq_comp
        (coeFn_boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ))),
      Measure.quasiMeasurePreserving_snd.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ)))]
      with p h1 h2 h3 h4 h5
    rw [h1, h2, h3]
    simp only [Function.comp_apply] at h4 h5
    rw [h4, h5, smul_eq_mul, smul_eq_mul]
    by_cases hp : p.2 ∈ s <;> simp [hp, mul_comm]
  · intro U V _ _ _ hU hV
    rw [map_add, map_add, hU, hV, map_add, map_add]
  · exact isClosed_eq (fubiniLift.continuous.comp (boundedSMul hG hC).continuous)
      ((boundedSMul _ _).continuous.comp fubiniLift.continuous)
end Malliavin
