-- Prove2me | solution 1 for GlobalTheory.ae_eval_circleMap_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:17:35.053317+00:00
-- url     : https://prove2.me/submissions/788a017d-6a6f-4474-9f47-9e49881328a8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralLogNormLeHalfLogIntegralSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AeEvalCircleMapNeZero
import Theorems.Thm_GlobalTheory_coe_sphereRotation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_sphereRotation
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open MeasureTheory Metric NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hcont : Continuous fun (x : Fin (m + 1) → ℝ) =>
        MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f :=
      (MvPolynomial.continuous_eval f).comp
        (continuous_pi fun i => (continuous_circleMap 0 1).comp (continuous_apply i))
    have hmeas : MeasurableSet {z : ℝ × (Fin m → ℝ) |
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0} :=
      (hcont.measurable.comp e.symm.measurable) (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℝ × (Fin m → ℝ))),
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s =>
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm (y, s) i)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      set w : Fin m → ℂ := fun i => circleMap 0 1 (s i) with hw
      have hQ : Polynomial.map (MvPolynomial.eval w) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => Polynomial.coeff q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval w) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := (hfin.countable.preimage_circleMap 0 one_ne_zero).measure_zero
        (volume : Measure ℝ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (fun i => circleMap 0 1 ((e.symm (y, s) : Fin (m + 1) → ℝ) i)) =
          Fin.cons (circleMap 0 1 y) w := by
        have : (e.symm (y, s) : Fin (m + 1) → ℝ) = Fin.cons y s := by
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
        rw [this]
        funext i
        cases i using Fin.cases <;> simp [hw]
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx
end GlobalTheory
