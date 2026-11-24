-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsHaarProd.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:11.891821+00:00
-- url     : https://prove2.me/submissions/908e81ff-f32f-4e01-b276-38bbc1bae4de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
import Theorems.Thm_GlobalTheory_RestrMeas_IsCylProd_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}
variable [BorelSpace X] [∀ w, BorelSpace (Ya w)] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X]
omit [BorelSpace X] [∀ w, BorelSpace (Ya w)] [IsTopologicalGroup X]
namespace GlobalTheory.RestrMeas
namespace IsHaarProd
theorem _root_.solution (h : IsHaarProd pa pf K μa μf μ) (hK : ∀ v, IsOpen (K v : Set (Yf v))) (c : W → ℝ≥0)
    (d : V → ℝ≥0) (hc : ∀ w, c w ≠ 0) (hd0 : ∀ v, d v ≠ 0) (T : Finset V) (hd : ∀ v ∉ T, d v = 1) :
    IsHaarProd pa pf K (fun w => c w • μa w) (fun v => d v • μf v) (((∏ w, c w) * ∏ v ∈ T, d v) • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun w => IsHaarMeasure.nnreal_smul _ (hc w), fun v => IsHaarMeasure.nnreal_smul _ (hd0 v),
    IsHaarMeasure.nnreal_smul _ (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => hc w)
      (Finset.prod_ne_zero_iff.2 fun v _ => hd0 v)), ?_⟩
  have := h4.smul (fun v => (hK v).measurableSet) (fun w => c w) (fun v => d v) T fun v hv => by simp [hd v hv]
  simpa only [ENNReal.smul_def, ENNReal.coe_mul, ENNReal.ofNNReal_finsetProd] using this
end IsHaarProd
end GlobalTheory.RestrMeas
