-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsCylProd.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:27.834394+00:00
-- url     : https://prove2.me/submissions/0fa72ab2-499d-4c16-958b-c4ea53daa97b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually

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
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type}
variable {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v} {K K' : ∀ v, Set (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}
namespace GlobalTheory.RestrMeas
namespace IsCylProd
theorem _root_.solution (h : IsCylProd pa pf K μa μf μ) (hK : ∀ v, MeasurableSet (K v)) (c : W → ℝ≥0∞)
    (d : V → ℝ≥0∞) (T : Finset V) (hd : ∀ v ∉ T, d v = 1) :
    IsCylProd pa pf K (fun w => c w • μa w) (fun v => d v • μf v) (((∏ w, c w) * ∏ v ∈ T, d v) • μ) := by
  classical
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually h.1
  refine isCylProd_of_large hK (S₀ ∪ T) (fun v hv => ?_) (fun _ _ => rfl) fun S hs A B hA hB => ?_
  · rw [Finset.notMem_union] at hv
    rw [hd v hv.2, one_smul, hS v hv.1]
  · rw [Finset.prod_subset (Finset.subset_union_right.trans hs) fun v _ hv => hd v hv]
    simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
    rw [h.2 S (fun v hv => hS v fun h' => hv (hs (Finset.mem_union_left _ h'))) A B hA hB, mul_mul_mul_comm]
end IsCylProd
end GlobalTheory.RestrMeas
