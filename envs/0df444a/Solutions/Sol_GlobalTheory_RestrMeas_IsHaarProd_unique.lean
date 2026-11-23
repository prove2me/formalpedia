-- Prove2me | solution 1 for GlobalTheory.RestrMeas.IsHaarProd.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:44.510223+00:00
-- url     : https://prove2.me/submissions/19dde26c-16dd-43f1-a685-a662ed9cd10e

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
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}
variable [BorelSpace X] [∀ w, BorelSpace (Ya w)] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X]
variable [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)]
omit [∀ w, IsTopologicalGroup (Ya w)]
namespace GlobalTheory.RestrMeas
namespace IsHaarProd
theorem _root_.solution (hK : ∀ v, IsOpen (K v : Set (Yf v))) (hK' : ∀ v, IsCompact (K v : Set (Yf v)))
    (h : IsHaarProd pa pf K μa μf μ) (h' : IsHaarProd pa pf K μa μf μ') : μ = μ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨-, -, h3', h4'⟩ := h'
  obtain ⟨S, hS⟩ := exists_finset_of_eventually h4.1
  let C : ∀ w, TopologicalSpace.PositiveCompacts (Ya w) := fun w => Classical.arbitrary _
  have e := h4.2 S hS (fun w => C w) _ (fun w => (C w).isCompact.measurableSet) fun v _ => (hK v).measurableSet
  have e' := h4'.2 S hS (fun w => C w) _ (fun w => (C w).isCompact.measurableSet) fun v _ => (hK v).measurableSet
  have h0 : (∏ w, μa w (C w)) * ∏ v ∈ S, μf v (K v) ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => (measure_pos_of_nonempty_interior _ (C w).interior_nonempty).ne')
      (Finset.prod_ne_zero_iff.2 fun v _ => ((hK v).measure_pos _ ⟨1, one_mem _⟩).ne')
  have ht : (∏ w, μa w (C w)) * ∏ v ∈ S, μf v (K v) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.prod_ne_top fun w _ => (C w).isCompact.measure_lt_top.ne)
      (ENNReal.prod_ne_top fun v _ => (hK' v).measure_lt_top.ne)
  have hm := isMulLeftInvariant_eq_smul μ μ'
  rw [hm, Measure.smul_apply, e', ENNReal.smul_def, smul_eq_mul] at e
  have : (haarScalarFactor μ μ' : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj h0 ht).1 (e.trans (one_mul _).symm)
  rw [hm, ENNReal.coe_eq_one.1 this, one_smul]
end IsHaarProd
end GlobalTheory.RestrMeas
