-- Prove2me | solution 1 for GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:21.031213+00:00
-- url     : https://prove2.me/submissions/210c3577-9281-47a8-81a3-db7bbc35f939

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.AbsInv
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
open MeasureTheory Filter Topology Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
namespace GlobalTheory.JR.AbsInv
namespace _root_.GlobalTheory.JR.AbsInv
theorem _root_.solution (μ : Measure V) [μ.IsAddHaarMeasure] (g : V → ℂ) (m : V) (c : ℂ)
    (hc : c ≠ 1) (h : ∀ x, g (x + m) = c * g x) : ∫ x, g x ∂μ = 0 := by
  have h1 : ∫ x, g x ∂μ = c * ∫ x, g x ∂μ := by
    calc ∫ x, g x ∂μ = ∫ x, g (x + m) ∂μ := (integral_add_right_eq_self g m).symm
      _ = ∫ x, c * g x ∂μ := integral_congr_ae (Eventually.of_forall fun x => h x)
      _ = c * ∫ x, g x ∂μ := integral_const_mul c _
  have h2 : (1 - c) * ∫ x, g x ∂μ = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.2 h1
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hc.symm)
end _root_.GlobalTheory.JR.AbsInv
end GlobalTheory.JR.AbsInv
