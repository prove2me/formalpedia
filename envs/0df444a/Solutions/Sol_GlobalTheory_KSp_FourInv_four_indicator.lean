-- Prove2me | solution 1 for GlobalTheory.KSp.FourInv.four_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:40:14.001826+00:00
-- url     : https://prove2.me/submissions/92ed077c-5b76-414c-bdc0-8d921cf56607

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect
import Theorems.Thm_GlobalTheory_KSp_FourInv_indicator_invariant
import Theorems.Thm_GlobalTheory_KSp_FourInv_four_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.FourInv
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}
variable [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
namespace GlobalTheory.KSp.FourInv
theorem _root_.solution (he : IsPair e) (L : AddSubgroup X) (ho : IsOpen (L : Set X)) (x : X) :
    four μ e ((L : Set X).indicator fun _ => (1 : ℂ)) x =
      (ann he L : Set X).indicator (fun _ => (μ.real (L : Set X) : ℂ)) x := by
  by_cases hx : x ∈ (ann he L : Set X)
  · rw [Set.indicator_of_mem hx]
    have hx' : ∀ y ∈ (L : Set X), e y x = 1 := hx
    simp only [four]
    have h : (fun z => e x z * (L : Set X).indicator (fun _ => (1 : ℂ)) z) =
        (L : Set X).indicator (fun _ => (1 : ℂ)) := by
      ext z
      by_cases hz : z ∈ (L : Set X)
      · rw [Set.indicator_of_mem hz, mul_one, he.symm, hx' z hz]
      · rw [Set.indicator_of_notMem hz, mul_zero]
    rw [h, integral_indicator_const _ ho.measurableSet]
    simp
  · rw [Set.indicator_of_notMem hx]
    exact four_eq_zero μ he (indicator_invariant L 1) hx
end GlobalTheory.KSp.FourInv
