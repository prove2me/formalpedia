-- Prove2me | solution 1 for GlobalTheory.KSp.setIntegral_addSubgroup_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:23:36.416257+00:00
-- url     : https://prove2.me/submissions/98217683-5041-4f08-aacf-6ae94a677d7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussIntegralQuadraticCharEventuallyConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology Classical
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution {X : Type} [AddCommGroup X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddRightInvariant] (H : AddSubgroup X)
    (hH : MeasurableSet (H : Set X)) {h : X} (hh : h ∈ H) (g : X → ℂ) :
    ∫ x in (H : Set X), g (x + h) ∂μ = ∫ x in (H : Set X), g x ∂μ := by
  rw [← integral_indicator hH, ← integral_indicator hH]
  have key : (Set.indicator (H : Set X) fun x => g (x + h)) =
      fun x => Set.indicator (H : Set X) g (x + h) := by
    funext x
    by_cases hx : x ∈ H
    · have hx' : x + h ∈ H := H.add_mem hx hh
      simp [Set.indicator_apply, hx, hx']
    · have hx' : x + h ∉ H := fun h' => hx (by simpa using H.sub_mem h' hh)
      simp [Set.indicator_apply, hx, hx']
  rw [key, integral_add_right_eq_self (Set.indicator (H : Set X) g) h]
end GlobalTheory.KSp
