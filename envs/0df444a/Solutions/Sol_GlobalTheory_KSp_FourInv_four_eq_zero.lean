-- Prove2me | solution 1 for GlobalTheory.KSp.FourInv.four_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:26:12.73647+00:00
-- url     : https://prove2.me/submissions/21754d22-a23c-49f8-9bbd-1d8613625fbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect

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
theorem _root_.solution (he : IsPair e) {M : Set X} {f : X → ℂ}
    (hs : ∀ t ∈ M, ∀ x, f (x + t) = f x) {y : X} (hy : y ∉ ann he M) : four μ e f y = 0 := by
  have hy' : ¬ ∀ t ∈ M, e t y = 1 := hy
  simp only [not_forall] at hy'
  obtain ⟨t, ht, hne⟩ := hy'
  have hne' : e y t ≠ 1 := by rwa [he.symm]
  have key : four μ e f y = e y t * four μ e f y := by
    simp only [four]
    calc ∫ z, e y z * f z ∂μ = ∫ z, e y (t + z) * f (t + z) ∂μ :=
          (integral_add_left_eq_self (fun z => e y z * f z) t).symm
      _ = ∫ z, e y t * (e y z * f z) ∂μ := by
          congr 1; ext z
          rw [add_right he, add_comm t z, hs t ht z]; ring
      _ = e y t * ∫ z, e y z * f z ∂μ := integral_const_mul _ _
  by_contra h
  exact hne' (mul_right_cancel₀ h (key.symm.trans (one_mul _).symm))
end GlobalTheory.KSp.FourInv
