-- Prove2me | solution 1 for GlobalTheory.KSp.WeilFormula.setIntegral_addSubgroup_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:51:57.482453+00:00
-- url     : https://prove2.me/submissions/68d8b0e9-0e85-4130-9981-d3be5546ff95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformMemSchwartzBruhatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilFormulaFourierQuadraticCharacter

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
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.WeilFormula
namespace GlobalTheory.KSp.WeilFormula
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (g : V → ℂ)
    {t : V} (ht : t ∈ L) :
    ∫ z in (L : Set V), g (z + t) ∂μ = ∫ z in (L : Set V), g z ∂μ := by
  simp_rw [add_comm _ t]
  rw [← integral_indicator hLo.measurableSet, ← integral_indicator hLo.measurableSet,
    ← integral_add_left_eq_self (μ := μ) ((L : Set V).indicator g) t]
  congr 1
  funext z
  by_cases hz : z ∈ L
  · rw [Set.indicator_of_mem (show z ∈ (L : Set V) from hz),
      Set.indicator_of_mem (show t + z ∈ (L : Set V) from L.add_mem ht hz)]
  · have hz' : t + z ∉ L := fun h => hz ((L.add_mem_cancel_left ht).1 h)
    rw [Set.indicator_of_notMem (show z ∉ (L : Set V) from hz),
      Set.indicator_of_notMem (show t + z ∉ (L : Set V) from hz')]
end GlobalTheory.KSp.WeilFormula
