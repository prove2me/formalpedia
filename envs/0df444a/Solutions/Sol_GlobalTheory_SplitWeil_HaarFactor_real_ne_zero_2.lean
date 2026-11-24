-- Prove2me | solution 2 for GlobalTheory.SplitWeil.HaarFactor.real_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:24:18.035102+00:00
-- url     : https://prove2.me/submissions/0d23ded5-2d49-4da4-8f03-ab5d9b43ed96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TranslationInvariantSchwartzBruhatMapFactorsInte

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.HaarFactor
variable {X₀ A : Type*} [TopologicalSpace X₀] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [T2Space X₀] [T2Space A]
variable [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil.HaarFactor
theorem _root_.solution {U : AddSubgroup A} (hUo : IsOpen (U : Set A)) (hUc : IsCompact (U : Set A)) :
    (μ.real (U : Set A) : ℂ) ≠ 0 := by
  have h1 : 0 < μ (U : Set A) := hUo.measure_pos μ ⟨0, U.zero_mem⟩
  have h2 : μ (U : Set A) ≠ ⊤ := hUc.measure_lt_top.ne
  exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
end GlobalTheory.SplitWeil.HaarFactor
