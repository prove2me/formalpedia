-- Prove2me | solution 1 for GlobalTheory.SplitWeil.volGL_haar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:16:45.871102+00:00
-- url     : https://prove2.me/submissions/3aba77c5-35fb-4126-a3b7-77184c448312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Theorems.Thm_GlobalTheory_SplitWeil_isHaarMeasure_volGL
import Theorems.Thm_GlobalTheory_StepData_isOpen_KOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
  (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SplitWeil
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure], BorelSpace (GL n k) ∧ LocallyCompactSpace (GL n k) ∧ SecondCountableTopology (GL n k) ∧ IsCompact (KO k n : Set (GL n k)) ∧ IsOpen (KO k n : Set (GL n k)) ∧ IsOpen (KOne k n : Set (GL n k)) ∧ (volGL ν n).IsHaarMeasure ∧ (volGL ν n).IsMulRightInvariant :=
  fun _ _ _ _ _ _ _ n _ _ ν _ =>
    haveI := isHaarMeasure_volGL (n := n) ν
    ⟨SplitFlip.borel_GL, SplitFlip.locallyCompact_GL, SplitFlip.secondCountable_GL, SplitFlip.isCompact_KO,
      SplitFlip.isOpen_KO, StepData.isOpen_KOne, this, SplitFlip.isMulRightInvariant_of_haar _⟩
end GlobalTheory.SplitWeil
