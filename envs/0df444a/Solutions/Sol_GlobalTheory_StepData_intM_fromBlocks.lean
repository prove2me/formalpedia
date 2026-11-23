-- Prove2me | solution 1 for GlobalTheory.StepData.intM_fromBlocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:12.859086+00:00
-- url     : https://prove2.me/submissions/ec8c67c7-cc7c-4a85-902c-2d134dcfa8cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution {a' t' : Type*} {A : Matrix a a' k} {B : Matrix a t' k} {C : Matrix t a' k} {D : Matrix t t' k} :
    IntM (fromBlocks A B C D) ↔ IntM A ∧ IntM B ∧ IntM C ∧ IntM D :=
  ⟨fun h => ⟨fun i j => h (.inl i) (.inl j), fun i j => h (.inl i) (.inr j), fun i j => h (.inr i) (.inl j),
    fun i j => h (.inr i) (.inr j)⟩, by
    rintro ⟨h1, h2, h3, h4⟩ (i | i) (j | j)
    exacts [h1 i j, h2 i j, h3 i j, h4 i j]⟩
end GlobalTheory.StepData
