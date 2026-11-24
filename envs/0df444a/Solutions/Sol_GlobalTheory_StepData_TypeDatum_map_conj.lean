-- Prove2me | solution 1 for GlobalTheory.StepData.TypeDatum.map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:44.455305+00:00
-- url     : https://prove2.me/submissions/786a5224-31b4-48d6-afd8-a9b345cf28df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_isOpen
import Theorems.Thm_GlobalTheory_StepData_TypeDatum_isCompact
import Theorems.Thm_GlobalTheory_StepData_isOpen_isCompact_conj

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
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k]
variable {ι ι' Y Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
variable [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.StepData
namespace TypeDatum
theorem _root_.solution (P : TypeDatum k ι) (F : LatFrame k ι Y) :
    IsOpen ((P.toLevel.map F.conj).J : Set (GL Y k)) ∧ IsCompact ((P.toLevel.map F.conj).J : Set (GL Y k)) ∧
      (P.toLevel.map F.conj).J ≤ stabLat F.bas := by
  have e : (P.toLevel.map F.conj).J = (P.reindex F.ord).J.comap (MulAut.conj F.bas⁻¹).toMonoidHom := by
    ext h; exact Iff.rfl
  rw [e]
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj F.bas (P.reindex F.ord).isOpen (P.reindex F.ord).isCompact
  exact ⟨h1, h2, Subgroup.comap_mono (P.reindex F.ord).le_KO⟩
end TypeDatum
end GlobalTheory.StepData
