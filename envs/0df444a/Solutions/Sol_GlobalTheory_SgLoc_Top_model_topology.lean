-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.model_topology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:41:18.396623+00:00
-- url     : https://prove2.me/submissions/d4d412a6-f2b9-4e08-a812-a577432a3118

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Theorems.Thm_GlobalTheory_SgLoc_Top_localField_secondCountable
import Theorems.Thm_GlobalTheory_SgLoc_Top_t2Space_of_isNonarchimedeanLocalField_flag_measures
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_exists_coords
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_homeo
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_topRing
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_integers
import Theorems.Thm_GlobalTheory_SgLoc_Top_R_le_O
import Theorems.Thm_GlobalTheory_SgLoc_Top_isOpen_R

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [MeasurableSpace E]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type}
    [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK →
    IsTopologicalRing E ∧ T2Space E ∧ LocallyCompactSpace E ∧ SecondCountableTopology E ∧
    ContinuousSMul F E ∧ IsCompact (M.R : Set E) ∧ IsOpen (M.R : Set E) ∧
    IsCompact (M.L.O : Set E) ∧ IsOpen (M.L.O : Set E) ∧ M.R ≤ M.L.O := by
  intro F _ _ _ E _ _ _ _ M hM
  have := hM.loc
  have := hM.char0
  obtain ⟨ψ, -, -, -, -⟩ := locE_exists_coords M.L
  obtain ⟨h, -⟩ := locE_homeo M.L ψ
  have hTR := locE_topRing M.L
  have := t2Space_of_isNonarchimedeanLocalField_flag_measures F
  have := localField_secondCountable F
  have := M.L.top
  have hRo := isOpen_R M
  have hO := locE_integers M.L
  have hRc : IsClosed (M.R : Set E) := AddSubgroup.isClosed_of_isOpen M.R.toAddSubgroup hRo
  exact ⟨hTR, h.symm.isEmbedding.t2Space, h.symm.isClosedEmbedding.locallyCompactSpace,
    h.symm.isEmbedding.secondCountableTopology, inferInstance,
    hO.1.of_isClosed_subset hRc (R_le_O M), hRo, hO.1, hO.2, R_le_O M⟩
end GlobalTheory.SgLoc.Top
