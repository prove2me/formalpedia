-- Prove2me | solution 1 for GlobalTheory.HL.FrameTuple.det_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:42:03.393744+00:00
-- url     : https://prove2.me/submissions/ada64adf-e7df-45bf-bbc6-a5b9b2b095c3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNondegenerateTupleComplementFixer
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameTuple
variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {m : ℕ}
namespace GlobalTheory.HL.FrameTuple
theorem _root_.solution (s : Matrix (Fin m) (Fin m) E) (h0 : ∀ i j, j < i → s i j = 0) (h1 : ∀ i, s i i = 1) :
    s.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j hij => h0 i j hij)]
  simp [h1]
end GlobalTheory.HL.FrameTuple
