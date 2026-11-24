-- Prove2me | solution 1 for GlobalTheory.UnRep.Compare.splitPl_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:58:10.548866+00:00
-- url     : https://prove2.me/submissions/236150ca-522c-48cf-8252-13df66c93dd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_SupportedAtSplit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSplitPlaceOfSplitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_isSplitPlace_of_splitPl
import Theorems.Thm_GlobalTheory_UnRep_Compare_moved_of_not_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.Compare
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceUnitaryEvaluation
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.UnRep.Compare
theorem _root_.solution (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (v : HeightOneSpectrum (𝓞 F)) : SplitPl c v ↔ IsSplitPlace E v := by
  refine ⟨isSplitPlace_of_splitPl c, ?_⟩
  rintro ⟨w, w', hne, hw, hw', h, h'⟩
  by_cases hle : w ≤ w'
  · exact ⟨w, hw, h, moved_of_not_le c h2 hc hw (h'.trans h.symm) fun h => hne (le_antisymm hle h)⟩
  · exact ⟨w', hw', h', moved_of_not_le c h2 hc hw' (h.trans h'.symm) hle⟩
end GlobalTheory.UnRep.Compare
