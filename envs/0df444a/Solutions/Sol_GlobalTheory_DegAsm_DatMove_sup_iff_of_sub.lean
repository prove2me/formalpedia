-- Prove2me | solution 1 for GlobalTheory.DegAsm.DatMove.sup_iff_of_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:35:37.397919+00:00
-- url     : https://prove2.me/submissions/68efbb29-af67-4207-b492-eecb7b8433fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotent
import Theorems.Thm_GlobalTheory_DegAsm_DatMove_sup_iff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.DatMove
open AdaptInv
namespace GlobalTheory.DegAsm.DatMove
theorem _root_.solution {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (t : M ≃+ M)
    {A B C : Submodule R M} (h : ∀ y, t y ∈ A ↔ y ∈ B) (h' : ∀ y, t y ∈ C ↔ y ∈ C) {y : M}
    (hy : t y - y ∈ C) : y ∈ A ⊔ C ↔ y ∈ B ⊔ C := by
  rw [← sup_iff t h h' y]
  have h1 : t y - y ∈ A ⊔ C := Submodule.mem_sup_right hy
  rw [← Submodule.add_mem_iff_right _ h1]
  simp
end GlobalTheory.DegAsm.DatMove
