-- Prove2me | solution 1 for GlobalTheory.DegAsm.DatMove.sup_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:14:22.469882+00:00
-- url     : https://prove2.me/submissions/40dbdfb3-a974-42e3-83c0-989877fa024b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotent
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
    {A B A' B' : Submodule R M} (h : ∀ y, t y ∈ A ↔ y ∈ B) (h' : ∀ y, t y ∈ A' ↔ y ∈ B') (y : M) :
    t y ∈ A ⊔ A' ↔ y ∈ B ⊔ B' := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨t.symm a, (h _).1 (by simpa using ha), t.symm b, (h' _).1 (by simpa using hb), ?_⟩
    apply t.injective
    simp [hab]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨t a, (h _).2 ha, t b, (h' _).2 hb, by simp⟩
end GlobalTheory.DegAsm.DatMove
