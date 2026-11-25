-- Prove2me | solution 1 for GlobalTheory.DegAsm.DatMove.commonIsotropic_le_flagPairDefinitePartLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:21:14.670705+00:00
-- url     : https://prove2.me/submissions/6b5b3dad-8931-498d-953d-ffb447f86793

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EmbeddedDatumInvariantUnderUnipotent
import Theorems.Thm_GlobalTheory_DegAsm_DatMove_herm_zero
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.DatMove
open AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)
variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]
namespace GlobalTheory.DegAsm.DatMove
theorem _root_.solution {F G : FlagD H r} (hI : ∀ x ∈ II F G, ∀ w ∈ V0 F G, H.B w x = 0) (Λ : Submodule R V)
    {x : V} (hx : x ∈ II F G) : x ∈ flagPairDefinitePartLattice F G Λ := by
  refine ⟨⟨?_, Submodule.mem_sup_right hx.1⟩, ?_⟩
  · exact (mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w (Submodule.mem_sup_left hw))
  · exact (mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w hw)
end GlobalTheory.DegAsm.DatMove
