-- Prove2me | solution 1 for GlobalTheory.DegAsm.IndIsom.mem_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:55.523271+00:00
-- url     : https://prove2.me/submissions/1ca44925-aa29-415e-b486-38e3512b0875

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDefiniteSpaceIsometryOfAdaptedPair
import Theorems.Thm_GlobalTheory_DegAsm_IndIsom_map_mem

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
open Formalism.HermitianLatticeCounting.P
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.IndIsom
variable {K V W : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.IndIsom
theorem _root_.solution {F G : FlagD H r} {γ : V ≃ₗ[K] V} (hG : ∀ a, G.e a = γ (F.e a)) {x : V} (hx : γ x ∈ G.X) :
    x ∈ F.X := by
  have h := map_mem (F := G) (G := F) (γ := γ.symm)
    (fun a => by rw [hG a, LinearEquiv.symm_apply_apply]) hx
  rwa [LinearEquiv.symm_apply_apply] at h
end GlobalTheory.DegAsm.IndIsom
