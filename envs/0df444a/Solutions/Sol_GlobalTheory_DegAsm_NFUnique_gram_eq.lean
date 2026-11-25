-- Prove2me | solution 1 for GlobalTheory.DegAsm.NFUnique.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:36:52.486836+00:00
-- url     : https://prove2.me/submissions/6dfa6e53-de76-4c0d-9c57-e01ba2c1db49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0


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
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegAsm.NFUnique
theorem _root_.solution {F G : FlagD H r} (hT : F.T = G.T) (a b : Fin (r + 1)) :
    H.B (F.e a) (F.e b) = H.B (G.e a) (G.e b) := by
  refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
  · rw [F.zz, G.zz, hT]
  · rw [B_swap0 H (F.zperp b), B_swap0 H (G.zperp b)]
  · rw [F.zperp, G.zperp]
  · rw [F.iso, G.iso]
end GlobalTheory.DegAsm.NFUnique
