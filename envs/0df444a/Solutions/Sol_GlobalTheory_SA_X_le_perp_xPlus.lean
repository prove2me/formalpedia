-- Prove2me | solution 1 for GlobalTheory.SA.X_le_perp_xPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:07:27.326598+00:00
-- url     : https://prove2.me/submissions/b420364f-ef75-492c-9158-a2c3eb7c8ac1

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_z_mem_perp
import Theorems.Thm_GlobalTheory_HermLat_mem_perp_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.SA
theorem _root_.solution (F : FlagD H r) : F.X ≤ perp H (xPlus F) := fun x hx =>
  (mem_perp_xPlus F x).2 ⟨X_le_perp F hx, B_eq_zero_comm.1 ((mem_perp_iff H _ _).1 (z_mem_perp F) x hx)⟩
end GlobalTheory.SA
