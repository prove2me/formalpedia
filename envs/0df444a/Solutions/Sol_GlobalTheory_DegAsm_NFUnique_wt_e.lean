-- Prove2me | solution 1 for GlobalTheory.DegAsm.NFUnique.wt_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:55:24.804826+00:00
-- url     : https://prove2.me/submissions/16525746-d593-4085-af6c-90c03633a348

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
import Theorems.Thm_GlobalTheory_DegAsm_NFUnique_flag_vector_mem_base_lattice
import Theorems.Thm_P2M_GlobalTheory_DegCnt_NFGeom_mem_perp__b010c7cdb5ee


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
variable [NumberField K]
namespace GlobalTheory.DegAsm.NFUnique
theorem _root_.solution (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F.e a) w = 0 :=
  (NFGeom.mem_perp' _ _).1 hw _ (Submodule.mem_sup_left (flag_vector_mem_base_lattice _ _ a))
end GlobalTheory.DegAsm.NFUnique
