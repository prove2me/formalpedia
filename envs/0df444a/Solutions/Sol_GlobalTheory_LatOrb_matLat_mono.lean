-- Prove2me | solution 1 for GlobalTheory.LatOrb.matLat_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:32:42.864913+00:00
-- url     : https://prove2.me/submissions/1379a014-8033-489f-a0a7-b7b2270221d7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
noncomputable section
open GlobalTheory GlobalTheory.LatOrb
variable {K : Type} [Field K] {n : ℕ}
namespace GlobalTheory.LatOrb
theorem _root_.solution {O : Type} [CommRing O] [Algebra O K] {M N : Submodule O (Fin n → K)}
    (u : Matrix (Fin n) (Fin n) K) (h : M ≤ N) : matLat O u M ≤ matLat O u N :=
  Submodule.map_mono h
end GlobalTheory.LatOrb
