-- Prove2me | solution 1 for GlobalTheory.LatOrbGL.matLat_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:37.12389+00:00
-- url     : https://prove2.me/submissions/c52b6b65-a291-4361-adcb-26b92c1d038c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGLintIffMatrixImageStandardLatticeEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
open GlobalTheory GlobalTheory.LatOrbGL
variable {K : Type} [Field K] (V : ValuationSubring K)
namespace GlobalTheory.LatOrbGL
theorem _root_.solution {n : ℕ} (g : Matrix (Fin n) (Fin n) K) {M N : Submodule V (Fin n → K)}
    (h : M ≤ N) : matLat V g M ≤ matLat V g N := Submodule.map_mono h
end GlobalTheory.LatOrbGL
