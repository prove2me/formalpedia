-- Prove2me | solution 1 for GlobalTheory.PolyNorm.gen_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:27:10.991026+00:00
-- url     : https://prove2.me/submissions/0f782f95-6d01-4ab7-8b13-e65412b2bd71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm
namespace GlobalTheory.PolyNorm
theorem _root_.solution {r : ℕ} {K L : Type} [CommRing K] [CommRing L] (φ : K →+* L) (f : Fin r → K) :
    (gen f).map φ = gen (fun i => φ (f i)) := by
  simp [gen, Polynomial.map_sum]
end GlobalTheory.PolyNorm
