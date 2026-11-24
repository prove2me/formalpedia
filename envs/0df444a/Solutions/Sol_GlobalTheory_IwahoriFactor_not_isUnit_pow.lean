-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.not_isUnit_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:57:25.473976+00:00
-- url     : https://prove2.me/submissions/74034323-4c77-4f5e-9e63-ac7ba24946e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
namespace GlobalTheory.IwahoriFactor
theorem _root_.solution {O : Type} [CommRing O] {ϖ : O} (hϖ : Irreducible ϖ) {s : ℕ} (hs : 1 ≤ s) :
    ¬ IsUnit (ϖ ^ s) := fun h =>
  hϖ.not_isUnit ((isUnit_pow_iff (by omega)).1 h)
end GlobalTheory.IwahoriFactor
