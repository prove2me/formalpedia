-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.not_isUnit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:38.157563+00:00
-- url     : https://prove2.me/submissions/b3e847d8-00bc-4b6e-8eb9-eefd802c402f

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
variable {O : Type} [CommRing O] {n : ℕ}
namespace GlobalTheory.IwahoriFactor
theorem _root_.solution {α β : O} (hβ : ¬ IsUnit β) : ¬ IsUnit (α * β) :=
  fun h => hβ (isUnit_of_mul_isUnit_right h)
end GlobalTheory.IwahoriFactor
