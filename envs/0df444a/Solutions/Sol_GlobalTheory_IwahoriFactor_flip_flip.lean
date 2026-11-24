-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.flip_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:12:46.858059+00:00
-- url     : https://prove2.me/submissions/1312f448-fb7d-4e47-8e42-01ad438304a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular
import Theorems.Thm_GlobalTheory_IwahoriFactor_flip_apply

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
theorem _root_.solution (g : Matrix (Fin n) (Fin n) O) : flip (flip g) = g := by
  ext i j; simp [flip_apply]
end GlobalTheory.IwahoriFactor
