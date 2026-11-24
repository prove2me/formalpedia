-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.LowerUnip.flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:33.902599+00:00
-- url     : https://prove2.me/submissions/cce32c9e-2b84-470c-8f96-58ab9aa07757

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
namespace LowerUnip
theorem _root_.solution {β : O} {l : Matrix (Fin n) (Fin n) O} (hl : LowerUnip β l) :
    UpperUnip β (flip l) := fun i j =>
  ⟨fun h => (hl _ _).1 (Fin.rev_lt_rev.2 h), fun h => (hl _ _).2.1 (congrArg Fin.rev h),
    fun h => (hl _ _).2.2 (Fin.rev_lt_rev.2 h)⟩
end LowerUnip
end GlobalTheory.IwahoriFactor
