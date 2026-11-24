-- Prove2me | solution 1 for GlobalTheory.UnipotentBorder.IsUU.top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:49:54.7348+00:00
-- url     : https://prove2.me/submissions/ccd79701-d7cd-4987-9282-774053ebc96b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]
namespace GlobalTheory.UnipotentBorder
namespace IsUU
theorem _root_.solution {n : ℕ} {U : Matrix (Fin (n+1)) (Fin (n+1)) O} (hU : IsUU U) :
    IsUU (U.submatrix Fin.castSucc Fin.castSucc) := fun _ _ ↦
  ⟨fun h ↦ (hU _ _).1 (Fin.castSucc_lt_castSucc_iff.2 h), fun h ↦ (hU _ _).2 (congrArg _ h)⟩
end IsUU
end GlobalTheory.UnipotentBorder
