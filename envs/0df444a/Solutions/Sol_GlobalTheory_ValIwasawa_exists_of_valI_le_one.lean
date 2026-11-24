-- Prove2me | solution 1 for GlobalTheory.ValIwasawa.exists_of_valI_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:10:30.913906+00:00
-- url     : https://prove2.me/submissions/4bae0f8e-f539-4941-a839-6f5f1bfa7276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOfValILeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ValIwasawa
open Matrix
variable {V F : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]
namespace GlobalTheory.ValIwasawa
theorem _root_.solution {x : F} (h : valI V x ≤ 1) : ∃ a : V, algebraMap V F a = x :=
  (ValuationRing.mem_integer_iff V F x).1 h
end GlobalTheory.ValIwasawa
