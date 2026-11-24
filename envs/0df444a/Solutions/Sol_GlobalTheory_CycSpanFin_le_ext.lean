-- Prove2me | solution 1 for GlobalTheory.CycSpanFin.le_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:08:15.387011+00:00
-- url     : https://prove2.me/submissions/1f4ed9c3-9326-4466-b729-b537bf8ddda9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteDimensionalSpanAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Polynomial
open GlobalTheory GlobalTheory.CycSpanFin
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CycSpanFin
theorem _root_.solution (T : Module.End ℂ V) (d : ℕ) (N : Submodule ℂ V) : N ≤ ext T d N := fun v hv =>
  Submodule.mem_iSup_of_mem (0 : Fin (d + 1)) ⟨v, hv, by simp⟩
end GlobalTheory.CycSpanFin
