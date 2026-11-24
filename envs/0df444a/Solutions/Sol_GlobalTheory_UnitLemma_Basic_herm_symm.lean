-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Basic.herm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:03:15.554825+00:00
-- url     : https://prove2.me/submissions/b343e4f7-099d-4790-8c8e-946585fa446a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NLineOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible
import Theorems.Thm_GlobalTheory_UnitLemma_Basic_trace_sigma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Basic
variable {K : UQ} (B : InvAlg K)
variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K)
namespace GlobalTheory.UnitLemma.Basic
namespace _root_.GlobalTheory.UnitLemma.Basic
theorem _root_.solution (x : B.A) (hx : B.σ x = x) (y z : B.A) :
    B.herm x z y = K.c (B.herm x y z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [← _root_.GlobalTheory.UnitLemma.Basic.trace_sigma, map_mul B.σ, map_mul B.σ, hx, B.σ_σ]
  congr 1
  ring
end _root_.GlobalTheory.UnitLemma.Basic
end GlobalTheory.UnitLemma.Basic
