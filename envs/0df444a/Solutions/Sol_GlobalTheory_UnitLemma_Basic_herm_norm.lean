-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Basic.herm_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:40:46.862836+00:00
-- url     : https://prove2.me/submissions/93acfc0f-a453-496b-b68b-65f8699b2fa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NLineOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ValIrreducible

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
theorem _root_.solution (x u y z : B.A) :
    B.herm (x * (u * B.σ u)) y z = B.herm x (u * y) (u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ]
  congr 1
  ring
end _root_.GlobalTheory.UnitLemma.Basic
end GlobalTheory.UnitLemma.Basic
