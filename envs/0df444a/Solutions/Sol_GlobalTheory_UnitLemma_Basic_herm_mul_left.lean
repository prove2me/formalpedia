-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Basic.herm_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:36.179721+00:00
-- url     : https://prove2.me/submissions/8a790bfb-53f1-44b7-ab59-1c89f6a931e8

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
    B.herm x (u * y) z = B.herm x y (B.σ u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ, B.σ_σ]
  congr 1
  ring
end _root_.GlobalTheory.UnitLemma.Basic
end GlobalTheory.UnitLemma.Basic
