-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Basic.herm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:06.516272+00:00
-- url     : https://prove2.me/submissions/46cdbc22-1e49-41ec-b3b0-b850a83483f0

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
theorem _root_.solution (x y z : B.A) (e : K.E) :
    B.herm x (e • y) z = e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]
end _root_.GlobalTheory.UnitLemma.Basic
end GlobalTheory.UnitLemma.Basic
