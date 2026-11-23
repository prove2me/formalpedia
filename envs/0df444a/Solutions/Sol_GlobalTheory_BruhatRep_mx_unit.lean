-- Prove2me | solution 1 for GlobalTheory.BruhatRep.mx_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:07.29726+00:00
-- url     : https://prove2.me/submissions/1a462f86-ff9c-40c4-8aa0-b8fe49d6c4e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
import Theorems.Thm_GlobalTheory_BruhatRep_mx_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]
variable {M : Type} [Monoid M]
namespace GlobalTheory.BruhatRep
theorem _root_.solution (m : Kˣ → M) (s : Kˣ) : mx m (s : K) = m s := by
  rw [mx_ne m s.ne_zero, Units.mk0_val]
end GlobalTheory.BruhatRep
