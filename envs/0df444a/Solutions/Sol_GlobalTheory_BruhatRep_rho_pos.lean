-- Prove2me | solution 1 for GlobalTheory.BruhatRep.rho_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:54.387548+00:00
-- url     : https://prove2.me/submissions/a9834f70-b3d6-4ed8-ab9f-b194408e06a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations

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
variable (n : K → M) (m : Kˣ → M) (t : M)
namespace GlobalTheory.BruhatRep
theorem _root_.solution {g : SpecialLinearGroup (Fin 2) K} (h : en g 1 0 = 0) :
    rho n m t g = mx m (en g 0 0) * n (en g 0 1 / en g 0 0) := by
  unfold rho; rw [if_pos h]
end GlobalTheory.BruhatRep
