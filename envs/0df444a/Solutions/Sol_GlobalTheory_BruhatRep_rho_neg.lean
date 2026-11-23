-- Prove2me | solution 1 for GlobalTheory.BruhatRep.rho_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:27.685497+00:00
-- url     : https://prove2.me/submissions/7a079268-f5a0-4e8f-99da-90232ecbe85e

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
theorem _root_.solution {g : SpecialLinearGroup (Fin 2) K} (h : en g 1 0 ≠ 0) :
    rho n m t g = n (en g 0 0 / en g 1 0) * mx m (-1 / en g 1 0) * t * n (en g 1 1 / en g 1 0) := by
  unfold rho; rw [if_neg h]
end GlobalTheory.BruhatRep
