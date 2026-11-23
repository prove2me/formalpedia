-- Prove2me | solution 1 for GlobalTheory.BruhatRep.en_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:23.361121+00:00
-- url     : https://prove2.me/submissions/69d75d9c-4d0f-4224-a490-85a54acafbdb

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
namespace GlobalTheory.BruhatRep
theorem _root_.solution (g h : SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    en (g * h) i j = en g i 0 * en h 0 j + en g i 1 * en h 1 j := by
  simp [en, Matrix.mul_apply, Fin.sum_univ_two]
end GlobalTheory.BruhatRep
