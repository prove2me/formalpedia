-- Prove2me | solution 1 for GlobalTheory.BruhatRep.det_en
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:27.767978+00:00
-- url     : https://prove2.me/submissions/4cbee739-9902-44d7-bb29-51d4d780a732

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
theorem _root_.solution (g : SpecialLinearGroup (Fin 2) K) : en g 0 0 * en g 1 1 - en g 0 1 * en g 1 0 = 1 := by
  have h := g.2; rw [Matrix.det_fin_two] at h; exact h
end GlobalTheory.BruhatRep
