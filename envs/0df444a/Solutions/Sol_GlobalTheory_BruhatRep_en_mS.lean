-- Prove2me | solution 1 for GlobalTheory.BruhatRep.en_mS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:58.821801+00:00
-- url     : https://prove2.me/submissions/baa4068b-a5c6-4ca3-8267-e536e1392ba1

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
theorem _root_.solution (s : Kˣ) : en (mS s) 0 0 = s ∧ en (mS s) 0 1 = 0 ∧ en (mS s) 1 0 = 0 ∧ en (mS s) 1 1 = (s : K)⁻¹ := by
  simp [en, mS]
end GlobalTheory.BruhatRep
