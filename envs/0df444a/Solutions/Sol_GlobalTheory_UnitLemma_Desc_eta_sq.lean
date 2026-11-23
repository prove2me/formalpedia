-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.eta_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:41.316802+00:00
-- url     : https://prove2.me/submissions/a1656625-a601-483a-b6b4-0ae9e571caa4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology Classical
variable {K : UQ} (B : InvAlg K) {ι : Type}
namespace GlobalTheory.UnitLemma.Desc
theorem _root_.solution (x : K.E) : K.eta x * K.eta x = 1 := by
  unfold UQ.eta
  rw [← mul_zpow]; simp
end GlobalTheory.UnitLemma.Desc
