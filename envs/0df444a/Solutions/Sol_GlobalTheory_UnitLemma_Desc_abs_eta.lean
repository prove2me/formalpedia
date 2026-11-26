-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Desc.abs_eta
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:31:07.279725+00:00
-- url     : https://prove2.me/submissions/d2c851a2-1546-4d4d-9f13-708420e2691a

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

theorem solution (x : K.E) : |K.eta x| = 1 := by
  simp [UQ.eta, abs_zpow, abs_neg, abs_one]
