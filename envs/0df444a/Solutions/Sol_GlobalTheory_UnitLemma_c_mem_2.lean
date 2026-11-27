-- Prove2me | solution 2 for GlobalTheory.UnitLemma.c_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:35:59.14854+00:00
-- url     : https://prove2.me/submissions/cdfb3651-7af1-47dc-a9d9-51d4e02826f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsInhabitants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NLineOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial IsLocalRing
namespace GlobalTheory.UnitLemma
theorem _root_.solution (K : UQ) {z : K.E} (hz : z ∈ (algebraMap K.O K.E).range) : K.c z ∈ (algebraMap K.O K.E).range := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨y, hy⟩ := K.c_int x
  exact ⟨y, hy.symm⟩
end GlobalTheory.UnitLemma
