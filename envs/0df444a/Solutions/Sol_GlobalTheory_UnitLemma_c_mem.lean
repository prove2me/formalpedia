-- Prove2me | solution 1 for GlobalTheory.UnitLemma.c_mem
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T13:32:57.888032+00:00
-- url     : https://prove2.me/submissions/d520e078-ac1e-42a2-825c-5db90e3f92d6

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

theorem solution (K : UQ) {z : K.E} (hz : z ∈ (algebraMap K.O K.E).range) :
    K.c z ∈ (algebraMap K.O K.E).range := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨y, hy⟩ := K.c_int x
  exact ⟨y, hy.symm⟩
