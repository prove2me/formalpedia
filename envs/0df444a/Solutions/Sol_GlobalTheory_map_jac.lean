-- Prove2me | solution 1 for GlobalTheory.map_jac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:11.952552+00:00
-- url     : https://prove2.me/submissions/73148e41-f93d-4252-a380-881509ce8e6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
import Theorems.Thm_GlobalTheory_jacAlt_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.exteriorPowerMapOver_ιMulti
attribute [local simp] GlobalTheory.wedgeContract_ιMulti
attribute [local simp] GlobalTheory.jacAlt_apply

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] {D : ℕ}
open KaehlerDifferential
variable {R}
namespace GlobalTheory
theorem _root_.solution (S B : Type*) [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [IsScalarTower R S B] [SMulCommClass S A B]
    (f : Fin (D + 1) → A) :
    exteriorPowerMapOver B D (KaehlerDifferential.map R S A B) (jac R f)
      = jac S (fun i => algebraMap A B (f i)) := by
  rw [jac, jac, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, dWedge, exteriorPowerMapOver_ιMulti, ← algebraMap_smul B]
  simp [dWedge]
end GlobalTheory
