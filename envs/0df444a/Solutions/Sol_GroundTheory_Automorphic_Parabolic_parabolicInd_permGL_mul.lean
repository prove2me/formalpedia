-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.parabolicInd_permGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:31.161503+00:00
-- url     : https://prove2.me/submissions/3d44940d-9759-4b69-ac4f-e4eba34b8898

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellRep_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_parabolicIndSpace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β : Fin n → ℕ} (w : Equiv.Perm (Fin n))
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (f : parabolicIndSpace F n β σ) (x : blockUpper F n (β ∘ w))
    (y : GL (Fin n) F) :
    (f : GL (Fin n) F → W) (permGL F w * ((x : GL (Fin n) F) * y)) =
      cellRep β w σ x ((f : GL (Fin n) F → W) (permGL F w * y)) := by
  have h := ((mem_parabolicIndSpace σ).1 f.2).1 (permConj F β w x) (permGL F w * y)
  rw [coe_permConj] at h
  rw [cellRep_apply, inflateTwist_apply, ← h]
  group
end GroundTheory.Automorphic.Parabolic
