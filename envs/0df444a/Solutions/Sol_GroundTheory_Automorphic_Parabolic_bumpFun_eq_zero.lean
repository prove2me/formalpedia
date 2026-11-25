-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.bumpFun_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:25.41466+00:00
-- url     : https://prove2.me/submissions/8976ac3b-ba8e-4530-87b1-c8a1d4b93c65

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective

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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
variable {σ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {x : GL (Fin n) F} {K : Subgroup (GL (Fin n) F)} {v : W}
    {g : GL (Fin n) F}
    (hg : ¬ ∃ p : blockUpper F n β, ∃ k ∈ K, g = (p : GL (Fin n) F) * x * k) :
    bumpFun σ x K v g = 0 := by
  unfold bumpFun
  rw [dif_neg hg]
end GroundTheory.Automorphic.Parabolic
