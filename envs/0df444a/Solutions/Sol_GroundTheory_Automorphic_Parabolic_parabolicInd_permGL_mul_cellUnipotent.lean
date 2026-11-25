-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.parabolicInd_permGL_mul_cellUnipotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:27.090394+00:00
-- url     : https://prove2.me/submissions/5213cfbf-a026-4bb1-b766-c45c0aab30b4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_parabolicInd_permGL_mul

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
variable (F) (β γ : Fin n → ℕ) (w : Equiv.Perm (Fin n))
variable {F β γ w}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (f : parabolicIndSpace F n β σ)
    (a : cellUnipotent F β γ w) (y : GL (Fin n) F) :
    (f : GL (Fin n) F → W) (permGL F w * ((a : GL (Fin n) F) * y)) =
      cellRepA β γ w σ a ((f : GL (Fin n) F → W) (permGL F w * y)) :=
  parabolicInd_permGL_mul w σ f (Subgroup.inclusion cellUnipotent_le_blockUpper a) y
end GroundTheory.Automorphic.Parabolic
