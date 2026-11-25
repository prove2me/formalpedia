-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.permGL_conj_mem_congruenceSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:35:58.233784+00:00
-- url     : https://prove2.me/submissions/fefb3701-19d5-4d14-b157-d8a1ab47396d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_permGL_mem_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_conj_mem_congruenceSubgroup


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
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {J : ℕ} {k : GL (Fin n) F}
    (hk : k ∈ congruenceSubgroup F n J) :
    permGL F w * k * (permGL F w)⁻¹ ∈ congruenceSubgroup F n J :=
  conj_mem_congruenceSubgroup F n (permGL_mem_integralGL w) hk
end GroundTheory.Automorphic.Parabolic
