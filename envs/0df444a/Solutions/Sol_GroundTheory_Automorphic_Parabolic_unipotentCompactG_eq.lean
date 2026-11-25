-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.unipotentCompactG_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:21.679097+00:00
-- url     : https://prove2.me/submissions/91c0a174-670a-4ee4-a03e-4667fd2a0bc1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentCompactG

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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable (γ : Fin n → ℕ)
variable {γ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (e : ℕ) :
    unipotentCompactG (F := F) γ e = unipotentRadical F n γ ⊓
      (integralGL F n).comap (MulAut.conj (rankTorus F n γ e)).toMonoidHom := by
  ext u
  rw [mem_unipotentCompactG, Subgroup.mem_inf, Subgroup.mem_comap]
  rfl
end GroundTheory.Automorphic.Parabolic
