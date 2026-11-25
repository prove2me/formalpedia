-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isCompact_unipotentCompactG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:53.758061+00:00
-- url     : https://prove2.me/submissions/cc029444-52c0-4e1b-a197-55fc16eca1b4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompact_unipotentCompact


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
    IsCompact (unipotentCompactG (F := F) γ e : Set (GL (Fin n) F)) := by
  rw [unipotentCompactG, Subgroup.coe_map]
  exact (isCompact_unipotentCompact e).image continuous_subtype_val
end GroundTheory.Automorphic.Parabolic
