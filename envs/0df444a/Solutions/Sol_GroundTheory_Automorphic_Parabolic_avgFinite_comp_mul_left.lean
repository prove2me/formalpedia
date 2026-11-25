-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgFinite_comp_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:11:46.381839+00:00
-- url     : https://prove2.me/submissions/b50bb3ef-3632-4969-a837-2ee2b04b4d4d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_rightStab


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
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) (h : G) :
    AvgFinite K (fun y => f (h * y)) := by
  intro h0
  have hle : rightStab f ≤ rightStab (fun y => f (h * y)) := fun g hg => by
    rw [mem_rightStab] at hg ⊢
    intro x
    rw [← mul_assoc, hg]
  exact hf (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_of_le_left _ hle))
end GroundTheory.Automorphic.Parabolic
