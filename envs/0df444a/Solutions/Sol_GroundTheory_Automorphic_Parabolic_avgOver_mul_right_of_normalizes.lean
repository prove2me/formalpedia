-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_mul_right_of_normalizes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:12:47.486058+00:00
-- url     : https://prove2.me/submissions/40b59591-b4f9-456c-b01d-6ee82278b8e4

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_comp_mul_left
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgOver_map_conj


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
theorem _root_.solution {K : Subgroup G} {f : G → W} (hf : AvgFinite K f) {k : G}
    (hk : K.map (MulAut.conj k).toMonoidHom = K) (hkf : ∀ y, f (y * k) = f y) (y : G) :
    avgOver K f (y * k) = avgOver K f y := by
  have h1 := avgOver_map_conj k hf (k * y)
  rw [hk] at h1
  have h2 : (fun z => f (k⁻¹ * z * k)) = fun z => f (k⁻¹ * z) := by
    funext z
    exact hkf _
  rw [h2, avgOver_comp_mul_left] at h1
  rw [show k⁻¹ * (k * y) * k = y * k by group] at h1
  rw [← h1]
  congr 1
  group
end GroundTheory.Automorphic.Parabolic
