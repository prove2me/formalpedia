-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.avgOver_permGL_mul_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:24:51.85583+00:00
-- url     : https://prove2.me/submissions/59bed11e-72d8-4dc9-91c6-528da569b6c6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_avgFinite_comp_mul_left
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
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (f : parabolicIndSpace F n β σ) {K : Subgroup (GL (Fin n) F)}
    (hf : AvgFinite K (f : GL (Fin n) F → W)) {t : GL (Fin n) F}
    (ht : K.map (MulAut.conj t).toMonoidHom = K) (u : GL (Fin n) F) :
    avgOver K (f : GL (Fin n) F → W) (permGL F w * u * t) = avgOver K (cellFun w σ f t) u := by
  have h0 := avgFinite_comp_mul_left hf (permGL F w * t)
  have h1 := avgOver_map_conj t h0 u
  rw [ht] at h1
  have h2 : (fun y => (fun z => (f : GL (Fin n) F → W) (permGL F w * t * z)) (t⁻¹ * y * t)) =
      cellFun w σ f t := by
    funext y
    unfold cellFun
    group
  rw [h2] at h1
  rw [h1, avgOver_comp_mul_left]
  congr 1
  group
end GroundTheory.Automorphic.Parabolic
