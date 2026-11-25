-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.jacquetFiltration_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:43:48.963794+00:00
-- url     : https://prove2.me/submissions/ff3b7ec9-2fe0-41f9-bb4b-f742a38fc5ec

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_supportedIn_univ

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
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β : Fin n → ℕ} (γ : Fin n → ℕ)
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable {σ}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution : jacquetFiltration γ (σ := σ) univ = ⊤ := by
  rw [jacquetFiltration, supportedIn_univ, Submodule.map_top, LinearMap.range_eq_top]
  exact Representation.Coinvariants.mk_surjective _
end GroundTheory.Automorphic.Parabolic
