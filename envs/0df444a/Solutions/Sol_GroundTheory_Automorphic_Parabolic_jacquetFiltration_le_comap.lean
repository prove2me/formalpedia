-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.jacquetFiltration_le_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:41:37.354668+00:00
-- url     : https://prove2.me/submissions/72d17de4-2951-461d-a6f3-233f3a0f41c7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_supportedIn_le_comap

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
theorem _root_.solution {Y : Set (GL (Fin n) F)}
    (hY : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y) (m : levi F n γ) :
    jacquetFiltration γ (σ := σ) Y ≤
      (jacquetFiltration γ Y).comap (jacquetRep F n γ (parabolicInd F n β σ) m) := by
  rintro _ ⟨f, hf, rfl⟩
  rw [Submodule.mem_comap, jacquetRep_mk]
  exact Submodule.smul_mem _ _ ⟨_, supportedIn_le_comap γ hY (levi_le_blockUpper m.2) hf, rfl⟩
end GroundTheory.Automorphic.Parabolic
