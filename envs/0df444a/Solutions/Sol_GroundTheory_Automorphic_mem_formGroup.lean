-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_formGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:03:03.540819+00:00
-- url     : https://prove2.me/submissions/8cf5bb4d-7b3e-43fd-9226-eee1ff5bb854

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicDixmierMalliavinLie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set
set_option linter.unusedSectionVars false
noncomputable section
variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [FiniteDimensional ℝ 𝔄]
  (σ : 𝔄 →ₗ[ℝ] 𝔄) (hσ1 : σ 1 = 1) (hσ : ∀ x y, σ (x * y) = σ y * σ x) (J : 𝔄ˣ)
namespace GroundTheory.Automorphic
theorem _root_.solution {g : 𝔄ˣ} : g ∈ formGroup σ hσ1 hσ J ↔ σ g * J * g = J := Iff.rfl
end GroundTheory.Automorphic
