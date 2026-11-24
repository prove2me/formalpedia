-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_ne_zero_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:28.941933+00:00
-- url     : https://prove2.me/submissions/eb07d77c-1d62-47c1-a3f8-53f643e10ad1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRepSchur

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Polynomial Cardinal
variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
namespace GroundTheory.Automorphic
theorem _root_.solution [ρ.IsIrreducible] : ∃ v : V, v ≠ 0 := by
  by_contra h
  push Not at h
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule ℂ V) = ⊤
  ext v
  simp [h v]
end GroundTheory.Automorphic
