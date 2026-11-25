-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.relIndex_ne_zero_of_le_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:49.373862+00:00
-- url     : https://prove2.me/submissions/77db9b7f-f586-4564-a481-a9378d2601d5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage

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
open Set
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
  {K : Subgroup G} {f : G → W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {H K K' : Subgroup G} (hKK' : K ≤ K')
    (h : H.relIndex K' ≠ 0) : H.relIndex K ≠ 0 := by
  have : (H.subgroupOf K').FiniteIndex := ⟨h⟩
  have : Finite (K ⧸ H.subgroupOf K) :=
    Finite.of_injective _ (Subgroup.quotientSubgroupOfEmbeddingOfLE H hKK').injective
  exact Subgroup.index_ne_zero_of_finite
end GroundTheory.Automorphic.Parabolic
