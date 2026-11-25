-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.range_orbitMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:31.311192+00:00
-- url     : https://prove2.me/submissions/8d66b313-2cd8-4788-a4e4-6465b30440cf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff

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
open Set
open GroundTheory.Automorphic.RestrictedTensor
variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (ρ : Representation ℂ G V) (v : V) :
    LinearMap.range (orbitMap ρ v) = Submodule.span ℂ (range fun g => ρ g v) := by
  rw [orbitMap, Finsupp.range_linearCombination]
end GroundTheory.Automorphic.RestrictedTensor
