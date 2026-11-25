-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.orbitSpan_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:59:30.497935+00:00
-- url     : https://prove2.me/submissions/c795c347-bf0c-4535-b9aa-c7ac9a6730d3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_orbitSpan_self

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
theorem _root_.solution {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) :
    orbitSpan ρ v = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (orbitSpan ρ v) with h | h
  · exfalso
    apply hv
    have := mem_orbitSpan_self ρ v
    rw [h] at this
    exact this
  · exact h
end GroundTheory.Automorphic.RestrictedTensor
