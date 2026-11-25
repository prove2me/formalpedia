-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mem_span_mOrbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:04:28.013211+00:00
-- url     : https://prove2.me/submissions/1e230e10-4128-43d9-9108-9cc1db4c4591

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_mOrbitSpan_self

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
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ρ : Representation ℂ M V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    (x : V) : x ∈ Submodule.span ℂ (range fun m => ρ m v) := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (mOrbitSpan ρ v) with h | h
  · exfalso
    apply hv
    have := mem_mOrbitSpan_self ρ v
    rw [h] at this
    exact this
  · have hx : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
    rw [← h] at hx
    exact hx
end GroundTheory.Automorphic.RestrictedTensor
