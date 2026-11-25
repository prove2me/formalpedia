-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.mem_span_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:11.092752+00:00
-- url     : https://prove2.me/submissions/55f1c194-cb77-4f2f-b90b-2f599df1cd68

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_orbitSpan_eq_top

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
theorem _root_.solution {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) (x : V) :
    x ∈ Submodule.span ℂ (range fun g => ρ g v) := by
  have := orbitSpan_eq_top (ρ := ρ) hv
  have hx : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
  rw [← this] at hx
  exact hx
end GroundTheory.Automorphic.RestrictedTensor
