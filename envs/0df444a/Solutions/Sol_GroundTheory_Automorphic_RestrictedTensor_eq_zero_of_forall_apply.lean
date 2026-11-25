-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.eq_zero_of_forall_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:51.756794+00:00
-- url     : https://prove2.me/submissions/17d2be34-026d-4cde-83c1-f8c2e14fac75

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_span_orbit

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
theorem _root_.solution {ρ : Representation ℂ G V} [ρ.IsIrreducible] {v : V} (hv : v ≠ 0)
    {l : Module.Dual ℂ V} (h : ∀ g, l (ρ g v) = 0) : l = 0 := by
  ext x
  have hx := mem_span_orbit (ρ := ρ) hv x
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact h g
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]
end GroundTheory.Automorphic.RestrictedTensor
