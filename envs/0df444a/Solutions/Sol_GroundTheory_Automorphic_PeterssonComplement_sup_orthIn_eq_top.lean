-- Prove2me | solution 1 for GroundTheory.Automorphic.PeterssonComplement.sup_orthIn_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:47.744947+00:00
-- url     : https://prove2.me/submissions/990d0497-0780-4893-bc2c-81902fde08cf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement

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
open GroundTheory.Automorphic.PeterssonComplement
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
variable {ι}
namespace GroundTheory.Automorphic.PeterssonComplement
theorem _root_.solution (U : Submodule ℂ V)
    (h : ∀ v : V, ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ v ∈ W ∧
      ∀ u ∈ U, ∃ u' ∈ U ⊓ W, ∀ w ∈ W, inner ℂ (ι u) (ι w) = inner ℂ (ι u') (ι w)) :
    U ⊔ orthIn ι U = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨W, hWf, hvW, hW⟩ := h v
  set M : Submodule ℂ H := (U ⊓ W).map ι with hM
  have : FiniteDimensional ℂ (U ⊓ W : Submodule ℂ V) :=
    Submodule.finiteDimensional_of_le (inf_le_right : U ⊓ W ≤ W)
  have : FiniteDimensional ℂ M := by rw [hM]; infer_instance
  have hp : M.starProjection (ι v) ∈ M := Submodule.starProjection_apply_mem M (ι v)
  obtain ⟨a, haUW, hax⟩ := Submodule.mem_map.1 hp
  have horth : ι v - M.starProjection (ι v) ∈ Mᗮ := Submodule.sub_starProjection_mem_orthogonal _
  refine Submodule.mem_sup.2 ⟨a, haUW.1, v - a, fun u hu => ?_, add_sub_cancel _ _⟩
  obtain ⟨u', hu'UW, hu'⟩ := hW u hu
  rw [hu' (v - a) (W.sub_mem hvW haUW.2), map_sub, hax]
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.mem_map_of_mem hu'UW) horth
end GroundTheory.Automorphic.PeterssonComplement
