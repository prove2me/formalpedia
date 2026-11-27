-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_unramifiedClosure_of_forall_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:49:29.820837+00:00
-- url     : https://prove2.me/submissions/a2c803b4-7ff6-4ea5-ad98-c98671a1c062

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
import Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_p_algCl_lt_one
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_le_max_of_ultrametric

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
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {β : PadicAlgCl p}
    (h : ∀ m : ℕ, ∃ u ∈ unramifiedClosure p, ‖β - u‖ ≤ ‖(p : PadicAlgCl p)‖ ^ m) :
    β ∈ unramifiedClosure p := by
  rw [← InfiniteGalois.fixedField_fixingSubgroup (unramifiedClosure p),
    IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have hnorm : ∀ z, ‖σ z‖ = ‖z‖ := fun z => (spectralNorm_eq_of_equiv σ z).symm
  have key : ∀ m : ℕ, ‖σ β - β‖ ≤ ‖(p : PadicAlgCl p)‖ ^ m := fun m => by
    obtain ⟨u, hu, hbu⟩ := h m
    have hσu : σ u = u := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ u hu
    have e : σ β - β = σ (β - u) - (β - u) := by rw [map_sub, hσu]; ring
    rw [e]
    refine (norm_sub_le_max_of_ultrametric _ _).trans (max_le ?_ hbu)
    rw [hnorm]
    exact hbu
  by_contra hne
  have hpos : 0 < ‖σ β - β‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (norm_natCast_p_algCl_lt_one (p := p))
  exact absurd (key m) (not_le.2 hm)
end GroundTheory.PAdicHodge
