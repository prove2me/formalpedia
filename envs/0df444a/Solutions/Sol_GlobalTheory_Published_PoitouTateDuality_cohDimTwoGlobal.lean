-- Prove2me | solution 1 for GlobalTheory.Published.PoitouTateDuality.cohDimTwoGlobal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:09:24.210814+00:00
-- url     : https://prove2.me/submissions/4543e247-d01d-4a06-9131-dc6886d98a5a

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__CohDimTwoLocalOfLocalFiniteness_b2c2e165733ad400
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ExistsPrimitiveRootPow_85cddf4c39d1fc1a
import Theorems.Thm_GlobalTheory_Published_exists_primitiveRoot_pow
import Theorems.Thm_GlobalTheory_Published_PoitouTate_exists_lift_cycMod
import Theorems.Thm_GlobalTheory_Published_subsingleton_Hn_succ_iff
import Theorems.Thm_ReciprocityTheory_Gal_exists_isPlaceOver


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.Published
open PoitouTate
open NumberField IsDedekindDomain
namespace GlobalTheory.Published
namespace _root_.GlobalTheory.Published.PoitouTateDuality
theorem _root_.solution
    (h : _root_.GlobalTheory.Published.PoitouTateDuality) : _root_.GlobalTheory.Published.CohDimTwoGlobal := by
  unfold _root_.GlobalTheory.Published.CohDimTwoGlobal
  intro F Ω _ _ _ _ _ _ l _ r M _ _ _ _ _ S rhoS hS hρ n hn
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    haveI : Subsingleton M := Module.subsingleton (ZMod (l ^ 0)) M
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [_root_.GlobalTheory.Published.subsingleton_Hn_succ_iff]
    intro f _ _
    exact ⟨0, continuous_zero, Subsingleton.elim _ _⟩
  · obtain ⟨ζ, hζ⟩ := _root_.GlobalTheory.Published.exists_primitiveRoot_pow F Ω l r
    obtain ⟨inv, _, hall⟩ := h F Ω l r (Or.inr inferInstance) hr ζ hζ
    obtain ⟨μ, hμ⟩ := _root_.GlobalTheory.Published.PoitouTate.exists_lift_cycMod (Ω := Ω) (r := r) hS
    exact (hall S hS (fun v => (_root_.ReciprocityTheory.Gal.exists_isPlaceOver Ω v.1).choose) (fun v => (_root_.ReciprocityTheory.Gal.exists_isPlaceOver Ω v.1).choose_spec)
      μ hμ M rhoS hρ).2.2 n hn
end _root_.GlobalTheory.Published.PoitouTateDuality
end GlobalTheory.Published
