-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.exists_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:45:11.79852+00:00
-- url     : https://prove2.me/submissions/59164d06-8abb-44c7-9ac9-3dde78f25ff2

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_le_one_iff
import Theorems.Thm_GroundTheory_FunctionField_Place_valuation_lt_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
namespace GroundTheory.FunctionField.Place
theorem _root_.solution (v : Place k K) : ∃ w : Place k K', w.LiesOver v := by
  let f : v.ring →+* K' := (algebraMap K K').comp v.ring.subtype
  have hf : Function.Injective f := (algebraMap K K').injective.comp Subtype.val_injective
  let g : v.ring →+* f.range := f.rangeRestrict
  have hg : Function.Bijective g :=
    ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  let I : Ideal f.range := (IsLocalRing.maximalIdeal v.ring).map g
  have hI : I ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal v.ring).ne_top ((Ideal.map_eq_top_of_bijective g hg).1 h)
  obtain ⟨B, hAB, hIB⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hmem : ∀ a : v.ring, a ∈ IsLocalRing.maximalIdeal v.ring → f a ∈ B.nonunits := fun a ha =>
    hIB ⟨g a, Ideal.mem_map_of_mem g ha, rfl⟩
  have hAB' : ∀ a : v.ring, f a ∈ B := fun a => hAB (RingHom.mem_range_self f a)
  obtain ⟨x, hx0, hx⟩ := v.exists_valuation_lt_one_ne_zero
  have hxO : x ∈ v.ring := (v.ring.valuation_le_one_iff x).1 hx.le
  have hfx : algebraMap K K' x ∈ B.nonunits := hmem ⟨x, hxO⟩ ((v.ring.valuation_lt_one_iff _).2 hx)
  refine ⟨⟨B, ?_, ?_⟩, ?_⟩
  · intro htop
    rcases B.mem_nonunits_iff_or.1 hfx with h | h
    · exact hx0 ((algebraMap K K').injective (h.trans (map_zero _).symm))
    · exact h (htop ▸ ValuationSubring.mem_top _)
  · intro c
    rw [IsScalarTower.algebraMap_apply k K K']
    exact hAB' ⟨_, v.algebraMap_mem c⟩
  · apply le_antisymm
    · intro y hy
      rw [ValuationSubring.mem_comap] at hy
      by_contra hyv
      have hy0 : y ≠ 0 := fun h => hyv (h ▸ v.ring.zero_mem)
      have hinv : y⁻¹ ∈ v.ring.nonunits := v.ring.inv_mem_nonunits_iff.2 (Or.inr hyv)
      obtain ⟨hr, hrm⟩ := v.ring.mem_nonunits_iff_exists_mem_maximalIdeal.1 hinv
      have h1 : algebraMap K K' y⁻¹ ∈ B.nonunits := hmem _ hrm
      rw [map_inv₀] at h1
      rcases B.inv_mem_nonunits_iff.1 h1 with h | h
      · exact hy0 ((algebraMap K K').injective (h.trans (map_zero _).symm))
      · exact h hy
    · intro y hy
      exact ValuationSubring.mem_comap.2 (hAB' ⟨y, hy⟩)
end GroundTheory.FunctionField.Place
