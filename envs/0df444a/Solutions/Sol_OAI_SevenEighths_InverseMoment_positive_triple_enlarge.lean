-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.positive_triple_enlarge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:45.491272+00:00
-- url     : https://prove2.me/submissions/a7c3911c-3828-4e7e-989d-631039918477

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SieveComposition

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution {M H C : Type*}
    [DecidableEq M] [DecidableEq H] [DecidableEq C]
    (pairs : Finset (M × H)) (cset : M → Finset C)
    (hs : Finset H) (mc : Finset (M × C)) (E : H → M → C → ℝ)
    (hh : ∀ p ∈ pairs, p.2 ∈ hs)
    (hm : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc)
    (hE : ∀ h m c, 0 ≤ E h m c) :
    (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      ∑ h ∈ hs, ∑ u ∈ mc, E h u.1 u.2 := by
  let f : (Σ _p : M × H, C) → H × (M × C) := fun p => (p.1.2, (p.1.1, p.2))
  have hf : Function.Injective f := by
    have hi : Function.LeftInverse
        (fun u : H × (M × C) => (⟨(u.2.1, u.1), u.2.2⟩ : Σ _p : M × H, C)) f := by
      rintro ⟨⟨m, h⟩, c⟩
      rfl
    exact hi.injective
  have hmapped : ((pairs.sigma (fun p => cset p.1)).image f) ⊆ hs ×ˢ mc := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    have hp' := Finset.mem_sigma.mp hp
    exact Finset.mem_product.mpr ⟨hh p.1 hp'.1, hm p.1 hp'.1 p.2 hp'.2⟩
  have hb : (∑ p ∈ pairs.sigma (fun p => cset p.1), E p.1.2 p.1.1 p.2) ≤
      ∑ u ∈ hs ×ˢ mc, E u.1 u.2.1 u.2.2 := by
    calc
      _ = ∑ u ∈ (pairs.sigma (fun p => cset p.1)).image f, E u.1 u.2.1 u.2.2 :=
        (Finset.sum_image hf.injOn).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hmapped
        (by intro u _ _; exact hE _ _ _)
  simpa only [Finset.sum_sigma, Finset.sum_product] using hb
end OAI.SevenEighths.InverseMoment
