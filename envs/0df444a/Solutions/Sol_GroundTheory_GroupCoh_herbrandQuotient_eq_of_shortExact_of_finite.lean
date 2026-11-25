-- Prove2me | solution 1 for GroundTheory.GroupCoh.herbrandQuotient_eq_of_shortExact_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:17.329673+00:00
-- url     : https://prove2.me/submissions/216b3796-1782-43dc-a923-35c4459bc91b

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Theorems.Thm_GroundTheory_GroupCoh_finite_of_exact
import Theorems.Thm_GroundTheory_GroupCoh_natCard_kerModRange_eq_of_finite
import Theorems.Thm_GroundTheory_GroupCoh_KerModRange_ker_map_eq_range_map
import Theorems.Thm_GroundTheory_GroupCoh_range_connecting
import Theorems.Thm_GroundTheory_GroupCoh_natCard_kerModRange_hexagon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}
namespace GroundTheory.GroupCoh
theorem _root_.solution [Finite C] (hi : Function.Injective i)
    (hp : Function.Surjective p) (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    herbrandQuotient fA gA = herbrandQuotient fB gB := by
  have hfgC : ∀ c, fC (gC c) = 0 := by
    intro c
    obtain ⟨b, rfl⟩ := hp c
    rw [← hgp, ← hfp, hfgB, map_zero]
  have hgfC : ∀ c, gC (fC c) = 0 := by
    intro c
    obtain ⟨b, rfl⟩ := hp c
    rw [← hfp, ← hgp, hgfB, map_zero]
  have h := natCard_kerModRange_hexagon hi hp hex hfi hgi hfp hgp hfgB hgfB
  rw [natCard_kerModRange_eq_of_finite hfgC hgfC] at h
  have h3 : 0 < Nat.card (KerModRange gC fC) := Nat.card_pos
  have h15 : Nat.card (KerModRange fA gA) * Nat.card (KerModRange gB fB) =
      Nat.card (KerModRange fB gB) * Nat.card (KerModRange gA fA) := by
    apply Nat.eq_of_mul_eq_mul_right h3
    calc _ = Nat.card (KerModRange fA gA) * Nat.card (KerModRange gC fC) *
          Nat.card (KerModRange gB fB) := by ring
      _ = _ := h
  by_cases h4 : Finite (KerModRange gA fA)
  · have h5 : Finite (KerModRange gB fB) :=
      finite_of_exact (KerModRange.map i hgi hfi) (KerModRange.map p hgp hfp)
        (KerModRange.ker_map_eq_range_map hi hp hex hgi hfi hgp hfp hgfB)
    have h4' : (Nat.card (KerModRange gA fA) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have h5' : (Nat.card (KerModRange gB fB) : ℚ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    rw [herbrandQuotient, herbrandQuotient, div_eq_div_iff h4' h5']
    exact_mod_cast h15
  · have h5 : ¬ Finite (KerModRange gB fB) := fun h5 =>
      h4 (finite_of_exact (connecting hi hp hex hfi hgi hfp hgp hfgB hgfB)
        (KerModRange.map i hgi hfi) (range_connecting hi hp hex hfi hgi hfp hgp hfgB hgfB).symm)
    rw [not_finite_iff_infinite] at h4 h5
    rw [herbrandQuotient, herbrandQuotient, Nat.card_eq_zero_of_infinite (α := KerModRange gA fA),
      Nat.card_eq_zero_of_infinite (α := KerModRange gB fB)]
    simp
end GroundTheory.GroupCoh
