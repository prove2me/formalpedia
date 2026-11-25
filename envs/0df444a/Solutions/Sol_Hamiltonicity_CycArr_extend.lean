-- Prove2me | solution 1 for Hamiltonicity.CycArr.extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:31:46.286908+00:00
-- url     : https://prove2.me/submissions/96985667-94d5-4b68-b11a-cdbd441b9bb0

module
public import Definitions.Def_MengerHamilton_CyclicArrangement
public import Definitions.Def_MengerHamilton_LongerCycle
public import Theorems.Thm_Hamiltonicity_CycArr_extend_core
public import Theorems.Thm_Hamiltonicity_CycArr_eq_iff
public import Theorems.Thm_Hamiltonicity_CycArr_eq_succ
public import Theorems.Thm_Hamiltonicity_CycArr_pos
public import Theorems.Thm_Hamiltonicity_CycArr_rotate
public import Theorems.Thm_Menger_Aux_Sep_symm


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution (hC : CycArr G m f) {a b : ℕ} (hab : f a ≠ f b) (Q : G.Walk (f a) (f b))
    (hQ : Q.IsPath) (hQl : 2 ≤ Q.length)
    (hint : ∀ y ∈ Q.support, ∀ i, f i = y → y = f a ∨ y = f b)
    (hadj : G.Adj (f (a + 1)) (f (b + 1))) :
    ∃ g, CycArr G (m + Q.length - 1) g := by
  have hpos := hC.pos
  obtain ⟨d, hdm, hd⟩ : ∃ d, d < m ∧ (a + d) % m = b % m := by
    have ha := Nat.mod_add_div a m
    have ha' : a % m < m := Nat.mod_lt _ hpos
    have hb' : b % m < m := Nat.mod_lt _ hpos
    by_cases hle : a % m ≤ b % m
    · refine ⟨b % m - a % m, by omega, ?_⟩
      rw [show a + (b % m - a % m) = b % m + m * (a / m) by omega, Nat.add_mul_mod_self_left,
        Nat.mod_mod]
    · refine ⟨b % m + m - a % m, by omega, ?_⟩
      rw [show a + (b % m + m - a % m) = b % m + m * (a / m + 1) by rw [Nat.mul_succ]; omega,
        Nat.add_mul_mod_self_left, Nat.mod_mod]
  have hfb : f b = f (a + d) := (hC.eq_iff.2 hd).symm
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hab (by rw [hfb]; rfl)
  have hR := hC.rotate a
  have hQ' := hR.extend_core (d := d) (by omega) hdm (Q.copy rfl hfb)
    ((Walk.isPath_copy _ _ _).2 hQ) (by rwa [Walk.length_copy])
    (by
      intro y hy i hi
      rw [Walk.support_copy] at hy
      rcases hint y hy (a + i) hi with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans hfb))
    (by
      have := hC.eq_succ hfb
      rw [show a + (d + 1) = a + d + 1 by omega, ← this]
      exact hadj)
  rwa [Walk.length_copy] at hQ'
end Hamiltonicity.CycArr
