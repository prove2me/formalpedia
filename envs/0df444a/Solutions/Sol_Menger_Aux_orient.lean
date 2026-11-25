-- Prove2me | solution 1 for Menger.Aux.orient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:11:25.633013+00:00
-- url     : https://prove2.me/submissions/123fd565-2445-4233-a23a-bcd8e37118d4

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Theorems.Thm_Menger_Aux_Sep_symm
public import Theorems.Thm_Menger_Aux_R_of_mem
public import Theorems.Thm_Menger_Aux_R_disj
public import Theorems.Thm_Menger_Aux_first_use

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution {G : SimpleGraph V} {e : Sym2 V} {A B Y : Finset V}
    (hY : Sep (G.deleteEdges {e}) A B Y) (hG : ¬ Sep G A B Y) :
    ∃ x y, G.Adj x y ∧ s(x, y) = e ∧ R (G.deleteEdges {e}) A Y x ∧
      R (G.deleteEdges {e}) B Y y := by
  simp only [Sep, not_forall, not_exists, not_and] at hG
  obtain ⟨a, ha, b, hb, p, hp⟩ := hG
  have hp' : ∀ w ∈ p.support, w ∉ Y := fun w hw hwY => hp w hwY hw
  obtain ⟨z0, w0, h0, he0, hR0⟩ :=
    first_use hY p hb (R.of_mem ha (hp' a p.start_mem_support)) hp'
  obtain ⟨z1, w1, h1, he1, hR1⟩ :=
    first_use hY.symm p.reverse ha (R.of_mem hb (hp' b p.end_mem_support)) (by simpa using hp')
  have he := he0.trans he1.symm
  rw [Sym2.eq_iff] at he
  rcases he with ⟨h2, -⟩ | ⟨h2, h3⟩
  · subst h2
    exact (R_disj hY hR0 hR1).elim
  · exact ⟨z0, w0, h0, he0, hR0, h3 ▸ hR1⟩
end Menger.Aux
