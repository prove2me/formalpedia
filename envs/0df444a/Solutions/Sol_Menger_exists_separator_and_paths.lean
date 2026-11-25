-- Prove2me | solution 1 for Menger.exists_separator_and_paths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:19:42.046488+00:00
-- url     : https://prove2.me/submissions/9a96dad1-356b-48ea-9168-131454fde474

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Definitions.Def_MengerHamilton_Menger
public import Theorems.Thm_Menger_Aux_fam_of_le


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger
variable {V : Type*}
namespace Menger
theorem _root_.solution [Finite V] (G : SimpleGraph V)
    (A B : Finset V) :
    ∃ X : Finset V, Separates G A B X ∧
      ∃ (a b : Fin X.card → V) (p : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A ∧ b i ∈ B ∧ (p i).IsPath) ∧
        ∀ i j, i ≠ j → ∀ x ∈ (p i).support, x ∉ (p j).support := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨X, hXmem, hXmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun X : Finset V => Separates G A B X)) Finset.card
    ⟨A, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun a ha b _ p => ⟨a, ha, p.start_mem_support⟩⟩⟩
  rw [Finset.mem_filter] at hXmem
  obtain ⟨P, hP, hd⟩ := Aux.fam_of_le _ G rfl A B X.card
    (fun Z hZ => hXmin Z (Finset.mem_filter.2 ⟨Finset.mem_univ _, hZ⟩))
  exact ⟨X, hXmem.2, fun i => (P i).1, fun i => (P i).2.1, fun i => (P i).2.2,
    fun i => ⟨(hP i).1, (hP i).2.1, (hP i).2.2.1⟩, hd⟩
end Menger
