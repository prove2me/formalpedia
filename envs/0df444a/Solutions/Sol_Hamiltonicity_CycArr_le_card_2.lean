-- Prove2me | solution 2 for Hamiltonicity.CycArr.le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:49:55.701745+00:00
-- url     : https://prove2.me/submissions/16488899-e7e2-4267-bd73-ddb865274910

module
public import Definitions.Def_MengerHamilton_Menger
public import Definitions.Def_MengerHamilton_CyclicArrangement

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}
open Hamiltonicity.CycArr
variable {G : SimpleGraph V} {m : ℕ} {f : ℕ → V}
namespace Hamiltonicity.CycArr
theorem _root_.solution [Fintype V] (h : CycArr G m f) : m ≤ Fintype.card V := by
  classical
  have : ((Finset.range m).image f).card = m := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact h.inj i j (by simpa using hi) (by simpa using hj) hij
  rw [← this]
  exact Finset.card_le_univ _
end Hamiltonicity.CycArr
