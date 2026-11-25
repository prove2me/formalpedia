-- Prove2me | solution 1 for Menger.Aux.path_R
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:10:34.943258+00:00
-- url     : https://prove2.me/submissions/f887b0c3-82a5-4b4f-a9ca-48fce4f28b36

module
public import Mathlib
public import Definitions.Def_MengerHamilton_MengerCore
public import Theorems.Thm_Menger_Aux_path_takeUntil_end_not_mem

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Menger Menger.Aux
variable {V : Type*}
namespace Menger.Aux
theorem _root_.solution {H : SimpleGraph V} {A X Y : Finset V} (hYX : Y ⊆ X) {a v : V} (ha : a ∈ A)
    (p : H.Walk a v) (hp : p.IsPath) (hX : ∀ w ∈ p.support, w ∈ X → w = v) {w : V}
    (hw : w ∈ p.support) (hne : w ≠ v) : R H A Y w := by
  classical
  refine ⟨a, ha, p.takeUntil w hw, fun u hu huY => ?_⟩
  have hu' := p.support_takeUntil_subset_support hw hu
  have := hX u hu' (hYX huY)
  subst this
  exact path_takeUntil_end_not_mem p hp hw hne hu
end Menger.Aux
