-- Prove2me | solution 1 for GlobalTheory.exists_compatible_seq_of_finite_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:08.355238+00:00
-- url     : https://prove2.me/submissions/c140630d-647f-478c-a85f-f2c866d22baf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCompatibleSeqOfFiniteNonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n))
    (hfin : ∀ n, (Y n).Finite) (hne : ∀ n, (Y n).Nonempty)
    (hmap : ∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) :
    ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by
  classical
  let g : ∀ n, ((Y (n + 1) : Set (X (n + 1))) : Type) ⟶ ((Y n : Set (X n)) : Type) :=
    fun n => TypeCat.ofHom (fun x => ⟨f n x.1, hmap n x.1 x.2⟩)
  let F : ℕᵒᵖ ⥤ Type := Functor.ofOpSequence (X := fun n => ((Y n : Set (X n)) : Type)) g
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun n => (u (Opposite.op n)).1, fun n => ⟨(u (Opposite.op n)).2, ?_⟩⟩
  have h := hu (homOfLE (Nat.le_add_right n 1)).op
  have hm : F.map (homOfLE (Nat.le_add_right n 1)).op = g n :=
    Functor.ofOpSequence_map_homOfLE_succ (X := fun n => ((Y n : Set (X n)) : Type)) g n
  rw [hm] at h
  exact congrArg Subtype.val h
end GlobalTheory
