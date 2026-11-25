-- Prove2me | solution 1 for GrahamPollak.exists_bicliqueDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:15:39.469845+00:00
-- url     : https://prove2.me/submissions/da9458c3-65b4-46fe-87ac-246fe50d5481

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak

set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}
namespace GrahamPollak
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ A B : Fin (n - 1) → Finset (Fin n), IsBicliqueDecomposition A B := by
  refine ⟨fun i => {⟨i.val, by omega⟩},
    fun i => Finset.univ.filter (fun v : Fin n => i.val < v.val), ?_, ?_⟩
  · intro i
    simp
  · intro u v huv
    have huv' : u.val ≠ v.val := fun h => huv (Fin.ext h)
    rw [Finset.card_eq_one]
    refine ⟨⟨min u.val v.val, by omega⟩, ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.ext_iff]
    omega
end GrahamPollak
