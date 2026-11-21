-- Prove2me | solution 1 for GwExact.isGood_of_goodB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:18:21.146102+00:00
-- url     : https://prove2.me/submissions/7ef6babd-97e5-4b74-87d6-9bf8311e39b0

module
public import Definitions.Def_GwExact_Defs
public import Definitions.Def_GwExact_Lower

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {r l n : ℕ} {c : ℕ → Fin r} (hl : 2 ≤ l) (h : goodB r l n c = true) :
    IsGoodExactColouring r l n c := by
  simp only [goodB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨hall, hrb⟩, hmono⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro col
    obtain ⟨x, -, ⟨hx1, hx2⟩, hx3⟩ := hall col.val col.isLt
    exact ⟨x, hx1, hx2, Fin.ext hx3⟩
  · intro x d hx hd hxd ⟨h1, h2, h3⟩
    rcases hrb x (by omega) d (by omega) with (⟨h | h⟩ | h) | ((h | h) | h)
    · omega
    · omega
    · omega
    · exact h (Fin.val_ne_of_ne h1)
    · exact h (Fin.val_ne_of_ne h2)
    · exact h (Fin.val_ne_of_ne h3)
  · intro x d hx hd hxd hall'
    have hdl : d ≤ (l - 1) * d := Nat.le_mul_of_pos_left d (by omega)
    rcases hmono x (by omega) d (by omega) with (⟨h | h⟩ | h) | ⟨j, hj, hne⟩
    · omega
    · omega
    · omega
    · exact hne (congrArg Fin.val (hall' j hj))
end GwExact
