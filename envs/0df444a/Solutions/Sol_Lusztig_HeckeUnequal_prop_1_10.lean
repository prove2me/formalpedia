-- Prove2me | solution 1 for Lusztig.HeckeUnequal.prop_1_10
-- status  : ACCEPTED   (prove)
-- author  : @lookeng
-- created : 2026-11-13T18:09:46.707965+00:00
-- url     : https://prove2.me/submissions/8904f648-9da9-4a5b-a90c-10e6fd4ba22c

import Mathlib.GroupTheory.Coxeter.Length
import Theorems.Thm_Lusztig_HeckeUnequal_prop_1_7

open CoxeterSystem

/-- Case `l(wt) = l(w) + 1` of Lusztig, Prop. 1.10, deduced from Prop. 1.7. -/
private theorem prop_1_10_up {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w : W) (s t : B)
    (hup : cs.length (w * cs.simple t) = cs.length w + 1)
    (h₁ : cs.length (cs.simple s * w * cs.simple t) = cs.length w)
    (h₂ : cs.length (cs.simple s * w) = cs.length (w * cs.simple t)) :
    cs.simple s * w = w * cs.simple t := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hω' : cs.IsReduced (ω ++ [t]) := by
    unfold CoxeterSystem.IsReduced at hω ⊢
    rw [cs.wordProd_append, cs.wordProd_singleton, hup, hω]
    simp
  have hlen : cs.length (cs.simple s * cs.wordProd (ω ++ [t])) =
      cs.length (cs.wordProd (ω ++ [t])) - 1 := by
    rw [cs.wordProd_append, cs.wordProd_singleton, ← mul_assoc, h₁, hup]
    simp
  obtain ⟨j, hj, hjeq⟩ :=
    Lusztig.HeckeUnequal.prop_1_7 cs _ s hlen (ω ++ [t]) hω' rfl
  simp only [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · -- the deleted letter is some `s_{j+1}` of `w`: then `l(sw) ≤ l(w) - 1`, impossible
    exfalso
    rw [List.take_append_of_le_length hj.le,
      List.take_append_of_le_length (Nat.succ_le_of_lt hj)] at hjeq
    have hsw : cs.simple s * cs.wordProd ω =
        cs.wordProd (ω.take j) * cs.wordProd (ω.drop (j + 1)) := by
      have hsplit : cs.wordProd ω = cs.wordProd (ω.take j) *
          (cs.simple (ω[j]'hj) * cs.wordProd (ω.drop (j + 1))) := by
        rw [← cs.wordProd_cons, ← cs.wordProd_append, List.cons_getElem_drop_succ,
          List.take_append_drop]
      have htake : cs.wordProd (ω.take (j + 1)) =
          cs.wordProd (ω.take j) * cs.simple (ω[j]'hj) := by
        rw [List.take_succ_eq_append_getElem hj, cs.wordProd_append, cs.wordProd_singleton]
      rw [hsplit, ← mul_assoc, ← mul_assoc, hjeq, htake, mul_assoc (cs.wordProd _),
        cs.simple_mul_simple_self, mul_one]
    have hle : cs.length (cs.simple s * cs.wordProd ω) ≤ ω.length - 1 := by
      rw [hsw]
      refine (cs.length_mul_le _ _).trans ?_
      have h1 := cs.length_wordProd_le (ω.take j)
      have h2 := cs.length_wordProd_le (ω.drop (j + 1))
      simp only [List.length_take, List.length_drop] at h1 h2
      omega
    rw [h₂, hup, hω] at hle
    omega
  · -- the deleted letter is the final `t`: then `swt = w`
    rw [List.take_left' rfl] at hjeq
    rw [show ω.length + 1 = (ω ++ [t]).length by simp, List.take_length,
      cs.wordProd_append, cs.wordProd_singleton] at hjeq
    exact hjeq

theorem solution {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)
    (w : W) (s t : B)
    (h₁ : cs.length (cs.simple s * w * cs.simple t) = cs.length w)
    (h₂ : cs.length (cs.simple s * w) = cs.length (w * cs.simple t)) :
    cs.simple s * w = w * cs.simple t := by
  rcases cs.length_mul_simple w t with hup | hdown
  · exact prop_1_10_up cs w s t hup h₁ h₂
  · -- Case `l(wt) = l(w) - 1`: apply the first case to `w' = wt`.
    set w' := w * cs.simple t with hw'
    have hw't : w' * cs.simple t = w := cs.simple_mul_simple_cancel_right t
    have key := prop_1_10_up cs w' s t (by rw [hw't]; omega)
      (by rw [hw', ← mul_assoc, cs.simple_mul_simple_cancel_right, h₂])
      (by rw [hw't, hw', ← mul_assoc, h₁])
    rw [hw't, hw', ← mul_assoc] at key
    calc cs.simple s * w = cs.simple s * w * cs.simple t * cs.simple t :=
          (cs.simple_mul_simple_cancel_right t).symm
      _ = w * cs.simple t := by rw [key]
