-- Prove2me | solution 1 for GlobalTheory.exists_nsmul_add_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:45:46.488168+00:00
-- url     : https://prove2.me/submissions/2d2f9f49-f979-425f-ba26-86d5aeb8b933

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfEvalGridEqZeroOfTotalDegreeLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] {W : ι → Type*}
  [∀ j, AddCommGroup (W j)]
namespace GlobalTheory
theorem _root_.solution [∀ j, IsAddTorsionFree (W j)] (l : ∀ j, V →+ W j)
    (v w : V) :
    ∃ c : ℕ, c ≤ Fintype.card ι ∧ ∀ j, l j v ≠ 0 ∨ l j w ≠ 0 → l j (c • w + v) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  choose f hf hf0 using h
  have hinj : Function.Injective fun a : Fin (Fintype.card ι + 1) =>
      f a (Nat.lt_succ_iff.1 a.2) := by
    intro a b hab
    have h1 := hf0 a (Nat.lt_succ_iff.1 a.2)
    have h2 := hf0 b (Nat.lt_succ_iff.1 b.2)
    have h3 := hf a (Nat.lt_succ_iff.1 a.2)
    simp only at hab
    rw [← hab] at h2
    generalize f a _ = j at h1 h2 h3
    rw [map_add, map_nsmul] at h1 h2
    have hw : l j w ≠ 0 := by
      intro hw
      rw [hw, nsmul_zero, zero_add] at h1
      exact h3.elim (· h1) (· hw)
    have h4 : (a : ℕ) • l j w = (b : ℕ) • l j w := add_right_cancel (h1.trans h2.symm)
    have h5 : ((a : ℤ) - (b : ℤ)) • l j w = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul, h4, sub_self]
    have h6 := (smul_eq_zero.1 h5).resolve_right hw
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective _ hinj
  simp at this
end GlobalTheory
