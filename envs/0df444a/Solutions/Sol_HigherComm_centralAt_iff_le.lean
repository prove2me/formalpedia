-- Prove2me | solution 1 for HigherComm.centralAt_iff_le
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T07:38:31.60546+00:00
-- url     : https://prove2.me/submissions/750f1b7f-838f-41f7-aa4a-d78060ddf345

import Definitions.Def_HigherComm_defs
import Theorems.Thm_HigherComm_shift_rotation
import Theorems.Thm_HigherComm_centralAt_of_centralAt

universe u₁ v₁ w₁

set_option linter.unusedSectionVars false

open FirstOrder FirstOrder.Language

namespace HigherComm
namespace HCUp

variable {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]

/-- Vertex bookkeeping: the base vertex `g` of a cross-section square ignores the
coordinate `l`. -/
theorem base_update_l {K : ℕ} (j l : Fin K) (f : Fin K → Bool) (c : Bool) :
    Function.update (Function.update (Function.update f l c) j false) l false =
      Function.update (Function.update f j false) l false := by
  funext i; simp only [Function.update_apply]; split_ifs <;> simp_all

/-- The descending step of Moorhead's generator argument (Lemma 4.3), for a fixed `δ`:
`Q i` says that every `h ∈ M(T)` whose `(i)`-supporting lines are `δ`-pairs and whose
`(i)`-lines at vertices with some coordinate `< i` equal to `0` are constant has its
`(i)`-pivot line in `δ`. -/
def Q {k : ℕ} (T : Fin (k + 2) → Congruence (L := L) M) (δ : Congruence (L := L) M) (i : ℕ)
    (hi : i < k + 2) : Prop :=
  ∀ h, IsTMatrix T h → SupportingRel δ h ⟨i, hi⟩ →
    (∀ f : Fin (k + 2) → Bool, (∃ j : Fin (k + 2), j.val < i ∧ f j = false) →
      h (Function.update f ⟨i, hi⟩ false) = h (Function.update f ⟨i, hi⟩ true)) →
    PivotRel δ h ⟨i, hi⟩

theorem Q_top [L.IsAlgebraic] {k : ℕ} (T : Fin (k + 2) → Congruence (L := L) M)
    (δ : Congruence (L := L) M) (hle : higherComm T ≤ δ) : Q T δ (k + 1) (by omega) := by
  intro h hh _ hb
  apply hle
  intro δ' hδ'
  apply hδ' h hh
  intro f ⟨j, hj, hfj⟩
  have hjv : j.val < k + 1 := by
    have : j.val ≠ k + 1 := fun e => hj (Fin.ext e)
    omega
  unfold LineRel
  rw [show Fin.last (k + 1) = ⟨k + 1, by omega⟩ from rfl, hb f ⟨j, hjv, hfj⟩]

theorem Q_step {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (δ : Congruence (L := L) M) (i : ℕ)
    (hi : i + 1 < k + 2) (hQ : Q T δ (i + 1) hi) : Q T δ i (by omega) := by
  set J : Fin (k + 2) := ⟨i, by omega⟩ with hJ
  set Lc : Fin (k + 2) := ⟨i + 1, hi⟩ with hLc
  have hJL : J ≠ Lc := by simp [hJ, hLc, Fin.ext_iff]
  have hLJ : Lc ≠ J := Ne.symm hJL
  obtain ⟨R, hR⟩ := shift_rotation m hm T J Lc hJL
  intro h hh hS hb
  obtain ⟨hmem, hform, h2, h3⟩ := hR h hh
  have hb' : ∀ e (f : Fin (k + 2) → Bool), (∃ j : Fin (k + 2), j.val < i + 1 ∧ f j = false) →
      R e h (Function.update f Lc false) = R e h (Function.update f Lc true) := by
    intro e f ⟨j, hj, hfj⟩
    rw [hform e, hform e]
    simp only [base_update_l, Function.update_of_ne hJL, Function.update_self]
    set g := Function.update (Function.update f J false) Lc false with hg
    cases hfJ : f J
    · rfl
    · simp only [if_true, if_false, Bool.false_eq_true]
      have hjJ : j ≠ J := by rintro rfl; simp_all
      have hjv : j.val < i := by
        have : j.val ≠ i := fun e => hjJ (Fin.ext e)
        omega
      have hjL : j ≠ Lc := by
        intro e; rw [e] at hjv; simp [hLc] at hjv
      have hru : h g = h (Function.update g J true) := by
        have := hb g ⟨j, hjv, by
          simp [hg, Function.update_of_ne hjL, Function.update_of_ne hjJ, hfj]⟩
        have vg : Function.update g J false = g := by
          funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
        rwa [vg] at this
      have hsv : h (Function.update g Lc true) =
          h (Function.update (Function.update g J true) Lc true) := by
        have := hb (Function.update g Lc true) ⟨j, hjv, by
          simp [hg, Function.update_of_ne hjL, Function.update_of_ne hjJ, hfj]⟩
        have w1 : Function.update (Function.update g Lc true) J false =
            Function.update g Lc true := by
          funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
        have w2 : Function.update (Function.update g Lc true) J true =
            Function.update (Function.update g J true) Lc true :=
          Function.update_comm hLJ _ _ _
        rwa [w1, w2] at this
      rw [← hru, ← hsv, hm.1, hm.1]
  have hpiv : ∀ e, PivotRel δ (R e h) Lc := fun e =>
    hQ (R e h) (hmem e) (h2 δ hS e) (hb' e)
  have hL : LineRel δ h J (Function.update (fun _ => true) Lc false) :=
    hS _ ⟨Lc, hLJ, by simp⟩
  exact (h3 δ hL).mpr hpiv

theorem Q_all [L.IsAlgebraic] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (δ : Congruence (L := L) M)
    (hle : higherComm T ≤ δ) : ∀ d i (hi : i < k + 2), i + d = k + 1 → Q T δ i hi := by
  intro d
  induction d with
  | zero => intro i hi hd; obtain rfl : i = k + 1 := by omega
            exact Q_top T δ hle
  | succ d ih =>
    intro i hi hd
    exact Q_step m hm T δ i (by omega) (ih (i + 1) (by omega) (by omega))

theorem up_main [L.IsAlgebraic] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4))
    (hm : IsDayTerms M m) (T : Fin (k + 2) → Congruence (L := L) M) (j : Fin (k + 2))
    (δ : Congruence (L := L) M) : CentralAt T j δ ↔ higherComm T ≤ δ := by
  constructor
  · intro h x y hxy
    exact hxy δ (centralAt_of_centralAt m hm T δ j h _)
  · intro hle
    have h0 : CentralAt T ⟨0, by omega⟩ δ := by
      intro h hh hS
      exact Q_all m hm T δ hle (k + 1) 0 (by omega) (by omega) h hh hS
        (fun f ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero _))
    exact centralAt_of_centralAt m hm T δ _ h0 j

end HCUp
end HigherComm

theorem solution {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]
    [L.IsAlgebraic] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : HigherComm.IsDayTerms M m)
    (T : Fin (k + 2) → HigherComm.Congruence (L := L) M) (j : Fin (k + 2))
    (δ : HigherComm.Congruence (L := L) M) :
    HigherComm.CentralAt T j δ ↔ HigherComm.higherComm T ≤ δ :=
  HigherComm.HCUp.up_main m hm T j δ
