-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.weighted_dominating_monomialOrder
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:14:18.872002+00:00
-- url     : https://prove2.me/submissions/63ae57d8-24df-4477-b3fd-5035e77d83b1

import Mathlib
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Complex.Basic

open scoped BigOperators
universe u41

def h41Syn (m : ℕ) (w : Fin (m + 1) → ℝ) : Type u41 := ULift.{u41} (Fin (m + 1) →₀ ℕ)

noncomputable def h41key {m : ℕ} (w : Fin (m + 1) → ℝ) (a : Fin (m + 1) →₀ ℕ) :
    Lex (ℝ × Lex (Fin (m + 1) →₀ ℕ)) :=
  toLex (∑ j, w j * (a j : ℝ), toLex a)

theorem h41key_inj {m : ℕ} (w : Fin (m + 1) → ℝ) : Function.Injective (h41key w) := by
  intro a b h
  have := congrArg (fun x => (ofLex x).2) h
  simpa [h41key] using this

noncomputable instance h41Syn.acm (m : ℕ) (w : Fin (m + 1) → ℝ) : AddCommMonoid (h41Syn.{u41} m w) :=
  inferInstanceAs (AddCommMonoid (ULift.{u41} (Fin (m + 1) →₀ ℕ)))

noncomputable instance h41Syn.lo (m : ℕ) (w : Fin (m + 1) → ℝ) : LinearOrder (h41Syn.{u41} m w) :=
  LinearOrder.lift' (fun a : ULift.{u41} (Fin (m + 1) →₀ ℕ) => h41key w a.down)
    (fun a b h => ULift.ext _ _ (h41key_inj w h))

theorem h41Syn_le_iff {m : ℕ} {w : Fin (m + 1) → ℝ} (a b : ULift.{u41} (Fin (m + 1) →₀ ℕ)) :
    (show h41Syn.{u41} m w from a) ≤ (show h41Syn.{u41} m w from b) ↔ h41key w a.down ≤ h41key w b.down :=
  Iff.rfl

theorem h41W_add {m : ℕ} (w : Fin (m + 1) → ℝ) (a c : Fin (m + 1) →₀ ℕ) :
    ∑ j, w j * ((a + c) j : ℝ) = ∑ j, w j * (a j : ℝ) + ∑ j, w j * (c j : ℝ) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add]; ring

theorem h41key_add_le {m : ℕ} {w : Fin (m + 1) → ℝ} {a b : Fin (m + 1) →₀ ℕ}
    (h : h41key w a ≤ h41key w b) (c : Fin (m + 1) →₀ ℕ) : h41key w (a + c) ≤ h41key w (b + c) := by
  unfold h41key at h ⊢
  rw [Prod.Lex.toLex_le_toLex] at h ⊢
  simp only [h41W_add]
  rcases h with h | ⟨h1, h2⟩
  · left; dsimp only at h ⊢; linarith
  · right; dsimp only at h1 h2 ⊢; refine ⟨by rw [h1], ?_⟩
    simp only [toLex_add]
    exact add_le_add_left h2 _

instance h41Syn.ioam (m : ℕ) (w : Fin (m + 1) → ℝ) : IsOrderedAddMonoid (h41Syn.{u41} m w) where
  add_le_add_left a b h c := h41key_add_le (a := a.down) (b := b.down) h c.down

theorem h41key_mono {m : ℕ} {w : Fin (m + 1) → ℝ} (hw : ∀ i, 0 ≤ w i) {a b : Fin (m + 1) →₀ ℕ}
    (h : a ≤ b) : h41key w a ≤ h41key w b := by
  unfold h41key
  rw [Prod.Lex.toLex_le_toLex]
  have hle : ∑ j, w j * (a j : ℝ) ≤ ∑ j, w j * (b j : ℝ) :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (by exact_mod_cast h j) (hw j))
  rcases hle.lt_or_eq with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨h1, Finsupp.toLex_monotone h⟩

theorem h41Syn_wqo {m : ℕ} {w : Fin (m + 1) → ℝ} (hw : ∀ i, 0 ≤ w i) :
    WellQuasiOrderedLE (h41Syn.{u41} m w) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨i, j, hij, hle⟩ := (wellQuasiOrdered_le (α := Fin (m + 1) → ℕ))
    (fun k => ⇑((f k : ULift.{u41} (Fin (m + 1) →₀ ℕ)).down))
  exact ⟨i, j, hij, h41key_mono hw (fun t => hle t)⟩

theorem h41Syn_wf {m : ℕ} {w : Fin (m + 1) → ℝ} (hw : ∀ i, 0 ≤ w i) :
    WellFoundedLT (h41Syn.{u41} m w) := by
  have := h41Syn_wqo.{u41} hw
  infer_instance

noncomputable def h41order {m : ℕ} (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) :
    MonomialOrder.{0, u41} (Fin (m + 1)) where
  syn := h41Syn.{u41} m w
  toSyn := AddEquiv.ulift.symm
  toSyn_monotone a b h := h41key_mono hw h
  wellFoundedLT_syn := h41Syn_wf hw

theorem h41order_lt {m : ℕ} (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) (a b : Fin (m + 1) →₀ ℕ) :
    (h41order.{u41} w hw).toSyn a < (h41order.{u41} w hw).toSyn b ↔ h41key w a < h41key w b :=
  Iff.rfl

theorem solution (m : ℕ) (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i) (D : ℝ) (N : Fin (m + 1) → ℕ) (hN : ∀ i, D < (N i : ℝ) * w i) : ∃ o : MonomialOrder (Fin (m + 1)), ∀ i b, (∑ j, w j * (b j : ℝ) ≤ D) → o.toSyn b < o.toSyn (Finsupp.single i (N i)) := by
  refine ⟨h41order w (fun i => (hw i).le), fun i b hb => ?_⟩
  rw [h41order_lt]
  unfold h41key
  rw [Prod.Lex.toLex_lt_toLex]
  left
  have : ∑ j, w j * ((Finsupp.single i (N i) j : ℕ) : ℝ) = (N i : ℝ) * w i := by
    rw [Finset.sum_eq_single i]
    · simp [mul_comm]
    · intro j _ hj; simp [Finsupp.single_apply, Ne.symm hj]
    · simp
  dsimp only
  rw [this]; linarith [hN i]

