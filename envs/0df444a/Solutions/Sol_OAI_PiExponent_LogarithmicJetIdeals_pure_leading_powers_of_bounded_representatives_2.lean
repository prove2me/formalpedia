-- Prove2me | solution 2 for OAI.PiExponent.LogarithmicJetIdeals.pure_leading_powers_of_bounded_representatives
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:14:58.71372+00:00
-- url     : https://prove2.me/submissions/b2f152f7-f311-47bf-bd67-faf3c4f34c72

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

theorem h41_bsub (m : ℕ) (w : Fin (m + 1) → ℝ) (D : ℝ) (N : Fin (m + 1) → ℕ) (o : MonomialOrder (Fin (m + 1))) (ho : ∀ i b, (∑ j, w j * (b j : ℝ) ≤ D) → o.toSyn b < o.toSyn (Finsupp.single i (N i))) (i : Fin (m + 1)) (Q : MvPolynomial (Fin (m + 1)) ℂ) (hQ : ∀ b ∈ Q.support, ∑ j, w j * (b j : ℝ) ≤ D) : (o.leadingCoeff (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q) = 1) ∧ (o.degree (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q) = Finsupp.single i (N i)) := by
  classical
  have hdm : o.degree (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ)) = Finsupp.single i (N i) := by
    rw [o.degree_monomial]; simp
  have hlm : o.leadingCoeff (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ)) = 1 := by
    rw [o.leadingCoeff_monomial]
  by_cases hQ0 : Q = 0
  · subst hQ0; simp only [sub_zero]; exact ⟨hlm, hdm⟩
  have hlt : o.toSyn (o.degree Q) < o.toSyn (o.degree (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ))) := by
    rw [hdm]
    exact ho i _ (hQ _ (o.degree_mem_support hQ0))
  exact ⟨(o.leadingCoeff_sub_of_lt hlt).trans hlm, (o.degree_sub_of_lt hlt).trans hdm⟩

theorem solution
    (m : ℕ) (w : Fin (m + 1) → ℝ) (hw : ∀ i, 0 < w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (D : ℝ) (hD : 0 ≤ D)
    (hrep : ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
        P - Q ∈ I ∧
        ∀ b ∈ Q.support, ∑ i, w i * (b i : ℝ) ≤ D) :
    ∃ (N : Fin (m + 1) → ℕ)
      (o : MonomialOrder (Fin (m + 1)))
      (f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ),
      (∀ i, 0 < N i) ∧
      (∀ i, f i ∈ I) ∧
      (∀ i, o.leadingCoeff (f i) = 1) ∧
      (∀ i, o.degree (f i) = Finsupp.single i (N i)) ∧
      (∀ i, (N i : ℝ) * w i ≤ D + w i) := by
  classical
  have hNex : ∀ i, ∃ N : ℕ, 0 < N ∧ D < (N : ℝ) * w i ∧ (N : ℝ) * w i ≤ D + w i := by
    intro i
    have hwi := hw i
    refine ⟨⌊D / w i⌋₊ + 1, Nat.succ_pos _, ?_, ?_⟩
    · have := Nat.lt_floor_add_one (D / w i)
      rw [div_lt_iff₀ hwi] at this
      push_cast; linarith
    · have h1 : (⌊D / w i⌋₊ : ℝ) ≤ D / w i := Nat.floor_le (div_nonneg hD hwi.le)
      have h2 : (⌊D / w i⌋₊ : ℝ) * w i ≤ D := by rwa [le_div_iff₀ hwi] at h1
      push_cast; linarith
  choose N hN0 hND hNle using hNex
  have ho : ∀ i b, (∑ j, w j * (b j : ℝ) ≤ D) →
      (h41order w (fun i => (hw i).le)).toSyn b <
        (h41order w (fun i => (hw i).le)).toSyn (Finsupp.single i (N i)) := by
    intro i b hb
    rw [h41order_lt]
    unfold h41key
    rw [Prod.Lex.toLex_lt_toLex]
    left
    have : ∑ j, w j * ((Finsupp.single i (N i) j : ℕ) : ℝ) = (N i : ℝ) * w i := by
      rw [Finset.sum_eq_single i]
      · simp [mul_comm]
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    dsimp only
    rw [this]; linarith [hND i]
  have h := fun i => hrep (MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ))
  choose Q hQI hQw using h
  refine ⟨N, h41order w (fun i => (hw i).le),
    fun i => MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) - Q i, hN0, hQI,
    fun i => ?_, fun i => ?_, hNle⟩
  · exact (h41_bsub m w D N _ ho i (Q i) (hQw i)).1
  · exact (h41_bsub m w D N _ ho i (Q i) (hQw i)).2

