-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_adjoin_of_strict_monic_relations
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T23:16:21.186986+00:00
-- url     : https://prove2.me/submissions/9520f1b7-e75e-492d-b433-c1f49e04dd42

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Finiteness.Defs

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
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

theorem h41key_lt_of_weight {m : ℕ} {w : Fin (m + 1) → ℝ} {a b : Fin (m + 1) →₀ ℕ}
    (h : ∑ j, w j * (a j : ℝ) < ∑ j, w j * (b j : ℝ)) : h41key w a < h41key w b := by
  unfold h41key
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

theorem solution
    {m : Nat}
    (w : Fin (m + 1) → Real)
    (I : Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (s : Nat) (D : Real)
    (N : Fin (m + 1) → Nat)
    (r f : Fin (m + 1) → MvPolynomial (Fin (m + 1)) Complex)
    (hN : ∀ i, 0 < N i)
    (hf : ∀ i, f i = MvPolynomial.X i ^ N i - r i)
    (hmem : ∀ i, f i ∈ I ^ s)
    (hbound : ∀ i, ∀ a ∈ (f i).support,
      ∑ j, w j * (a j : Real) ≤ D)
    (hNbound : ∀ i, (N i : Real) * w i ≤ D)
    (hlow : ∀ i, ∀ a ∈ (r i).support,
      ∑ j, w j * (a j : Real) < (N i : Real) * w i)
    (hw : ∀ i, 0 < w i) :
    Module.Finite (Algebra.adjoin Complex (Set.range f))
      (MvPolynomial (Fin (m + 1)) Complex) := by
  classical
  set A := Algebra.adjoin ℂ (Set.range f) with hA
  let W : (Fin (m + 1) →₀ ℕ) → ℝ := fun b => ∑ j, w j * (b j : ℝ)
  let T : Finset (Fin (m + 1) →₀ ℕ) :=
    (Fintype.piFinset (fun i => Finset.range (N i))).image (Finsupp.equivFunOnFinite.symm)
  let S : Finset (MvPolynomial (Fin (m + 1)) ℂ) := T.image (fun c => MvPolynomial.monomial c (1 : ℂ))
  let M : Submodule A (MvPolynomial (Fin (m + 1)) ℂ) := Submodule.span A (S : Set _)
  let o := h41order.{0} w (fun i => (hw i).le)
  have hWlt : ∀ a b, W a < W b → o.toSyn a < o.toSyn b := by
    intro a b h
    rw [h41order_lt]
    exact h41key_lt_of_weight h
  have hmon : ∀ a, MvPolynomial.monomial a (1 : ℂ) ∈ M := by
    intro a
    obtain ⟨s, rfl⟩ : ∃ s, o.toSyn.symm s = a := ⟨o.toSyn a, by simp⟩
    induction s using WellFoundedLT.induction with
    | _ s ih =>
    by_cases hsmall : ∀ i, (o.toSyn.symm s) i < N i
    · apply Submodule.subset_span
      simp only [S, T, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      refine ⟨o.toSyn.symm s, ⟨fun i => (o.toSyn.symm s) i, ?_, ?_⟩, rfl⟩
      · simp only [Fintype.mem_piFinset, Finset.mem_range]; exact hsmall
      · ext i; simp
    push Not at hsmall
    obtain ⟨i, hi⟩ := hsmall
    set a := o.toSyn.symm s with ha
    set a' := a - Finsupp.single i (N i) with ha'
    have hsplit : a' + Finsupp.single i (N i) = a :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hi)
    have hWadd : ∀ x y : Fin (m + 1) →₀ ℕ, W (x + y) = W x + W y := fun x y => h41W_add w x y
    have hWsingle : W (Finsupp.single i (N i)) = (N i : ℝ) * w i := by
      show ∑ j, w j * ((Finsupp.single i (N i) j : ℕ) : ℝ) = _
      rw [Finset.sum_eq_single i]
      · simp [mul_comm]
      · intro j _ hj; simp [Ne.symm hj]
      · simp
    have hpos : 0 < (N i : ℝ) * w i := mul_pos (by exact_mod_cast hN i) (hw i)
    have hIH : ∀ b, W b < W a → MvPolynomial.monomial b (1 : ℂ) ∈ M := by
      intro b hb
      have := ih (o.toSyn b) (by
        have h1 := hWlt b a hb
        rw [ha] at h1; simpa using h1)
      simpa using this
    have hXa : MvPolynomial.monomial a (1 : ℂ) =
        f i * MvPolynomial.monomial a' (1 : ℂ) + MvPolynomial.monomial a' (1 : ℂ) * r i := by
      have : f i + r i = MvPolynomial.monomial (Finsupp.single i (N i)) (1 : ℂ) := by
        rw [hf i, MvPolynomial.X_pow_eq_monomial]; ring
      rw [mul_comm (f i), ← mul_add, this, MvPolynomial.monomial_mul, mul_one, hsplit]
    rw [hXa]
    refine M.add_mem ?_ ?_
    · have hm : MvPolynomial.monomial a' (1 : ℂ) ∈ M := hIH a' (by
        rw [← hsplit, hWadd, hWsingle]; linarith)
      have hfA : f i ∈ A := Algebra.subset_adjoin ⟨i, rfl⟩
      exact M.smul_mem (⟨f i, hfA⟩ : A) hm
    · conv => arg 2; rw [(r i).as_sum, Finset.mul_sum]
      refine M.sum_mem (fun c hc => ?_)
      rw [MvPolynomial.monomial_mul, one_mul]
      have hc' : MvPolynomial.monomial (a' + c) (MvPolynomial.coeff c (r i)) =
          MvPolynomial.coeff c (r i) • MvPolynomial.monomial (a' + c) (1 : ℂ) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [hc']
      refine Submodule.smul_of_tower_mem M _ (hIH _ ?_)
      rw [← hsplit, hWadd, hWadd, hWsingle]
      have := hlow i c hc
      show W a' + W c < _
      have : W c < (N i : ℝ) * w i := this
      linarith
  refine ⟨⟨S, ?_⟩⟩
  refine eq_top_iff.2 (fun p _ => ?_)
  rw [p.as_sum]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  have : MvPolynomial.monomial a (MvPolynomial.coeff a p) =
      MvPolynomial.coeff a p • MvPolynomial.monomial a (1 : ℂ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_of_tower_mem _ _ (hmon a)

