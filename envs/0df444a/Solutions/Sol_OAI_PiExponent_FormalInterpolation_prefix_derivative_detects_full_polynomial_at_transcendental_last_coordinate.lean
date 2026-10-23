-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.prefix_derivative_detects_full_polynomial_at_transcendental_last_coordinate
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-23T00:38:03.79141+00:00
-- url     : https://prove2.me/submissions/2d146967-b2c4-4751-acb4-f98081bbcb83

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

noncomputable section

theorem solution :
    ¬ (∀ {n : Nat} (W V : Fin (n + 1) → Rat)
      (hW : ∀ i, 0 < (W i : Real)) (hV : ∀ i, 0 < (V i : Real))
      (E : Type) [Field E] [Algebra Complex E] (x : Fin (n + 1) → E)
      (hlast : ∀ a : Complex, x (Fin.last n) ≠ algebraMap Complex E a)
      (B : Real)
      (hprefix : ∀ T : Nat, 0 < T →
        ∀ U : MvPolynomial (Fin n) Complex, U ≠ 0 →
          fibreContactSupportBound (fun i => W i.castSucc) T U →
          ∃ word : List (Fin n),
            fibreContactWordCost (fun i => V i.castSucc) word ≤ B * (T : Real) ∧
            MvPolynomial.aeval (fun i => x i.castSucc)
              (fibreContactWord word U) ≠ 0)
      (N : Nat) (hN : 0 < N)
      (F : MvPolynomial (Fin (n + 1)) Complex) (hF : F ≠ 0)
      (hbound : fibreContactSupportBound W N F),
      ∃ word : List (Fin (n + 1)),
        (∀ i ∈ word, ∃ j : Fin n, i = j.castSucc) ∧
        fibreContactWordCost V word ≤ B * (N : Real) ∧
        MvPolynomial.aeval x (fibreContactWord word F) ≠ 0) := by
  intro target
  let W : Fin 2 → Rat := fun _ => 1
  let V : Fin 2 → Rat := fun _ => 1
  let x : Fin 2 → RatFunc Complex := fun _ => RatFunc.X
  let F : MvPolynomial (Fin 2) Complex :=
    MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (Fin.last 1)
  have hW : ∀ i, 0 < (W i : Real) := by
    intro i
    norm_num [W]
  have hV : ∀ i, 0 < (V i : Real) := by
    intro i
    norm_num [V]
  have htrans : Transcendental Complex (RatFunc.X : RatFunc Complex) :=
    RatFunc.transcendental_X
  have hlast : ∀ a : Complex,
      x (Fin.last 1) ≠ algebraMap Complex (RatFunc Complex) a := by
    intro a heq
    have hx : (RatFunc.X : RatFunc Complex) =
        algebraMap Complex (RatFunc Complex) a := by
      simpa [x] using heq
    have halg : IsAlgebraic Complex (RatFunc.X : RatFunc Complex) := by
      rw [hx]
      exact isAlgebraic_algebraMap a
    exact htrans halg
  have hAI : AlgebraicIndependent Complex
      (fun _ : Fin 1 => (RatFunc.X : RatFunc Complex)) := by
    rw [algebraicIndependent_unique_type_iff]
    exact htrans
  have hae : Function.Injective
      (MvPolynomial.aeval (fun _ : Fin 1 => RatFunc.X) :
        MvPolynomial (Fin 1) Complex →ₐ[Complex] RatFunc Complex) :=
    algebraicIndependent_iff_injective_aeval.mp hAI
  have hprefix : ∀ T : Nat, 0 < T →
      ∀ U : MvPolynomial (Fin 1) Complex, U ≠ 0 →
        fibreContactSupportBound (fun i => W i.castSucc) T U →
        ∃ word : List (Fin 1),
          fibreContactWordCost (fun i => V i.castSucc) word ≤ 0 * (T : Real) ∧
          MvPolynomial.aeval (fun i => x i.castSucc)
            (fibreContactWord word U) ≠ 0 := by
    intro T hT U hU hUbound
    refine ⟨[], ?_, ?_⟩
    · simp [fibreContactWordCost]
    · simpa [x, fibreContactWord] using
        (fun hz : MvPolynomial.aeval (fun _ : Fin 1 => RatFunc.X) U = 0 =>
          hU (hae hz))
  have hN : 0 < (2 : Nat) := by norm_num
  have hF : F ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun P : MvPolynomial (Fin 2) Complex =>
        P.coeff (Finsupp.single (0 : Fin 2) 1)) hzero
    norm_num [F] at hcoeff
  have hbound : fibreContactSupportBound W 2 F := by
    intro a ha
    by_cases ha0 : a = Finsupp.single (0 : Fin 2) 1
    · subst a
      norm_num [F, W, Finsupp.single_apply]
    by_cases ha1 : a = Finsupp.single (1 : Fin 2) 1
    · have ha1' : a = Finsupp.single (Fin.last 1) 1 := by
        simpa using ha1
      rw [ha1']
      norm_num [F, W, Finsupp.single_apply]
    have hcoeff : F.coeff a ≠ 0 := (MvPolynomial.mem_support_iff).mp ha
    have h0 : Finsupp.single (0 : Fin 2) 1 ≠ a := fun heq => ha0 heq.symm
    have h1 : Finsupp.single (1 : Fin 2) 1 ≠ a := fun heq => ha1 heq.symm
    have hcoeff0 : F.coeff a = 0 := by
      simp [F, MvPolynomial.coeff_X, h0, h1]
    exact (hcoeff hcoeff0).elim
  have hcounter := target (n := 1) W V hW hV (RatFunc Complex) x hlast 0 hprefix 2 hN F hF hbound
  obtain ⟨word, hword, hcost, heval⟩ := hcounter
  have hlen : (word.length : Real) ≤ 0 := by
    simpa [fibreContactWordCost, V] using hcost
  have hlength_le : word.length ≤ 0 := by
    exact_mod_cast hlen
  have hlength : word.length = 0 := Nat.eq_zero_of_le_zero hlength_le
  cases word with
  | nil =>
      have heval_zero :
          MvPolynomial.aeval x (fibreContactWord [] F) = 0 := by
        simp [x, F, fibreContactWord]
      exact heval heval_zero
  | cons i rest =>
      have hlen' : Nat.succ rest.length = 0 := by
        simpa using hlength
      exact (Nat.succ_ne_zero _ hlen').elim