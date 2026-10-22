-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_separated_derivative_rigidity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-21T13:39:35.536208+00:00
-- url     : https://prove2.me/submissions/c88496f5-5b54-4894-bf84-8e44ace26acb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_nonconstant_has_detectable_derivative

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution
    {m : Nat} (w v : Fin (m + 1) → Rat) (sigma : Rat)
    (hm : 1 ≤ m) (hsigma : 0 < (sigma : Real))
    (hw : ∀ i, 0 < (w i : Real)) (hv : ∀ i, 0 < (v i : Real))
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
        (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
        interpolationSeparationConstant m sigma *
          (∏ j ∈ B, (v j : Real)) < ∏ j ∈ A, (w j : Real))
    (E : Type) [Field E] [Algebra Complex E] (x : Fin m → E) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N → 0 < N →
      ∀ F : MvPolynomial (Fin m) Complex, F ≠ 0 →
        fibreContactSupportBound (fun i => w i.succ) N F →
        (∀ word : List (Fin m),
          fibreContactWordCost (fun i => v i.succ) word ≤
            (sigma : Real) * (N : Real) →
          MvPolynomial.aeval x (fibreContactWord word F) = 0) →
        ∃ (i : Fin m) (a : Complex), x i = algebraMap Complex E a := by
  classical
  obtain ⟨N0, hN0⟩ :=
    OAI.PiExponent.FormalInterpolation.fibreContact_nonconstant_has_detectable_derivative
      (w := w) (v := v) (sigma := sigma) hm hsigma hw hv hseparated E x
  refine ⟨N0, ?_⟩
  intro N hN hNpos F hF hsupport hvanish
  by_contra hcoordinate
  push_neg at hcoordinate
  obtain ⟨word, hcost, hnonzero⟩ :=
    hN0 N hN hNpos F hF hsupport hvanish hcoordinate
  exact hnonzero (hvanish word hcost)
