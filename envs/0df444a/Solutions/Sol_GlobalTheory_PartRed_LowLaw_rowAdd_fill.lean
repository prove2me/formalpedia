-- Prove2me | solution 1 for GlobalTheory.PartRed.LowLaw.rowAdd_fill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:17:12.333091+00:00
-- url     : https://prove2.me/submissions/184ff65a-d93f-4abe-bfa6-94c85656822a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLaw
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_rowAdd_mul_apply
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_fill_row_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.PartRed GlobalTheory.PartRed.LowLaw
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
namespace GlobalTheory.PartRed.LowLaw
theorem _root_.solution (ρ : ℕ) (l r : Fin c) (i : Fin (c + 1)) (hi : ρ < i.val) (hil : i.val ≤ l.val)
    (hr : r.val + 1 = i.val) (E : Finset ((n ⊕ Fin c) × (n' ⊕ Fin (c + 1)))) (hfix : fixSet ρ ⊆ E)
    (hlow : (lowSet ρ).filter (fun e => colIx e < i.val) ⊆ E) (b : k)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : (transSet (n := n) (n' := n') (c := c) ρ) → k) :
    (fromBlocks 1 0 0 (transvection r l b) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) *
        fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y =
      fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x (y + fun j => if j.1.1 = Sum.inr r then
        b * fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) j.1.2 else 0) := by
  ext p q
  rw [rowAdd_mul_apply]
  by_cases hpq : (p, q) ∈ transSet (n := n) (n' := n') (c := c) ρ
  · conv_rhs => rw [fillAt, of_apply, dif_pos hpq]
    conv_lhs => rw [fillAt, of_apply, dif_pos hpq]
    rfl
  · have h0 : (if p = Sum.inr r then
        b * fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) q else 0) = 0 := by
      split_ifs with hp
      · subst hp
        rw [fill_row_zero ρ l r i hi hil hr E hfix hlow x y q hpq, mul_zero]
      · rfl
    rw [h0, add_zero]
    simp only [fillAt, of_apply, dif_neg hpq]
end GlobalTheory.PartRed.LowLaw
