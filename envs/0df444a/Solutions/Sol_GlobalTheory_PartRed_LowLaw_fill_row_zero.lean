-- Prove2me | solution 1 for GlobalTheory.PartRed.LowLaw.fill_row_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:07:26.150998+00:00
-- url     : https://prove2.me/submissions/aaf1dbf0-ff2c-4451-b850-e5b8a4b61784

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IntegralCoordinateShearHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionLowerEntryMultiplicationLaw
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_mem_trans
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_mem_fix
import Theorems.Thm_GlobalTheory_PartRed_LowLaw_mem_low

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
    (hlow : (lowSet ρ).filter (fun e => colIx e < i.val) ⊆ E)
    (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : (transSet (n := n) (n' := n') (c := c) ρ) → k)
    (q : n' ⊕ Fin (c + 1)) (hq : (Sum.inr r, q) ∉ transSet (n := n) (n' := n') (c := c) ρ) :
    fillAt (basePt c (0 : Matrix n n' k)) E (transSet ρ) x y (Sum.inr l) q = 0 := by
  simp only [fillAt, of_apply]
  rcases q with s | j
  · have h1 : (Sum.inr l, Sum.inl s) ∉ transSet (n := n) (n' := n') (c := c) ρ := by
      rw [mem_trans]; simp [Free]; omega
    have h2 : (Sum.inr l, Sum.inl s) ∈ E := hfix (by rw [mem_fix]; right; exact ⟨l, s, rfl, by omega, rfl⟩)
    rw [dif_neg h1, if_pos h2]
    simp [basePt]
  · rw [mem_trans] at hq
    simp [Free] at hq
    have hj : j.val ≤ r.val := by omega
    have h1 : (Sum.inr l, Sum.inr j) ∉ transSet (n := n) (n' := n') (c := c) ρ := by
      rw [mem_trans]; simp [Free]; omega
    have h2 : (Sum.inr l, Sum.inr j) ∈ E := by
      by_cases hjρ : j.val ≤ ρ
      · exact hfix (by rw [mem_fix]; left; exact ⟨j, rfl, hjρ, by simp [Free]; omega⟩)
      · exact hlow (by
          rw [Finset.mem_filter, mem_low]
          exact ⟨⟨l, j, rfl, by omega, by omega⟩, by simp [colIx]; omega⟩)
    have hlj : l.val ≠ j.val := by omega
    rw [dif_neg h1, if_pos h2]
    simp [basePt, hlj]
end GlobalTheory.PartRed.LowLaw
