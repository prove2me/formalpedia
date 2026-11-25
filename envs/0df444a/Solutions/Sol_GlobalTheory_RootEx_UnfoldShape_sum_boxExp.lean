-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.sum_boxExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:45:27.469365+00:00
-- url     : https://prove2.me/submissions/e12895fa-6d3f-4e88-a016-5c78326a1b42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat
import Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_sum_fin_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
namespace GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution (n n' : Type) [Fintype n] [Fintype n'] (c : ℕ) :
    ∑ rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)), boxExp rs = expo c (Fintype.card n) := by
  rw [Fintype.sum_prod_type_right, Fintype.sum_sum_type]
  simp only [Fintype.sum_sum_type, boxExp, Finset.sum_const_zero, zero_add,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h : ∀ j : Fin (c + 1), Fintype.card n * j.val + ∑ l : Fin c, (j.val - (l.val + 1))
      = j.val * Fintype.card n + j.val * (j.val - 1) / 2 := by
    intro j
    rw [sum_fin_sub c j (by omega), mul_comm]
  rw [Finset.sum_congr rfl fun j _ => h j,
    Fin.sum_univ_eq_sum_range (fun j => j * Fintype.card n + j * (j - 1) / 2) (c + 1), expo]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_Icc, Finset.mem_range] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_Icc, Finset.mem_range] at hx hx'
    obtain rfl : x = 0 := by omega
    simp
end GlobalTheory.RootEx.UnfoldShape
