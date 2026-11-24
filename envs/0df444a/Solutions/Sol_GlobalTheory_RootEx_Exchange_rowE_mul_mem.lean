-- Prove2me | solution 1 for GlobalTheory.RootEx.Exchange.rowE_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:16:50.028252+00:00
-- url     : https://prove2.me/submissions/4d93c200-51cd-4807-946d-8383d6f7afb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Theorems.Thm_GlobalTheory_RootEx_Exchange_rowE_mul_inl
import Theorems.Thm_GlobalTheory_RootEx_Exchange_rowE_mul_inr
import Theorems.Thm_GlobalTheory_RootEx_Exchange_mul_rowE_inr
import Theorems.Thm_GlobalTheory_RootEx_Exchange_mul_rowE_inl
import Theorems.Thm_GlobalTheory_RootEx_Exchange_rowE_neg_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.Exchange
theorem _root_.solution (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c (P.val + 1 + 1)) :
    ∃ w : n → k, ∀ u : n → k, ∃ h ∈ N k n c (P.val + 1), simpleSum h = simpleSum g ∧
      rowE c (P.val + 1) u * g = h * rowE c (P.val + 1) (u + w) := by
  rw [Model.mem_N_iff] at hg
  have h11 : ∀ r s, g.val (Sum.inl r) (Sum.inl s) = if r = s then 1 else 0 := fun r s => by
    simpa [Matrix.one_apply] using hg (Sum.inl r) (Sum.inl s) le_rfl
  have h12 : ∀ r (s : Fin c), s.val ≤ P.val + 1 → g.val (Sum.inl r) (Sum.inr s) = 0 := fun r s h => by
    simpa using hg (Sum.inl r) (Sum.inr s) (by simpa [lev] using h)
  have h21 : ∀ (r : Fin c) s, P.val < r.val → g.val (Sum.inr r) (Sum.inl s) = 0 := fun r s h => by
    simpa using hg (Sum.inr r) (Sum.inl s) (by simp [lev]; omega)
  have h22 : ∀ (r s : Fin c), s.val ≤ r.val → g.val (Sum.inr r) (Sum.inr s) = if r = s then 1 else 0 :=
    fun r s h => by simpa [Matrix.one_apply] using hg (Sum.inr r) (Sum.inr s) (by simpa [lev] using h)
  refine ⟨fun s => g.val (Sum.inr P) (Sum.inl s), fun u => ⟨rowE c (P.val + 1) u * g *
    rowE c (P.val + 1) (-(u + fun s => g.val (Sum.inr P) (Sum.inl s))), ?_, ?_, ?_⟩⟩
  · rw [Model.mem_N_iff]
    rintro (r | r) (s | s) h <;> simp only [lev, Sum.elim_inl, Sum.elim_inr] at h <;>
      simp only [Units.val_mul, mul_rowE_inl, mul_rowE_inr, rowE_mul_inl, rowE_mul_inr]
    · simp [h11, h12 r P (by omega), Matrix.one_apply]
    · simp [h12 r s (by omega)]
    · by_cases hr : r = P
      · subst hr; simp [h11, h12, h22]; ring
      · have : P.val < r.val := by have := Fin.val_ne_of_ne hr; omega
        simp [h21 r s this, h22 r P this.le, hr, this.ne']
    · by_cases hr : r = P
      · subst hr; simp [h22 r s (by omega), fun t => h12 t s (by omega), Matrix.one_apply]
      · simp [h22 r s (by omega), Fin.val_ne_of_ne hr, Matrix.one_apply]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · simp only [Units.val_mul, mul_rowE_inr, rowE_mul_inr]
      split_ifs with hi
      · simp [fun t => h12 t j (by omega)]
      · simp
    · rfl
  · rw [mul_assoc, rowE_neg_mul, mul_one]
end GlobalTheory.RootEx.Exchange
