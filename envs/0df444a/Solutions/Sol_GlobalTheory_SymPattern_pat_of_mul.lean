-- Prove2me | solution 1 for GlobalTheory.SymPattern.pat_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:33:57.543609+00:00
-- url     : https://prove2.me/submissions/2f67207a-63a5-4ddd-b9fa-4e018eeef525

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Theorems.Thm_GlobalTheory_SymPattern_mul_fromBlocks_inl
import Theorems.Thm_GlobalTheory_SymPattern_mul_fromBlocks_inr
import Theorems.Thm_GlobalTheory_RootEx_Radical_embX_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymPattern
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {F : Type} [Field F] {κ l : ℕ}
namespace GlobalTheory.SymPattern
theorem _root_.solution (ρ : ℕ) (u : GL (Fin κ ⊕ Fin l) F) (hu : InN (ρ + 1) u) (γ : GL (Fin κ) F)
    (hγ : IsUpperUnip Fin.val γ.val) :
    ∀ a b, ¬ FreeTop ρ a b → (u * embX l γ).val a b = (1 : Matrix _ _ F) a b := by
  intro a b hab
  have hv : (u * embX l γ).val = u.val * fromBlocks γ.val 0 0 1 := by
    rw [Units.val_mul, Radical.embX_val]
  rw [hv]
  rcases a with i | i <;> rcases b with j | j <;> simp only [FreeTop, not_lt] at hab
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inl i) (Sum.inl t) = if i = t then 1 else 0 := fun t => by
      rw [hu (Sum.inl i) (Sum.inl t) le_rfl, Matrix.one_apply]; simp
    simp only [hu', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hγ i j (by exact_mod_cast hab)]
    simp [Matrix.one_apply]
  · rw [mul_fromBlocks_inr, hu (Sum.inl i) (Sum.inr j) (Nat.succ_le_succ hab)]
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inr i) (Sum.inl t) = 0 := fun t => by
      rw [hu (Sum.inr i) (Sum.inl t) (Nat.succ_le_succ hab)]; simp
    simp [hu']
  · rw [mul_fromBlocks_inr, hu (Sum.inr i) (Sum.inr j) (Nat.succ_le_succ hab)]
end GlobalTheory.SymPattern
