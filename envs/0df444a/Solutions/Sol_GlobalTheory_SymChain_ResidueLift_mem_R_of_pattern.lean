-- Prove2me | solution 1 for GlobalTheory.SymChain.ResidueLift.mem_R_of_pattern
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:21:26.772691+00:00
-- url     : https://prove2.me/submissions/3b9e7ba2-57a9-4ffe-86dc-24d11c60a7ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruenc
import Theorems.Thm_GlobalTheory_SymChain_ResidueLift_of_blockIx_lt

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
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.ResidueLift
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.SymChain.ResidueLift
theorem _root_.solution (r : GL (n ⊕ Fin c) k)
    (hr : ∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
      r.val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b) :
    r ∈ R k n c p := by
  have hbt : r.val.BlockTriangular (blockIx p) := fun a b h => by
    obtain ⟨h1, h2, h3⟩ := of_blockIx_lt h
    rw [hr a b h1 h2, one_apply_ne h3]
  have hbt' : (r⁻¹).val.BlockTriangular (blockIx p) := by
    rw [Matrix.coe_units_inv]; exact blockTriangular_inv_of_blockTriangular hbt
  have hz : ∀ (x : n) (j : Fin c), j.val + 1 ≤ p → r.val (.inl x) (.inr j) = 0 := fun x j hj => by
    rw [hr _ _ (by simpa [lev] using hj) (by simp)]; simp
  have hz' : ∀ (x : n) (j : Fin c), p ≤ j.val + 1 → (r⁻¹).val (.inr j) (.inl x) = 0 := fun x j hj =>
    hbt' (by simp only [blockIx, Sum.elim_inl, Sum.elim_inr]; omega)
  have e1 : r.val.toBlocks₁₁ * (r⁻¹).val.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.toBlocks₁₁ (congrArg Units.val (mul_inv_cancel r))
    rw [Units.val_mul, mul_toBlocks₁₁, Units.val_one, ← fromBlocks_one, toBlocks_fromBlocks₁₁] at this
    rw [← this, left_eq_add]
    ext x x'
    simp only [mul_apply, toBlocks₁₂, toBlocks₂₁, of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rcases le_total (j.val + 1) p with hj | hj
    · rw [hz x j hj, zero_mul]
    · rw [hz' x' j hj, mul_zero]
  let γ : GL n k := ⟨r.val.toBlocks₁₁, (r⁻¹).val.toBlocks₁₁, e1, mul_eq_one_comm.1 e1⟩
  have e2 : (γ⁻¹).val * r.val.toBlocks₁₁ = 1 := Units.inv_mul γ
  have hm : InN p ((embX c γ)⁻¹ * r) := by
    intro a b hab
    rw [← map_inv, Units.val_mul, show (embX c γ⁻¹).val = fromBlocks (γ⁻¹).val 0 0 1 from rfl]
    rcases a with x | i
    · rcases b with x' | j
      · have := congrFun (congrFun e2 x) x'
        simpa [mul_apply, Fintype.sum_sum_type, toBlocks₁₁, one_apply] using this
      · have hj : j.val + 1 ≤ p := by simpa [lev] using hab
        simp [mul_apply, Fintype.sum_sum_type, hz _ _ hj]
    · have := hr (.inr i) b hab (by simp)
      simpa [mul_apply, Fintype.sum_sum_type, one_apply] using this
  have : r = embX c γ * ((embX c γ)⁻¹ * r) := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left ⟨γ, rfl⟩) (Subgroup.mem_sup_right (Subgroup.subset_closure hm))
end GlobalTheory.SymChain.ResidueLift
