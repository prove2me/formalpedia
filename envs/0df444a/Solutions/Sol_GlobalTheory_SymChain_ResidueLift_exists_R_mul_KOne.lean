-- Prove2me | solution 1 for GlobalTheory.SymChain.ResidueLift.exists_R_mul_KOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:34:52.960576+00:00
-- url     : https://prove2.me/submissions/ae05ffa1-7a24-43e6-adc9-78559258934c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruenc
import Theorems.Thm_GlobalTheory_SymChain_ResidueLift_mem_R_of_pattern
import Theorems.Thm_GlobalTheory_StepData_Model_typeFrame_inv
import Theorems.Thm_GlobalTheory_StepData_Model_typeFrame_val
import Theorems.Thm_GlobalTheory_StepData_Model_wt_ne_zero
import Theorems.Thm_GlobalTheory_StepData_exists_mul_KOne


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
namespace GlobalTheory.SymChain.ResidueLift
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ϖ : kˣ) (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (h : GL (n ⊕ Fin c) k), (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KO k (n ⊕ Fin c) → (∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) → valuation k (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b - (1 : Matrix _ _ k) a b) < 1) → ∃ r ∈ R k n c p, ∃ u : GL (n ⊕ Fin c) k, (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * u * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas ∈ KOne k (n ⊕ Fin c) ∧ h = r * u := by
  intro k _ _ _ _ ϖ n _ _ c p h hg hpat
  classical
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of fun a b =>
    if lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) then (1 : Matrix _ _ k) a b
    else ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val a b
  have hM : MaxM (M - ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h *
      (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas).val) := fun a b => by
    simp only [M, Matrix.sub_apply, Matrix.of_apply]
    split_ifs with hc
    · rw [← neg_sub, Valuation.map_neg]; exact hpat a b hc.1 hc.2
    · simp
  obtain ⟨u', hu', eu'⟩ := exists_mul_KOne hg hM
  refine ⟨(typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas *
      (((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * h * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas) * u') *
      (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹, ?_,
    (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹, ?_, ?_⟩
  · refine mem_R_of_pattern _ fun a b h1 h2 => ?_
    rw [Units.val_mul, Units.val_mul, eu', Model.typeFrame_val, Model.typeFrame_inv, mul_diagonal, diagonal_mul]
    simp only [M, Matrix.of_apply, if_pos (And.intro h1 h2)]
    by_cases hab : a = b
    · subst hab; simp [mul_inv_cancel₀ (Model.wt_ne_zero ϖ a)]
    · simp [one_apply_ne hab]
  · have e : (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹ * ((typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas * u'⁻¹ *
        (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas⁻¹) * (typeFrame ϖ (Equiv.refl (n ⊕ Fin c))).bas = u'⁻¹ := by group
    rw [e]; exact inv_mem hu'
  · group
end GlobalTheory.SymChain.ResidueLift
