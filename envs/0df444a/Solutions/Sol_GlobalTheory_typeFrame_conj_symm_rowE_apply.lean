-- Prove2me | solution 1 for GlobalTheory.typeFrame_conj_symm_rowE_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:10:50.675998+00:00
-- url     : https://prove2.me/submissions/b84e1bef-46e2-4a10-92d4-bd20a4f330f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentLatticeFrameConjApply
import Theorems.Thm_GlobalTheory_StepData_standardOrderExtendedBasis_apply_low_block


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (k : Type) [Field k] (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (ϖ : kˣ) (j c l : ℕ) (h : j + c = l) (p : ℕ) (hp : p < c) (u : XIx κ t j → k) (a b : Ix (κ ⊕ Fin l) t j), ((typeFrame ϖ (stdOrd κ t j c h)).conj.symm (rowE c (p + 1) u)).val a b = (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b + if a = Sum.inl (Sum.inr ⟨p, by omega⟩) then Sum.elim (fun y => ((ϖ : k) ^ (p + 1))⁻¹ * u y) (fun _ => 0) (stdOrd κ t j c h b) else 0 := by
  intro k _ κ t _ _ _ _ ϖ j c l h p hp u a b
  set ord := stdOrd κ t j c h with hord
  have hbas : (typeFrame ϖ ord).bas.val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => (ϖ : k) ^ (i.val + 1)) := by
    change fromBlocks 1 0 0 _ = _
    congr 1
  have hinv : ((typeFrame ϖ ord).bas⁻¹).val =
      fromBlocks 1 0 0 (diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hbas]
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  have hM : ((typeFrame ϖ ord).bas⁻¹ * rowE c (p + 1) u * (typeFrame ϖ ord).bas).val =
      fromBlocks 1 0 (Matrix.of fun (i : Fin c) y => if i.val = p then ((ϖ : k) ^ (p + 1))⁻¹ * u y else 0) 1 := by
    rw [Units.val_mul, Units.val_mul, hinv, hbas]
    change fromBlocks _ _ _ _ * fromBlocks 1 0 _ 1 * _ = _
    simp only [fromBlocks_multiply]
    congr 1 <;> ext i y <;> simp [diagonal_apply]
    by_cases hi : (i : ℕ) = p <;> simp [hi]
  have e : ((typeFrame ϖ ord).conj.symm (rowE c (p + 1) u)).val =
      ((typeFrame ϖ ord).bas⁻¹ * rowE c (p + 1) u * (typeFrame ϖ ord).bas).val.submatrix ord ord := rfl
  rw [e, submatrix_apply, hM]
  have haux : ord (Sum.inl (Sum.inr ⟨p, by omega⟩)) = Sum.inr ⟨p, hp⟩ := standardOrderExtendedBasis_apply_low_block κ t j c h ⟨p, hp⟩
  have hcond : a = Sum.inl (Sum.inr ⟨p, by omega⟩) ↔ ord a = Sum.inr ⟨p, hp⟩ := by
    rw [← haux]; exact ord.apply_eq_iff_eq.symm
  have h1 : (1 : Matrix (Ix (κ ⊕ Fin l) t j) (Ix (κ ⊕ Fin l) t j) k) a b =
      (1 : Matrix (XIx κ t j ⊕ Fin c) (XIx κ t j ⊕ Fin c) k) (ord a) (ord b) := by
    simp [one_apply, ord.apply_eq_iff_eq]
  rw [h1]
  simp only [hcond]
  generalize ord a = x
  generalize ord b = y
  rcases x with x | i <;> rcases y with y | i' <;> simp [one_apply, Fin.ext_iff]
end GlobalTheory
