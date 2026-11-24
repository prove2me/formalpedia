-- Prove2me | solution 1 for GlobalTheory.SymChain.PrImage.entry_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:47:01.496276+00:00
-- url     : https://prove2.me/submissions/9e638123-f5a7-4aed-8efa-3863cf34dd1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPattern
import Theorems.Thm_GlobalTheory_SymChain_PrImage_embA_mem_fixX
import Theorems.Thm_GlobalTheory_SymChain_PrImage_embX_mul_embA
import Theorems.Thm_GlobalTheory_SymChain_PrImage_mul_embX_inl
import Theorems.Thm_GlobalTheory_SymChain_PrImage_embX_inr
import Theorems.Thm_GlobalTheory_SymChain_PrImage_conj_symm_apply

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
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.PrImage
variable {k : Type*} [Field k] {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.SymChain.PrImage
theorem _root_.solution (ϖ : kˣ) (o : ι ≃ n ⊕ Fin c) {w : GL (n ⊕ Fin c) k} (hw : w ∈ fixX k n c) (g : GL n k)
    (a b : ι) :
    ((typeFrame ϖ o).conj.symm (embX c g)).val a b = ((typeFrame ϖ o).conj.symm (w * embX c g)).val a b ∨
      ((typeFrame ϖ o).conj.symm (embX c g)).val a b = (1 : Matrix ι ι k) a b := by
  obtain ⟨D, hD⟩ : ∃ D, (typeFrame ϖ o).bas = embA n D := ⟨_, rfl⟩
  have ho : (typeFrame ϖ o).ord = o := rfl
  have e1 : (embA n D)⁻¹ * embX c g * embA n D = embX c g := by
    rw [mul_assoc, embX_mul_embA, inv_mul_cancel_left]
  have e2 : (embA n D)⁻¹ * (w * embX c g) * embA n D = ((embA n D)⁻¹ * w * embA n D) * embX c g := by
    simp only [mul_assoc, embX_mul_embA]
  have hw' : (embA n D)⁻¹ * w * embA n D ∈ fixX k n c :=
    mul_mem (mul_mem (inv_mem (embA_mem_fixX D)) hw) (embA_mem_fixX D)
  rw [conj_symm_apply, conj_symm_apply, hD, ho, e1, e2, reGL_symm_val, reGL_symm_val, submatrix_apply,
    submatrix_apply, ← submatrix_one_equiv o, submatrix_apply]
  rcases o b with x | i
  · exact Or.inl (mul_embX_inl hw' g _ x).symm
  · exact Or.inr (embX_inr g _ i)
end GlobalTheory.SymChain.PrImage
