-- Prove2me | solution 1 for GlobalTheory.Doubling.leviElt_mem_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:42.442108+00:00
-- url     : https://prove2.me/submissions/8fc7675a-a077-4b43-9c26-2857cfcbea61

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
variable [Invertible (2 : A)]
namespace GlobalTheory.Doubling
theorem _root_.solution {σ : A →+* A} {J : Matrix n n A} {α β : GL n A} (h1 : cT σ β.1 * J * α.1 = J)
    (h2 : cT σ α.1 * J * β.1 = J) : leviElt e (α, β) ∈ UJ σ (dblGram e J) := by
  have hT : cT σ (cayley (A := A) e).1 = (cayley e).1 := by
    change ((fromBlocks 1 1 1 (-1) : Matrix (n ⊕ n) (n ⊕ n) A).map σ)ᵀ.submatrix e.symm e.symm = _
    simp [cayley, fromBlocks_map, fromBlocks_transpose, Matrix.map_neg _ (map_neg σ), Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hQ : cT σ (cayley (A := A) e).1 * dblGram e J * (cayley e).1 =
      (fromBlocks 0 (J + J) (J + J) 0).submatrix e.symm e.symm := by
    rw [hT]
    simp [cayley, dblGram, blkMat, submatrix_mul_equiv, fromBlocks_multiply]
  have hB : cT σ (blkMat e α.1 β.1) * (cT σ (cayley (A := A) e).1 * dblGram e J * (cayley e).1) * blkMat e α.1 β.1 =
      cT σ (cayley (A := A) e).1 * dblGram e J * (cayley e).1 := by
    rw [hQ, cT_blkMat]
    simp [blkMat, submatrix_mul_equiv, fromBlocks_multiply, Matrix.mul_add, Matrix.add_mul, h1, h2]
  change cT σ ((cayley e).1 * blkMat e α.1 β.1 * (cayley e)⁻¹.1) * _ * ((cayley e).1 * blkMat e α.1 β.1 * (cayley e)⁻¹.1) = _
  calc _ = cT σ (cayley (A := A) e)⁻¹.1 * (cT σ (blkMat e α.1 β.1) *
        (cT σ (cayley (A := A) e).1 * dblGram e J * (cayley e).1) * blkMat e α.1 β.1) * (cayley e)⁻¹.1 := by
        simp only [cT_mul, Matrix.mul_assoc]
    _ = cT σ ((cayley (A := A) e).1 * (cayley (A := A) e)⁻¹.1) * dblGram e J * ((cayley e).1 * (cayley e)⁻¹.1) := by
        rw [hB]; simp only [cT_mul, Matrix.mul_assoc]
    _ = _ := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]
end GlobalTheory.Doubling
