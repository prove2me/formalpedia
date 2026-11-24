-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistSL.vecMul_mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:38.973067+00:00
-- url     : https://prove2.me/submissions/2760d271-76c3-4e36-aeb1-636efdb40d71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMulSL2Z
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistSL
namespace GlobalTheory.HilbFam.TwistSL
theorem _root_.solution {F : Type} [Field F] [NumberField F] (B : Matrix (Fin 2) (Fin 2) ℤ) {w : Fin 2 → F}
    (hw : w ∈ stdLat F) : Matrix.vecMul w (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h0 := hw 0 (Set.mem_univ _)
  have h1 := hw 1 (Set.mem_univ _)
  have e : Matrix.vecMul w (B.map (Int.cast : ℤ → F)) j = B 0 j • w 0 + B 1 j • w 1 := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  change Matrix.vecMul w (B.map (Int.cast : ℤ → F)) j ∈ (1 : Submodule (𝓞 F) F)
  rw [e]
  exact Submodule.add_mem _ (zsmul_mem h0 _) (zsmul_mem h1 _)
end GlobalTheory.HilbFam.TwistSL
