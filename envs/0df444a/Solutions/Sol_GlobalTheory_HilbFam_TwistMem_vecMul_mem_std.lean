-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistMem.vecMul_mem_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:33.951904+00:00
-- url     : https://prove2.me/submissions/64e13846-2dcc-4579-a013-9555f3e0b389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLift
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
noncomputable section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistMem
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HilbFam.TwistMem
theorem _root_.solution (B : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h0 := hy 0 (Set.mem_univ _)
  have h1 := hy 1 (Set.mem_univ _)
  have : Matrix.vecMul y (B.map (Int.cast : ℤ → F)) j = B 0 j • y 0 + B 1 j • y 1 := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ h0) (Submodule.smul_of_tower_mem _ _ h1)
end GlobalTheory.HilbFam.TwistMem
