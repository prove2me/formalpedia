-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistMul.std_vecMul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:37.002827+00:00
-- url     : https://prove2.me/submissions/fa436060-a66f-4f2f-ada8-1f30e49fc603

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMul
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
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistMul
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HilbFam.TwistMul
theorem _root_.solution (A : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (A.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h : ∀ i, y i * ((A i j : ℤ) : F) ∈ (1 : Submodule (𝓞 F) F) := fun i ↦ by
    have := Submodule.smul_of_tower_mem (1 : Submodule (𝓞 F) F) (A i j) (hy i (Set.mem_univ i))
    rwa [zsmul_eq_mul, mul_comm] at this
  have e : Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j = y 0 * ((A 0 j : ℤ) : F) + y 1 * ((A 1 j : ℤ) : F) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  change Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j ∈ (1 : Submodule (𝓞 F) F)
  rw [e]
  exact Submodule.add_mem _ (h 0) (h 1)
end GlobalTheory.HilbFam.TwistMul
