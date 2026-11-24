-- Prove2me | solution 1 for GlobalTheory.HilbFam.mem_mulMat_smul_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:30:42.621649+00:00
-- url     : https://prove2.me/submissions/0fbe4609-c7d9-4a49-9ef9-a6699eb97b7f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMulMatSmulOneIff
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
open GlobalTheory GlobalTheory.HilbFam
namespace GlobalTheory.HilbFam
theorem _root_.solution {F : Type} [Field F] [NumberField F] (L : Lat F) (c : ℤ) (v : Fin 2 → F) :
    v ∈ mulMat L (c • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ↔ ∃ y ∈ L, v = (c : 𝓞 F) • y := by
  have h : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F)) = (c : 𝓞 F) • y := by
    intro y
    have hm : (c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F) = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [Int.cast_smul_eq_zsmul, hm, Matrix.vecMul_smul, Matrix.vecMul_one]
  unfold mulMat
  simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, h]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
end GlobalTheory.HilbFam
