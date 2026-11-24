-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistSL.twist_mul_sl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:24:46.457072+00:00
-- url     : https://prove2.me/submissions/ef48ad84-fd8a-4ba9-9cb6-973311f3c679

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMulSL2Z
import Theorems.Thm_GlobalTheory_HilbFam_TwistSL_vecMul_mem_stdLat
import Theorems.Thm_GlobalTheory_HilbFam_TwistSL_map_cast_mul
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_T_mem_hilbertLatticeTwist_iff_lift
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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α : Matrix (Fin 2) (Fin 2) (ZMod N)) (γ : SL(2, ℤ)), L ≤ stdLat F → twist N L (α * (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N)) = mulMat (twist N L α) (γ : Matrix (Fin 2) (Fin 2) ℤ) := by
  intro F _ _ _ N L α γ hL
  obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin 2) (Fin 2) ℤ, α = A.map (Int.cast : ℤ → ZMod N) :=
    ⟨α.map (ZMod.cast : ZMod N → ℤ), by ext i j; simp⟩
  rw [← map_cast_mul]
  have hinv : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F) *
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F) = 1 := by
    rw [← map_cast_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.map_one _ Int.cast_zero Int.cast_one
  ext v
  rw [GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L _ v hL]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨Matrix.vecMul y (A.map (Int.cast : ℤ → F)) +
      (N : F) • Matrix.vecMul w (((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → F)), ?_, ?_⟩
    · exact (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).2 ⟨y, hy, _, vecMul_mem_stdLat _ hw, rfl⟩
    · rw [LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hinv,
        Matrix.vecMul_one, map_cast_mul]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨y, hy, w, hw, rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).1 hu
    refine ⟨y, hy, _, vecMul_mem_stdLat (γ : Matrix (Fin 2) (Fin 2) ℤ) hw, ?_⟩
    rw [LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, Matrix.add_vecMul, Matrix.smul_vecMul, Matrix.vecMul_vecMul, map_cast_mul]
end GlobalTheory.HilbFam.TwistSL
