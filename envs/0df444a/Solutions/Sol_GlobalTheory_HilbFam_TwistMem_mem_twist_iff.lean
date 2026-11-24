-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistMem.mem_twist_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:44.518914+00:00
-- url     : https://prove2.me/submissions/fe0bb565-3635-4a27-8736-b8a024f55d6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLift
import Theorems.Thm_GlobalTheory_HilbFam_TwistMem_vecMul_mem_std
import Theorems.Thm_GlobalTheory_HilbFam_TwistMem_exists_lift_diff
import Theorems.Thm_GlobalTheory_HilbFam_TwistMem_vecMul_scalar
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
theorem _root_.solution (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → F) (hL : L ≤ stdLat F) :
    (v ∈ twist N L (A.map (Int.cast : ℤ → ZMod N)) ↔
      ∃ y ∈ L, ∃ w ∈ stdLat F, v = Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) := by
  obtain ⟨B, hB⟩ := exists_lift_diff (F := F) N A
  unfold twist mulMat
  simp only [Submodule.mem_sup, Submodule.mem_map, LinearMap.restrictScalars_apply,
    Matrix.vecMulLinear_apply, hB, vecMul_scalar, Matrix.vecMul_add, Matrix.vecMul_smul]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨y, hy, Matrix.vecMul y (B.map (Int.cast : ℤ → F)) + w,
      Submodule.add_mem _ (vecMul_mem_std B (hL hy)) hw, ?_⟩
    rw [smul_add, add_assoc]
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨_, ⟨y, hy, rfl⟩, _, ⟨w - Matrix.vecMul y (B.map (Int.cast : ℤ → F)),
      Submodule.sub_mem _ hw (vecMul_mem_std B (hL hy)), rfl⟩, ?_⟩
    rw [smul_sub]
    abel
end GlobalTheory.HilbFam.TwistMem
