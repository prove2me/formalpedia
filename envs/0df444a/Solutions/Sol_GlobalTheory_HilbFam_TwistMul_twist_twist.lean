-- Prove2me | solution 1 for GlobalTheory.HilbFam.TwistMul.twist_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:24:49.938836+00:00
-- url     : https://prove2.me/submissions/318544ab-a345-4c8a-8206-48b76165a3f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMul
import Theorems.Thm_GlobalTheory_HilbFam_TwistMul_std_vecMul_int
import Theorems.Thm_GlobalTheory_HilbFam_TwistMul_std_natCast_smul
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
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistMul
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HilbFam.TwistMul
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (α β : Matrix (Fin 2) (Fin 2) (ZMod N)), L ≤ stdLat F → twist N (twist N L α) β = twist N L (α * β) := by
  intro F _ _ _ N L α β hL
  have lift : ∀ γ : Matrix (Fin 2) (Fin 2) (ZMod N), ∃ C : Matrix (Fin 2) (Fin 2) ℤ, C.map (Int.cast : ℤ → ZMod N) = γ :=
    fun γ ↦ ⟨γ.map (ZMod.cast : ZMod N → ℤ), by ext i j; simp⟩
  obtain ⟨A, rfl⟩ := lift α
  obtain ⟨B, rfl⟩ := lift β
  have hm : A.map (Int.cast : ℤ → ZMod N) * B.map (Int.cast : ℤ → ZMod N) = (A * B).map (Int.cast : ℤ → ZMod N) :=
    (Matrix.map_mul (f := Int.castRingHom (ZMod N))).symm
  have hF : (A * B).map (Int.cast : ℤ → F) = A.map (Int.cast : ℤ → F) * B.map (Int.cast : ℤ → F) :=
    Matrix.map_mul (f := Int.castRingHom F)
  have hT : twist N L (A.map (Int.cast : ℤ → ZMod N)) ≤ stdLat F := by
    intro v hv
    obtain ⟨y, hy, w, hw, rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A v hL).1 hv
    exact Submodule.add_mem _ (std_vecMul_int A (hL hy)) (std_natCast_smul N hw)
  rw [hm]
  ext v
  rw [GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ B v hT, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L (A * B) v hL, hF]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    obtain ⟨y, hy, w', hw', rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A u hL).1 hu
    refine ⟨y, hy, Matrix.vecMul w' (B.map (Int.cast : ℤ → F)) + w,
      Submodule.add_mem _ (std_vecMul_int B hw') hw, ?_⟩
    rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.smul_vecMul, smul_add, add_assoc]
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨Matrix.vecMul y (A.map (Int.cast : ℤ → F)),
      (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).2 ⟨y, hy, 0, Submodule.zero_mem _, by simp⟩, w, hw, ?_⟩
    rw [Matrix.vecMul_vecMul]
end GlobalTheory.HilbFam.TwistMul
