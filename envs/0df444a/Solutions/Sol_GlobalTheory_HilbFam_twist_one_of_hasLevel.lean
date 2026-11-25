-- Prove2me | solution 1 for GlobalTheory.HilbFam.twist_one_of_hasLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:54:56.033221+00:00
-- url     : https://prove2.me/submissions/cfe59196-aa4b-410f-a2a8-d4fdca247134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMulMatSmulOneIff
import Theorems.Thm_GlobalTheory_HilbFam_mem_mulMat_smul_one_iff
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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F),
    HasLevel N L → twist N L 1 = L := by
  intro F _ _ _ N L hL
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
      = (ZMod.cast (1 : ZMod N) : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  unfold twist
  rw [h1]
  apply le_antisymm
  · refine sup_le (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    · obtain ⟨y, hy, rfl⟩ := (mem_mulMat_smul_one_iff _ _ _).1 hv
      exact L.smul_mem _ hy
    · obtain ⟨y, hy, rfl⟩ := (mem_mulMat_smul_one_iff _ _ _).1 hv
      simpa using hL.1 y hy
  · intro v hv
    by_cases hN : N = 1
    · subst hN
      refine Submodule.mem_sup_right ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hL.2 hv, by simp⟩)
    · have hc : (ZMod.cast (1 : ZMod N) : ℤ) = 1 := by
        rcases N with _ | _ | N
        · rfl
        · exact absurd rfl hN
        · rw [ZMod.cast_eq_val, ZMod.val_one'' hN]; simp
      rw [hc]
      exact Submodule.mem_sup_left ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hv, by simp⟩)
end GlobalTheory.HilbFam
