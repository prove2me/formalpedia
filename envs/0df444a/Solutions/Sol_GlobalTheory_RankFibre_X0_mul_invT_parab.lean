-- Prove2me | solution 1 for GlobalTheory.RankFibre.X0_mul_invT_parab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:41.914605+00:00
-- url     : https://prove2.me/submissions/e2c42ee6-c92e-49b4-bdc8-74c58e1cceaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreMemInducedSpace
import Theorems.Thm_P2M_GlobalTheory_RankFibre_stdSum_rfl__782d855e1287
import Theorems.Thm_GlobalTheory_SmGL_mem_parab_two
import Theorems.Thm_GlobalTheory_SplitFlip_frameMatrixFirstColumnBlock_mul_apply
import Theorems.Thm_GlobalTheory_SplitFlip_invT_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM
open GlobalTheory GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
local notation:70 M:70 " ⬝ₘ " N:71 => HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) M N
namespace GlobalTheory.RankFibre
theorem _root_.solution (a b : ℕ) (p : parab k (blocks a b)) :
    X0 k finSumFinEquiv ⬝ₘ (invT (p : GL (Fin (a + b)) k)).val =
      (invT (leviProj k (blocks a b) p false)).val ⬝ₘ X0 k finSumFinEquiv := by
  have hA : (invT (leviProj k (blocks a b) p false)).val
      = ((leviProj k (blocks a b) p⁻¹ false : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)ᵀ := by
    rw [invT_val, map_inv]; rfl
  refine Matrix.ext fun i j => ?_
  rw [frameMatrixFirstColumnBlock_mul_apply, invT_val, hA]
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with j | j
  · have := leviProj_apply k (blocks a b) p⁻¹ false j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this]
  · have hne : ∀ (i : Fin a), Fin.castAdd b i ≠ Fin.natAdd a j := fun i h => by
      have := congrArg Fin.val h; simp at this; omega
    have := (mem_parab_two k).1 (p⁻¹).2 j i
    simp [stdSum_rfl'] at this
    simp [Matrix.mul_apply, X0, this, hne]
end GlobalTheory.RankFibre
