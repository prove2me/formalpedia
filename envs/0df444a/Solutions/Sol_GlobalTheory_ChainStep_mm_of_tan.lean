-- Prove2me | solution 1 for GlobalTheory.ChainStep.mm_of_tan
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:51:17.577906+00:00
-- url     : https://prove2.me/submissions/e6a6461e-8fa0-4e7d-836d-d3d87cefa3dc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal
import Theorems.Thm_GlobalTheory_ChainStep_mm_sum
import Theorems.Thm_GlobalTheory_ChainStep_mm_mul_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_U_det_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_U_int
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_inv_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.ChainStep
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.ChainStep
theorem _root_.solution {d : ℕ} {I J : Type} [Fintype I] [Fintype J] {G : Cart V d I J} (S : Sys G)
    (z : I → C) (h : ∀ k, V.MM (∑ c, z c * S.tan c k)) (c : I) : V.MM (z c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have h2 : z c = ∑ k, (∑ b, z b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, z b * S.tan b k * S.U⁻¹ k c = z b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp [Sys.U, mul_assoc]
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [h2]
  exact mm_sum fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)
end GlobalTheory.ChainStep
