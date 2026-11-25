-- Prove2me | solution 1 for GlobalTheory.AdaptedChain.co_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:27:31.790131+00:00
-- url     : https://prove2.me/submissions/c0e0bba9-eb81-4d16-9978-e029262a1dec

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_U_det_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_l_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {X : Cart V d I J}
namespace GlobalTheory.AdaptedChain
theorem _root_.solution (S : Sys X) (h : I ⊕ J → C) (g lam : I → C)
    (e : ∀ k, (V.l : C) * h (Sum.inl k) = ∑ e, g e * S.tan e k + (V.l : C) * lam k) (b : I) :
    S.co h b = (V.l : C)⁻¹ * (g b + (V.l : C) * S.co (Sum.elim lam 0) b) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have h2 : ∑ k, (∑ e, g e * S.tan e k) * S.U⁻¹ k b = g b := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ e, ∑ k, g e * S.tan e k * S.U⁻¹ k b = g e * (S.U * S.U⁻¹) e b := by
      intro e
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp [Sys.U, mul_assoc]
    simp [this, h1, Matrix.one_apply]
  rw [eq_inv_mul_iff_mul_eq₀ VF.l_ne_zero, ← h2]
  simp only [Sys.co, Finset.mul_sum, ← mul_assoc, e, add_mul, Finset.sum_add_distrib, Sum.elim_inl]
end GlobalTheory.AdaptedChain
