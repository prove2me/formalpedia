-- Prove2me | solution 1 for GlobalTheory.RowRat.exists_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:39.226929+00:00
-- url     : https://prove2.me/submissions/5826854a-9d99-4e6e-a3a1-bcb12ab688f8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ReprMemOfCoeff
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism.L2.DIV MvPolynomial
open GlobalTheory GlobalTheory.RowRat
namespace GlobalTheory.RowRat
theorem _root_.solution (K' : Subfield ℂ) : ∃ φ : ℂ →ₗ[K'] ℂ, (∀ x : K', φ x = x) ∧ ∀ x, φ x ∈ K' := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K' ℂ)
    (LinearMap.ker_eq_bot.2 (FaithfulSMul.algebraMap_injective K' ℂ))
  refine ⟨(Algebra.linearMap K' ℂ).comp g, fun x => ?_, fun x => (g x).2⟩
  have h := congrArg (fun f => f x) hg
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h
  show algebraMap K' ℂ (g (Algebra.linearMap K' ℂ x)) = algebraMap K' ℂ x
  rw [h]
end GlobalTheory.RowRat
