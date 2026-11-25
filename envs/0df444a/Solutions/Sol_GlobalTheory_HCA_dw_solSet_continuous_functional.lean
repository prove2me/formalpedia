-- Prove2me | solution 1 for GlobalTheory.HCA.dw_solSet_continuous_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:24:48.832828+00:00
-- url     : https://prove2.me/submissions/782e9e9c-2293-4073-b5cc-35b8d238d44b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctional
import Theorems.Thm_GlobalTheory_HCA_SolFunc_continuous_extLin_apply
import Theorems.Thm_GlobalTheory_HCA_SolFunc_continuousOn_extendByZeroOffSubset
import Theorems.Thm_GlobalTheory_HCA_solSet_closed_submodule
import Theorems.Thm_GlobalTheory_T_exists_continuous_functional_iterPartialDeriv
import Theorems.Thm_ZetaZeros_D_EllReg_elliptic_regularity_of_parts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory.HCA.SolFunc
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : S →L[ℂ] ℂ, ∀ u : S, l u = dw w (ext0 U (u : U →ᵇ ℂ)) x := by
  intro d ι _ P U hU ha hell S hS w x hx
  have hcl : IsClosed (S : Set (U →ᵇ ℂ)) := by
    rw [hS]; exact (GlobalTheory.HCA.solSet_closed_submodule d ι P U hU ha).1
  haveI : CompleteSpace S := hcl.completeSpace_coe
  have hsm : ∀ u : S, ContDiffOn ℝ ∞ (extLin S u) U := by
    intro u
    have hu : (u : U →ᵇ ℂ) ∈ solSet P U := by rw [← hS]; exact u.2
    exact ZetaZeros.D.EllReg.elliptic_regularity_of_parts d ι P U _ ⟨hU, ha, hell, continuousOn_extendByZeroOffSubset _, hu⟩
  obtain ⟨l, hl⟩ := GlobalTheory.T.exists_continuous_functional_iterPartialDeriv d U hU S (extLin S) (fun y _ => continuous_extLin_apply S y) hsm w x hx
  exact ⟨l, fun u => hl u⟩
end GlobalTheory.HCA
