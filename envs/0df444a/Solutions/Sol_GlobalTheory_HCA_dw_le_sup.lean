-- Prove2me | solution 1 for GlobalTheory.HCA.dw_le_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:43:34.344691+00:00
-- url     : https://prove2.me/submissions/474486e7-4a5a-4655-b986-bf89274ea078

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DwSmoothLocalLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticWeakSolWordDerivLeConstMulSup
import Theorems.Thm_GlobalTheory_HCA_SupEst_tr_eq_zero_of_notMem
import Theorems.Thm_GlobalTheory_HCA_eqOn_dw_of_isOpen
import Theorems.Thm_GlobalTheory_HCA_solSet_closed_submodule
import Theorems.Thm_GlobalTheory_T_ellipticSystem_derivative_continuous_functional


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
open GlobalTheory.HCA.SupEst
namespace GlobalTheory.HCA
theorem _root_.solution : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ (w : List (Fin d)), ∀ x₀ ∈ U, ∃ C : ℝ, 0 ≤ C ∧ ∀ u : E d → ℂ, ContinuousOn u U → WeakSol P U u → ∀ M : ℝ, (∀ x ∈ U, ‖u x‖ ≤ M) → ‖dw w u x₀‖ ≤ C * M := by
  intro d ι _ P U hU ha hell w x₀ hx₀
  obtain ⟨S, hS⟩ := (solSet_closed_submodule d ι P U hU ha).2
  obtain ⟨l, hl⟩ := GlobalTheory.T.ellipticSystem_derivative_continuous_functional d ι P U hU ha hell S hS w x₀ hx₀
  refine ⟨‖l‖, norm_nonneg _, ?_⟩
  intro u hu hweak M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x₀ hx₀)
  have hcont : Continuous (U.restrict u) := continuousOn_iff_continuous_restrict.mp hu
  let u' : U →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup (U.restrict u) hcont M
    (fun x => hM x.1 x.2)
  have hu'n : ‖u'‖ ≤ M := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM0 _
  have hext : Set.EqOn (ext0 U u') u U := by
    intro x hx
    simp only [ext0, hx, dif_pos, u']
    rfl
  have hmem : u' ∈ solSet P U := by
    intro i φ h1 h2 h3
    rw [← hweak i φ h1 h2 h3]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [hext hx]
    · have : x ∉ tsupport φ := fun h => hx (h3 h)
      rw [tr_eq_zero_of_notMem P i this]
      simp
  have hmemS : u' ∈ S := by rw [← SetLike.mem_coe, hS]; exact hmem
  have hval : l ⟨u', hmemS⟩ = dw w u x₀ := by
    rw [hl]
    exact eqOn_dw_of_isOpen hU w _ _ hext hx₀
  rw [← hval]
  calc ‖l ⟨u', hmemS⟩‖ ≤ ‖l‖ * ‖(⟨u', hmemS⟩ : S)‖ := l.le_opNorm _
    _ = ‖l‖ * ‖u'‖ := rfl
    _ ≤ ‖l‖ * M := mul_le_mul_of_nonneg_left hu'n (norm_nonneg _)
end GlobalTheory.HCA
