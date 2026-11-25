-- Prove2me | solution 1 for GlobalTheory.SW.weil_comp_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:36:56.991178+00:00
-- url     : https://prove2.me/submissions/f642c1b3-1adc-4024-9275-cc2bbafbf7b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_thH_mul
import Theorems.Thm_GlobalTheory_SW_UnitaryLeft_transH_mul
import Theorems.Thm_GlobalTheory_T_hermitianWeilAction_unitaryGroup_testFunctions
import Theorems.Thm_GlobalTheory_T_schwartzBruhatInvariantIntegral_matrix_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory.SW.UnitaryLeft
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ h : Matrix (Fin n) (Fin n) E, ccT h * h = 1 → ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (fun x : Matrix (Fin n) (Fin N) E => φ (h * x)) ∧ (∀ γ ∈ UU E N, weil Ψ γ (fun x => φ (h * x)) = fun x => weil Ψ γ φ (h * x)) ∧ ∀ Z ∈ Hn Ψ N, thH Ψ (fun x => φ (h * x)) Z 0 0 = thH Ψ φ Z 0 0 ∧ eis Ψ (fun x => φ (h * x)) Z 0 0 = eis Ψ φ Z 0 0 := by
  intro E _ _ _ Ψ hΨ n N hn h hh φ hφ
  have hdet : h.det ≠ 0 := by
    have h1 := congrArg Matrix.det hh
    rw [Matrix.det_mul, Matrix.det_one] at h1
    exact right_ne_zero_of_mul_eq_one h1
  have hSB : ∀ ψ : Matrix (Fin n) (Fin N) E → ℂ, IsSB ψ →
      IsSB (fun x : Matrix (Fin n) (Fin N) E => ψ (h * x)) :=
    fun ψ hψ => ((GlobalTheory.T.schwartzBruhatInvariantIntegral_matrix_mul E (Fin n) (Fin N) ψ hψ).2 h hdet).1
  have hw : ∀ γ ∈ UU E N, weil Ψ γ (fun x => φ (h * x)) = fun x => weil Ψ γ φ (h * x) := by
    intro γ hγ
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ φ hφ
    exact ((GlobalTheory.T.hermitianWeilAction_unitaryGroup_testFunctions E Ψ hΨ n N hn γ hγ _ (hSB φ hφ)).2.2.1 _ (hSB _ h1)
      (transH_mul Ψ hh γ h2)).symm
  refine ⟨hSB φ hφ, hw, fun Z _ => ⟨?_, ?_⟩⟩
  · refine (thH_mul Ψ hh φ Z 0 0).trans ?_
    congr 1
    · funext τ; simp [mv]
    · funext τ; simp [mv']
  · unfold eis
    refine tsum_congr fun U => ?_
    unfold eisTerm
    rw [hw _ U.2.choose_spec.1]
    simp
end GlobalTheory.SW
