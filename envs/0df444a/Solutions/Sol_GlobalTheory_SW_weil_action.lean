-- Prove2me | solution 1 for GlobalTheory.SW.weil_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:58:22.896679+00:00
-- url     : https://prove2.me/submissions/6de807b7-8a2e-41b7-ac7c-1bb9609bcd1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_QuadCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatRationalCoordsIntegralProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctions
import Theorems.Thm_GlobalTheory_SW_WeilAct_thH_smul
import Theorems.Thm_GlobalTheory_SW_WeilAct_thH_add
import Theorems.Thm_GlobalTheory_SW_WeilAct_unique
import Theorems.Thm_GlobalTheory_SW_WeilAct_exists_op
import Theorems.Thm_GlobalTheory_SW_WeilAct_weil_spec
import Theorems.Thm_GlobalTheory_SW_Base_one_mem_UU
import Theorems.Thm_GlobalTheory_SW_Base_transH_one
import Theorems.Thm_GlobalTheory_SW_transH_comp
import Theorems.Thm_GlobalTheory_SW_unitary_act_halfSpace
import Theorems.Thm_GlobalTheory_T_rationalSchwartzBruhat_algebra_integral_linear


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
open GlobalTheory GlobalTheory.SW
open WeilAct
namespace GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ γ ∈ UU E N, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → TransH Ψ γ φ ψ → ψ = weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → ip (weil Ψ γ φ) (weil Ψ γ ψ) = ip φ ψ ∧ weil Ψ γ (φ + ψ) = weil Ψ γ φ + weil Ψ γ ψ) ∧ (∀ c : ℂ, weil Ψ γ (c • φ) = c • weil Ψ γ φ) ∧ (∀ γ' ∈ UU E N, weil Ψ (γ' * γ) φ = weil Ψ γ' (weil Ψ γ φ)) ∧ weil Ψ 1 φ = φ := by
  intro E _ _ _ Ψ hΨ n N hn γ hγ φ hφ
  obtain ⟨s1, t1⟩ := weil_spec hΨ hn hγ hφ
  refine ⟨s1, t1, fun ψ hψ t => unique hΨ hγ hψ s1 t t1, fun ψ hψ => ⟨?_, ?_⟩, fun c => ?_,
    fun γ' hγ' => ?_, ?_⟩
  · obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ hψ
    obtain ⟨W, hW⟩ := exists_op (n := n) hΨ hn hγ
    rw [unique hΨ hγ s1 (hW φ hφ).1 t1 (hW φ hφ).2.1,
      unique hΨ hγ s2 (hW ψ hψ).1 t2 (hW ψ hψ).2.1]
    exact (hW φ hφ).2.2 ψ hψ
  · obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ hψ
    obtain ⟨s3, t3⟩ := weil_spec hΨ hn hγ (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ ψ hφ hψ).1
    refine unique hΨ hγ s3 (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ s1 s2).1 t3 fun Z hZ z z' => ?_
    rw [thH_add hΨ s1 s2 ((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).2.1, thH_add hΨ hφ hψ hZ,
      t1 Z hZ, t2 Z hZ, mul_add]
  · obtain ⟨s3, t3⟩ := weil_spec hΨ hn hγ ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ φ φ hφ hφ).2.1 c)
    refine unique hΨ hγ s3 ((GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear E _ _ _ _ s1 s1).2.1 c) t3 fun Z hZ z z' => ?_
    rw [thH_smul, thH_smul, t1 Z hZ, mul_left_comm]
  · have hm := (unitary_act_halfSpace E Ψ N γ hγ).1.2.2.2.2 γ' hγ'
    obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ' s1
    obtain ⟨s3, t3⟩ := weil_spec hΨ hn hm hφ
    exact unique hΨ hm s3 s2 t3 ((transH_comp E Ψ n N γ γ' hγ hγ').2 _ _ _ t1 t2)
  · obtain ⟨s3, t3⟩ := weil_spec hΨ hn Base.one_mem_UU hφ
    exact unique hΨ Base.one_mem_UU s3 hφ t3 (Base.transH_one Ψ φ)
end GlobalTheory.SW
