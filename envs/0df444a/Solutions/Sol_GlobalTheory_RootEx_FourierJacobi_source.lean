-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobi.source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:27.74158+00:00
-- url     : https://prove2.me/submissions/3ee6a262-bffb-49f1-853d-28d599079b43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralWhittakerTwist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsHeisenbergSubgroupFourierJacobiCommutatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatSupportedNhdsIntegralOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemFourierJacobiSubgroupIffParabolicMulColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntriStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeHeisenbergVariableSignStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeOperatorWeilRowUnipotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicQuotientStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotIntFJUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumSmulOfLocallyConstantCompactSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzFourierTransformPiSurjectiveSchwartzBruhStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalFStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralMulOfSupport
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_integral_mul_of_support
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FourierJacobiAverage_app_coe
import Theorems.Thm_GlobalTheory_PowerTwoNormLowerBound_main
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_continuous_rowE
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_rowE_zero
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_mul
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_smooth
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_val
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_orbit_locallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_T_continuous_characters_locallyConstant_nonarchLocalField
import Theorems.Thm_GlobalTheory_T_exists_schwartzBruhat_supported_nhds_integral_one
import Theorems.Thm_GlobalTheory_T_isUnimodular_blockUpperTriangular_symmetricLevels
import Theorems.Thm_GlobalTheory_T_mem_rootExchangeParabolic_and_fourierJacobi_iff_entries
import Theorems.Thm_GlobalTheory_T_rootExchangeOperator_weil_rowUnipotent
import Theorems.Thm_GlobalTheory_T_schwartzFourierTransformPi_surjective_schwartzBruhat
import Theorems.Thm_GlobalTheory_exists_weakIntegral_of_isLocallyConstant_of_isCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.FourierJacobi
open GlobalTheory.RootEx.Unfolding (omR omR_val omR_mul omR_smooth orbit_locallyConstant opL ev)
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.RootEx.FourierJacobi
theorem _root_.solution : Source k := by
  intro n n' _ _ _ _ c ρ hc ψ ν hψ hψ1 hν μ hμ μX μG hX hG P A P' A' _ _ _ _ _ _ _ _ π σ π' σ' _ _ _ _
    ϑ θ hϑ _ fj' b b' _ _ hfj φ F
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hμ' := (GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).1 μ hμ
  have hF := GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n' ψ hψ hψ1 ν hν
  have main : ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Φ₀ : SB (n' → k)),
      ∃ w : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), avg ψ ν μ ρ Φ₀ Φ.1 = w.1 ∧
      (∀ h, opE ψ ν ρ (om μ 1 h w.1) = opEFJ ψ ν ρ Φ₀ (om μ 1 h Φ.1)) ∧ fj' φ (ϑ F Φ) Φ₀ = b' φ (ϑ F w) := by
    intro Φ Φ₀
    have hh := hF.1 Φ₀
    let T : (n' → k) → SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := fun u =>
      hat ψ ν Φ₀.1 u • omR μ (rowE (c + 1) ρ u, 1) Φ
    have hT : IsLocallyConstant T :=
      (hh.1.prodMk ((orbit_locallyConstant (omR_smooth hμ') Φ).comp_continuous
        (ExchangeSupport.continuous_rowE.prodMk continuous_const))).comp fun z => z.1 • z.2
    obtain ⟨w, hw⟩ := GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n' → k)
      (Measure.pi fun _ => ν) _ T hT _ hh.2 fun u hu => by
        simp only [T, image_eq_zero_of_notMem_tsupport hu, zero_smul]
    refine ⟨w, funext fun x => (hw (ev x)).symm, fun h => funext fun x₀ => ?_, ?_⟩
    · refine (hw ((ev x₀).comp ((opL hψ ν ρ).comp (omR μ (1, h))))).trans ?_
      rw [opEFJ]
      congr 1; funext u
      simp only [T, LinearMap.comp_apply, map_smul, smul_eq_mul]
      congr 1
      have := GlobalTheory.T.rootExchangeOperator_weil_rowUnipotent k n n' c ρ (by omega) (by omega) ψ hψ ν μ (omR μ (1, h) Φ) u x₀
      rw [← omR_val, omR_mul, one_mul, mul_one] at this
      rw [omR_mul, one_mul, mul_one]
      exact this
    · rw [hfj]
      refine Eq.trans ?_ (hw ((b' φ).comp (ϑ F))).symm
      congr 1; funext u
      have := hϑ (rowE (c + 1) ρ u) 1 F Φ (omR μ (rowE (c + 1) ρ u, 1) Φ) rfl
      rw [map_one, Module.End.one_apply] at this
      simp only [T, LinearMap.comp_apply, map_smul, smul_eq_mul, this]
  refine ⟨GlobalTheory.T.isUnimodular_blockUpperTriangular_symmetricLevels k n c _ _ (fun i => ?_) _ (GlobalTheory.T.mem_rootExchangeParabolic_and_fourierJacobi_iff_entries k n c ρ).1, fun Φ Φ₀ => ?_, fun H Φ => ?_,
    fun H Φ Φ₀ => ?_⟩
  · have := i.2
    simp only [Fin.val_rev]
    omega
  · obtain ⟨w, e1, e2, e3⟩ := main Φ Φ₀
    rw [e1, app_coe]
    exact ⟨w.2, fun h => (opL hψ ν ρ (omR μ (1, h) Φ)).2, fun h => e2 h ▸ (opL hψ ν ρ (omR μ (1, h) w)).2, e2, e3⟩
  · have hU : {u : n' → k | omR μ (rowE (c + 1) ρ u, 1) Φ = Φ} ∈ 𝓝 (0 : n' → k) :=
      ((omR_smooth hμ' Φ).preimage (ExchangeSupport.continuous_rowE.prodMk continuous_const)).mem_nhds (by
        change omR μ (rowE (c + 1) ρ 0, 1) Φ = Φ
        rw [ExchangeSupport.rowE_zero, ← Prod.one_eq_mk, map_one, Module.End.one_apply])
    obtain ⟨g, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n' ν _ hU
    obtain ⟨Φ₀, h0⟩ := hF.2 g
    obtain ⟨w, e1, e2, e3⟩ := main Φ Φ₀
    have e : w = Φ := by
      refine Subtype.ext (e1.symm.trans (funext fun x => ?_))
      rw [avg, h0, integral_mul_of_support (z := Φ.1 x) a, a1, one_mul]
      intro u hu
      exact congrArg (fun t : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) => t.1 x) hu
    have := H Φ Φ₀
    simp only [← e2, e3, e] at this
    exact this
  · obtain ⟨w, -, e2, e3⟩ := main Φ Φ₀
    simp only [← e2, e3]
    exact H w
end GlobalTheory.RootEx.FourierJacobi
