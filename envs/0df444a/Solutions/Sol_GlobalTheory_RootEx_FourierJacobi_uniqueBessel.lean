-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobi.uniqueBessel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:47.375796+00:00
-- url     : https://prove2.me/submissions/a45e40fe-7b8e-458e-aa36-3439d88a1130

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
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_sb_int
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_stab_nhds
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_exists_represents
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_represents_eval
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_exchanges_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_exchange_support
import Theorems.Thm_GlobalTheory_RootEx_Exchange_exchange_isPos
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_mul
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_smooth
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_val
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_orbit_locallyConstant
import Theorems.Thm_GlobalTheory_RootEx_exDown_exUp_and_exUp_exDown
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_T_exists_schwartzBruhat_supported_nhds_integral_one
import Theorems.Thm_GlobalTheory_T_schwartzFourierTransformPi_surjective_schwartzBruhat
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
variable {n : Type} [Fintype n] [DecidableEq n] {c ρ : ℕ} {ψ : AddChar k Circle} {ν : Measure k}
  {P A : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
  {σ : Representation ℂ (GL (n ⊕ Fin c) k) A}
  {fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ} {b b₀ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ}
namespace GlobalTheory.RootEx.FourierJacobi
theorem _root_.solution : UniqueBessel k := by
  intro n _ _ c ρ h1 hc ψ ν hψ hψ1 hν P A _ _ _ _ σ hσ fj hfj
  have h2 : ρ < c := by omega
  have := hν.1
  have := secondCountable k
  have := t2Space k
  have hS := ExchangeSupport.exchange_support k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ
  refine ⟨existsUnique_of_exists_of_unique (exists_represents h1 h2 hψ hψ1 hσ hfj) fun b b' hb hb' => ?_,
    fun b hb => ⟨existsUnique_of_exists_of_unique ?_ fun b₀ b₁ h h' => ?_, fun b₀ h φ v Φ₀ => ?_⟩⟩
  · ext φ v
    obtain ⟨Ψ, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν _ (stab_nhds (ρ := ρ) hσ v)
    have e := represents_eval hb φ v Ψ a
    rw [represents_eval hb' φ v Ψ a, a1, one_mul, one_mul] at e
    exact e.symm
  · choose L hL hL' using fun φ =>
      (Exchange.exchange_isPos k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ).2.1 (b φ) (hb.1 φ)
    refine ⟨⟨⟨L, fun φ φ' => ?_⟩, fun z φ => ?_⟩, hL', fun φ v => ⟨sb_int ((hS _ v).1 (hL' φ)).1, ?_⟩⟩
    · ext v
      simp only [hL, exDown, map_add, LinearMap.add_apply]
      exact integral_add (sb_int ((hS _ v).2 (hb.1 φ)).1) (sb_int ((hS _ v).2 (hb.1 φ')).1)
    · ext v
      simp only [hL, exDown, map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, integral_const_mul]
    · rw [← (exDown_exUp_and_exUp_exDown k n c ρ h1 h2 ψ hψ hψ1 ν hν A σ hσ (b φ) v).2 (hb.1 φ)]
      congr 1
      funext w
      exact (hL φ w).symm
  · ext φ v
    rw [exchanges_eq h1 h2 hψ hψ1 hν hσ h, exchanges_eq h1 h2 hψ hψ1 hν hσ h']
  · obtain ⟨s1, -, s3⟩ := (hS (b₀ φ) v).1 (h.1 φ)
    have hh := (GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat k n ψ hψ hψ1 ν hν).1 Φ₀
    refine ⟨sb_int ⟨hh.1.mul s1.1, hh.2.mul_right⟩, ?_⟩
    rw [(hb.2 φ v Φ₀).2]
    simp only [(h.2 φ _).2, s3, hat, ← integral_const_mul, ← integral_mul_const]
    rw [integral_integral_swap]
    · congr 1; funext u; congr 1; funext β; ring
    · have := ((sb_int (ν := ν) Φ₀.2).mul_prod (sb_int (ν := ν) s1)).bdd_mul (c := 1)
        (f := fun z : (n → k) × (n → k) => (ψ (z.2 ⬝ᵥ z.1) : ℂ))
        (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun z => (Circle.norm_coe _).le)
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [Function.uncurry]
      ring
end GlobalTheory.RootEx.FourierJacobi
