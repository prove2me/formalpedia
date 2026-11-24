-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobi.exponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:09.113972+00:00
-- url     : https://prove2.me/submissions/9e6b2762-3b38-46d2-8774-f820035dcb44

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
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_stab_nhds
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_represents_eval
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_exchanges_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_PowerTwoNormLowerBound_main
import Theorems.Thm_GlobalTheory_RootEx_Exchange_exchange_isPos
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_conj_colE
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_mul
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_smooth
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_val
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_orbit_locallyConstant
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_linear_change_of_variables
import Theorems.Thm_GlobalTheory_T_exists_schwartzBruhat_supported_nhds_integral_one
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
theorem _root_.solution : Exponents k := by
  intro n _ _ c ρ h1 hc ψ ν hψ hψ1 hν P A _ _ _ _ π σ _ hσ η _ _ fj b _ hb
  have h2 : ρ < c := by omega
  have := hν.1
  have main : ∀ s e : ℝ, s + e + 1 = 0 → IsFJInv η s π σ fj → ∀ (g : GL n k) φ v,
      b (twist η π g φ) (σ (embX c g) v) =
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ e : ℝ) : ℂ) * b φ v := by
    intro s e hse hinv g φ v
    obtain ⟨Ψ, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν _ (stab_nhds (ρ := ρ) hσ v)
    let T : (n → k) ≃ₜ (n → k) :=
      { toFun := fun β => (g⁻¹ : GL n k).val *ᵥ β
        invFun := fun β => g.val *ᵥ β
        left_inv := fun β => by simp only [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
        right_inv := fun β => by simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let Φ : SB (n → k) := ((η (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ)) •
        ⟨fun β => Ψ.1 (T β), Ψ.2.1.comp_continuous T.continuous, Ψ.2.2.comp_homeomorph T⟩
    have e1 := hinv g φ v Ψ Φ rfl
    have hpos : 0 < nabs k (Matrix.GeneralLinearGroup.det g) := by
      simp only [nabs]; exact_mod_cast distribHaarChar_pos
    have hinv' : (nabs k (Matrix.GeneralLinearGroup.det g⁻¹))⁻¹ = nabs k (Matrix.GeneralLinearGroup.det g) := by
      simp [nabs]
    have e2 : ∫ y, Φ.1 y ∂(Measure.pi fun _ => ν) = (η (Matrix.GeneralLinearGroup.det g) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (s + 1) : ℝ) : ℂ) := by
      have := (linear_change_of_variables k n n ν).1 g⁻¹ Ψ.1
      rw [a1, hinv'] at this
      change ∫ y, _ * Ψ.1 ((g⁻¹ : GL n k).val *ᵥ y) ∂_ = _
      rw [integral_const_mul, this, Real.rpow_add hpos]
      simp [mul_assoc]
    rw [represents_eval hb φ v Ψ a, a1, one_mul, represents_eval hb _ _ Φ, e2] at e1
    · change b ((η (Matrix.GeneralLinearGroup.det g) : ℂ) • π g φ) _ = _
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, ← e1]
      have : ((nabs k (Matrix.GeneralLinearGroup.det g) ^ e : ℝ) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (s + 1) : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ← Real.rpow_add hpos, show e + (s + 1) = 0 by linarith]
        simp
      linear_combination (-(η (Matrix.GeneralLinearGroup.det g) : ℂ) * b (π g φ) (σ (embX c g) v)) * this
    · intro y hy
      change _ * Ψ.1 ((g⁻¹ : GL n k).val *ᵥ y) = 0
      rw [a _ fun h => hy ?_, mul_zero]
      have h' : σ _ v = v := h
      rw [← QuotStep.conj_colE, map_inv, inv_inv] at h'
      change σ _ _ = _
      conv_rhs => rw [← h']
      simp only [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨main, fun hinv => ?_⟩
  have hp : IsPos ψ (ρ + 1) (twist η π) σ b :=
    ⟨hb.1, main _ _ (by rw [hc]; push_cast; ring) hinv⟩
  refine ⟨hp, fun b₀ h => ?_⟩
  obtain ⟨b', e, hb'⟩ := ((Exchange.exchange_isPos k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ).2.2 P _ b).2 hp
  have : b₀ = b' := by
    ext φ v
    rw [e, exchanges_eq h1 h2 hψ hψ1 hν hσ h]
  exact this ▸ hb'
end GlobalTheory.RootEx.FourierJacobi
