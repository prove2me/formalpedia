-- Prove2me | solution 1 for GlobalTheory.RootEx.FourierJacobi.exists_represents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:29.428491+00:00
-- url     : https://prove2.me/submissions/f0cb564b-ab8a-4d59-b39e-575ec5c4b963

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
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_fj_conv
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_integral_mul_of_support
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobi_fj_indep
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_QuotInt_exists_open_stab
import Theorems.Thm_GlobalTheory_RootEx_ConjVol_colE_add
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_colE_add
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_exchange_support
import Theorems.Thm_GlobalTheory_RootEx_FourierJacobiGroup_colE_add
import Theorems.Thm_GlobalTheory_RootEx_RadicalDecomp_succ_decomp
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_unipotent_radical_basic
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_mul
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_smooth
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_val
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_orbit_locallyConstant
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_T_continuous_characters_locallyConstant_nonarchLocalField
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
theorem _root_.solution [ν.IsAddHaarMeasure] (h1 : 1 ≤ ρ) (h2 : ρ < c) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    (hσ : IsSmoothRep σ) (hfj : IsFJ ψ ρ σ fj) : ∃ b, Represents ψ ν ρ σ fj b := by
  choose Ψ hΨ hΨ1 using fun v : A => GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν _ (stab_nhds (ρ := ρ) hσ v)
  have key : ∀ U ∈ 𝓝 (0 : n → k), ∃ Φ : SB (n → k), (∀ y, y ∉ U → Φ.1 y = 0) ∧
      ∫ y, Φ.1 y ∂(Measure.pi fun _ => ν) = 1 ∧ ∀ φ v, U ⊆ stab ρ σ v → fj φ v (Ψ v) = fj φ v Φ := by
    intro U hU
    obtain ⟨Φ, a, a1⟩ := GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one k n ν U hU
    exact ⟨Φ, a, a1, fun φ v hv => fj_indep hfj φ v _ _ (hΨ v) (hΨ1 v) (fun y hy => a y fun h => hy (hv h)) a1⟩
  let b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ := LinearMap.mk₂ ℂ (fun φ v => fj φ v (Ψ v)) (by intros; simp) (by intros; simp)
    (by
      intro φ v w
      obtain ⟨Φ, -, -, h⟩ := key _ (inter_mem (stab_nhds (ρ := ρ) hσ v) (stab_nhds (ρ := ρ) hσ w))
      rw [h φ v Set.inter_subset_left, h φ w Set.inter_subset_right, h φ (v + w)]
      · simp
      · intro y hy
        change σ _ _ = _
        rw [map_add, show σ _ v = v from hy.1, show σ _ w = w from hy.2])
    (by
      intro z φ v
      obtain ⟨Φ, -, -, h⟩ := key _ (stab_nhds (ρ := ρ) hσ v)
      rw [h φ v subset_rfl, h φ (z • v)]
      · simp
      · intro y hy
        change σ _ _ = _
        rw [map_smul, show σ _ v = v from hy])
  have hb : ∀ φ v, b φ v = fj φ v (Ψ v) := fun _ _ => rfl
  have hN : ∀ φ, IsNEquiv ψ (ρ + 1) σ (b φ) := by
    intro φ g hg v
    obtain ⟨g₁, hg₁, u, rfl⟩ := RadicalDecomp.succ_decomp k n c ρ g hg
    obtain ⟨-, hs, -, -, -, -, hr, -⟩ := Radical.unipotent_radical_basic k n c (ρ + 1)
    have hu : {β : n → k | (ψ ((-u) ⬝ᵥ β) : ℂ) = 1} ∈ 𝓝 (0 : n → k) :=
      ((((GlobalTheory.T.continuous_characters_locallyConstant_nonarchLocalField k).2 ψ hψ).comp_continuous (f := fun β : n → k => (-u) ⬝ᵥ β)
        (by fun_prop)).isOpen_fiber 1).mem_nhds (by simp)
    obtain ⟨Φ, a, -, h⟩ := key _ (inter_mem (inter_mem (stab_nhds (ρ := ρ) hσ v)
      (stab_nhds (ρ := ρ) hσ (σ (g₁ * rowE c ρ u) v))) hu)
    rw [hb, hb, h φ v fun y hy => hy.1.1, h φ _ fun y hy => hy.1.2, map_mul, Module.End.mul_apply,
      hfj.2.2 φ _ Φ g₁ hg₁, hs _ hg₁.2 _ (hr ρ u (by omega)).1, (hr ρ u (by omega)).2, add_zero,
      hfj.2.1 φ v u Φ Φ]
    funext β
    by_cases hβ : (ψ ((-u) ⬝ᵥ β) : ℂ) = 1
    · rw [schM, hβ, one_mul]
    · rw [schM, a β fun h => hβ h.2, mul_zero]
  refine ⟨b, hN, fun φ v Φ₀ => ⟨?_, ?_⟩⟩
  · have := ((ExchangeSupport.exchange_support k n c ρ h1 h2 ψ hψ hψ1 ν A σ hσ (b φ) v).2 (hN φ)).1
    exact sb_int ⟨Φ₀.2.1.mul this.1, Φ₀.2.2.mul_right⟩
  · obtain ⟨K, hK, hKi⟩ := GlobalTheory.QuotInt.exists_open_stab (G := Multiplicative (n → k))
      (F := fun x => Φ₀.1 x.toAdd) Φ₀.2
    have hK' : {y : n → k | Multiplicative.ofAdd y ∈ K} ∈ 𝓝 (0 : n → k) := hK.mem_nhds K.one_mem
    obtain ⟨Φ, a, a1, h⟩ := key _ (inter_mem (stab_nhds (ρ := ρ) hσ v) hK')
    obtain ⟨w, -, e2, e3⟩ := fj_conv (ν := ν) hfj Φ₀ Φ
    have e : w = Φ₀ := by
      refine Subtype.ext (funext fun x => ?_)
      rw [e2, integral_mul_of_support (z := Φ₀.1 x) a, a1, one_mul]
      intro y hy
      rw [sub_eq_add_neg]
      exact hKi (Multiplicative.ofAdd x) _ (K.inv_mem hy.2)
    rw [← e, e3, e]
    congr 1; funext y
    rw [hb, h]
    intro β hβ
    change σ _ _ = _
    rw [← Module.End.mul_apply, ← map_mul, ← ExchangeSupport.colE_add, add_comm β y, ExchangeSupport.colE_add,
      map_mul, Module.End.mul_apply, show σ _ v = v from hβ.1]
end GlobalTheory.RootEx.FourierJacobi
