-- Prove2me | solution 1 for GlobalTheory.RootEx.Unfolding.fc_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:24.862837+00:00
-- url     : https://prove2.me/submissions/c4801d53-5d54-4b1f-9d1e-233f49d79f72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClosedEmbeddingAffPtUncurry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersectionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsMemSBEqOneOnCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvariaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpECutOmEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ColEInvMulAffPt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RowSupportUniform
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecompositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralWhittakerTwist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OrbitLocallyConstant
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_val
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_mul
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_omR_smooth
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_orbit_locallyConstant
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_ColumnSupport_opE_colE_eq_zero
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_continuous_colE
import Theorems.Thm_GlobalTheory_RootEx_Exchange_opE_exchange
import Theorems.Thm_GlobalTheory_RootEx_QuotStep_continuous_colE
import Theorems.Thm_GlobalTheory_RootEx_Radical_unipotent_radical_basic
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
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
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Unfolding
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ} {ψ : AddChar k Circle} (hψ : Continuous ψ) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ)
  {A P P' : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup P] [Module ℂ P] [AddCommGroup P'] [Module ℂ P']
  (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) {π : Representation ℂ (GL n k) P} {π' : Representation ℂ (GL n' k) P'}
  (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (φ : P') (F : A)
variable {μ σ θ b}
namespace GlobalTheory.RootEx.Unfolding
theorem _root_.solution (hp : 1 ≤ p) (hc : p < c) (hμ : IsOpen (μ.ker : Set kˣ)) (hb : IsPos ψ p π σ b)
    (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ) (Φ Φχ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (hΦχ : ∀ l : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] ℂ, l Φχ =
      ∫ u : n' → k, χ u * l (omR μ (rowE (c + 1) p u, 1) Φ) ∂(Measure.pi fun _ => ν))
    (h : GL (n ⊕ Fin c) k) :
    ∫ β : n → k, fc hψ ν μ σ θ b φ F p χ hχ Φ (colE c (p + 1) β * h) ∂(Measure.pi fun _ => ν) =
      b (θ φ (opL hψ ν p (omR μ (1, h) Φχ))) (σ h F) := by
  have := secondCountable k
  have := t2Space k
  set Φ' := omR μ (1, h) Φ with hΦ'
  let T : (n → k) → SB (Matrix n n' k) := fun β =>
    opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, colE c (p + 1) β) Φ'))
  have hT : IsLocallyConstant T :=
    ((orbit_locallyConstant (omR_smooth hμ) Φ').comp_continuous
      (continuous_const.prodMk ExchangeSupport.continuous_colE)).comp
      fun Ψ => opL hψ ν (p + 1) (cutL p χ hχ Ψ)
  obtain ⟨K, hK, HK⟩ := _root_.GlobalTheory.RootEx.ColumnSupport.opE_colE_eq_zero k n n' c p hc ψ ν μ Φ'.1 Φ'.2
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact (n → k) (Measure.pi fun _ => ν) _ T hT K hK
    fun β hβ => Subtype.ext (HK β hβ fun y => cut p χ y.toCols₁)
  have e : opL hψ ν p (omR μ (1, h) Φχ) = w := by
    apply Subtype.ext; funext x₀
    have h1 := hΦχ ((ev x₀).comp ((opL hψ ν p).comp (omR μ (1, h))))
    have h2 := hw (ev x₀)
    have h3 := (_root_.GlobalTheory.RootEx.Exchange.opE_exchange k n n' c p hp hc ψ hψ ν μ Φ'.1 Φ'.2 x₀ χ hχ).2.2
    refine h1.trans (Eq.trans ?_ (h3.trans h2.symm))
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [LinearMap.comp_apply]
    rw [← omR_val, hΦ', omR_mul, omR_mul, one_mul, mul_one, one_mul, mul_one]
    rfl
  rw [e]
  refine Eq.trans ?_ (hw ((b.flip (σ h F)).comp (θ φ))).symm
  refine integral_congr_ae (Eventually.of_forall fun β => ?_)
  have h1 := (Radical.unipotent_radical_basic k n c p).2.2.2.2.2.2.2 (p + 1) β (by omega)
  simp only [fc, T, LinearMap.comp_apply, LinearMap.flip_apply, hΦ', omR_mul, one_mul, map_mul,
    Module.End.mul_apply]
  rw [hb.1 _ _ h1.1, h1.2]
  simp
end GlobalTheory.RootEx.Unfolding
