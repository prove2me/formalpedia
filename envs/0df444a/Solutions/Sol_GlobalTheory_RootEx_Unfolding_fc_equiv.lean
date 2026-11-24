-- Prove2me | solution 1 for GlobalTheory.RootEx.Unfolding.fc_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:52.455333+00:00
-- url     : https://prove2.me/submissions/d232ecaa-4896-4afa-8ce2-e846c8327b00

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
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_OpELevi_nabs_pos
import Theorems.Thm_GlobalTheory_RootEx_opE_cut_om_equivariant
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos
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
theorem _root_.solution (hp : 1 ≤ p) (hc : p < c)
    (hθ : ∀ g h φ Ψ Ψ', Ψ'.1 = om μ g h Ψ.1 → θ (π' g φ) Ψ' = π h (θ φ Ψ)) (hb : IsPos ψ p π σ b)
    (χ : (n' → k) → ℂ) (hχ : IsLocallyConstant χ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (x : GL n k) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c p ⊓ N k n c (p + 1)) (h : GL (n ⊕ Fin c) k) :
    fc hψ ν μ σ θ b φ F p χ hχ Φ (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) - 2 * p) : ℝ) : ℂ) *
        fc hψ ν μ σ θ b φ F p χ hχ Φ h := by
  unfold fc
  set Ψ := opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, h) Φ)) with hΨ
  have e1 : opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, embX c x * u * h) Φ)) =
      (((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        (ψ (-simpleSum u) : ℂ)) • omR μ (1, x) Ψ := by
    have := _root_.GlobalTheory.RootEx.opE_cut_om_equivariant k n n' c p hp hc ψ ν μ χ (omR μ (1, h) Φ).1 x u hu
    rw [← omR_val, omR_mul, one_mul] at this
    exact Subtype.ext this
  have e2 : θ φ (omR μ (1, x) Ψ) = π x (θ φ Ψ) := by
    have := hθ 1 x φ Ψ _ (omR_val μ 1 x Ψ)
    rwa [map_one, Module.End.one_apply] at this
  have e3 : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]; simp
  have e4 : (nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) - 2 * p) : ℝ) =
      nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p + 1 : ℕ) : ℝ)) *
      nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) := by
    rw [← Real.rpow_add (nabs_pos k _)]; congr 1; push_cast; ring
  rw [e1, map_smul, map_smul, e2, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    LinearMap.smul_apply, hb.2, hb.1 _ u hu.1, e4]
  push_cast
  rw [smul_eq_mul]
  linear_combination (((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((p : ℝ) + 1)) : ℝ) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - p) : ℝ) : ℂ) * b (θ φ Ψ) (σ h F)) * e3
end GlobalTheory.RootEx.Unfolding
