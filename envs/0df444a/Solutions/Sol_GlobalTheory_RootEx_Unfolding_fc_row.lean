-- Prove2me | solution 1 for GlobalTheory.RootEx.Unfolding.fc_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:13:26.193992+00:00
-- url     : https://prove2.me/submissions/10747362-f7b0-427c-9c6f-f4090d59e6be

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
import Theorems.Thm_GlobalTheory_RootEx_Unfolding_cut_eq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Radical_unipotent_radical_basic
import Theorems.Thm_GlobalTheory_RootEx_opE_om_target_unipotent
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
theorem _root_.solution (hp : 1 ≤ p) (hc : p < c) {b₁ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ} (hb₁ : ∀ φ v, b₁ φ v = exUp ν p σ (b φ) v)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (h : GL (n ⊕ Fin c) k) :
    ∫ u : n → k, fc hψ ν μ σ θ b φ F p (fun _ => 1) (IsLocallyConstant.const 1) Φ (rowE c p u * h)
        ∂(Measure.pi fun _ => ν) =
      b₁ (θ φ (opL hψ ν (p + 1) (omR μ (1, h) Φ))) (σ h F) := by
  rw [hb₁, exUp]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have e : opL hψ ν (p + 1) (cutL p (fun _ => 1) (IsLocallyConstant.const 1) (omR μ (1, rowE c p u * h) Φ)) =
      opL hψ ν (p + 1) (omR μ (1, h) Φ) := by
    have e0 : ∀ Ψ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
        cutL p (fun _ => 1) (IsLocallyConstant.const 1) Ψ = Ψ := fun Ψ => by
      apply Subtype.ext; funext y
      show cut p _ _ * Ψ.1 y = _
      rw [cut_eq hp hc, one_mul]
    have h1 := (Radical.unipotent_radical_basic k n c (p + 1)).2.2.2.2.2.2.1 p u (by omega)
    have := opE_om_target_unipotent k n n' c (p + 1) (by omega) hc ψ ν μ (omR μ (1, h) Φ).1 _ h1.1
    rw [← omR_val, omR_mul, one_mul, h1.2] at this
    rw [e0]
    apply Subtype.ext
    rw [neg_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_smul] at this
    exact this
  simp only [fc, e, map_mul, Module.End.mul_apply]
end GlobalTheory.RootEx.Unfolding
