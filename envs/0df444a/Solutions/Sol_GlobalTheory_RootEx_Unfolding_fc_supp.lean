-- Prove2me | solution 1 for GlobalTheory.RootEx.Unfolding.fc_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:58.261769+00:00
-- url     : https://prove2.me/submissions/2ad4a5ce-db37-4a70-90f0-ddcb24e047f2

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
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_ExchangeSupport_continuous_rowE
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_mul
import Theorems.Thm_GlobalTheory_RootEx_Radical_exists_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_RowSupport_row_support_uniform
import Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
import Theorems.Thm_GlobalTheory_RootEx_VolN_exists_of_mem_R
import Theorems.Thm_GlobalTheory_RootEx_opE_support_compact_mod_R
import Theorems.Thm_GlobalTheory_StepData_IntM_mul
import Theorems.Thm_GlobalTheory_T_rootExchangeUnipotentSubgroup_succ_decomposition
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_matrix_exists_open_addSubgroup_invariant
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
theorem _root_.solution (hp : 1 ≤ p) (hc : p < c) (hψ1 : ψ ≠ 1) (hσ : IsSmoothRep σ) (hb : IsPos ψ p π σ b)
    (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) :
    ∃ Ω : Set (GL (n ⊕ Fin c) k), IsCompact Ω ∧ ∀ χ hχ h, fc hψ ν μ σ θ b φ F p χ hχ Φ h ≠ 0 →
      ∃ x : GL n k, ∃ u ∈ N k n c p ⊓ N k n c (p + 1), ∃ w ∈ Ω, h = embX c x * u * w := by
  obtain ⟨Λ, hΛ, hΦ⟩ := GlobalTheory.T.schwartzBruhat_matrix_exists_open_addSubgroup_invariant k _ _ Φ.1 Φ.2
  obtain ⟨Ω, hΩ, H⟩ := opE_support_compact_mod_R k n n' c (p + 1) (by omega) hc ψ hψ hψ1 ν
    (tsupport Φ.1) Φ.2.2 Λ hΛ
  obtain ⟨B, hB, HB⟩ := _root_.GlobalTheory.RootEx.RowSupport.row_support_uniform k n c p hp hc ψ hψ1 A σ hσ F Ω hΩ
  refine ⟨_, (hB.image (ExchangeSupport.continuous_rowE (c := c) (p := p))).mul hΩ, fun χ hχ h hne => ?_⟩
  have h1 : opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, h) Φ)) ≠ 0 := by
    intro e; apply hne; unfold fc; rw [e]; simp
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, (opL hψ ν (p + 1) (cutL p χ hχ (omR μ (1, h) Φ))).1 x₀ ≠ 0 := by
    by_contra hh
    push Not at hh
    exact h1 (Subtype.ext (funext hh))
  obtain ⟨r, hr, w, hw, rfl⟩ := H μ Φ.1 (subset_tsupport _) hΦ (cut p χ) (cut_lc p hχ) h x₀ hx₀
  obtain ⟨x, g, hg, rfl⟩ := Radical.exists_of_mem_R hr
  obtain ⟨g₁, hg₁, u, rfl⟩ := GlobalTheory.T.rootExchangeUnipotentSubgroup_succ_decomposition k n c p g hg
  refine ⟨x, g₁, hg₁, rowE c p u * w, Set.mul_mem_mul (Set.mem_image_of_mem _ ?_) hw, by group⟩
  by_contra hu
  apply hne
  unfold fc
  generalize θ φ _ = φ₁
  have e : φ₁ = π x (π x⁻¹ φ₁) := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [e]
  simp only [map_mul, Module.End.mul_apply]
  rw [hb.2, hb.1 _ g₁ hg₁.1, HB _ (hb.1 _) w hw u hu]
  simp
end GlobalTheory.RootEx.Unfolding
