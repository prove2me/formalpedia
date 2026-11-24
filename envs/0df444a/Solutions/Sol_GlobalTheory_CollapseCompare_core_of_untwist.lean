-- Prove2me | solution 1 for GlobalTheory.CollapseCompare.core_of_untwist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:59.860917+00:00
-- url     : https://prove2.me/submissions/07917794-9f0f-49cf-88c4-84f06e049d9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_FlatOmegaSeries
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemNormalizerOfTri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmulFrameMulFrameInvApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CoreIffCollapsesWith
import Theorems.Thm_GlobalTheory_CollapseCompare_flat_eq_smul
import Theorems.Thm_GlobalTheory_CollapseCompare_om_eq_smul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff
import Theorems.Thm_GlobalTheory_RootEx_VolN_det_unitri
import Theorems.Thm_GlobalTheory_RootEx_VolN_val_embX
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FlatOmegaSeries
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.CollapseCompare
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable [MeasurableSpace k] [BorelSpace k]
variable {ν : Measure k} {μX : Measure (GL n k)} {μG : Measure (GL (n ⊕ Fin c) k)}
  {J : Subgroup (GL (n ⊕ Fin c) k)} {bas : GL (n ⊕ Fin c) k} {ψ : AddChar k Circle} {μ : kˣ →* ℂˣ}
  {lam : J →* ℂˣ} {κ : ℝ}
omit [BorelSpace k]
namespace GlobalTheory.CollapseCompare
theorem _root_.solution {Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ}
    (H : Core ν μX μG J bas ψ 1 (untwist μ lam) Φ κ) : Core ν μX μG J bas ψ μ lam Φ κ := by
  intro V' V A _ _ _ _ _ _ π σ θ b hθ hb φ v hv f hf Ξ hΞ z
  refine H V' V A (SmGL.twist π (μ.comp Matrix.GeneralLinearGroup.det))
    (SmGL.twist σ (μ.comp Matrix.GeneralLinearGroup.det)⁻¹) θ b (fun γ φ Ψ Ψ' e => ?_)
    ⟨fun φ g hg a => ?_, fun g φ a => ?_⟩ φ v (fun j => ?_) f (fun h Ψ e => ?_) Ξ ?_ z
  · rw [SmGL.twist_apply, ← hθ γ φ Ψ (omS μ 1 γ Ψ) rfl, ← map_smul]
    exact congrArg _ (Subtype.ext (e.trans (om_eq_smul μ _ _)))
  · have : Matrix.GeneralLinearGroup.det g = 1 :=
      Units.ext (VolN.det_unitri (lev 1) _ (RootEx.Model.mem_N_iff.1 hg))
    simpa [this] using hb.1 φ g hg a
  · have : Matrix.GeneralLinearGroup.det (embX c g) = Matrix.GeneralLinearGroup.det g :=
      Units.ext (by simp [VolN.val_embX, Matrix.GeneralLinearGroup.val_det_apply])
    simp only [SmGL.twist_apply, map_smul, LinearMap.smul_apply, hb.2 g φ a, smul_eq_mul, MonoidHom.inv_apply,
      MonoidHom.comp_apply, this, Units.val_inv_eq_inv_val]
    field_simp
  · rw [SmGL.twist_apply, hv j, smul_smul]
    simp [untwist, mul_comm]
  · rw [hf h ((((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) • Ψ) (by rw [flat_eq_smul, ← e]; rfl)]
    simp
  · rw [hΞ]
    funext x
    simp only [xi]
    rw [flat_eq_smul μ]
    simp
end GlobalTheory.CollapseCompare
