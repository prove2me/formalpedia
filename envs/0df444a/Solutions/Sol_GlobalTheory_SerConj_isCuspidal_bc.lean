-- Prove2me | solution 1 for GlobalTheory.SerConj.isCuspidal_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:24.731355+00:00
-- url     : https://prove2.me/submissions/4ec24e37-e886-48fb-8e1a-0f414c04855e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_P2M_GlobalTheory_SerConj_bcEquiv___3b5f4a7a85e0
import Theorems.Thm_Formalism_L2_NT_IsTeich_injective
import Theorems.Thm_Formalism_L2_NT_IsTeich_map_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
variable {Γ : Type} [Group Γ]
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SerConj
theorem _root_.solution (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ (GL ι K)} (h : IsCuspidal K τ) : IsCuspidal K (bc σ τ) := by
  intro s b hb hs w hw
  obtain ⟨v, rfl⟩ := (bcEquiv σ τ).surjective w
  rw [h s b hb hs v fun u hu => (bcEquiv σ τ).injective ((bcEquiv_ρ σ τ u v).trans (hw u hu)), map_zero]
end GlobalTheory.SerConj
