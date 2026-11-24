-- Prove2me | solution 1 for GlobalTheory.SerConj.bcEquiv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:58.856276+00:00
-- url     : https://prove2.me/submissions/35247531-78c6-4fcf-95a7-3d129889dc25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
variable {Γ : Type} [Group Γ]
namespace GlobalTheory.SerConj
theorem _root_.solution (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (a : ℂ) (v : τ) :
    bcEquiv σ τ (a • v) = σ a • bcEquiv σ τ v := by
  refine funext fun i => ?_
  change σ ((Module.finBasis ℂ τ).repr (a • v) i) = σ a * σ ((Module.finBasis ℂ τ).repr v i)
  simp
end GlobalTheory.SerConj
