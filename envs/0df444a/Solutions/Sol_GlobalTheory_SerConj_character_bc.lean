-- Prove2me | solution 1 for GlobalTheory.SerConj.character_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:30.621947+00:00
-- url     : https://prove2.me/submissions/6bd4ca2f-d903-40d6-8f50-46568c5bb7b3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TYPES_trace_bcRepr


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
namespace GlobalTheory.SerConj
theorem _root_.solution (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ) : (bc σ τ).character γ = σ (τ.character γ) :=
  trace_bcRepr σ τ.ρ γ
end GlobalTheory.SerConj
