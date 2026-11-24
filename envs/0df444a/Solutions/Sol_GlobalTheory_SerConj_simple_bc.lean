-- Prove2me | solution 1 for GlobalTheory.SerConj.simple_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:26.094903+00:00
-- url     : https://prove2.me/submissions/1e8b4bfd-0716-4c63-8100-df5dbdf449a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_GlobalTheory_SerConj_character_bc
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
theorem _root_.solution [Fintype Γ] (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ Γ} (h : Simple τ) : Simple (bc σ τ) := by
  rw [FDRep.simple_iff_char_is_norm_one] at h ⊢
  simp only [character_bc]
  rw [← map_natCast σ, ← h, map_sum]
  simp only [map_mul]
end GlobalTheory.SerConj
