-- Prove2me | solution 1 for GlobalTheory.SerConj.hasLabelO_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:23.926447+00:00
-- url     : https://prove2.me/submissions/2994e155-f2df-4381-a657-fcb586ea9299

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_GlobalTheory_SerConj_character_bc
import Theorems.Thm_GlobalTheory_SerConj_simple_bc
import Theorems.Thm_GlobalTheory_SerConj_isCuspidal_bc
import Theorems.Thm_GlobalTheory_SerConj_isConstituent_bc
import Theorems.Thm_GlobalTheory_SerConj_normRev_prod
import Theorems.Thm_Formalism_L2_PT_character_transp
import Theorems.Thm_Formalism_L2_PT_isCuspidal_transp
import Theorems.Thm_Formalism_L2_PT_simple_transp
import Theorems.Thm_GlobalTheory_DualLabel_lab_dual
import Theorems.Thm_PI_SerBridgeGLW_conjugate_character_formula


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
variable {K : Type} [Field K]
variable [Fintype K] [DecidableEq K] {Cv : LabelConv K}
namespace GlobalTheory.SerConj
theorem _root_.solution (O : LabelMap K Cv) (hO : LabelMapEquivariant O) {ι : Type} [Fintype ι] [DecidableEq ι]
    {τ : FDRep ℂ (GL ι K)} {f : K[X]} (h : HasLabelO O τ f) :
    HasLabelO O (bc (starRingAut : ℂ ≃+* ℂ) τ) (C (f.coeff 0)⁻¹ * f.reverse) := by
  obtain ⟨s, b, lam, hb, hl, hc, rfl⟩ := h
  refine ⟨s, b, fun c => bc starRingAut (lam c), hb, fun c => ⟨simple_bc _ (hl c).1, isCuspidal_bc _ (hl c).2⟩,
    isConstituent_bc _ b lam hc, ?_⟩
  rw [normRev_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  have hd : 1 ≤ Fintype.card {i // b i = c} := by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  refine (GlobalTheory.DualLabel.lab_dual O hO _ _ _ hd (Formalism.L2.PT.simple_transp _ (hl c).1)
    (Formalism.L2.PT.isCuspidal_transp _ (hl c).2) (Formalism.L2.PT.simple_transp _ (simple_bc _ (hl c).1))
    (Formalism.L2.PT.isCuspidal_transp _ (isCuspidal_bc _ (hl c).2)) fun γ => ?_).symm
  change (transp _ (bc starRingAut (lam c))).character γ = (transp _ (lam c)).character γ⁻¹
  rw [Formalism.L2.PT.character_transp, Formalism.L2.PT.character_transp, character_bc, map_inv]
  exact PI.SerBridgeGLW.conjugate_character_formula _ _ _
end GlobalTheory.SerConj
