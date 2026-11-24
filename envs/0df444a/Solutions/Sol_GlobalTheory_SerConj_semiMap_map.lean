-- Prove2me | solution 1 for GlobalTheory.SerConj.semiMap_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:26:57.95688+00:00
-- url     : https://prove2.me/submissions/98f98cb3-5a7c-4140-99fa-c17506b9a7c8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_GlobalTheory_SerConj_semiMap_tprod
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
variable {ι : Type} {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
namespace GlobalTheory.SerConj
theorem _root_.solution (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (A : ∀ i, V i →ₗ[ℂ] V i) (B : ∀ i, W i →ₗ[ℂ] W i) (h : ∀ i v, j i (A i v) = B i (j i v))
    (x : PiTensorProduct ℂ V) :
    semiMap σ j hj (PiTensorProduct.map A x) = PiTensorProduct.map B (semiMap σ j hj x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.map_tprod, semiMap_tprod, semiMap_tprod, map_smul, PiTensorProduct.map_tprod]
    simp only [h]
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.SerConj
