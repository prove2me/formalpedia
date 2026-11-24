-- Prove2me | solution 1 for GlobalTheory.SerConj.semiMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:27.391721+00:00
-- url     : https://prove2.me/submissions/20d4e52b-938f-4166-8e41-09585b2bb870

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_GlobalTheory_SerConj_semiMap_tprod
import Theorems.Thm_GlobalTheory_SerConj_symm_smul
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_NT_IsTeich_injective
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
theorem _root_.solution (σ : ℂ ≃+* ℂ) (j : ∀ i, V i ≃+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v) :
    Function.Injective (semiMap σ.toRingHom (fun i => (j i).toAddMonoidHom) hj) := by
  refine Function.LeftInverse.injective
    (g := semiMap σ.symm.toRingHom (fun i => (j i).symm.toAddMonoidHom) fun i => symm_smul σ (j i) (hj i)) fun x => ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine (congrArg _ (semiMap_tprod _ _ _ r f)).trans ((semiMap_tprod _ _ _ _ _).trans ?_)
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
end GlobalTheory.SerConj
