-- Prove2me | solution 1 for GlobalTheory.SerConj.symm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:32.34891+00:00
-- url     : https://prove2.me/submissions/2d401212-5493-4dfc-88d0-14235123a9e5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
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
theorem _root_.solution {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (σ : ℂ ≃+* ℂ)
    (j : A ≃+ B) (hj : ∀ (a : ℂ) v, j (a • v) = σ a • j v) (a : ℂ) (w : B) :
    j.symm (a • w) = σ.symm a • j.symm w := by
  apply j.injective
  rw [hj]; simp
end GlobalTheory.SerConj
