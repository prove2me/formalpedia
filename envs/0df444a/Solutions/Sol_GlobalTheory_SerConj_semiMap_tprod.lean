-- Prove2me | solution 1 for GlobalTheory.SerConj.semiMap_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:30.709948+00:00
-- url     : https://prove2.me/submissions/d983fcd4-45f0-4d46-b3a0-460163d32671

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly

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
variable {ι : Type} {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
namespace GlobalTheory.SerConj
theorem _root_.solution (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (a : ℂ) (f : ∀ i, V i) :
    semiMap σ j hj (a • PiTensorProduct.tprod ℂ f) = σ a • PiTensorProduct.tprod ℂ fun i => j i (f i) := by
  rw [← PiTensorProduct.tprodCoeff_eq_smul_tprod]
  rfl
end GlobalTheory.SerConj
