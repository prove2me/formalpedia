-- Prove2me | solution 1 for GlobalTheory.SerConj.semiMap_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:52.515855+00:00
-- url     : https://prove2.me/submissions/dc8627e2-1e2b-4e0b-9e92-ce960a8d3e40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_GlobalTheory_SerConj_semiMap_tprod

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
    (a : ℂ) (x : PiTensorProduct ℂ V) : semiMap σ j hj (a • x) = σ a • semiMap σ j hj x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [smul_smul, semiMap_tprod, semiMap_tprod, smul_smul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
end GlobalTheory.SerConj
