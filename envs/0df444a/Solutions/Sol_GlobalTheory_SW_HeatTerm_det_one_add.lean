-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.det_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:08.854932+00:00
-- url     : https://prove2.me/submissions/a5debeb9-a7da-4e59-879a-9189b2651a0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
namespace GlobalTheory.SW.HeatTerm
theorem _root_.solution {N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (a b : Fin N) (s : ℂ) :
    (1 + S * Matrix.single a b s).det = 1 + s * S b a := by
  have : S * Matrix.single a b s =
      replicateCol Unit (fun i => S i a * s) * replicateRow Unit (Pi.single b (1 : ℂ)) := by
    ext i j
    by_cases hj : j = b
    · subst hj; simp [Matrix.mul_apply, Matrix.single_apply]
    · simp [Matrix.mul_apply, Matrix.single_apply, hj, Ne.symm hj]
  rw [this, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp [mul_comm]
end GlobalTheory.SW.HeatTerm
