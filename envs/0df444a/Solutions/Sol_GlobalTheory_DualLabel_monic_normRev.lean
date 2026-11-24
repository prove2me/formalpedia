-- Prove2me | solution 1 for GlobalTheory.DualLabel.monic_normRev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:03:23.46232+00:00
-- url     : https://prove2.me/submissions/a142fbd0-c046-433a-b394-a42271967c88

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd

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
open GlobalTheory GlobalTheory.DualLabel
namespace GlobalTheory.DualLabel
theorem _root_.solution {K : Type} [Field K] {f : K[X]} (h0 : f.coeff 0 ≠ 0) :
    (C (f.coeff 0)⁻¹ * f.reverse).Monic := by
  rw [Monic, leadingCoeff_mul, leadingCoeff_C, reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0,
    inv_mul_cancel₀ h0]
end GlobalTheory.DualLabel
