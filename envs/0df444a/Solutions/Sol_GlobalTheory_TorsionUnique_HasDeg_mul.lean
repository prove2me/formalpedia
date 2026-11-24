-- Prove2me | solution 1 for GlobalTheory.TorsionUnique.HasDeg.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:24:01.147957+00:00
-- url     : https://prove2.me/submissions/6c910470-e1b1-410f-9ecf-97909f3ccd1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfVanish

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TorsionUnique
variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix]
omit [DecidableEq Ix]
namespace GlobalTheory.TorsionUnique
namespace HasDeg
theorem _root_.solution {deg : Ix → ℕ} {k l : ℤ} {X Y : Matrix Ix Ix R}
    (hX : HasDeg deg k X) (hY : HasDeg deg l Y) : HasDeg deg (k + l) (X * Y) := by
  intro p q hpq
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases h : (deg p : ℤ) = deg r + k
  · rw [hY r q (by omega), mul_zero]
  · rw [hX p r h, zero_mul]
end HasDeg
end GlobalTheory.TorsionUnique
