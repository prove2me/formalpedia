-- Prove2me | solution 1 for GlobalTheory.TorsionUnique.HasDeg.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:21.407274+00:00
-- url     : https://prove2.me/submissions/a3be5adf-7e2f-4217-8bea-a02bf1f1a973

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
omit [Fintype Ix] [DecidableEq Ix]
namespace GlobalTheory.TorsionUnique
namespace HasDeg
theorem _root_.solution {deg : Ix → ℕ} {k : ℤ} {X Y : Matrix Ix Ix R}
    (hX : HasDeg deg k X) (hY : HasDeg deg k Y) : HasDeg deg k (X - Y) := by
  intro p q hpq
  rw [Matrix.sub_apply, hX p q hpq, hY p q hpq, sub_zero]
end HasDeg
end GlobalTheory.TorsionUnique
