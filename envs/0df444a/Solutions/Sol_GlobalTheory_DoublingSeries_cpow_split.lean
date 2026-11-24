-- Prove2me | solution 1 for GlobalTheory.DoublingSeries.cpow_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:42.183951+00:00
-- url     : https://prove2.me/submissions/8be95308-f9d5-47c2-b0b9-acd693e10d6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RatFunDifferentiableOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
noncomputable section
open GlobalTheory GlobalTheory.DoublingSeries
namespace GlobalTheory.DoublingSeries
theorem _root_.solution {q : ℕ} (hq : 1 < q) (N : ℕ) (s : ℂ) {m : ℤ} (hm : 0 ≤ m) :
    (q : ℂ) ^ (-((N : ℂ) / 2 + s) * (m : ℂ)) =
      (((q : ℝ) ^ (-((N : ℝ) / 2) * (m : ℝ)) : ℝ) : ℂ) * ((q : ℂ) ^ (-s)) ^ m.toNat := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]
  congr 1
  have : ((m.toNat : ℕ) : ℂ) = (m : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hm
  push_cast
  rw [this]
  ring
end GlobalTheory.DoublingSeries
