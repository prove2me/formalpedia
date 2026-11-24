-- Prove2me | solution 1 for GlobalTheory.DoublingSeries.ratFun_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:44.128847+00:00
-- url     : https://prove2.me/submissions/f52fda02-f8e0-4446-82dd-36c0da2347bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RatFunDifferentiableOn
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
noncomputable section
open GlobalTheory GlobalTheory.DoublingSeries
namespace GlobalTheory.DoublingSeries
theorem _root_.solution {q : ℕ} (hq : 1 < q) (N : ℕ) (α : Fin N → ℂˣ) (s : ℂ) :
    lFactor q α (s + 1 / 2) * lFactor q α⁻¹ (s + 1 / 2) * invNormFactor q N s =
      ratFun q N α ((q : ℂ) ^ (-s)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have h1 : (q : ℂ) ^ (-(s + 1 / 2)) = (q : ℂ) ^ (-(1 / 2 : ℂ)) * (q : ℂ) ^ (-s) := by
    rw [← Complex.cpow_add _ _ hq0]; ring_nf
  have h2 : ∀ i : ℕ, (q : ℂ) ^ (-(2 * s + i)) = (q : ℂ) ^ (-(i : ℂ)) * ((q : ℂ) ^ (-s)) ^ 2 := fun i => by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hq0]; push_cast; ring_nf
  simp only [lFactor, invNormFactor, ratFun, h1, h2, Pi.inv_apply, mul_assoc]
end GlobalTheory.DoublingSeries
