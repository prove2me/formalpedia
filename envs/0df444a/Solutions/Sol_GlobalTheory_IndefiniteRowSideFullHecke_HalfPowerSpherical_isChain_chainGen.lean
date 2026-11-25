-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical.isChain_chainGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:51:02.46039+00:00
-- url     : https://prove2.me/submissions/a0c3ee02-f3c3-49ba-be24-7fd4911451d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
theorem _root_.solution (α α' : kˣ) (m : ℕ) : IsChain α α' m (chainGen α α' m) := by
  refine ⟨fun i _ _ => ?_, fun j i _ _ => ?_⟩
  · congr 1
    unfold chainGen
    rw [mul_div_mul_left_eq_div, div_eq_mul_inv, ← _root_.zpow_sub]
    have : ((m / 2 : ℕ) : ℤ) - (i : ℤ) - (((m / 2 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ)) = 1 := by push_cast; ring
    rw [this, _root_.zpow_one]
  · congr 1
    unfold chainGen
    rw [← mul_assoc, ← mul_assoc]
    congr 2
    rw [← _root_.zpow_neg_one, ← _root_.zpow_add]
    congr 1
    push_cast; ring
end GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
