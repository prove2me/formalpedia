-- Prove2me | solution 1 for GlobalTheory.LocFlat.PureColPf.le_of_mul_pow_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:11:49.973604+00:00
-- url     : https://prove2.me/submissions/421d42e2-4614-47c9-9020-614253594bf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPosition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.PureColPf
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
namespace GlobalTheory.LocFlat.PureColPf
theorem _root_.solution {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (r : ℕ) {y : k}
    (h : valuation k (y * (ϖ : k) ^ (r + 1)) < 1) : valuation k y ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k) := by
  have h1 := (hϖ _).1 h
  have h0 : ((ϖ : k) ^ (r + 1)) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have ey : y = (y * (ϖ : k) ^ (r + 1)) * ((ϖ : k) ^ (r + 1))⁻¹ := by field_simp
  have ec : (((ϖ ^ r)⁻¹ : kˣ) : k) = (ϖ : k) * ((ϖ : k) ^ (r + 1))⁻¹ := by
    simp [pow_succ]
  calc valuation k y = valuation k (y * (ϖ : k) ^ (r + 1)) * valuation k (((ϖ : k) ^ (r + 1))⁻¹) := by
        rw [← map_mul, ← ey]
    _ ≤ valuation k (ϖ : k) * valuation k (((ϖ : k) ^ (r + 1))⁻¹) := mul_le_mul_left h1 _
    _ = _ := by rw [← map_mul, ec]
end GlobalTheory.LocFlat.PureColPf
