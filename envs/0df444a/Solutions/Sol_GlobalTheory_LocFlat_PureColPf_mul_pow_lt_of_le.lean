-- Prove2me | solution 1 for GlobalTheory.LocFlat.PureColPf.mul_pow_lt_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:11:32.52128+00:00
-- url     : https://prove2.me/submissions/b65a6c6f-cc2b-4aad-a567-b6a3ba3726de

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
    (h : valuation k y ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k)) : valuation k (y * (ϖ : k) ^ (r + 1)) < 1 := by
  have h0 : ((ϖ : k) ^ (r + 1)) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
  have e : (((ϖ ^ r)⁻¹ : kˣ) : k) * (ϖ : k) ^ (r + 1) = ϖ := by
    simp [pow_succ]
  have h1 : valuation k (ϖ : k) < 1 := (hϖ _).2 le_rfl
  calc valuation k (y * (ϖ : k) ^ (r + 1)) = valuation k y * valuation k ((ϖ : k) ^ (r + 1)) := map_mul _ _ _
    _ ≤ valuation k (((ϖ ^ r)⁻¹ : kˣ) : k) * valuation k ((ϖ : k) ^ (r + 1)) := mul_le_mul_left h _
    _ = valuation k (ϖ : k) := by rw [← map_mul, e]
    _ < 1 := h1
end GlobalTheory.LocFlat.PureColPf
