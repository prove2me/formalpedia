-- Prove2me | solution 1 for GlobalTheory.norm_coeff_le_of_hasSum_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:44.584278+00:00
-- url     : https://prove2.me/submissions/1dbd8b78-d7cf-4d51-995e-3da01b7a49bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ResidueNormValuationSubringEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Filter Topology MvPowerSeries
namespace GlobalTheory
theorem _root_.solution {C : Type*} [NontriviallyNormedField C]
    [IsUltrametricDist C] [IsAlgClosed C] {σ : Type*} {g : MvPowerSeries σ C} {f : (σ → C) → C}
    (hf : ∀ z : σ → C, (∀ i, ‖z i‖ < 1) →
      HasSum (fun t : σ →₀ ℕ => coeff t g * t.prod (z · ^ ·)) (f z)) {M : ℝ}
    (h : ∀ z : σ → C, (∀ i, ‖z i‖ < 1) → ‖f z‖ ≤ M) (t : σ →₀ ℕ) : ‖coeff t g‖ ≤ M :=
  haveI := infinite_residueField_of_isAlgClosed (C := C)
  norm_coeff_le_of_hasSum exists_lt_norm_lt_one_of_isAlgClosed (fun _ hx z hz =>
    ⟨_, hf z fun i => (hz i).trans_lt hx, h z fun i => (hz i).trans_lt hx⟩) t
end GlobalTheory
