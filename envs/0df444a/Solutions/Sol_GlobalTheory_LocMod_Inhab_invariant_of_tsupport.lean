-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.invariant_of_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:48:49.133499+00:00
-- url     : https://prove2.me/submissions/ad55a11c-9db0-4ecc-9cf2-2bd3c224c953

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution {Φ : Matrix Y Y' k → ℂ} {K : AddSubgroup (Matrix Y Y' k)}
    (h : ∀ u ∈ K, ∀ t ∈ tsupport Φ, Φ (t + u) = Φ t) (u : Matrix Y Y' k) (hu : u ∈ K) (t : Matrix Y Y' k) :
    Φ (t + u) = Φ t := by
  by_cases ht : t ∈ tsupport Φ
  · exact h u hu t ht
  by_cases ht' : t + u ∈ tsupport Φ
  · rw [← h _ (neg_mem hu) _ ht', add_neg_cancel_right]
  · rw [image_eq_zero_of_notMem_tsupport ht, image_eq_zero_of_notMem_tsupport ht']
end GlobalTheory.LocMod.Inhab
