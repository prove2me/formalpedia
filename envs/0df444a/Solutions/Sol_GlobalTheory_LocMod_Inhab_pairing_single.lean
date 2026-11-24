-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.pairing_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:48:54.498073+00:00
-- url     : https://prove2.me/submissions/a60e65a6-7042-4406-bfac-f71f86da7b47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing

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
theorem _root_.solution (ψ : AddChar k Circle) (t : Matrix Y Y' k) (r : Y) (q : Y') (c : k) :
    pairing ψ t (Matrix.single r q c) = ψ (c * t r q) := by
  unfold pairing
  rw [Finset.sum_eq_single r, Finset.sum_eq_single q]
  · simp
  · intro q' _ h; simp [h.symm]
  · simp
  · intro r' _ h; simp [h.symm]
  · simp
end GlobalTheory.LocMod.Inhab
