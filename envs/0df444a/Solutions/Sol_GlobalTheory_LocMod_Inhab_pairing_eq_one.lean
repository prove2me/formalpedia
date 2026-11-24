-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.pairing_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:48:52.772944+00:00
-- url     : https://prove2.me/submissions/5d91a123-aaf3-4695-a1f6-390cc63542b1

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
theorem _root_.solution {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {t b : Matrix Y Y' k}
    (h : ∀ r q, valuation k (b r q * t r q) ≤ valuation k (d : k)) : pairing ψ t b = 1 := by
  rw [pairing, (hd d).2 le_rfl _ (Valuation.map_sum_le _ fun r _ => Valuation.map_sum_le _ fun q _ => h r q)]
  rfl
end GlobalTheory.LocMod.Inhab
