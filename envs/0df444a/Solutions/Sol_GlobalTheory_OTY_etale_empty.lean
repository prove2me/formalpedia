-- Prove2me | solution 1 for GlobalTheory.OTY.etale_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:06:57.109721+00:00
-- url     : https://prove2.me/submissions/02f31f3f-6178-4dd9-9071-e56cb2afd93b

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_EtaleEmpty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OTY
open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
noncomputable section
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace GlobalTheory.OTY
theorem _root_.solution (A : WeightedAtlas n Y ι La) (z : Y → V n) : Etale A ∅ z :=
  ⟨isOpen_empty, fun _ => by simp [differentiableOn_empty], fun _ _ h => h.elim⟩
end GlobalTheory.OTY
