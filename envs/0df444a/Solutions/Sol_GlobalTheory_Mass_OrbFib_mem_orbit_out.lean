-- Prove2me | solution 1 for GlobalTheory.Mass.OrbFib.mem_orbit_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:24.64423+00:00
-- url     : https://prove2.me/submissions/1dc2fd03-efdc-404d-8236-2b39661292d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassEqWeightedSumFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.OrbFib
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]
open NumberField Matrix
open scoped ENNReal Classical
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]
namespace GlobalTheory.Mass.OrbFib
namespace _root_.GlobalTheory.Mass.OrbFib
theorem _root_.solution (q : MulAction.orbitRel.Quotient G α) (x : α) :
    x ∈ MulAction.orbit G (Quotient.out q) ↔ (Quotient.mk (MulAction.orbitRel G α) x) = q := by
  constructor
  · intro h
    exact (Quotient.sound h).trans (Quotient.out_eq q)
  · intro h
    exact Quotient.exact (h.trans (Quotient.out_eq q).symm)
end _root_.GlobalTheory.Mass.OrbFib
end GlobalTheory.Mass.OrbFib
