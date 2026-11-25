-- Prove2me | solution 1 for GlobalTheory.Mass.OrbMono.orbSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:50.923022+00:00
-- url     : https://prove2.me/submissions/8dac567a-deae-4f38-9685-cd2c8287f53f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumMonoSubadditive

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.OrbMono
namespace GlobalTheory.Mass.OrbMono
theorem _root_.solution (G α : Type) [Group G] [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) :
    orbSum G X N = ∑' q : MulAction.orbitRel.Quotient G α,
      if Quotient.out q ∈ X then
        ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ * N (Quotient.out q)
      else 0 := by
  exact (tsum_subtype {q : MulAction.orbitRel.Quotient G α | Quotient.out q ∈ X}
    (fun q => ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ *
      N (Quotient.out q))).trans (tsum_congr fun q => by simp [Set.indicator_apply])
end GlobalTheory.Mass.OrbMono
