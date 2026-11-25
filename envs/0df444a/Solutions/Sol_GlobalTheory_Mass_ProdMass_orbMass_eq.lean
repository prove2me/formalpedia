-- Prove2me | solution 1 for GlobalTheory.Mass.ProdMass.orbMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:31:20.601086+00:00
-- url     : https://prove2.me/submissions/3abbbbce-6c1f-4b1c-9aca-ba137baf7c43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassProdEqMul

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ProdMass
namespace GlobalTheory.Mass.ProdMass
theorem _root_.solution (G : Type) [Group G] {α : Type} [MulAction G α] (X : Set α) :
    orbMass G X = ∑' q : MulAction.orbitRel.Quotient G α, wt G X (Quotient.out q) := by
  unfold orbMass orbSum
  have := tsum_subtype {q : MulAction.orbitRel.Quotient G α | Quotient.out q ∈ X}
    (fun q => ((ENat.card (MulAction.stabilizer G (Quotient.out q)) : ℕ∞) : ℝ≥0∞)⁻¹ * 1)
  refine this.trans (tsum_congr fun q => ?_)
  simp [Set.indicator, wt]
end GlobalTheory.Mass.ProdMass
