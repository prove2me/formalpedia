-- Prove2me | solution 1 for GlobalTheory.SublatCount.smul_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:05:41.471525+00:00
-- url     : https://prove2.me/submissions/65353d33-cdd6-40b6-9bdb-35ede9091db1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardSublatticesQuotientProdDegreeOnePrimes

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
open GlobalTheory GlobalTheory.SublatCount
variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]
namespace GlobalTheory.SublatCount
theorem _root_.solution {I : Ideal O} {c : O} (hc : c ∈ I) (y : O ⧸ I) : c • y = 0 := by
  have : algebraMap O (O ⧸ I) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
  rw [Algebra.smul_def, this, zero_mul]
end GlobalTheory.SublatCount
