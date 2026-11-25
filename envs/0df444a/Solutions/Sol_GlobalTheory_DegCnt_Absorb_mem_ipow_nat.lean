-- Prove2me | solution 1 for GlobalTheory.DegCnt.Absorb.mem_ipow_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:30:20.460165+00:00
-- url     : https://prove2.me/submissions/dfaee6c1-356f-4143-b7f0-13c2ca5d1f69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SameBlockAppend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsStarStableIdealAbsorbingMinors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.Absorb
variable {K : Type} [Field K] [NumberField K]
open NumberField
open scoped Pointwise ENNReal Classical nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.DegCnt.Absorb
namespace _root_.GlobalTheory.DegCnt.Absorb
theorem _root_.solution (𝔡 : Ideal (𝓞 K)) (n : ℕ) (x : K) :
    x ∈ _root_.GlobalTheory.DegCnt.ipow 𝔡 n ↔ ∃ d ∈ 𝔡 ^ n, (d : K) = x := by
  rw [_root_.GlobalTheory.DegCnt.ipow, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coe,
    FractionalIdeal.mem_coeIdeal]
end _root_.GlobalTheory.DegCnt.Absorb
end GlobalTheory.DegCnt.Absorb
