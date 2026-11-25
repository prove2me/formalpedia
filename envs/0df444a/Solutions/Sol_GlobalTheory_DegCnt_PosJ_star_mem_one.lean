-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.star_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:14:22.673882+00:00
-- url     : https://prove2.me/submissions/599fa300-1981-4f4f-ad15-86417532d4fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormFlagLatticesNearUnderStabiliser

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.PosJ
variable {K : Type} [Field K] [NumberField K]
variable [StarRing K]
omit [NumberField K]
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : star x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  have : IsIntegral ℤ (star (algebraMap (𝓞 K) K y)) :=
    (RingOfIntegers.isIntegral_coe y).map (starRingEnd K).toIntAlgHom
  exact Submodule.mem_one.2 ⟨⟨_, this⟩, rfl⟩
end GlobalTheory.DegCnt.PosJ
