-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.ipow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:34.69692+00:00
-- url     : https://prove2.me/submissions/6aa12b2f-d467-4028-bc05-de4bab085ade

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
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (m n : ℤ) : ipow 𝔡 (m + n) = ipow 𝔡 m * ipow 𝔡 n := by
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  rw [ipow, ipow, ipow, zpow_add₀ h0, FractionalIdeal.coe_mul]
end GlobalTheory.DegCnt.PosJ
