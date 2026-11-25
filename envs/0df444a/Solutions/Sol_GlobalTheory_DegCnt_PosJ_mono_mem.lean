-- Prove2me | solution 1 for GlobalTheory.DegCnt.PosJ.mono_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:26:18.215555+00:00
-- url     : https://prove2.me/submissions/0243b69e-832d-4551-92bc-6f806d142b0b

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
open LaurentPolynomial
variable {K : Type} [Field K]
namespace GlobalTheory.DegCnt.PosJ
theorem _root_.solution (I : ℤ → AddSubgroup K) (h1 : (1 : K) ∈ I 0)
    (hmul : ∀ m n x y, x ∈ I m → y ∈ I n → x * y ∈ I (m + n)) (c : K) (m : ℤ) :
    C c * T m ∈ gradedSub I h1 hmul ↔ c ∈ I m := by
  rw [← single_eq_C_mul_T]
  constructor
  · intro h
    have := h m
    rwa [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at this
  · intro h n
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with e
    · exact e ▸ h
    · exact zero_mem _
end GlobalTheory.DegCnt.PosJ
