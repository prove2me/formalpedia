-- Prove2me | solution 1 for GlobalTheory.Mass.PrimCount.one_le_rd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:03:34.938091+00:00
-- url     : https://prove2.me/submissions/d734a9ec-1cfa-494d-9316-014ca2d79cd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardShortVectorsLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsRest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatInIsLattice

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimCount
namespace GlobalTheory.Mass.PrimCount
theorem _root_.solution (K : Type) [Field K] [NumberField K] : 1 ≤ 2 * vInv K := by
  have h : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero K)
    exact_mod_cast this
  have := Real.one_le_rpow h (z := (1 : ℝ) / (2 * fDeg K)) (by positivity)
  unfold vInv
  linarith
end GlobalTheory.Mass.PrimCount
