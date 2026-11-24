-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.continuous_flipInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:37.322369+00:00
-- url     : https://prove2.me/submissions/fa03a658-55a2-4d71-8b77-99a36849414b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.LevelUnimod
theorem _root_.solution [TopologicalSpace k] (σ : ι ≃ ι) : Continuous (flipInv (k := k) σ) :=
  Units.continuous_iff.2 ⟨(Units.continuous_coe_inv.matrix_transpose).matrix_submatrix σ σ,
    (Units.continuous_val.matrix_transpose).matrix_submatrix σ σ⟩
end GlobalTheory.LevelUnimod
