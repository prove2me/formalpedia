-- Prove2me | solution 1 for GlobalTheory.FrameUnits.exists_period_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:47:37.910039+00:00
-- url     : https://prove2.me/submissions/497c5296-9fc6-4ce1-a9e6-ce11ebd88537

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.FrameUnits
theorem _root_.solution : ∃ R : ℝ, ∀ z : Fin g → ℂ, ∃ l ∈ u.Λ, ‖z + l‖ ≤ R := by
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  let b := (Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis ℝ u.Λ
  refine ⟨∑ i, ‖b i‖, fun z => ⟨-(ZSpan.floor b z : Fin g → ℂ), u.Λ.neg_mem ?_, ?_⟩⟩
  · exact ((Module.Free.chooseBasis ℤ u.Λ).ofZLatticeBasis_span ℝ u.Λ).le (ZSpan.floor b z).2
  · rw [← sub_eq_add_neg, ← ZSpan.fract_apply]
    exact ZSpan.norm_fract_le b z
end GlobalTheory.FrameUnits
