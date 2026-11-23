-- Prove2me | solution 1 for GlobalTheory.FrameValue.const_of_norm_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:12.49207+00:00
-- url     : https://prove2.me/submissions/0057903d-c81a-4e5e-b67c-8b39da3e8d6e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
namespace GlobalTheory.FrameValue
theorem _root_.solution (u : HolUnif A L g) {F : (Fin g → ℂ) → ℂ} (hF : Differentiable ℂ F)
    (hp : ∀ (l : u.Λ) z, ‖F (z + l)‖ = ‖F z‖) (z w : Fin g → ℂ) : F z = F w := by
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  have hc := (IsZLattice.isCompact_range_of_periodic u.Λ (fun z => ‖F z‖) hF.continuous.norm
    (fun z l hl => hp ⟨l, hl⟩ z)).isBounded
  obtain ⟨C, hC⟩ := hc.exists_norm_le
  refine hF.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩) z w
  rintro _ ⟨x, rfl⟩
  simpa using hC _ ⟨x, rfl⟩
end GlobalTheory.FrameValue
