-- Prove2me | solution 1 for GlobalTheory.FrameValue.isLift_rosati
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:17.121406+00:00
-- url     : https://prove2.me/submissions/5af43ff6-ea99-4c4e-91df-75b7420b7157

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
variable [IsCommMonObj A] {f f' : A ⟶ A} {F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
namespace GlobalTheory.FrameValue
theorem _root_.solution (hF : ∀ z, u.ex (F z) = u.ex z ≫ f) (hG : ∀ z, u.ex (G z) = u.ex z ≫ f') (x z : Fin g → ℂ) :
    IsLift u (Out.rosatiφ A f f') (lift (u.ex x) (u.ex z)).left (rosatiLift F G x z) := fun k => by
  have e : ∀ (q : A ⊗ A ⟶ A) w, lift (u.ex x) (u.ex z) ≫ q = u.ex w →
      (lift (u.ex x) (u.ex z)).left ≫ q.left = (u.ex w).left := fun q w hq => congrArg (fun m => m.left) hq
  fin_cases k
  · exact e _ (F x + z) ((MonObj.comp_mul _ _ _).trans (by simp [u.ex_add, hF]))
  · exact e _ (F x) (by simp [hF])
  · exact e _ z (by simp)
  · exact e _ (x + G z) ((MonObj.comp_mul _ _ _).trans (by simp [u.ex_add, hG]))
  · exact e _ x (by simp)
  · exact e _ (G z) (by simp [hG])
end GlobalTheory.FrameValue
