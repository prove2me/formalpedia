-- Prove2me | solution 1 for GlobalTheory.UnifCompare.isDiff_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:32:54.875961+00:00
-- url     : https://prove2.me/submissions/59047e27-e219-44ed-97d3-b4ab75b11adb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_UnimodularAndTangentOfIsAH
import Theorems.Thm_GlobalTheory_coe_modNEquivTorsion_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.coe_modNEquivTorsion_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.UnifCompare
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}
namespace GlobalTheory.UnifCompare
theorem _root_.solution (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) (w : Fin g → ℂ) (v : epsR ℂ ⟶ A) :
    u.IsDiff w v ↔ u₀.IsDiff (F w) v := by
  have key : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w =
        fderiv ℂ (fun z => valAt' (u₀.ex z).left U f) 0 (F w) := fun U f => by
    have e : (fun z => valAt' (u.ex z).left U f) = (fun z => valAt' (u₀.ex z).left U f) ∘ F := by
      funext z
      simp only [Function.comp, hF]
    rw [e, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
    rfl
  simp only [HolUnif.IsDiff, key]
end GlobalTheory.UnifCompare
