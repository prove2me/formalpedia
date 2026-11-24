-- Prove2me | solution 1 for GlobalTheory.AnalyticHom.le_preimage_nonzeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:35:50.182549+00:00
-- url     : https://prove2.me/submissions/b893b5be-c5a2-41cb-8616-fb46eb9171d2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_DenseClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsHomOfLinearScalingHermForm
import Theorems.Thm_GlobalTheory_AnalyticHom_le_preimage_mono
import Theorems.Thm_GlobalTheory_AnalyticHom_val_sec
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_valueRules


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.AnalyticHom
open CubeValues SymmetricSemicharacter ComplexPoints AffinePointValues
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
namespace GlobalTheory.AnalyticHom
theorem _root_.solution {L : LB X} (s : L.Sec) (j : L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus s ↔ valAt' x (L.U j) (s.f j) ≠ 0 := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (((valueRules X x).1 _).1 h)
    have hi' := ((valueRules X x).1 _).2 hi
    have h1 := ((valueRules X x).2.2.2.2.1 _ _).1 hi'
    rw [val_sec x s i j (le_preimage_mono x (X.basicOpen_le _) hi') hj] at h1
    exact right_ne_zero_of_mul h1
  · intro h
    exact le_preimage_mono x (le_iSup (fun k => X.basicOpen (s.f k)) j)
      (((valueRules X x).2.2.2.2.1 _ _).2 h)
end GlobalTheory.AnalyticHom
