-- Prove2me | solution 1 for GlobalTheory.PointwiseRegular.exists_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:06.931942+00:00
-- url     : https://prove2.me/submissions/204599c8-a4c6-4ac9-ad33-718f7c3f5d23

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniqueHomOfLocallyRegular
import Theorems.Thm_P2M_GlobalTheory_ComplexPoints_eq_of_valAt__eq_437ab7d0d2f0
import Theorems.Thm_P2M_GlobalTheory_valAt__add_b0728a15060b
import Theorems.Thm_P2M_GlobalTheory_valAt__mul_dca2439ccec2
import Theorems.Thm_P2M_GlobalTheory_valAt__one_9935cf2928d8
import Theorems.Thm_P2M_GlobalTheory_valAt__zero_f075fc9dd23d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.PointwiseRegular
namespace GlobalTheory.PointwiseRegular
theorem _root_.solution {X Y : Over (Sp ℂ)} [IsReduced Y.left] [LocallyOfFiniteType Y.hom]
    (F : (𝟙_ (Over (Sp ℂ)) ⟶ Y) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : Y.left.Opens) (D : X.left.Opens)
    (hF : ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U → ⊤ ≤ (F y).left ⁻¹ᵁ D)
    (h : ∀ φ : Γ(X.left, D), ∃ ρ : Γ(Y.left, U), ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U ρ = valAt' (F y).left D φ) :
    ∃ r : Γ(X.left, D) →+* Γ(Y.left, U), ∀ φ, ∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U (r φ) = valAt' (F y).left D φ := by
  choose r hr using h
  have ext : ∀ a b : Γ(Y.left, U), (∀ y : (𝟙_ (Over (Sp ℂ)) ⟶ Y), ⊤ ≤ y.left ⁻¹ᵁ U →
      valAt' y.left U a = valAt' y.left U b) → a = b := fun a b hab =>
    ComplexPoints.eq_of_valAt'_eq Y.hom U a b fun x hx hU => hab (Over.homMk x hx) hU
  refine ⟨⟨⟨⟨r, ?_⟩, ?_⟩, ?_, ?_⟩, hr⟩
  · exact ext _ _ fun y hy => by
      rw [hr _ y hy]; exact (valAt'_one _ (hF y hy)).trans (valAt'_one _ hy).symm
  · exact fun a b => ext _ _ fun y hy => by
      refine (hr _ y hy).trans (((valAt'_mul _ _ _ _).trans ?_).trans (valAt'_mul _ _ _ _).symm)
      rw [hr _ y hy, hr _ y hy]
  · exact ext _ _ fun y hy => (hr _ y hy).trans ((valAt'_zero _ _).trans (valAt'_zero _ _).symm)
  · exact fun a b => ext _ _ fun y hy => by
      refine (hr _ y hy).trans (((valAt'_add _ _ _ _).trans ?_).trans (valAt'_add _ _ _ _).symm)
      exact congrArg₂ (· + ·) (hr _ y hy).symm (hr _ y hy).symm
end GlobalTheory.PointwiseRegular
