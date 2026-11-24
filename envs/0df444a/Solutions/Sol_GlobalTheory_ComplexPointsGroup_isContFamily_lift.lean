-- Prove2me | solution 1 for GlobalTheory.ComplexPointsGroup.isContFamily_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:42:53.836646+00:00
-- url     : https://prove2.me/submissions/240388aa-2df2-4bcc-aedf-c2726c786b0b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsTopologicalGroupComplexPoints
import Theorems.Thm_GlobalTheory_ComplexPointsGroup_isContFamily_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ComplexPointsGroup
variable {T : Type} [TopologicalSpace T]
variable (hv : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a))
include hv
namespace GlobalTheory.ComplexPointsGroup
theorem _root_.solution {A B : Over (Sp ℂ)} {a : T → (𝟙_ (Over (Sp ℂ)) ⟶ A)} {b : T → (𝟙_ (Over (Sp ℂ)) ⟶ B)}
    (ha : IsContFamily (X := A.left) (fun t => (a t).left)) (hb : IsContFamily (X := B.left) (fun t => (b t).left)) :
    IsContFamily (X := (A ⊗ B).left) (fun t => (lift (a t) (b t)).left) := by
  have H : IsPullback (fst A B).left (snd A B).left A.hom B.hom := IsPullback.of_hasPullback A.hom B.hom
  refine isContFamily_of_isPullback hv H ?_ ?_
  · convert ha using 2 with t
    exact congrArg CommaMorphism.left (lift_fst (a t) (b t))
  · convert hb using 2 with t
    exact congrArg CommaMorphism.left (lift_snd (a t) (b t))
end GlobalTheory.ComplexPointsGroup
