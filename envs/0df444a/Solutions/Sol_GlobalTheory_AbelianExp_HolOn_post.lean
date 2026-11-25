-- Prove2me | solution 1 for GlobalTheory.AbelianExp.HolOn.post
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:32:22.179065+00:00
-- url     : https://prove2.me/submissions/b98fab3c-78ca-47de-9350-ade2045679d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ContinuousOnValue

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
open GlobalTheory GlobalTheory.AbelianExp
attribute [local instance] pointTopology
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] {W : Set E} {X Y : Over (Sp ℂ)} {a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)}
namespace GlobalTheory.AbelianExp
namespace HolOn
theorem _root_.solution
    (hval : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X) (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens)
      (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f)
    (h : HolOn W a) (q : X ⟶ Y) : HolOn W fun w => a w ≫ q := by
  intro U f
  have e1 : ∀ w, (a w ≫ q).left ⁻¹ᵁ U = (a w).left ⁻¹ᵁ (q.left ⁻¹ᵁ U) := fun w => by
    rw [Over.comp_left]
    simp
  have e2 : ∀ w, valAt' (a w ≫ q).left U f =
      valAt' (a w).left (q.left ⁻¹ᵁ U) ((q.left.app U).hom f) := fun w => by
    rw [Over.comp_left, hval]
  simp only [e1, e2]
  exact h (q.left ⁻¹ᵁ U) ((q.left.app U).hom f)
end HolOn
end GlobalTheory.AbelianExp
