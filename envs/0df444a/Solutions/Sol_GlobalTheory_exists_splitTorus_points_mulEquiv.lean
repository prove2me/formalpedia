-- Prove2me | solution 1 for GlobalTheory.exists_splitTorus_points_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:22.162435+00:00
-- url     : https://prove2.me/submissions/b5561a7a-05a6-4b7e-ab84-cc44d056c099

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Theorems.Thm_GlobalTheory_splitTorusPointsEquiv_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (Z : Over S),
      ∃ e : (Z ⟶ splitTorus S X) ≃* (Multiplicative X →* Γ(Z.left, ⊤)ˣ),
        ∀ (t : Z ⟶ splitTorus S X) (χ : X),
          (e t (Multiplicative.ofAdd χ)).val = t.left.appTop.hom (charUnit S X χ).val :=
  fun S X _ Z => ⟨splitTorusPointsEquiv S X Z, splitTorusPointsEquiv_val S X Z⟩
end GlobalTheory
