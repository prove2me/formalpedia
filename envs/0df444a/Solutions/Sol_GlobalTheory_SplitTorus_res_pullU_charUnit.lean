-- Prove2me | solution 1 for GlobalTheory.SplitTorus.res_pullU_charUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:56:06.870322+00:00
-- url     : https://prove2.me/submissions/7e0eecc1-637a-46b7-a4fc-0763e2d834b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Theorems.Thm_GlobalTheory_SplitTorus_charUnit_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open AddMonoidAlgebra (single)
open GlobalTheory
open GlobalTheory.SplitTorus
variable {S : Scheme.{u}} {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  {T T' : Over S}
namespace GlobalTheory.SplitTorus
theorem _root_.solution (g : T ⟶ splitTorus S X) (a : X) (h : ⊤ ≤ g.left ⁻¹ᵁ ⊤) :
    (res h (pullU g.left ⊤ (charUnit S X a))).val = g.left.appTop.hom (chi X a) := by
  have : (res h (pullU g.left ⊤ (charUnit S X a))).val =
      (g.left.appLE ⊤ ⊤ h).hom (charUnit S X a).val := rfl
  rw [this, charUnit_val, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
end GlobalTheory.SplitTorus
