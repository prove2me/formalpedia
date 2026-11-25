-- Prove2me | solution 1 for GlobalTheory.UU.sval_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:17:41.030909+00:00
-- url     : https://prove2.me/submissions/508dcf9a-4ea5-4d4a-a22d-8b311e98789f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R]
variable {I : Ideal R} {D : DegPre R} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace GlobalTheory.UU
theorem _root_.solution {W : Type} [CommRing W] [Algebra R W] {k : ℕ} (a : Multiplicative D.X →* Wˣ)
    (f : ∀ α, SecBT D (TA R W) k α) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TA R W ⊗ D.P.A).left) (z : Z) {J}
    (hJ : Good D.P.L z J) :
    sval (twist a f α) r z J =
      gs r z ⊤ (scal (R := W) (fst (TA R W) D.P.A).left (a (Multiplicative.ofAdd α)).val) * sval (f α) r z J := by
  unfold twist sval DVR.SecOps.secScale
  have hm := hJ.mem (famφT D (TA R W) α) r
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm _))
end GlobalTheory.UU
