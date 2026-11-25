-- Prove2me | solution 1 for GlobalTheory.NullExp.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:37.635356+00:00
-- url     : https://prove2.me/submissions/b5334ebd-7bb6-4e45-a292-166fc241d91e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_StalkMapInjectiveOfFlat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_Imports
import Theorems.Thm_GlobalTheory_LiftTest_main
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.NullExp
namespace GlobalTheory.NullExp
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k : ℕ) (σ : U.SecGT T k) (f : ∀ α, SecBT D T k α), U.ExpT T k σ f → NullFam I f := by
  intro R _ _ I D A G _ _ U T k σ f H e
  obtain ⟨s, hs⟩ := H e
  refine ⟨s, fun α hα Z r hr z J hJ => ?_⟩
  refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (f α)
    ?_ Z r hr z J hJ
  intro Z x r hx z J hJ
  have hc : (r ≫ (fst T D.P.A).left) ≫ T.hom = (x ≫ (fstG I e G).left) ≫ G.hom := by
    rw [Category.assoc, Category.assoc, Over.w (fst T D.P.A), Over.w (fstG I e G), ← Over.w (snd T D.P.A),
      ← Category.assoc, hx, Category.assoc, Over.w (U.gt e).pG]
  let rG : Z ⟶ (T ⊗ G).left := pullback.lift (r ≫ (fst T D.P.A).left) (x ≫ (fstG I e G).left) hc
  choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
  exact (hs Z x rG r (pullback.lift_snd _ _ _) hx (pullback.lift_fst _ _ _).symm z JG J hJG hJ).1 α hα
end GlobalTheory.NullExp
