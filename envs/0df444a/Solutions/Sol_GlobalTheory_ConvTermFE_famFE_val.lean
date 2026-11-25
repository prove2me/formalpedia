-- Prove2me | solution 1 for GlobalTheory.ConvTermFE.famFE_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:20:22.17481+00:00
-- url     : https://prove2.me/submissions/96221d32-18d2-4fcd-bf9f-66b4982d5998

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TranslationUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConvTermFe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


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
open GlobalTheory GlobalTheory.ConvTermFE
open ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.ConvTermFE
theorem _root_.solution (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s : Raw D F k) (hs : DegPre.FamFE D F k s) (mu β : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    sval (s (β + k • mu)) r.left z J = sval (s β) (r ≫ DegPre.trF D F mu).left z J *
      (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu β
  rw [← hv u hu hc Z r z J hJ]
  exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hs mu β u hu hc) _ r.left z J hJ
end GlobalTheory.ConvTermFE
