-- Prove2me | solution 1 for GlobalTheory.AddCurve.algOverHom_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:39:17.526642+00:00
-- url     : https://prove2.me/submissions/6ed56250-7b5f-4371-9175-00b03619d754

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsUniversalChartOfFormalGroupChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TopLeAlgOverHom
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AddCurve
variable {k : Type} [CommRing k]
namespace GlobalTheory.AddCurve
theorem _root_.solution {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (f : A →ₐ[k] B) (h : B →ₐ[k] C) : algOverHom h ≫ algOverHom f = algOverHom (h.comp f) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp]; rfl
end GlobalTheory.AddCurve
