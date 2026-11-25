-- Prove2me | solution 1 for GlobalTheory.PsiScalUnit.ev_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:28:21.673254+00:00
-- url     : https://prove2.me/submissions/21f56a59-1c70-4b0a-a7a3-f26edce7b18e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiScalarsRelationsUpToBaseUnits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
noncomputable section
open GlobalTheory GlobalTheory.PsiScalUnit
variable {V : Type} [CommRing V] [IsDomain V]
namespace GlobalTheory.PsiScalUnit
theorem _root_.solution (z : (TK V).left) (w : Γ(Spec (CommRingCat.of V), ⊤)ˣ) :
    ∃ u : Vˣ, (gm (jK V) z ⊤ w).val = ev z (algebraMap V (FractionRing V) u.val) := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom.toMonoidHom w, ?_⟩
  rw [← gs_unit _ z ⊤ trivial, gs_eq _ z ⊤ trivial]
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at e
  exact congrArg ((TK V).left.presheaf.germ ⊤ z trivial).hom e.symm
end GlobalTheory.PsiScalUnit
