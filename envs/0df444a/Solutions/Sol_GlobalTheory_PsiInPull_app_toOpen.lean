-- Prove2me | solution 1 for GlobalTheory.PsiInPull.app_toOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:38:53.017986+00:00
-- url     : https://prove2.me/submissions/00e85c0a-ec76-42ca-9c41-5b2648072a4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg

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
noncomputable section
open GlobalTheory
open GlobalTheory.PsiInPull
namespace GlobalTheory.PsiInPull
theorem _root_.solution {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (V : (Spec (CommRingCat.of R)).Opens) (a : R) :
    ((specOf φ).app V).hom (DegPre.toOpen V a) = DegPre.toOpen (specOf φ ⁻¹ᵁ V) (φ a) := by
  have nat := congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  have e := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    ((specOf φ).naturality (homOfLE (le_top : V ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp only [DegPre.toOpen, RingHom.comp_apply]
  rw [e, nat]
  rfl
end GlobalTheory.PsiInPull
