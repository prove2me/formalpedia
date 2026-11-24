-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.loc_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:07:58.015057+00:00
-- url     : https://prove2.me/submissions/5ab695b8-3c4b-4dd7-9549-9cfee2aa1eb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
import Theorems.Thm_GlobalTheory_AbLaw_Seesaw_app_cst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw
variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
variable {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M)
variable {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
  (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
include h
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution (v : Fin P.a → R) (i : P.I) : loc P π f' (g ∘ v) i = (π.app (P.W i)).hom (loc₀ P v i) := by
  simp only [loc, loc₀, map_sum, map_mul, app_cst h.w, Function.comp_apply]
end GlobalTheory.AbLaw.Seesaw
