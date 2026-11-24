-- Prove2me | solution 1 for GlobalTheory.AbLaw.Seesaw.app_cst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:01.86341+00:00
-- url     : https://prove2.me/submissions/e45671eb-854a-4f17-9cd3-300b24c178c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector

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
namespace GlobalTheory.AbLaw.Seesaw
theorem _root_.solution {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (W : X.Opens) (r : R) :
    (π.app W).hom (cst f W r) = cst f' (π ⁻¹ᵁ W) (g r) := by
  have e₁ := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  have e₂ := congrArg (fun q => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) w
  have e₃ := congrArg (fun q => q.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
    (π.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₁ e₂ e₃
  refine e₃.trans ?_
  change rs X' le_top (π.appTop.hom _) = rs X' le_top (f'.appTop.hom _)
  rw [e₂, ← e₁]
end GlobalTheory.AbLaw.Seesaw
