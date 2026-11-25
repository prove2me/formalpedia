-- Prove2me | solution 1 for GlobalTheory.Published.SemiAbelianHomExtension.act_comp_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:14:30.723225+00:00
-- url     : https://prove2.me/submissions/a4f62365-4ee5-4145-86aa-2286b40b9b94

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_SemiabelianTori_GeometricallyConnectedSplitTorusAff
import Theorems.Thm_GlobalTheory_ExtUnique_over_hom_ext_of_isPullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SemiAbelianHomExtension
open ExtUnique
variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]
omit [AlgebraicGeometry.IsNoetherian S]
namespace GlobalTheory.Published.SemiAbelianHomExtension
theorem _root_.solution {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {G H : Over S} [GrpObj G] [GrpObj H] [Flat G.hom] [IsSeparated H.hom] {G' H' : Over U} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsPullback φ G'.hom G.hom j)
    {O : Type} [CommRing O] (a : OAct O G) (b : OAct O H) (a' : OAct O G') (b' : OAct O H')
    (ha : ∀ x, (a'.act x).left ≫ φ = φ ≫ (a.act x).left) (hb : ∀ x, (b'.act x).left ≫ ψ = ψ ≫ (b.act x).left)
    (f : G' ⟶ H') (hf : ∀ x, a'.act x ≫ f = f ≫ b'.act x) (F : G ⟶ H) (hF : f.left ≫ ψ = φ ≫ F.left) (x : O) :
    a.act x ≫ F = F ≫ b.act x := by
  refine over_hom_ext_of_isPullback hφ ?_
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← ha, Category.assoc, ← hF, ← Category.assoc,
    ← Over.comp_left, hf, Over.comp_left, Category.assoc, hb, ← Category.assoc, hF, Category.assoc]
end GlobalTheory.Published.SemiAbelianHomExtension
