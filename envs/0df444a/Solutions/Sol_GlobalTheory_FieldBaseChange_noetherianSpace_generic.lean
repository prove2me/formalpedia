-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.noetherianSpace_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:56:57.195376+00:00
-- url     : https://prove2.me/submissions/0946a143-3e3f-4fd6-86a8-2cfe4a766950

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsFinsetRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
include U
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution : NoetherianSpace (pullback G.hom (jK R) : Scheme) := by
  have := A.isAb.proper
  have : IsIso U.gen.hom.left := ⟨⟨U.gen.inv.left, by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]⟩⟩
  have : IsProper (pullback.snd G.hom (jK R)) := by
    have e : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK R) := Over.w U.gen.hom
    rw [← e]; infer_instance
  have : IsLocallyNoetherian (pullback G.hom (jK R) : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd G.hom (jK R))
  have : CompactSpace (pullback G.hom (jK R) : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd G.hom (jK R))
  have : IsNoetherian (pullback G.hom (jK R) : Scheme) := {}
  infer_instance
end GlobalTheory.FieldBaseChange
