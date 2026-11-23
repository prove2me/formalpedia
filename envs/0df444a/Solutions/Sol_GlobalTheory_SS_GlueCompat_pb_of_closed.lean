-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.pb_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:23.367989+00:00
-- url     : https://prove2.me/submissions/f756991c-86a8-4af2-ba7a-723ba84a3d52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
import Theorems.Thm_GlobalTheory_SS_GlueCompat_schDom_open

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.GlueCompat
set_option backward.isDefEq.respectTransparency false
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}
variable [IsDomain R] [IsFractionRing R K]
namespace GlobalTheory.SS.GlueCompat
theorem _root_.solution (N : Model R A) {X G M W : Over (Sp R)} (p : X ⟶ N.Y) [IsOpenImmersion p.left] (q : X ⟶ G)
    (g : M ⟶ G) [IsOpenImmersion g.left] (a : W ⟶ X) (b : W ⟶ M) (w : a.left ≫ q.left = b.left ≫ g.left)
    (hc : IsClosedImmersion (lift (a ≫ p) b).left) (j : A.left ⟶ W.left) (hj : j ≫ a.left ≫ p.left = N.j) :
    IsPullback a.left b.left q.left g.left := by
  let l : W.left ⟶ pullback q.left g.left := pullback.lift a.left b.left w
  let m : pullback q.left g.left ⟶ pullback N.Y.hom M.hom :=
    pullback.lift (pullback.fst _ _ ≫ p.left) (pullback.snd _ _) (by
      rw [Category.assoc, Over.w p, ← Over.w q, ← Over.w g, pullback.condition_assoc])
  have e : l ≫ m = (lift (a ≫ p) b).left := by
    apply pullback.hom_ext <;> simp [l, m]
  have : IsSeparated (m ≫ pullback.fst _ _) := by
    simp only [m, pullback.lift_fst]; infer_instance
  have : IsSeparated m := IsSeparated.of_comp m (pullback.fst _ _)
  have : IsClosedImmersion (l ≫ m) := e ▸ hc
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l m
  have : IsSchemeTheoreticallyDominant (j ≫ l) :=
    schDom_open N (pullback.fst q.left g.left ≫ p.left) (by simp [l, ← hj])
  have : IsIso l := IsClosedImmersion.isIso_iff_ker_eq_bot.2
    (le_bot_iff.1 ((Scheme.Hom.le_ker_comp j l).trans (j ≫ l).ker_eq_bot.le))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso l) (by simp [l]) (by simp [l])
end GlobalTheory.SS.GlueCompat
