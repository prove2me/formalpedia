-- Prove2me | solution 1 for GlobalTheory.SS.ArcInf.algOverHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:04.105216+00:00
-- url     : https://prove2.me/submissions/461f7295-1ced-4d01-9465-9ca8cd26692f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AlgOverHomSurjective

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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.ArcInf
variable {k : Type} [CommRing k] {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]
namespace GlobalTheory.SS.ArcInf
theorem _root_.solution : Function.Surjective (algOverHom : (A →ₐ[k] B) → _) := by
  intro φ
  obtain ⟨g, hg⟩ := Spec.map_surjective φ.left
  have hw : φ.left ≫ spMap (algebraMap k A) = spMap (algebraMap k B) := Over.w φ
  rw [← hg, ← Spec.map_comp] at hw
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
  refine ⟨⟨g.hom, fun c => congrArg (fun f : k →+* B => f c) h2⟩, ?_⟩
  ext1
  exact hg
end GlobalTheory.SS.ArcInf
