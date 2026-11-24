-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.exists_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:18:04.699984+00:00
-- url     : https://prove2.me/submissions/4ced5eff-b316-4ef9-beb1-5cc96bb5122a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsCompletionPointClosedPointMemOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TranslationBySection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslate

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.LawDef
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' : Over (Sp K)}
variable [IsLocalRing R]
namespace GlobalTheory.SS.LawDef
theorem _root_.solution {M : Model R A} {W Y : Over (Sp R)} {l : M.Y ⟶ W} {p : W ⟶ Y} {s : 𝟙_ (Over (Sp R)) ⟶ Y}
    (h : IsPullback l (toUnit _) p s) (z : W.left) (hz : p.left z = sp0 s) : ∃ u ∈ M.sp, l.left u = z := by
  obtain ⟨u, h1, h2⟩ := Scheme.exists_preimage_of_isPullback (h.map (Over.forget _)) z (IsLocalRing.closedPoint R) hz
  refine ⟨u, ?_, h1⟩
  have e := Over.w (toUnit M.Y)
  show M.Y.hom u = _
  rw [← e, Scheme.Hom.comp_apply]
  exact h2
end GlobalTheory.SS.LawDef
