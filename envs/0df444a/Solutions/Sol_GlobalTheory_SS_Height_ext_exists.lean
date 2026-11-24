-- Prove2me | solution 1 for GlobalTheory.SS.Height.ext_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:01.446827+00:00
-- url     : https://prove2.me/submissions/317321e6-d918-4656-902f-c79b89f395db

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleHeightProperScheme

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Height
open IsLocalRing
variable {k K : Type} [Field k] [Field K] [Algebra k K]
namespace GlobalTheory.SS.Height
theorem _root_.solution (O : ValuationSubring K) (hO : ∀ c, algebraMap k K c ∈ O) (B : Over (Sp k))
    [IsProper B.hom] (x : Over.mk (spMap (algebraMap k K)) ⟶ B) :
    ∃ b : Sp O ⟶ B.left, spMap O.subtype ≫ b = x.left := by
  have hE : ValuativeCriterion.Existence B.hom :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed B.hom) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) B.hom).1
  obtain ⟨⟨l⟩⟩ := hE { R := O, K := K, i₁ := x.left, i₂ := spMap ((algebraMap k K).codRestrict O hO), commSq := ⟨(Over.w x).trans (by rw [← Spec.map_comp]; rfl)⟩ }
  exact ⟨l.l, l.fac_left⟩
end GlobalTheory.SS.Height
