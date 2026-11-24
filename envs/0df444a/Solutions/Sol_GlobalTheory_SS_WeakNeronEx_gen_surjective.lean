-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.gen_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:21:58.28213+00:00
-- url     : https://prove2.me/submissions/7a77723a-867d-4523-8ea1-e61e21e60b50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out
variable (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {D : Type} [CommRing D] [Algebra K D] [Algebra R D] [IsScalarTower R K D]
omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace GlobalTheory.SS.WeakNeronEx
theorem _root_.solution {I : Type} (r : I → D)
    (h : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K D) r)) :
    Function.Surjective (gen R K (Algebra.adjoin R (Set.range r))) := by
  intro d
  obtain ⟨p, rfl⟩ := h d
  refine ⟨MvPolynomial.aeval (fun i => (1 : K) ⊗ₜ (⟨r i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ :
    Algebra.adjoin R (Set.range r))) p, ?_⟩
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp [gen, MvPolynomial.aeval_def]
end GlobalTheory.SS.WeakNeronEx
