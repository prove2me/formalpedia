-- Prove2me | solution 1 for GlobalTheory.SS.GlueCompat.schDom_open
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:57.537802+00:00
-- url     : https://prove2.me/submissions/321b9a85-134b-47ee-8a86-6c51ce8c3a2d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModels
import Theorems.Thm_GlobalTheory_SS_GlueCompat_pb_mono
import Theorems.Thm_GlobalTheory_SS_GlueCompat_j_isPullback

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
theorem _root_.solution (M : Model R A) {X : Scheme.{0}} (i : X ⟶ M.Y.left) [IsOpenImmersion i] {a : A.left ⟶ X}
    (h : a ≫ i = M.j) : IsSchemeTheoreticallyDominant a := by
  have := M.smooth
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) := by
    have : IsDominant (spMap (algebraMap R K)) :=
      ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
        exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
    exact IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsSchemeTheoreticallyDominant M.j := IsSchemeTheoreticallyDominant.of_isPullback (j_isPullback M).flip
  have : QuasiCompact M.j := MorphismProperty.of_isPullback (P := @QuasiCompact) (j_isPullback M).flip inferInstance
  exact IsSchemeTheoreticallyDominant.of_isPullback (pb_mono h).flip
end GlobalTheory.SS.GlueCompat
