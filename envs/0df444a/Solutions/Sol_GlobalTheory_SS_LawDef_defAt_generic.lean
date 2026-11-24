-- Prove2me | solution 1 for GlobalTheory.SS.LawDef.defAt_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:24:36.865264+00:00
-- url     : https://prove2.me/submissions/1a9788e6-b404-4340-9a5e-00a73d19503a

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
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_mk
import Theorems.Thm_GlobalTheory_SS_Model_j_hom
import Theorems.Thm_GlobalTheory_isOpenImmersion_spMap_of_isDiscreteValuationRing


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
namespace GlobalTheory.SS.LawDef
theorem _root_.solution [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]
    (M : Model R A) (N : Model R A') (f : A ⟶ A') (y : M.Y.left) (hy : y ∉ M.sp) : DefAt M N f y := by
  have := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : IsOpenImmersion M.j := by unfold Model.j; infer_instance
  obtain ⟨x, rfl⟩ : y ∈ Set.range M.j := by
    have h1 : y ∈ Set.range (pullback.fst M.Y.hom (spMap (algebraMap R K))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨(⊥ : PrimeSpectrum K), ?_⟩
      have hp : PrimeSpectrum.asIdeal (R := R) (M.Y.hom y) = ⊥ := by
        by_contra h
        exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((M.Y.hom y).isPrime.isMaximal h)))
      apply PrimeSpectrum.ext
      rw [hp]
      exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
    obtain ⟨w, rfl⟩ := h1
    obtain ⟨x, rfl⟩ := M.e.inv.left.surjective w
    exact ⟨x, rfl⟩
  refine defAt_mk M N f M.j (f.left ≫ N.j) ?_ ?_ x
  · rw [Category.assoc, N.j_hom, M.j_hom, Over.w_assoc]
  · intro T t u e
    rw [(cancel_mono _).1 e]
end GlobalTheory.SS.LawDef
