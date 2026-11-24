-- Prove2me | solution 1 for GlobalTheory.TorusConst.exists_extension_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:34:06.747645+00:00
-- url     : https://prove2.me/submissions/8e10f4b4-2c32-407b-8f92-2cb7a19b013e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Theorems.Thm_GlobalTheory_TorusConst_exists_extension
import Theorems.Thm_GlobalTheory_TorusConst_valuationRing_stalk
import Theorems.Thm_GlobalTheory_TorusConst_Glue_symm

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
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
open LaurentPolynomial
variable {L : Type} [Field L] [Algebra K L]
namespace GlobalTheory.TorusConst
theorem _root_.solution [IsProper B.hom] (u : sp K L[T;T⁻¹] ⟶ B) :
    ∃ b : sp K L[X] ⟶ B, spm (inc K L) ≫ b = u := by
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap L[X] L[T;T⁻¹]))) :=
    IsOpenImmersion.of_isLocalization (X : L[X])
  have h2 : B.left.IsSeparated := ⟨by
    rw [← terminal.comp_from B.hom]
    infer_instance⟩
  obtain ⟨g, hg, hg'⟩ := exists_extension (valuationRing_stalk L[X])
    (Spec.map (CommRingCat.ofHom (algebraMap L[X] L[T;T⁻¹]))) (sp K L[X]).hom B.hom u.left
    ((Over.w u).trans (Over.w (spm (inc K L))).symm)
  exact ⟨Over.homMk g hg', by ext1; exact hg⟩
end GlobalTheory.TorusConst
