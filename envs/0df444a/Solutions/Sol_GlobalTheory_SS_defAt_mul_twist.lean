-- Prove2me | solution 1 for GlobalTheory.SS.defAt_mul_twist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:38.764995+00:00
-- url     : https://prove2.me/submissions/082fdd51-83dc-4d08-9934-c20e968facfb

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
import Theorems.Thm_GlobalTheory_SS_LawDef_defAt_generic
import Theorems.Thm_GlobalTheory_SS_LawDef_exists_section
import Theorems.Thm_GlobalTheory_SS_LawDef_lawdef_section
import Theorems.Thm_GlobalTheory_SS_isoAt_id


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
open GlobalTheory.SS.LawDef
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : Model R A, Strict M → ∀ z : (M.prod M).Y.left, ∃ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso M M (transl a).hom ∧ DefAt (M.prod M) (M.twist (transl a)) (μ[A]) z := by
  intro R K _ _ _ _ _ hR A _ _ hA M hM z
  by_cases hz : z ∈ (M.prod M).sp
  · obtain ⟨Z, hZ⟩ := exists_section hR (M.prod M) (C := closure {z}) isClosed_closure.isLocallyClosed
      ⟨z, subset_closure rfl, hz⟩
    obtain ⟨a, ga, U, g, hU, h⟩ := lawdef_section hR A hA M hM (Z ≫ fst M.Y M.Y) (Z ≫ snd M.Y M.Y)
    have e : lift (Z ≫ fst M.Y M.Y) (Z ≫ snd M.Y M.Y) = Z := by
      rw [← comp_lift, lift_fst_snd]; exact Category.comp_id _
    rw [e] at hU
    exact ⟨a, ga, U, g, (specializes_iff_mem_closure.2 hZ).mem_open U.isOpen hU, h⟩
  · have := hR.1
    have := hR.2.2.2
    obtain ⟨y, hy⟩ := hM.1.1.nonempty
    have e : (transl (1 : 𝟙_ (Over (Sp K)) ⟶ A)).hom = 𝟙 A := by simp [transl]
    exact ⟨1, ⟨y, hy, e ▸ isoAt_id M y⟩, defAt_generic _ _ _ z hz⟩
end GlobalTheory.SS
