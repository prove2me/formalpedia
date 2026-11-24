-- Prove2me | solution 1 for GlobalTheory.SS.StrictLaw.exists_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:23:15.532997+00:00
-- url     : https://prove2.me/submissions/ce6a84e6-645f-48d6-ab0d-035c480ec270

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeronStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_EqOnPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStrictModelOfBirational
import Theorems.Thm_GlobalTheory_SS_StrictLaw_isPullback_j

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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.StrictLaw
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.StrictLaw
theorem _root_.solution [IsNoetherianRing R] (M : Model R A) (V : M.Y.left.Opens)
    (hV : Set.range M.j ⊆ V) :
    ∃ (N : Model R A) (g : N.Y ⟶ M.Y), IsOpenImmersion g.left ∧ N.j ≫ g.left = M.j ∧
      Set.range g.left = V := by
  have := M.smooth
  have := M.sep
  have := M.qc
  have : IsLocallyNoetherian M.Y.left := LocallyOfFiniteType.isLocallyNoetherian M.Y.hom
  let j' : A.left ⟶ V.toScheme := IsOpenImmersion.lift V.ι M.j (by simpa using hV)
  have hj : j' ≫ V.ι = M.j := IsOpenImmersion.lift_fac _ _ _
  have h1 : IsPullback j' (𝟙 _) V.ι M.j := IsPullback.of_vert_isIso_mono ⟨by simp [hj]⟩
  have h2 := (h1.flip.paste_horiz (isPullback_j M).flip).flip
  rw [Category.id_comp] at h2
  refine ⟨⟨Over.mk (V.ι ≫ M.Y.hom), (Over.isoMk h2.isoPullback h2.isoPullback_hom_snd).symm,
    inferInstanceAs (Smooth (V.ι ≫ M.Y.hom)), inferInstanceAs (IsSeparated (V.ι ≫ M.Y.hom)),
    inferInstanceAs (QuasiCompact (V.ι ≫ M.Y.hom))⟩, Over.homMk V.ι rfl,
    (inferInstance : IsOpenImmersion V.ι), ?_, Scheme.Opens.range_ι V⟩
  exact (congrArg (· ≫ V.ι) h2.isoPullback_hom_fst).trans hj
end GlobalTheory.SS.StrictLaw
