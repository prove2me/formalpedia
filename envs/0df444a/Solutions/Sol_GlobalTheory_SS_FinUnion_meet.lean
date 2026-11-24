-- Prove2me | solution 1 for GlobalTheory.SS.FinUnion.meet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:41:15.813217+00:00
-- url     : https://prove2.me/submissions/adf18c9f-b68d-4096-a2b7-0437e98bd8b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_StrictModelTranslatesTwistCompatibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGlueFinitelyManyCompatibleSmoothModelsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelGroupLawDefinedAtTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelExtensionOfDefinedAtPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnionTranslates
import Theorems.Thm_GlobalTheory_SS_FinUnion_mem_of_closed
import Theorems.Thm_GlobalTheory_SS_FinUnion_dense_res
import Theorems.Thm_GlobalTheory_SS_FinUnion_twist_j
import Theorems.Thm_GlobalTheory_SS_FinUnion_sp_inter
import Theorems.Thm_GlobalTheory_SS_GI_twist_j
import Theorems.Thm_GlobalTheory_SS_Translates_twist_j


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
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.FinUnion
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.SS.FinUnion
theorem _root_.solution [IsDomain R] [IsLocalRing R] [IsFractionRing R K] {M G : Model R A} (f : A ≅ A) (hf : GenIso M M f.hom)
    (g : (M.twist f).Y ⟶ G.Y) (hg : (M.twist f).j ≫ g.left = G.j) (g₀ : M.Y ⟶ G.Y) (hg₀ : M.j ≫ g₀.left = G.j) :
    (G.sp ∩ Set.range g.left ∩ Set.range g₀.left).Nonempty := by
  obtain ⟨x, hx, V, τ, hV, hτ, -⟩ := hf
  have := G.sep
  have : IsClosedImmersion (lift (𝟙 G.Y) (𝟙 G.Y)).left := by
    have : (lift (𝟙 G.Y) (𝟙 G.Y)).left = pullback.diagonal G.Y.hom := by
      apply pullback.hom_ext
      · change (lift (𝟙 G.Y) (𝟙 G.Y) ≫ fst _ _).left = _
        simp
      · change (lift (𝟙 G.Y) (𝟙 G.Y) ≫ snd _ _).left = _
        simp
    rw [this]; infer_instance
  let U : Over (Sp R) := Over.mk (V.ι ≫ M.Y.hom)
  let i : U ⟶ (M.twist f).Y := Over.homMk V.ι rfl
  let φ : U ⟶ M.Y := Over.homMk τ hτ.1
  obtain ⟨v, h1, h2⟩ := mem_of_closed (𝟙 G.Y) (𝟙 G.Y) (i ≫ g) (φ ≫ g₀) (M.j ∣_ V) (dense_res M V)
    ((M.j ⁻¹ᵁ V).ι ≫ f.hom.left ≫ G.j)
    (by
      change M.j ∣_ V ≫ V.ι ≫ g.left = _ ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, morphismRestrict_ι, ← hg, ← Category.assoc f.hom.left, twist_j,
        Category.assoc])
    (by
      change M.j ∣_ V ≫ τ ≫ g₀.left = _ ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, hτ.2, ← hg₀]
      simp only [Category.assoc]) ⟨x, hV⟩
  refine ⟨g.left x, ?_, τ ⟨x, hV⟩, h2.symm.trans h1⟩
  rw [sp_inter]
  exact ⟨x, hx, rfl⟩
end GlobalTheory.SS.FinUnion
