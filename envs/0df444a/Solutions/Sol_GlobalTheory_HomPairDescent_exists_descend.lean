-- Prove2me | solution 1 for GlobalTheory.HomPairDescent.exists_descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:58:04.33301+00:00
-- url     : https://prove2.me/submissions/8f5ddd2e-1a02-4d46-8855-136d35580225

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomPairDescendsToFinite
import Theorems.Thm_GlobalTheory_FunDescent_hom_ext
import Theorems.Thm_GlobalTheory_Spread_exists_fg_comp_eq


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
open GlobalTheory GlobalTheory.HomPairDescent
open GlobalTheory.Spread
namespace GlobalTheory.HomPairDescent
theorem _root_.solution {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A B : Over (Sp K))
    [QuasiCompact A.hom] [QuasiSeparated A.hom] [LocallyOfFinitePresentation B.hom]
    (f : (Over.pullback (spMap (algebraMap K Ω))).obj A ⟶ (Over.pullback (spMap (algebraMap K Ω))).obj B) :
    ∃ s : Finset Ω, ∀ L : IntermediateField K Ω, (s : Set Ω) ⊆ L →
      ∃ g : (Over.pullback (spMap (algebraMap K L))).obj A ⟶ (Over.pullback (spMap (algebraMap K L))).obj B,
        bcMap A.hom L.val ≫ g.left = f.left ≫ bcMap B.hom L.val := by
  have hfw : f.left ≫ pullback.snd _ _ = pullback.snd _ _ := Over.w f
  obtain ⟨R, ψ, ⟨s, rfl⟩, hψ, hψf⟩ := exists_fg_comp_eq A.hom B.hom (f.left ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ _) hfw)
  refine ⟨s, fun L hL => ?_⟩
  have hle : Algebra.adjoin K (s : Set Ω) ≤ L.toSubalgebra := Algebra.adjoin_le hL
  let ρ : Algebra.adjoin K (s : Set Ω) →ₐ[K] L := Subalgebra.inclusion hle
  have hw : (bcMap A.hom ρ ≫ ψ) ≫ B.hom = pullback.snd _ _ ≫ spMap (algebraMap K L) := by
    rw [Category.assoc, hψ, bcMap_fst_assoc, pullback.condition]
  let g₀ : pullback A.hom (spMap (algebraMap K L)) ⟶ pullback B.hom (spMap (algebraMap K L)) :=
    pullback.lift (bcMap A.hom ρ ≫ ψ) (pullback.snd _ _) hw
  let f₀ : pullback A.hom (spMap (algebraMap K Ω)) ⟶ pullback B.hom (spMap (algebraMap K Ω)) := f.left
  have hf₀ : f₀ ≫ pullback.snd _ _ = pullback.snd _ _ := hfw
  have hψ₀ : bcMap A.hom (Algebra.adjoin K (s : Set Ω)).val ≫ ψ = f₀ ≫ pullback.fst _ _ := hψf
  refine ⟨Over.homMk g₀ (pullback.lift_snd _ _ _), ?_⟩
  change bcMap A.hom L.val ≫ g₀ = f₀ ≫ bcMap B.hom L.val
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, pullback.lift_fst,
      bcMap_comp_of_eq_assoc A.hom ρ L.val (Algebra.adjoin K (s : Set Ω)).val fun _ ↦ rfl, hψ₀]
  · rw [Category.assoc, Category.assoc, bcMap_snd, pullback.lift_snd, bcMap_snd, reassoc_of% hf₀]
end GlobalTheory.HomPairDescent
