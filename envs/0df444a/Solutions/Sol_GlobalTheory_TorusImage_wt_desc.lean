-- Prove2me | solution 1 for GlobalTheory.TorusImage.wt_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:04.765944+00:00
-- url     : https://prove2.me/submissions/a731a2e4-11cc-439d-a534-4a2e9080d779

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
import Theorems.Thm_GlobalTheory_TorusImage_appTop_appLE
import Theorems.Thm_GlobalTheory_Diag_diagMap_chi
import Theorems.Thm_GlobalTheory_Diag_flat_diagMap
import Theorems.Thm_GlobalTheory_Diag_surjective_diagMap
import Theorems.Thm_GlobalTheory_FunDescent_appTop_injective


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
open GlobalTheory GlobalTheory.TorusImage
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
namespace GlobalTheory.TorusImage
theorem _root_.solution {X' : Type} [AddCommGroup X'] (φ : X' →+ X) (hφ : Function.Injective φ) (i' : splitTorus S X' ⟶ G)
    (e : Diag.diagMap S φ ≫ i' = i) {U : G.left.Opens} {u : Γ(G.left, U)} {χ : X'} (h : Wt i U u (φ χ)) :
    Wt i' U u χ := by
  intro Z t g h₁ h₂
  have := Diag.flat_diagMap S hφ
  have := Diag.surjective_diagMap S hφ
  let Z' : Over S := Over.mk (pullback.fst t.left (Diag.diagMap S φ).left ≫ Z.hom)
  let π : Z' ⟶ Z := Over.homMk (pullback.fst t.left (Diag.diagMap S φ).left) rfl
  let t' : Z' ⟶ splitTorus S X := Over.homMk (pullback.snd t.left (Diag.diagMap S φ).left) (by
    show _ = pullback.fst _ _ ≫ _
    rw [← Over.w (Diag.diagMap S φ), ← Category.assoc, ← pullback.condition, Category.assoc, Over.w])
  have hc : π ≫ t = t' ≫ Diag.diagMap S φ := Over.OverMorphism.ext pullback.condition
  have : Epi π.left := Flat.epi_of_flat_of_surjective (pullback.fst t.left (Diag.diagMap S φ).left)
  apply FunDescent.appTop_injective π.left
  have e1 : π.left ≫ ((t ≫ i') * g).left = ((t' ≫ i) * (π ≫ g)).left := by
    rw [← Over.comp_left, MonObj.comp_mul, ← Category.assoc, hc, Category.assoc, e]
  have k1 : ⊤ ≤ ((t' ≫ i) * (π ≫ g)).left ⁻¹ᵁ U := by
    rw [← e1]; exact fun x _ => h₁ (trivial : π.left x ∈ (⊤ : Z.left.Opens))
  have k2 : ⊤ ≤ (π ≫ g).left ⁻¹ᵁ U := fun x _ => h₂ (trivial : π.left x ∈ (⊤ : Z.left.Opens))
  rw [map_mul, appTop_appLE _ _ _ e1 h₁ k1, appTop_appLE _ _ (π ≫ g).left rfl h₂ k2, h Z' t' (π ≫ g) k1 k2,
    appTop_charUnit, appTop_charUnit, ← SplitTorus.val_comp, hc, SplitTorus.val_comp t', SplitTorus.val_eq (Diag.diagMap S φ),
    Diag.diagMap_chi, SplitTorus.val_eq]
end GlobalTheory.TorusImage
