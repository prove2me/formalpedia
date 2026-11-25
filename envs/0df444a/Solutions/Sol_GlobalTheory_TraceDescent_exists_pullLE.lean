-- Prove2me | solution 1 for GlobalTheory.TraceDescent.exists_pullLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:59:20.692849+00:00
-- url     : https://prove2.me/submissions/17e7120f-e85b-471c-8061-ae0737774f24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
import Theorems.Thm_GlobalTheory_TraceDescent_coord_pullLE
import Theorems.Thm_GlobalTheory_TraceDescent_exists_fun
import Theorems.Thm_GlobalTheory_TraceDescent_pb_injective
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_pb_rs
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_rs_pb
import Theorems.Thm_GlobalTheory_AbLaw_PowVanish_rs_pull_g
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_coord_pullLE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish
variable {X Y : Scheme.{0}} (f : Y ⟶ X) (M : LB X)
variable {G : Type} (τ : G → (Y ⟶ Y)) (hτ : ∀ y, τ y ≫ f = f)
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
include hτ hgal
namespace GlobalTheory.TraceDescent
theorem _root_.solution (V : X.Opens) (W : Y.Opens) (e : W ≤ f ⁻¹ᵁ V) (e' : f ⁻¹ᵁ V ≤ W)
    (s : SecOn (M.pull f) W) (hs : ∀ y (e : W ≤ τ y ⁻¹ᵁ W), act f M (hτ y) e s = s) :
    ∃ x, SecOn.pullLE M f V W e x = s := by
  have inv : ∀ y, W ≤ τ y ⁻¹ᵁ W := fun y => by
    obtain rfl := le_antisymm e e'
    rw [← Scheme.Hom.comp_preimage, hτ]
  have H : ∀ i : M.ι, ∃ g : Γ(X, V ⊓ M.U i),
      pb f ((inf_le_inf_right _ e).trans (GlobalTheory.LB.pull_inf_le f V (fun _ => i))) g =
        GlobalTheory.LB.coord s (fun _ => i) := fun i =>
    (exists_fun f τ hgal (V ⊓ M.U i) (W ⊓ (M.pull f).U (fun _ => i)) _
      (fun y hy => ⟨e' hy.1, mem_pull.2 hy.2⟩) _ fun y _ =>
      congrArg (GlobalTheory.LB.coord · (fun _ => i : (M.pull f).ι)) (hs y (inv y))).exists
  choose g hg using H
  refine ⟨GlobalTheory.LB.mkSec g fun i j => ?_, GlobalTheory.LB.sec_ext fun j => (coord_pullLE f M e _ j).trans (hg _)⟩
  have e₀ : W ⊓ (M.pull f).U (fun _ => i) ⊓ (M.pull f).U (fun _ => j) ≤ f ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
    fun y hy => ⟨⟨e hy.1.1, mem_pull.1 hy.1.2⟩, mem_pull.1 hy.2⟩
  apply pb_injective f τ hτ hgal (V ⊓ M.U i ⊓ M.U j) _ e₀
    (fun y hy => ⟨⟨e' hy.1.1, mem_pull.2 hy.1.2⟩, mem_pull.2 hy.2⟩)
  have h := GlobalTheory.LB.coord_mem s (fun _ => i) (fun _ => j)
  rw [← hg, ← hg] at h
  exact (pb_rs f e₀ _ _).trans ((rs_pb f _ _ _).symm.trans (h.trans ((congrArg₂ (· * ·)
    ((rs_pull_g M f i j _).trans (pb_rs f e₀ _ _).symm)
    ((rs_pb f _ _ _).trans (pb_rs f e₀ _ _).symm)).trans (map_mul _ _ _).symm)))
end GlobalTheory.TraceDescent
