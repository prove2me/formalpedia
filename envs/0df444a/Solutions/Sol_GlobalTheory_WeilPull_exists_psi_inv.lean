-- Prove2me | solution 1 for GlobalTheory.WeilPull.exists_psi_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:00.886167+00:00
-- url     : https://prove2.me/submissions/64b0711f-978d-49ac-a7d8-7a3065fafa8e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilPull
open GlobalTheory.CommPairing
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {k : ℤ}
namespace GlobalTheory.WeilPull
theorem _root_.solution [IsIso τ] : ∃ χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left,
    (psiO hp τ hτ).left ≫ χ = 𝟙 (T ⊗ A).left ∧ χ ≫ (psiO hp τ hτ).left = 𝟙 _ := by
  have w₁ : (snd T₀ G).left ≫ G.hom = ((fst T₀ G).left ≫ inv τ ≫ T.hom) ≫ f := by
    rw [Over.w, Category.assoc, Category.assoc, ← hτ, IsIso.inv_hom_id_assoc, Over.w]
  let a : (T₀ ⊗ G).left ⟶ A.left := hp.1.lift _ _ w₁
  have a₁ : a ≫ φ = (snd T₀ G).left := hp.1.lift_fst _ _ _
  have a₂ : a ≫ A.hom = (fst T₀ G).left ≫ inv τ ≫ T.hom := hp.1.lift_snd _ _ _
  let χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left :=
    pullback.lift ((fst T₀ G).left ≫ inv τ) a (by rw [a₂, Category.assoc])
  have c₁ : χ ≫ (fst T A).left = (fst T₀ G).left ≫ inv τ := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd T A).left = a := pullback.lift_snd _ _ _
  have p₁ := psi_fst hp τ hτ
  have p₂ := psi_snd hp τ hτ
  refine ⟨χ, ?_, ?_⟩
  · refine pullback.hom_ext (f := T.hom) (g := A.hom) ?_ ?_
    · show (_ ≫ χ) ≫ (fst T A).left = 𝟙 _ ≫ (fst T A).left
      rw [Category.assoc, c₁, ← Category.assoc, p₁, Category.assoc, IsIso.hom_inv_id, Category.id_comp,
        Category.comp_id]
    · show (_ ≫ χ) ≫ (snd T A).left = 𝟙 _ ≫ (snd T A).left
      rw [Category.assoc, c₂, Category.id_comp]
      refine hp.1.hom_ext ?_ ?_
      · rw [Category.assoc, a₁, p₂]
      · rw [Category.assoc, a₂, ← Category.assoc, p₁, Category.assoc, IsIso.hom_inv_id_assoc, Over.w, Over.w]
  · refine pullback.hom_ext (f := T₀.hom) (g := G.hom) ?_ ?_
    · show (χ ≫ _) ≫ (fst T₀ G).left = 𝟙 _ ≫ (fst T₀ G).left
      rw [Category.assoc, p₁, ← Category.assoc, c₁, Category.assoc, IsIso.inv_hom_id, Category.id_comp,
        Category.comp_id]
    · show (χ ≫ _) ≫ (snd T₀ G).left = 𝟙 _ ≫ (snd T₀ G).left
      rw [Category.assoc, p₂, ← Category.assoc, c₂, a₁, Category.id_comp]
end GlobalTheory.WeilPull
