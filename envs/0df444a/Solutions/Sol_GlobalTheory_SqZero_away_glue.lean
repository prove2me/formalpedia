-- Prove2me | solution 1 for GlobalTheory.SqZero.away_glue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:20.258919+00:00
-- url     : https://prove2.me/submissions/8d3d53dd-b594-4544-8bba-d9ac00a88bf3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one')
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {X : Over (Spec (CommRingCat.of R))} {A : Type} [CommRing A] [Algebra R A]
  {κ : Type} {s : κ → A} {B : κ → Type} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
namespace GlobalTheory.SqZero
theorem _root_.solution (hs : Ideal.span (Set.range s) = ⊤) (q : ∀ i, A →ₐ[R] B i)
    (hq : ∀ i, IsAway (q i) (s i)) (y : ∀ i, sp (B i) ⟶ X)
    (h : ∀ i j (T : Type) [CommRing T] [Algebra R T] (a : B i →ₐ[R] T) (b : B j →ₐ[R] T),
      a.comp (q i) = b.comp (q j) → spMap a ≫ y i = spMap b ≫ y j) :
    ∃ z : sp A ⟶ X, ∀ i, spMap (q i) ≫ z = y i := by
  have hc : ∀ i j : κ, pullback.fst ((awayCover hs q hq).f i) ((awayCover hs q hq).f j) ≫ (y i).left =
      pullback.snd _ _ ≫ (y j).left := by
    intro i j
    letI := (q i : A →+* B i).toAlgebra
    letI := (q j : A →+* B j).toAlgebra
    haveI : IsScalarTower R A (B i) := IsScalarTower.of_algebraMap_eq fun r => ((q i).commutes r).symm
    haveI : IsScalarTower R A (B j) := IsScalarTower.of_algebraMap_eq fun r => ((q j).commutes r).symm
    have := congrArg CommaMorphism.left (h i j (TensorProduct A (B i) (B j))
      Algebra.TensorProduct.includeLeft
      (Algebra.TensorProduct.includeRight.restrictScalars R)
      (AlgHom.ext fun a => by
        change (algebraMap A (B i) a) ⊗ₜ[A] (1 : B j) = (1 : B i) ⊗ₜ[A] algebraMap A (B j) a
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]))
    change pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap A (B i))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (B j)))) ≫ _ = pullback.snd _ _ ≫ _
    rw [← pullbackSpecIso_hom_fst, ← pullbackSpecIso_hom_snd, Category.assoc, Category.assoc]
    exact congrArg _ this
  have hk : ∀ i : κ, (spMap (q i)).left ≫ (awayCover hs q hq).glueMorphisms (fun i => (y i).left) hc =
      (y i).left := fun i => (awayCover hs q hq).ι_glueMorphisms _ hc i
  refine ⟨Over.homMk ((awayCover hs q hq).glueMorphisms (fun i => (y i).left) hc) ?_,
    fun i => Over.OverMorphism.ext (hk i)⟩
  refine (awayCover hs q hq).hom_ext _ _ fun (i : κ) => ?_
  change (spMap (q i)).left ≫ _ = (spMap (q i)).left ≫ (sp A).hom
  rw [← Category.assoc, hk, Over.w, Over.w]
end GlobalTheory.SqZero
