-- Prove2me | solution 1 for GlobalTheory.LieLoc.univChart_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:13:56.233247+00:00
-- url     : https://prove2.me/submissions/5caf9b8c-9e27-40e8-8062-aac782dbe1e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SpanEqTopOfForallMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_UnivChartOfStandardSmooth
import Theorems.Thm_GlobalTheory_LieLoc_univChart_of_standardSmooth
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_IsAway_lift
import Theorems.Thm_GlobalTheory_SqZero_chart_inj
import Theorems.Thm_GlobalTheory_SqZero_exists_chart_pt_of_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_aug_surj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_elt_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_pullR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_spMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


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
open GlobalTheory GlobalTheory.LieLoc
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
namespace GlobalTheory.LieLoc
theorem _root_.solution (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (n : ℕ)
    (S : Type) [CommRing S] [Algebra R S] [Algebra.IsStandardSmoothOfRelativeDimension n R S]
    (j : sp (R₀ := R) S ⟶ G) [IsOpenImmersion j.left] (R' : Type) [CommRing R'] [Algebra R R']
    (ε : S →ₐ[R] R') (hε : spMap ε ≫ j = 1) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R') (JetR R' (Fin n) m) ⟶ (Over.pullback (fB R R')).obj G,
      IsUnivChart _ n x := by
  let inc : S →ₐ[R] R' ⊗[R] S := Algebra.TensorProduct.includeRight
  let j' : sp (R₀ := R') (R' ⊗[R] S) ⟶ (Over.pullback (fB R R')).obj G := pullR G (spMap inc ≫ j)
  have hpush : ∀ (A : Type) [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (φ : R' ⊗[R] S →ₐ[R'] A), pushR G (spMap φ ≫ j') = spMap ((φ.restrictScalars R).comp inc) ≫ j := by
    intro A _ _ _ _ φ
    rw [pushR_spMap, pushR_pullR, ← Category.assoc, spMap_comp]
  have hlift : ∀ (A : Type) [CommRing A] [Algebra R' A] [Algebra R A] [IsScalarTower R R' A]
      (φ : S →ₐ[R] A), ∃ φ' : R' ⊗[R] S →ₐ[R'] A, (φ'.restrictScalars R).comp inc = φ := by
    intro A _ _ _ _ φ
    refine ⟨Algebra.TensorProduct.lift (Algebra.ofId R' A) φ fun _ _ => Commute.all _ _, ?_⟩
    ext s
    simp [inc]
  obtain ⟨ε', hε'⟩ := hlift R' ε
  refine univChart_of_standardSmooth _ n (R' ⊗[R] S) j' ε' ?_ ?_ ?_
  · apply pushR_inj G
    rw [hpush, hε', hε, pushR_one]
  · intro A _ _ aug hJ y hy
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have _ : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hz : spMap (aug.restrictScalars R) ≫ pushR G y = spMap ε ≫ j := by
      rw [← pushR_spMap, hy, pushR_one, hε]
    obtain ⟨φ, h1, -⟩ := SqZero.exists_chart_pt_of_nil j (aug.restrictScalars R) (aug_surj aug)
      (fun a ha => elt_nil _ hJ a ha) _ _ hz
    obtain ⟨φ', h2⟩ := hlift A φ
    refine ⟨φ', pushR_inj G ?_⟩
    rw [hpush, h2, h1]
  · intro A _ _ φ φ' h
    let _ : Algebra R A := ((algebraMap R' A).comp (algebraMap R R')).toAlgebra
    have _ : IsScalarTower R R' A := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h1 := congrArg (pushR G) h
    rw [hpush, hpush] at h1
    have h2 := SqZero.chart_inj j h1
    exact Algebra.TensorProduct.ext (Subsingleton.elim _ _) h2
end GlobalTheory.LieLoc
