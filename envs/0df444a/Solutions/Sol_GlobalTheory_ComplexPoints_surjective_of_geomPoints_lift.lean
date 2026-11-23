-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.surjective_of_geomPoints_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:18.265452+00:00
-- url     : https://prove2.me/submissions/cd252ab2-ceea-42fb-b3ea-179926361280

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_exists_point_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {K : Type u} [Field K] [IsAlgClosed K]
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {K : Type u} [Field K] [IsAlgClosed K]
namespace GlobalTheory.ComplexPoints
namespace _root_.GlobalTheory.ComplexPoints
theorem _root_.solution {A B S : Scheme.{u}} (p : A ⟶ S)
    [LocallyOfFiniteType p]
    (t : Spec (.of K) ⟶ S) [Surjective t] (ψ : B ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Spec (.of K) ⟶ A, x ≫ p = t → ∃ y : Spec (.of K) ⟶ B, y ≫ ψ = x) :
    Surjective ψ := by
  constructor
  by_contra hns
  have hne : (Set.range ψ)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro hr
    exact hns (Set.range_eq_univ.mp hr)
  have hP : (pullback.fst p t ⁻¹' (Set.range ψ)ᶜ).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨z, hz⟩ := (pullback.fst p t).surjective a
    exact ⟨z, by simpa [hz] using ha⟩
  obtain ⟨y, hy1, hy2⟩ := _root_.GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd p t)
    (hψ.isOpen_compl.preimage (pullback.fst p t).continuous).isLocallyClosed hP
  obtain ⟨w, hw⟩ := h (y ≫ pullback.fst p t) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy1, Category.id_comp])
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of K)))
  apply hy2 a
  exact ⟨w a, by rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]⟩
end _root_.GlobalTheory.ComplexPoints
end GlobalTheory.ComplexPoints
