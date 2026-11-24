-- Prove2me | solution 1 for GlobalTheory.ComplexPoints.iSup_eq_top_of_complexPoints
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:50.270591+00:00
-- url     : https://prove2.me/submissions/e4a2ac95-8c8a-4e38-8166-fd1c9e2b3946

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Theorems.Thm_GlobalTheory_ComplexPoints_exists_point_mem
import Theorems.Thm_GlobalTheory_ComplexPoints_top_le_preimage_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
namespace GlobalTheory.ComplexPoints
section General
variable {K : Type u} [Field K] [IsAlgClosed K]
end General
variable {X Y : Scheme.{0}}
set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj in
variable {X Y : Scheme.{0}} in
private theorem opens_le_of_forall_complex_section (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    (U V : X.Opens)
    (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  intro y hyU
  by_contra hyV
  obtain ⟨x, hx1, hx2⟩ := _root_.GlobalTheory.ComplexPoints.exists_point_mem (K := ℂ) p
    (Z := (U : Set X) ∩ (V : Set X)ᶜ)
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hyU, hyV⟩
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
  have hU : ⊤ ≤ x ⁻¹ᵁ U := (_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x U a).mpr (hx2 a).1
  exact (hx2 a).2 ((_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x V a).mp (h x hx1 hU))
end GlobalTheory.ComplexPoints
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
universe u
open GlobalTheory GlobalTheory.ComplexPoints
variable {X Y : Scheme.{0}}
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
variable {X Y : Scheme.{0}}
namespace GlobalTheory.ComplexPoints
namespace _root_.GlobalTheory.ComplexPoints
theorem _root_.solution (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) [LocallyOfFiniteType p]
    {I : Type*} (U : I → X.Opens) (h : ∀ x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X, x ≫ p = 𝟙 _ → ∃ i, ⊤ ≤ x ⁻¹ᵁ U i) :
    ⨆ i, U i = ⊤ := by
  refine eq_top_iff.mpr (opens_le_of_forall_complex_section p ⊤ _ fun x hx _ => ?_)
  obtain ⟨i, hi⟩ := h x hx
  obtain ⟨a⟩ := (inferInstance : Nonempty (Spec (.of ℂ)))
  rw [_root_.GlobalTheory.ComplexPoints.top_le_preimage_iff x _ a] at hi ⊢
  exact (le_iSup U i) hi
end _root_.GlobalTheory.ComplexPoints
end GlobalTheory.ComplexPoints
