-- Prove2me | solution 1 for GlobalTheory.unimodular_symplectic_coordinates_and_lattice_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:38:58.054458+00:00
-- url     : https://prove2.me/submissions/db8e664f-764e-498b-a9c7-c4d2a8430ed9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnimodularSymplecticCoordinatesAndLatticeRank
import Theorems.Thm_GlobalTheory_hermForm_self_im_eq_zero
import Theorems.Thm_GlobalTheory_free_finite_finrank_of_discrete_span
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left
import Theorems.Thm_GlobalTheory_exists_isSymplecticBasis_of_finrank
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ), Function.Bijective EF → (∀ x, EF x x = 0) → Module.finrank ℤ La = 2 * g → ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La, ∀ a b, EF (bas a) (bas b) = omegaStd a b) ∧ ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧ ∀ x, EF x x = 0 := by
  refine ⟨fun La _ _ _ EF g hbij halt hrk => ?_,
    fun La _ EF g Q Hm ⟨hinj, hd, hsp, hH, _, hIm⟩ => ?_⟩
  · obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank (B := EF) halt hbij hrk
    have hf : IsSymplecticFamily EF (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i))
        (fun _ => 1) := hb
    classical
    refine ⟨b.equivFun.symm, fun x y => ?_⟩
    simp only [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, map_add, LinearMap.add_apply,
      map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [hf.left_left, hf.right_right, hf.left_right, hf.right_left halt, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, mul_ite, _root_.mul_one, mul_neg,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib, omegaStd]
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · obtain ⟨h1, h2, h3⟩ := free_finite_finrank_of_discrete_span Q hinj hd hsp
    exact ⟨h1, h2, h3, fun x => by
      have e : ((EF x x : ℤ) : ℝ) = 0 := by rw [← hIm x x]; exact hermForm_self_im_eq_zero hH _
      exact_mod_cast e⟩
end GlobalTheory
