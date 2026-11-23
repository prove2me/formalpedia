-- Prove2me | solution 1 for GlobalTheory.exists_equiv_pi_range_of_matrixUnits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:09.604803+00:00
-- url     : https://prove2.me/submissions/d19f6ee4-a72a-4c69-ab7e-9a1ba7253312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UnimodularSymplecticCoordinatesAndLatticeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSiegelForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEquivPiRangeOfMatrixUnits
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
theorem _root_.solution {R M n : Type} [CommRing R] [AddCommGroup M]
    [Module R M] [Fintype n] [DecidableEq n] (p q : n → M →ₗ[R] M) (P : M →ₗ[R] M)
    (hpq : ∀ u v x, p u (q v x) = if u = v then P x else 0)
    (hs : ∀ x, ∑ u, q u (p u x) = x) (hP : ∀ x, P (P x) = P x) :
    ∃ φ : M ≃ₗ[R] (n → LinearMap.range P), (∀ x u, (φ x u : M) = p u x) ∧
      ∀ x, x = ∑ u, q u (φ x u) := by
  have hmem : ∀ u x, p u x ∈ LinearMap.range P := fun u x => by
    refine ⟨p u x, ?_⟩
    conv_rhs => rw [← hs x]
    simp [map_sum, hpq]
  let f : M →ₗ[R] (n → LinearMap.range P) :=
    LinearMap.pi fun u => (p u).codRestrict _ (hmem u)
  have hf : ∀ x u, (f x u : M) = p u x := fun _ _ => rfl
  have hb : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, fun y => ⟨∑ v, q v (y v), ?_⟩⟩
    · rw [← hs x]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [← hf, hx]; simp
    · funext u
      apply Subtype.ext
      rw [hf]
      obtain ⟨z, hz⟩ := (y u).2
      simp only [map_sum, hpq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← hz, hP]
  exact ⟨LinearEquiv.ofBijective f hb, hf, fun x => (hs x).symm⟩
end GlobalTheory
