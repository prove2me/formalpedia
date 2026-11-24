-- Prove2me | solution 1 for GlobalTheory.SaturatedSections.existsUnique_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:13.652355+00:00
-- url     : https://prove2.me/submissions/0338f6ee-4595-47e8-b06d-2f1ef0130d88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueCombOfIndependentSpecialFibre
import Theorems.Thm_GlobalTheory_SaturatedSections_exists_comb

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
open GlobalTheory GlobalTheory.SaturatedSections
namespace GlobalTheory.SaturatedSections
theorem _root_.solution {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    {J : Type} {A : J → Type} [∀ j, CommRing (A j)] (φ : ∀ j, W →+* A j) {ϖ : W}
    (hϖ : Irreducible ϖ) (reg : ∀ j (x : A j), φ j ϖ * x = 0 → x = 0)
    {r : ℕ} (s : Fin r → ∀ j, A j)
    (ind : ∀ (c : Fin r → W) (y : ∀ j, A j), (∀ j, φ j ϖ * y j = ∑ i, φ j (c i) * s i j) →
      ∀ i, c i ∈ IsLocalRing.maximalIdeal W) (t : ∀ j, A j) (a : W) (c : Fin r → W) (ha : a ≠ 0)
    (h : ∀ j, φ j a * t j = ∑ i, φ j (c i) * s i j) :
    ∃! d : Fin r → W, ∀ j, t j = ∑ i, φ j (d i) * s i j := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  obtain ⟨d, -, hd⟩ := exists_comb φ hϖ reg s ind n t (fun i => (u⁻¹ : Wˣ) * c i) (fun j => by
    simp only [map_mul, _root_.mul_assoc, ← Finset.mul_sum, ← h j]
    rw [← _root_.mul_assoc (φ j (u⁻¹ : Wˣ)), ← map_mul, Units.inv_mul, map_one,
      _root_.one_mul])
  refine ⟨d, hd, fun d' hd' => ?_⟩
  funext i
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  obtain ⟨e, he, -⟩ := exists_comb φ hϖ reg s ind (m + 1) (fun _ => 0) (fun i => d' i - d i)
    (fun j => by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, ← hd j, ← hd' j, sub_self,
        MulZeroClass.mul_zero])
  have h1 : ϖ ^ m * (v : W) = ϖ ^ m * (ϖ * e i) := by
    have := he i
    rw [hv] at this
    linear_combination this
  have h2 := mul_left_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ v.isUnit))
end GlobalTheory.SaturatedSections
