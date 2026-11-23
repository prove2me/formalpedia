-- Prove2me | solution 1 for GlobalTheory.AdLat.hilbert90_involution_of_idempotent_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:59.531054+00:00
-- url     : https://prove2.me/submissions/07b04ea1-4e9b-49ed-b88a-ef6400bba195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIdempotentIsUnitOneAddOrSubAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Hilbert90AdeleRingTensorQuadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
namespace GlobalTheory.AdLat
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x)
    (u d e s : R) (hu : u * σ u = 1) (hd : σ d = -d) (hdu : IsUnit d) (h2 : IsUnit (2 : R))
    (he : e * e = e) (hσe : σ e = e) (hs : u + σ u = 2 * s)
    (hun : IsUnit (e * (1 + s) + (1 - e) * (1 - s))) :
    ∃ x : Rˣ, (x : R) = u * σ x := by
  obtain ⟨d', hd'⟩ := hdu.exists_right_inv
  have h3 : IsUnit (e - (1 - e) * d ^ 2) := by
    refine IsUnit.of_mul_eq_one (e - (1 - e) * d' ^ 2) ?_
    have h : d ^ 2 * d' ^ 2 = 1 := by rw [← mul_pow, hd', one_pow]
    linear_combination (1 + d ^ 2 + d' ^ 2 + d ^ 2 * d' ^ 2) * he + (1 - e) * h
  have hx : σ (e * (1 + u) + (1 - e) * d * (1 - u)) = e * (1 + σ u) - (1 - e) * d * (1 - σ u) := by
    simp only [map_add, map_mul, map_sub, map_one, hσe, hd]; ring
  have hN : (e * (1 + u) + (1 - e) * d * (1 - u)) * (e * (1 + σ u) - (1 - e) * d * (1 - σ u)) =
      2 * (e * (1 + s) + (1 - e) * (1 - s)) * (e - (1 - e) * d ^ 2) := by
    have hv : σ u = 2 * s - u := by linear_combination hs
    rw [hv] at hu ⊢
    have h1 : e * (1 - e) = 0 := by linear_combination - he
    have h4 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
    generalize 1 - e = f at h1 h4 ⊢
    linear_combination (e * e - f * f * d ^ 2) * hu +
      (d * ((1 - u) * (1 + (2 * s - u)) - (1 + u) * (1 - (2 * s - u))) + 2 * (1 + s) * d ^ 2 - 2 * (1 - s)) * h1
  have hxu : IsUnit (e * (1 + u) + (1 - e) * d * (1 - u)) :=
    isUnit_of_mul_isUnit_left (hN ▸ (h2.mul hun).mul h3)
  refine ⟨hxu.unit, ?_⟩
  rw [IsUnit.unit_spec, hx]
  linear_combination (- e - (1 - e) * d) * hu
end GlobalTheory.AdLat
