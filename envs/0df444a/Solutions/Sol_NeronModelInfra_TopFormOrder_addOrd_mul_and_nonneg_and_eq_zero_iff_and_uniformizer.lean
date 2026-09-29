-- Prove2me | solution 1 for NeronModelInfra.TopFormOrder.addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1f2b173a-99b5-5c4b-b63e-05184b677203

import Mathlib
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

namespace OCA
open NeronModelInfra.TopFormOrder IsDedekindDomain

variable (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L]

lemma addOrd_of_ne_zero {a : L} (ha : a ≠ 0) :
    addOrd O L a = -(Multiplicative.toAdd (WithZero.unzero
      (((maximalSpectrum O).valuation L).ne_zero_iff.mpr ha))) := by
  unfold addOrd; rw [dif_neg ha]

lemma addOrd_mul {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    addOrd O L (a * b) = addOrd O L a + addOrd O L b := by
  rw [addOrd_of_ne_zero O L ha, addOrd_of_ne_zero O L hb, addOrd_of_ne_zero O L (mul_ne_zero ha hb),
    ← neg_add, ← toAdd_mul]
  congr 2
  apply WithZero.coe_injective
  rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero, map_mul]

lemma unzero_le_one {x : O} (hx : x ≠ 0) :
    WithZero.unzero (((maximalSpectrum O).valuation L).ne_zero_iff.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hx)) ≤ 1 := by
  rw [← WithZero.coe_le_coe, WithZero.coe_unzero, WithZero.coe_one,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (maximalSpectrum O).intValuation_le_one x

lemma addOrd_algebraMap_nonneg (x : O) : 0 ≤ addOrd O L (algebraMap O L x) := by
  by_cases hx : x = 0
  · subst hx; unfold addOrd; simp
  have hne : algebraMap O L x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hx
  rw [addOrd_of_ne_zero O L hne, neg_nonneg]
  have h := unzero_le_one O L hx
  rw [← Multiplicative.toAdd_le, toAdd_one] at h
  exact h

lemma addOrd_algebraMap_eq_zero_iff {x : O} (hx : x ≠ 0) :
    addOrd O L (algebraMap O L x) = 0 ↔ IsUnit x := by
  have hne : algebraMap O L x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O L)).mpr hx
  rw [addOrd_of_ne_zero O L hne, neg_eq_zero]
  constructor
  · intro h
    have h1 : (maximalSpectrum O).valuation L (algebraMap O L x) = 1 := by
      rw [← WithZero.coe_unzero (((maximalSpectrum O).valuation L).ne_zero_iff.mpr hne), ← WithZero.coe_one,
        Multiplicative.toAdd.injective (h.trans toAdd_one.symm)]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff] at h1
    by_contra hu
    exact h1 ((IsLocalRing.mem_maximalIdeal x).mpr hu)
  · intro hu
    have h1 : (maximalSpectrum O).intValuation x = 1 :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.mpr
        (fun hm => (IsLocalRing.mem_maximalIdeal x).mp hm hu)
    have h2 : WithZero.unzero (((maximalSpectrum O).valuation L).ne_zero_iff.mpr hne) = 1 := by
      apply WithZero.coe_injective
      rw [WithZero.coe_unzero, WithZero.coe_one, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, h1]
    rw [h2, toAdd_one]

end OCA

theorem solution
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L] :
    (∀ a b : L, a ≠ 0 → b ≠ 0 → addOrd O L (a * b) = addOrd O L a + addOrd O L b) ∧
    (∀ x : O, 0 ≤ addOrd O L (algebraMap O L x)) ∧
    (∀ x : O, x ≠ 0 → (addOrd O L (algebraMap O L x) = 0 ↔ IsUnit x)) ∧
    (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R' O]
      [IsLocalHom (algebraMap R' O)],
      Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O →
      ∀ π : R', IsLocalRing.maximalIdeal R' = Ideal.span {π} →
        addOrd O L (algebraMap O L (algebraMap R' O π)) = 1) := by
  refine ⟨fun a b ha hb => OCA.addOrd_mul O L ha hb, fun x => OCA.addOrd_algebraMap_nonneg O L x,
    fun x hx => OCA.addOrd_algebraMap_eq_zero_iff O L hx, ?_⟩
  intro R' _ _ _ _ _ hmap π hπ
  apply addOrd_uniformizer
  rw [← hmap, hπ, Ideal.map_span, Set.image_singleton]

end S_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer
end P2MW
export P2MW.S_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer (solution)
