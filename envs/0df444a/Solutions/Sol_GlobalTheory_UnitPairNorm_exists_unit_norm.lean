-- Prove2me | solution 1 for GlobalTheory.UnitPairNorm.exists_unit_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:11.883634+00:00
-- url     : https://prove2.me/submissions/c2b17c48-1127-4999-b21c-b7a120d63c5a

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
import Theorems.Thm_GlobalTheory_UnitPairNorm_h_add_right
import Theorems.Thm_GlobalTheory_UnitPairNorm_h_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
namespace GlobalTheory.UnitPairNorm
theorem _root_.solution (c : E ≃+* E) (hcc : ∀ x, c (c x) = x)
    (hcint : ∀ x : O, ∃ y : O, c (algebraMap O E x) = algebraMap O E y)
    (hz : ∃ z : O, algebraMap O E z + c (algebraMap O E z) = 1)
    (h : V → V → E)
    (hadd : ∀ x y z : V, h (x + y) z = h x z + h y z)
    (hsmul : ∀ (s : E) (x z : V), h (s • x) z = s * h x z)
    (hsym : ∀ x y : V, h y x = c (h x y))
    (L : Submodule O V) (hint : ∀ x ∈ L, ∀ y ∈ L, h x y ∈ (algebraMap O E).range)
    (x y : V) (hx : x ∈ L) (hy : y ∈ L) (a : Oˣ) (ha : h x y = algebraMap O E a) :
    ∃ e ∈ L, ∃ u : Oˣ, h e e = algebraMap O E u := by
  by_contra hcon
  push_neg at hcon
  have nu : ∀ e ∈ L, ∀ o : O, algebraMap O E o = h e e → o ∈ IsLocalRing.maximalIdeal O := by
    intro e he o ho
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hcon e he hu.unit (by rw [IsUnit.unit_spec]; exact ho.symm)
  obtain ⟨z0, hz0⟩ := hz
  obtain ⟨t, ht⟩ := hcint (z0 * ((a⁻¹ : Oˣ) : O))
  have hct : c (algebraMap O E t) = algebraMap O E (z0 * ((a⁻¹ : Oˣ) : O)) := by
    rw [← ht, hcc]
  obtain ⟨ox, hox⟩ := hint x hx x hx
  obtain ⟨oy, hoy⟩ := hint y hy y hy
  have hyx : h y x = c (algebraMap O E a) := by rw [hsym x y, ha]
  have hA : algebraMap O E (z0 * ((a⁻¹ : Oˣ) : O)) * algebraMap O E (a : O) = algebraMap O E z0 := by
    rw [← map_mul, mul_assoc, Units.inv_mul, mul_one]
  have hB : algebraMap O E t * c (algebraMap O E (a : O)) = c (algebraMap O E z0) := by
    rw [← ht, ← map_mul, hA]
  have heL : x + t • y ∈ L := L.add_mem hx (L.smul_mem t hy)
  have key : h (x + t • y) (x + t • y) =
      algebraMap O E (ox + t * (z0 * ((a⁻¹ : Oˣ) : O)) * oy + 1) := by
    have hty : t • y = algebraMap O E t • y := (algebraMap_smul E t y).symm
    rw [hty, hadd, h_add_right c h hadd hsym, h_add_right c h hadd hsym,
      h_smul_right c h hsmul hsym, h_smul_right c h hsmul hsym, hsmul, hsmul, hct, ha, hyx,
      ← hox, ← hoy, hA, hB]
    simp only [map_add, map_mul, map_one]
    linear_combination hz0
  obtain ⟨oe, hoe⟩ := hint _ heL _ heL
  have h1 : (1 : O) = oe - (ox + t * (z0 * ((a⁻¹ : Oˣ) : O)) * oy) := by
    apply IsFractionRing.injective O E
    rw [map_sub, hoe, key]
    simp only [map_add, map_one, map_mul]
    ring
  have hm : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [h1]
    refine Ideal.sub_mem _ (nu _ heL oe hoe) (Ideal.add_mem _ (nu x hx ox hox) ?_)
    exact Ideal.mul_mem_left _ _ (nu y hy oy hoy)
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal O).ne_top hm
end GlobalTheory.UnitPairNorm
