-- Prove2me | solution 1 for ModularCurve.qExpand_mem_and_mem_nonunits_of_forall_mem_iff_exists_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1f11576b-d1cc-514a-be44-ad98d5c10992

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_mem_and_mem_nonunits_of_forall_mem_iff_exists_powerSeries

set_option autoImplicit false

namespace GQ_node14

open ModularCurve

theorem expand_eq_zero_iff {R : Type} [CommRing R] (N : ℕ) (hN : N ≠ 0) (z : PowerSeries R) :
    PowerSeries.expand N hN z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  ext m
  rw [← PowerSeries.coeff_expand_mul N hN, h, map_zero, map_zero]

theorem qExpand_ofPowerSeries {R : Type} [CommRing R] (N : ℕ) [NeZero N] (φ : PowerSeries R) :
    qExpand R N (HahnSeries.ofPowerSeries ℤ R φ) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand N (NeZero.ne N) φ) := by
  ext n
  have hN : (0 : ℤ) < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hn : (N : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hn
    rw [qExpand_coeff_mul]
    show ((φ : PowerSeries R) : LaurentSeries R).coeff k =
      ((PowerSeries.expand N (NeZero.ne N) φ : PowerSeries R) : LaurentSeries R).coeff ((N : ℤ) * k)
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    by_cases hk : k < 0
    · rw [if_pos hk, if_pos (mul_neg_of_pos_of_neg hN hk)]
    · rw [if_neg hk, if_neg (not_lt.mpr (mul_nonneg hN.le (not_lt.mp hk))), Int.natAbs_mul, Int.natAbs_natCast,
        PowerSeries.coeff_expand_mul]
  · rw [qExpand_coeff_of_not_dvd N _ hn]
    show (0 : R) = ((PowerSeries.expand N (NeZero.ne N) φ : PowerSeries R) : LaurentSeries R).coeff n
    rw [PowerSeries.coeff_coe]
    split_ifs with h
    · rfl
    · rw [PowerSeries.coeff_expand_of_not_dvd]
      rwa [Int.natCast_dvd] at hn

end GQ_node14

theorem solution
    (L : Type) [Field L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L]
    (W₀ : ValuationSubring ↥K)
    (h1 : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (h5 : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (N : ℕ) [NeZero N] (f : ↥K) (hfN : ModularCurve.qExpand L N (f : LaurentSeries L) ∈ K) :
    (f ∈ W₀ → (⟨ModularCurve.qExpand L N (f : LaurentSeries L), hfN⟩ : ↥K) ∈ W₀) ∧
    (f ∈ W₀.nonunits → (⟨ModularCurve.qExpand L N (f : LaurentSeries L), hfN⟩ : ↥K) ∈ W₀.nonunits) := by
  have hN : N ≠ 0 := NeZero.ne N

  have pres : ∀ (x y : PowerSeries A),
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (((⟨ModularCurve.qExpand L N (f : LaurentSeries L), hfN⟩ : ↥K)) : LaurentSeries L) *
          HahnSeries.ofPowerSeries ℤ L ((PowerSeries.expand N hN y).map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L ((PowerSeries.expand N hN x).map (algebraMap A L)) := by
    intro x y hxy
    have h := congrArg (ModularCurve.qExpand L N) hxy
    rw [map_mul, GQ_node14.qExpand_ofPowerSeries, GQ_node14.qExpand_ofPowerSeries,
      ← PowerSeries.map_expand, ← PowerSeries.map_expand] at h
    exact h
  have hres : ∀ z : PowerSeries A, (PowerSeries.expand N hN z).map (IsLocalRing.residue A) ≠ 0 ↔
      z.map (IsLocalRing.residue A) ≠ 0 := fun z => by
    rw [PowerSeries.map_expand, Ne, GQ_node14.expand_eq_zero_iff]
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨x, y, hy, hxy⟩ := (h1 f).1 hf
    exact (h1 _).2 ⟨PowerSeries.expand N hN x, PowerSeries.expand N hN y, (hres y).2 hy, pres x y hxy⟩
  · have hfW : f ∈ W₀ := W₀.nonunits_subset hf
    obtain ⟨x, y, hy, hxy⟩ := (h1 f).1 hfW
    have hx0 : x.map (IsLocalRing.residue A) = 0 := (h5 f x y hy hxy).1 hf
    refine (h5 _ (PowerSeries.expand N hN x) (PowerSeries.expand N hN y) ((hres y).2 hy) (pres x y hxy)).2 ?_
    rw [PowerSeries.map_expand, hx0, map_zero]

end S_ModularCurve_qExpand_mem_and_mem_nonunits_of_forall_mem_iff_exists_powerSeries
end P2MW
export P2MW.S_ModularCurve_qExpand_mem_and_mem_nonunits_of_forall_mem_iff_exists_powerSeries (solution)
