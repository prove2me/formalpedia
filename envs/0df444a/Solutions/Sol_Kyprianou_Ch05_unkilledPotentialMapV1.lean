-- Prove2me | solution 1 for Kyprianou.Ch05.unkilledPotentialMapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:42:09.00122+00:00
-- url     : https://prove2.me/submissions/6439f718-915b-451e-b0ef-e0390ce0fed7

import Theorems.Thm_Kyprianou_Ch04_levyJointMeasurableVersionV1
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Represent the potential family as the pushforward of discounted time measure times the probability measure under a jointly measurable process version. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    ∃ Z : NNReal → Omega → Real,
      Measurable (fun p : Real × Omega => Z (Real.toNNReal p.1) p.2) ∧
      (∀ᵐ w ∂P, ∀ t : NNReal, Z t w = Y t w) ∧
      ∀ q : Real, 0 ≤ q →
        U q = Measure.map (fun p : Real × Omega => Z (Real.toNNReal p.1) p.2)
          (((volume.restrict (Set.Ici (0 : Real))).withDensity
            (fun t => ENNReal.ofReal (Real.exp (-q*t)))).prod P) := by
  obtain ⟨Z, hZ, he⟩ := Kyprianou.Ch04.levyJointMeasurableVersionV1 P Y hKilled.1.1
  have hmap : Measurable (fun p : Real × Omega => Z (Real.toNNReal p.1) p.2) :=
    hZ.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  refine ⟨Z, hmap, he, ?_⟩
  intro q hq
  have hd := hKilled.2.2.2.1 rfl
  ext B hB
  rw [Measure.map_apply hmap hB, Measure.prod_apply (hmap hB),
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (measurable_measure_prodMk_left (hmap hB)), (hPotential q hq).2 B hB]
  apply lintegral_congr
  intro t
  change _ = ENNReal.ofReal (Real.exp (-q*t)) * P (Z (Real.toNNReal t) ⁻¹' B)
  congr 1
  apply measure_congr
  filter_upwards [he] with w hw
  apply propext
  change ((Real.toNNReal t : WithTop NNReal) < death w ∧ Y (Real.toNNReal t) w ∈ B) ↔
    Z (Real.toNNReal t) w ∈ B
  rw [hd w, hw (Real.toNNReal t)]
  exact and_iff_right (WithTop.coe_lt_top _)
