-- Prove2me | solution 1 for Kyprianou.Ch04.limitingDrawdown_LaplaceTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:47:17.849036+00:00
-- url     : https://prove2.me/submissions/15b0e189-79d7-4261-83a9-3f5df4255273

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch04_nonSingularInfimumTransform
import Theorems.Thm_Kyprianou_Ch04_zeroSlopeOfPositiveRoot
import Theorems.Thm_Kyprianou_Ch04_nonpositiveSlopeLowerUnbounded
import Theorems.Thm_Kyprianou_Ch04_infimumLimitSupport
import Theorems.Thm_Kyprianou_Ch04_fixedHorizonSignedExtremaLaplaceEquality
open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator :
      ¬ (∀ᵐ omega : Omega ∂P, Antitone (fun t : NNReal => L.X t omega))) :
    let nonnegativeSlope : Real :=
      max 0 (sInf ((fun theta : Real => L.ψ theta / theta) '' Set.Ioi 0))
    let meanNonpositive : Prop :=
      forall epsilon : Real, 0 < epsilon ->
        exists theta : Real, 0 < theta ∧ L.ψ theta < epsilon * theta
    (∀ beta : Real, 0 < beta →
      Tendsto
        (fun t : NNReal =>
          ∫ omega, Real.exp (-beta *
            (sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t) - L.X t omega)) ∂P)
        atTop (nhds (nonnegativeSlope * beta / L.ψ beta))) := by
  intro m mean beta hb
  have hinf : Tendsto
      (fun t : NNReal => ∫ w, Real.exp (beta * sInf ((fun s : NNReal => L.X s w) '' Iic t)) ∂P)
      atTop (nhds (m * beta / L.ψ beta)) := by
    by_cases hz : L.ψ beta = 0
    · have hm : m = 0 := Kyprianou.Ch04.zeroSlopeOfPositiveRoot L.ψ beta hb hz
      have hB := Kyprianou.Ch04.nonpositiveSlopeLowerUnbounded P F L hNotNegativeSubordinator hm
      have h := (Kyprianou.Ch04.infimumLimitSupport P F L beta hb).2.2 hB
      simpa only [hm,zero_mul,zero_div] using h
    · exact Kyprianou.Ch04.nonSingularInfimumTransform P F L hNotNegativeSubordinator beta hb hz
  apply hinf.congr'
  filter_upwards [eventually_gt_atTop (0 : NNReal)] with t ht
  have h := Kyprianou.Ch04.fixedHorizonSignedExtremaLaplaceEquality P F L t ht beta
  rw [← h]
  apply integral_congr_ae
  exact Eventually.of_forall (fun w => by congr 1; ring)
