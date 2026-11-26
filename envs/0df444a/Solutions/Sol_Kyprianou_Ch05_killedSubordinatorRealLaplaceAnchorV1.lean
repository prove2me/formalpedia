-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinatorRealLaplaceAnchorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:01:22.19966+00:00
-- url     : https://prove2.me/submissions/717fa054-f3d9-4e3c-9177-7986105359ac

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set Complex Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta))) :
    Integrable (fun x : ℝ => min (1 : ℝ) |x|) (Pi.restrict (Ioi (0 : ℝ))) ∧
    ∀ (t : NNReal) (x : ℝ), 0 < x →
      (∫ y, Complex.exp (-(x : ℂ) * (y : ℂ)) ∂(P.map (Y t))) =
        Complex.exp (-((t : ℝ) : ℂ) *
          ((d : ℂ) * (x : ℂ) +
            ∫ y in Ioi (0 : ℝ), (1 - Complex.exp (-(x : ℂ) * (y : ℂ))) ∂Pi)) := by
  have hm := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hKilled.1.1
  have hi : Integrable (fun x : ℝ => min (1 : ℝ) |x|) (Pi.restrict (Ioi (0 : ℝ))) := by
    refine ⟨(by fun_prop),?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have he : (fun x : ℝ => ENNReal.ofReal ‖min (1 : ℝ) |x|‖) =ᵐ[Pi.restrict (Ioi 0)]
        (fun x => ENNReal.ofReal (min (1 : ℝ) x)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx' : 0 ≤ x := (mem_Ioi.mp hx).le
      rw [abs_of_nonneg hx',Real.norm_eq_abs,abs_of_nonneg (le_min zero_le_one hx')]
    rw [lintegral_congr_ae he]
    exact hTriplet.2.2.2.1
  refine ⟨hi,?_⟩
  intro t x hx
  rw [integral_map (hm t) (by fun_prop)]
  have he1 : (fun w => Complex.exp (-(x : ℂ) * (Y t w : ℂ))) =
      fun w => ((Real.exp (-x * Y t w) : ℝ) : ℂ) := by
    funext w
    push_cast
    simp [Complex.ofReal_exp]
  have he2 : (fun y : ℝ => 1 - Complex.exp (-(x : ℂ) * (y : ℂ))) =
      fun y => ((1 - Real.exp (-x * y) : ℝ) : ℂ) := by
    funext y
    push_cast
    simp [Complex.ofReal_exp]
  rw [he1,integral_complex_ofReal,hLaplaceLaw t x hx.le,he2,integral_complex_ofReal]
  rw [Complex.ofReal_exp]
  congr 1
  rw [hTriplet.2.2.2.2 x hx.le]
  push_cast
  ring
