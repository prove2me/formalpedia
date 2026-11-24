-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.An.at_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:32:41.428379+00:00
-- url     : https://prove2.me/submissions/820082cf-d630-484e-9c0f-1240a07f5819

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_FarRight
import Theorems.Thm_GlobalTheory_ThK_Dbl_An_BC_mul
import Theorems.Thm_GlobalTheory_ThK_Dbl_An_BC_comp
import Theorems.Thm_GlobalTheory_ThK_Dbl_An_BC_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.An
open MeasureTheory Filter Topology
variable {G H : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (ν : Measure G) [IsFiniteMeasure ν] (ρ : Measure H) [IsFiniteMeasure ρ] {φ : G → ℂ}
namespace GlobalTheory.ThK.Dbl.An
theorem _root_.solution {θ : H × G → ℂ} (hθ : BC θ) (hφ : BC φ) :
    ∫ y, (∫ g, θ (g, y.1) * star (θ (g, y.2)) ∂ρ) * (φ y.2 * star (φ y.1)) ∂ν.prod ν =
      ∫ g, (∫ h, φ h * star (θ (g, h)) ∂ν) * star (∫ h, φ h * star (θ (g, h)) ∂ν) ∂ρ := by
  simp only [← integral_mul_const]
  rw [integral_integral_swap (f := fun (y : G × G) g => θ (g, y.1) * star (θ (g, y.2)) * (φ y.2 * star (φ y.1)))
    (BC.int (((hθ.comp (u := fun y : (G × G) × H => (y.2, y.1.1)) (by fun_prop)).mul
      (hθ.comp (u := fun y : (G × G) × H => (y.2, y.1.2)) (by fun_prop)).star).mul
      ((hφ.comp (by fun_prop)).mul (hφ.comp (by fun_prop)).star)) _)]
  refine integral_congr_ae (.of_forall fun g => ?_)
  simp only [integral_mul_const]
  rw [mul_comm, Complex.star_def, ← integral_conj, ← integral_prod_mul]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring
end GlobalTheory.ThK.Dbl.An
