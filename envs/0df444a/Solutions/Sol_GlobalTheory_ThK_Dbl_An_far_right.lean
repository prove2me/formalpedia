-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.An.far_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:28:40.251203+00:00
-- url     : https://prove2.me/submissions/a70fd46d-ed3b-4f3c-8de6-6a67d8fbac54

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
theorem _root_.solution [Group G] [ContinuousMul G] (μ : Measure G) [SFinite μ] {k : G × G → ℂ} {w : G → ℂ} (hk : BC k) (hφ : BC φ)
    (hw : Integrable w μ) (h : ∀ h, ∫ h', k (h, h') * φ h' ∂ν = ∫ g, w g * φ (h * g) ∂μ) :
    ∫ y, k y * (φ y.2 * star (φ y.1)) ∂ν.prod ν = ∫ g, w g * ∫ h, φ (h * g) * star (φ h) ∂ν ∂μ := by
  rw [integral_prod _ (BC.int (hk.mul ((hφ.comp continuous_snd).mul (hφ.comp continuous_fst).star)) _)]
  simp only [← mul_assoc, integral_mul_const, h]
  simp only [← integral_mul_const, ← integral_const_mul, mul_assoc]
  obtain ⟨c, C, hC⟩ := (hφ.comp (u := fun y : G × G => y.1 * y.2) (by fun_prop)).mul (hφ.comp continuous_fst).star
  exact integral_integral_swap (f := fun h g => w g * (φ (h * g) * star (φ h)))
    ((hw.comp_snd ν).mul_bdd c.aestronglyMeasurable (.of_forall hC))
end GlobalTheory.ThK.Dbl.An
