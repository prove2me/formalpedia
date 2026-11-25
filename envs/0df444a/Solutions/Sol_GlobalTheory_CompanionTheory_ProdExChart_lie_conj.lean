-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ProdExChart.lie_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:45:48.275562+00:00
-- url     : https://prove2.me/submissions/3afb7597-3c92-4317-bc50-c3f062225de6

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ChartExistence
import Theorems.Thm_GlobalTheory_CompanionTheory_ProdExChart_isUnit_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdExChart
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ProdExChart
theorem _root_.solution {Hm g Y : Mat n} (h : Hm * Hm = 1) (hg : g ∈ UH Hm) (hY : Lie Hm Y) :
    Lie Hm (g⁻¹ * Y * g) := by
  have hg' : gᴴ * Hm * g = Hm := hg
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).1 (isUnit_of_mem h hg)
  have e2 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e3 : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, e2, conjTranspose_one]
  have a1 : (g⁻¹)ᴴ * Hm = Hm * g := by
    calc (g⁻¹)ᴴ * Hm = (g⁻¹)ᴴ * (gᴴ * Hm * g) := by rw [hg']
      _ = ((g⁻¹)ᴴ * gᴴ) * Hm * g := by simp only [Matrix.mul_assoc]
      _ = Hm * g := by rw [e3, Matrix.one_mul]
  have a2 : Hm * g⁻¹ = gᴴ * Hm := by
    calc Hm * g⁻¹ = (gᴴ * Hm * g) * g⁻¹ := by rw [hg']
      _ = gᴴ * Hm * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
      _ = gᴴ * Hm := by rw [e2, Matrix.mul_one]
  have hY' : Yᴴ * Hm + Hm * Y = 0 := hY
  unfold Lie
  calc (g⁻¹ * Y * g)ᴴ * Hm + Hm * (g⁻¹ * Y * g)
      = gᴴ * Yᴴ * ((g⁻¹)ᴴ * Hm) + (Hm * g⁻¹) * Y * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Yᴴ * Hm + Hm * Y) * g := by
        rw [a1, a2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY', Matrix.mul_zero, Matrix.zero_mul]
end GlobalTheory.CompanionTheory.ProdExChart
