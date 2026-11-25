-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuDsAd.lie_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:33:18.70533+00:00
-- url     : https://prove2.me/submissions/f7c9e20b-8e31-4fc1-aebd-01aedf0c522a

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DerivedSeriesAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuDsAd
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.BmuDsAd
theorem _root_.solution {Hm y X : Mat n} (hy : IsUnit y) (hyH : yᴴ * Hm * y = Hm) (hX : Lie Hm X) :
    Lie Hm (y⁻¹ * X * y) := by
  have hd : IsUnit y.det := (Matrix.isUnit_iff_isUnit_det y).1 hy
  have h1 : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h2 : Hm * y⁻¹ = yᴴ * Hm := by
    calc Hm * y⁻¹ = yᴴ * Hm * y * y⁻¹ := by rw [hyH]
      _ = yᴴ * Hm := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h3 : y⁻¹ᴴ * Hm = Hm * y := by
    calc y⁻¹ᴴ * Hm = y⁻¹ᴴ * (yᴴ * Hm * y) := by rw [hyH]
      _ = (y * y⁻¹)ᴴ * (Hm * y) := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hm * y := by rw [h1]; simp
  unfold Lie at hX ⊢
  calc (y⁻¹ * X * y)ᴴ * Hm + Hm * (y⁻¹ * X * y)
      = yᴴ * Xᴴ * (y⁻¹ᴴ * Hm) + (Hm * y⁻¹) * X * y := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = yᴴ * (Xᴴ * Hm + Hm * X) * y := by
        rw [h2, h3]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX]; simp
end GlobalTheory.CompanionTheory.BmuDsAd
