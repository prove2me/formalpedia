-- Prove2me | solution 1 for GlobalTheory.UnimodVol.det_gram_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:02:57.848584+00:00
-- url     : https://prove2.me/submissions/41e94245-4141-4406-84ff-fd4803136dae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_VolumeFundamentalDomainStdRealBasis
import Theorems.Thm_GlobalTheory_UnimodVol_re_dotProduct_star
import Theorems.Thm_GlobalTheory_UnimodVol_im_hermForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped ComplexOrder
open GlobalTheory GlobalTheory.UnimodVol
namespace GlobalTheory.UnimodVol
theorem _root_.solution {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (v : (Σ _ : Fin g, Fin 2) → Fin g → ℂ) :
    (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im).det =
      ((stdRealBasis g).det v) ^ 2 * ‖Hm.det‖ ^ 2 := by
  set T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    (Matrix.toLin' (Complex.I • Hm.map star)).restrictScalars ℝ with hT
  have h : (Matrix.of fun i j => (hermForm Hm (v i) (v j)).im) =
      ((stdRealBasis g).toMatrix v)ᵀ * (stdRealBasis g).toMatrix (T ∘ v) := by
    ext i j
    rw [Matrix.of_apply, im_hermForm, re_dotProduct_star, Matrix.mul_apply]
    rfl
  have hd : LinearMap.det T = ‖Hm.det‖ ^ 2 := by
    have : (Hm.map star).det = star Hm.det := ((starRingEnd ℂ).map_det Hm).symm
    rw [hT, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, Matrix.det_smul, this]
    simp
  rw [h, Matrix.det_mul, Matrix.det_transpose, ← Module.Basis.det_apply, ← Module.Basis.det_apply,
    Module.Basis.det_comp, hd]
  ring
end GlobalTheory.UnimodVol
