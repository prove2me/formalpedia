-- Prove2me | solution 1 for GlobalTheory.det_gram_pi_hermForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:33:54.918834+00:00
-- url     : https://prove2.me/submissions/8ee51cf1-adad-4896-9749-589c47e0bcef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_VolumeFundamentalDomainStdRealBasis

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
open GlobalTheory
open UnimodVol
namespace GlobalTheory
theorem _root_.solution {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)).det =
      (Real.pi : ℂ) ^ g * Hm.det * ((‖W.det‖ ^ 2 : ℝ) : ℂ) := by
  have h : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)) =
      (Real.pi : ℂ) • (W * (Hm * Wᴴ)) := by
    ext i j
    simp [hermForm, Matrix.mul_apply, dotProduct, mulVec]
  rw [h, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Fintype.card_fin,
    ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring
end GlobalTheory
