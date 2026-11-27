-- Prove2me | solution 1 for GlobalTheory.volume_div_eq_inv_of_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:57.236878+00:00
-- url     : https://prove2.me/submissions/47034044-877f-46e2-b6f0-fd6110529e08

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_VolumeFundamentalDomainStdRealBasis
import Theorems.Thm_GlobalTheory_UnimodVol_posDef_of_hermForm
import Theorems.Thm_GlobalTheory_UnimodVol_det_re_pos
import Theorems.Thm_GlobalTheory_volume_mul_det_eq_one_of_unimodular
import Theorems.Thm_GlobalTheory_det_gram_pi_hermForm

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
theorem _root_.solution (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hfull : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Fd : Set (Fin g → ℂ))
    (hH : Hm.IsHermitian) (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hE : ∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) (hbij : Function.Bijective Ef)
    (hFd : IsAddFundamentalDomain Λ Fd volume) (W : Matrix (Fin g) (Fin g) ℂ) (hW : W.det ≠ 0) :
    0 < Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 ∧
    (volume Fd).toReal / (Real.pi ^ g * ‖W.det‖ ^ 2) = (Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2)⁻¹ ∧
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W i) (W j)).det =
      ((Real.pi ^ g * Hm.det.re * ‖W.det‖ ^ 2 : ℝ) : ℂ) := by
  have h := volume_mul_det_eq_one_of_unimodular g Λ hfull Hm Ef Fd hH hpos hE hbij hFd
  have hp := (det_re_pos hH hpos).1
  have hW' : 0 < ‖W.det‖ := norm_pos_iff.2 hW
  have hπ := Real.pi_pos
  refine ⟨by positivity, ?_, ?_⟩
  · rw [eq_inv_of_mul_eq_one_left h]
    field_simp
  · have him : Hm.det = (Hm.det.re : ℂ) :=
      Complex.ext rfl (by simpa using (Complex.pos_iff.1 (posDef_of_hermForm hH hpos).det_pos).2.symm)
    rw [det_gram_pi_hermForm, him]
    push_cast
    simp
end GlobalTheory
