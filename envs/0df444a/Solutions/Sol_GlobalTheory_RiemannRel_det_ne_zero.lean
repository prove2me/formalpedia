-- Prove2me | solution 1 for GlobalTheory.RiemannRel.det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:46.704819+00:00
-- url     : https://prove2.me/submissions/68b12275-5d83-4dd7-82b0-d94636c9a447

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Theorems.Thm_GlobalTheory_RiemannRel_hermForm_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.RiemannRel
variable {g : ℕ}
open NumberField Matrix
open scoped nonZeroDivisors
variable {g : ℕ}
namespace GlobalTheory.RiemannRel
namespace _root_.GlobalTheory.RiemannRel
theorem _root_.solution (G A B : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z z).re)
    (hM : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0)
    (hN : ∀ j k, ((Aᵀ * G * B.map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k) :
    A.det ≠ 0 := by
  intro hA0
  obtain ⟨v, hv0, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA0
  have hreal : ∀ r s : Fin g → ℝ,
      (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ fun j => (r j : ℂ)) (A *ᵥ fun j => (s j : ℂ))).im = 0 := by
    intro r s
    rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec]
    simp [dotProduct, mulVec, Complex.im_sum, Complex.mul_im, hM]
  have hcross : ∀ (r : Fin g → ℝ) (k : Fin g),
      (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ fun j => (r j : ℂ)) (B *ᵥ Pi.single k 1)).im = -r k := by
    intro r k
    rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec, Pi.star_single, star_one, Matrix.mulVec_single_one]
    simp [dotProduct, Complex.im_sum, Complex.mul_im, hN, Matrix.one_apply]
  set x : Fin g → ℂ := fun j => ((v j).re : ℂ) with hx
  set y : Fin g → ℂ := fun j => ((v j).im : ℂ) with hy
  have hv : v = x + Complex.I • y := by
    ext j; simp only [x, y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]; exact (Complex.re_add_im _).symm
  have hAx : A *ᵥ x = -(Complex.I • A *ᵥ y) := by
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_smul] at hAv
    exact eq_neg_of_add_eq_zero_left hAv
  have hform : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ x) (A *ᵥ x) = Complex.I * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ x) (A *ᵥ y) := by
    conv_lhs => arg 3; rw [hAx]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
    simp [star_neg, star_smul, Matrix.mulVec_neg, Matrix.mulVec_smul, dotProduct_smul]
  have hx0 : A *ᵥ x = 0 := by
    by_contra hne
    have h1 := hpos _ hne
    rw [hform, Complex.mul_re, Complex.I_re, Complex.I_im, hreal] at h1
    simp at h1
  have hy0 : A *ᵥ y = 0 := by
    rw [hx0, eq_comm, neg_eq_zero, smul_eq_zero] at hAx
    exact hAx.resolve_left Complex.I_ne_zero
  apply hv0
  ext k
  have h1 := hcross (fun j => (v j).re) k
  have h2 := hcross (fun j => (v j).im) k
  change (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ x) _).im = _ at h1
  change (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G (A *ᵥ y) _).im = _ at h2
  rw [hx0] at h1
  rw [hy0] at h2
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, zero_dotProduct, Complex.zero_im, zero_eq_neg] at h1 h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2
end _root_.GlobalTheory.RiemannRel
end GlobalTheory.RiemannRel
