-- Prove2me | solution 1 for GlobalTheory.RiemannRel.symm_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:19.578821+00:00
-- url     : https://prove2.me/submissions/9a0a32e7-34da-4854-83ca-501dda6e2614

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
theorem _root_.solution (G A τ : Matrix (Fin g) (Fin g) ℂ) (hG : G.IsHermitian)
    (hA : A.det ≠ 0)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm G z z).re)
    (hM : ∀ j k, ((Aᵀ * G * A.map (starRingEnd ℂ)) j k).im = 0)
    (hN : ∀ j k, ((Aᵀ * G * (A * τ).map (starRingEnd ℂ)) j k).im = -(1 : Matrix (Fin g) (Fin g) ℝ) j k)
    (hK : ∀ j k, (((A * τ)ᵀ * G * (A * τ).map (starRingEnd ℂ)) j k).im = 0) :
    τ.IsSymm ∧ (τ.map Complex.im).PosDef := by
  set M := Aᵀ * G * A.map (starRingEnd ℂ) with hMdef
  set S : Matrix (Fin g) (Fin g) ℝ := M.map Complex.re with hSdef
  set X : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.re with hXdef
  set Y : Matrix (Fin g) (Fin g) ℝ := τ.map Complex.im with hYdef
  have hMh : Mᴴ = M := by
    have h1 : (A.map (starRingEnd ℂ))ᴴ = Aᵀ := by ext i j; simp
    have h2 : (Aᵀ)ᴴ = A.map (starRingEnd ℂ) := by ext i j; simp
    rw [hMdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1, h2, hG.eq, Matrix.mul_assoc]
  have hSsymm : ∀ j k, S k j = S j k := by
    intro j k
    have := congrFun (congrFun hMh j) k
    rw [Matrix.conjTranspose_apply] at this
    simp only [S, Matrix.map_apply, ← this, Complex.star_def, Complex.conj_re]
  have hSh : S.IsHermitian := by
    ext j k; simp [hSsymm]
  have hN' : Aᵀ * G * (A * τ).map (starRingEnd ℂ) = M * τ.map (starRingEnd ℂ) := by
    rw [Matrix.map_mul, hMdef]; simp only [Matrix.mul_assoc]
  have hSY : S * Y = 1 := by
    ext j k
    have := hN j k
    rw [hN'] at this
    simp only [Matrix.mul_apply, Complex.im_sum, Complex.mul_im, hM, Matrix.map_apply,
      Complex.conj_re, Complex.conj_im, zero_mul, add_zero] at this
    simp only [Matrix.mul_apply, S, Y, Matrix.map_apply]
    linarith [show ∑ x, (M j x).re * -(τ x k).im = -∑ x, (M j x).re * (τ x k).im by
      simp [Finset.sum_neg_distrib]]
  have hSpos : S.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hSh, fun x hx => ?_⟩
    have hAx : A *ᵥ (fun j => (x j : ℂ)) ≠ 0 := by
      intro h0
      apply hx
      ext j
      have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hA h0) j
      simpa using this
    have h := hpos _ hAx
    rw [_root_.GlobalTheory.RiemannRel.hermForm_mulVec] at h
    simpa [dotProduct, mulVec, Complex.re_sum, Complex.mul_re, hM, S] using h
  have hYinv : Y = S⁻¹ := (Matrix.inv_eq_right_inv hSY).symm
  have hYpos : Y.PosDef := hYinv ▸ hSpos.inv
  have hK' : (A * τ)ᵀ * G * (A * τ).map (starRingEnd ℂ) = τᵀ * M * τ.map (starRingEnd ℂ) := by
    rw [Matrix.transpose_mul, Matrix.map_mul, hMdef]; simp only [Matrix.mul_assoc]
  have hKim : ∀ j k, ((τᵀ * M * τ.map (starRingEnd ℂ)) j k).im = (Yᵀ * S * X - Xᵀ * S * Y) j k := by
    intro j k
    simp only [Matrix.mul_apply, Matrix.sub_apply, Complex.im_sum, Complex.re_sum, Complex.mul_im,
      Complex.mul_re, hM, Matrix.map_apply, Matrix.transpose_apply, Complex.conj_re, Complex.conj_im,
      Finset.sum_mul, ← Finset.sum_sub_distrib, S, X, Y]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  have hYS : Yᵀ * S = 1 := by
    have hSt : Sᵀ = S := by ext j k; exact hSsymm j k
    rw [← hSt, ← Matrix.transpose_mul, hSY, Matrix.transpose_one]
  have hXs : ∀ j k, X j k = X k j := by
    intro j k
    have h := hK j k
    rw [hK', hKim, Matrix.mul_assoc Xᵀ, hSY, hYS, Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply,
      Matrix.transpose_apply] at h
    linarith
  have hYs : ∀ j k, Y j k = Y k j := by
    intro j k
    have := congrFun (congrFun hYpos.1 k) j
    simpa using this
  refine ⟨Matrix.IsSymm.ext fun i j => Complex.ext ?_ ?_, hYpos⟩
  · exact hXs j i
  · exact hYs j i
end _root_.GlobalTheory.RiemannRel
end GlobalTheory.RiemannRel
