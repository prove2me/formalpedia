-- Prove2me | solution 1 for GlobalTheory.RiemannRel.matrix_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:18:03.630778+00:00
-- url     : https://prove2.me/submissions/25e67cad-86ae-410c-af6f-ddf97f85b88e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSiegelPeriodOfSymplecticBasis
import Theorems.Thm_GlobalTheory_RiemannRel_map_im_mul
import Theorems.Thm_GlobalTheory_RiemannRel_map_re_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam
open Matrix
open GlobalTheory GlobalTheory.RiemannRel
namespace GlobalTheory.RiemannRel
theorem _root_.solution {h : ℕ} (Hm L M : Matrix (Fin h) (Fin h) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin h → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re)
    (hG : (Mᵀ * Hm * M.map star).map Complex.im = 0)
    (hA : (Lᵀ * Hm * M.map star).map Complex.im = 1)
    (hB : (Lᵀ * Hm * L.map star).map Complex.im = 0) :
    IsUnit M.det ∧ (M⁻¹ * L).IsSymm ∧ ((M⁻¹ * L).map Complex.im).PosDef := by
  set G := Mᵀ * Hm * M.map star with hGdef
  have hGh : G.IsHermitian := by
    have h1 : M.map star = (Mᵀ)ᴴ := by ext i j; simp
    rw [hGdef, h1]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hH
  set R := G.map Complex.re with hR
  have hRs : Rᵀ = R := by
    ext i j
    have := congrArg Complex.re (hGh.apply i j)
    simpa [hR] using this
  have hGR : G = R.map Complex.ofReal := by
    ext i j
    have := congrFun (congrFun hG i) j
    apply Complex.ext
    · simp [hR]
    · simpa [hR] using this
  have hRp : R.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (by simpa [Matrix.IsHermitian] using hRs) fun x hx => ?_
    set xc : Fin h → ℂ := fun i => (x i : ℂ) with hxc
    have hst : star (M.mulVec xc) = (M.map star).mulVec xc := by
      funext i
      simp [Matrix.mulVec, dotProduct, hxc]
    have hne : M.mulVec xc ≠ 0 := by
      intro h0
      apply hx
      have h1 : (Lᵀ * Hm * M.map star).mulVec xc = 0 := by
        rw [← Matrix.mulVec_mulVec, ← hst, h0]; simp
      have h2 : ((Lᵀ * Hm * M.map star).map Complex.im).mulVec x = 0 := by
        funext i
        have := congrArg Complex.im (congrFun h1 i)
        simpa [Matrix.mulVec, dotProduct, hxc, Complex.im_sum] using this
      rwa [hA, Matrix.one_mulVec] at h2
    have h3 := hpos _ hne
    have h4 : M.mulVec xc ⬝ᵥ Hm.mulVec (star (M.mulVec xc)) = xc ⬝ᵥ G.mulVec xc := by
      rw [hst, hGdef, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec xc, Matrix.vecMul_transpose]
    rw [h4] at h3
    simpa [Matrix.mulVec, dotProduct, hxc, Complex.re_sum, hR] using h3
  have hRu : IsUnit R.det := hRp.det_pos.ne'.isUnit
  have hMu : IsUnit M.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h1 : G.det = 0 := by
      rw [hGdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0]; simp
    have h2 : G.det = (R.det : ℂ) := by
      rw [hGR]
      exact (Complex.ofRealHom.map_det R).symm
    rw [h1] at h2
    exact hRu.ne_zero (Complex.ofReal_eq_zero.1 h2.symm)
  set τ := M⁻¹ * L with hτ
  have hL : L = M * τ := by rw [hτ, Matrix.mul_nonsing_inv_cancel_left _ _ hMu]
  have hA' : Lᵀ * Hm * M.map star = τᵀ * G := by
    conv_lhs => rw [hL]
    rw [hGdef, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
  have hB' : Lᵀ * Hm * L.map star = τᵀ * G * τ.map star := by
    have : L.map star = M.map star * τ.map star := by
      conv_lhs => rw [hL]
      exact Matrix.map_mul (f := starRingEnd ℂ)
    rw [this, ← Matrix.mul_assoc, hA']
  set X := τ.map Complex.re with hX
  set Y := τ.map Complex.im with hY
  have e1 : τᵀ.map Complex.re = Xᵀ := rfl
  have e2 : τᵀ.map Complex.im = Yᵀ := rfl
  have e3 : (τ.map star).map Complex.re = X := by ext i j; simp [hX]
  have e4 : (τ.map star).map Complex.im = -Y := by ext i j; simp [hY]
  rw [hB', map_im_mul, ← hA', hA, hA', map_re_mul, e1, e2, e3, e4, hG, ← hR] at hB
  rw [hA', map_im_mul, e1, e2, hG, ← hR, Matrix.mul_zero, zero_add] at hA
  have hRY : R * Y = 1 := by
    have := congrArg Matrix.transpose hA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, hRs, Matrix.transpose_one] at this
  have hYi : R⁻¹ = Y := Matrix.inv_eq_right_inv hRY
  have hYi' : R⁻¹ = Yᵀ := Matrix.inv_eq_left_inv hA
  have hXs : Xᵀ = X := by
    rw [Matrix.mul_zero, sub_zero, Matrix.mul_neg, Matrix.mul_assoc, hRY, Matrix.mul_one, Matrix.one_mul] at hB
    exact (neg_add_eq_zero.1 hB)
  refine ⟨hMu, ?_, hYi ▸ hRp.inv⟩
  ext i j
  apply Complex.ext
  · exact congrFun (congrFun hXs i) j
  · exact congrFun (congrFun (hYi'.symm.trans hYi) i) j
end GlobalTheory.RiemannRel
