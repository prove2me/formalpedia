-- Prove2me | solution 1 for GlobalTheory.SharpObj.im_hermForm_per
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:15:04.941856+00:00
-- url     : https://prove2.me/submissions/8546e2a8-c8dc-45cc-8d8d-7321c05557e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian
import Theorems.Thm_GlobalTheory_SharpObj_hermForm_real_im
import Theorems.Thm_GlobalTheory_SharpObj_per_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SharpObj
variable {h : ℕ}
variable {τ : Matrix (Fin h) (Fin h) ℂ}
private theorem re_mulVec_ofRealVec (a : Fin h → ℝ) (i : Fin h) :
    ((τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a)) i).re = ((τ.map Complex.re).mulVec a) i := by
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [Matrix.mulVec, dotProduct, Complex.re_sum]
private theorem im_mulVec_ofRealVec (a : Fin h → ℝ) (i : Fin h) :
    ((τ.mulVec (ReciprocityTheory.PTheta.ofRealVec a)) i).im = ((τ.map Complex.im).mulVec a) i := by
  unfold ReciprocityTheory.PTheta.ofRealVec
  simp [Matrix.mulVec, dotProduct, Complex.im_sum]
private theorem re_per' (x : Fin h ⊕ Fin h → ℤ) :
    (fun i => (per τ x i).re) = (τ.map Complex.re).mulVec (fun i => (x (.inl i) : ℝ)) + fun i => (x (.inr i) : ℝ) := by
  funext i
  rw [per_eq, Pi.add_apply, Complex.add_re, re_mulVec_ofRealVec]
  simp [ReciprocityTheory.PTheta.ofRealVec.eq_1]
private theorem im_per' (x : Fin h ⊕ Fin h → ℤ) :
    (fun i => (per τ x i).im) = (τ.map Complex.im).mulVec (fun i => (x (.inl i) : ℝ)) := by
  funext i
  rw [per_eq, Pi.add_apply, Complex.add_im, im_mulVec_ofRealVec]
  simp [ReciprocityTheory.PTheta.ofRealVec.eq_1]
end GlobalTheory.SharpObj
end
end

set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SharpObj
variable {h : ℕ}
variable {τ : Matrix (Fin h) (Fin h) ℂ}
namespace GlobalTheory.SharpObj
theorem _root_.solution (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) (x y : Fin h ⊕ Fin h → ℤ) :
    (hermForm (imInv τ) (per τ x) (per τ y)).im = omegaStd x y := by
  have hu : IsUnit (τ.map Complex.im).det := (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have hYt : Matrix.transpose (τ.map Complex.im) = τ.map Complex.im := by
    have := hp.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hXt : Matrix.transpose (τ.map Complex.re) = τ.map Complex.re := by
    rw [← Matrix.transpose_map, hs.eq]
  rw [imInv, hermForm_real_im, re_per', im_per', re_per', im_per']
  set X := τ.map Complex.re
  set Y := τ.map Complex.im
  set a : Fin h → ℝ := fun i => (x (.inl i) : ℝ)
  set b : Fin h → ℝ := fun i => (x (.inr i) : ℝ)
  set c : Fin h → ℝ := fun i => (y (.inl i) : ℝ)
  set d : Fin h → ℝ := fun i => (y (.inr i) : ℝ)
  have e1 : Y⁻¹.mulVec (Y.mulVec c) = c := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have e2 : ∀ v, (Y.mulVec a) ⬝ᵥ (Y⁻¹.mulVec v) = a ⬝ᵥ v := fun v => by
    rw [← hYt, ← Matrix.vecMul_transpose, hYt, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hYt,
      Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have e3 : (X.mulVec a) ⬝ᵥ c = a ⬝ᵥ (X.mulVec c) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hXt, dotProduct_comm]
  rw [e1, e2, add_dotProduct, e3, dotProduct_add]
  have hω : (omegaStd x y : ℝ) = a ⬝ᵥ d - b ⬝ᵥ c := by
    simp only [omegaStd, a, b, c, d, dotProduct]
    push_cast
    rw [Finset.sum_sub_distrib]
  rw [hω]
  ring
end GlobalTheory.SharpObj
