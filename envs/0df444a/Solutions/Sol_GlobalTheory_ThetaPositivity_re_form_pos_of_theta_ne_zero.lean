-- Prove2me | solution 1 for GlobalTheory.ThetaPositivity.re_form_pos_of_theta_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:09:32.545101+00:00
-- url     : https://prove2.me/submissions/4d7a34a9-0999-4a59-9a8f-887fd2c070a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ReFormPosOfThetaNeZero
import Theorems.Thm_GlobalTheory_ThetaPositivity_form_add_self
import Theorems.Thm_GlobalTheory_ThetaPositivity_exists_norm_le
import Theorems.Thm_GlobalTheory_ThetaPositivity_eq_zero_of_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory.ThetaPositivity
variable {g : ℕ}
open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
private lemma re_form_add_smul_of_isHermitian {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) (t : ℂ) :
    ((z + t • w) ⬝ᵥ Hm.mulVec (star (z + t • w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (star t * (z ⬝ᵥ Hm.mulVec (star w))).re
        + Complex.normSq t * (w ⬝ᵥ Hm.mulVec (star w)).re := by
  rw [_root_.GlobalTheory.ThetaPositivity.form_add_self hH]
  have h1 : z ⬝ᵥ Hm.mulVec (star (t • w)) = star t * (z ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : (t • w) ⬝ᵥ Hm.mulVec (star (t • w)) =
      (Complex.normSq t : ℂ) * (w ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_comm (star t), Complex.star_def, Complex.mul_conj]
  rw [h1, h2, Complex.re_ofReal_mul]
end GlobalTheory.ThetaPositivity
end

set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaPositivity
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}
namespace GlobalTheory.ThetaPositivity
namespace _root_.GlobalTheory.ThetaPositivity
theorem _root_.solution :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
        (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) →
        (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) →
        Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 →
        (∀ (l : Λ) z, θ (z + l) =
          (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
            Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) →
        ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro g Λ hdisc hspan Hm χ Ef θ hH hχ hE hinj hθ hθ0 htr z hz
  classical
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  have hpsd : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := by
    intro w
    by_contra hw
    push_neg at hw
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.ThetaPositivity.exists_norm_le Λ hH χ hχ hθ.continuous htr
    exact hθ0 (_root_.GlobalTheory.ThetaPositivity.eq_zero_of_neg hH hθ hC hw)
  refine lt_of_le_of_ne (hpsd z) (fun hz0 => hz ?_)
  have him : ∀ v : Fin g → ℂ, (z ⬝ᵥ Hm.mulVec (star v)).im = 0 := by
    intro v
    have key : ∀ s : ℝ, 0 ≤ 2 * s * (z ⬝ᵥ Hm.mulVec (star v)).im
        + s ^ 2 * (v ⬝ᵥ Hm.mulVec (star v)).re := by
      intro s
      have h := hpsd (z + ((s : ℂ) * Complex.I) • v)
      rw [re_form_add_smul_of_isHermitian hH, ← hz0] at h
      have e1 : (star ((s : ℂ) * Complex.I) * (z ⬝ᵥ Hm.mulVec (star v))).re =
          s * (z ⬝ᵥ Hm.mulVec (star v)).im := by
        simp [Complex.mul_re]
      have e2 : Complex.normSq ((s : ℂ) * Complex.I) = s ^ 2 := by simp [sq]
      rw [e1, e2] at h
      linarith
    set c := (z ⬝ᵥ Hm.mulVec (star v)).im
    set d := (v ⬝ᵥ Hm.mulVec (star v)).re
    have hd1 : 0 < d + 1 := by linarith [hpsd v]
    have h' : 0 ≤ -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
      have e : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d = -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
        field_simp
        ring
      linarith [key (-c / (d + 1))]
    rw [neg_div, neg_nonneg, div_le_iff₀ (by positivity), zero_mul] at h'
    have hc2 : c ^ 2 = 0 := by nlinarith [sq_nonneg c, hpsd v]
    exact (pow_eq_zero_iff two_ne_zero).mp hc2
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  let M : Matrix _ _ ℤ := Matrix.of fun i j => Ef (b i) (b j)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hc0
    have hl : Ef (b.equivFun.symm c) = 0 := by
      refine b.ext fun j => ?_
      have := congrFun hc j
      simpa [Module.Basis.equivFun_symm_apply, map_sum, Matrix.vecMul, dotProduct, M] using this
    have := hinj (hl.trans (map_zero Ef).symm)
    have h2 := congrArg b.equivFun this
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  have hr : (fun i => bR.repr z i) ᵥ* M.map (Int.cast : ℤ → ℝ) = 0 := by
    funext j
    have h := him (b j : Fin g → ℂ)
    rw [← bR.sum_repr z] at h
    simp only [sum_dotProduct, smul_dotProduct, Complex.im_sum, Complex.smul_im,
      Module.Basis.ofZLatticeBasis_apply, bR, ← hE] at h
    simpa [Matrix.vecMul, dotProduct, M] using h
  have hdetR : (M.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    have e : (M.map (Int.castRingHom ℝ)).det = Int.castRingHom ℝ M.det := (RingHom.map_det _ _).symm
    simpa using e ▸ (Int.cast_ne_zero.mpr hdet)
  have hr0 : (fun i => bR.repr z i) = 0 := by
    by_contra hne
    exact hdetR (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hr⟩)
  have hz' : bR.repr z = 0 := by
    ext i
    exact congrFun hr0 i
  simpa using hz'
end _root_.GlobalTheory.ThetaPositivity
end GlobalTheory.ThetaPositivity
