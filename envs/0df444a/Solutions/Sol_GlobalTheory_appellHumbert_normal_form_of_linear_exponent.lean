-- Prove2me | solution 1 for GlobalTheory.appellHumbert_normal_form_of_linear_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:14:32.982979+00:00
-- url     : https://prove2.me/submissions/54c2094f-cdbf-437e-9d3b-711b518aa394

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertNormalFormOfLinearExponent
import Theorems.Thm_GlobalTheory_AppellHumbert_exists_real_extension
import Theorems.Thm_GlobalTheory_AppellHumbert_eq_sum_re_im

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) → (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ) (Q : (Fin g → ℂ) → ℂ), Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ ∀ (l : Λ) z, a l * cexp (B l z) * cexp (Q z - Q (z + l)) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))))) := by
  intro g Λ hdisc hΛ a B ha hcoc
  classical
  haveI := hdisc
  let b : Λ →+ (Fin g → ℂ) :=
    { toFun := fun l j => B l (Pi.single j 1)
      map_zero' := by ext j; simp
      map_add' := fun l m => by ext j; simp }
  obtain ⟨F, hF0⟩ := _root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ b
  have hF : ∀ (l : Λ) z, B l z = F l ⬝ᵥ z := by
    intro l z
    rw [hF0]
    conv_lhs => rw [show z = ∑ j, z j • (Pi.single j (1 : ℂ) : Fin g → ℂ) by ext i; simp [Pi.single_apply]]
    simp [map_sum, dotProduct, b, mul_comm]
  have hskew : ∀ l m : Λ, ∃ n : ℤ, B l m = B m l + n * (2 * π * I) := by
    intro l m
    have h := hcoc l m
    rw [add_comm, hcoc m l, mul_comm (a m) (a l)] at h
    exact Complex.exp_eq_exp_iff_exists_int.mp (mul_left_cancel₀ (mul_ne_zero (ha l) (ha m)) h).symm
  have hlin : ∀ (P : (Fin g → ℂ) → Prop), P 0 → (∀ x y, P x → P y → P (x + y)) →
      (∀ (c : ℝ) x, P x → P (c • x)) → (∀ l : Λ, P l) → ∀ x, P x := by
    intro P h0 hadd hsmul hl x
    have hx : x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy => exact hl ⟨y, hy⟩
    | zero => exact h0
    | add y z _ _ hy hz => exact hadd y z hy hz
    | smul c y _ hy => exact hsmul c y hy
  have hD1 : ∀ u (m : Λ), (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0 := by
    intro u m
    refine hlin (fun u => (F u ⬝ᵥ m - F m ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_)
      (fun c x hx => ?_) (fun l => ?_) u
    · simp only [map_add, add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢
      linarith
    · simp only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re,
        smul_eq_mul] at hx ⊢
      rw [← mul_sub, hx, mul_zero]
    · obtain ⟨n, hn⟩ := hskew l m
      rw [← hF, ← hF, hn]; simp
  have hD : ∀ u v, (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0 := by
    intro u v
    refine hlin (fun v => (F u ⬝ᵥ v - F v ⬝ᵥ u).re = 0) (by simp) (fun x y hx hy => ?_)
      (fun c x hx => ?_) (fun m => hD1 u m) v
    · simp only [map_add, add_dotProduct, dotProduct_add, Complex.sub_re, Complex.add_re] at hx hy ⊢
      linarith
    · simp only [map_smul, smul_dotProduct, dotProduct_smul, Complex.sub_re, Complex.smul_re,
        smul_eq_mul] at hx ⊢
      rw [← mul_sub, hx, mul_zero]
  let M : Matrix (Fin g) (Fin g) ℂ := fun k j =>
    (1/2 : ℝ) • (F (Pi.single k 1) j - I * F (Pi.single k I) j)
  let N : Matrix (Fin g) (Fin g) ℂ := fun k j =>
    (1/2 : ℝ) • (F (Pi.single k 1) j + I * F (Pi.single k I) j)
  have hFMN : ∀ u, F u = u ᵥ* M + star u ᵥ* N := by
    intro u; ext j
    conv_lhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]
    simp only [map_sum, map_add, map_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, vecMul,
      dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    apply Complex.ext <;> simp [M, N, Complex.mul_re, Complex.mul_im] <;> ring
  have hsym : ∀ k j, (F (Pi.single k 1) j).re = (F (Pi.single j 1) k).re ∧
      (F (Pi.single k I) j).im = (F (Pi.single j I) k).im ∧
      (F (Pi.single k I) j).re = -(F (Pi.single j 1) k).im := by
    intro k j
    have h1 := hD (Pi.single k 1) (Pi.single j 1)
    have h2 := hD (Pi.single k I) (Pi.single j I)
    have h3 := hD (Pi.single k I) (Pi.single j 1)
    simp only [dotProduct_single, mul_one, Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_sub, sub_zero] at h1 h2 h3
    refine ⟨by linarith, by linarith, by linarith⟩
  have hMsym : Mᵀ = M := by
    ext k j
    rw [transpose_apply]
    obtain ⟨a1, a2, a3⟩ := hsym k j
    obtain ⟨b1, b2, b3⟩ := hsym j k
    apply Complex.ext <;> simp [M, Complex.mul_re, Complex.mul_im] <;> linarith
  have hNherm : ∀ i j, (starRingEnd ℂ) (N i j) = N j i := by
    intro k j
    obtain ⟨a1, a2, a3⟩ := hsym k j
    obtain ⟨b1, b2, b3⟩ := hsym j k
    apply Complex.ext <;> simp [N, Complex.mul_re, Complex.mul_im] <;> linarith

  let A : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun u v => u ⬝ᵥ M *ᵥ v
  let K : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun z u => z ⬝ᵥ Nᵀ *ᵥ star u
  have hAsym : ∀ u v, A u v = A v u := by
    intro u v
    simp only [A]
    conv_rhs => rw [← hMsym]
    rw [mulVec_transpose, dotProduct_comm v, ← dotProduct_mulVec]
  have hBF : ∀ (l : Λ) z, B l z = A l z + K z l := by
    intro l z
    simp only [A, K]
    rw [hF, hFMN, add_dotProduct, dotProduct_mulVec, mulVec_transpose, dotProduct_comm z]
  have hKherm : ∀ u v, K v u = (starRingEnd ℂ) (K u v) := by
    intro u v
    simp only [K, dotProduct, mulVec, transpose_apply, map_sum, map_mul, Pi.star_apply,
      Complex.star_def, Complex.conj_conj, hNherm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAadd : ∀ u v, A (u + v) (u + v) = A u u + A u v + A u v + A v v := by
    intro u v
    have := hAsym v u
    simp only [A, mulVec_add, dotProduct_add, add_dotProduct] at this ⊢
    rw [this]; ring
  have hKadd : ∀ u v, K (u + v) (u + v) = K u u + K u v + K v u + K v v := by
    intro u v
    simp only [K, star_add, mulVec_add, dotProduct_add, add_dotProduct]
    ring

  let Hm : Matrix (Fin g) (Fin g) ℂ := (Real.pi⁻¹ : ℝ) • Nᵀ
  have hHmK : ∀ x y, (Real.pi : ℂ) * (x ⬝ᵥ Hm *ᵥ star y) = K x y := by
    intro x y
    simp only [Hm, K, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul, Complex.ofReal_inv]
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  have hHerm : Hm.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [Hm, hNherm]
  have hint : ∀ l m : Λ, ∃ n : ℤ, ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = n := by
    intro l m
    obtain ⟨n, hn⟩ := hskew l m
    rw [hBF, hBF, hAsym m l, hKherm l m] at hn
    have him := congrArg Complex.im hn
    simp [Complex.mul_im] at him
    have h1 : Real.pi * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (m : Fin g → ℂ)).im = (K l m).im := by
      rw [← hHmK]; simp
    refine ⟨-n, ?_⟩
    push_cast
    apply mul_left_cancel₀ Real.pi_pos.ne'
    rw [h1]; linarith
  choose e he using hint
  have headd1 : ∀ l l' m, e (l + l') m = e l m + e l' m := by
    intro l l' m
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← he, ← he, ← he]
    simp only [Submodule.coe_add, add_dotProduct, Complex.add_im]
  have headd2 : ∀ l m m', e l (m + m') = e l m + e l m' := by
    intro l m m'
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [← he, ← he, ← he]
    simp only [Submodule.coe_add, star_add, mulVec_add, dotProduct_add, Complex.add_im]
  let Ef : LinearMap.BilinForm ℤ Λ := LinearMap.mk₂ ℤ e headd1
    (fun c l m => map_zsmul (AddMonoidHom.mk' (fun l => e l m) (fun l l' => headd1 l l' m)) c l)
    headd2
    (fun c l m => map_zsmul (AddMonoidHom.mk' (fun m => e l m) (fun m m' => headd2 l m m')) c m)
  have ha0 : a 0 = 1 := by
    have h := hcoc 0 0
    rw [add_zero, map_zero, LinearMap.zero_apply, Complex.exp_zero, mul_one] at h
    exact mul_left_cancel₀ (ha 0) (h.symm.trans (mul_one (a 0)).symm)
  let φ0 : Λ →+ ℝ :=
    { toFun := fun l => Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2
      map_zero' := by simp [ha0, A, K]
      map_add' := fun l m => by
        rw [hcoc, norm_mul, norm_mul, Complex.norm_exp,
          Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m)))
            (Real.exp_pos _).ne',
          Real.log_mul (norm_ne_zero_iff.mpr (ha l)) (norm_ne_zero_iff.mpr (ha m)), Real.log_exp,
          Submodule.coe_add, hAadd, hKadd, hBF, hKherm (l : Fin g → ℂ) m]
        simp only [Complex.add_re, Complex.conj_re]
        ring }
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.AppellHumbert.exists_real_extension Λ hΛ φ0
  let c : Fin g → ℂ := fun j => (φ (Pi.single j 1) : ℂ) - I * φ (Pi.single j I)
  have hc : ∀ u, (c ⬝ᵥ u).re = φ u := by
    intro u
    conv_rhs => rw [_root_.GlobalTheory.AppellHumbert.eq_sum_re_im u]
    simp only [map_sum, map_add, map_smul, smul_eq_mul, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [c, Complex.mul_re]
    ring
  let χ : Λ → ℂ := fun l => a l * cexp (-(A l l) / 2 - K l l / 2) * cexp (-(c ⬝ᵥ (l : Fin g → ℂ)))
  have hχ : ∀ l, ‖χ l‖ = 1 := by
    intro l
    have h1 : (c ⬝ᵥ (l : Fin g → ℂ)).re = Real.log ‖a l‖ - (A l l).re / 2 - (K l l).re / 2 := by
      rw [hc, hφ]; rfl
    simp only [χ, norm_mul, Complex.norm_exp, Complex.neg_re, Complex.sub_re, Complex.div_ofNat_re,
      h1, mul_assoc, ← Real.exp_add]
    rw [show -(A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2 +
        -(Real.log ‖a l‖ - (A ↑l ↑l).re / 2 - (K ↑l ↑l).re / 2) = -Real.log ‖a l‖ by ring,
      Real.exp_neg, Real.exp_log (norm_pos_iff.mpr (ha l))]
    exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr (ha l))
  let Q : (Fin g → ℂ) → ℂ := fun z => A z z / 2 + c ⬝ᵥ z
  refine ⟨Hm, χ, Ef, Q, hHerm, hχ, fun l m => (he l m).symm, ?_, by simp [Q, A], ?_⟩
  · simp only [Q, A, dotProduct, mulVec]
    fun_prop
  · intro l z
    have hQ : Q z - Q (z + l) = -A l z - A l l / 2 - c ⬝ᵥ l := by
      simp only [Q, dotProduct_add]
      rw [hAadd, hAsym z l]; ring
    have h2 : (Real.pi : ℂ) / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm *ᵥ star (l : Fin g → ℂ)) = K l l / 2 := by
      rw [← hHmK]; ring
    rw [hHmK, h2, mul_assoc, ← Complex.exp_add, hBF, hQ]
    simp only [χ]
    rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring
end _root_.GlobalTheory
end GlobalTheory
