-- Prove2me | solution 1 for GlobalTheory.UnitaryOrbitForm.eq_smul_of_norm_eq_one_on_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:26:02.463992+00:00
-- url     : https://prove2.me/submissions/9d3a9a69-dac7-42cb-b1b8-4c87a691cc55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfEventuallyDotProductStarEqZero
import Theorems.Thm_GlobalTheory_UnitaryOrbitForm_eq_zero_of_eventually_dotProduct_star_eq_zero
import Theorems.Thm_GlobalTheory_UnitaryOrbitForm_dotProduct_star_eq_re
import Theorems.Thm_GlobalTheory_UnitaryOrbitForm_exists_unitary_mulVec_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}
private lemma dotProduct_mulVec_star_real_smul (C : Matrix (Fin r) (Fin r) ℂ) (a : ℝ) (x : Fin r → ℂ) :
    ((a : ℂ) • x) ⬝ᵥ C *ᵥ star ((a : ℂ) • x) = ((a ^ 2 : ℝ) : ℂ) * (x ⬝ᵥ C *ᵥ star x) := by
  simp only [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring
end GlobalTheory.UnitaryOrbitForm
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}
namespace GlobalTheory.UnitaryOrbitForm
theorem _root_.solution :
    ∀ (r : ℕ) (A B : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ), A.IsHermitian → B.IsHermitian →
      B.det ≠ 0 → (∀ h : Matrix (Fin r) (Fin r) ℂ, hᵀ * B * h.map (starRingEnd ℂ) = B →
        ‖(h *ᵥ v) ⬝ᵥ (A *ᵥ star (h *ᵥ v))‖ = 1) → ∃ t : ℝ, t ≠ 0 ∧ A = (t : ℂ) • B := by
  intro r A B v hA hB hdet hh
  have hid : (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * B * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      B := by
    simp
  have hv : v ≠ 0 := by
    rintro rfl
    have := hh 1 hid
    simp at this
  have hAre := dotProduct_star_eq_re hA
  have hBre := dotProduct_star_eq_re hB

  have horb : ∀ w : Fin r → ℂ, w ≠ 0 → (w ⬝ᵥ B *ᵥ star w).re = (v ⬝ᵥ B *ᵥ star v).re →
      |(w ⬝ᵥ A *ᵥ star w).re| = 1 := by
    intro w hw hwv
    have hQ : w ⬝ᵥ B *ᵥ star w = v ⬝ᵥ B *ᵥ star v := by
      rw [hBre w, hBre v, hwv]
    obtain ⟨g, hg, rfl⟩ := exists_unitary_mulVec_eq hB hdet hv hw hQ
    have := hh g hg
    rwa [hAre (g *ᵥ v), Complex.norm_real, Real.norm_eq_abs] at this
  have hsr : |(v ⬝ᵥ A *ᵥ star v).re| = 1 := horb v hv rfl

  have hcr : (v ⬝ᵥ B *ᵥ star v).re ≠ 0 := by
    intro h0
    have e := horb (((2 : ℝ) : ℂ) • v) (smul_ne_zero (by norm_num) hv)
      (by rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, h0, mul_zero])
    rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, abs_mul, hsr] at e
    norm_num at e
  set cr := (v ⬝ᵥ B *ᵥ star v).re with hcr_def
  set sr := (v ⬝ᵥ A *ᵥ star v).re with hsr_def
  have hcont : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      Continuous fun w : Fin r → ℂ => (w ⬝ᵥ M *ᵥ star w).re := fun M =>
    Complex.continuous_re.comp
      (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star))

  have hφ : Filter.Tendsto (fun w : Fin r → ℂ =>
      (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) (𝓝 v) (𝓝 sr) := by
    have h : ContinuousAt (fun w : Fin r → ℂ =>
        (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) v :=
      ((hcont A).continuousAt.mul (continuousAt_const (y := cr))).div (hcont B).continuousAt hcr
    have h2 : Filter.Tendsto (fun w : Fin r → ℂ =>
        (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re) (𝓝 v) (𝓝 (sr * cr / cr)) := h.tendsto
    have hval : sr * cr / cr = sr := by field_simp
    rwa [hval] at h2
  have E1 : ∀ᶠ w in 𝓝 v, w ≠ 0 := eventually_ne_nhds hv
  have E2 : ∀ᶠ w in 𝓝 v, 0 < (w ⬝ᵥ B *ᵥ star w).re * cr :=
    continuousAt_const.eventually_lt ((hcont B).continuousAt.mul continuousAt_const)
      (mul_self_pos.mpr hcr)
  have E3 := hφ.eventually (Ioo_mem_nhds (show sr - 1 < sr by linarith) (show sr < sr + 1 by linarith))
  have key : ∀ᶠ w in 𝓝 v, w ⬝ᵥ (A - ((sr / cr : ℝ) : ℂ) • B) *ᵥ star w = 0 := by
    filter_upwards [E1, E2, E3] with w hw hpos hI
    obtain ⟨hI1, hI2⟩ := hI
    have hqB : (w ⬝ᵥ B *ᵥ star w).re ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hq : 0 < cr / (w ⬝ᵥ B *ᵥ star w).re := by
      rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact div_pos h2 h1
      · exact div_pos_of_neg_of_neg h2 h1
    have ha2 : Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) ^ 2 = cr / (w ⬝ᵥ B *ᵥ star w).re :=
      Real.sq_sqrt hq.le
    have ha : Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) ≠ 0 := (Real.sqrt_pos.mpr hq).ne'

    have e := horb ((Real.sqrt (cr / (w ⬝ᵥ B *ᵥ star w).re) : ℂ) • w)
      (smul_ne_zero (Complex.ofReal_ne_zero.mpr ha) hw)
      (by rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, ha2]; field_simp)
    rw [dotProduct_mulVec_star_real_smul, Complex.re_ofReal_mul, ha2] at e
    have e' : |(w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re| = 1 := by
      rw [← e]
      congr 1
      ring
    have hφw : (w ⬝ᵥ A *ᵥ star w).re * cr / (w ⬝ᵥ B *ᵥ star w).re = sr := by
      rcases (abs_eq zero_le_one).mp e' with h1 | h1 <;>
        rcases (abs_eq zero_le_one).mp hsr with h2 | h2 <;> linarith [hI1, hI2]
    have hreal : (w ⬝ᵥ A *ᵥ star w).re - sr / cr * (w ⬝ᵥ B *ᵥ star w).re = 0 := by
      have h := hφw
      field_simp at h ⊢
      linear_combination h
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul, hAre w, hBre w,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub, hreal, Complex.ofReal_zero]
  have hC := eq_zero_of_eventually_dotProduct_star_eq_zero key
  refine ⟨sr / cr, div_ne_zero ?_ hcr, sub_eq_zero.mp hC⟩
  intro h0
  rw [h0, abs_zero] at hsr
  exact zero_ne_one hsr
end GlobalTheory.UnitaryOrbitForm
