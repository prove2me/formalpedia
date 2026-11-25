-- Prove2me | solution 1 for GlobalTheory.ClassFin.HarmMin.sum_log_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:36:41.490044+00:00
-- url     : https://prove2.me/submissions/2e334704-02de-4c66-be6d-aadea55d94b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MulLogEqNegLogMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsHermitianLogOfPosDefGramStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SumHermitianLogGramEqZeroOfEnergyMinimum
import Theorems.Thm_GlobalTheory_ClassFin_HarmMin_log_herm
import Theorems.Thm_GlobalTheory_ClassFin_HarmMin_log_comm
import Theorems.Thm_GlobalTheory_ClassFin_HarmMin_exists_path
import Theorems.Thm_GlobalTheory_ClassFin_HarmMin_deriv_entry
import Theorems.Thm_GlobalTheory_ClassFin_HarmMin_deriv_phi
import Theorems.Thm_GlobalTheory_ClassFin_HarmMin_trace_id
import Theorems.Thm_GlobalTheory_T_exists_isHermitianLogOfPosDef_gram
import Theorems.Thm_GlobalTheory_T_hermitian_log_trace_sq_first_variation_bound
import Theorems.Thm_P2M_GlobalTheory_T_mul_log_eq_neg_log_mul__1ff42444a818


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin GlobalTheory.ClassFin.HarmMin
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ClassFin.HarmMin
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ) (g H : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → (∀ s, IsLog (H s) ((g s)ᴴ * g s)) → (∀ (P' : Matrix ι ι ℂ) (H' : σ → Matrix ι ι ℂ), IsUnit P'.det → (∀ s, IsLog (H' s) ((P' * g s * P'⁻¹)ᴴ * (P' * g s * P'⁻¹))) → ∑ s, (Matrix.trace (H s * H s)).re ≤ ∑ s, (Matrix.trace (H' s * H' s)).re) → ∑ s, H s = 0 := by
  intro ι _ _ σ _ τ g H hτ hH hmin
  set X := ∑ s, H s with hXdef
  have hX : Xᴴ = X := by
    rw [hXdef, conjTranspose_sum]; exact Finset.sum_congr rfl fun s _ => log_herm (hH s)
  obtain ⟨P, Q, hP0, hQ0, hPQ, hPh, hQh, hP, hQ⟩ := exists_path X hX
  choose C δ hδ hC using fun s => GlobalTheory.T.hermitian_log_trace_sq_first_variation_bound ι (H s) _ (hH s)
  let Y : σ → ℝ → Matrix ι ι ℂ := fun s t => Q t * (g s)ᴴ * P t * P t * g s * Q t - (g s)ᴴ * g s
  have hY0 : ∀ s, Y s 0 = 0 := fun s => by simp [Y, hP0, hQ0]
  have hY : ∀ s, HasDerivAt (Y s) (-X * ((g s)ᴴ * g s) + (g s)ᴴ * X * g s + (g s)ᴴ * X * g s
      - ((g s)ᴴ * g s) * X) 0 := by
    intro s
    have := (((((hQ.mul_const (g s)ᴴ).mul hP).mul hP).mul_const (g s)).mul hQ).sub_const ((g s)ᴴ * g s)
    refine HasDerivAt.congr_deriv this ?_
    simp only [Pi.mul_apply, hP0, hQ0]
    noncomm_ring
  have hinv : ∀ t, (P t)⁻¹ = Q t := fun t => Matrix.inv_eq_right_inv (hPQ t)
  have hPu : ∀ t, IsUnit (P t).det := fun t => Matrix.isUnit_det_of_right_inverse (hPQ t)
  have hQu : ∀ t, IsUnit (Q t).det := fun t => Matrix.isUnit_det_of_left_inverse (hPQ t)
  have hA : ∀ s t, (P t * g s * (P t)⁻¹)ᴴ * (P t * g s * (P t)⁻¹) = (g s)ᴴ * g s + Y s t := by
    intro s t
    simp only [hinv, Y, conjTranspose_mul, hPh, hQh, Matrix.mul_assoc]
    abel
  let φ : ℝ → ℝ := fun t => ∑ s, (2 * (Matrix.trace (H s * ((g s)ᴴ * g s)⁻¹ * Y s t)).re
    + C s * ∑ i, ∑ j, ‖Y s t i j‖ ^ 2)
  have hφ := HasDerivAt.fun_sum (u := Finset.univ) fun s _ =>
    deriv_phi (hY s) (hY0 s) (H s * ((g s)ᴴ * g s)⁻¹) (C s)
  have hloc : IsLocalMin φ 0 := by
    have hev : ∀ᶠ t in nhds (0 : ℝ), ∀ s i j, ‖Y s t i j‖ ≤ δ s := by
      simp only [Filter.eventually_all]
      intro s i j
      have hc := (deriv_entry (hY s) i j).continuousAt.norm
      refine hc.eventually (p := fun x => x ≤ δ s) ?_
      refine Filter.Eventually.mono (gt_mem_nhds (a := δ s) ?_) fun x hx => le_of_lt hx
      simp [hY0, hδ]
    filter_upwards [hev] with t ht
    have h0 : φ 0 = 0 := by simp [φ, hY0]
    have hu : ∀ s, IsUnit (P t * g s * (P t)⁻¹).det := fun s => by
      rw [hinv, det_mul, det_mul]
      exact ((hPu t).mul (Matrix.isUnit_det_of_left_inverse (hτ s))).mul (hQu t)
    choose H' hH' using fun s => GlobalTheory.T.exists_isHermitianLogOfPosDef_gram ι _ (hu s)
    have h1 := hmin (P t) H' (hPu t) hH'
    have h2 := Finset.sum_le_sum (s := Finset.univ) fun s _ => hC s (Y s t) (H' s) (ht s) (hA s t ▸ hH' s)
    simp only [add_assoc] at h2
    rw [Finset.sum_add_distrib] at h2
    rw [h0]
    show 0 ≤ ∑ s, _
    linarith
  have hz := hloc.hasDerivAt_eq_zero hφ
  have hid := fun s => trace_id (X := X) (hτ s) (log_comm (hH s))
    (GlobalTheory.T.mul_log_eq_neg_log_mul' ι (g s) (g (τ s)) (H s) (H (τ s)) (hH s) (hH (τ s)) (hτ s))
  simp only [hid] at hz
  have s1 : ∑ s, Matrix.trace (H s * X) = Matrix.trace (X * X) := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul]
  have s2 : ∑ s, Matrix.trace (H (τ s) * X) = Matrix.trace (X * X) := by
    rw [← s1]; exact Equiv.sum_comp τ fun s => Matrix.trace (H s * X)
  rw [← Finset.mul_sum, ← Complex.re_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    s1, s2] at hz
  have hre : (Matrix.trace (X * X)).re = 0 := by
    simp at hz
    linarith
  have hnn : 0 ≤ Matrix.trace (Xᴴ * X) := (Matrix.posSemidef_conjTranspose_mul_self X).trace_nonneg
  refine Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 ?_
  rw [hX] at hnn ⊢
  exact Complex.ext hre (Complex.le_def.1 hnn).2.symm
end GlobalTheory.ClassFin.HarmMin
