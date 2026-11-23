-- Prove2me | solution 1 for GlobalTheory.HermClass.det_ne_zero_and_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:41.402736+00:00
-- url     : https://prove2.me/submissions/47bfbf0b-746c-4aa8-bb4b-6f4c9a93bfbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MinkowskiLinearForms
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open MeasureTheory Module Submodule NumberField Matrix
namespace GlobalTheory.HermClass
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι ℚ)
    {M : ℤ} (hM : M ≠ 0)
    (h : ∀ x : ι → ℚ, (∀ j, ∃ m : ℤ, (x ᵥ* T) j = m) → ∀ i, ∃ m : ℤ, M * x i = m) :
    T.det ≠ 0 ∧ |T.det| ≤ |(M : ℚ)| ^ Fintype.card ι := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have h0 : T.det ≠ 0 := by
    intro hd
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx0
    have hi' : x i ≠ 0 := hi
    obtain ⟨m, hm⟩ := h ((2 * M * x i)⁻¹ • x) (fun j => ⟨0, by rw [Matrix.smul_vecMul, hx]; simp⟩) i
    have h2 : (2 * m : ℚ) = 1 := by
      rw [← hm]; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    have h3 : 2 * m = 1 := by exact_mod_cast h2
    omega
  refine ⟨h0, ?_⟩
  have hu : IsUnit T.det := isUnit_iff_ne_zero.2 h0
  have hK : ∀ k i, ∃ m : ℤ, M * T⁻¹ k i = m := fun k => h (T⁻¹ k) fun j => by
    have : (T⁻¹ k ᵥ* T) j = (T⁻¹ * T) k j := rfl
    rw [this, Matrix.nonsing_inv_mul T hu, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  choose K hK using hK
  have hKe : (Int.castRingHom ℚ).mapMatrix (Matrix.of K) = (M : ℚ) • T⁻¹ := by
    ext k i; simp [← hK]
  have hdet : (((Matrix.of K).det : ℤ) : ℚ) * T.det = (M : ℚ) ^ Fintype.card ι := by
    have := (Int.castRingHom ℚ).map_det (Matrix.of K)
    rw [hKe, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at this
    rw [← eq_intCast (Int.castRingHom ℚ), this]; field_simp
  have hK0 : (Matrix.of K).det ≠ 0 := by
    intro hz; rw [hz] at hdet
    exact pow_ne_zero _ hM' (by simpa using hdet.symm)
  have h1 : (1 : ℚ) ≤ |(((Matrix.of K).det : ℤ) : ℚ)| := by exact_mod_cast Int.one_le_abs hK0
  rw [← abs_pow, ← hdet, abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) h1
end GlobalTheory.HermClass
