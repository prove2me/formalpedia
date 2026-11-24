-- Prove2me | solution 1 for GlobalTheory.sum_log_gramDet_ratio_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:05.617965+00:00
-- url     : https://prove2.me/submissions/12153134-4bb3-467b-85f5-a0d90ce0cbf1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetRePosIffInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : (∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (A B : Matrix m n ℂ), ‖(Aᴴ * B).det‖ ^ 2 ≤ (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ∧ ((Aᴴ * B).det ≠ 0 → (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ≤ ‖(Aᴴ * B).det‖ ^ 2 → ∃ C : Matrix n n ℂ, B = A * C)) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, 0 < (((a * M)ᴴ * (a * M)).det.re)) ∧ 0 < ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) := by
  intro hCS r S hS hirr i hi0 hir M hM
  have hG0 : ∀ X : Matrix (Fin r) (Fin i) ℂ, 0 ≤ (Xᴴ * X).det.re ∧ (Xᴴ * X).det.im = 0 := by
    intro X
    have h := Complex.le_def.mp (posSemidef_conjTranspose_mul_self X).det_nonneg
    exact ⟨by simpa using h.1, by simpa using h.2.symm⟩
  have hnorm : ∀ X : Matrix (Fin r) (Fin i) ℂ, ‖(Xᴴ * X).det‖ = (Xᴴ * X).det.re := by
    intro X
    have h : (Xᴴ * X).det = (((Xᴴ * X).det.re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [(hG0 X).2])
    rw [h, Complex.norm_real, Real.norm_of_nonneg (by simpa using (hG0 X).1)]
    simp
  have hunit : ∀ a ∈ S, IsUnit a.det := fun a ha => isUnit_iff_ne_zero.mpr (hS a ha).2.1
  have hmul : ∀ a ∈ S, (a * M)ᴴ * (a⁻¹ * M) = Mᴴ * M := by
    intro a ha
    rw [conjTranspose_mul, (hS a ha).1.eq, Matrix.mul_assoc, ← Matrix.mul_assoc a,
      mul_nonsing_inv _ (hunit a ha), Matrix.one_mul]
  have hpair : ∀ a ∈ S, ((Mᴴ * M).det.re) ^ 2 ≤
      ((a * M)ᴴ * (a * M)).det.re * ((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re := by
    intro a ha
    have h := (hCS (Fin r) (Fin i) (a * M) (a⁻¹ * M)).1
    rwa [hmul a ha, hnorm] at h
  have hMsq : 0 < ((Mᴴ * M).det.re) ^ 2 := pow_pos hM 2
  have hpos : ∀ a ∈ S, 0 < ((a * M)ᴴ * (a * M)).det.re := by
    intro a ha
    refine lt_of_le_of_ne (hG0 _).1 fun h => ?_
    have h' := hpair a ha
    rw [← h, zero_mul] at h'
    linarith
  refine ⟨hpos, ?_⟩
  have hinvinv : ∀ a ∈ S, a⁻¹⁻¹ = a := fun a ha => nonsing_inv_nonsing_inv a (hunit a ha)
  have hsum_inv : ∑ a ∈ S, Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) =
      ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) :=
    Finset.sum_nbij' (·⁻¹) (·⁻¹) (fun a ha => (hS a ha).2.2) (fun a ha => (hS a ha).2.2)
      (fun a ha => hinvinv a ha) (fun a ha => hinvinv a ha) (fun a _ => rfl)
  have hterm : ∀ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) =
      Real.log (((a * M)ᴴ * (a * M)).det.re * ((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re /
        ((Mᴴ * M).det.re) ^ 2) := by
    intro a ha
    rw [← Real.log_mul (div_pos (hpos a ha) hM).ne' (div_pos (hpos _ (hS a ha).2.2) hM).ne']
    congr 1
    field_simp
  have hnonneg : ∀ a ∈ S, 0 ≤ Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) := by
    intro a ha
    rw [hterm a ha]
    exact Real.log_nonneg ((one_le_div hMsq).mpr (hpair a ha))
  have hstrict : ∃ a ∈ S, 0 < Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re)) := by
    by_contra hcon
    push_neg at hcon
    have hle : ∀ a ∈ S, ((a * M)ᴴ * (a * M)).det.re * ((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re ≤
        ((Mᴴ * M).det.re) ^ 2 := by
      intro a ha
      refine (div_le_one hMsq).mp (not_lt.mp fun h => ?_)
      have h' := hcon a ha
      rw [hterm a ha] at h'
      exact absurd h' (not_le.mpr (Real.log_pos h))
    have hdet : (Mᴴ * M).det ≠ 0 := by
      intro h
      rw [h] at hM
      simp at hM
    have hcol : ∀ a ∈ S, ∃ C : Matrix (Fin i) (Fin i) ℂ, a * a * M = M * C := by
      intro a ha
      have ha' := (hS a ha).2.2
      have h := (hCS (Fin r) (Fin i) (a⁻¹ * M) (a⁻¹⁻¹ * M)).2
      rw [hmul _ ha', hnorm] at h
      obtain ⟨C, hC⟩ := h hdet (hle _ ha')
      rw [hinvinv a ha] at hC
      refine ⟨C, ?_⟩
      rw [Matrix.mul_assoc, hC, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        mul_nonsing_inv _ (hunit a ha), Matrix.one_mul]
    have hW : ∀ a ∈ S, ∀ v ∈ LinearMap.range (Matrix.mulVecLin M), (a * a).mulVec v ∈
        LinearMap.range (Matrix.mulVecLin M) := by
      rintro a ha v ⟨w, rfl⟩
      obtain ⟨C, hC⟩ := hcol a ha
      refine ⟨C *ᵥ w, ?_⟩
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hC]
    rcases hirr _ hW with h | h
    · have hM0 : M = 0 := by
        ext x l
        have h2 := congrArg (fun f => f (Pi.single l 1) x) (LinearMap.range_eq_bot.mp h)
        simpa [Matrix.mulVecLin_apply] using h2
      haveI : Nonempty (Fin i) := ⟨⟨0, hi0⟩⟩
      rw [hM0] at hM
      simp at hM
    · have h1 := LinearMap.finrank_range_le (Matrix.mulVecLin M)
      rw [h, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at h1
      omega
  have htot : 0 < ∑ a ∈ S, (Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) +
      Real.log ((((a⁻¹ * M)ᴴ * (a⁻¹ * M)).det.re) / (((M)ᴴ * (M)).det.re))) :=
    Finset.sum_pos' hnonneg hstrict
  rw [Finset.sum_add_distrib, hsum_inv] at htot
  linarith
end _root_.GlobalTheory
end GlobalTheory
