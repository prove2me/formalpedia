-- Prove2me | solution 1 for GlobalTheory.PointStepCompare.sum_pos_of_tensor_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:34.119626+00:00
-- url     : https://prove2.me/submissions/9a4de1ce-8add-4df4-8d75-78bb38a69d86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumPosOfTensorPos
import Theorems.Thm_GlobalTheory_PointStepCompare_evalOn_tensorCoord
import Theorems.Thm_GlobalTheory_PointStepCompare_posSemidef_of_int
import Theorems.Thm_GlobalTheory_PointStepCompare_posDef_of_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PointStepCompare
open NumberField Matrix
open scoped MatrixOrder
namespace GlobalTheory.PointStepCompare
theorem _root_.solution : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (ι : Type) [Fintype ι] (a c : ι → Y), (∀ f g : Y →ₗ[ℤ] ℤ, ∑ i, f (a i) * g (c i) = ∑ i, g (a i) * f (c i)) → (∀ f : Y →ₗ[ℤ] ℤ, f ≠ 0 → 0 < ∑ i, f (a i) * f (c i)) → ∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ x y, γ x y = γ y x) → (∀ x, 0 ≤ γ x x) → γ ≠ 0 → 0 < ∑ i, γ (a i) (c i) := by
  intro Y _ _ _ ι _ a c hs hp γ hγ h0 hne
  classical
  let b := Module.finBasis ℤ Y
  let M : Matrix _ _ ℤ := Matrix.of fun p q => ∑ i, b.coord p (a i) * b.coord q (c i)
  have hM := (posDef_of_int M (fun p q => hs _ _) fun x hx => by
    have := hp (∑ p, x p • b.coord p) fun h => hx (funext fun q => by
      simpa [Finsupp.single_apply] using LinearMap.congr_fun h (b q))
    convert this using 1
    simp only [dotProduct, mulVec, M, Matrix.of_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    ring).2
  let G : Matrix _ _ ℝ := Matrix.of fun p q => γ (b p) (b q)
  have hG : G.PosSemidef := posSemidef_of_int (by ext p q; simp [G, hγ (b p) (b q)]) fun x => by
    convert h0 (∑ p, x p • b p) using 1
    simp only [dotProduct, mulVec, G, Matrix.of_apply, map_sum, map_zsmul, LinearMap.sum_apply,
      LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]; ring
  have htr : ∑ i, γ (a i) (c i) = (M.map (Int.cast : ℤ → ℝ) * G).trace := by
    simp only [← evalOn_tensorCoord b γ]
    change ∑ i, ∑ p : _ × _, ((b.repr (a i) p.1 * b.repr (c i) p.2 : ℤ) : ℝ) * γ (b p.1) (b p.2) = _
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, M, G, Matrix.of_apply,
      Int.cast_sum, Finset.sum_mul, Module.Basis.coord_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  have hCd : IsUnit C.det := by
    refine Ne.isUnit fun h => hM.det_pos.ne' ?_
    rw [hC, det_mul, h, mul_zero]
  have h1 := hG.mul_mul_conjTranspose_same C
  have h2 : (C * G * Cᴴ).trace = ∑ i, γ (a i) (c i) := by
    rw [htr, hC, trace_mul_cycle, star_eq_conjTranspose]
  rw [← h2]
  refine lt_of_le_of_ne h1.trace_nonneg fun h => hne ?_
  have h3 := h1.trace_eq_zero_iff.1 h.symm
  have hu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 hCd
  have h4 : G = 0 := by
    rwa [← star_eq_conjTranspose, hu.star.mul_left_eq_zero, hu.mul_right_eq_zero] at h3
  exact b.ext fun p => b.ext fun q => congrFun (congrFun h4 p) q
end GlobalTheory.PointStepCompare
