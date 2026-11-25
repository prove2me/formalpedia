-- Prove2me | solution 1 for GlobalTheory.ThetaPositivity.eq_zero_of_mulVec_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:25:53.685309+00:00
-- url     : https://prove2.me/submissions/a460aafa-9a34-4e38-bd7d-4c68c0cdb1d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ReFormPosOfThetaNeZero

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
open GlobalTheory GlobalTheory.ThetaPositivity
variable {g : ℕ}
namespace GlobalTheory.ThetaPositivity
theorem _root_.solution (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {Hm : Matrix (Fin g) (Fin g) ℂ} (Ef : LinearMap.BilinForm ℤ Λ)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) =
      ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hinj : Function.Injective Ef) {w : Fin g → ℂ} (hw : Hm.mulVec (star w) = 0) : w = 0 := by
  classical
  have := ZLattice.module_free ℝ Λ
  have := ZLattice.module_finite ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  let B := b.ofZLatticeBasis ℝ Λ
  have hdet : (LinearMap.toMatrix₂ b b Ef).det ≠ 0 :=
    (LinearMap.separatingLeft_iff_det_ne_zero b).mp
      (LinearMap.separatingLeft_iff_ker_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hinj))
  let M := (LinearMap.toMatrix₂ b b Ef).map (Int.castRingHom ℝ)
  have hM : M.det ≠ 0 := by
    have h := (Int.castRingHom ℝ).map_det (LinearMap.toMatrix₂ b b Ef)
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    simpa using hdet
  have hsum : ∑ j, B.repr w j • (b j : Fin g → ℂ) = w := by
    conv_rhs => rw [← B.sum_repr w]
    simp [B]
  have hv : M.mulVec (B.repr w) = 0 := by
    funext i
    have h : ((b i : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star w)).im = 0 := by simp [hw]
    rw [← hsum, star_sum, mulVec_sum, dotProduct_sum, im_sum] at h
    rw [Pi.zero_apply, ← h]
    simp only [mulVec, M]
    change ∑ j, _ = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_smul, star_trivial]
    change _ = ((b i : Fin g → ℂ) ⬝ᵥ Hm.mulVec (B.repr w j • star (b j : Fin g → ℂ))).im
    rw [mulVec_smul, dotProduct_smul, smul_im, ← hE]
    simp [mul_comm]
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hM hv
  rw [← hsum, h0]
  simp
end GlobalTheory.ThetaPositivity
