-- Prove2me | solution 1 for GlobalTheory.MatSqrtNearOne.exists_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:46:33.412028+00:00
-- url     : https://prove2.me/submissions/d8c107c5-f90e-48e2-840d-18aef692d7d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMatrixSqrtNearOneUltrametric
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_commute_iter
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_norm_iter_diff_le
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_tau_add
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_tau_sub
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_tau_mul
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_tau_one
import Theorems.Thm_GlobalTheory_MatSqrtNearOne_tau_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open GlobalTheory GlobalTheory.MatSqrtNearOne
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] {n : ℕ}
namespace GlobalTheory.MatSqrtNearOne
theorem _root_.solution [CompleteSpace K] [CharZero K] (σ : K →+* K) (hσ : Continuous σ)
    (s : Matrix (Fin n) (Fin n) K)
    (hs : ∀ i j, ‖s i j - (1 : Matrix (Fin n) (Fin n) K) i j‖ < ‖(4 : K)‖) :
    ∃ r : Matrix (Fin n) (Fin n) K, r * r = s ∧ (∀ a : Matrix (Fin n) (Fin n) K,
      a * s = s * a → a * r = r * a) ∧ ((s.map σ)ᵀ = s → (r.map σ)ᵀ = r) := by
  have h4 : (4 : K) ≠ 0 := by norm_num
  have h4p : 0 < ‖(4 : K)‖ := norm_pos_iff.2 h4
  set u : Matrix (Fin n) (Fin n) K := (4 : K)⁻¹ • (s - 1) with hu
  have hs1 : ‖s - 1‖ < ‖(4 : K)‖ := (Matrix.norm_lt_iff h4p).2 fun i j => by simpa using hs i j
  have hc : ‖u‖ < 1 := by
    rw [hu, norm_smul, norm_inv, inv_mul_lt_iff₀ h4p, mul_one]
    exact hs1
  have hcs : CauchySeq (iter u) := cauchySeq_of_le_geometric ‖u‖ ‖u‖ hc fun k => by
    rw [dist_eq_norm, norm_sub_rev]; exact norm_iter_diff_le hc k
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcs
  have hfix : y + y * y = u := by
    have h1 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 y) := hy.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun k => iter u (k + 1)) atTop (𝓝 (u - y * y)) :=
      tendsto_const_nhds.sub (hy.mul hy)
    exact eq_sub_iff_add_eq.1 (tendsto_nhds_unique h1 h2)
  refine ⟨1 + (2 : K) • y, ?_, ?_, ?_⟩
  · calc (1 + (2 : K) • y) * (1 + (2 : K) • y) = 1 + (4 : K) • (y + y * y) := by
          rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, smul_mul_smul_comm]
          module
      _ = s := by rw [hfix, hu, smul_inv_smul₀ h4]; abel
  · intro a ha
    have hau : Commute a u := ((Commute.sub_right ha (Commute.one_right a))).smul_right _
    have hay : a * y = y * a :=
      tendsto_nhds_unique (hy.const_mul a)
        ((hy.mul_const a).congr fun k => (commute_iter hau k).eq.symm)
    exact ((Commute.one_right a).add_right ((show Commute a y from hay).smul_right (2 : K))).eq
  · intro hsσ
    have hτu : (u.map σ)ᵀ = u := by
      rw [hu, tau_smul, tau_sub, tau_one, hsσ, map_inv₀, map_ofNat]
    have hτiter : ∀ k, ((iter u k).map σ)ᵀ = iter u k := by
      intro k
      induction k with
      | zero => ext i j; simp [iter]
      | succ k ih =>
        show ((u - iter u k * iter u k).map σ)ᵀ = u - iter u k * iter u k
        rw [tau_sub, tau_mul, ih, hτu]
    have hτc : Continuous fun M : Matrix (Fin n) (Fin n) K => (M.map σ)ᵀ :=
      (continuous_id.matrix_map hσ).matrix_transpose
    have hτy : (y.map σ)ᵀ = y :=
      tendsto_nhds_unique ((hτc.tendsto y).comp hy) (hy.congr fun k => (hτiter k).symm)
    rw [tau_add, tau_one, tau_smul, hτy, map_ofNat]
end GlobalTheory.MatSqrtNearOne
