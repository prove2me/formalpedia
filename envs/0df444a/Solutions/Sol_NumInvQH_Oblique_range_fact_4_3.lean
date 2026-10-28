-- Prove2me | solution 1 for NumInvQH.Oblique.range_fact_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:41:08.353982+00:00
-- url     : https://prove2.me/submissions/8104a6eb-5265-4107-b990-607e5172d70e

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
import Definitions.Def_NumInvQH_Oblique_Basic

open Matrix

open NumInvQH.Oblique in
theorem solution {d : ℕ}
    (C : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) (γ : ℝ)
    (hJoint : (Matrix.fromBlocks C (Matrix.of (fun i (_ : Fin 1) => u i))
      (Matrix.of (fun (_ : Fin 1) j => u j))
      (Matrix.of (fun (_ _ : Fin 1) => γ))).PosSemidef) :
    u ∈ LinearMap.range (Matrix.toLin' C) := by
  have hpsd := Matrix.posSemidef_iff_dotProduct_mulVec.mp hJoint
  have hC : C.IsHermitian := (Matrix.isHermitian_fromBlocks_iff.mp hpsd.1).1
  -- u is orthogonal to ker C
  have horth : ∀ v : Fin d → ℝ, C *ᵥ v = 0 → u ⬝ᵥ v = 0 := by
    intro v hv
    have key : ∀ t : ℝ, 0 ≤ 2 * t * (u ⬝ᵥ v) + γ := by
      intro t
      have h := hpsd.2 (Sum.elim (t • v) (fun _ => 1))
      rw [star_trivial, fromBlocks_mulVec, sumElim_dotProduct_sumElim] at h
      have e1 : (Sum.elim (t • v) (fun _ : Fin 1 => (1 : ℝ)) ∘ Sum.inl) = t • v := rfl
      have e2 : (Sum.elim (t • v) (fun _ : Fin 1 => (1 : ℝ)) ∘ Sum.inr) = fun _ => 1 := rfl
      rw [e1, e2, mulVec_smul, hv, smul_zero, zero_add] at h
      have h3 : (Matrix.of (fun i (_ : Fin 1) => u i)) *ᵥ (fun _ => (1 : ℝ)) = u := by
        funext i; simp [mulVec, dotProduct]
      have h4 : ((Matrix.of (fun (_ : Fin 1) j => u j)) *ᵥ (t • v) +
          (Matrix.of (fun (_ _ : Fin 1) => γ)) *ᵥ (fun _ => (1 : ℝ))) =
          fun _ => t * (u ⬝ᵥ v) + γ := by
        funext i
        simp [mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring
      rw [h3, h4] at h
      have h5 : (t • v) ⬝ᵥ u = t * (u ⬝ᵥ v) := by
        rw [smul_dotProduct, dotProduct_comm, smul_eq_mul]
      rw [h5] at h
      have h6 : (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ (fun _ => t * (u ⬝ᵥ v) + γ) =
          t * (u ⬝ᵥ v) + γ := by simp [dotProduct]
      rw [h6] at h
      linarith
    by_contra hne
    have := key (-(γ + 1) / (2 * (u ⬝ᵥ v)))
    have e : 2 * (-(γ + 1) / (2 * (u ⬝ᵥ v))) * (u ⬝ᵥ v) = -(γ + 1) := by
      field_simp
    linarith
  -- transport to Euclidean space
  set T := Matrix.toEuclideanLin C with hT
  have hsymm : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hC
  have hmem : (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d)) ∈ (LinearMap.ker T)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [LinearMap.mem_ker] at hw
    have hw' : C *ᵥ (WithLp.ofLp w) = 0 := by
      have := congrArg WithLp.ofLp hw
      simpa [hT] using this
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    simpa using horth _ hw'
  rw [← hsymm.orthogonal_range, Submodule.orthogonal_orthogonal] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨WithLp.ofLp w, ?_⟩
  have := congrArg WithLp.ofLp hw
  simpa [hT] using this
