-- Prove2me | solution 1 for GeomDRSub.eq_60
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:14:18.220713+00:00
-- url     : https://prove2.me/submissions/94f66bf3-5528-458c-8756-8e07c57c34f7

import Mathlib
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj

namespace Aux_GeomDRSub_eq60

open scoped RealInnerProductSpace

theorem proj_le {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    {z p o : EuclideanSpace ℝ (Fin d)} (hp : OrabonaOL.OGD.IsEuclideanProj K z p) (ho : o ∈ K) :
    ‖p - o‖ ^ 2 ≤ ‖z - o‖ ^ 2 := by
  haveI : Nonempty K := ⟨⟨p, hp.1⟩⟩
  have hbdd : BddBelow (Set.range fun w : K => ‖z - (w : EuclideanSpace ℝ (Fin d))‖) :=
    ⟨0, Set.forall_mem_range.mpr fun w => norm_nonneg _⟩
  have hinf : ‖z - p‖ = ⨅ w : K, ‖z - (w : EuclideanSpace ℝ (Fin d))‖ := by
    apply le_antisymm
    · exact le_ciInf fun w => hp.2 w.1 w.2
    · exact ciInf_le hbdd (⟨p, hp.1⟩ : K)
  have hinner := (norm_eq_iInf_iff_real_inner_le_zero hK hp.1).mp hinf o ho
  have e : z - o = (z - p) + (p - o) := by abel
  rw [e, norm_add_sq_real]
  have : ⟪z - p, p - o⟫ = -⟪z - p, o - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [this]
  nlinarith [sq_nonneg ‖z - p‖]

end Aux_GeomDRSub_eq60

open scoped RealInnerProductSpace in
theorem solution {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : Convex ℝ K)
    (D : ℝ) (hD : ∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D) (η : ℝ) (hη : 0 < η) (T : ℕ)
    (ĝ x : ℕ → EuclideanSpace ℝ (Fin d)) (hx0 : x 0 ∈ K)
    (hupd : ∀ t < T, OrabonaOL.OGD.IsEuclideanProj K (x t + η • ĝ t) (x (t + 1)))
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ K) :
    ∑ t ∈ Finset.range T, inner ℝ (ĝ t) (o - x t) ≤
      D ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖ĝ t‖ ^ 2 := by
  have hstep : ∀ t ∈ Finset.range T, 2 * η * inner ℝ (ĝ t) (o - x t) ≤
      (‖x t - o‖ ^ 2 - ‖x (t + 1) - o‖ ^ 2) + η ^ 2 * ‖ĝ t‖ ^ 2 := by
    intro t ht
    have hp := Aux_GeomDRSub_eq60.proj_le hK (hupd t (Finset.mem_range.mp ht)) ho
    have e : x t + η • ĝ t - o = (x t - o) + η • ĝ t := by abel
    rw [e, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs] at hp
    have : inner ℝ (ĝ t) (o - x t) = -inner ℝ (x t - o) (ĝ t) := by
      rw [real_inner_comm, ← inner_neg_left, neg_sub]
    rw [this]
    nlinarith
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun t => ‖x t - o‖ ^ 2),
    ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have h0 : ‖x 0 - o‖ ^ 2 ≤ D ^ 2 := by
    have h1 := hD _ hx0 _ ho
    have h2 := norm_nonneg (x 0 - o)
    nlinarith
  have hT := sq_nonneg ‖x T - o‖
  have key : 2 * η * ∑ t ∈ Finset.range T, inner ℝ (ĝ t) (o - x t) ≤
      D ^ 2 + η ^ 2 * ∑ t ∈ Finset.range T, ‖ĝ t‖ ^ 2 := by linarith
  have e2 : D ^ 2 / (2 * η) + η / 2 * ∑ t ∈ Finset.range T, ‖ĝ t‖ ^ 2 =
      (D ^ 2 + η ^ 2 * ∑ t ∈ Finset.range T, ‖ĝ t‖ ^ 2) / (2 * η) := by
    field_simp
  rw [e2, le_div_iff₀ (by positivity)]
  linarith
