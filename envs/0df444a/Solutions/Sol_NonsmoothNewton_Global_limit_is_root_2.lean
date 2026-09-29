-- Prove2me | solution 2 for NonsmoothNewton.Global.limit_is_root
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:05:17.555448+00:00
-- url     : https://prove2.me/submissions/6d23fb92-6a9c-4040-b2b5-7a2430660137

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun

namespace NonsmoothNewton.Global

open Filter Topology

/-- Elements of the Clarke Jacobian at a point of an open set on which `F` is `K`-Lipschitz
have operator norm at most `K`. -/
theorem aux_lir_clarke_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (F : E → E) (U : Set E) (hUo : IsOpen U) (K : NNReal)
    (hlip : LipschitzOnWith K F U) (y : E) (hy : y ∈ U) (W : E →L[ℝ] E)
    (hW : W ∈ clarkeJac F y) : ‖W‖ ≤ K := by
  have hsub : bJac F y ⊆ Metric.closedBall (0 : E →L[ℝ] E) K := by
    rintro A ⟨u, hu, -, hA⟩
    rw [mem_closedBall_zero_iff]
    have h1 : ∀ᶠ i in atTop, u i ∈ U := hu (hUo.mem_nhds hy)
    have h2 : ∀ᶠ i in atTop, ‖fderiv ℝ F (u i)‖ ≤ K :=
      h1.mono fun i hi => norm_fderiv_le_of_lipschitzOn ℝ (hUo.mem_nhds hi) hlip
    exact le_of_tendsto hA.norm h2
  have := convexHull_min hsub (convex_closedBall (0 : E →L[ℝ] E) K) hW
  rwa [mem_closedBall_zero_iff] at this

end NonsmoothNewton.Global

open NonsmoothNewton.Global
open Filter Topology

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hF : LocallyLipschitz F)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hrun : IsNewtonRun F x V) (hS : ∀ k, x k ∈ Metric.closedBall x0 r)
    (xstar : EuclideanSpace ℝ (Fin n)) (hlim : Tendsto x atTop (𝓝 xstar)) :
    (∃ C : ℝ, ∀ k, ‖V k‖ ≤ C) ∧ xstar ∈ Metric.closedBall x0 r ∧ F xstar = 0 := by
  obtain ⟨K, t, ht, hlip⟩ := hF xstar
  have hU : interior t ∈ 𝓝 xstar := interior_mem_nhds.mpr ht
  have hlipU : LipschitzOnWith K F (interior t) := hlip.mono interior_subset
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim hU)
  have hbound : ∃ C : ℝ, ∀ k, ‖V k‖ ≤ C := by
    refine ⟨(K : ℝ) + ∑ k ∈ Finset.range N, ‖V k‖, fun k => ?_⟩
    have hsum : 0 ≤ ∑ k ∈ Finset.range N, ‖V k‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    rcases lt_or_ge k N with hk | hk
    · have : ‖V k‖ ≤ ∑ k ∈ Finset.range N, ‖V k‖ :=
        Finset.single_le_sum (f := fun k => ‖V k‖) (fun i _ => norm_nonneg _)
          (Finset.mem_range.2 hk)
      have hK : (0 : ℝ) ≤ K := K.coe_nonneg
      linarith
    · have := aux_lir_clarke_norm_le F (interior t) isOpen_interior K hlipU (x k) (hN k hk)
        (V k) (hrun k).1
      linarith
  refine ⟨hbound, Metric.isClosed_closedBall.mem_of_tendsto hlim (Eventually.of_forall hS), ?_⟩
  obtain ⟨C, hC⟩ := hbound
  have hstep : Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
    have := (hlim.comp (tendsto_add_atTop_nat 1)).sub hlim
    simpa using this
  have hFx0 : Tendsto (fun k => F (x k)) atTop (𝓝 0) := by
    have hC0 : Tendsto (fun k => C * ‖x (k + 1) - x k‖) atTop (𝓝 0) := by
      simpa using hstep.norm.const_mul C
    refine squeeze_zero_norm (fun k => ?_) hC0
    have h1 : F (x k) = -(V k (x (k + 1) - x k)) := by rw [(hrun k).2, neg_neg]
    rw [h1, norm_neg]
    exact (V k).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _))
  have hFx : Tendsto (fun k => F (x k)) atTop (𝓝 (F xstar)) :=
    (hF.continuous.tendsto xstar).comp hlim
  exact tendsto_nhds_unique hFx hFx0
