-- Prove2me | solution 1 for MasulloGRH.weakDual_polar_isCompact_of_nhds
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:39:06.481565+00:00
-- url     : https://prove2.me/submissions/a82a05b0-0998-4254-b573-108aa394221c

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex

open Set Filter Topology Bornology MasulloGRH
open scoped Pointwise


theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (V : Set E) (hV : V ∈ 𝓝 (0:E)) : IsCompact (WeakDual.polar ℂ V) := by
  classical
  let K := {f : E → ℂ | (∀ x y, f (x+y) = f x + f y) ∧
    (∀ (c:ℂ) x, f (c • x) = c • f x) ∧ ∀ x ∈ V, ‖f x‖ ≤ 1}
  have hKc : IsClosed K := by
    dsimp [K]
    simp only [ofPred_and, ofPred_forall]
    refine (isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ ?_).inter
      ((isClosed_iInter fun c => isClosed_iInter fun x => isClosed_eq ?_ ?_).inter
        (isClosed_biInter fun x _ => isClosed_le (continuous_apply x).norm continuous_const)) <;>
      fun_prop
  have hbound (x:E) : ∃ r : ℝ, ∀ f ∈ K, ‖f x‖ ≤ r := by
    obtain ⟨c,hc⟩ := ((absorbent_nhds_zero (𝕜:=ℂ) hV) x).exists
    obtain ⟨y,hy,hxy⟩ := hc (mem_singleton _)
    refine ⟨‖c‖, fun f hf => ?_⟩
    change c • y = x at hxy
    rw [← hxy, hf.2.1, norm_smul]
    simpa using mul_le_mul_of_nonneg_left (hf.2.2 y hy) (norm_nonneg c)
  choose r hr using hbound
  have hK : IsCompact K :=
    (isCompact_univ_pi fun x : E => isCompact_closedBall (0:ℂ) (r x)).of_isClosed_subset hKc
      (fun f hf x _ => mem_closedBall_zero_iff.mpr (hr x f hf))
  have he : Topology.IsEmbedding (fun (f:WeakDual ℂ E) => (f : E → ℂ)) :=
    WeakBilin.isEmbedding ContinuousLinearMap.coe_injective
  apply he.isInducing.isCompact_iff.mpr
  have him : (fun (f:WeakDual ℂ E) => (f:E → ℂ)) '' WeakDual.polar ℂ V = K := by
    ext g
    constructor
    · rintro ⟨f,hf,rfl⟩
      exact ⟨f.map_add, fun c x => f.map_smul c x, hf⟩
    · intro hg
      let L : E →ₗ[ℂ] ℂ := ⟨⟨g,hg.1⟩,hg.2.1⟩
      have hp : Continuous L.toSeminorm := by
        apply Seminorm.continuous (r:=2)
        apply mem_of_superset hV
        intro x hx
        rw [Seminorm.mem_ball_zero]
        exact (hg.2.2 x hx).trans_lt (by norm_num)
      have hL : Continuous L := by
        apply continuous_of_continuousAt_zero L
        rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
        simpa only [map_zero, LinearMap.coe_toSeminorm] using (hp.continuousAt (x:=0)).tendsto
      exact ⟨StrongDual.toWeakDual (⟨L,hL⟩ : StrongDual ℂ E), hg.2.2, rfl⟩
  simpa [him] using hK

