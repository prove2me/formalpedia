-- Prove2me | solution 1 for MasulloGRH.weakStar_barrel_mem_nhds_strongDual
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:39:05.292431+00:00
-- url     : https://prove2.me/submissions/d6ac8517-ad76-4f6f-831e-f872fa4c75a9

import Mathlib
import Theorems.Thm_MasulloGRH_bounded_iff_weakly_bounded

open Set Filter Topology Bornology MasulloGRH
open scoped Pointwise


theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) (W : Set (WeakDual ℂ E))
    (hc : IsClosed W) (hb : Balanced ℂ W) (hv : Convex ℝ W) (ha : Absorbent ℂ W) :
    StrongDual.toWeakDual ⁻¹' W ∈ 𝓝 (0 : StrongDual ℂ E) := by
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := hE
  have hadd := hp.topologicalAddGroup
  have hsmul := hp.continuousSMul
  let A := {x : E | ∀ f ∈ W, ‖(f : WeakDual ℂ E) x‖ ≤ 1}
  have hA : IsVonNBounded ℂ A := by
    apply (bounded_iff_weakly_bounded E ⟨⟨ι, inferInstance, p, hp⟩,hT2⟩ A).mpr
    intro f
    obtain ⟨c, hc⟩ := (ha (StrongDual.toWeakDual f)).exists
    obtain ⟨g,hg,he⟩ := hc (mem_singleton _)
    rw [isBounded_iff_forall_norm_le]
    refine ⟨‖c‖, ?_⟩
    rintro _ ⟨x,hx,rfl⟩
    change ‖(StrongDual.toWeakDual f) x‖ ≤ _
    rw [← he]
    change ‖c * g x‖ ≤ ‖c‖
    simpa using mul_le_mul_of_nonneg_left (hx g hg) (norm_nonneg c)
  have hzero : 0 ∈ W := ha.zero_mem
  apply mem_of_superset (ContinuousLinearMap.hasBasis_nhds_zero.mem_of_mem
    (i := (A, Metric.ball (0 : ℂ) 1)) ⟨hA, Metric.ball_mem_nhds _ zero_lt_one⟩)
  intro f hf
  change StrongDual.toWeakDual f ∈ W
  by_contra h
  have tower : IsScalarTower ℝ ℂ (WeakDual ℂ E) := ⟨fun a b f => by apply DFunLike.ext; intro x; exact smul_assoc a b (f x)⟩
  have hlcs : LocallyConvexSpace ℝ (WeakDual ℂ E) := (topDualPairing ℂ E).weakBilin_withSeminorms.toLocallyConvexSpace
  obtain ⟨L,u,hW,hu⟩ := @RCLike.geometric_hahn_banach_closed_point ℂ (WeakDual ℂ E) _ _ _ W _ _ _ _ _ _ hlcs hv hc h
  obtain ⟨x,rfl⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ E) L
  change u < (f x).re at hu
  change ∀ g ∈ W, ((g : WeakDual ℂ E) x).re < u at hW
  have hu0 : 0 < u := by exact hW _ hzero
  have hx : ((u:ℂ)⁻¹ • x) ∈ A := by
    intro g hg
    obtain ⟨c,hc,he⟩ := Complex.exists_norm_eq_mul_self (g x)
    have h := hW (c • g) (hb.smul_mem hc.le hg)
    change (c * g x).re < u at h
    rw [← he, Complex.ofReal_re] at h
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    exact (inv_mul_le_one₀ hu0).mpr h.le
  have hfx := mem_ball_zero_iff.mp (hf _ hx)
  change ‖f ((u:ℂ)⁻¹ • x)‖ < 1 at hfx
  rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu0.le] at hfx
  have := (inv_mul_lt_one₀ hu0).mp hfx
  exact (hu.trans_le (Complex.re_le_norm _)).not_ge this.le

