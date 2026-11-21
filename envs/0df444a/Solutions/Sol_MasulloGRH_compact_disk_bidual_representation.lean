-- Prove2me | solution 1 for MasulloGRH.compact_disk_bidual_representation
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T23:48:10.829877+00:00
-- url     : https://prove2.me/submissions/2ddff194-9fec-4b93-9d64-06d0de1c4ea5

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Topology Filter Set
open scoped ComplexOrder

noncomputable section

private theorem norm_le_of_re_le_on_balanced {E : Type*} [AddCommGroup E] [Module ℂ E]
    (K : Set E) (hK : Balanced ℂ K) (f : E →ₗ[ℂ] ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hf : ∀ y ∈ K, (f y).re ≤ r) : ∀ y ∈ K, ‖f y‖ ≤ r := by
  intro y hy
  by_cases hz : f y = 0
  · simpa [hz] using hr
  let c : ℂ := (‖f y‖ : ℂ) / f y
  have hc : ‖c‖ ≤ 1 := by simp [c, hz]
  have h := hf (c • y) (hK c hc (Set.smul_mem_smul_set hy))
  simpa [map_smul, smul_eq_mul, c, div_mul_cancel₀ _ hz] using h

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (K : Set E) (hK : IsCompact K) (hconv : Convex ℝ K)
    (hbal : Balanced ℂ K) (h0 : (0 : E) ∈ K)
    (F : StrongDual ℂ (StrongDual ℂ E))
    (hF : ∀ (f : StrongDual ℂ E) (r : ℝ), 0 ≤ r →
      (∀ y ∈ K, ‖f y‖ ≤ r) → ‖F f‖ ≤ r) :
    ∃ y ∈ K, ∀ f : StrongDual ℂ E, F f = f y := by
  let _ := WeakBilin.instAddCommGroup (𝕜 := ℂ) (E := StrongDual ℂ (StrongDual ℂ E)) (F := StrongDual ℂ E) (topDualPairing ℂ (StrongDual ℂ E))
  have : IsTopologicalAddGroup (WeakBilin (topDualPairing ℂ (StrongDual ℂ E))) :=
    WeakBilin.instIsTopologicalAddGroup (𝕜 := ℂ) (E := StrongDual ℂ (StrongDual ℂ E)) (F := StrongDual ℂ E) (topDualPairing ℂ (StrongDual ℂ E))
  have : LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℂ (StrongDual ℂ E))) :=
    WeakBilin.locallyConvexSpace (𝕜 := ℂ) (E := StrongDual ℂ (StrongDual ℂ E)) (F := StrongDual ℂ E) (B := topDualPairing ℂ (StrongDual ℂ E))
  have : T2Space (WeakBilin (topDualPairing ℂ (StrongDual ℂ E))) := (WeakBilin.isEmbedding (B := topDualPairing ℂ (StrongDual ℂ E))
    (fun f g h => ContinuousLinearMap.ext (fun x => LinearMap.congr_fun h x))).t2Space
  let j : E →ₗ[ℂ] (WeakBilin (topDualPairing ℂ (StrongDual ℂ E))) :=
    { toFun := fun x => (show StrongDual ℂ (StrongDual ℂ E) from
        ⟨(topDualPairing ℂ E).flip x, continuous_eval_const x⟩)
      map_add' := by intros; apply ContinuousLinearMap.ext; intro f; exact f.map_add _ _
      map_smul' := by intros; apply ContinuousLinearMap.ext; intro f; exact f.map_smul _ _ }
  have hj : Continuous j := WeakBilin.continuous_of_continuous_eval _ fun f => f.continuous
  have hmem : (F : (WeakBilin (topDualPairing ℂ (StrongDual ℂ E)))) ∈ j '' K := by
    by_contra hn
    have hc : Convex ℝ (j '' K) := hconv.linear_image (j.restrictScalars ℝ)
    obtain ⟨g, r, hg, hr⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      hc (hK.image hj).isClosed hn
    obtain ⟨f, hf⟩ := LinearMap.dualEmbedding_surjective (𝕜 := ℂ) (E := StrongDual ℂ (StrongDual ℂ E)) (F := StrongDual ℂ E)
      (topDualPairing ℂ (StrongDual ℂ E)) g
    have hgr : ∀ y ∈ K, (f y).re < r := by
      intro y hy
      have h := hg (j y) (mem_image_of_mem j hy)
      rw [← hf] at h
      exact h
    have hr0 : 0 ≤ r := le_of_lt (by simpa using hgr 0 h0)
    have hnorm := norm_le_of_re_le_on_balanced K hbal f.toLinearMap r hr0
      (fun y hy => (hgr y hy).le)
    have h := hF f r hr0 hnorm
    rw [← hf] at hr
    exact (not_lt_of_ge ((Complex.re_le_norm (F f)).trans h)) hr
  obtain ⟨y, hy, he⟩ := hmem
  exact ⟨y, hy, fun f => (congrArg (fun G : (WeakBilin (topDualPairing ℂ (StrongDual ℂ E))) => (topDualPairing ℂ (StrongDual ℂ E)) G f) he).symm⟩
