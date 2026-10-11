-- Prove2me | solution 1 for NonconvexDRS.ImageLsc.theorem_5_11
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:09:32.616407+00:00
-- url     : https://prove2.me/submissions/94a1c454-b6f8-463e-b4b3-8544367aee29

import Mathlib
import Definitions.Def_NonconvexDRS_ImageLsc_Setting

open Filter Topology

open NonconvexDRS.ImageLsc in
theorem solution {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hbot : ∀ z, g z ≠ ⊥) (hlsc : LowerSemicontinuous g)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    (∀ sbar ∈ B '' dom g, LowerSemicontinuousAt (NonconvexDRS.ADMM.imageFn B g) sbar) ↔
      ∀ zbar ∈ dom g, Cond55 g B zbar := by
  constructor
  · intro hL zbar hz
    unfold Cond55
    have h1 : (⨅ (d : EuclideanSpace ℝ (Fin n)) (_ : B d = 0), g (zbar + d))
        ≤ NonconvexDRS.ADMM.imageFn B g (B zbar) := by
      refine le_iInf₂ fun x hx => ?_
      have : B (x - zbar) = 0 := by rw [map_sub, hx, sub_self]
      refine le_trans (iInf₂_le (x - zbar) this) (le_of_eq ?_)
      congr 1; abel
    refine h1.trans (le_of_forall_lt_imp_le_of_dense fun c hc => ?_)
    have hev := hL (B zbar) ⟨zbar, hz, rfl⟩ c hc
    have ht : Tendsto (fun d => B (zbar + d))
        (Bornology.cobounded _ ⊓ Filter.comap B (𝓝 0)) (𝓝 (B zbar)) := by
      have : Tendsto (fun d => B zbar + B d) (Filter.comap B (𝓝 0)) (𝓝 (B zbar + 0)) :=
        tendsto_const_nhds.add tendsto_comap
      rw [add_zero] at this
      simpa [map_add] using this.mono_left inf_le_right
    refine Filter.le_liminf_of_le (f := Bornology.cobounded _ ⊓ Filter.comap B (𝓝 0)) (u := fun d => g (zbar + d)) (h := ?_)
    filter_upwards [ht.eventually hev] with d hd
    exact le_of_lt (lt_of_lt_of_le hd (iInf₂_le (f := fun x (_ : B x = B (zbar + d)) => g x) (zbar + d) rfl))
  · intro hC sbar hs
    obtain ⟨zbar0, hz0, rfl⟩ := hs
    intro y hy
    obtain ⟨y', hy1, hy2⟩ := exists_between hy
    have hinf : NonconvexDRS.ADMM.imageFn B g (B zbar0)
        ≤ ⨅ (d : EuclideanSpace ℝ (Fin n)) (_ : B d = 0), g (zbar0 + d) :=
      le_iInf₂ fun d hd => iInf₂_le (zbar0 + d) (by simp [hd])
    have hev : ∀ᶠ d in Bornology.cobounded _ ⊓ Filter.comap B (𝓝 0), y' < g (zbar0 + d) :=
      Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le hy2 (hinf.trans (hC zbar0 hz0)))
    rw [Filter.Eventually, Filter.mem_inf_iff] at hev
    obtain ⟨U, hU, V, hV, hUV⟩ := hev
    have hUb : Bornology.IsBounded Uᶜ := Bornology.isBounded_def.2 (by rwa [compl_compl])
    obtain ⟨R, hR⟩ := hUb.subset_closedBall 0
    obtain ⟨t, ht, htV⟩ := Filter.mem_comap.1 hV
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
    set C := Metric.closedBall zbar0 R ∩ g ⁻¹' Set.Iic y' with hCdef
    have hCc : IsCompact C := (isCompact_closedBall _ _).inter_right (hlsc.isClosed_preimage y')
    have hBC : IsClosed (B '' C) := (hCc.image B.continuous).isClosed
    have hnot : B zbar0 ∉ B '' C := by
      rintro ⟨z, ⟨_, hzle⟩, hBz⟩
      have h1 : NonconvexDRS.ADMM.imageFn B g (B zbar0) ≤ g z := iInf₂_le z hBz
      have h2 : g z ≤ y' := hzle
      exact absurd (lt_of_lt_of_le hy2 (h1.trans h2)) (lt_irrefl _)
    filter_upwards [hBC.isOpen_compl.mem_nhds hnot, Metric.ball_mem_nhds (B zbar0) hδ]
      with s hs1 hs2
    refine lt_of_lt_of_le hy1 (le_iInf₂ fun z hz => le_of_lt ?_)
    by_cases hzR : z ∈ Metric.closedBall zbar0 R
    · by_contra hle
      push Not at hle
      exact hs1 ⟨z, ⟨hzR, hle⟩, hz⟩
    · have hdU : z - zbar0 ∈ U := by
        by_contra hdU
        apply hzR
        have := hR hdU
        rw [Metric.mem_closedBall, dist_zero_right] at this
        rwa [Metric.mem_closedBall, dist_eq_norm]
      have hdV : z - zbar0 ∈ V := by
        apply htV
        apply hball
        rw [Metric.mem_ball, dist_zero_right, map_sub, hz, ← dist_eq_norm]
        exact hs2
      have : z - zbar0 ∈ {x | y' < g (zbar0 + x)} := hUV ▸ ⟨hdU, hdV⟩
      simpa using this

#print axioms solution
