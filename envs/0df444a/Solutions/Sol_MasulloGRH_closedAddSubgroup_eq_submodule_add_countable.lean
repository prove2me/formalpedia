-- Prove2me | solution 1 for MasulloGRH.closedAddSubgroup_eq_submodule_add_countable
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T16:22:49.777918+00:00
-- url     : https://prove2.me/submissions/f753dbd3-d38a-45e9-b99a-555001c9d58d

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Ring.Star

set_option autoImplicit false

open Topology Filter

namespace MasulloGRHClosedSubAux

theorem main {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : AddSubgroup E) (hH : IsClosed (H : Set E)) :
    ∃ V : Submodule ℝ E, (V : Set E) ⊆ H ∧ ∃ D : Set E, D.Countable ∧ D ⊆ H ∧
      ∀ h ∈ H, ∃ v ∈ V, ∃ δ ∈ D, h = v + δ := by
  let V : Submodule ℝ E :=
    { carrier := {v | ∀ t : ℝ, t • v ∈ H}
      add_mem' := by
        intro a b ha hb t
        simp only [Set.mem_ofPred_eq] at ha hb
        rw [smul_add]
        exact H.add_mem (ha t) (hb t)
      zero_mem' := by
        intro t
        rw [smul_zero]
        exact H.zero_mem
      smul_mem' := by
        intro c v hv t
        simp only [Set.mem_ofPred_eq] at hv
        rw [smul_smul]
        exact hv (t * c) }
  have hVH : (V : Set E) ⊆ H := fun v hv => by
    have := hv 1
    rwa [one_smul] at this
  obtain ⟨W, hVW⟩ := Submodule.exists_isCompl V
  have hWc : IsClosed (W : Set E) := W.closed_of_finiteDimensional
  -- discreteness of `H ∩ W`
  have key : ∃ ε > 0, ∀ w ∈ W, w ∈ H → w ≠ 0 → ε ≤ ‖w‖ := by
    by_contra! hne
    have hseq : ∀ k : ℕ, ∃ w ∈ W, w ∈ H ∧ w ≠ 0 ∧ ‖w‖ < 1 / ((k : ℝ) + 1) :=
      fun k => hne _ (by positivity)
    choose w hwW hwH hw0 hwlt using hseq
    have hwpos : ∀ k, 0 < ‖w k‖ := fun k => norm_pos_iff.mpr (hw0 k)
    set u : ℕ → E := fun k => ‖w k‖⁻¹ • w k with hu
    have humem : ∀ k, u k ∈ Metric.sphere (0 : E) 1 ∩ W := by
      intro k
      refine ⟨?_, W.smul_mem _ (hwW k)⟩
      rw [mem_sphere_zero_iff_norm, hu, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (hwpos k).ne']
    obtain ⟨u₀, ⟨hu₀s, hu₀W⟩, φ, hφ, hlim⟩ :=
      ((isCompact_sphere (0 : E) 1).inter_right hWc).tendsto_subseq humem
    have hρ : Tendsto (fun k => ‖w (φ k)‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hwlt (φ k)).le) h1
    have hu₀V : u₀ ∈ V := by
      intro t
      have h1 : Tendsto (fun k => t • u (φ k)) atTop (𝓝 (t • u₀)) := hlim.const_smul t
      have h2 : Tendsto (fun k => (⌊t / ‖w (φ k)‖⌋ : ℤ) • w (φ k) - t • u (φ k)) atTop
          (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hρ
        set ρ := ‖w (φ k)‖ with hρdef
        have hρp : 0 < ρ := hwpos _
        have hw : w (φ k) = ρ • u (φ k) := by
          simp only [hu]
          rw [smul_smul, mul_inv_cancel₀ hρp.ne', one_smul]
        have hun : ‖u (φ k)‖ = 1 := by
          have := (humem (φ k)).1
          rwa [mem_sphere_zero_iff_norm] at this
        set q := t / ρ with hq
        have htq : t = q * ρ := by rw [hq, div_mul_cancel₀ _ hρp.ne']
        have e : (⌊q⌋ : ℤ) • w (φ k) - t • u (φ k) = (((⌊q⌋ : ℝ) - q) * ρ) • u (φ k) := by
          rw [hw, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, htq, ← sub_smul]
          congr 1
          ring
        rw [e, norm_smul, hun, mul_one, Real.norm_eq_abs, abs_mul, abs_of_pos hρp]
        have hf1 := Int.floor_le q
        have hf2 := Int.lt_floor_add_one q
        have : |(⌊q⌋ : ℝ) - q| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
        nlinarith [abs_nonneg ((⌊q⌋ : ℝ) - q)]
      have h3 := h2.add h1
      simp only [sub_add_cancel, zero_add] at h3
      exact hH.mem_of_tendsto h3 (Eventually.of_forall fun k => H.zsmul_mem (hwH _) _)
    have h0 : u₀ = 0 := by
      have : u₀ ∈ V ⊓ W := ⟨hu₀V, hu₀W⟩
      rw [hVW.inf_eq_bot, Submodule.mem_bot] at this
      exact this
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hu₀s
    exact zero_ne_one hu₀s
  obtain ⟨ε, hε, hεW⟩ := key
  let D : Set E := {x | x ∈ H ∧ x ∈ W}
  have hDc : D.Countable := by
    haveI : DiscreteTopology D := DiscreteTopology.of_forall_le_dist hε fun x y hxy => by
      show ε ≤ dist x y
      rw [Subtype.dist_eq, dist_eq_norm]
      refine hεW _ (W.sub_mem x.2.2 y.2.2) (H.sub_mem x.2.1 y.2.1) ?_
      exact sub_ne_zero.mpr fun h => hxy (Subtype.ext h)
    haveI : TopologicalSpace.SeparableSpace D := inferInstance
    exact Set.countable_coe_iff.mp (TopologicalSpace.separableSpace_iff_countable.mp this)
  refine ⟨V, hVH, D, hDc, fun x hx => hx.1, fun h hh => ?_⟩
  have hmem : h ∈ V ⊔ W := by rw [hVW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
  refine ⟨y, hy, z, ⟨?_, hz⟩, hyz.symm⟩
  have : z = h - y := by rw [← hyz]; abel
  rw [this]
  exact H.sub_mem hh (hVH hy)

end MasulloGRHClosedSubAux


theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (H : AddSubgroup E) (hH : IsClosed (H : Set E)) :
    ∃ V : Submodule ℝ E, (V : Set E) ⊆ H ∧ ∃ D : Set E, D.Countable ∧ D ⊆ H ∧
      ∀ h ∈ H, ∃ v ∈ V, ∃ δ ∈ D, h = v + δ :=
  MasulloGRHClosedSubAux.main H hH
