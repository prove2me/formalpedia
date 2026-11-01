-- Prove2me | solution 1 for HeteroRetire.Boundary.theorem_19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:44:43.343544+00:00
-- url     : https://prove2.me/submissions/85c61661-8287-47bc-96b8-464e34150043
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HeteroRetire_Boundary_Market
import Definitions.Def_HeteroRetire_Boundary_Model
import Theorems.Thm_HeteroRetire_Boundary_thm19_anti_t
import Theorems.Thm_HeteroRetire_Boundary_proposition_17
import Theorems.Thm_HeteroRetire_Boundary_thm19_terminal_lower

open MeasureTheory ProbabilityTheory Set Filter Topology
open HeteroRetire.Boundary

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝔽 : Filtration ℝ ‹MeasurableSpace Ω›)
    {n : ℕ} (M : Market n) (hM : M.Standing)
    (Z : ℝ → Ω → ℝ) (hZ : IsDualNoise P 𝔽 M Z)
    (ell : ℝ) (I' L' : ℝ → ℝ)
    (h18 : Assumption18 M ell I' L') (hconst : ConstOnAged M ell) :
    MonotoneOn (bdry P 𝔽 M Z) (Icc (M.T - ell) M.T) ∧
    Tendsto (bdry P 𝔽 M Z) (𝓝[<] M.T)
      (𝓝 ((M.L M.T / M.I M.T : ℝ) : EReal)) := by
  have hanti := thm19_anti_t P 𝔽 M hM Z hZ ell I' L' h18 hconst
  refine ⟨?_, ?_⟩
  · intro s hs t ht hst
    apply sInf_le_sInf
    rintro _ ⟨y, ⟨hy0, hyW⟩, rfl⟩
    exact ⟨y, ⟨hy0, lt_of_lt_of_le hyW (hanti s hs t ⟨hst, ht.2⟩ y hy0)⟩, rfl⟩
  · -- continuity of L/I at T from the left
    have hT0 : 0 ≤ M.T := hM.T_pos.le
    have hTmem : M.T ∈ Icc 0 M.Tbar := ⟨hT0, hM.T_lt.le⟩
    have hIc : ContinuousWithinAt M.I (Icc 0 M.Tbar) M.T := hM.I_regular.2.1 _ hTmem
    have hLc : ContinuousWithinAt M.L (Icc 0 M.Tbar) M.T := hM.L_regular.2.1 _ hTmem
    have hIpos : M.I M.T ≠ 0 := (hM.I_regular.1 _ hTmem).ne'
    have hsub : Ioo 0 M.T ⊆ Icc 0 M.Tbar := fun x hx => ⟨hx.1.le, hx.2.le.trans hM.T_lt.le⟩
    have hnhds : 𝓝[Ioo 0 M.T] M.T = 𝓝[<] M.T := by
      apply nhdsWithin_eq_nhdsWithin' (s := Ioi 0) (Ioi_mem_nhds hM.T_pos)
      ext x; simp [Ioo, and_comm]
    have hratio : Tendsto (fun t => M.L t / M.I t) (𝓝[<] M.T) (𝓝 (M.L M.T / M.I M.T)) := by
      rw [← hnhds]
      exact ((hLc.mono hsub).div (hIc.mono hsub) hIpos)
    have hratioE : Tendsto (fun t => ((M.L t / M.I t : ℝ) : EReal)) (𝓝[<] M.T)
        (𝓝 ((M.L M.T / M.I M.T : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp hratio
    have hup : ∀ᶠ t in 𝓝[<] M.T, bdry P 𝔽 M Z t ≤ ((M.L t / M.I t : ℝ) : EReal) := by
      have : Ioo 0 M.T ∈ 𝓝[<] M.T := by rw [← hnhds]; exact self_mem_nhdsWithin
      filter_upwards [this] with t ht
      exact proposition_17 P 𝔽 M hM Z hZ t ⟨ht.1.le, ht.2⟩
    have hlow := thm19_terminal_lower P 𝔽 M hM Z hZ ell I' L' h18 hconst
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · obtain ⟨c, hac, hcl⟩ := EReal.lt_iff_exists_real_btwn.mp ha
      have hc : c < M.L M.T / M.I M.T := EReal.coe_lt_coe_iff.mp hcl
      filter_upwards [hlow c hc] with t ht
      exact lt_of_lt_of_le hac ht
    · filter_upwards [hup, (tendsto_order.mp hratioE).2 a ha] with t h1 h2
      exact lt_of_le_of_lt h1 h2
