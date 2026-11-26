-- Prove2me | solution 1 for ManyServerQED.Scheduling.controlled_queue_state_and_effective_noise_are_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:54:54.322327+00:00
-- url     : https://prove2.me/submissions/eb9525c4-bd13-49c3-be45-7decdb702cd2

import Theorems.Thm_ManyServerQED_Scheduling_cadlag_composition_with_continuous_nondecreasing_clock
import Theorems.Thm_ManyServerQED_Scheduling_queue_centered_primitives_are_cadlag
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem IsCadlag.sub' {f g : ℝ → ℝ} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (fun t => f t-g t) := by
  refine ⟨fun t ht => (hf.1 t ht).sub (hg.1 t ht),?_⟩
  intro t ht
  obtain ⟨a,ha⟩ := hf.2 t ht
  obtain ⟨b,hb⟩ := hg.2 t ht
  exact ⟨a-b,ha.sub hb⟩

private theorem IsCadlag.add' {f g : ℝ → ℝ} (hf : IsCadlag f) (hg : IsCadlag g) :
    IsCadlag (fun t => f t+g t) := by
  refine ⟨fun t ht => (hf.1 t ht).add (hg.1 t ht),?_⟩
  intro t ht
  obtain ⟨a,ha⟩ := hf.2 t ht
  obtain ⟨b,hb⟩ := hg.2 t ht
  exact ⟨a+b,ha.add hb⟩

private theorem cadlag_of_continuousOn {f : ℝ → ℝ} (h : ContinuousOn f (Ici (0:ℝ))) :
    IsCadlag f := by
  refine ⟨fun t ht => (h t ht).mono (fun s hs => ht.trans hs),fun t ht => ⟨f t,?_⟩⟩
  have ht' : Ici (0:ℝ) ∈ 𝓝 t := Ici_mem_nhds ht
  exact ((h t ht.le).continuousAt ht').tendsto.mono_left nhdsWithin_le_nhds

private theorem IsCadlag.congr_nonneg {f g : ℝ → ℝ} (hf : IsCadlag f)
    (h : EqOn f g (Ici (0:ℝ))) : IsCadlag g := by
  refine ⟨?_,?_⟩
  · intro t ht
    exact (hf.1 t ht).congr (fun s hs => (h (ht.trans hs)).symm) (h ht).symm
  · intro t ht
    obtain ⟨a,ha⟩ := hf.2 t ht
    refine ⟨a,ha.congr' ?_⟩
    filter_upwards [nhdsWithin_le_nhds (Ici_mem_nhds ht)] with s hs
    exact h hs

private theorem clock_properties {v : ℝ → ℝ}
    (hi : ∀ t, 0 ≤ t → IntervalIntegrable v volume 0 t)
    (hp : ∀ t, 0 ≤ t → 0 ≤ v t) :
    let c (t : ℝ) := ∫ s in (0:ℝ)..t,v s
    ContinuousOn c (Ici (0:ℝ)) ∧ MonotoneOn c (Ici (0:ℝ)) ∧
      ∀ t, 0 ≤ t → 0 ≤ c t := by
  intro c
  refine ⟨?_,?_,?_⟩
  · intro t ht
    have hpos : (0:ℝ) ≤ t+1 := by linarith [show 0 ≤ t from ht]
    have he : ContinuousOn c (Icc (0:ℝ) (t+1)) := by
      simpa only [uIcc_of_le hpos] using
        (intervalIntegral.continuousOn_primitive_interval' (hi (t+1) hpos)
          (a := (0:ℝ)) (by simp [hpos]))
    have hN : Icc (0:ℝ) (t+1) ∈ 𝓝[Ici 0] t := by
      rw [← Ici_inter_Iic, inter_mem_iff]
      exact ⟨self_mem_nhdsWithin,nhdsWithin_le_nhds (Iic_mem_nhds (show t < t+1 by linarith))⟩
    have ht' : t ∈ Icc (0:ℝ) (t+1) := ⟨ht,by linarith⟩
    exact (he t ht').mono_of_mem_nhdsWithin hN
  · intro a ha b hb hab
    have hi' : IntervalIntegrable v volume a b :=
      (hi a ha).symm.trans (hi b hb)
    have h := intervalIntegral.integral_add_adjacent_intervals (hi a ha) hi'
    have hn := intervalIntegral.integral_nonneg (μ := volume) hab (fun s hs => hp s (ha.trans hs.1))
    dsimp [c]
    linarith
  · intro t ht
    exact intervalIntegral.integral_nonneg ht (fun s hs => hp s hs.1)

set_option maxHeartbeats 1300000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 1 ≤ n) (X0 : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsControlled n X0 X Ψ)
    (ω : Ω) (i : Fin k) :
    IsCadlag (fun t => M.Xhat n X ω t i) ∧
    IsCadlag (fun t =>
      (M.Ahat n ω t i-M.Shat n ω (busyTime Ψ ω i t/(n:ℝ)) i-
        M.Rhat n ω (queueTime X Ψ ω i t/(n:ℝ)) i)/M.diffData.r i) := by
  obtain ⟨hA,hS,hR⟩ := queue_centered_primitives_are_cadlag M n ω i
  have hSB := clock_properties (fun t ht => (hC.integrable ω i t ht).1)
    (fun t ht => hC.psi_nonneg ω t i ht)
  have hRB := clock_properties (fun t ht => (hC.integrable ω i t ht).2)
    (fun t ht => hC.phi_nonneg ω t i ht)
  change ContinuousOn (busyTime Ψ ω i) (Ici (0:ℝ)) ∧
    MonotoneOn (busyTime Ψ ω i) (Ici (0:ℝ)) ∧ ∀ t, 0 ≤ t → 0 ≤ busyTime Ψ ω i t at hSB
  change ContinuousOn (queueTime X Ψ ω i) (Ici (0:ℝ)) ∧
    MonotoneOn (queueTime X Ψ ω i) (Ici (0:ℝ)) ∧ ∀ t, 0 ≤ t → 0 ≤ queueTime X Ψ ω i t at hRB
  have hSn := cadlag_composition_with_continuous_nondecreasing_clock
    (fun t => M.Shat n ω t i) (fun t => busyTime Ψ ω i t/(n:ℝ))
    hS (hSB.1.div_const _) (fun a ha b hb hab => div_le_div_of_nonneg_right (hSB.2.1 ha hb hab)
      (Nat.cast_nonneg _)) (fun t ht => div_nonneg (hSB.2.2 t ht) (Nat.cast_nonneg _))
  have hRn := cadlag_composition_with_continuous_nondecreasing_clock
    (fun t => M.Rhat n ω t i) (fun t => queueTime X Ψ ω i t/(n:ℝ))
    hR (hRB.1.div_const _) (fun a ha b hb hab => div_le_div_of_nonneg_right (hRB.2.1 ha hb hab)
      (Nat.cast_nonneg _)) (fun t ht => div_nonneg (hRB.2.2 t ht) (Nat.cast_nonneg _))
  have hS' := cadlag_composition_with_continuous_nondecreasing_clock _ _
    ((M.S_poisson n i).cadlag ω) hSB.1 hSB.2.1 hSB.2.2
  have hR' := cadlag_composition_with_continuous_nondecreasing_clock _ _
    ((M.R_poisson n i).cadlag ω) hRB.1 hRB.2.1 hRB.2.2
  have hA' : IsCadlag (fun t => M.A n i ω t) := by
    have hc : IsCadlag (fun t : ℝ => M.lamN n i*t) :=
      cadlag_of_continuousOn ((continuous_const.mul continuous_id).continuousOn)
    have hm : IsCadlag (fun t => M.Ahat n ω t i*Real.sqrt n) := by
      refine ⟨fun t ht => (hA.1 t ht).mul continuousWithinAt_const,?_⟩
      intro t ht
      obtain ⟨q,hq⟩ := hA.2 t ht
      exact ⟨q*Real.sqrt n,hq.mul tendsto_const_nhds⟩
    apply IsCadlag.congr_nonneg (IsCadlag.add' hm hc)
    intro t _
    dsimp [SystemSequence.Ahat]
    have hn' : (0:ℝ) < n := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn |> Nat.pos_of_ne_zero
    field_simp [(Real.sqrt_pos.2 hn').ne']
    ring
  have hX' : IsCadlag (fun t => X ω t i) := by
    have h0 : IsCadlag (fun _ : ℝ => (X0 i:ℝ)) := cadlag_of_continuousOn continuousOn_const
    apply IsCadlag.congr_nonneg (IsCadlag.sub' (IsCadlag.sub' (IsCadlag.add' h0 hA') hR') hS')
    intro t ht
    exact (hC.eq7 ω t i ht).symm
  have hX : IsCadlag (fun t => X ω t i-M.rho i*n) :=
    IsCadlag.sub' hX' (cadlag_of_continuousOn continuousOn_const)
  have hW := IsCadlag.sub' (IsCadlag.sub' hA hSn) hRn
  refine ⟨⟨fun t ht => (hX.1 t ht).div_const _,?_⟩,⟨fun t ht => (hW.1 t ht).div_const _,?_⟩⟩
  · intro t ht
    obtain ⟨q,hq⟩ := hX.2 t ht
    exact ⟨q/Real.sqrt n,hq.div_const _⟩
  · intro t ht
    obtain ⟨q,hq⟩ := hW.2 t ht
    exact ⟨q/M.diffData.r i,hq.div_const _⟩
