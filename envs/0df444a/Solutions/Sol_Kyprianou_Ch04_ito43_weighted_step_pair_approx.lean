-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_step_pair_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:19:04.342379+00:00
-- url     : https://prove2.me/submissions/4e1ada39-f6fc-4eb5-8907-c6090c54f3e8

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
import Definitions.Def_WhittFLT_Composition_SkorohodD
import Theorems.Thm_Kyprianou_Ch04_ito43_real_step_partition
import Theorems.Thm_Kyprianou_Ch04_ito43_real_step_left_transfer
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_real_path_right
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_real_path_left
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04
open scoped Topology

open Set
theorem solution  {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → ℝ) (w : Omega)
    (hc : IsCadlag (fun t => X t w))
    (hl : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Set.Iio t)) (nhds (Xleft t w)))
    (σ : ℝ) (hσ : 0 ≤ σ)
    (g : ℝ × ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ici (0 : ℝ) ×ˢ (Set.univ : Set ℝ)))
    (T : NNReal)
    (hs : Summable (fun s : Set.Ioc (0:NNReal) (T+1) => (X s w-Xleft s w)^2))
 :
    let W : ℕ → (ℕ → NNReal) → (ℕ → ℝ) → NNReal → ℝ :=
      fun m b c s => ∑ i ∈ Finset.range m, c i * (if b i ≤ s then (1:ℝ) else 0)
    let L : ℕ → (ℕ → NNReal) → (ℕ → ℝ) → NNReal → ℝ :=
      fun m b c s => ∑ i ∈ Finset.range m, c i * (if b i < s then (1:ℝ) else 0)
    ∀ δ : ℝ, 0 < δ → ∃ (m : ℕ) (b : ℕ → NNReal) (c : ℕ → ℝ),
(∀ s ≤ T, |g ((s:ℝ),X s w)-W m b c s| ≤ δ) ∧
      (∀ s : NNReal, 0 < s → s ≤ T → |g ((s:ℝ),Xleft s w)-L m b c s| ≤ δ) := by
  dsimp only
  intro δ hδ
  let Y : ℝ → ℝ := fun r => g (r,X r.toNNReal w)
  let YL : ℝ → ℝ := fun r => g (r,Xleft r.toNNReal w)
  let U : ℝ := (T:ℝ)+1
  have hU : 0 < U := by dsimp [U]; positivity
  have hY : WhittFLT.Composition.IsCadlagOn (Icc 0 U) Y := by
    intro t ht
    constructor
    · exact (ito43_weighted_real_path_right X w g hg hc t ht.1).mono inter_subset_right
    · by_cases hp : 0 < t
      · exact ⟨YL t, (ito43_weighted_real_path_left X w g hg Xleft hl t hp).mono_left
          (nhdsWithin_mono _ inter_subset_right)⟩
      · have hz : t = 0 := le_antisymm (le_of_not_gt hp) ht.1
        subst t
        have he : Icc (0:ℝ) U ∩ Iio 0 = ∅ := by
          ext r
          simp only [mem_inter_iff,mem_Icc,mem_Iio,mem_empty_iff_false]
          exact ⟨fun h => (not_lt_of_ge h.1.1) h.2, False.elim⟩
        exact ⟨0, by simp [he]⟩
  obtain ⟨m,b,c,hb,hW⟩ := ito43_real_step_partition Y U hU hY δ hδ
  have hW' : ∀ r : ℝ, 0 ≤ r → r ≤ (T:ℝ) →
      |Y r - ∑ i ∈ Finset.range m, c i * (if b i ≤ r then (1:ℝ) else 0)| ≤ δ := by
    intro r hr hrt
    apply hW r hr
    dsimp [U]
    linarith
  have hL := ito43_real_step_left_transfer Y YL (T:ℝ)
    (fun t ht _ => ito43_weighted_real_path_left X w g hg Xleft hl t ht)
    δ m b c hW'
  have hbc (i : ℕ) : ((b i).toNNReal : ℝ) = b i := Real.coe_toNNReal (b i) (hb i)
  have hle (i : ℕ) (s : NNReal) : (b i).toNNReal ≤ s ↔ b i ≤ (s:ℝ) := by
    change ((b i).toNNReal : ℝ) ≤ (s:ℝ) ↔ _
    rw [hbc]
  have hlt (i : ℕ) (s : NNReal) : (b i).toNNReal < s ↔ b i < (s:ℝ) := by
    change ((b i).toNNReal : ℝ) < (s:ℝ) ↔ _
    rw [hbc]
  refine ⟨m,fun i => (b i).toNNReal,c,?_,?_⟩
  · intro s hs
    simpa [Y,hle] using hW' (s:ℝ) s.2 (show (s:ℝ) ≤ (T:ℝ) from hs)
  · intro s hs ht
    simpa [YL,hlt] using hL (s:ℝ) (show (0:ℝ) < (s:ℝ) from hs)
      (show (s:ℝ) ≤ (T:ℝ) from ht)
