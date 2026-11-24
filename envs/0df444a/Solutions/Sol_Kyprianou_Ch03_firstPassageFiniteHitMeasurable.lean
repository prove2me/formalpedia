-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageFiniteHitMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T03:25:24.358155+00:00
-- url     : https://prove2.me/submissions/72c94aab-c0c4-4159-97ad-f383fd3f0b61

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageFiniteHitMeasurableNonneg

open MeasureTheory AvramDividend.Classical Set Filter Topology
open scoped NNReal ENNReal

set_option autoImplicit false

/-!
Measurability of `{τ_x^+ < ∞}` for arbitrary barrier `x`.

* If `0 ≤ x`, apply Proved `firstPassageFiniteHitMeasurableNonneg`.
* If `x < 0`, then `X_0 = 0 > x`; right-continuity at 0 yields a positive-time
  exceedance, so the event is `univ` (hence measurable).
-/

namespace Kyprianou.Ch03

private lemma firstHitting_ne_top_of_mem
    {Omega : Type} (X : NNReal → Omega → Real) (x : Real) (ω : Omega)
    {t : NNReal} (ht : 0 < t) (htmem : X t ω ∈ Ioi x) :
    firstHittingTime X (Ioi x) ω ≠ ⊤ := by
  have hmem :
      (t : WithTop NNReal) ∈
        (fun u : NNReal => (u : WithTop NNReal)) ''
          {u : NNReal | 0 < u ∧ X u ω ∈ Ioi x} :=
    ⟨t, ⟨ht, htmem⟩, rfl⟩
  have hle : firstHittingTime X (Ioi x) ω ≤ (t : WithTop NNReal) :=
    csInf_le (OrderBot.bddBelow _) hmem
  intro htop
  rw [htop] at hle
  exact WithTop.not_top_le_coe t hle

private lemma exists_pos_time_exceedance_of_neg_barrier
    {Omega : Type} [MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (x : Real) (hx : x < 0) (ω : Omega) :
    ∃ t : NNReal, 0 < t ∧ L.X t ω ∈ Ioi x := by
  have hx0 : x < L.X 0 ω := by rw [L.X_zero ω]; exact hx
  have htend :
      Tendsto (fun s : NNReal => L.X s ω) (𝓝[Ici (0 : NNReal)] 0) (𝓝 (L.X 0 ω)) :=
    (L.rightCont ω 0).tendsto
  have hev : ∀ᶠ t in 𝓝[Ici (0 : NNReal)] 0, L.X t ω ∈ Ioi x :=
    htend.eventually (Ioi_mem_nhds hx0)
  have hle : 𝓝[>] (0 : NNReal) ≤ 𝓝[Ici (0 : NNReal)] 0 :=
    nhdsWithin_mono 0 Ioi_subset_Ici_self
  have hev' : ∀ᶠ t in 𝓝[>] (0 : NNReal), L.X t ω ∈ Ioi x := hev.filter_mono hle
  obtain ⟨t, htmem, htIoi⟩ := (hev'.and self_mem_nhdsWithin).exists
  exact ⟨t, mem_Ioi.mp htIoi, htmem⟩

private lemma finiteHit_eq_univ_of_neg_barrier
    {Omega : Type} [MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal (inferInstance : MeasurableSpace Omega)}
    (L : SpectrallyNegativeLevy P F) (x : Real) (hx : x < 0) :
    {omega : Omega | firstHittingTime L.X (Ioi x) omega != ⊤} = univ := by
  ext ω
  simp only [mem_univ, iff_true, bne_iff_ne]
  obtain ⟨t, ht0, htmem⟩ := exists_pos_time_exceedance_of_neg_barrier L x hx ω
  exact firstHitting_ne_top_of_mem L.X x ω ht0 htmem

end Kyprianou.Ch03

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : Real) :
    MeasurableSet {omega : Omega |
      firstHittingTime L.X (Set.Ioi x) omega != ⊤} := by
  by_cases hx : 0 ≤ x
  · exact firstPassageFiniteHitMeasurableNonneg P F L x hx
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [finiteHit_eq_univ_of_neg_barrier L x hxneg]
    exact MeasurableSet.univ
