-- Prove2me | solution 1 for HeymanStidham.HLG.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T18:25:36.769797+00:00
-- url     : https://prove2.me/submissions/d831559c-bcda-45b8-9f5e-67b25246811c

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting
import Theorems.Thm_HeymanStidham_HLG_theorem_1
import Theorems.Thm_HeymanStidham_HLG_eq6_parts

open Filter Topology MeasureTheory

open HeymanStidham.HLG in
/-- Arrival epochs tend to infinity when the arrival rate is positive. -/
private lemma hlg2_tendsto_t (t : ℕ → ℝ) (ht : Monotone t) (lam : ℝ) (hlam : 0 < lam)
    (hrate : IsArrivalRate t lam) : Tendsto t atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone ht ?_
  intro b
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ᶠ T : ℝ in atTop, (arrivalCount t T : ℝ) / T = 0 := by
    filter_upwards [eventually_ge_atTop b] with T hT
    have hset : {n : ℕ | t n ≤ T} = Set.univ := by
      ext n; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (hcon n).le.trans hT
    simp [arrivalCount, hset, Set.Infinite.ncard Set.infinite_univ]
  have h0 : Tendsto (fun T : ℝ => (arrivalCount t T : ℝ) / T) atTop (𝓝 0) :=
    (tendsto_congr' hzero).mpr tendsto_const_nhds
  exact hlam.ne' (tendsto_nhds_unique hrate h0)

open HeymanStidham.HLG in
theorem solution (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) (hI : CondI t f s) (hII : CondII s)
    (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam)
    (hv : ∀ n, IntegrableOn (f n) (Set.Ici 0))
    (Gp Gm : ℝ)
    (hGp : IsCustomerAverage (custTotal (posPartFn f)) Gp)
    (hGm : IsCustomerAverage (custTotal (negPartFn f)) Gm) :
    IsCustomerAverage (custTotal f) (Gp - Gm) ∧
      IsTimeAverage (rate f) (lam * (Gp - Gm)) := by
  have htinf := hlg2_tendsto_t t ht lam hlam hrate
  -- (i) for f⁺ and f⁻
  have hIp : CondI t (posPartFn f) s := by
    refine ⟨hI.1, fun n τ hτ hn => ?_⟩
    simp [posPartFn, hI.2 n τ hτ hn]
  have hIm : CondI t (negPartFn f) s := by
    refine ⟨hI.1, fun n τ hτ hn => ?_⟩
    simp [negPartFn, hI.2 n τ hτ hn]
  -- (iii) and (iv) for f⁺ and f⁻
  have hiiip : ∀ n τ, 0 ≤ τ → 0 ≤ posPartFn f n τ := fun n τ _ => le_max_left _ _
  have hiiim : ∀ n τ, 0 ≤ τ → 0 ≤ negPartFn f n τ := fun n τ _ => le_max_left _ _
  have hivp : ∀ n, IntegrableOn (posPartFn f n) (Set.Ici 0) := by
    intro n
    have := (hv n).pos_part
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp [posPartFn, max_comm]
  have hivm : ∀ n, IntegrableOn (negPartFn f n) (Set.Ici 0) := by
    intro n
    have := (hv n).neg_part
    refine this.congr (Filter.Eventually.of_forall fun τ => ?_)
    simp [negPartFn, max_comm]
  -- (5): Theorem 1 applied to f⁺ and f⁻
  have hHp := theorem_1 t ht ht0 (posPartFn f) s hIp hII lam hlam hrate hiiip hivp Gp hGp
  have hHm := theorem_1 t ht ht0 (negPartFn f) s hIm hII lam hlam hrate hiiim hivm Gm hGm
  -- (6)
  have h6 := eq6_parts t ht ht0 htinf f s hI hv Gp Gm (lam * Gp) (lam * Gm) hGp hGm hHp hHm
  refine ⟨h6.1, ?_⟩
  rw [mul_sub]
  exact h6.2
