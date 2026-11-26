-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_selected_before
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:49:37.801479+00:00
-- url     : https://prove2.me/submissions/a63ddc58-d9bf-429f-a48b-4d31356663cd

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_selected_cell_near
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (X L : NNReal → ℝ)
    (hCad : IsCadlag X)
    (hLeft : ∀ s : NNReal, 0 < s →
      Tendsto X (nhdsWithin s (Iio s)) (nhds (L s)))
    (K : NNReal → ℝ → ℝ → ℝ)
    (hK : Continuous (fun p : NNReal × ℝ × ℝ => K p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : ∀ s x z, |z| ≤ ρ → K s x z = 0)
    (T : NNReal)
    (s : NNReal) (hs : 0 < s) (hsT : s ≤ T) (j : ℕ → ℕ)
    (hj : ∀ᶠ n : ℕ in atTop,
      j n < n ∧ T * (j n : NNReal) / (n : NNReal) < s ∧
      s ≤ T * ((j n+1 : ℕ) : NNReal) / (n : NNReal)) :
    let u : ℕ → ℕ → NNReal := fun n k => T * (k : NNReal) / (n : NNReal)
    let C : ℕ → NNReal → ℕ → ℝ := fun n t k =>
      K (u n k) (X (u n k))
        (X (min t (u n (k+1))) - X (min t (u n k)))
    let A : NNReal → NNReal → ℝ := fun t s =>
      if s ≤ t then K s (L s) (X s-L s) else 0
    ∀ᶠ n : ℕ in atTop, ∀ t : NNReal, t < s → C n t (j n) = 0 := by
  intro u C A
  obtain ⟨δ,hδ,hnear⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp (hLeft s hs) (ρ/3) (by positivity)
  have hgeo := Kyprianou.Ch04.ito43_cutoff_selected_cell_near T s j hj δ hδ
  filter_upwards [hgeo] with n hn
  let a := u n (j n)
  let b := u n (j n+1)
  obtain ⟨ha,hb,hnearcell⟩ := hn
  intro t ht
  change K a (X a) (X (min t b)-X (min t a)) = 0
  by_cases hta : t ≤ a
  · rw [min_eq_left hta,min_eq_left (hta.trans (ha.le.trans hb)),sub_self]
    exact hzero _ _ _ (by simpa using hρ.le)
  · have hat : a ≤ t := le_of_not_ge hta
    rw [min_eq_right hat,min_eq_left (ht.le.trans hb)]
    apply hzero
    have hXa := hnear ha (hnearcell a ⟨le_rfl,ha.le.trans hb⟩)
    have hXt := hnear ht (hnearcell t ⟨hat,ht.le.trans hb⟩)
    rw [Real.dist_eq] at hXa hXt
    have htri := abs_sub_le (X t) (L s) (X a)
    rw [abs_sub_comm (L s) (X a)] at htri
    linarith
