-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_selected_after
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:49:33.407794+00:00
-- url     : https://prove2.me/submissions/9e7e5d52-012b-40c1-8b03-1ab01921b57b

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
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : NNReal, s ≤ t → |C n t (j n) - K s (L s) (X s-L s)| < ε := by
  intro u C A e he
  obtain ⟨d,hd,hKnear⟩ := Metric.continuousAt_iff.mp
    (hK.continuousAt (x := (s,L s,X s-L s))) e he
  obtain ⟨dl,hdl,hLnear⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp (hLeft s hs) (d/3) (by positivity)
  obtain ⟨dr,hdr,hRnear⟩ :=
    Metric.tendsto_nhdsWithin_nhds.mp (hCad s).1.tendsto (d/3) (by positivity)
  have hgeo := Kyprianou.Ch04.ito43_cutoff_selected_cell_near T s j hj
    (min d (min dl dr)) (lt_min hd (lt_min hdl hdr))
  filter_upwards [hgeo] with n hn
  let a := u n (j n)
  let b := u n (j n+1)
  obtain ⟨ha,hb,hnear⟩ := hn
  intro t ht
  change |K a (X a) (X (min t b)-X (min t a))-K s (L s) (X s-L s)| < e
  rw [min_eq_right (ha.le.trans ht)]
  have hda := hnear a ⟨le_rfl,ha.le.trans hb⟩
  have hdb := hnear (min t b) ⟨ha.le.trans (le_min ht hb),min_le_right _ _⟩
  have hXa := hLnear ha (hda.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hXb := hRnear (le_min ht hb)
    (hdb.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  rw [Real.dist_eq] at hXa hXb
  have hdiff : |(X (min t b)-X a)-(X s-L s)| < d := by
    have hEq : (X (min t b)-X a)-(X s-L s) =
        (X (min t b)-X s)-(X a-L s) := by ring
    rw [hEq]
    have htri := abs_sub_le (X (min t b)-X s) 0 (X a-L s)
    simp only [sub_zero,zero_sub,abs_neg] at htri
    linarith
  have hp : dist (a,X a,X (min t b)-X a) (s,L s,X s-L s) < d := by
    rw [Prod.dist_eq,Prod.dist_eq,max_lt_iff,max_lt_iff]
    exact ⟨hda.trans_le (min_le_left _ _),
      by rw [Real.dist_eq]; linarith, by simpa only [Real.dist_eq] using hdiff⟩
  simpa only [Real.dist_eq] using hKnear hp
