-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cadlag_stopped_cutoff_kernel_uniform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:48:09.23551+00:00
-- url     : https://prove2.me/submissions/b4672a13-3ff0-4b27-81b6-cbd0c6877bc7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_finite_cell_reindex
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_selected_cell_uniform
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
    (T : NNReal) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ t : NNReal, t ≤ T →
        let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
        let v : ℕ → NNReal := fun k => min t (u k)
        |(∑ k ∈ Finset.range n,
          K (u k) (X (u k)) (X (v (k+1))-X (v k))) -
          (∑' s : Ioc (0 : NNReal) t,
            K s.1 (L s.1) (X s.1-L s.1))| < ε := by
  intro ε he
  classical
  obtain ⟨S,j,hS,hj,hgrid,hjump⟩ :=
    Kyprianou.Ch04.ito43_cutoff_finite_cell_reindex
      X L hCad hLeft K hK ρ hρ hzero T
  let u : ℕ → ℕ → NNReal := fun n k => T * (k : NNReal) / (n : NNReal)
  let C : ℕ → NNReal → ℕ → ℝ := fun n t k =>
    K (u n k) (X (u n k))
      (X (min t (u n (k+1))) - X (min t (u n k)))
  let A : NNReal → NNReal → ℝ := fun t s =>
    if s ≤ t then K s (L s) (X s-L s) else 0
  let δ : ℝ := ε / ((S.card : ℝ)+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsingle (s : NNReal) (hs : s ∈ S) :
      ∀ᶠ n : ℕ in atTop, ∀ t ≤ T, |C n t (j s n)-A t s| < δ :=
    Kyprianou.Ch04.ito43_cutoff_selected_cell_uniform X L hCad hLeft
      K hK ρ hρ hzero T s (hS s hs).1 (hS s hs).2 (j s)
      (hj.mono fun n hn => hn s hs) δ hδ
  have hall : ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ S, ∀ t ≤ T, |C n t (j s n)-A t s| < δ := by
    have haux : ∀ R : Finset NNReal, R ⊆ S →
        ∀ᶠ n : ℕ in atTop, ∀ s ∈ R, ∀ t ≤ T, |C n t (j s n)-A t s| < δ := by
      intro R
      induction R using Finset.induction_on with
      | empty => simp
      | @insert a R ha ih =>
        intro hsub
        have haS := hsub (Finset.mem_insert_self a R)
        have hRS : R ⊆ S := fun b hb => hsub (Finset.mem_insert_of_mem hb)
        filter_upwards [hsingle a haS, ih hRS] with n h1 h2
        intro b hb
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact h1
        · exact h2 b hb
    exact haux S (Finset.Subset.refl S)
  filter_upwards [hall,hgrid] with n hn hg
  intro t ht
  change |(∑ k ∈ Finset.range n, C n t k) -
    (∑' s : Ioc (0 : NNReal) t, K s.1 (L s.1) (X s.1-L s.1))| < ε
  rw [hg t ht,hjump t ht,← Finset.sum_sub_distrib]
  calc
    |∑ s ∈ S, (C n t (j s n)-A t s)| ≤
        ∑ s ∈ S, |C n t (j s n)-A t s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ S, δ := Finset.sum_le_sum (fun s hs => (hn s hs t ht).le)
    _ = (S.card : ℝ)*δ := by simp
    _ < ε := by
      dsimp [δ]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith
