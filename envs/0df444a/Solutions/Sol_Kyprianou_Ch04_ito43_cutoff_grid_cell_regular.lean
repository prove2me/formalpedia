-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_grid_cell_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:14:20.512382+00:00
-- url     : https://prove2.me/submissions/69f83311-b470-4868-a73e-e0649b4a8842

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_exercise41PathCompactV10
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
    (n k : ℕ) :
    let u : ℕ → NNReal := fun i => T*(i:NNReal)/(n:NNReal)
    let F : NNReal → ℝ := fun t =>
      K (u k) (X (u k)) (X (min t (u (k+1)))-X (min t (u k)))
    (∀ t, ContinuousWithinAt F (Ici t) t) ∧
      ∃ M : ℝ, ∀ t ≤ T, |F t| ≤ M := by
  intro u F
  let G : ℝ → ℝ := fun z => K (u k) (X (u k)) z
  have hG : Continuous G :=
    hK.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  have hc (a t : NNReal) : ContinuousWithinAt (fun s => X (min s a)) (Ici t) t := by
    have hm : Continuous (fun s : NNReal => min s a) := continuous_id.min continuous_const
    have hmap : MapsTo (fun s : NNReal => min s a) (Ici t) (Ici (min t a)) :=
      by
        intro s hs
        change min t a ≤ min s a
        exact min_le_min (show t ≤ s from hs) le_rfl
    exact ((hCad (min t a)).1).comp (f := fun s : NNReal => min s a)
      hm.continuousWithinAt hmap
  constructor
  · intro t
    exact hG.continuousAt.comp_continuousWithinAt ((hc (u (k+1)) t).sub (hc (u k) t))
  · obtain ⟨_,R,hR,hX,_⟩ :=
      Kyprianou.Ch04.exercise41PathCompactV10 (fun t (_ : Unit) => X t)
        (fun t (_ : Unit) => L t) () hCad hLeft T
    obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (-2*R) (2*R))).bddAbove_image
      hG.abs.continuousOn
    refine ⟨M,fun t ht => ?_⟩
    apply hM
    let z := X (min t (u (k+1)))-X (min t (u k))
    have hz : |z| ≤ 2*R := by
      have ha := hX (min t (u (k+1))) ((min_le_left _ _).trans ht)
      have hb := hX (min t (u k)) ((min_le_left _ _).trans ht)
      have hh := abs_sub_le (X (min t (u (k+1)))) 0 (X (min t (u k)))
      simp only [sub_zero,zero_sub,abs_neg] at hh
      exact hh.trans (by linarith)
    exact ⟨z,by constructor <;> linarith [abs_le.mp hz],rfl⟩
