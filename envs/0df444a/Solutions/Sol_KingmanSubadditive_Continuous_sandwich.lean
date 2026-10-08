-- Prove2me | solution 1 for KingmanSubadditive.Continuous.sandwich
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T11:32:26.490408+00:00
-- url     : https://prove2.me/submissions/0258c290-95cd-4654-8de4-f7f4d6309b95

import Mathlib
import Definitions.Def_KingmanSubadditive_Continuous_Process



namespace KingmanSubadditive.Continuous

open MeasureTheory

/-- a single admissible pair inside `I` is bounded by the oscillation over `I`. -/
lemma abs_le_osc_toReal {S : Type*} [MeasurableSpace S]
    (x : ℝ → ℝ → S → ℝ) (I : Set ℝ) (ω : S)
    (hfinite : oscillation x I ω < ⊤)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s < t) (hsI : s ∈ I) (htI : t ∈ I) :
    |x s t ω| ≤ (oscillation x I ω).toReal := by
  have h1 : ENNReal.ofReal (|x s t ω|) ≤ oscillation x I ω := by
    unfold oscillation
    exact le_iSup₂ (f := fun (p : TimePair) (_ : p.1.1 ∈ I ∧ p.1.2 ∈ I) =>
      ENNReal.ofReal (|x p.1.1 p.1.2 ω|)) (⟨(s, t), hs, hst⟩ : TimePair) ⟨hsI, htI⟩
  have h2 := ENNReal.toReal_mono hfinite.ne h1
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at h2

theorem sandwich_core {S : Type*} [MeasurableSpace S]
    (P : Measure S) (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hnt : (n : ℝ) < t) (htn : t < (n : ℝ) + 1)
    (ω : S)
    (hfinite : oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω < ⊤) :
    x 0 ((n : ℝ) + 1) ω -
        (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal ≤
      x 0 t ω ∧
      x 0 t ω ≤ x 0 n ω +
        (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal := by
  obtain ⟨_, hsub, _, _, _⟩ := hproc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht0 : (0 : ℝ) < t := lt_trans hn0 hnt
  have hA := hsub 0 t ((n : ℝ) + 1) le_rfl ht0 htn ω
  have hB := hsub 0 n t le_rfl hn0 hnt ω
  have hC := abs_le_osc_toReal x _ ω hfinite t ((n : ℝ) + 1) ht0.le htn
    ⟨hnt.le, htn.le⟩ ⟨by linarith, le_rfl⟩
  have hD := abs_le_osc_toReal x _ ω hfinite n t hn0.le hnt
    ⟨le_rfl, by linarith⟩ ⟨hnt.le, htn.le⟩
  constructor
  · have := (abs_le.mp hC).2
    linarith
  · have := (abs_le.mp hD).2
    linarith

end KingmanSubadditive.Continuous

open KingmanSubadditive.Continuous
open MeasureTheory

theorem solution {S : Type*} [MeasurableSpace S]
    (P : Measure S) (x : ℝ → ℝ → S → ℝ)
    (hproc : IsProcess P x)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hnt : (n : ℝ) < t) (htn : t < (n : ℝ) + 1)
    (ω : S)
    (hfinite : oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω < ⊤) :
    x 0 ((n : ℝ) + 1) ω -
        (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal ≤
      x 0 t ω ∧
      x 0 t ω ≤ x 0 n ω +
        (oscillation x (Set.Icc (n : ℝ) ((n : ℝ) + 1)) ω).toReal := by
  exact sandwich_core P x hproc n hn t hnt htn ω hfinite
