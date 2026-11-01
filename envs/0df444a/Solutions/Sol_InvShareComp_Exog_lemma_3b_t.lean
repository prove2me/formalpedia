-- Prove2me | solution 1 for InvShareComp.Exog.lemma_3b_t
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T19:00:10.840991+00:00
-- url     : https://prove2.me/submissions/ca9053e5-1f4c-44b9-99d9-e0ccb82e83fb

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model
import Theorems.Thm_InvShareComp_Exog_proposition_1a

open MeasureTheory Classical

open InvShareComp.Exog in
theorem solution (P : Params) (hP : P.Standing) (ν : Measure (ℝ × ℝ)) (hν : IsDemandLaw ν)
    (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1) :
    AntitoneOn (fun t => sHat P ν t I) (Set.Icc 0 (P.cbar - P.δ)) := by
  have hP' := hP
  obtain ⟨hc0, hccb, hcbp, hk, hβ, hδ0, hδ⟩ := hP
  intro a ha b hb hab
  obtain ⟨ia, hW0, -⟩ := proposition_1a P hP' ν hν I hI a ha
  obtain ⟨ib, -, -⟩ := proposition_1a P hP' ν hν I hI b hb
  have hk2 : 0 < 2 * P.k := by linarith
  have e : sHat P ν a I - sHat P ν b I = 2 * (b - a) * P.β * Wval ν I / (2 * P.k) := by
    have : sHat P ν a I - sHat P ν b I
        = (sHat P ν a I - sHatN P ν I) - (sHat P ν b I - sHatN P ν I) := by ring
    rw [this, ia, ib]; field_simp; ring
  have : 0 ≤ 2 * (b - a) * P.β * Wval ν I / (2 * P.k) :=
    div_nonneg (mul_nonneg (mul_nonneg (by linarith) hβ) hW0) hk2.le
  show sHat P ν b I ≤ sHat P ν a I
  linarith
