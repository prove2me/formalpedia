-- Prove2me | solution 1 for Kyprianou.Ch04.positiveRootSequenceWhLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:49:59.71085+00:00
-- url     : https://prove2.me/submissions/d3f892ad-7dce-4676-bfa1-ceaced973f2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_Kyprianou_Ch03_exercise35LaplaceExponentRegularity
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch04_positiveRootQuotientSecantLimit
import Theorems.Thm_Kyprianou_Ch04_whRatioLimitOfRootQuotient
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Positive roots give the limiting nonsingular Wiener–Hopf quotient. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (hNotNegativeSubordinator : ¬ (∀ᵐ w : Ω ∂P, Antitone (fun t : NNReal => L.X t w)))
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hq0 : Tendsto q atTop (nhds 0))
    (beta : ℝ) (hpsi : L.ψ beta ≠ 0) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ (∀ n, L.ψ (r n) = q n) ∧
      Tendsto (fun n => (q n / r n) * ((r n-beta)/(q n-L.ψ beta))) atTop
        (nhds (max 0 (sInf ((fun theta : ℝ => L.ψ theta / theta) '' Ioi 0)) * beta / L.ψ beta)) := by
  let : IsProbabilityMeasure P := L.isProbability
  let m := max 0 (sInf ((fun theta : ℝ => L.ψ theta / theta) '' Ioi 0))
  obtain ⟨hzero,_,hconv,_,_⟩ := Kyprianou.Ch03.exercise35LaplaceExponentRegularity P F L
  have hmono : MonotoneOn (fun x : ℝ => L.ψ x / x) (Ioi 0) := by
    intro x hx y hy hxy
    have hx' : 0 < x := hx
    have hy' : 0 < y := hy
    simpa only [hzero,sub_zero] using
      hconv.secant_mono (show (0 : ℝ) ∈ Ici 0 by simp)
        hx'.le hy'.le hx'.ne' hy'.ne' hxy
  have hroots (n : ℕ) : ∃ r : ℝ, 0 < r ∧ L.ψ r = q n := by
    obtain ⟨r,hr,hroot,_⟩ :=
      Kyprianou.Ch03.firstPassageTransform_maximalRootExistence P F L hNotNegativeSubordinator (q n) (hq n).le
    refine ⟨r,lt_of_le_of_ne hr ?_,hroot⟩
    intro he
    rw [← he,hzero] at hroot
    exact (hq n).ne' hroot.symm
  choose r hr hroot using hroots
  have hquot := Kyprianou.Ch04.positiveRootQuotientSecantLimit L.ψ hmono q r hq hr hroot hq0
  have hW := Kyprianou.Ch04.whRatioLimitOfRootQuotient q r beta m (L.ψ beta) hr hpsi hq0 hquot
  exact ⟨r,hr,hroot,hW⟩
