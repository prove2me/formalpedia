-- Prove2me | solution 1 for InvShareComp.Exog.lemma_A1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:53:25.745038+00:00
-- url     : https://prove2.me/submissions/98232933-966a-4ef1-9811-b2d23af3355f

import Mathlib
import Definitions.Def_InvShareComp_Exog_Model

open MeasureTheory Classical

open InvShareComp.Exog in
theorem solution (ν : Measure (ℝ × ℝ)) (hν : IsDemandLaw ν)
    (I : ℝ) (hI : I ∈ Set.Icc (0:ℝ) 1) (Z : ℝ → ℝ → ℝ) :
    (∫ ω, (if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2 then Z ω.1 ω.2 else 0) ∂ν
      = ∫ ω, (if 2 * I ≤ ω.2 ∧ ω.1 < 4 * I - ω.2 then Z ω.2 ω.1 else 0) ∂ν) ∧
    (∫ ω, (if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1 then Z ω.1 ω.2 else 0) ∂ν
      = ∫ ω, (if 2 * I ≤ ω.2 ∧ 4 * I - ω.2 ≤ ω.1 ∧ ω.1 < 2 * I then Z ω.2 ω.1 else 0) ∂ν) := by
  have hswap : ∀ g : ℝ × ℝ → ℝ, ∫ ω, g (ω.2, ω.1) ∂ν = ∫ ω, g ω ∂ν := by
    intro g
    have h := integral_map_equiv (μ := ν) (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) g
    have hm : Measure.map (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)) ν = ν := hν.exch
    rw [hm] at h
    rw [h]; rfl
  constructor
  · rw [← hswap (fun ω => if ω.2 < 2 * I ∧ 2 * I ≤ ω.1 ∧ ω.1 < 4 * I - ω.2 then Z ω.1 ω.2 else 0)]
    congr 1; funext ω
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1, by linarith⟩
  · rw [← hswap (fun ω => if ω.2 < 2 * I ∧ 4 * I - ω.2 ≤ ω.1 then Z ω.1 ω.2 else 0)]
    congr 1; funext ω
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith, h1⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h3, by linarith⟩
