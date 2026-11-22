-- Prove2me | solution 1 for LevyStochCalc.Ito.SecondMoment.integral_add_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-22T04:45:22.897815+00:00
-- url     : https://prove2.me/submissions/9cb52810-8fe1-42ca-a665-066d7177dc78

import Mathlib

open MeasureTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

theorem solution {a b c d : Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P)
    (hc : MemLp c 2 P) (hd : MemLp d 2 P) :
    ∫ ω, (a ω + b ω) * (c ω + d ω) ∂P
      = ∫ ω, a ω * c ω ∂P + ∫ ω, a ω * d ω ∂P + ∫ ω, b ω * c ω ∂P + ∫ ω, b ω * d ω ∂P := by
  have hac : Integrable (fun ω => a ω * c ω) P := ha.integrable_mul hc
  have had : Integrable (fun ω => a ω * d ω) P := ha.integrable_mul hd
  have hbc : Integrable (fun ω => b ω * c ω) P := hb.integrable_mul hc
  have hbd : Integrable (fun ω => b ω * d ω) P := hb.integrable_mul hd
  have h₁ : Integrable (fun ω => a ω * c ω + a ω * d ω) P := hac.add had
  have h₂ : Integrable (fun ω => a ω * c ω + a ω * d ω + b ω * c ω) P := h₁.add hbc
  calc
    _ = ∫ ω, ((a ω * c ω + a ω * d ω) + b ω * c ω) + b ω * d ω ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by ring
    _ = _ := by
      rw [integral_add h₂ hbd, integral_add h₁ hbc,
        integral_add hac had]
#print axioms solution
