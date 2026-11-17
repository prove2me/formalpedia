-- Prove2me | solution 1 for Kyprianou.Ch07.kestenTruncatedTailIntegralMajorant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T03:20:05.723186+00:00
-- url     : https://prove2.me/submissions/83fa28f7-f12d-4746-b53a-187291e6fed0

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenTruncatedTailIntegralMajorant
    (G mu : Measure Real) (x T : Real) (hT : 0 < T)
    (C : ENNReal)
    (hMaj : ∀ y : Real, 0 < y →
      mu (Set.Ioi y) ≤ C * G (Set.Ioi y))
    (hMeas : Measurable (fun a : Real => G (Set.Ioi (x - a)))) :
    (∫⁻ a : Real in Set.Iic (x - T),
      mu (Set.Ioi (x - a)) ∂G) ≤
      C * (∫⁻ a : Real in Set.Iic (x - T),
        G (Set.Ioi (x - a)) ∂G) := by
  calc (∫⁻ a : Real in Set.Iic (x - T), mu (Set.Ioi (x - a)) ∂G)
      ≤ ∫⁻ a : Real in Set.Iic (x - T), C * G (Set.Ioi (x - a)) ∂G := by
        apply setLIntegral_mono' measurableSet_Iic
        intro a ha
        apply hMaj
        have : a ≤ x - T := ha
        linarith
    _ = C * (∫⁻ a : Real in Set.Iic (x - T), G (Set.Ioi (x - a)) ∂G) :=
        lintegral_const_mul C hMeas

theorem solution
    (G mu : Measure Real) (x T : Real) (hT : 0 < T)
    (C : ENNReal)
    (hMaj : ∀ y : Real, 0 < y →
      mu (Set.Ioi y) ≤ C * G (Set.Ioi y))
    (hMeas : Measurable (fun a : Real => G (Set.Ioi (x - a)))) :
    (∫⁻ a : Real in Set.Iic (x - T),
      mu (Set.Ioi (x - a)) ∂G) ≤
      C * (∫⁻ a : Real in Set.Iic (x - T),
        G (Set.Ioi (x - a)) ∂G) :=
  Kyprianou.Ch07.kestenTruncatedTailIntegralMajorant G mu x T hT C hMaj hMeas
