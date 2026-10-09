-- Prove2me | solution 1 for OAI.SevenEighths.ProbeEuler.pow_mul_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:34:01.600115+00:00
-- url     : https://prove2.me/submissions/b9d694dd-6b8b-4785-b99a-2a1387a6c77b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B000

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.HighRowsFirstTerms
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic ProbePrimePower
local notation "O" => ActualEisensteinCubic.O
variable (p : O)
  (hp : Prime p)
  [(Ideal.span {p}:Ideal O).IsMaximal]
  (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma pow_mul_sqrt_oai (Q : ℝ) (hQ : 0<Q) (n : ℕ) : Q^n*Real.sqrt Q=Q^((n:ℝ)+1/2) := by
  rw [Real.rpow_add hQ,Real.rpow_natCast,Real.sqrt_eq_rpow]

end SevenEighths.ProbeEuler
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbeEuler.pow_mul_sqrt_oai := @OAI.SevenEighths.ProbeEuler.pow_mul_sqrt_oai
