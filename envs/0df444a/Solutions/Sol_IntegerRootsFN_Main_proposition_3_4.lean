-- Prove2me | solution 1 for IntegerRootsFN.Main.proposition_3_4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:26.760858+00:00
-- url     : https://prove2.me/submissions/a57e1a7f-7c10-4be5-900b-c2257745a998
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ApproximationConstruction
import Theorems.Thm_IntegerRootsFN_Main_proposition_3_4_computation
import Theorems.Thm_IntegerRootsFN_Main_proposition_3_4_analysis

set_option autoImplicit false

open IntegerRootsFN.Main

theorem solution :
    ∃ M : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧ ∃ k l : ℕ,
    ∀ (d b : ℕ) (g : Polynomial ℤ), Valid g d b →
    ∃ (samples : Fin (d + 1) → ApproxGKR.GaussDyadic) (q : ℤ × ℤ)
      (B : ℕ) (ws : Fin d → ℤ × ℤ) (β : Fin d → GaussianRational),
      ApproximationTrace g d b samples q B ws β ∧
      (B : ℝ) ≤ C * approximationPrecision d b ∧
      CoversRoots (complexify g) (fun i => (β i).value) ∧
      logRootSize (fun i => (β i).value) ≤ rootSizeBound d b ∧
      (∑ i, ((β i).bitSize : ℝ)) ≤ softBound C k l d b ((d : ℝ) * (b + (d : ℝ))) ∧
      Runs M (polynomialWord g d b) (approximationOutputWord samples q B ws β)
        (softBound C k l d b ((d : ℝ) * (b + (d : ℝ)))) := by
  obtain ⟨M, C, hC, k, l, hcomp⟩ := IntegerRootsFN.Main.proposition_3_4_computation
  refine ⟨M, C, hC, k, l, ?_⟩
  intro d b g hg
  obtain ⟨samples, q, B, ws, β, hshift, hq, hclear, hfactor, hβ,
    hB, hsize, hrun⟩ := hcomp d b g hg
  obtain ⟨hnonzero, hcover, hlog⟩ :=
    IntegerRootsFN.Main.proposition_3_4_analysis d b g hg q B ws hq hclear hfactor
  refine ⟨samples, q, B, ws, β, ?_, hB, ?_, ?_, hsize, hrun⟩
  · exact ⟨hshift, hclear, hfactor, hnonzero, hβ⟩
  · simpa only [hβ] using hcover
  · simpa only [hβ] using hlog
