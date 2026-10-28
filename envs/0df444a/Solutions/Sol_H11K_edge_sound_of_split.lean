-- Prove2me | solution 1 for H11K.edge_sound_of_split
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:39:47.251121+00:00
-- url     : https://prove2.me/submissions/1bdb8fab-11bd-4258-9f5e-95d2fbde7549

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_H11K_EdgeSplit
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Arb4_edgeOK_sound
namespace Arb4
end Arb4
namespace Arb4.Q
end Arb4.Q
/-  H11K_EdgeSplit.lean -- lane H11K: the Arb4 edge checker `Arb4.edgeOK` assembled from one
    kernel check PER OCTANT PIECE.

    `Arb4.edgeOK` is one Boolean per edge, checked by ONE `decide +kernel`; the Arb4 lane measured its
    memory at about 19 GB for an edge at height 1e4 (25 pieces, EM cut N = 0.3 T).  Here the piece
    conjunct of `edgeOK` is split off:

      * `pieceJ E j`   -- piece `j`: `Arb4.pieceOK` and both breakpoints inside its radius;
      * `edgeRest E`   -- everything else in `edgeOK` (label steps, endpoints, the two endpoint boxes
                          with their corners, the final `π` / `arctan` inequalities);
      * `edgeOK_of_split` -- `edgeRest E = true` and `pieceJ E j = true` for every `j < E.m` give
                          `edgeOK E = true`, hence `Arb4.edgeOK_sound`.

    Each `pieceJ E j` is then one small `decide +kernel` (one evaluator run of N terms).
    Trust: proved from its stated hypotheses; axioms within [propext, Classical.choice, Quot.sound]
    (H11K_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


open Complex

namespace H11K

open Arb4 Arb4.Q





/-- **`edgeOK` from its split checks.** -/
theorem edgeOK_of_split (E : EdgeD) (hr : edgeRest E = true)
    (hp : ∀ j, j < E.m → pieceJ E j = true) : edgeOK E = true := by
  simp only [edgeRest, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, htn⟩, hx0⟩, hxm⟩, hsteps⟩, hc0⟩, hc1⟩, hb0⟩, hb1⟩, hlo⟩, hhi⟩ := hr
  have hpcs : (List.range E.m).all (fun j => pieceOK E.tn E.tq E.N E.L (E.pc j) &&
      inRad (E.x j) (E.pc j) && inRad (E.x (j + 1)) (E.pc j)) = true := by
    rw [List.all_eq_true]
    intro j hj
    exact hp j (List.mem_range.mp hj)
  simp only [edgeOK, hm, htn, hx0, hxm, hpcs, hsteps, hc0, hc1, hb0, hb1, hlo, hhi, Bool.and_self]



end H11K


/-  H11K_EdgeSplit.lean -- lane H11K: the Arb4 edge checker `Arb4.edgeOK` assembled from one
    kernel check PER OCTANT PIECE.

    `Arb4.edgeOK` is one Boolean per edge, checked by ONE `decide +kernel`; the Arb4 lane measured its
    memory at about 19 GB for an edge at height 1e4 (25 pieces, EM cut N = 0.3 T).  Here the piece
    conjunct of `edgeOK` is split off:

      * `pieceJ E j`   -- piece `j`: `Arb4.pieceOK` and both breakpoints inside its radius;
      * `edgeRest E`   -- everything else in `edgeOK` (label steps, endpoints, the two endpoint boxes
                          with their corners, the final `π` / `arctan` inequalities);
      * `edgeOK_of_split` -- `edgeRest E = true` and `pieceJ E j = true` for every `j < E.m` give
                          `edgeOK E = true`, hence `Arb4.edgeOK_sound`.

    Each `pieceJ E j` is then one small `decide +kernel` (one evaluator run of N terms).
    Trust: proved from its stated hypotheses; axioms within [propext, Classical.choice, Quot.sound]
    (H11K_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


open Complex

section
namespace H11K
end H11K
open H11K

open Arb4 Arb4.Q








theorem solution (E : EdgeD) (hr : edgeRest E = true)
    (hp : ∀ j, j < E.m → pieceJ E j = true) :
    DiffractionCore.argChangeHoriz riemannZeta E.T 2 (-1) ∈ Set.Icc E.Lo.val E.Hi.val :=
  edgeOK_sound E (edgeOK_of_split E hr hp)
