-- Prove2me | solution 1 for MIPStarRE.QPBT.directPolynomialAgreement_avg_le_mdq
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:28:22.922751+00:00
-- url     : https://prove2.me/submissions/136ce7b1-e286-4350-b3bf-5374f01dd676

-- Generated proof for MIPStarRE.QPBT.directPolynomialAgreement_avg_le_mdq.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_MIPStarRE_QPBT_directLdtPointNonempty

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Simultaneous polynomial measurements for the direct low-degree game

This module applies the quantum soundness theorem of the low individual
degree test to each coordinate of a projective strategy for the directly
indexed low-degree game, transports the Schwartz--Zippel collision estimate
to the direct polynomial representatives, and, for simultaneity parameter
`1`, obtains the polynomial-tuple conclusion of `lem:ld-soundness` from the
coordinate conclusions.

## The simultaneity obstruction

For simultaneity parameter `k ≥ 2` the coordinate conclusions alone do not
determine simultaneous polynomial measurements, so no palindromic combination
of the coordinate measurements can be consistent with a joint point
measurement in general.  Let `q = 2^s`, let the degree be `1`, and let Bob
measure the univariate polynomials `g = g₀ + g₁ x` once in the standard basis
`|g⟩` and once in the Fourier basis attached to the symmetric pairing
`⟨h, g⟩ = h₀ g₁ + h₁ g₀`.  In characteristic two every evaluation functional
`h ↦ h(u)` is represented by an isotropic vector of this pairing, so at every
point `u` the value-level coarse-grainings `Q^{1,u}_{[a]}` (Fourier basis) and
`Q^{2,u}_{[b]}` (standard basis) commute, and on the maximally entangled state
Alice may answer point questions with the joint projective measurement
`P^u_{a,b} = (Q^{1,u}_{[a]} Q^{2,u}_{[b]})ᵀ`.  All coordinate consistencies of
`lem:ld-soundness` then hold with defect `0` and distinct polynomials collide
at a uniform point with probability `1 / q`, but the sandwiched POVM has
`∑_{g₂(u) = b} |g₂⟩⟨g₂| Q^{1,u}_{[a]} |g₂⟩⟨g₂| = q⁻¹ Q^{2,u}_{[b]}`, whose
consistency defect against `P^u` is `1 - 1/q`; more strongly, every
polynomial-pair POVM on Bob's side has defect at least `1 - 2/q` against
`P^u`.  No bound of the form `C k √(δ + m d / q)` holds for a universal `C`.
The source obtains the general case not coordinatewise but by the combining
reduction of Theorem 4.43 in the NEEXP paper, which applies the `k = 1`
theorem once, in dimension `m + k`, to a combined strategy; that reduction is
not formalized here.  The two-measurement pasting estimate (Fact 4.35 there)
does not apply either, since it evaluates the two coordinates at
independently sampled points while the low-degree game evaluates all
coordinates at one point.  The counterexample and the resulting formal
status are recorded in `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:465-501`
* `references/neexp-paper/05_quantum_preliminaries.tex:912-1060` and `:1409-1503`
* `references/ldt-paper/test_definition.tex:180-202`
* `lem:ld-soundness` in `blueprint/src/chapter/ch13_qpbt_test.tex`
* `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
* `docs/paper-gaps/qpbt_ld-simultaneous-sandwich.tex`
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum



/-! ## Direct polynomial collision estimate -/

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (g g' : _root_.MIPStarRE.QPBT.PolyIndex D.m (_root_.MIPStarRE.QPBT.DirectScalarQ D) D.d) (hneq : g ≠ g') :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u g'.1 then
          (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) ≤
      (D.m * D.d : _root_.LIDT.MIPStarRE.LDT.Error) / D.q := by
  letI := D.toLDTFieldModel
  let gLdt := _root_.MIPStarRE.QPBT.directPolyEquivPolynomial D g
  let g'Ldt := _root_.MIPStarRE.QPBT.directPolyEquivPolynomial D g'
  have hneqLdt : gLdt ≠ g'Ldt := by
    intro heq
    exact hneq ((_root_.MIPStarRE.QPBT.directPolyEquivPolynomial D).injective heq)
  calc
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u => if MvPolynomial.eval u g.1 = MvPolynomial.eval u g'.1 then
          (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) =
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
        (fun u => if gLdt (_root_.MIPStarRE.QPBT.directPointEquiv D u) =
          g'Ldt (_root_.MIPStarRE.QPBT.directPointEquiv D u) then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) := by
            apply _root_.LIDT.MIPStarRE.LDT.avgOver_congr
            intro u
            simp only [gLdt, g'Ldt, _root_.MIPStarRE.QPBT.directPolyEquivPolynomial_apply]
            exact if_congr
              ((_root_.MIPStarRE.QPBT.directScalarEquiv D).injective.eq_iff.symm) rfl rfl
    _ = _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters))
        (fun u : _root_.LIDT.MIPStarRE.LDT.Point D.toLDTParameters =>
          if gLdt u = g'Ldt u then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) := by
      simpa using
        (_root_.LIDT.MIPStarRE.LDT.avgOver_uniform_equiv (_root_.MIPStarRE.QPBT.directPointEquiv D)
          (fun u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D =>
            if gLdt (_root_.MIPStarRE.QPBT.directPointEquiv D u) =
              g'Ldt (_root_.MIPStarRE.QPBT.directPointEquiv D u) then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0))
    _ ≤ (D.m * D.d : _root_.LIDT.MIPStarRE.LDT.Error) / D.q :=
      _root_.LIDT.MIPStarRE.LDT.Preliminaries.polynomialAgreement_avg_le_mdq D.toLDTParameters gLdt g'Ldt hneqLdt
