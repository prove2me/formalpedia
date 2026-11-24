-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.separable_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:07:58.286811+00:00
-- url     : https://prove2.me/submissions/f51af627-b1f3-4bf4-b07e-b7289a9d9481

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q : MvPolynomial (Fin d) ℂ) (hq : Polynomial.C q ∈ Ideal.span {p, p.derivative})
    (x : Fin d → ℂ) (hx : MvPolynomial.eval x q ≠ 0) :
    (p.map (MvPolynomial.eval x)).Separable := by
  obtain ⟨a, b, h⟩ := Ideal.mem_span_pair.1 hq
  have h' := congrArg (Polynomial.map (MvPolynomial.eval x)) h
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at h'
  refine ⟨Polynomial.C (MvPolynomial.eval x q)⁻¹ * a.map (MvPolynomial.eval x),
    Polynomial.C (MvPolynomial.eval x q)⁻¹ * b.map (MvPolynomial.eval x), ?_⟩
  rw [Polynomial.derivative_map, mul_assoc, mul_assoc, ← mul_add, h', ← Polynomial.C_mul,
    inv_mul_cancel₀ hx, Polynomial.C_1]
end GlobalTheory.FiniteCoverGrowth
