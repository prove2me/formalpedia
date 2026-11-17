-- Prove2me | solution 1 for N25.canonicalConeDirectSumPolynomial25_coeff
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:44.410265+00:00
-- url     : https://prove2.me/submissions/cf0f7379-92c2-4c16-ba26-d40d2f13a4c6

import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalConePolynomial

/-! A graded polynomial representation of the canonical cone, normalized by A. -/

noncomputable section

universe u

namespace N25

open HomogeneousLocalization DirectSum

variable (K : Type u) [Field K]

/-- The coefficient of T^n remembers precisely the degree-n homogeneous component. -/
theorem _root_.solution (x : ⨁ n, canonicalConePiece25 K n) (n : ℕ) :
    (canonicalConeDirectSumPolynomial25 K x).coeff n = canonicalConeFractionPiece25 K n (x n) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i x =>
      rw [canonicalConeDirectSumPolynomial25, DirectSum.toSemiring_of]
      change (Polynomial.monomial i (canonicalConeFractionPiece25 K i x)).coeff n = _
      rw [Polynomial.coeff_monomial]
      by_cases h : i = n
      · subst i; simp
      · simp [h, DirectSum.of_eq_of_ne (β := fun n : ℕ => canonicalConePiece25 K n) i n x (Ne.symm h)]
  | add x y hx hy =>
      rw [map_add, Polynomial.coeff_add, hx, hy]
      change _ = canonicalConeFractionPiece25 K n (x n + y n)
      exact (map_add _ _ _).symm

end N25
