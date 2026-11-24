-- Prove2me | solution 1 for GlobalTheory.AnArc.finrank_La
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:42:10.73298+00:00
-- url     : https://prove2.me/submissions/a587605d-b5ae-4392-9041-35676ca01a3e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution : Module.finrank ℤ A.La = Module.finrank ℝ A.V := by
  have h1 : Module.finrank ℤ (A.X →+ ℤ) = Module.finrank ℤ A.X := by
    rw [(addMonoidHomLequivInt ℤ (A := A.X) (B := ℤ)).finrank_eq]
    simp [Module.finrank_linearMap]
  have h2 : Module.finrank ℤ A.abelian₂ = 2 * A.gB := by
    rw [ZLattice.rank ℝ A.abelian₂, finrank_real_of_complex]; simp
  have h3 : Module.finrank ℝ A.V = 2 * Module.finrank ℂ A.V := by
    rw [← Module.finrank_mul_finrank ℝ ℂ A.V, Complex.finrank_real_complex]
  rw [A.laEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod, h1, h2, h3, finrank_V]; ring
end GlobalTheory.AnArc
