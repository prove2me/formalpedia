-- Prove2me | solution 1 for GlobalTheory.AnArc.Sum_add_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:29:58.418303+00:00
-- url     : https://prove2.me/submissions/15f2a4d7-d0c1-4a72-9834-9c0198ccf5ba

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv
import Theorems.Thm_GlobalTheory_AnArc_term_add_period

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
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
open AlgebraicGeometry CategoryTheory Limits
variable {O : Type} [CommRing O] [StarRing O] (A : _root_.GlobalTheory.AnArc O)
namespace GlobalTheory.AnArc
namespace _root_.GlobalTheory.AnArc
theorem _root_.solution {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) (w : ℂ)
    (la : A.La) (v : A.V) :
    A.Sum j α th w (v + A.Pw w la) = A.perFactor w la v ^ j * A.Sum j α th w v := by
  simp only [_root_.GlobalTheory.AnArc.Sum, A.term_add_period h w la]
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.addRight la.y).tsum_eq
    fun μ => A.term j α th μ v * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.eTwoPi (w * A.exponent j α μ)
end _root_.GlobalTheory.AnArc
end GlobalTheory.AnArc
