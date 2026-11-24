-- Prove2me | solution 1 for GlobalTheory.AnArc.term_add_P0_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:57:44.646636+00:00
-- url     : https://prove2.me/submissions/dc7e69a5-e5f3-42e6-9fa5-ed011db55ffe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero

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
attribute [instance] AnArc.acg AnArc.free AnArc.fin AnArc.mod AnArc.discrete
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (j : ℕ) (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (μ : A.X) (n : A.X →+ ℤ) (v : A.V) :
    A.term j α th μ (v + A.P0 (La.mk 0 n 0)) = A.term j α th μ v := by
  have h1 : (v + A.P0 (La.mk 0 n 0)).1 (α + j • μ) = v.1 (α + j • μ) + (n (α + j • μ) : ℤ) := by
    rw [Prod.fst_add, AddMonoidHom.add_apply, degeneratingTori_basePeriodMap_fst_apply]; simp
  have h2 : (v + A.P0 (La.mk 0 n 0)).2 = v.2 := by simp
  rw [term, term, h1, h2, e_add, e_intCast, mul_one]
end GlobalTheory.AnArc
