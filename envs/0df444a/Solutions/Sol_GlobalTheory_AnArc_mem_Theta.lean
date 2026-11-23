-- Prove2me | solution 1 for GlobalTheory.AnArc.mem_Theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:35.467438+00:00
-- url     : https://prove2.me/submissions/001fe66b-e4c2-4c2a-9187-8aa1daaf9b9f

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
theorem _root_.solution {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} : th ∈ A.Theta j α ↔
    Differentiable ℂ th ∧ ∀ (l : A.abelian₂) z, th (z + l) =
      (A.chi l * Complex.exp (Real.pi * A.H z l + Real.pi / 2 * A.H l l)) ^ j *
        Complex.exp (Real.pi * A.H (A.ct α) l) * th z := Iff.rfl
end GlobalTheory.AnArc
