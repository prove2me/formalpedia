-- Prove2me | solution 1 for GlobalTheory.AnArc.differentiable_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:56:27.343437+00:00
-- url     : https://prove2.me/submissions/d0a31b0b-eb49-4fde-bf12-6a2803e9440b

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
theorem _root_.solution (j : ℕ) (α : A.X) {th : (Fin A.gB → ℂ) → ℂ} (h : Differentiable ℂ th) (μ : A.X) :
    Differentiable ℂ (A.term j α th μ) := by
  have h1 : Differentiable ℂ fun v : A.V => v.1 (α + j • μ) :=
    (A.evalCLM (α + j • μ)).differentiable.comp differentiable_fst
  unfold term eTwoPi
  fun_prop
end GlobalTheory.AnArc
