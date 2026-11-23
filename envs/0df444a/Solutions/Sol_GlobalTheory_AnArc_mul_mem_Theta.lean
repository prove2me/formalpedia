-- Prove2me | solution 1 for GlobalTheory.AnArc.mul_mem_Theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:07.954094+00:00
-- url     : https://prove2.me/submissions/cdf9abb9-b6fa-4826-a166-16e1793522bf

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
theorem _root_.solution {j j' : ℕ} {α α' : A.X} {th th' : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α)
    (h' : th' ∈ A.Theta j' α') : th * th' ∈ A.Theta (j + j') (α + α') :=
  ⟨h.1.mul h'.1, fun l z => by
    simp only [Pi.mul_apply, h.2 l z, h'.2 l z, map_add, H_add_left, mul_add, Complex.exp_add]; ring⟩
end GlobalTheory.AnArc
