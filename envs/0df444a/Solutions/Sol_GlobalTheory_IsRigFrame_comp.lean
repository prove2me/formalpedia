-- Prove2me | solution 1 for GlobalTheory.IsRigFrame.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:43.817056+00:00
-- url     : https://prove2.me/submissions/fb0b1126-80fd-4cdf-a14c-eccfb1e604c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_CoeffFSumDerivEqFderiv

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]
variable {V' : Type} [NormedAddCommGroup V'] [NormedSpace ℂ V']
namespace GlobalTheory
namespace IsRigFrame
theorem _root_.solution {L : RigLB G} {y : Sp ℂ ⟶ S} {e : V → (Sp ℂ ⟶ G.left)} {fr : L.L.ι → V → ℂ}
    (H : IsRigFrame L y e fr) (h : V' →L[ℂ] V) : IsRigFrame L y (fun z => e (h z)) (fun j z => fr j (h z)) :=
  ⟨fun j => (H.1 j).comp h.differentiable.differentiableOn fun _ hz => hz, fun j z => H.2.1 j (h z),
    fun j j' z => H.2.2.1 j j' (h z), fun j hj => by
      simp only [map_zero] at hj ⊢
      exact H.2.2.2 j hj⟩
end IsRigFrame
end GlobalTheory
