-- Prove2me | solution 1 for GlobalTheory.IsAlgebraicIn.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:47.712794+00:00
-- url     : https://prove2.me/submissions/0dd5997f-1079-4bde-b615-73457baf848a

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
omit [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
namespace GlobalTheory
namespace IsAlgebraicIn
theorem _root_.solution {L : RigLB G} {y : Sp ℂ ⟶ S} {e : V → (Sp ℂ ⟶ G.left)} {θ : V → ℂ}
    {fr : L.L.ι → V → ℂ} (H : IsAlgebraicIn L y e θ fr) (h : V' → V) :
    IsAlgebraicIn L y (fun z => e (h z)) (fun z => θ (h z)) (fun j z => fr j (h z)) :=
  H.imp fun _ hs j z => hs j (h z)
end IsAlgebraicIn
end GlobalTheory
