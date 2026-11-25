-- Prove2me | solution 1 for GlobalTheory.subsingleton_cohOn_of_cechAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:56:34.711136+00:00
-- url     : https://prove2.me/submissions/2f7a9c33-3c4e-4be1-a819-0e5ce88723c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
import Theorems.Thm_GlobalTheory_subsingleton_cechH


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}} {ι : Type}
variable {V : X.Opens} {U : ι → X.Opens} {F G : X.Modules}
variable [LinearOrder ι] (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable [Finite ι] (hc : V ≤ ⨆ i, U i)
omit [LinearOrder ι] [Finite ι]
include hc
namespace GlobalTheory
theorem _root_.solution [Fintype ι] (hF : CechAcyclicMod V U F) {n : ℕ}
    (hn : Fintype.card ι ≤ n) : Subsingleton (cohOn F V n) :=
  letI : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  haveI := subsingleton_cechH ℤ F V U hn
  (cechHEquivCohOn ℤ hc hF n).symm.injective.subsingleton
end GlobalTheory
