-- Prove2me | solution 1 for GlobalTheory.cechHEquivCohOn_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:19.593954+00:00
-- url     : https://prove2.me/submissions/8f99801e-8540-46fe-abfa-c9ff1f90a566

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic
import Theorems.Thm_P2M_GlobalTheory_cechAbHEquivH__toCechAbH_41bd61f78311
import Theorems.Thm_P2M_GlobalTheory_toH__cechHEquivCohOn_d09ae21bbaab
import Theorems.Thm_GlobalTheory_cechAbHEquiv_toCechAbH


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
namespace GlobalTheory
theorem _root_.solution (hF : CechAcyclicMod V U F) :
    cechHEquivCohOn R hc hF 0 = cechHZeroEquivCohOn R F hc := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := (toCechH_bijective R F hc).2 x
  apply (cohOn.toH' F V 0).injective
  refine (congrArg (fun z => cohOn.toH' F V 0 (cechHEquivCohOn R hc hF 0 z))
    (cechAbHEquiv_toCechAbH R F V U y).symm).trans ((toH'_cechHEquivCohOn R hc hF 0 _).trans
      ((cechAbHEquivH'_toCechAbH (T := X.toPresheafedSpace.carrier) hc
        (cechAcyclicMod_iff.1 hF) _).trans ?_))
  rw [cechHZeroEquivCohOn, LinearEquiv.trans_apply, cechHZeroEquiv_toCechH]
  rfl
end GlobalTheory
