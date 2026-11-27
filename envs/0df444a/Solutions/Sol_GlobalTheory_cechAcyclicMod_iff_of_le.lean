-- Prove2me | solution 1 for GlobalTheory.cechAcyclicMod_iff_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:42.228204+00:00
-- url     : https://prove2.me/submissions/8651f743-99f4-4fed-8fbc-86df3875bfde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic

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
namespace GlobalTheory
theorem _root_.solution (h : ∀ i, U i ≤ V) : CechAcyclicMod V U F ↔
    ∀ s : Finset ι, s.Nonempty → ∀ q, 0 < q → Subsingleton (cohOn F (⨅ i ∈ s, U i) q) := by
  refine forall₂_congr fun s hs => ?_
  rw [cechOpen_of_nonempty h hs]
  exact ⟨fun H q hq => by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hq.ne'
    exact H q, fun H q => H _ q.succ_pos⟩
end GlobalTheory
