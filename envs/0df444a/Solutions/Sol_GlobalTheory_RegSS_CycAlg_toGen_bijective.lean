-- Prove2me | solution 1 for GlobalTheory.RegSS.CycAlg.toGen_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:29:42.105851+00:00
-- url     : https://prove2.me/submissions/80a6c885-a575-4edd-ae76-8555a8cc98e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_charpoly_dvd
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_exists_aeval
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_toGen_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open GlobalTheory GlobalTheory.RegSS GlobalTheory.RegSS.CycAlg
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.RegSS.CycAlg
theorem _root_.solution {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) :
    Function.Bijective (toGen M) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun l => ?_⟩
  · obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [toGen_mk] at hx
    rw [AdjoinRoot.mk_eq_zero]
    refine charpoly_dvd h ?_
    rw [← coe_aeval_gen, hx]
    exact Matrix.zero_mulVec v
  · obtain ⟨p, hp⟩ := exists_aeval l
    exact ⟨AdjoinRoot.mk _ p, Subtype.ext (by rw [toGen_mk, coe_aeval_gen, hp])⟩
end GlobalTheory.RegSS.CycAlg
