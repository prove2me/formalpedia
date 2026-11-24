-- Prove2me | solution 1 for GlobalTheory.RegSS.CycAlg.actOn_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:29:41.314625+00:00
-- url     : https://prove2.me/submissions/fea830fc-16b4-4e02-97ed-44ab04eb629b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_aeval_lowPoly_mulVec
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_charpoly_dvd
import Theorems.Thm_GlobalTheory_RegSS_CycAlg_exists_aeval

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
    Function.Bijective (actOn M v) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun l hl => ?_, fun w => ?_⟩
  · obtain ⟨p, hp⟩ := exists_aeval l
    have hl' : aeval M p *ᵥ v = 0 := by rw [hp]; exact hl
    obtain ⟨q, rfl⟩ := charpoly_dvd h hl'
    refine Subtype.ext ?_
    rw [← hp, map_mul, Matrix.aeval_self_charpoly, zero_mul]; rfl
  · refine ⟨aeval (gen M) (lowPoly ((krylov M v)⁻¹ *ᵥ w)), ?_⟩
    change ((aeval (gen M) _ : genAlg M) : Matrix n n A) *ᵥ v = w
    rw [coe_aeval_gen, aeval_lowPoly_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h,
      Matrix.one_mulVec]
end GlobalTheory.RegSS.CycAlg
