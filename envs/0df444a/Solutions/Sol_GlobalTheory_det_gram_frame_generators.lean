-- Prove2me | solution 1 for GlobalTheory.det_gram_frame_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:14:50.94832+00:00
-- url     : https://prove2.me/submissions/942cc447-ce5d-4430-8363-7da277614bf4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetUpdateRowLastSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramSumElimSmulSub
import Theorems.Thm_GlobalTheory_det_gram_sumElim_frames
import Theorems.Thm_GlobalTheory_det_gram_sumElim_smul_sub
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
      [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK →
      ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r _k : ℕ) (P : LocNG.FPair H r),
        (H.gram P.MMgen).det * algebraMap F E (LocNG.theta M) ^ (2 * (r + 1))
          = (-1) ^ (r + 1) * P.Gv := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r _ P
  unfold LocNG.FPair.MMgen HermSp.MMfam LocNG.theta
  cases hs : M.split with
  | none =>
    simp only [map_one, one_pow, mul_one]
    exact det_gram_sumElim_frames H P
  | some g =>
    simp only
    rw [det_gram_sumElim_smul_sub H, det_gram_sumElim_frames H P, mul_comm _ (algebraMap F E _ ^ _),
      ← mul_assoc, ← mul_pow, ← map_mul]
    have hq : ((g.q : 𝒪[F]) : F) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    rw [mul_inv_cancel₀ hq, map_one, one_pow, one_mul]
end GlobalTheory
