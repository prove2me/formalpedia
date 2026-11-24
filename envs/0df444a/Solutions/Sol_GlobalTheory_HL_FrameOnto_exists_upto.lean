-- Prove2me | solution 1 for GlobalTheory.HL.FrameOnto.exists_upto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:07:03.514799+00:00
-- url     : https://prove2.me/submissions/b749c8fc-4a96-403f-8ba6-462e90d3554f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Theorems.Thm_GlobalTheory_HL_FrameOnto_spanTo_mono
import Theorems.Thm_GlobalTheory_HL_FrameOnto_mem_spanTo
import Theorems.Thm_GlobalTheory_HL_FrameOnto_exists_step
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameOnto
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (T : Fˣ)
  (gram : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0)
  (dual : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
include gram dual
namespace GlobalTheory.HL.FrameOnto
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (x : Fin (r + 1) → S.V)
    (hx : ∀ j : Fin (r + 1), x j ∈ S.spanTo g j) (m : ℕ) :
    ∃ n ∈ S.Nof g, ∀ j : Fin (r + 1), n (g j) = if (j : ℕ) < m then g j + x j else g j := by
  induction m with
  | zero => exact ⟨1, one_mem _, fun j => by simp⟩
  | succ m ih =>
    obtain ⟨n, hn, h⟩ := ih
    by_cases hm : m < r + 1
    · obtain ⟨e, he, h1, h2, h3⟩ := exists_step S g gs T gram dual ⟨m, hm⟩ _ (hx ⟨m, hm⟩)
      refine ⟨e * n, mul_mem he hn, fun j => ?_⟩
      change e (n (g j)) = _
      rw [h]
      rcases lt_trichotomy (j : ℕ) m with hj | hj | hj
      · rw [if_pos hj, if_pos (by omega)]
        exact h3 _ (add_mem (mem_spanTo S g hj) (spanTo_mono S g hj.le (hx j)))
      · obtain rfl : j = ⟨m, hm⟩ := Fin.ext hj
        rw [if_neg (by simp), if_pos (by simp), h1]
      · rw [if_neg (by omega), if_neg (by omega)]
        exact h2 j fun hh => by rw [hh] at hj; simp at hj
    · refine ⟨n, hn, fun j => ?_⟩
      have := j.2
      rw [h, if_pos (by omega), if_pos (by omega)]
end GlobalTheory.HL.FrameOnto
