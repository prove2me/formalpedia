-- Prove2me | solution 1 for GlobalTheory.IdxInt.Model.cint_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:43:28.050469+00:00
-- url     : https://prove2.me/submissions/c377028f-466e-4080-84cc-907e5ce09559

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
import Theorems.Thm_GlobalTheory_IdxInt_Model_ratio_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory GlobalTheory.IdxInt GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt
variable {W : Type} [AddCommGroup W]
namespace GlobalTheory.IdxInt.Model
theorem _root_.solution {A B : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) :
    cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  have hn : Nice A φ := ⟨B, h⟩
  rw [cint, dif_pos hn]
  exact ratio_eq hn.choose_spec h
end GlobalTheory.IdxInt.Model
