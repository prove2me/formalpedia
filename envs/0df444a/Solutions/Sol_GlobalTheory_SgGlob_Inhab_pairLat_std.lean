-- Prove2me | solution 1 for GlobalTheory.SgGlob.Inhab.pairLat_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:59:34.517836+00:00
-- url     : https://prove2.me/submissions/eaeaa65c-e555-47bd-bb1c-4f91ba0edbd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
import Theorems.Thm_GlobalTheory_SgGlob_Inhab_frameLat_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SgGlob GlobalTheory.SgGlob.Inhab
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.SgGlob.Inhab
theorem _root_.solution {g : ℕ} (hg : g ≠ 0) :
    pairLat (r := 0) g (!![0; 1] : Matrix (Fin 2) (Fin (0 + 1)) E) !![(g : E); 1 + g] = std E := by
  have hg' : (g : E) ≠ 0 := Nat.cast_ne_zero.2 hg
  rw [pairLat, frameLat_zero, frameLat_zero, std, Submodule.span_insert]
  congr 3
  · ext i; fin_cases i <;> simp
  · ext i; fin_cases i <;> simp [hg']
end GlobalTheory.SgGlob.Inhab
