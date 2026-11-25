-- Prove2me | solution 1 for GlobalTheory.Models.one_le_w_and_wst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:21:16.103887+00:00
-- url     : https://prove2.me/submissions/f9e265b0-888e-4805-977d-57824b873699

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
variable {l n : ℕ} {R : RingPG k l}
namespace GlobalTheory.Models
theorem _root_.solution {r : ℕ} (Dt : TopData n r) (i : ZMod n) : 1 ≤ Dt.w i ∧ 1 ≤ Dt.wst i := by
  have h1 := Dt.one_le_letterBlockLength
  have h := Dt.range i (Dt.w i) (Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩)))
  exact ⟨h.1, by rw [TopData.wst]; omega⟩
end GlobalTheory.Models
