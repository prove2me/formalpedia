-- Prove2me | solution 1 for GlobalTheory.KSp.exists_translate_inCell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:49.005024+00:00
-- url     : https://prove2.me/submissions/738bf887-b60a-4aec-8eb1-cbf674417fec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InCellIffDetNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianSplitUnitaryLowerBlockInvertibleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsTranslateInCell
import Theorems.Thm_GlobalTheory_KSp_exists_herm_transversal
import Theorems.Thm_GlobalTheory_T_inCell_iff_det_lower_left_block_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory GlobalTheory.KSp
namespace GlobalTheory.KSp
theorem _root_.solution : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))),
    ∃ u : UG c (stdJ ν E), ∀ g ∈ s, InCell c (g * u) := by
  intro F _ _ E _ _ c δ hE ν _ _ s
  obtain ⟨t, ht, h⟩ := exists_herm_transversal F E c δ hE ν s
  let u : UG c (stdJ ν E) :=
    ⟨⟨fromBlocks 1 0 t 1, fromBlocks 1 0 (-t) 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩, by
      rw [mem_UG_iff]
      have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
      have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
      simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h0, h1, ht]⟩
  refine ⟨u, fun g hg => (GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero F E c δ hE ν _).mpr ?_⟩
  have e : mat c (g * u) = mat c g * fromBlocks 1 0 t 1 := rfl
  rw [e, ← fromBlocks_toBlocks (mat c g), fromBlocks_multiply, toBlocks_fromBlocks₂₁, Matrix.mul_one]
  exact h g hg
end GlobalTheory.KSp
