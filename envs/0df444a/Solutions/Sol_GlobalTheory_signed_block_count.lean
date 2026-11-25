-- Prove2me | solution 1 for GlobalTheory.signed_block_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:51.392845+00:00
-- url     : https://prove2.me/submissions/244fcedc-ff93-4a33-b07f-742ec55c6f57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SignedBlockAntidiagWithLeadingMinorsEncardLe
import Theorems.Thm_GlobalTheory_SignedBlockCount_sign_ne
import Theorems.Thm_GlobalTheory_SignedBlockCount_count_lists
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory
open Formalism.MainNotions.S.Loc SignedBlockCount
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] (j : ℕ) (δ : ℕ → K), (({P : Matrix (Fin j) (Fin j) K | (∃ (w : Formalism.MainNotions.S.Loc.Pt K j) (sgn : Fin j → ℤˣ), ∀ a b, P a b = w.mat a b * ((sgn b : ℤ) : K)) ∧ ∀ (l : ℕ) (hl : l ≤ j), (P.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = δ l}).encard : ℕ∞) ≤ 8 ^ j := by
  intro K _ j δ
  choose T hT hT' using count_lists (K := K) j
  let η : (Fin j → ℤˣ) → ℕ → K := fun sgn l =>
    if hl : l ≤ j then δ l / ∏ b : Fin l, ((sgn (Fin.castLE hl b) : ℤ) : K) else 0
  let U : Finset (Matrix (Fin j) (Fin j) K) := Finset.univ.biUnion fun sgn : Fin j → ℤˣ =>
    (T (η sgn)).image fun bs => Matrix.of fun a b => ptEntryL bs a b * ((sgn b : ℤ) : K)
  have hU : U.card ≤ 8 ^ j := by
    refine (Finset.card_biUnion_le_card_mul _ _ (2 ^ j)
      fun sgn _ => Finset.card_image_le.trans (hT _)).trans ?_
    simp only [Finset.card_univ, Fintype.card_pi, Fintype.card_units_int, Finset.prod_const,
      Fintype.card_fin]
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) _
  refine (Set.encard_le_encard (t := (U : Set _)) ?_).trans ?_
  · rintro P ⟨⟨w, sgn, hP⟩, hδ⟩
    refine Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨sgn, Finset.mem_univ _,
      Finset.mem_image.2 ⟨w.blocks, hT' _ _ w.size fun l hl => ?_, ?_⟩⟩)
    · simp only [η, dif_pos hl]
      rw [eq_div_iff (Finset.prod_ne_zero_iff.2 fun b _ => sign_ne _), ← hδ l hl, mul_comm, minor,
        ← Matrix.det_mul_row]
      congr 1
      ext a b
      simp [hP, Pt.mat, mul_comm]
    · ext a b
      simp [hP, Pt.mat]
  · rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hU
end GlobalTheory
