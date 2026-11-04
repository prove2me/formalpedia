-- Prove2me | solution 1 for Light.fits_of_small
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:27:08.715292+00:00
-- url     : https://prove2.me/submissions/f3c0c577-a162-4e1e-ae1b-55e1ac80a31e

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Compiler_WholeProgram
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Machine_Solving
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Size
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_one_le_polyBound
import Definitions.Def_WeightedCache3SUM_Alias_a3d10551df69558f
import Theorems.Thm_Light_polyBound_mul

section
open ThreeSumApsp.WordRam
namespace Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
private theorem fits_of_lt {W : ℕ} {lim : Limits} {N Q B : ℕ} (hB : B ≤ 2 ^ W)
    (hword : 2 * (2 * lim.word + 2) < (B : ℤ)) (hspace : 2 * lim.space < B) (hstack : 4 * Q < B)
    (hpool : 2 * N < B) : Fits W lim N Q := by
  have hB' : (B : ℤ) ≤ (2 : ℤ) ^ W := by exact_mod_cast hB
  constructor <;> omega
section run
variable {W : ℕ} {lim : Limits} {μ : ℕ → ℤ}
end run
end Light
set_option autoImplicit false
section
open ThreeSumApsp.WordRam
open Light
open ThreeSumApsp Compiler
open EndStatement (exec loadWords)
namespace Light
theorem _root_.solution {W s k r b : ℕ} {params : List ℕ} {lim : Limits} (P : Program) (dec : Bool)
    (h : Small s k params lim) (hadm : Admissible b params W) (hr : params.length ≤ r)
    (hb : slopeOf P dec s k r ≤ b) : Fits W lim (dispPos P dec) (stackCells P lim) := by
  have hword := h.word
  have hspace := h.space
  have hdepth := h.depth
  set pb := polyBound s k params with hpb
  have hpb_pos : 1 ≤ pb := one_le_polyBound s k params
  -- the text's constant times the polynomial is below 2^W
  have hB : 2 ^ textBoundBits P dec * pb ≤ 2 ^ W := by
    rw [hpb, polyBound_mul]
    exact polyBound_le hadm hr (by unfold slopeOf at hb; omega)
  have hlt : textBound P dec * pb < 2 ^ textBoundBits P dec * pb :=
    Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) hpb_pos
  have htext : textBound P dec * pb
      = 32 * pb + 8 * ((frameSize P + 1) * pb) + 2 * (dispPos P dec * pb) := by
    unfold textBound; ring
  -- and each of the four numbers is below the text's constant times the polynomial
  have hstack : (frameSize P + 1) * (lim.depth + 1) ≤ 2 * ((frameSize P + 1) * pb) :=
    (Nat.mul_le_mul_left _ (by omega : lim.depth + 1 ≤ 2 * pb)).trans_eq (by ring)
  have hpool : dispPos P dec ≤ dispPos P dec * pb := Nat.le_mul_of_pos_right _ hpb_pos
  refine fits_of_lt hB ?_ ?_ ?_ ?_
  · -- 2 (2 word + 2) ≤ 4 pb + 4 ≤ 8 pb
    have : ((8 * pb : ℕ) : ℤ) < ((2 ^ textBoundBits P dec * pb : ℕ) : ℤ) := by
      exact_mod_cast (by omega : 8 * pb < 2 ^ textBoundBits P dec * pb)
    omega
  · -- 2 space ≤ 2 pb
    omega
  · -- 4 (4 + (F + 1) (depth + 1)) ≤ 16 pb + 8 (F + 1) pb
    unfold stackCells mainFrame
    omega
  · -- 2 N ≤ 2 N pb
    omega
end Light
