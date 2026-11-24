-- Prove2me | solution 1 for GlobalTheory.CuspGL.mangoldt_conv_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:04:32.685299+00:00
-- url     : https://prove2.me/submissions/27ebcabb-73b4-44c3-b3c5-6e56dc1fd859

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne
import Theorems.Thm_GlobalTheory_CuspGL_mangoldt_pow
import Theorems.Thm_GlobalTheory_CuspGL_mangoldt_eq_zero
import Theorems.Thm_GlobalTheory_CuspGL_conv_const_one_eq_divisorSum
import Theorems.Thm_GlobalTheory_CuspGL_IsAdditive_eq_divisorSum_mangoldt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]
namespace GlobalTheory.CuspGL
theorem _root_.solution : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s →
    (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧
    (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧
    ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) →
      mangoldt s P = 0 := by
  intro F _ s hs
  refine ⟨fun P hP => ?_, mangoldt_pow s, mangoldt_eq_zero s⟩
  rw [conv_const_one_eq_divisorSum _ P hP]
  exact hs.eq_divisorSum_mangoldt P hP
end GlobalTheory.CuspGL
