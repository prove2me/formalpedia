-- Prove2me | solution 1 for GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:51:56.58083+00:00
-- url     : https://prove2.me/submissions/1484c207-e24e-450b-adee-4715e38ca905

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrder
import Theorems.Thm_GlobalTheory_SchwartzTranslateUnif_seminorm_lineDerivOp_le
import Theorems.Thm_GlobalTheory_SchwartzTranslateUnif_seminorm_translate_sub_le_explicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
open GlobalTheory GlobalTheory.SchwartzTranslateUnif
open GlobalTheory.SchwartzTranslate
namespace GlobalTheory.SchwartzTranslateUnif
theorem _root_.solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : 𝓢(X, ℂ)) (k n : ℕ) : ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 →
      SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f
        - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by
  refine ⟨2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k (n + 2) f
    + SchwartzMap.seminorm ℂ 0 (n + 2) f), fun a ha => ?_⟩
  have h := seminorm_translate_sub_le_explicit a f k n 1 (by simp)
  simp only [one_smul, Complex.ofReal_one, one_pow, mul_one] at h
  refine h.trans ?_
  have hA : ∀ j, SchwartzMap.seminorm ℂ j n
      (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f))
      ≤ ‖a‖ ^ 2 * SchwartzMap.seminorm ℂ j (n + 2) f := by
    intro j
    calc _ ≤ ‖a‖ * SchwartzMap.seminorm ℂ j (n + 1) (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) :=
          seminorm_lineDerivOp_le a _ j n
      _ ≤ ‖a‖ * (‖a‖ * SchwartzMap.seminorm ℂ j (n + 1 + 1) f) := by
          gcongr; exact seminorm_lineDerivOp_le a f j (n + 1)
      _ = _ := by ring
  have hak : ‖a‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) ha
  have h0 := hA 0
  have hk := hA k
  have s0 : 0 ≤ SchwartzMap.seminorm ℂ 0 n
      (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f)) :=
    apply_nonneg _ _
  have hmul : ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n
      (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f))
      ≤ ‖a‖ ^ 2 * SchwartzMap.seminorm ℂ 0 (n + 2) f :=
    (mul_le_of_le_one_left s0 hak).trans h0
  calc _ ≤ 2 ^ (k - 1) * (‖a‖ ^ 2 * SchwartzMap.seminorm ℂ k (n + 2) f
          + ‖a‖ ^ 2 * SchwartzMap.seminorm ℂ 0 (n + 2) f) := by gcongr
    _ = _ := by ring
end GlobalTheory.SchwartzTranslateUnif
