-- Prove2me | solution 1 for GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_le_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:48.32609+00:00
-- url     : https://prove2.me/submissions/12a91542-f932-4244-92a5-aea0e4cdc7ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrder
import Theorems.Thm_GlobalTheory_SchwartzTranslate_hasDerivAt_iteratedFDeriv_line
import Theorems.Thm_GlobalTheory_SchwartzTranslate_taylor_two


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
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : V) (f : 𝓢(V, ℂ)) (k n : ℕ) (t : ℝ) (ht : |t| ≤ 1) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f
        - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f)
      ≤ 2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k n
            (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f))
          + ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n
            (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f)))
        * t ^ 2 := by
  set f1 : 𝓢(V, ℂ) := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f with hf1
  set f2 : 𝓢(V, ℂ) := LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f1 with hf2
  have e1 : (fun y => fderiv ℝ f y a) = f1 := by
    funext y; rw [hf1, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have e2 : (fun y => fderiv ℝ f1 y a) = f2 := by
    funext y; rw [hf2, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have hn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have c1 : ContDiff ℝ ∞ f1 := f1.smooth'
  have ct : ContDiff ℝ ∞ (fun z => f (z + t • a)) := c0.comp (contDiff_id.add contDiff_const)
  have efun : ⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1)
      = (fun z => f (z + t • a)) - ⇑f - t • ⇑f1 := by
    funext z
    simp
  have eit : iteratedFDeriv ℝ n
      ⇑(SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f - (t : ℂ) • f1) x
      = iteratedFDeriv ℝ n f (x + t • a) - iteratedFDeriv ℝ n f x
        - t • iteratedFDeriv ℝ n f1 x := by
    rw [efun, iteratedFDeriv_sub_apply (f := (fun z => f (z + t • a)) - ⇑f) (g := t • ⇑f1)
      ((ct.sub c0).of_le hn).contDiffAt
      ((c1.const_smul t).of_le hn).contDiffAt,
      iteratedFDeriv_sub_apply (ct.of_le hn).contDiffAt (c0.of_le hn).contDiffAt,
      iteratedFDeriv_const_smul_apply (c1.of_le hn).contDiffAt, iteratedFDeriv_comp_add_right]
  have key := taylor_two (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f (x + s • a))
    (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f1 (x + s • a))
    (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f2 (x + s • a))
    (fun s => by
      have := hasDerivAt_iteratedFDeriv_line a n f c0 x s
      rw [e1] at this
      exact this.const_smul (‖x‖ ^ k))
    (fun s => by
      have := hasDerivAt_iteratedFDeriv_line a n f1 c1 x s
      rw [e2] at this
      exact this.const_smul (‖x‖ ^ k))
    (2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k n f2 + ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n f2))
    (fun s hs => by
      have hx : ‖x‖ ≤ ‖x + s • a‖ + ‖a‖ := by
        have h3 : ‖s • a‖ ≤ ‖a‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) hs
        have h4 := norm_sub_le (x + s • a) (s • a)
        rw [add_sub_cancel_right] at h4
        linarith
      have hp : ‖x‖ ^ k ≤ 2 ^ (k - 1) * (‖x + s • a‖ ^ k + ‖a‖ ^ k) :=
        (pow_le_pow_left₀ (norm_nonneg _) hx k).trans
          (add_pow_le (norm_nonneg _) (norm_nonneg _) k)
      have b1 := SchwartzMap.le_seminorm ℂ k n f2 (x + s • a)
      have b2 := SchwartzMap.le_seminorm ℂ 0 n f2 (x + s • a)
      rw [pow_zero, one_mul] at b2
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      calc _ ≤ 2 ^ (k - 1) * (‖x + s • a‖ ^ k + ‖a‖ ^ k)
              * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖ := by gcongr
        _ = 2 ^ (k - 1) * (‖x + s • a‖ ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖
              + ‖a‖ ^ k * ‖iteratedFDeriv ℝ n f2 (x + s • a)‖) := by ring
        _ ≤ _ := by gcongr) t ht
  simp only [zero_smul, add_zero] at key
  rw [smul_comm t, ← smul_sub, ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  rw [eit]
  exact key
end GlobalTheory.SchwartzTranslateUnif
