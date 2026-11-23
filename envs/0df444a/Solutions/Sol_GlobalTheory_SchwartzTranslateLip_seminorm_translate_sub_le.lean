-- Prove2me | solution 1 for GlobalTheory.SchwartzTranslateLip.seminorm_translate_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:23.680128+00:00
-- url     : https://prove2.me/submissions/2d68e510-e84b-4181-999b-c92e22c6a498

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap NNReal ContDiff
open GlobalTheory.Published.Metaplectic
open GlobalTheory GlobalTheory.SchwartzTranslateLip
namespace GlobalTheory.SchwartzTranslateLip
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K N k n : ℕ) (hk : k ≤ K) (hn : n ≤ N) (a : V) (f : 𝓢(V, ℂ)) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f)
      ≤ ‖a‖ * (1 + ‖a‖) ^ K * (2 ^ K *
        ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f) := by
  set B := 2 ^ K * ((Finset.Iic (K, N + 1)).sup fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x => ?_
  have c0 : ContDiff ℝ ∞ f := f.smooth'
  have hnn : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have ct : ContDiff ℝ ∞ (fun z => f (z + a)) := c0.comp (contDiff_id.add contDiff_const)
  have efun : ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) = (fun z => f (z + a)) - ⇑f := by
    funext z; simp
  have eit : iteratedFDeriv ℝ n ⇑(SchwartzMap.compSubConstCLM ℂ (-a) f - f) x
      = iteratedFDeriv ℝ n f (x + a) - iteratedFDeriv ℝ n f x := by
    rw [efun, iteratedFDeriv_sub_apply (ct.of_le hnn).contDiffAt (c0.of_le hnn).contDiffAt,
      iteratedFDeriv_comp_add_right]
  have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
    c0.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top n)
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ‖x‖ ^ k • iteratedFDeriv ℝ n f (x + s • a))
      (‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a) s := by
    intro s
    have hl : HasDerivAt (fun s : ℝ => x + s • a) a s := by
      simpa using ((hasDerivAt_id s).smul_const a).const_add x
    exact ((hd (x + s • a)).hasFDerivAt.comp_hasDerivAt s hl).const_smul (‖x‖ ^ k)
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖‖x‖ ^ k • fderiv ℝ (iteratedFDeriv ℝ n f) (x + s • a) a‖ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by
    intro s hs
    set y := x + s • a with hy
    have hsa : ‖s • a‖ ≤ ‖a‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    have hx : ‖x‖ ≤ ‖y‖ + ‖a‖ := by
      have h4 := norm_sub_le y (s • a)
      rw [show y - s • a = x by simp [hy]] at h4
      linarith
    have hx2 : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖y‖) := by
      nlinarith [norm_nonneg a, norm_nonneg y, mul_nonneg (norm_nonneg a) (norm_nonneg y)]
    have ha1 : 1 ≤ 1 + ‖a‖ := by linarith [norm_nonneg a]
    have hxk : ‖x‖ ^ k ≤ (1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k := by
      calc ‖x‖ ^ k ≤ ((1 + ‖a‖) * (1 + ‖y‖)) ^ k := pow_le_pow_left₀ (norm_nonneg _) hx2 k
        _ = (1 + ‖a‖) ^ k * (1 + ‖y‖) ^ k := mul_pow _ _ _
        _ ≤ _ := by gcongr
    have hop : ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖ := by
      rw [← norm_fderiv_iteratedFDeriv]; exact (fderiv ℝ (iteratedFDeriv ℝ n f) y).le_opNorm a
    have hS := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K, N + 1)) (k := k)
      (n := n + 1) hk (by simp; omega) f y
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ‖x‖ ^ k * ‖fderiv ℝ (iteratedFDeriv ℝ n f) y a‖
        ≤ ((1 + ‖a‖) ^ K * (1 + ‖y‖) ^ k) * (‖iteratedFDeriv ℝ (n + 1) f y‖ * ‖a‖) := by gcongr
      _ = ‖a‖ * (1 + ‖a‖) ^ K * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n + 1) f y‖) := by ring
      _ ≤ ‖a‖ * (1 + ‖a‖) ^ K * B := by gcongr
  have key := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := 0) (y := 1) (fun s _ => (hderiv s).hasDerivWithinAt) hbound (by simp) (by simp)
  simp only [zero_smul, add_zero, one_smul, sub_zero, norm_one, mul_one] at key
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)] at key
  rw [eit]
  exact key
end GlobalTheory.SchwartzTranslateLip
