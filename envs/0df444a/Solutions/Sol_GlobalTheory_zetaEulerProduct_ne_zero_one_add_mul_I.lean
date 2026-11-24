-- Prove2me | solution 1 for GlobalTheory.zetaEulerProduct_ne_zero_one_add_mul_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:42:32.078263+00:00
-- url     : https://prove2.me/submissions/e36fd9cf-3172-4401-a1cf-e85cda5dbfd5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ZetaEulerProductNeZeroOneAddMulI
import Theorems.Thm_GlobalTheory_conj_apply_conj_of_entire
import Theorems.Thm_GlobalTheory_LogEulerSeries_hasSum_log_zeta_sq_mul
import Theorems.Thm_GlobalTheory_conj_neg_log_euler_factor
import Theorems.Thm_GlobalTheory_landau_exp_summable
import Theorems.Thm_GlobalTheory_not_summable_two_add_two_re_pow_div


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) (N : ι → ℕ), (∀ i, 2 ≤ N i) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z : ℂ → ℂ, Differentiable ℂ Z → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → ∀ t : ℝ, t ≠ 0 → Z (1 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro ι N hN hsum hne Z hZ hZs t ht ha
  obtain ⟨i₀⟩ := hne
  have hpos : ∀ i, 0 < N i := fun i => by have := hN i; omega
  have hN0 : ∀ i, ((N i : ℕ) : ℂ) ≠ 0 := fun i => by exact_mod_cast (hpos i).ne'
  have hconj : ∀ s, starRingEnd ℂ (Z (starRingEnd ℂ s)) = Z s := by
    refine conj_apply_conj_of_entire Z hZ fun s hs => ?_
    have hs' : 1 < (starRingEnd ℂ s).re := by simpa using hs
    rw [hZs _ hs', hZs s hs, map_mul, map_sub, Complex.conj_conj, map_one, ← Complex.exp_conj,
      Complex.conj_tsum]
    simp only [conj_neg_log_euler_factor _ (hN _) 1 (by simp) s hs, map_one]
  set u : ℂ := (t : ℂ) * Complex.I with hu
  have hu0 : u ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have hure : u.re = 0 := by simp [hu]
  have huc : starRingEnd ℂ u = -u := by simp [hu]
  have hb : Z (1 - u) = 0 := by
    rw [← hconj, map_sub, map_one, huc, sub_neg_eq_add, ha, map_zero]
  have hds : ∀ (f : ℂ → ℂ) (a : ℂ), Differentiable ℂ f → Differentiable ℂ (dslope f a) := by
    intro f a hf
    rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
    exact hf.differentiableOn
  have hmul : ∀ (f : ℂ → ℂ) (a : ℂ), f a = 0 → ∀ s, (s - a) * dslope f a s = f s := by
    intro f a h0 s
    have := sub_smul_dslope f a s
    rw [smul_eq_mul, h0, sub_zero] at this
    exact this
  have hD1 := hds Z (1 + u) hZ
  have hD2 := hds Z (1 - u) hZ
  have hG := hds _ (1 - u) hD1
  have hD1b : dslope Z (1 + u) (1 - u) = 0 := by
    have := hmul Z (1 + u) ha (1 - u)
    rw [hb, mul_eq_zero] at this
    refine this.resolve_left fun h => hu0 ?_
    linear_combination (-1 / 2 : ℂ) * h
  set c : ι → ℂ := fun i => ((N i : ℕ) : ℂ) ^ (-u) with hcdef
  have hc : ∀ i, ‖c i‖ ≤ 1 := fun i => by
    simp only [hcdef]
    rw [Complex.norm_natCast_cpow_of_pos (hpos i), Complex.neg_re, hure]
    simp
  have hcc : ∀ i, starRingEnd ℂ (c i) = ((N i : ℕ) : ℂ) ^ u := fun i => by
    have harg' : ((N i : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
    have := Complex.cpow_conj ((N i : ℕ) : ℂ) (-u) harg'
    rw [map_neg, huc, neg_neg, map_natCast] at this
    exact this.symm
  have key := GlobalTheory.landau_exp_summable (ι × ℕ)
    (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1))
    (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1))
    (fun s => Z s * dslope (dslope Z (1 + u)) (1 - u) s * dslope Z (1 + u) (s + u) *
      dslope Z (1 - u) (s - u))
    (fun p => by
      have hw : ‖c p.1 ^ (p.2 + 1)‖ ≤ 1 := by
        rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hc _)
      have h1 := Complex.abs_re_le_norm (c p.1 ^ (p.2 + 1))
      have h2 := neg_abs_le (c p.1 ^ (p.2 + 1)).re
      apply div_nonneg (by linarith) (by positivity))
    (fun p => mul_nonneg (by positivity) (Real.log_natCast_nonneg _))
    (((hZ.mul hG).mul (hD1.comp (differentiable_id.add_const u))).mul
      (hD2.comp (differentiable_id.sub_const u)))
    (fun s hs => by
      refine ⟨_, GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩
      have e1 : ∀ i, c i * ((N i : ℕ) : ℂ) ^ (-s) = 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)) := by
        intro i
        simp only [hcdef]
        rw [one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      have e2 : ∀ i, starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s) =
          1 * ((N i : ℕ) : ℂ) ^ (-(s - u)) := by
        intro i
        rw [hcc, one_mul, ← Complex.cpow_add _ _ (hN0 i)]
        congr 1; ring
      simp only [e1, e2]
      rw [Complex.exp_add, Complex.exp_add, two_mul, Complex.exp_add]
      have h0 := hZs s hs
      have h1 := hZs (s + u) (by simpa [hure] using hs)
      have h2 := hZs (s - u) (by simpa [hure] using hs)
      have g0 := hmul Z (1 + u) ha s
      have g0' := hmul _ (1 - u) hD1b s
      have g1 := hmul Z (1 + u) ha (s + u)
      have g2 := hmul Z (1 - u) hb (s - u)
      have n1 : s - 1 ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp at this; linarith
      have n2 : s - (1 + u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      have n3 : s - (1 - u) ≠ 0 := fun h => by
        have := congrArg Complex.re h
        simp [hure] at this; linarith
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s))) = E at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s + u)))) = E1 at *
      generalize Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-(s - u)))) = E2 at *
      generalize dslope (dslope Z (1 + u)) (1 - u) s = G at *
      generalize dslope Z (1 + u) (s + u) = A at *
      generalize dslope Z (1 - u) (s - u) = B at *
      have k0 : (s - (1 + u)) * (s - (1 - u)) * G = (s - 1) * E := by
        rw [← h0, ← g0, ← g0']; ring
      have k1 : (s - 1) * A = (s - (1 - u)) * E1 := by
        linear_combination g1 + h1
      have k2 : (s - 1) * B = (s - (1 + u)) * E2 := by
        linear_combination g2 + h2
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero n1 n2) n3)
      rw [h0]
      calc (s - 1) * (s - (1 + u)) * (s - (1 - u)) * ((s - 1) * E * G * A * B)
          = E * ((s - (1 + u)) * (s - (1 - u)) * G) * ((s - 1) * A) * ((s - 1) * B) := by ring
        _ = _ := by rw [k0, k1, k2]; ring)
  exact not_summable_two_add_two_re_pow_div (c i₀) (hc i₀) (key.prod_factor i₀)
end GlobalTheory
