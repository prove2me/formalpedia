-- Prove2me | solution 1 for GlobalTheory.SmoothedSumMellin.exists_entire_mellin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:19:39.35543+00:00
-- url     : https://prove2.me/submissions/85e00cac-35f6-4f98-83ab-5a25ed767c0b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum
import Theorems.Thm_GlobalTheory_SmoothedSumMellin_weight_mellinConvergent
import Theorems.Thm_GlobalTheory_SmoothedSumMellin_continuousOn_sum
import Theorems.Thm_GlobalTheory_SmoothedSumMellin_mellin_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Set Filter Asymptotics Topology
open GlobalTheory GlobalTheory.SmoothedSumMellin
namespace GlobalTheory.SmoothedSumMellin
theorem _root_.solution : ∀ (ι : Type) [Countable ι] (a : ι → ℂ) (N : ι → ℝ) (R : ℂ) (wt : ℝ → ℂ), ContDiff ℝ ∞ wt → (∃ a b : ℝ, 0 < a ∧ ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) → (∀ i, a i ≠ 0 → 1 ≤ N i) → (∀ σ : ℝ, 1 < σ → Summable fun i => ‖a i‖ * N i ^ (-σ)) → (∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' i, a i * wt (t * N i) - R / (t : ℂ)‖ ≤ C * t ^ A) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = R ∧ ∀ s : ℂ, 1 < s.re → Z s = mellin wt s * ((s - 1) * ∑' i, a i * (N i : ℂ) ^ (-s)) := by
  intro ι _ a N R wt hwt hsupp0 hN hsum hasym
  obtain ⟨α, β, hα, hsupp⟩ := hsupp0
  have hc : Continuous wt := hwt.continuous
  set F : ℝ → ℂ := fun t => ∑' i, a i * wt (t * N i) with hF
  set G : ℝ → ℂ := indicator (Ioc 0 1) (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) with hG
  set H : ℝ → ℂ := fun t => F t - R * G t with hH
  have hFtop : ∀ t, max β 1 < t → F t = 0 := by
    intro t ht
    have h1 : ∀ i, a i * wt (t * N i) = 0 := by
      intro i
      by_cases hai : a i = 0
      · rw [hai, zero_mul]
      · have hNi := hN i hai
        have hw0 : wt (t * N i) = 0 := by
          by_contra h
          have h2 := (hsupp _ h).2
          have h3 : t ≤ t * N i := le_mul_of_one_le_right (by linarith [le_max_right β 1]) hNi
          linarith [le_max_left β 1]
        rw [hw0, mul_zero]
    simp only [hF, h1, tsum_zero]
  have hFc : ContinuousOn F (Ioi 0) := continuousOn_sum hc hsupp hN (hsum 2 (by norm_num))
  have hGc : ContinuousOn (fun t : ℝ => R * (t : ℂ) ^ (-1 : ℂ)) (Ioi 0) := fun t ht =>
    (continuousAt_const.mul (ContinuousAt.cpow (Complex.continuous_ofReal.continuousAt (x := t))
      continuousAt_const (Complex.ofReal_mem_slitPlane.2 ht))).continuousWithinAt
  have hRGloc : LocallyIntegrableOn (fun t => R * G t) (Ioi 0) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro k hk hkc
    have h1 : IntegrableOn (fun t : ℝ => R * (t : ℂ) ^ (-1 : ℂ)) k :=
      (hGc.mono hk).integrableOn_compact hkc
    have h2 := h1.indicator (measurableSet_Ioc (a := (0 : ℝ)) (b := 1))
    refine h2.congr_fun (fun t _ => ?_) hkc.measurableSet
    simp only [hG, indicator]
    split_ifs <;> simp
  have hHloc : LocallyIntegrableOn H (Ioi 0) :=
    (hFc.locallyIntegrableOn measurableSet_Ioi).sub hRGloc
  have htop : ∀ c : ℝ, H =O[atTop] (· ^ c) := by
    intro c
    refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (max β 1)] with t ht
    have ht1 : t ∉ Ioc (0 : ℝ) 1 := fun h => by linarith [h.2, le_max_right β 1]
    simp only [hH, hFtop t ht, hG, Set.indicator_of_notMem ht1, mul_zero, sub_zero]
  have hbot : ∀ A : ℕ, H =O[𝓝[>] 0] (· ^ (A : ℝ)) := by
    intro A
    obtain ⟨C, hC⟩ := hasym A
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have ht0 : 0 < t := ht.1
    have hHt : H t = F t - R / t := by
      simp only [hH, hG, Set.indicator_of_mem ht, Complex.cpow_neg_one, div_eq_mul_inv]
    rw [hHt, Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg ht0.le A)]
    exact hC t ht0 ht.2
  have hbot' : ∀ s : ℂ, ∃ b : ℝ, b < s.re ∧ H =O[𝓝[>] 0] (· ^ (-b)) := by
    intro s
    refine ⟨-((⌈-s.re⌉₊ + 1 : ℕ) : ℝ), ?_, ?_⟩
    · push_cast
      linarith [Nat.le_ceil (-s.re)]
    · simpa only [neg_neg] using hbot (⌈-s.re⌉₊ + 1)
  have hHconv : ∀ s : ℂ, MellinConvergent H s := by
    intro s
    obtain ⟨b, hb, hbO⟩ := hbot' s
    exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := b) hHloc (htop _) (by linarith) hbO hb
  have hdiff : Differentiable ℂ (mellin H) := by
    intro s
    obtain ⟨b, hb, hbO⟩ := hbot' s
    exact mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := b) hHloc (htop _)
      (by linarith) hbO hb
  refine ⟨fun s => (s - 1) * mellin H s + R, ?_, by simp, ?_⟩
  · exact ((differentiable_id.sub_const 1).mul hdiff).add_const R
  · intro s hs
    have hs1 : s + -1 ≠ 0 := by
      intro h
      have : (s + -1).re = 0 := by rw [h]; simp
      simp at this
      linarith
    have hGm := hasMellin_cpow_Ioc (-1) (s := s) (by rw [Complex.neg_re, Complex.one_re]; linarith)
    have hGconv : MellinConvergent G s := hGm.1
    have hGval : mellin G s = 1 / (s + -1) := hGm.2
    have e1 : F = fun t => H t + R • G t := by
      funext t
      simp only [hH, smul_eq_mul]
      ring
    have hmF : mellin F s = mellin H s + R * (1 / (s + -1)) := by
      rw [e1, (hasMellin_add (hHconv s) (hGconv.const_smul R)).2, mellin_const_smul, hGval,
        smul_eq_mul]
    have hmel : mellin F s = mellin wt s * ∑' i, a i * (N i : ℂ) ^ (-s) :=
      mellin_sum (weight_mellinConvergent hc hα hsupp s) hN (hsum s.re hs)
    have hHs : mellin H s = mellin F s - R * (1 / (s + -1)) := by rw [hmF]; ring
    show (s - 1) * mellin H s + R = mellin wt s * ((s - 1) * ∑' i, a i * (N i : ℂ) ^ (-s))
    rw [hHs, hmel, ← sub_eq_add_neg]
    rw [← sub_eq_add_neg] at hs1
    field_simp
    ring
end GlobalTheory.SmoothedSumMellin
