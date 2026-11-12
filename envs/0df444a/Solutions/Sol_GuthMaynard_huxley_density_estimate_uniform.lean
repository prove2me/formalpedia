-- Prove2me | solution 1 for GuthMaynard.huxley_density_estimate_uniform
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:55:17.638777+00:00
-- url     : https://prove2.me/submissions/7f702127-ece5-48b0-85d7-0384911c356a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_GuthMaynard_huxley_density_estimate_of_le_nine_elevenths
import Theorems.Thm_GuthMaynard_huxley_density_estimate_of_nine_elevenths_le
import Theorems.Thm_GuthMaynard_zeroDensityCount_eq_zero_vinogradov_korobov

section
open Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Hux.PartA
/-- ζ is analytic on ℂ ∖ {1}. -/
lemma hx_analyticOnNhd : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

end GuthMaynard.CitedZeros.Hux.PartA
end

section
open Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Hux.PartA
open GuthMaynard.CitedZeros.Hux
lemma hx_isConnected : IsConnected ({1}ᶜ : Set ℂ) :=
  isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1

lemma hx_order_ne_top {s : ℂ} (hs : s ≠ 1) : analyticOrderAt riemannZeta s ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine hx_analyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    hx_isConnected.isPreconnected h2 hs ?_
  rw [(hx_analyticOnNhd 2 h2).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
  exact ENat.zero_ne_top

lemma hx_zeros_locallyFinite (z : ℂ) :
    ∃ t ∈ 𝓝 z, (t ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  by_cases hz : z = 1
  · subst hz
    have hres := riemannZeta_residue_one
    have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
      have : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 :=
        hres.eventually_ne one_ne_zero
      exact this.mono fun s hs h => hs (by simp [h])
    rw [eventually_nhdsWithin_iff] at hev
    refine ⟨{s | s ∈ ({1}ᶜ : Set ℂ) → riemannZeta s ≠ 0}, hev, ?_⟩
    refine (Set.finite_empty).subset ?_
    rintro s ⟨hs, hs1, hz⟩
    exact hs hs1 hz
  · have hcod := (hx_analyticOnNhd).eqOn_zero_or_eventually_ne_zero_of_preconnected
      hx_isConnected.isPreconnected
    rcases hcod with hzero | hcod
    · exfalso
      have : riemannZeta 2 = 0 := hzero (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) this
    · rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
      obtain ⟨t, ht, hfin⟩ := hcod z hz
      refine ⟨t, ht, hfin.subset ?_⟩
      rintro s ⟨hst, hs1, hs0⟩
      exact ⟨hst, hs1, by simpa using hs0⟩

lemma hx_re_lt_one {s : ℂ} (h : riemannZeta s = 0) : s.re < 1 := by
  by_contra hc
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.1 hc) h

lemma hx_box_finite (M : ℝ) :
    {s : ℂ | riemannZeta s = 0 ∧ 1 / 2 ≤ s.re ∧ |s.im| ≤ M}.Finite := by
  set K : Set ℂ := (Icc (1 / 2) 1) ×ℂ (Icc (-M) M) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using hx_zeros_locallyFinite
  obtain ⟨I, -, hcover⟩ := hKc.elim_nhds_subcover t (fun z _ => ht z)
  have hfinU : (⋃ z ∈ I, (t z ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0})).Finite :=
    I.finite_toSet.biUnion fun z _ => hfin z
  refine hfinU.subset ?_
  rintro ρ ⟨h0, hre, him⟩
  have hlt := hx_re_lt_one h0
  have hρK : ρ ∈ K := ⟨⟨hre, hlt.le⟩, abs_le.1 him⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  refine mem_iUnion₂.mpr ⟨z, hzI, hρz, ?_, h0⟩
  rintro rfl
  simp at hlt

lemma hx_enat_summable {β : Type*} (f : β → ℕ∞) : Summable f :=
  ⟨_, hasSum_of_isLUB _ (isLUB_sSup _)⟩

theorem count_le_small (T₁ : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, T ≤ T₁ → ∀ σ : ℝ, 3 / 4 ≤ σ →
    (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤ ENNReal.ofReal K := by
  set S : Set ℂ := {s : ℂ | riemannZeta s = 0 ∧ 1 / 2 ≤ s.re ∧ |s.im| ≤ T₁} with hS
  have hfin : S.Finite := hx_box_finite T₁
  set N : ℕ∞ := ∑' s : S, analyticOrderAt riemannZeta (s : ℂ) with hN
  have hNtop : N ≠ ⊤ := by
    have : Fintype S := hfin.fintype
    rw [hN, tsum_fintype]
    refine ENat.sum_ne_top.2 fun s _ => hx_order_ne_top ?_
    rintro h
    have := hx_re_lt_one s.2.1
    rw [h] at this; simp at this
  refine ⟨(N.toNat : ℝ), Nat.cast_nonneg _, fun T hT σ hσ => ?_⟩
  have hle : LindelofHypothesis.zeroDensityCount σ T ≤ N := by
    unfold LindelofHypothesis.zeroDensityCount
    have hsub : {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T} ⊆ S := by
      rintro s ⟨h0, hre, him⟩
      exact ⟨h0, by linarith, him.trans hT⟩
    exact (hx_enat_summable _).tsum_le_tsum_of_inj (Set.inclusion hsub)
      (Set.inclusion_injective hsub) (fun _ _ => zero_le) (fun _ => le_rfl)
      (hx_enat_summable _)
  rw [ENNReal.ofReal_natCast]
  have : (N : ℝ≥0∞) = ((N.toNat : ℕ) : ℝ≥0∞) := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hNtop
    rw [← hn]; simp
  rw [← this]
  exact ENat.toENNReal_le.2 hle

end GuthMaynard.CitedZeros.Hux.PartA
end

section
open Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Hux
/-!
# Huxley (1.9) uniformly in `3/4 ≤ α ≤ 1`: blueprint

Huxley (Invent. Math. 15 (1972)), §6, p. 169, splits the range: `3/4 ≤ α ≤ 9/11` with the choice
(6.5)–(6.6); `α ≥ 9/11` with Haneke's bound (6.7), valid unless `α ≥ 1 - 32400 log l / l` (6.10), where
"it is well known that `N(α, T)` is zero when `T` is sufficiently large". The two ranges are the
published statements `GuthMaynard.huxley_density_estimate_of_le_nine_elevenths` and
`GuthMaynard.huxley_density_estimate_of_nine_elevenths_le`; the zero-free range is covered by the
Vinogradov–Korobov region `GuthMaynard.zeroDensityCount_eq_zero_vinogradov_korobov`, which contains it
for large `T` (`32400 log l / l ≤ c l^{-2/3} (log l)^{-1/3}`); bounded `T` is a finite count.
-/
alias count_le_small := GuthMaynard.CitedZeros.Hux.PartA.count_le_small

end GuthMaynard.CitedZeros.Hux
end

section
open Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Hux.PartA
open GuthMaynard.CitedZeros.Hux
theorem vk_covers (c : ℝ) (hc : 0 < c) : ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    32400 * Real.log (Real.log T) / Real.log T ≤
      c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) := by
  have hlim : Tendsto (fun l : ℝ => Real.log l ^ 4 / l) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero
  have hev : ∀ᶠ l : ℝ in atTop, Real.exp 1 < l ∧ Real.log l ^ 4 / l < (c / 32400) ^ 3 :=
    (eventually_gt_atTop _).and (hlim.eventually (gt_mem_nhds (by positivity)))
  have hev2 := (Real.tendsto_log_atTop.eventually hev)
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hev2
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨hl1, hl2⟩ := hT₀ T hT
  set l := Real.log T with hl
  have hlpos : 0 < l := lt_trans (Real.exp_pos 1) hl1
  have hL1 : 1 < Real.log l := by
    rw [Real.lt_log_iff_exp_lt hlpos]; exact hl1
  set L := Real.log l with hLdef
  have hLpos : 0 < L := by linarith
  set a := L ^ (1 / 3 : ℝ) with ha
  set b := l ^ (1 / 3 : ℝ) with hb
  have ha0 : 0 < a := Real.rpow_pos_of_pos hLpos _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hlpos _
  have ha3 : a ^ 3 = L := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; norm_num
  have hb3 : b ^ 3 = l := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hlpos.le]; norm_num
  have hl23 : l ^ (-(2 / 3) : ℝ) = 1 / b ^ 2 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hlpos.le, Real.rpow_neg hlpos.le]
    norm_num
  have hL13 : L ^ (-(1 / 3) : ℝ) = 1 / a := by
    rw [ha, Real.rpow_neg hLpos.le]; simp
  rw [hl23, hL13]
  -- key: 32400 a^4 ≤ c b
  have hkey : 32400 * a ^ 4 ≤ c * b := by
    have h3 : (32400 * a ^ 4) ^ 3 ≤ (c * b) ^ 3 := by
      rw [← ha3, ← hb3] at hl2
      have hb3pos : 0 < b ^ 3 := by positivity
      rw [div_lt_iff₀ hb3pos] at hl2
      have : (32400 * a ^ 4) ^ 3 = 32400 ^ 3 * (a ^ 3) ^ 4 := by ring
      rw [this]
      have : (c * b) ^ 3 = 32400 ^ 3 * ((c / 32400) ^ 3 * b ^ 3) := by
        field_simp
      rw [this]
      nlinarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h3
  rw [← ha3, ← hb3, div_le_iff₀ (by positivity)]
  have : c * (1 / b ^ 2) * (1 / a) * b ^ 3 = c * b / a := by
    field_simp
  rw [this, le_div_iff₀ ha0]
  nlinarith [hkey]

end GuthMaynard.CitedZeros.Hux.PartA
end

section
open Filter Topology Set
open scoped ENNReal
namespace GuthMaynard.CitedZeros.Hux
alias vk_covers := GuthMaynard.CitedZeros.Hux.PartA.vk_covers

/-! ## Assembly (no `sorry` below) -/
theorem huxley_density_estimate_uniform_dev :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44) := by
  obtain ⟨C₁, T₁, h₁⟩ := GuthMaynard.huxley_density_estimate_of_le_nine_elevenths
  obtain ⟨C₂, T₂, h₂⟩ := GuthMaynard.huxley_density_estimate_of_nine_elevenths_le
  obtain ⟨c, hc, T₃, h₃⟩ := GuthMaynard.zeroDensityCount_eq_zero_vinogradov_korobov
  obtain ⟨T₄, h₄⟩ := vk_covers c hc
  set Tb : ℝ := max (max T₁ T₂) (max T₃ T₄) with hTb
  obtain ⟨K, hK, hsmall⟩ := count_le_small Tb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 < Real.log 2 ^ 44 := by positivity
  refine ⟨max C₁ 0 + max C₂ 0 + K / Real.log 2 ^ 44, fun T hT σ hσ0 hσ1 => ?_⟩
  have hTpos : 0 < T := by linarith
  have hlogT : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hLT : Real.log 2 ^ 44 ≤ Real.log T ^ 44 := by gcongr
  have hexp0 : 0 ≤ 3 * (1 - σ) / (3 * σ - 1) := div_nonneg (by linarith) (by linarith)
  set P : ℝ := T ^ (3 * (1 - σ) / (3 * σ - 1)) with hP
  set Lg : ℝ := Real.log T ^ 44 with hLg
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) hexp0
  have hLg0 : 0 ≤ Lg := by positivity
  have hPL : 0 ≤ P * Lg := by positivity
  have hK' : 0 ≤ K / Real.log 2 ^ 44 := div_nonneg hK hL0.le
  -- the final constant dominates each piece
  have hdom : ∀ C' : ℝ, C' ≤ max C₁ 0 + max C₂ 0 + K / Real.log 2 ^ 44 →
      ENNReal.ofReal (C' * P * Lg) ≤
        ENNReal.ofReal ((max C₁ 0 + max C₂ 0 + K / Real.log 2 ^ 44) * P * Lg) := by
    intro C' hC'
    apply ENNReal.ofReal_le_ofReal
    have := mul_le_mul_of_nonneg_right hC' hPL
    nlinarith
  by_cases hbig : Tb ≤ T
  · have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hbig
    have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hbig
    have hT3 : T₃ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hbig
    have hT4 : T₄ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hbig
    by_cases hA : σ ≤ 9 / 11
    · refine (h₁ T hT1 σ hσ0 hA).trans (hdom C₁ ?_)
      have := le_max_left C₁ 0; have := le_max_right C₂ 0; linarith
    · push Not at hA
      by_cases hB : σ ≤ 1 - 32400 * Real.log (Real.log T) / Real.log T
      · refine (h₂ T hT2 σ hA.le hB).trans (hdom C₂ ?_)
        have := le_max_right C₁ 0; have := le_max_left C₂ 0; linarith
      · push Not at hB
        have hv := h₄ T hT4
        rw [h₃ T hT3 σ (by linarith)]
        simp
  · push Not at hbig
    refine (hsmall T hbig.le σ hσ0).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have h1 : K = K / Real.log 2 ^ 44 * Real.log 2 ^ 44 := by field_simp
    have h2 : K / Real.log 2 ^ 44 * Real.log 2 ^ 44 ≤ K / Real.log 2 ^ 44 * (P * Lg) := by
      apply mul_le_mul_of_nonneg_left _ hK'
      nlinarith
    have h3 : K / Real.log 2 ^ 44 * (P * Lg) ≤
        (max C₁ 0 + max C₂ 0 + K / Real.log 2 ^ 44) * P * Lg := by
      have := mul_le_mul_of_nonneg_right
        (show K / Real.log 2 ^ 44 ≤ max C₁ 0 + max C₂ 0 + K / Real.log 2 ^ 44 by
          have := le_max_right C₁ 0; have := le_max_right C₂ 0; linarith) hPL
      nlinarith
    linarith

end GuthMaynard.CitedZeros.Hux
end

section
open Filter Topology Set
open scoped ENNReal
open GuthMaynard
open GuthMaynard.CitedZeros
open GuthMaynard.CitedZeros.Hux
theorem solution :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 3 / 4 ≤ σ → σ ≤ 1 →
      (LindelofHypothesis.zeroDensityCount σ T : ℝ≥0∞) ≤
        ENNReal.ofReal (C * T ^ (3 * (1 - σ) / (3 * σ - 1)) * Real.log T ^ 44) := by
  exact GuthMaynard.CitedZeros.Hux.huxley_density_estimate_uniform_dev
end
