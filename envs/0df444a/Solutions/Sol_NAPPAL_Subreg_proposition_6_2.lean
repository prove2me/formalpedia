-- Prove2me | solution 1 for NAPPAL.Subreg.proposition_6_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:01:57.01745+00:00
-- url     : https://prove2.me/submissions/359b68d4-344a-40b7-8232-0a0b327b0da9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NAPPAL_Subreg_Setting
import Definitions.Def_NAPPAL_Subreg_Subregularity
import Theorems.Thm_NAPPAL_Rate_theorem_4_1
import Theorems.Thm_NAPPAL_Subreg_lemma_6_1_uniform

open Filter Topology

lemma nappal62_tnorm_nonneg {n d m : ℕ} (ξ : NAPPAL.KL.W n d m) : 0 ≤ NAPPAL.KL.tnorm ξ :=
  Real.sqrt_nonneg _

lemma nappal62_wdist_comm {n d m : ℕ} (a b : NAPPAL.KL.W n d m) :
    NAPPAL.KL.wdist a b = NAPPAL.KL.wdist b a := by
  unfold NAPPAL.KL.wdist NAPPAL.KL.tnorm
  congr 1
  simp only [Prod.fst_sub, Prod.snd_sub]
  rw [← norm_neg (a.1 - b.1), ← norm_neg (a.2.1 - b.2.1), ← norm_neg (a.2.2 - b.2.2)]
  simp

lemma nappal62_tnorm_add {n d m : ℕ} (a b : NAPPAL.KL.W n d m) :
    NAPPAL.KL.tnorm (a + b) ≤ NAPPAL.KL.tnorm a + NAPPAL.KL.tnorm b := by
  unfold NAPPAL.KL.tnorm
  set x1 := ‖a.1‖; set x2 := ‖a.2.1‖; set x3 := ‖a.2.2‖
  set y1 := ‖b.1‖; set y2 := ‖b.2.1‖; set y3 := ‖b.2.2‖
  have h1 : ‖(a + b).1‖ ≤ x1 + y1 := norm_add_le _ _
  have h2 : ‖(a + b).2.1‖ ≤ x2 + y2 := norm_add_le _ _
  have h3 : ‖(a + b).2.2‖ ≤ x3 + y3 := norm_add_le _ _
  have hx1 : 0 ≤ x1 := norm_nonneg _
  have hx2 : 0 ≤ x2 := norm_nonneg _
  have hx3 : 0 ≤ x3 := norm_nonneg _
  have hy1 : 0 ≤ y1 := norm_nonneg _
  have hy2 : 0 ≤ y2 := norm_nonneg _
  have hy3 : 0 ≤ y3 := norm_nonneg _
  have hz1 : 0 ≤ ‖(a + b).1‖ := norm_nonneg _
  have hz2 : 0 ≤ ‖(a + b).2.1‖ := norm_nonneg _
  have hz3 : 0 ≤ ‖(a + b).2.2‖ := norm_nonneg _
  set X := x1 ^ 2 + x2 ^ 2 + x3 ^ 2
  set Y := y1 ^ 2 + y2 ^ 2 + y3 ^ 2
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  rw [Real.sqrt_le_left (by positivity)]
  have hsX := Real.sq_sqrt hX
  have hsY := Real.sq_sqrt hY
  have hsXY : Real.sqrt X * Real.sqrt Y = Real.sqrt (X * Y) := (Real.sqrt_mul hX Y).symm
  have hcs : x1 * y1 + x2 * y2 + x3 * y3 ≤ Real.sqrt (X * Y) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg (x1 * y2 - x2 * y1), sq_nonneg (x1 * y3 - x3 * y1),
      sq_nonneg (x2 * y3 - x3 * y2)]
  have e1 : ‖(a + b).1‖ ^ 2 ≤ (x1 + y1) ^ 2 := pow_le_pow_left₀ hz1 h1 2
  have e2 : ‖(a + b).2.1‖ ^ 2 ≤ (x2 + y2) ^ 2 := pow_le_pow_left₀ hz2 h2 2
  have e3 : ‖(a + b).2.2‖ ^ 2 ≤ (x3 + y3) ^ 2 := pow_le_pow_left₀ hz3 h3 2
  nlinarith

lemma nappal62_wdist_triangle {n d m : ℕ} (a b c : NAPPAL.KL.W n d m) :
    NAPPAL.KL.wdist a c ≤ NAPPAL.KL.wdist a b + NAPPAL.KL.wdist b c := by
  unfold NAPPAL.KL.wdist
  have := nappal62_tnorm_add (a - b) (b - c)
  simpa using this

theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (LK : ℝ) (K : NAPPAL.KL.E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Subreg.RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p)
    (wbar : NAPPAL.KL.W n d m) (hcl : MapClusterPt wbar Filter.atTop (NAPPAL.KL.wseq u v p))
    (δ3 η κ3 : ℝ) (hA3 : NAPPAL.Subreg.Assumption3 P γ wbar δ3)
    (hMS : NAPPAL.Subreg.MetricSubregularAt P γ wbar η κ3)
    (hηδ : η < δ3) :
    ∃ κ1 η' ν : ℝ, NAPPAL.KL.VPEB P γ (NAPPAL.KL.wseq u v p) wbar κ1 η' ν := by
  -- Theorem 4.1 (iv): the residual bound with constant `c5`
  have hrun' : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p := by
    obtain ⟨h1, h2, ⟨hγ, hσ, hσ1, hk⟩, h8⟩ := hrun
    refine ⟨h1, h2, ⟨hγ, hσ, hσ1, fun k => ?_⟩, h8⟩
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hk k
    exact ⟨⟨a1, a2, a3⟩, a4, a5, a6⟩
  obtain ⟨-, -, -, -, ⟨⟨c5, hc5, hres⟩, -⟩, -⟩ :=
    NAPPAL.Rate.theorem_4_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun'
  -- uniform cost-to-go inequality (Lemma 6.1)
  obtain ⟨c6, hc6, hcost⟩ :=
    NAPPAL.Subreg.lemma_6_1_uniform P LG LH L0 LOmj LK K β γ σ δ ε u v p hrun
  obtain ⟨hstat, hδ3, hloc⟩ := hA3
  obtain ⟨hη, hκ3, hsub⟩ := hMS
  set η' := min η (δ3 / 3) with hη'
  have hη'pos : 0 < η' := lt_min hη (by linarith)
  refine ⟨c6 * ((κ3 * c5) ^ 2 + 1), η', 1, by positivity, hη'pos, one_pos, ?_⟩
  intro k hk _
  set x := NAPPAL.KL.wseq u v p (k + 1) with hx
  set D := NAPPAL.KL.wdist (NAPPAL.KL.wseq u v p k) x with hD
  have hD0 : 0 ≤ D := nappal62_tnorm_nonneg _
  set r := κ3 * (c5 * D) with hr
  have hr0 : 0 ≤ r := by positivity
  set e := NAPPAL.KL.wdist x wbar with he
  have he0 : 0 ≤ e := nappal62_tnorm_nonneg _
  set s := min r e with hs
  have hs0 : 0 ≤ s := le_min hr0 he0
  -- the distance from `x` to the stationary set is at most `s`
  have hdist : NAPPAL.Subreg.distTo x (NAPPAL.Subreg.statSet P γ) ≤ ENNReal.ofReal s := by
    have h1 : NAPPAL.Subreg.distTo x (NAPPAL.Subreg.statSet P γ) ≤ ENNReal.ofReal r := by
      have hsx := hsub x (lt_of_lt_of_le hk (min_le_left _ _))
      have hres' := hres k
      calc NAPPAL.Subreg.distTo x (NAPPAL.Subreg.statSet P γ)
          ≤ ENNReal.ofReal κ3 * NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ x) := hsx
        _ ≤ ENNReal.ofReal κ3 * ENNReal.ofReal (c5 * D) := by
            gcongr
            exact hres'
        _ = ENNReal.ofReal r := by rw [hr, ENNReal.ofReal_mul hκ3.le]
    have h2 : NAPPAL.Subreg.distTo x (NAPPAL.Subreg.statSet P γ) ≤ ENNReal.ofReal e := by
      unfold NAPPAL.Subreg.distTo
      exact iInf₂_le wbar hstat
    rw [hs]
    rcases le_total r e with hre | hre
    · rw [min_eq_left hre]; exact h1
    · rw [min_eq_right hre]; exact h2
  have hsη : s < 2 * η' := by
    have : s ≤ e := min_le_right _ _
    linarith
  set A := NAPPAL.KL.augLag P γ x - NAPPAL.KL.augLag P γ wbar with hA
  -- for every `t ∈ (s, 2η']`, `A ≤ c6 (t² + D²)`
  have hkey : ∀ t : ℝ, s < t → t ≤ 2 * η' → A ≤ c6 * (t ^ 2 + D ^ 2) := by
    intro t hst ht
    have ht0 : 0 < t := lt_of_le_of_lt hs0 hst
    have hlt : NAPPAL.Subreg.distTo x (NAPPAL.Subreg.statSet P γ) < ENNReal.ofReal t :=
      lt_of_le_of_lt hdist ((ENNReal.ofReal_lt_ofReal_iff ht0).2 hst)
    unfold NAPPAL.Subreg.distTo at hlt
    obtain ⟨z, hlt⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hz, hlt⟩ := iInf_lt_iff.1 hlt
    have hxz : NAPPAL.KL.wdist x z < t := (ENNReal.ofReal_lt_ofReal_iff ht0).1 hlt
    have hxz0 : 0 ≤ NAPPAL.KL.wdist x z := nappal62_tnorm_nonneg _
    have hzw : NAPPAL.KL.wdist z wbar ≤ δ3 := by
      have := nappal62_wdist_triangle z x wbar
      rw [nappal62_wdist_comm z x] at this
      have h3 : η' ≤ δ3 / 3 := min_le_right _ _
      linarith
    have hLz := hloc z hz hzw
    have hc := hcost z hz k
    rw [nappal62_wdist_comm z] at hc
    have hsq : NAPPAL.KL.wdist x z ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hxz0 hxz.le 2
    calc A ≤ NAPPAL.KL.augLag P γ x - NAPPAL.KL.augLag P γ z := by rw [hA]; linarith
      _ ≤ c6 * (NAPPAL.KL.wdist x z ^ 2 + D ^ 2) := hc
      _ ≤ c6 * (t ^ 2 + D ^ 2) := by gcongr
  -- pass to the limit `t ↓ s`
  have hlim : A ≤ c6 * (s ^ 2 + D ^ 2) := by
    have hT : Tendsto (fun t : ℝ => c6 * (t ^ 2 + D ^ 2)) (𝓝[>] s) (𝓝 (c6 * (s ^ 2 + D ^ 2))) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      exact ((continuous_pow 2).add continuous_const).const_mul c6 |>.tendsto s |>.congr
        (fun _ => rfl)
    apply ge_of_tendsto hT
    filter_upwards [Ioo_mem_nhdsGT hsη] with t ht
    exact hkey t ht.1 ht.2.le
  have hsr : s ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hs0 (min_le_left _ _) 2
  calc A ≤ c6 * (s ^ 2 + D ^ 2) := hlim
    _ ≤ c6 * (r ^ 2 + D ^ 2) := by gcongr
    _ = c6 * ((κ3 * c5) ^ 2 + 1) * D ^ 2 := by rw [hr]; ring
