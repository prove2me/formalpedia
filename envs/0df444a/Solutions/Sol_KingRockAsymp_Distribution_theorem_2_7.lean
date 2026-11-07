-- Prove2me | solution 1 for KingRockAsymp.Distribution.theorem_2_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T15:58:24.42346+00:00
-- url     : https://prove2.me/submissions/84055174-0829-4c67-a376-7905e6c7cfcc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic
import Theorems.Thm_KingRockAsymp_Distribution_thm_2_4_display_upper_lipschitz
import Theorems.Thm_KingRockAsymp_Distribution_theorem_A3
import Theorems.Thm_KingRockAsymp_Distribution_proposition_A1

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open KingRockAsymp.Distribution
open scoped ENNReal


namespace KR26

variable {n m : ℕ}

lemma cd_of_seq (F : Rn n → Set (Rn m)) (x₀ : Rn n) {t : ℕ → ℝ} {yk : ℕ → Rn m}
    {uk : ℕ → Rn n} {y : Rn m} {u : Rn n} (htpos : ∀ k, 0 < t k)
    (ht : Tendsto t atTop (𝓝 0)) (hy : Tendsto yk atTop (𝓝 y)) (hu : Tendsto uk atTop (𝓝 u))
    (hF : ∀ᶠ k in atTop, t k • yk k ∈ F (x₀ + t k • uk k)) :
    u ∈ contingentDeriv (svInv F) 0 x₀ y := by
  simp only [contingentDeriv, setLimsup, mem_setOf_eq]
  intro ε hε
  have htw : Tendsto t atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall htpos⟩
  apply htw.frequently
  apply Eventually.frequently
  filter_upwards [(hy.prodMk_nhds hu) (ball_mem_nhds _ hε), hF] with k hk hFk
  refine ⟨(yk k, uk k), ⟨(t k • yk k, x₀ + t k • uk k), hFk, ?_⟩, hk⟩
  have h0 : t k ≠ 0 := (htpos k).ne'
  ext
  · simp [smul_smul, inv_mul_cancel₀ h0]
  · simp [smul_smul, inv_mul_cancel₀ h0]

lemma seq_of_cd (F : Rn n → Set (Rn m)) (x₀ : Rn n) {y : Rn m} {u : Rn n}
    (h : u ∈ contingentDeriv (svInv F) 0 x₀ y) :
    ∃ t : ℕ → ℝ, ∃ yk : ℕ → Rn m, ∃ uk : ℕ → Rn n, (∀ k, 0 < t k) ∧
      Tendsto t atTop (𝓝 0) ∧ Tendsto yk atTop (𝓝 y) ∧ Tendsto uk atTop (𝓝 u) ∧
      ∀ k, t k • yk k ∈ F (x₀ + t k • uk k) := by
  simp only [contingentDeriv, setLimsup, mem_setOf_eq] at h
  have key : ∀ k : ℕ, ∃ t : ℝ, ∃ q : Rn m × Rn n, 0 < t ∧ t < 1 / ((k : ℝ) + 1) ∧
      dist q (y, u) < 1 / ((k : ℝ) + 1) ∧ t • q.1 ∈ F (x₀ + t • q.2) := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hfr := h _ hk
    have hI : Ioo (0 : ℝ) (1 / ((k : ℝ) + 1)) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hk
    obtain ⟨t, ⟨q, hq, hqb⟩, ht⟩ := (hfr.and_eventually hI).exists
    obtain ⟨p, hp, rfl⟩ := hq
    have h0 : t ≠ 0 := ht.1.ne'
    refine ⟨t, t⁻¹ • (p - (0, x₀)), ht.1, ht.2, hqb, ?_⟩
    have e1 : t • (t⁻¹ • (p - ((0 : Rn m), x₀))).1 = p.1 := by
      simp [smul_smul, mul_inv_cancel₀ h0]
    have e2 : x₀ + t • (t⁻¹ • (p - ((0 : Rn m), x₀))).2 = p.2 := by
      simp [smul_smul, mul_inv_cancel₀ h0]
    rw [e1, e2]; exact hp
  choose t q htpos htlt hq hF using key
  have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hq' : Tendsto q atTop (𝓝 (y, u)) :=
    tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun k => dist_nonneg) (fun k => (hq k).le) h1)
  refine ⟨t, fun k => (q k).1, fun k => (q k).2, htpos,
    squeeze_zero (fun k => (htpos k).le) (fun k => (htlt k).le) h1,
    (continuous_fst.tendsto _).comp hq', (continuous_snd.tendsto _).comp hq', hF⟩

lemma zero_mem_cd (F : Rn n → Set (Rn m)) (x₀ : Rn n) (h0 : (0 : Rn m) ∈ F x₀) :
    (0 : Rn n) ∈ contingentDeriv (svInv F) 0 x₀ 0 := by
  apply cd_of_seq F x₀ (t := fun k => 1 / ((k : ℝ) + 1)) (yk := fun _ => 0) (uk := fun _ => 0)
    (fun k => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat tendsto_const_nhds
    tendsto_const_nhds
  exact Eventually.of_forall fun k => by simpa using h0

lemma cd_zero_eq (F : Rn n → Set (Rn m)) (x₀ : Rn n) (h0 : (0 : Rn m) ∈ F x₀)
    (hs : ∀ y, (contingentDeriv (svInv F) 0 x₀ y).Subsingleton) :
    contingentDeriv (svInv F) 0 x₀ 0 = {0} :=
  (hs 0).eq_singleton_of_mem (zero_mem_cd F x₀ h0)

lemma cd_closed (F : Rn n → Set (Rn m)) (x₀ : Rn n) {yk : ℕ → Rn m} {uk : ℕ → Rn n}
    {y : Rn m} {u : Rn n} (hy : Tendsto yk atTop (𝓝 y)) (hu : Tendsto uk atTop (𝓝 u))
    (hmem : ∀ k, uk k ∈ contingentDeriv (svInv F) 0 x₀ (yk k)) :
    u ∈ contingentDeriv (svInv F) 0 x₀ y := by
  simp only [contingentDeriv, setLimsup, mem_setOf_eq] at hmem ⊢
  intro ε hε
  have hp := hy.prodMk_nhds hu
  obtain ⟨k, hk⟩ := (show ∀ᶠ k in atTop, (yk k, uk k) ∈ ball (y, u) (ε / 2) from
    hp (ball_mem_nhds _ (half_pos hε))).exists
  refine (hmem k _ (half_pos hε)).mono fun t ht => ?_
  obtain ⟨q, hq1, hq2⟩ := ht
  refine ⟨q, hq1, ?_⟩
  rw [mem_ball] at hk hq2 ⊢
  calc dist q (y, u) ≤ dist q (yk k, uk k) + dist (yk k, uk k) (y, u) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hq2 hk
    _ = ε := add_halves ε

/-- Upper Lipschitz data. -/
lemma upperLip (F : Rn n → Set (Rn m)) (x₀ : Rn n) (h0 : (0 : Rn m) ∈ F x₀)
    (hs : ∀ y, (contingentDeriv (svInv F) 0 x₀ y).Subsingleton) :
    ∃ ρ > (0 : ℝ), ∃ lam : ℝ, 0 ≤ lam ∧ ∃ r > (0 : ℝ),
      ∀ y : Rn m, ‖y‖ < r → ∀ x, ‖x - x₀‖ < ρ → y ∈ F x → ‖x - x₀‖ ≤ lam * ‖y‖ := by
  obtain ⟨U₁, hU₁, lam, hlam, hev⟩ :=
    thm_2_4_display_upper_lipschitz F x₀ h0 (cd_zero_eq F x₀ h0 hs)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp hU₁
  refine ⟨ρ, hρ, lam, hlam, r, hr, fun y hy x hx hyx => ?_⟩
  have := hball (show dist y 0 < r by simpa using hy)
    ⟨hρU (by simpa [dist_eq_norm] using hx), hyx⟩
  simpa [dist_eq_norm] using this

lemma cd_bound (F : Rn n → Set (Rn m)) (x₀ : Rn n) {ρ lam r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hUL : ∀ y : Rn m, ‖y‖ < r → ∀ x, ‖x - x₀‖ < ρ → y ∈ F x → ‖x - x₀‖ ≤ lam * ‖y‖)
    {y : Rn m} {u : Rn n} (h : u ∈ contingentDeriv (svInv F) 0 x₀ y) :
    ‖u‖ ≤ lam * ‖y‖ := by
  obtain ⟨t, yk, uk, htpos, ht, hy, hu, hF⟩ := seq_of_cd F x₀ h
  have hty : Tendsto (fun k => t k • yk k) atTop (𝓝 0) := by
    simpa using ht.smul hy
  have htu : Tendsto (fun k => t k • uk k) atTop (𝓝 0) := by
    simpa using ht.smul hu
  have hev : ∀ᶠ k in atTop, ‖uk k‖ ≤ lam * ‖yk k‖ := by
    filter_upwards [hty (ball_mem_nhds 0 hr), htu (ball_mem_nhds 0 hρ)] with k h1 h2
    have := hUL (t k • yk k) (by simpa using h1) (x₀ + t k • uk k) (by simpa using h2) (hF k)
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (htpos k)] at this
    have := (htpos k)
    nlinarith
  exact le_of_tendsto_of_tendsto hu.norm (hy.norm.const_mul lam) hev

lemma cd_nonempty (F : Rn n → Set (Rn m)) (x₀ : Rn n) (hsub : IsSubinvertibleAt F x₀)
    (hs : ∀ y, (contingentDeriv (svInv F) 0 x₀ y).Subsingleton) (y : Rn m) :
    (contingentDeriv (svInv F) 0 x₀ y).Nonempty := by
  obtain ⟨h0, ε₀, hε₀, U', hU'c, -, -, G', hGcl, hx₀G, hG⟩ := hsub
  obtain ⟨ρ, hρ, lam, hlam, r, hr, hUL⟩ := upperLip F x₀ h0 hs
  have hG0 : ∀ x ∈ G' 0, x = x₀ := by
    intro x hx
    by_contra hne
    have hd : 0 < ‖x - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    set s : ℝ := min (1 / 2) (ρ / (2 * ‖x - x₀‖)) with hs_def
    have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
    have hs1 : s ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hsρ : s * ‖x - x₀‖ < ρ := by
      have : s ≤ ρ / (2 * ‖x - x₀‖) := min_le_right _ _
      calc s * ‖x - x₀‖ ≤ ρ / (2 * ‖x - x₀‖) * ‖x - x₀‖ :=
            mul_le_mul_of_nonneg_right this hd.le
        _ = ρ / 2 := by field_simp
        _ < ρ := half_lt_self hρ
    have hconv := (hG 0 (mem_closedBall_self hε₀.le)).2.1
    have hmem : x₀ + s • (x - x₀) ∈ G' 0 :=
      hconv.add_smul_sub_mem hx₀G hx ⟨hs0.le, hs1⟩
    have hF0 : (0 : Rn m) ∈ F (x₀ + s • (x - x₀)) :=
      (hG 0 (mem_closedBall_self hε₀.le)).2.2.2 hmem
    have hn : ‖x₀ + s • (x - x₀) - x₀‖ = s * ‖x - x₀‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    have := hUL 0 (by simpa using hr) _ (by rw [hn]; exact hsρ) hF0
    rw [hn, norm_zero, mul_zero] at this
    have : 0 < s * ‖x - x₀‖ := mul_pos hs0 hd
    linarith
  set c : ℝ := ε₀ / (‖y‖ + 1) with hc
  have hcpos : 0 < c := by positivity
  set t : ℕ → ℝ := fun k => c / ((k : ℝ) + 1) with ht_def
  have htpos : ∀ k, 0 < t k := fun k => by positivity
  have ht0 : Tendsto t atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul c
    simpa [ht_def, div_eq_mul_inv] using this
  have htyb : ∀ k, t k • y ∈ closedBall (0 : Rn m) ε₀ := by
    intro k
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (htpos k)]
    have h1 : t k ≤ c := by
      rw [ht_def]; simp only
      rw [div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    calc t k * ‖y‖ ≤ c * ‖y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ ε₀ := by
        rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg y]
  have hex : ∀ k, ∃ x, x ∈ G' (t k • y) := fun k => (hG _ (htyb k)).1
  choose xk hxk using hex
  have hty0 : Tendsto (fun k => t k • y) atTop (𝓝 0) := by simpa using ht0.smul_const y
  have hxlim : Tendsto xk atTop (𝓝 x₀) := by
    apply hU'c.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun k => (hG _ (htyb k)).2.2.1 (hxk k))
    intro a _ ha
    obtain ⟨φ, hφ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq ha
    have hpair : Tendsto (fun k => (t (φ k) • y, xk (φ k))) atTop (𝓝 ((0 : Rn m), a)) :=
      (hty0.comp hφ.tendsto_atTop).prodMk_nhds hlim
    have hmemC := hGcl.mem_of_tendsto hpair
      (Eventually.of_forall fun k => ⟨htyb (φ k), hxk (φ k)⟩)
    exact hG0 a hmemC.2
  set uk : ℕ → Rn n := fun k => (t k)⁻¹ • (xk k - x₀) with huk
  have hbd : ∀ᶠ k in atTop, uk k ∈ closedBall (0 : Rn n) (lam * ‖y‖) := by
    have hxr : Tendsto (fun k => xk k - x₀) atTop (𝓝 0) := by
      simpa using hxlim.sub_const x₀
    filter_upwards [hty0 (ball_mem_nhds 0 hr), hxr (ball_mem_nhds 0 hρ)] with k h1 h2
    have hFk : t k • y ∈ F (xk k) := (hG _ (htyb k)).2.2.2 (hxk k)
    have := hUL (t k • y) (by simpa using h1) (xk k) (by simpa using h2) hFk
    rw [mem_closedBall, dist_zero_right, huk]; simp only
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (htpos k), inv_mul_le_iff₀ (htpos k)]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos k)] at this
    linarith
  obtain ⟨u, -, ψ, hψ, hulim⟩ := (isCompact_closedBall (0 : Rn n) (lam * ‖y‖)).tendsto_subseq'
    hbd.frequently
  refine ⟨u, cd_of_seq F x₀ (t := t ∘ ψ) (yk := fun _ => y) (uk := uk ∘ ψ)
    (fun k => htpos (ψ k)) (ht0.comp hψ.tendsto_atTop) tendsto_const_nhds hulim ?_⟩
  refine Eventually.of_forall fun k => ?_
  have e : x₀ + (t ∘ ψ) k • (uk ∘ ψ) k = xk (ψ k) := by
    simp only [Function.comp, huk, smul_smul, mul_inv_cancel₀ (htpos (ψ k)).ne', one_smul]
    abel
  rw [e]
  exact (hG _ (htyb (ψ k))).2.2.2 (hxk (ψ k))

lemma L_cont (F : Rn n → Set (Rn m)) (x₀ : Rn n) (h0 : (0 : Rn m) ∈ F x₀)
    (hs : ∀ y, (contingentDeriv (svInv F) 0 x₀ y).Subsingleton) (L : Rn m → Rn n)
    (hL : ∀ y, L y ∈ contingentDeriv (svInv F) 0 x₀ y) : Continuous L := by
  obtain ⟨ρ, hρ, lam, hlam, r, hr, hUL⟩ := upperLip F x₀ h0 hs
  rw [continuous_iff_seqContinuous]
  intro yk y hy
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hz : Tendsto (yk ∘ ns) atTop (𝓝 y) := hy.comp hns
  have hbd : ∀ᶠ k in atTop, L ((yk ∘ ns) k) ∈ closedBall (0 : Rn n) (lam * (‖y‖ + 1)) := by
    filter_upwards [hz (ball_mem_nhds y one_pos)] with k hk
    rw [mem_closedBall, dist_zero_right]
    have h1 := cd_bound F x₀ hρ hr hUL (hL ((yk ∘ ns) k))
    have h2 : ‖(yk ∘ ns) k‖ ≤ ‖y‖ + 1 := by
      have := norm_le_norm_add_norm_sub' ((yk ∘ ns) k) y
      rw [mem_preimage, mem_ball, dist_eq_norm] at hk
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hlam)
  obtain ⟨a, -, ms, hms, hlim⟩ := (isCompact_closedBall _ _).tendsto_subseq' hbd.frequently
  have ha : a ∈ contingentDeriv (svInv F) 0 x₀ y :=
    cd_closed F x₀ (hz.comp hms.tendsto_atTop) hlim (fun k => hL _)
  have : a = L y := hs y ha (hL y)
  exact ⟨ms, this ▸ hlim⟩

lemma unif (F : Rn n → Set (Rn m)) (x₀ : Rn n) (h0 : (0 : Rn m) ∈ F x₀)
    (hs : ∀ y, (contingentDeriv (svInv F) 0 x₀ y).Subsingleton) (L : Rn m → Rn n)
    (hL : ∀ y, L y ∈ contingentDeriv (svInv F) 0 x₀ y) (R η : ℝ) (hη : 0 < η) :
    ∃ δ > (0 : ℝ), ∀ t : ℝ, 0 < t → t < δ → ∀ y : Rn m, ‖y‖ ≤ R → ∀ x : Rn n,
      ‖x - x₀‖ < δ → t • y ∈ F x → ‖t⁻¹ • (x - x₀) - L y‖ < η := by
  obtain ⟨ρ, hρ, lam, hlam, r, hr, hUL⟩ := upperLip F x₀ h0 hs
  have hLc := L_cont F x₀ h0 hs L hL
  by_contra hcon
  push_neg at hcon
  have key : ∀ k : ℕ, ∃ t : ℝ, ∃ y : Rn m, ∃ x : Rn n, 0 < t ∧ t < 1 / ((k : ℝ) + 1) ∧
      ‖y‖ ≤ R ∧ ‖x - x₀‖ < 1 / ((k : ℝ) + 1) ∧ t • y ∈ F x ∧
      η ≤ ‖t⁻¹ • (x - x₀) - L y‖ := by
    intro k
    obtain ⟨t, ht0, htd, y, hy, x, hx, hF, hge⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨t, y, x, ht0, htd, hy, hx, hF, hge⟩
  choose t yk xk htpos htlt hyR hxlt hF hge using key
  have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht0 : Tendsto t atTop (𝓝 0) :=
    squeeze_zero (fun k => (htpos k).le) (fun k => (htlt k).le) h1
  have hx0 : Tendsto (fun k => ‖xk k - x₀‖) atTop (𝓝 0) :=
    squeeze_zero (fun k => norm_nonneg _) (fun k => (hxlt k).le) h1
  set uk : ℕ → Rn n := fun k => (t k)⁻¹ • (xk k - x₀) with huk
  have htR : Tendsto (fun k => t k * R) atTop (𝓝 0) := by simpa using ht0.mul_const R
  have hbd : ∀ᶠ k in atTop, (yk k, uk k) ∈ closedBall (0 : Rn m) R ×ˢ closedBall (0 : Rn n) (lam * R) := by
    filter_upwards [htR (Iio_mem_nhds hr), hx0 (Iio_mem_nhds hρ)] with k h1 h2
    refine ⟨by simpa using hyR k, ?_⟩
    have hyn : ‖t k • yk k‖ < r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos k)]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hyR k) (htpos k).le) h1
    have := hUL _ hyn (xk k) h2 (hF k)
    rw [mem_closedBall, dist_zero_right, huk]; simp only
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (htpos k), inv_mul_le_iff₀ (htpos k)]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (htpos k)] at this
    calc ‖xk k - x₀‖ ≤ lam * (t k * ‖yk k‖) := this
      _ ≤ lam * (t k * R) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hyR k) (htpos k).le) hlam
      _ = t k * (lam * R) := by ring
  obtain ⟨⟨y, u⟩, -, φ, hφ, hlim⟩ :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).tendsto_subseq' hbd.frequently
  have hylim : Tendsto (yk ∘ φ) atTop (𝓝 y) := (continuous_fst.tendsto _).comp hlim
  have hulim : Tendsto (uk ∘ φ) atTop (𝓝 u) := (continuous_snd.tendsto _).comp hlim
  have hu : u ∈ contingentDeriv (svInv F) 0 x₀ y := by
    refine cd_of_seq F x₀ (t := t ∘ φ) (fun k => htpos (φ k)) (ht0.comp hφ.tendsto_atTop)
      hylim hulim (Eventually.of_forall fun k => ?_)
    have e : x₀ + (t ∘ φ) k • (uk ∘ φ) k = xk (φ k) := by
      simp only [Function.comp, huk, smul_smul, mul_inv_cancel₀ (htpos (φ k)).ne', one_smul]
      abel
    rw [e]; exact hF (φ k)
  have huL : u = L y := hs y hu (hL y)
  have hdiff : Tendsto (fun k => uk (φ k) - L (yk (φ k))) atTop (𝓝 0) := by
    have := hulim.sub ((hLc.tendsto y).comp hylim)
    rw [huL, sub_self] at this
    exact this
  have hev : ∀ᶠ k in atTop, ‖uk (φ k) - L (yk (φ k))‖ < η := by
    have := hdiff.norm
    rw [norm_zero] at this
    exact this (Iio_mem_nhds hη)
  obtain ⟨k, hk⟩ := hev.exists
  have := hge (φ k)
  exact absurd hk (not_lt.mpr this)

end KR26


namespace KR26

variable {n m : ℕ}

lemma tight {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    [IsProbabilityMeasure P] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Y : ℕ → Ω → E} {Yl : Ω' → E}
    (h : TendstoInDistribution Y atTop Yl (fun _ => P) μ') {e : ℝ≥0∞} (he : 0 < e) :
    ∃ R : ℝ, ∀ᶠ ν in atTop, P {ω | R ≤ ‖Y ν ω‖} < e := by
  set C : ℕ → Set E := fun k => {y | (k : ℝ) ≤ ‖y‖} with hC
  have hCc : ∀ k, IsClosed (C k) := fun k => isClosed_le continuous_const continuous_norm
  have hanti : Antitone C := by
    intro i j hij y hy
    simp only [hC, mem_setOf_eq] at hy ⊢
    exact le_trans (by exact_mod_cast hij) hy
  have hinter : (⋂ k, C k) = ∅ := by
    ext y
    simp only [mem_iInter, hC, mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall,
      not_le]
    exact exists_nat_gt ‖y‖
  have hlim := tendsto_measure_iInter_atTop (μ := μ'.map Yl)
    (fun k => (hCc k).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hlim
  obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds he)).exists
  refine ⟨K, ?_⟩
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto (hCc K)
  simp only [ProbabilityMeasure.coe_mk] at hport
  have hlt : limsup (fun ν => (P.map (Y ν)) (C K)) atTop < e :=
    lt_of_le_of_lt hport hK
  filter_upwards [eventually_lt_of_limsup_lt hlt] with ν hν
  rwa [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable ν) (hCc K).measurableSet] at hν

theorem prob_core {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (F : Rn n → Set (Rn m)) (x₀ : Rn n) (h0 : (0 : Rn m) ∈ F x₀)
    (hs : ∀ y, (contingentDeriv (svInv F) 0 x₀ y).Subsingleton) (L : Rn m → Rn n)
    (hL : ∀ y, L y ∈ contingentDeriv (svInv F) 0 x₀ y)
    (τ : ℕ → ℝ) (hτpos : ∀ ν, 0 < τ ν) (hτ : Tendsto τ atTop (𝓝 0))
    (x : ℕ → Ω → Rn n) (hx : ∀ ν, Measurable (x ν))
    (Y : ℕ → Ω → Rn m) (Yl : Ω' → Rn m)
    (hY : TendstoInDistribution Y atTop Yl (fun _ => P) μ')
    (hsel : ∀ᶠ ν in atTop, ∀ᵐ ω ∂P, τ ν • Y ν ω ∈ F (x ν ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun ν => x ν ω) atTop (𝓝 x₀)) :
    TendstoInDistribution (fun ν ω => (τ ν)⁻¹ • (x ν ω - x₀)) atTop
      (fun ω' => L (Yl ω')) (fun _ => P) μ' := by
  have hLc := L_cont F x₀ h0 hs L hL
  have hLY := hY.continuous_comp hLc
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hLY ?_
    (fun ν => (((hx ν).sub_const x₀).const_smul ((τ ν)⁻¹)).aemeasurable)
  have hxm : TendstoInMeasure P x atTop (fun _ => x₀) :=
    tendstoInMeasure_of_tendsto_ae (fun ν => (hx ν).aestronglyMeasurable) hlim
  rw [tendstoInMeasure_iff_norm] at hxm ⊢
  intro η hη
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨R, hR⟩ := tight hY (ENNReal.half_pos he.ne')
  obtain ⟨δ, hδ, hunif⟩ := unif F x₀ h0 hs L hL R η hη
  have hxδ := (hxm δ hδ) (gt_mem_nhds (ENNReal.half_pos he.ne'))
  filter_upwards [hR, hxδ, hsel, hτ (Iio_mem_nhds hδ)] with ν hRν hxν hselν hτν
  simp only [mem_preimage, mem_Iio] at hxν hτν
  calc P {ω | η ≤ ‖((fun ν ω => (τ ν)⁻¹ • (x ν ω - x₀)) - fun ν => L ∘ Y ν) ν ω - (0 : ℕ → Ω → Rn n) ν ω‖}
      ≤ P ({ω | R ≤ ‖Y ν ω‖} ∪ {ω | δ ≤ ‖x ν ω - x₀‖}) := by
        apply measure_mono_ae
        filter_upwards [hselν] with ω hω hmem
        simp only [mem_setOf_eq, Pi.sub_apply, Pi.zero_apply, sub_zero,
          Function.comp] at hmem
        by_contra hnot
        have h1 : ‖Y ν ω‖ < R := not_le.mp fun h => hnot (Or.inl h)
        have h2 : ‖x ν ω - x₀‖ < δ := not_le.mp fun h => hnot (Or.inr h)
        have := hunif (τ ν) (hτpos ν) hτν (Y ν ω) h1.le (x ν ω) h2 hω
        exact absurd hmem (not_le.mpr this)
    _ ≤ P {ω | R ≤ ‖Y ν ω‖} + P {ω | δ ≤ ‖x ν ω - x₀‖} := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hRν.le hxν.le
    _ = e := ENNReal.add_halves e

theorem prob_core' {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (F : Rn n → Set (Rn m)) (x₀ : Rn n) (h0 : (0 : Rn m) ∈ F x₀)
    (hs : ∀ y, (contingentDeriv (svInv F) 0 x₀ y).Subsingleton) (L : Rn m → Rn n)
    (hL : ∀ y, L y ∈ contingentDeriv (svInv F) 0 x₀ y)
    (τ : ℕ → ℝ) (hτpos : ∀ ν, 0 < τ ν) (hτ : Tendsto τ atTop (𝓝 0))
    (x : ℕ → Ω → Rn n) (hx : ∀ ν, Measurable (x ν))
    (Y : ℕ → Ω → Rn m) (Yl : Ω' → Rn m)
    (hY : TendstoInDistribution Y atTop Yl (fun _ => P) μ')
    (hsel : ∃ δ₁ > (0 : ℝ), ∀ᶠ ν in atTop, ∀ᵐ ω ∂P, ‖x ν ω - x₀‖ < δ₁ → τ ν • Y ν ω ∈ F (x ν ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun ν => x ν ω) atTop (𝓝 x₀)) :
    TendstoInDistribution (fun ν ω => (τ ν)⁻¹ • (x ν ω - x₀)) atTop
      (fun ω' => L (Yl ω')) (fun _ => P) μ' := by
  have hLc := L_cont F x₀ h0 hs L hL
  have hLY := hY.continuous_comp hLc
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hLY ?_
    (fun ν => (((hx ν).sub_const x₀).const_smul ((τ ν)⁻¹)).aemeasurable)
  have hxm : TendstoInMeasure P x atTop (fun _ => x₀) :=
    tendstoInMeasure_of_tendsto_ae (fun ν => (hx ν).aestronglyMeasurable) hlim
  rw [tendstoInMeasure_iff_norm] at hxm ⊢
  intro η hη
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  obtain ⟨R, hR⟩ := tight hY (ENNReal.half_pos he.ne')
  obtain ⟨δ₁, hδ₁, hsel⟩ := hsel
  obtain ⟨δ₂, hδ₂, hunif⟩ := unif F x₀ h0 hs L hL R η hη
  set δ := min δ₂ δ₁ with hδdef
  have hδ : 0 < δ := lt_min hδ₂ hδ₁
  have hxδ := (hxm δ hδ) (gt_mem_nhds (ENNReal.half_pos he.ne'))
  filter_upwards [hR, hxδ, hsel, hτ (Iio_mem_nhds hδ₂)] with ν hRν hxν hselν hτν
  simp only [mem_preimage, mem_Iio] at hxν hτν
  calc P {ω | η ≤ ‖((fun ν ω => (τ ν)⁻¹ • (x ν ω - x₀)) - fun ν => L ∘ Y ν) ν ω - (0 : ℕ → Ω → Rn n) ν ω‖}
      ≤ P ({ω | R ≤ ‖Y ν ω‖} ∪ {ω | δ ≤ ‖x ν ω - x₀‖}) := by
        apply measure_mono_ae
        filter_upwards [hselν] with ω hω hmem
        simp only [mem_setOf_eq, Pi.sub_apply, Pi.zero_apply, sub_zero,
          Function.comp] at hmem
        by_contra hnot
        have h1 : ‖Y ν ω‖ < R := not_le.mp fun h => hnot (Or.inl h)
        have h2 : ‖x ν ω - x₀‖ < δ := not_le.mp fun h => hnot (Or.inr h)
        have := hunif (τ ν) (hτpos ν) hτν (Y ν ω) h1.le (x ν ω)
          (lt_of_lt_of_le h2 (min_le_left _ _)) (hω (lt_of_lt_of_le h2 (min_le_right _ _)))
        exact absurd hmem (not_le.mpr this)
    _ ≤ P {ω | R ≤ ‖Y ν ω‖} + P {ω | δ ≤ ‖x ν ω - x₀‖} := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add hRν.le hxν.le
    _ = e := ENNReal.add_halves e

end KR26


namespace KR27

variable {m : ℕ}

lemma charFun_map_inner {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {G : Ω → Rn m}
    (hG : AEMeasurable G P) (t : Rn m) :
    charFun (P.map G) t = charFun (P.map (fun ω => inner ℝ t (G ω))) 1 := by
  have hG' : AEMeasurable (fun ω => inner ℝ t (G ω)) P :=
    (continuous_const.inner continuous_id).measurable.comp_aemeasurable hG
  rw [charFun_apply, charFun_apply_real, integral_map hG (by fun_prop),
    integral_map hG' (by fun_prop)]
  congr 1
  funext ω
  simp [real_inner_comm]

/-- Multivariate CLT, via Lévy's continuity theorem and the one-dimensional CLT (Cramér–Wold). -/
theorem clt_vec {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (X : ℕ → Ω → Rn m) (hXm : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (hX2 : MemLp (X 0) 2 P)
    (W : Ω' → Rn m) (hW : Measurable W)
    (hWlaw : ∀ ℓ : Rn m, μ'.map (fun ω' => inner ℝ ℓ (W ω')) =
      gaussianReal 0 (Var[fun ω => inner ℝ ℓ (X 0 ω); P]).toNNReal) :
    TendstoInDistribution
      (fun (ν : ℕ) ω => Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, X i ω - ∫ ω', X 0 ω' ∂P))
      atTop W (fun _ => P) μ' := by
  have hGm : ∀ ν : ℕ, Measurable (fun ω => Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν,
      X i ω - ∫ ω', X 0 ω' ∂P)) := by
    intro ν
    exact (((Finset.measurable_sum _ fun i _ => hXm i).const_smul ((ν : ℝ)⁻¹)).sub_const
      _).const_smul (Real.sqrt ν)
  refine ⟨fun ν => (hGm ν).aemeasurable, hW.aemeasurable,
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_⟩
  simp only [ProbabilityMeasure.coe_mk]
  set Xt : ℕ → Ω → ℝ := fun i ω => inner ℝ t (X i ω) with hXt
  have hcl : Continuous (fun v : Rn m => inner ℝ t v) := continuous_const.inner continuous_id
  have hXt2 : MemLp (Xt 0) 2 P := by
    have := (innerSL ℝ t).comp_memLp' hX2
    exact this
  have hindt : iIndepFun Xt P := hindep.comp (fun _ v => inner ℝ t v) fun _ => hcl.measurable
  have hidt : ∀ i, IdentDistrib (Xt i) (Xt 0) P P := fun i => (hident i).comp hcl.measurable
  have hlaw : HasLaw (fun ω' => inner ℝ t (W ω')) (gaussianReal 0 Var[Xt 0; P].toNNReal) μ' :=
    ⟨(hcl.measurable.comp hW).aemeasurable, hWlaw t⟩
  have h1 := tendstoInDistribution_inv_sqrt_mul_sum_sub hlaw hXt2 hindt hidt
  have h2 := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h1.tendsto) 1
  simp only [ProbabilityMeasure.coe_mk] at h2
  rw [charFun_map_inner μ' hW.aemeasurable t]
  convert h2 using 2 with ν
  rw [charFun_map_inner P (hGm ν).aemeasurable t]
  congr 2
  funext ω
  have hint : Integrable (X 0) P := hX2.integrable one_le_two
  have hE : P[Xt 0] = inner ℝ t (∫ ω', X 0 ω' ∂P) := by
    simp only [hXt]; exact integral_inner hint t
  rw [hE, inner_smul_right, inner_sub_right, inner_smul_right, inner_sum]
  simp only [hXt]
  rcases Nat.eq_zero_or_pos ν with h | h
  · subst h; simp
  · have hs : (0 : ℝ) < Real.sqrt ν := Real.sqrt_pos.mpr (by exact_mod_cast h)
    have hsq : Real.sqrt ν * Real.sqrt ν = ν := Real.mul_self_sqrt (Nat.cast_nonneg _)
    field_simp
    rw [sq, hsq]

end KR27


namespace KR27

lemma tid_congr {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {X X' : ℕ → Ω → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z (fun _ => P) μ') (heq : ∀ᶠ i in atTop, X i = X' i)
    (hX' : ∀ i, AEMeasurable (X' i) P) :
    TendstoInDistribution X' atTop Z (fun _ => P) μ' := by
  refine ⟨hX', h.aemeasurable_limit, h.tendsto.congr' ?_⟩
  filter_upwards [heq] with i hi
  apply Subtype.ext
  show P.map (X i) = P.map (X' i)
  rw [hi]

lemma equicont {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U : Set (Rn n)) [CompactSpace ↥U] (x₀' : ↥U)
    (μG : Measure C(↥U, Rn m)) [IsProbabilityMeasure μG]
    (H : ℕ → Ω → C(↥U, Rn m)) (hH : TendstoInDistribution H atTop id (fun _ => P) μG)
    (pr : ℕ → Ω → ↥U)
    (hpr : ∀ ε > (0 : ℝ), Tendsto (fun ν => P {ω | ε ≤ dist (pr ν ω) x₀'}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun ν ω => H ν ω x₀' - H ν ω (pr ν ω)) atTop 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro η hη
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  set C : ℕ → Set C(↥U, Rn m) := fun k =>
    {h | ∃ x : ↥U, dist x x₀' ≤ 1 / ((k : ℝ) + 1) ∧ η ≤ ‖h x₀' - h x‖} with hC
  have hCc : ∀ k, IsClosed (C k) := by
    intro k
    set S : Set (C(↥U, Rn m) × ↥U) :=
      {p | dist p.2 x₀' ≤ 1 / ((k : ℝ) + 1) ∧ η ≤ ‖p.1 x₀' - p.1 p.2‖} with hS
    have hSc : IsClosed S := by
      have h1 : IsClosed {p : C(↥U, Rn m) × ↥U | dist p.2 x₀' ≤ 1 / ((k : ℝ) + 1)} :=
        isClosed_le (continuous_snd.dist continuous_const) continuous_const
      have h2 : IsClosed {p : C(↥U, Rn m) × ↥U | η ≤ ‖p.1 x₀' - p.1 p.2‖} :=
        isClosed_le continuous_const
          ((((continuous_fst.eval continuous_const).sub continuous_eval)).norm)
      exact h1.inter h2
    have : C k = Prod.fst '' S := by
      ext h
      constructor
      · rintro ⟨x, hx1, hx2⟩
        exact ⟨(h, x), ⟨hx1, hx2⟩, rfl⟩
      · rintro ⟨⟨h', x⟩, ⟨hx1, hx2⟩, rfl⟩
        exact ⟨x, hx1, hx2⟩
    rw [this]
    exact isClosedMap_fst_of_compactSpace _ hSc
  have hanti : Antitone C := by
    intro i j hij h hh
    obtain ⟨x, hx1, hx2⟩ := hh
    refine ⟨x, le_trans hx1 ?_, hx2⟩
    apply one_div_le_one_div_of_le (by positivity)
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have hinter : (⋂ k, C k) = ∅ := by
    ext h
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hall
    choose xk hxk1 hxk2 using hall
    have hxl : Tendsto xk atTop (𝓝 x₀') := tendsto_iff_dist_tendsto_zero.mpr
      (squeeze_zero (fun k => dist_nonneg) hxk1 tendsto_one_div_add_atTop_nhds_zero_nat)
    have hcont : Tendsto (fun k => ‖h x₀' - h (xk k)‖) atTop (𝓝 0) := by
      have := ((h.continuous.tendsto x₀').comp hxl).const_sub (h x₀')
      simpa using this.norm
    obtain ⟨k, hk⟩ := (show ∀ᶠ k in atTop, ‖h x₀' - h (xk k)‖ < η from
      hcont (Iio_mem_nhds hη)).exists
    exact absurd (hxk2 k) (not_le.mpr hk)
  have hlim := tendsto_measure_iInter_atTop (μ := μG)
    (fun k => (hCc k).measurableSet.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at hlim
  obtain ⟨K, hK⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.half_pos he.ne'))).exists
  have hport := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hH.tendsto (hCc K)
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at hport
  have hlt : limsup (fun ν => (P.map (H ν)) (C K)) atTop < e / 2 :=
    lt_of_le_of_lt hport hK
  filter_upwards [eventually_lt_of_limsup_lt hlt,
    (hpr (1 / ((K : ℝ) + 1)) (by positivity)) (gt_mem_nhds (ENNReal.half_pos he.ne'))]
    with ν h1 h2
  rw [Measure.map_apply_of_aemeasurable (hH.forall_aemeasurable ν) (hCc K).measurableSet] at h1
  simp only [mem_preimage, mem_Iio] at h2
  calc P {ω | η ≤ ‖(fun ν ω => H ν ω x₀' - H ν ω (pr ν ω)) ν ω - (0 : ℕ → Ω → Rn m) ν ω‖}
      ≤ P (H ν ⁻¹' C K ∪ {ω | 1 / ((K : ℝ) + 1) ≤ dist (pr ν ω) x₀'}) := by
        apply measure_mono
        intro ω hω
        simp only [mem_setOf_eq, Pi.zero_apply, sub_zero] at hω
        by_cases hd : 1 / ((K : ℝ) + 1) ≤ dist (pr ν ω) x₀'
        · exact Or.inr hd
        · exact Or.inl ⟨pr ν ω, (not_le.mp hd).le, hω⟩
    _ ≤ P (H ν ⁻¹' C K) + P {ω | 1 / ((K : ℝ) + 1) ≤ dist (pr ν ω) x₀'} := measure_union_le _ _
    _ ≤ e / 2 + e / 2 := add_le_add h1.le h2.le
    _ = e := ENNReal.add_halves e

end KR27


theorem solution {n m : ℕ} {S Ω Ω' : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) [IsProbabilityMeasure P] (μ' : Measure Ω')
    [IsProbabilityMeasure μ']
    (U : Set (Rn n)) (x₀ : Rn n) (hUc : IsCompact U) (hU : U ∈ 𝓝 x₀)
    (f : Rn n → S → Rn m) (s : ℕ → Ω → S) (hP : ProbabilisticAssumptions U f s P)
    (hB : ∃ D : Rn n → Rn m, HasBDerivAt (expect f s P) D x₀)
    (N : Rn n → Set (Rn m)) (hN : IsClosed (graph N))
    (hNp : IsProtoDifferentiable N x₀ (-(expect f s P x₀)))
    (hM3 : IsSubinvertibleAt (FEst U f s P N) x₀)
    (hM4 : ∀ y, (contingentDeriv (svInv (FEst U f s P N)) 0 x₀ y).Subsingleton)
    (x : ℕ → Ω → Rn n) (hx : ∀ ν, Measurable (x ν))
    (hsel : ∀ ν, 1 ≤ ν → ∀ᵐ ω ∂P,
      ∃ v ∈ N (x ν ω), empMean f s ν ω (x ν ω) + v = 0)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun ν => x ν ω) atTop (𝓝 x₀))
    (W : Ω' → Rn m) (hW : Measurable W)
    (hWlaw : ∀ ℓ : Rn m, μ'.map (fun ω' => inner ℝ ℓ (W ω')) =
      gaussianReal 0 (Var[fun ω => inner ℝ ℓ (f x₀ (s 0 ω)); P]).toNNReal) :
    ∃ L : Rn m → Rn n,
      (∀ y : Rn m, L y ∈ contingentDeriv (svInv (FEst U f s P N)) 0 x₀ y) ∧
      TendstoInDistribution (fun (ν : ℕ) ω => Real.sqrt ν • (x ν ω - x₀)) atTop
        (fun ω' => L (-(W ω'))) (fun _ => P) μ' := by
  classical
  haveI : CompactSpace ↥U := isCompact_iff_compactSpace.mp hUc
  have hx₀U : x₀ ∈ U := mem_of_mem_nhds hU
  set x₀' : ↥U := ⟨x₀, hx₀U⟩ with hx₀'
  set F := FEst U f s P N with hFdef
  have h0 : (0 : Rn m) ∈ F x₀ := hM3.1
  have hne := KR26.cd_nonempty F x₀ hM3 hM4
  set L : Rn m → Rn n := fun y => (hne y).some with hLdef
  have hL : ∀ y, L y ∈ contingentDeriv (svInv F) 0 x₀ y := fun y => (hne y).some_mem
  refine ⟨L, hL, ?_⟩
  -- the C(U)-valued data
  set Ft : S → C(↥U, Rn m) := fun σ => ⟨fun y => f y σ, (hP.cont σ).restrict⟩ with hFt
  have hmeas' : ∀ y : ↥U, Measurable (fun σ => Ft σ y) := fun y => hP.meas y y.2
  have hP3' : ∃ y : ↥U, MemLp (fun ω => Ft (s 0 ω) y) 2 P := by
    obtain ⟨y, hy, h⟩ := hP.moment; exact ⟨⟨y, hy⟩, h⟩
  have hP4' : ∃ a : S → ℝ, MemLp (fun ω => a (s 0 ω)) 2 P ∧
      ∀ σ : S, ∀ x₁ x₂ : ↥U, ‖Ft σ x₁ - Ft σ x₂‖ ≤ a σ * ‖(x₁ : Rn n) - x₂‖ := by
    obtain ⟨a, ha, h⟩ := hP.lip
    exact ⟨a, ha, fun σ x₁ x₂ => h σ x₁ x₁.2 x₂ x₂.2⟩
  obtain ⟨μG, -, hA3⟩ := theorem_A3 P U Ft hmeas' s hP.meas_s hP.indep hP.ident hP3' hP4'
  have hFtm : Measurable Ft :=
    proposition_A1 P U Ft hmeas' s hP.meas_s hP.indep hP.ident hP3' hP4'
  -- integrability of `Ft ∘ s 0`
  obtain ⟨x₁, hx₁U, hm1⟩ := hP.moment
  obtain ⟨a, ha, hlip⟩ := hP.lip
  obtain ⟨Dm, hDm⟩ := hUc.isBounded.subset_closedBall x₁
  set D := max Dm 0 with hD
  have hbound : ∀ σ : S, ∀ y ∈ U, ‖f y σ‖ ≤ ‖f x₁ σ‖ + |a σ| * D := by
    intro σ y hy
    have h1 : ‖f y σ - f x₁ σ‖ ≤ a σ * ‖y - x₁‖ := hlip σ y hy x₁ hx₁U
    have h2 : ‖y - x₁‖ ≤ D := by
      have := hDm hy
      rw [mem_closedBall, dist_eq_norm] at this
      exact this.trans (le_max_left _ _)
    have h3 : a σ * ‖y - x₁‖ ≤ |a σ| * D :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
    calc ‖f y σ‖ ≤ ‖f x₁ σ‖ + ‖f y σ - f x₁ σ‖ := norm_le_insert' _ _
      _ ≤ ‖f x₁ σ‖ + |a σ| * D := by linarith
  have hgint : Integrable (fun ω => ‖f x₁ (s 0 ω)‖ + |a (s 0 ω)| * D) P :=
    (hm1.integrable one_le_two).norm.add ((ha.integrable one_le_two).abs.mul_const _)
  have hint : Integrable (fun ω => Ft (s 0 ω)) P := by
    refine hgint.mono' (hFtm.comp (hP.meas_s 0)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro y
    exact hbound (s 0 ω) y y.2
  have hI : ∀ y : ↥U, (∫ ω, Ft (s 0 ω) ∂P) y = expect f s P y := by
    intro y
    have := (ContinuousMap.evalCLM ℝ y : C(↥U, Rn m) →L[ℝ] Rn m).integral_comp_comm hint
    simp only [ContinuousMap.evalCLM_apply] at this
    rw [← this]
    rfl
  -- the processes
  set I := ∫ ω, Ft (s 0 ω) ∂P with hIdef
  set H : ℕ → Ω → C(↥U, Rn m) := fun ν ω =>
    Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, Ft (s i ω) - I) with hH
  have hHm : ∀ ν, Measurable (H ν) := by
    intro ν
    exact (((Finset.measurable_sum _ fun i _ => hFtm.comp (hP.meas_s i)).const_smul
      ((ν : ℝ)⁻¹)).sub_const _).const_smul (Real.sqrt ν)
  have hHapp : ∀ ν ω (y : ↥U), H ν ω y =
      Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f y (s i ω) - expect f s P y) := by
    intro ν ω y
    simp only [hH, ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.sum_apply]
    rw [hI]
    rfl
  set proj : Rn n → ↥U := fun y => if h : y ∈ U then ⟨y, h⟩ else x₀' with hproj
  have hprojm : Measurable proj := by
    exact Measurable.dite (s := U) (f := fun y : ↥U => y) (g := fun _ => x₀') measurable_id
      measurable_const hUc.isClosed.measurableSet
  set Y : ℕ → Ω → Rn m := fun ν ω => -(H ν ω (proj (x ν ω))) with hY
  have hYm : ∀ ν, AEMeasurable (Y ν) P := by
    intro ν
    exact (continuous_eval.measurable.comp ((hHm ν).prodMk (hprojm.comp (hx ν)))).neg.aemeasurable
  -- CLT at `x₀`
  have hfx₀m : Measurable (f x₀) := hP.meas x₀ hx₀U
  have hX2 : MemLp (fun ω => f x₀ (s 0 ω)) 2 P := by
    refine MemLp.of_le (hm1.norm.add ((ha.abs).mul_const D)) (hfx₀m.comp (hP.meas_s 0)).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have := hbound (s 0 ω) x₀ hx₀U
    simp only [Pi.add_apply, Real.norm_eq_abs]
    refine this.trans (le_trans ?_ (le_abs_self _))
    exact le_refl _
  have hclt := KR27.clt_vec P μ' (fun i ω => f x₀ (s i ω))
    (fun i => hfx₀m.comp (hP.meas_s i))
    (hP.indep.comp (fun _ => f x₀) fun _ => hfx₀m) (fun i => (hP.ident i).comp hfx₀m) hX2 W hW
    hWlaw
  have hGeq : (fun (ν : ℕ) ω => Real.sqrt ν • ((ν : ℝ)⁻¹ • ∑ i ∈ Finset.range ν, f x₀ (s i ω) -
      ∫ ω', f x₀ (s 0 ω') ∂P)) = fun ν ω => H ν ω x₀' := by
    funext ν ω; rw [hHapp]; rfl
  rw [hGeq] at hclt
  have hA := hclt.continuous_comp continuous_neg
  -- convergence in probability of `x`
  have hxm : TendstoInMeasure P x atTop (fun _ => x₀) :=
    tendstoInMeasure_of_tendsto_ae (fun ν => (hx ν).aestronglyMeasurable) hlim
  rw [tendstoInMeasure_iff_norm] at hxm
  have hprojd : ∀ y, dist (proj y) x₀' ≤ ‖y - x₀‖ := by
    intro y
    by_cases hy : y ∈ U
    · simp only [hproj, dif_pos hy, Subtype.dist_eq, hx₀', dist_eq_norm]; exact le_refl _
    · simp only [hproj, dif_neg hy, dist_self]; exact norm_nonneg _
  have hpr : ∀ ε > (0 : ℝ), Tendsto (fun ν => P {ω | ε ≤ dist (proj (x ν ω)) x₀'}) atTop (𝓝 0) := by
    intro ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hxm ε hε)
      (fun _ => bot_le) (fun ν => measure_mono fun ω hω => ?_)
    exact le_trans hω (hprojd _)
  have hEQ := KR27.equicont P U x₀' (μG : Measure C(↥U, Rn m)) H hA3 (fun ν ω => proj (x ν ω)) hpr
  have hYconv : TendstoInDistribution Y atTop (fun ω' => -(W ω')) (fun _ => P) μ' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub Y _ hA ?_ hYm
    have heq : (Y - fun ν => Neg.neg ∘ fun ω => H ν ω x₀') =
        fun ν ω => H ν ω x₀' - H ν ω (proj (x ν ω)) := by
      funext ν ω
      simp only [Pi.sub_apply, hY, Function.comp]
      abel
    rw [heq]; exact hEQ
  -- the scaling
  set τ : ℕ → ℝ := fun ν => if ν = 0 then 1 else (Real.sqrt ν)⁻¹ with hτ
  have hτpos : ∀ ν, 0 < τ ν := by
    intro ν
    by_cases h : ν = 0
    · simp [hτ, h]
    · simp only [hτ, if_neg h]
      exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero h))
  have hτ0 : Tendsto τ atTop (𝓝 0) := by
    have h1 : Tendsto (fun ν : ℕ => (Real.sqrt ν)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with ν hν
    simp only [hτ, if_neg (by omega : ν ≠ 0)]
  have hτinv : ∀ ν, 1 ≤ ν → (τ ν)⁻¹ = Real.sqrt ν := by
    intro ν hν
    simp only [hτ, if_neg (by omega : ν ≠ 0), inv_inv]
  obtain ⟨δ₁, hδ₁, hballU⟩ := Metric.mem_nhds_iff.mp hU
  have hsel' : ∃ δ₁ > (0 : ℝ), ∀ᶠ ν in atTop, ∀ᵐ ω ∂P,
      ‖x ν ω - x₀‖ < δ₁ → τ ν • Y ν ω ∈ F (x ν ω) := by
    refine ⟨δ₁, hδ₁, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with ν hν
    filter_upwards [hsel ν hν] with ω hω hclose
    obtain ⟨v, hvN, hv0⟩ := hω
    have hxU : x ν ω ∈ U := hballU (by rw [mem_ball, dist_eq_norm]; exact hclose)
    refine ⟨hxU, v, hvN, ?_⟩
    have hpx : proj (x ν ω) = ⟨x ν ω, hxU⟩ := by simp [hproj, hxU]
    have hs0 : Real.sqrt ν ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast hν)).ne'
    simp only [hY, hpx, hHapp]
    rw [smul_neg, smul_smul, show τ ν * Real.sqrt ν = 1 by
      rw [← hτinv ν hν, mul_inv_cancel₀ (hτpos ν).ne'], one_smul]
    have : v = -empMean f s ν ω (x ν ω) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hv0
    rw [this]
    simp only [empMean]
    abel
  have hmain := KR26.prob_core' P μ' F x₀ h0 hM4 L hL τ hτpos hτ0 x hx Y
    (fun ω' => -(W ω')) hYconv hsel' hlim
  refine KR27.tid_congr hmain ?_ (fun ν => (((hx ν).sub_const x₀).const_smul (Real.sqrt ν)).aemeasurable)
  filter_upwards [eventually_ge_atTop 1] with ν hν
  funext ω
  rw [hτinv ν hν]
