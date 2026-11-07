-- Prove2me | solution 1 for KingRockAsymp.Distribution.theorem_2_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T15:47:34.572823+00:00
-- url     : https://prove2.me/submissions/8940ede3-f721-472b-a112-b95c24cbc07c

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic
import Theorems.Thm_KingRockAsymp_Distribution_thm_2_4_display_upper_lipschitz

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

end KR26


namespace KRLipAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma slice {g : E → F} {D : E → F} {z : E} (hB : HasBDerivAt g D z) (w : E) :
    Tendsto (fun t : ℝ => t⁻¹ • (g (z + t • w) - g z)) (𝓝[>] (0 : ℝ)) (𝓝 (D w)) := by
  have h2 : Tendsto (fun t : ℝ => (t, w)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
    tendsto_id.prodMk tendsto_const_nhds
  exact (hB w).comp h2

lemma zero_eq {g : E → F} {D : E → F} {z : E} (hB : HasBDerivAt g D z) : D 0 = 0 := by
  have h := slice hB 0
  simp only [smul_zero, add_zero, sub_self] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma homog {g : E → F} {D : E → F} {z : E} (hB : HasBDerivAt g D z) {c : ℝ} (hc : 0 < c)
    (w : E) : D (c • w) = c • D w := by
  have h1 := slice hB (c • w)
  have hmul : Tendsto (fun t : ℝ => t * c) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => t * c) (𝓝 (0 : ℝ)) (𝓝 (0 * c)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht hc
  have h2 := ((slice hB w).comp hmul).const_smul c
  have heq : (fun t : ℝ => t⁻¹ • (g (z + t • (c • w)) - g z)) =
      (fun t : ℝ => c • ((fun t : ℝ => t⁻¹ • (g (z + t • w) - g z)) ∘ (fun t => t * c)) t) := by
    funext t
    simp only [Function.comp, smul_smul, mul_inv]
    rw [show c * (t⁻¹ * c⁻¹) = t⁻¹ by field_simp, mul_comm t c]
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

lemma bound {g : E → F} {D : E → F} {z : E} (hB : HasBDerivAt g D z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖D w‖ ≤ C * ‖w‖ := by
  have hD0 := zero_eq hB
  have h := hB 0 (ball_mem_nhds (D 0) one_pos)
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ht₂
  have hloc : ∀ w' : E, ‖w'‖ < δ → ‖D w'‖ ≤ 1 := by
    intro w' hw'
    have hs := (slice hB w').norm
    apply le_of_tendsto hs
    filter_upwards [ht₁] with t ht
    have hmem := hsub (mk_mem_prod ht (hδsub (by simpa using hw')))
    simp only [mem_preimage, mem_ball, hD0, dist_zero_right] at hmem
    exact hmem.le
  refine ⟨2 / δ, by positivity, fun w => ?_⟩
  by_cases hw : w = 0
  · simp [hw, hD0]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set c : ℝ := 2 * ‖w‖ / δ with hc_def
  have hc : 0 < c := by positivity
  have hw' : w = c • (c⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hn : ‖c⁻¹ • w‖ < δ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, hc_def]
    field_simp
    nlinarith
  rw [hw', homog hB hc, norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← hw']
  calc c * ‖D (c⁻¹ • w)‖ ≤ c * 1 := mul_le_mul_of_nonneg_left (hloc _ hn) hc.le
    _ = 2 / δ * ‖w‖ := by rw [hc_def]; ring


lemma bcont {g : E → F} {D : E → F} {z : E} (hB : HasBDerivAt g D z) : Continuous D := by
  rw [Metric.continuous_iff]
  intro w ε hε
  have h := hB w (ball_mem_nhds (D w) (half_pos hε))
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ht₂
  refine ⟨δ, hδ, fun w' hw' => ?_⟩
  have hle : dist (D w') (D w) ≤ ε / 2 := by
    apply le_of_tendsto ((slice hB w').dist tendsto_const_nhds)
    filter_upwards [ht₁] with t ht
    have hmem := hsub (mk_mem_prod ht (hδsub hw'))
    simp only [mem_preimage, mem_ball] at hmem
    exact hmem.le
  linarith

end KRLipAux

theorem solution {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [TopologicalSpace.SeparableSpace Z] [MeasurableSpace Z] [BorelSpace Z] {n m : ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P] (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) (z₀ : Z) (x₀ : Rn n) (Dz : Z → Rn m)
    (hM : AnalyticalAssumptions f N z₀ x₀ Dz)
    (τ : ℕ → ℝ) (hτpos : ∀ ν, 0 < τ ν) (hτ : Tendsto τ atTop (𝓝 0))
    (z : ℕ → Ω → Z) (hz : ∀ ν, Measurable (z ν))
    (W : Ω' → Z) (hW : Measurable W)
    (hconv : TendstoInDistribution (fun ν ω => (τ ν)⁻¹ • (z ν ω - z₀)) atTop W
      (fun _ => P) μ')
    (x : ℕ → Ω → Rn n) (hx : ∀ ν, Measurable (x ν))
    (hsel : ∀ ν, ∀ᵐ ω ∂P, x ν ω ∈ solMap f N (z ν ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun ν => x ν ω) atTop (𝓝 x₀)) :
    ∃ L : Z → Rn n,
      (∀ w : Z, L w ∈ contingentDeriv (svInv (fPlusN f N z₀)) 0 x₀ (-(Dz w))) ∧
      TendstoInDistribution (fun ν ω => (τ ν)⁻¹ • (x ν ω - x₀)) atTop
        (fun ω' => L (W ω')) (fun _ => P) μ' := by
  set F := fPlusN f N z₀ with hF
  have h0 : (0 : Rn m) ∈ F x₀ := hM.subinv.1
  have hs := hM.single
  have hne := KR26.cd_nonempty F x₀ hM.subinv hs
  set L' : Rn m → Rn n := fun y => (hne y).some with hL'def
  have hL' : ∀ y, L' y ∈ contingentDeriv (svInv F) 0 x₀ y := fun y => (hne y).some_mem
  refine ⟨fun w => L' (-(Dz w)), fun w => hL' _, ?_⟩
  have hB := hM.strong_z.1
  have hDc : Continuous Dz := KRLipAux.bcont hB
  have hD0 : Dz 0 = 0 := KRLipAux.zero_eq hB
  set V : ℕ → Ω → Z := fun ν ω => (τ ν)⁻¹ • (z ν ω - z₀) with hV
  set A : ℕ → Ω → Rn m := fun ν ω => -(Dz (V ν ω)) with hA
  set Y : ℕ → Ω → Rn m := fun ν ω => (τ ν)⁻¹ • (f z₀ (x ν ω) - f (z ν ω) (x ν ω)) with hY
  have hAconv : TendstoInDistribution A atTop (fun ω' => -(Dz (W ω'))) (fun _ => P) μ' :=
    hconv.continuous_comp (g := fun w => -(Dz w)) hDc.neg
  have hfm : Measurable (fun p : Z × Rn n => f p.1 p.2) := hM.continuous.measurable
  have hYm : ∀ ν, AEMeasurable (Y ν) P := by
    intro ν
    have h1 : Measurable (fun ω => f z₀ (x ν ω)) :=
      hfm.comp (measurable_const.prodMk (hx ν))
    have h2 : Measurable (fun ω => f (z ν ω) (x ν ω)) := hfm.comp ((hz ν).prodMk (hx ν))
    exact ((h1.sub h2).const_smul ((τ ν)⁻¹)).aemeasurable
  have hxm : TendstoInMeasure P x atTop (fun _ => x₀) :=
    tendstoInMeasure_of_tendsto_ae (fun ν => (hx ν).aestronglyMeasurable) hlim
  rw [tendstoInMeasure_iff_norm] at hxm
  have hYconv : TendstoInDistribution Y atTop (fun ω' => -(Dz (W ω'))) (fun _ => P) μ' := by
    refine tendstoInDistribution_of_tendstoInMeasure_sub Y _ hAconv ?_ hYm
    rw [tendstoInMeasure_iff_norm]
    intro η hη
    rw [ENNReal.tendsto_nhds_zero]
    intro e he
    have hVn := hconv.continuous_comp continuous_norm
    obtain ⟨R₀, hR₀⟩ := KR26.tight hVn (ENNReal.half_pos he.ne')
    set R : ℝ := max R₀ 1 with hRdef
    have hR1 : 1 ≤ R := le_max_right _ _
    have hR0 : 0 < R := by linarith
    set ε : ℝ := η / (R + 1) with hεdef
    have hε : 0 < ε := by positivity
    obtain ⟨Ωε, hΩε, Uε, hUε, hLip⟩ := hM.strong_z.2 ε hε
    obtain ⟨ρ', hρ', hball'⟩ := Metric.mem_nhds_iff.mp hΩε
    obtain ⟨ρ, hρ, hballU⟩ := Metric.mem_nhds_iff.mp hUε
    filter_upwards [hR₀, (hxm ρ hρ) (gt_mem_nhds (ENNReal.half_pos he.ne')),
      hτ (Iio_mem_nhds (show 0 < ρ' / R by positivity))] with ν h1 h2 h3
    simp only [mem_preimage, mem_Iio] at h2 h3
    calc P {ω | η ≤ ‖(Y - A) ν ω - (0 : ℕ → Ω → Rn m) ν ω‖}
        ≤ P ({ω | R₀ ≤ ‖((fun w => ‖w‖) ∘ V ν) ω‖} ∪ {ω | ρ ≤ ‖x ν ω - x₀‖}) := by
          apply measure_mono
          intro ω hω
          simp only [mem_setOf_eq, Pi.sub_apply, Pi.zero_apply, sub_zero] at hω
          by_contra hnot
          have hVlt : ‖V ν ω‖ < R₀ := by
            have : ¬ R₀ ≤ ‖((fun w => ‖w‖) ∘ V ν) ω‖ := fun h => hnot (Or.inl h)
            simpa [Function.comp, norm_norm] using this
          have hxlt : ‖x ν ω - x₀‖ < ρ := by
            have : ¬ ρ ≤ ‖x ν ω - x₀‖ := fun h => hnot (Or.inr h)
            exact not_le.mp this
          have hVR : ‖V ν ω‖ < R := lt_of_lt_of_le hVlt (le_max_left _ _)
          have hτν := hτpos ν
          have hzV : ‖z ν ω - z₀‖ = τ ν * ‖V ν ω‖ := by
            rw [hV]; simp only
            rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hτν, ← mul_assoc,
              mul_inv_cancel₀ hτν.ne', one_mul]
          have hzΩ : z ν ω ∈ Ωε := by
            apply hball'
            rw [mem_ball, dist_eq_norm, hzV]
            calc τ ν * ‖V ν ω‖ ≤ τ ν * R := mul_le_mul_of_nonneg_left hVR.le hτν.le
              _ < ρ' / R * R := mul_lt_mul_of_pos_right h3 hR0
              _ = ρ' := by field_simp
          have hxU : x ν ω ∈ Uε := hballU (by rw [mem_ball, dist_eq_norm]; exact hxlt)
          have hl := (hLip (x ν ω) hxU).dist_le_mul (z ν ω) hzΩ z₀ (mem_of_mem_nhds hΩε)
          rw [sub_self, sub_self, hD0, sub_zero, dist_eq_norm, dist_eq_norm, sub_zero,
            Real.coe_toNNReal _ hε.le] at hl
          have hhom : Dz (V ν ω) = (τ ν)⁻¹ • Dz (z ν ω - z₀) := by
            rw [hV]; exact KRLipAux.homog hB (inv_pos.mpr hτν) _
          have heq : Y ν ω - A ν ω = -((τ ν)⁻¹ •
              (f (z ν ω) (x ν ω) - f z₀ (x ν ω) - Dz (z ν ω - z₀))) := by
            simp only [hY, hA, hhom, smul_sub]
            abel
          rw [heq, norm_neg, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hτν] at hω
          have hb : (τ ν)⁻¹ * ‖f (z ν ω) (x ν ω) - f z₀ (x ν ω) - Dz (z ν ω - z₀)‖
              ≤ ε * ‖V ν ω‖ := by
            rw [inv_mul_le_iff₀ hτν]
            calc ‖f (z ν ω) (x ν ω) - f z₀ (x ν ω) - Dz (z ν ω - z₀)‖ ≤ ε * ‖z ν ω - z₀‖ := hl
              _ = τ ν * (ε * ‖V ν ω‖) := by rw [hzV]; ring
          have hεR : ε * ‖V ν ω‖ < η := by
            calc ε * ‖V ν ω‖ ≤ ε * R := mul_le_mul_of_nonneg_left hVR.le hε.le
              _ = η * (R / (R + 1)) := by rw [hεdef]; ring
              _ < η * 1 := mul_lt_mul_of_pos_left
                  (by rw [div_lt_one (by linarith)]; linarith) hη
              _ = η := mul_one η
          linarith
      _ ≤ P {ω | R₀ ≤ ‖((fun w => ‖w‖) ∘ V ν) ω‖} + P {ω | ρ ≤ ‖x ν ω - x₀‖} :=
          measure_union_le _ _
      _ ≤ e / 2 + e / 2 := add_le_add h1.le h2.le
      _ = e := ENNReal.add_halves e
  have hsel' : ∀ᶠ ν in atTop, ∀ᵐ ω ∂P, τ ν • Y ν ω ∈ F (x ν ω) := by
    refine Eventually.of_forall fun ν => ?_
    filter_upwards [hsel ν] with ω hω
    obtain ⟨v, hvN, hv0⟩ := hω
    have e1 : τ ν • Y ν ω = f z₀ (x ν ω) - f (z ν ω) (x ν ω) := by
      rw [hY]; simp only
      rw [smul_smul, mul_inv_cancel₀ (hτpos ν).ne', one_smul]
    rw [e1]
    refine ⟨v, hvN, ?_⟩
    have : v = -f (z ν ω) (x ν ω) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hv0.symm
    rw [this, sub_eq_add_neg]
  exact KR26.prob_core P μ' F x₀ h0 hs L' hL' τ hτpos hτ x hx Y _ hYconv hsel' hlim
