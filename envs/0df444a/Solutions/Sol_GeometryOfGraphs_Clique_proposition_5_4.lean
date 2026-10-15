-- Prove2me | solution 1 for GeometryOfGraphs.Clique.proposition_5_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T22:54:54.698087+00:00
-- url     : https://prove2.me/submissions/64702eeb-3852-492b-86a0-14ec9a7917f2

import Mathlib
import Definitions.Def_GeometryOfGraphs_Clique_isoDim

set_option autoImplicit false

open MeasureTheory Metric Set in
/-- Danzer–Grünbaum / Petty: an equilateral set in a `d`-dimensional normed space has at most `2^d` points. -/
theorem equilateral_card_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (n : ℕ) (x : Fin n → E)
    (hx : ∀ i j, i ≠ j → dist (x i) (x j) = 1) : n ≤ 2 ^ Module.finrank ℝ E := by
  by_contra hcon
  rw [not_le] at hcon
  set d := Module.finrank ℝ E with hd
  have hn : (2 : ℝ) ^ d < n := by exact_mod_cast hcon
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hcon
  -- choose λ < 1/2 with n λ^d > 1
  have hev : ∀ᶠ l : ℝ in nhds (1/2 : ℝ), 1 < (n : ℝ) * l ^ d := by
    have hc : Continuous fun l : ℝ => (n : ℝ) * l ^ d := continuous_const.mul (continuous_pow d)
    refine hc.continuousAt.eventually (lt_mem_nhds ?_)
    have : (n : ℝ) * (1/2 : ℝ) ^ d = n / 2 ^ d := by
      rw [one_div, inv_pow, div_eq_mul_inv]
    change 1 < (n : ℝ) * (1/2 : ℝ) ^ d
    rw [this, lt_div_iff₀ (by positivity)]
    simpa using hn
  have hev2 : ∀ᶠ l : ℝ in nhdsWithin (1/2 : ℝ) (Set.Iio (1/2)), 1 < (n : ℝ) * l ^ d ∧ 0 < l := by
    have h0 : ∀ᶠ l : ℝ in nhds (1/2 : ℝ), 0 < l := lt_mem_nhds (by norm_num)
    exact (hev.and h0).filter_mono nhdsWithin_le_nhds
  obtain ⟨l, ⟨hl1, hl0⟩, hlhalf⟩ := (hev2.and self_mem_nhdsWithin).exists
  have hlhalf' : l < 1/2 := hlhalf
  set δ : ℝ := ((1 - l) / l - 1) / 4 with hδ
  have hratio : 1 < (1 - l) / l := by
    rw [lt_div_iff₀ hl0]; linarith
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hlt : 1 + 2 * δ < (1 - l) / l := by rw [hδ]; linarith
  -- the convex body
  set P : Set E := convexHull ℝ (Set.range x) with hP
  set Q : Set E := cthickening δ P with hQ
  have hPcomp : IsCompact P := Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.finite_range x)
  have hQcomp : IsCompact Q := hPcomp.cthickening
  have hQconv : Convex ℝ Q := (convex_convexHull ℝ _).cthickening δ
  have hxP : ∀ i, x i ∈ P := fun i => subset_convexHull ℝ _ (Set.mem_range_self i)
  have hxQ : ∀ i, x i ∈ Q := fun i => self_subset_cthickening _ (hxP i)
  have hdiamrange : diam (Set.range x) ≤ 1 := by
    refine Metric.diam_le_of_forall_dist_le zero_le_one ?_
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    by_cases h : i = j
    · subst h; simp
    · exact (hx i j h).le
  have hdiamP : diam P ≤ 1 := by
    rw [hP, convexHull_diam]; exact hdiamrange
  have hdiamQ : diam Q ≤ 1 + 2 * δ := by
    have := diam_cthickening_le (s := P) (ε := δ) hδpos.le
    linarith
  -- Haar measure
  let μ : Measure E := Measure.addHaar
  have hQmeas : MeasurableSet Q := hQcomp.isClosed.measurableSet
  have hQfin : μ Q < ⊤ := hQcomp.measure_lt_top
  have hQpos : 0 < μ Q := by
    have hx0 : x ⟨0, hnpos⟩ ∈ P := hxP _
    have hsub : ball (x ⟨0, hnpos⟩) δ ⊆ Q := by
      intro z hz
      apply thickening_subset_cthickening
      exact mem_thickening_iff.2 ⟨_, hx0, by simpa [dist_comm] using hz⟩
    exact lt_of_lt_of_le (Metric.isOpen_ball.measure_pos μ ⟨_, mem_ball_self hδpos⟩) (measure_mono hsub)
  -- the pieces
  let T : Fin n → Set E := fun i => AffineMap.homothety (x i) l '' Q
  have hTsub : ∀ i, T i ⊆ Q := by
    rintro i _ ⟨q, hq, rfl⟩
    have := hQconv (hxQ i) hq (by linarith : (0:ℝ) ≤ 1 - l) hl0.le (by ring)
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    convert this using 1
    module
  have hTmeas : ∀ i, MeasurableSet (T i) := fun i => by
    have : IsCompact (T i) := hQcomp.image (AffineMap.homothety (x i) l).continuous_of_finiteDimensional
    exact this.isClosed.measurableSet
  have hTmeasure : ∀ i, μ (T i) = ENNReal.ofReal (l ^ d) * μ Q := fun i => by
    show μ (AffineMap.homothety (x i) l '' Q) = _
    rw [Measure.addHaar_image_homothety, abs_of_pos (pow_pos hl0 _), ← hd]
  have hTdisj : Pairwise (Function.onFun Disjoint T) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro z ⟨q, hq, rfl⟩ ⟨q', hq', hz⟩
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add] at hz
    have h1 : l • (q - q') = (1 - l) • (x j - x i) := by
      linear_combination (norm := module) (-1 : ℝ) • hz
    have h2 : l * dist q q' = 1 - l := by
      have := congrArg norm h1
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hl0,
        abs_of_pos (by linarith : (0:ℝ) < 1 - l), ← dist_eq_norm, ← dist_eq_norm,
        hx j i (Ne.symm hij)] at this
      simpa using this
    have h3 : dist q q' ≤ 1 + 2 * δ :=
      (dist_le_diam_of_mem hQcomp.isBounded hq hq').trans hdiamQ
    have h4 : l * dist q q' ≤ l * (1 + 2 * δ) := mul_le_mul_of_nonneg_left h3 hl0.le
    rw [lt_div_iff₀ hl0] at hlt
    nlinarith
  have hunion : μ (⋃ i, T i) = ∑ i, μ (T i) := by
    rw [measure_iUnion hTdisj hTmeas, tsum_fintype]
  have hle : μ (⋃ i, T i) ≤ μ Q := measure_mono (Set.iUnion_subset hTsub)
  rw [hunion] at hle
  simp only [hTmeasure, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  have h5 : ((n : ENNReal) * ENNReal.ofReal (l ^ d)) * μ Q ≤ 1 * μ Q := by
    rw [one_mul, mul_assoc]; exact hle
  have h6 := (ENNReal.mul_le_mul_iff_left hQpos.ne' hQfin.ne).1 h5
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_le_one] at h6
  linarith

/-- Type synonym carrying the norm `N`. -/
def NT {d : ℕ} (_N : (Fin d → ℝ) → ℝ) : Type := Fin d → ℝ

/-- Coercion into the synonym. -/
def NT.of {d : ℕ} {N : (Fin d → ℝ) → ℝ} (v : Fin d → ℝ) : NT N := v

instance NT.instAddCommGroup {d : ℕ} (N : (Fin d → ℝ) → ℝ) : AddCommGroup (NT N) :=
  inferInstanceAs (AddCommGroup (Fin d → ℝ))

instance NT.instModule {d : ℕ} (N : (Fin d → ℝ) → ℝ) : Module ℝ (NT N) :=
  inferInstanceAs (Module ℝ (Fin d → ℝ))

noncomputable instance NT.instNormedAddCommGroup {d : ℕ} (N : (Fin d → ℝ) → ℝ)
    [h : Fact (GeometryOfGraphs.Clique.IsNormFun N)] : NormedAddCommGroup (NT N) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun v : NT N => N (show Fin d → ℝ from v)
      map_zero' := by
        have h0 := h.out.2.2.1 0 (0 : Fin d → ℝ)
        simp only [zero_smul, abs_zero, zero_mul] at h0
        exact h0
      add_le' := fun a b => h.out.2.2.2 a b
      neg' := fun a => by
        have h1 := h.out.2.2.1 (-1) (show Fin d → ℝ from a)
        rw [neg_smul, one_smul, abs_neg, abs_one, one_mul] at h1
        exact h1
      eq_zero_of_map_eq_zero' := fun a ha => h.out.2.1 a ha }

noncomputable instance NT.instNormedSpace {d : ℕ} (N : (Fin d → ℝ) → ℝ)
    [h : Fact (GeometryOfGraphs.Clique.IsNormFun N)] : NormedSpace ℝ (NT N) where
  norm_smul_le := fun a v => (h.out.2.2.1 a (show Fin d → ℝ from v)).le

instance NT.instFiniteDimensional {d : ℕ} (N : (Fin d → ℝ) → ℝ) : FiniteDimensional ℝ (NT N) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin d → ℝ))

theorem NT.finrank {d : ℕ} (N : (Fin d → ℝ) → ℝ) : Module.finrank ℝ (NT N) = d :=
  Module.finrank_fin_fun ℝ

theorem lower_card_le {n d : ℕ} (N : (Fin d → ℝ) → ℝ) (hN : GeometryOfGraphs.Clique.IsNormFun N)
    (φ : Fin n → (Fin d → ℝ)) (h : ∀ i j, i ≠ j → N (φ i - φ j) = 1) : n ≤ 2 ^ d := by
  haveI : Fact (GeometryOfGraphs.Clique.IsNormFun N) := ⟨hN⟩
  letI : MeasurableSpace (NT N) := borel _
  haveI : BorelSpace (NT N) := ⟨rfl⟩
  have := equilateral_card_le (E := NT N) n (fun i => (NT.of (N := N) (φ i))) (fun i j hij => by
    rw [dist_eq_norm]
    exact h i j hij)
  rwa [NT.finrank] at this

theorem embeds_clog (n : ℕ) :
    GeometryOfGraphs.Clique.EmbedsIsometrically (Nat.clog 2 n)
      (fun i j : Fin n => (((⊤ : SimpleGraph (Fin n)).dist i j : ℕ) : ℝ)) := by
  classical
  set d := Nat.clog 2 n with hd
  have hcard : Fintype.card (Fin n) ≤ Fintype.card (Fin d → Bool) := by
    simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
    exact Nat.le_pow_clog (by norm_num) n
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun v => ‖v‖, ⟨fun x => norm_nonneg _, fun x hx => norm_eq_zero.1 hx,
    fun a x => by show ‖a • x‖ = |a| * ‖x‖; rw [norm_smul, Real.norm_eq_abs], fun x y => norm_add_le _ _⟩,
    fun i k => if f i k then 1 else 0, ?_⟩
  intro x y
  by_cases h : x = y
  · subst h; simp
  · have hd1 : (⊤ : SimpleGraph (Fin n)).dist x y = 1 := SimpleGraph.dist_top_of_ne h
    show ‖(fun k => if f x k then (1:ℝ) else 0) - (fun k => if f y k then (1:ℝ) else 0)‖ = (((⊤ : SimpleGraph (Fin n)).dist x y : ℕ) : ℝ)
    rw [hd1, Nat.cast_one]
    have hne : f x ≠ f y := fun e => h (f.injective e)
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro k'
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      cases f x k' <;> cases f y k' <;> simp
    · have h1 : (1 : ℝ) = ‖((fun k => if f x k then (1:ℝ) else 0) -
          (fun k => if f y k then (1:ℝ) else 0)) k‖ := by
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        revert hk
        cases f x k <;> cases f y k <;> simp
      exact h1.le.trans (norm_le_pi_norm ((fun k => if f x k then (1:ℝ) else 0) -
          (fun k => if f y k then (1:ℝ) else 0)) k)

open GeometryOfGraphs.Clique in
theorem solution (n : ℕ) (hn : 0 < n) :
    isoDim (fun i j : Fin n => ((⊤ : SimpleGraph (Fin n)).dist i j : ℝ)) =
      Nat.clog 2 n := by
  have hmem : Nat.clog 2 n ∈ {d : ℕ | EmbedsIsometrically d
      (fun i j : Fin n => ((⊤ : SimpleGraph (Fin n)).dist i j : ℝ))} := embeds_clog n
  have hlow : ∀ d ∈ {d : ℕ | EmbedsIsometrically d
      (fun i j : Fin n => ((⊤ : SimpleGraph (Fin n)).dist i j : ℝ))}, Nat.clog 2 n ≤ d := by
    rintro d ⟨N, hN, φ, hφ⟩
    apply Nat.clog_le_of_le_pow
    refine lower_card_le N hN φ (fun i j hij => ?_)
    rw [hφ i j]
    simp [SimpleGraph.dist_top_of_ne hij]
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ hlow)
