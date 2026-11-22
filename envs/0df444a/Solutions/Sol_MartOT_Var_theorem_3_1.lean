-- Prove2me | solution 1 for MartOT.Var.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:37:24.468082+00:00
-- url     : https://prove2.me/submissions/7c228eab-08cb-46f5-b679-00ee439c2f59

import Mathlib

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal CompactlySupported

section Helpers

/-- Kellerer's upper capacity functional `I(μ, A)`: the infimum of `∑ i, ∫⁻ f i dμ`
over Borel measurable `f : Fin n → X → ℝ≥0∞` satisfying `∑ i, f i (z i) ≥ 1` on `A`. -/
private noncomputable def cap {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (n : ℕ) (A : Set (Fin n → X)) : ℝ≥0∞ :=
  sInf { t : ℝ≥0∞ | ∃ f : Fin n → X → ℝ≥0∞,
    (∀ i, Measurable (f i)) ∧ (∀ z ∈ A, 1 ≤ ∑ i, f i (z i)) ∧
    t = ∑ i, ∫⁻ x, f i x ∂μ }

private lemma cap_mono {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} {A B : Set (Fin n → X)} (hAB : A ⊆ B) :
    cap μ n A ≤ cap μ n B := by
  apply sInf_le_sInf
  rintro t ⟨f, hf, hB, rfl⟩
  exact ⟨f, hf, fun z hz => hB z (hAB hz), rfl⟩

private lemma cap_le_of_witness {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} {A : Set (Fin n → X)} (f : Fin n → X → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hA : ∀ z ∈ A, 1 ≤ ∑ i, f i (z i)) :
    cap μ n A ≤ ∑ i, ∫⁻ x, f i x ∂μ :=
  sInf_le ⟨f, hf, hA, rfl⟩

private lemma cap_empty {X : Type*} [MeasurableSpace X] (μ : Measure X) (n : ℕ) :
    cap μ n ∅ = 0 := by
  refine le_antisymm ?_ bot_le
  calc cap μ n ∅
    _ ≤ ∑ _i : Fin n, ∫⁻ _x, (0 : ℝ≥0∞) ∂μ :=
        cap_le_of_witness μ (fun _ _ => 0) (fun _ => measurable_const) (fun _ h => h.elim)
    _ = 0 := by simp

private lemma cap_le_measure_univ {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {n : ℕ} (hn : 0 < n) (A : Set (Fin n → X)) :
    cap μ n A ≤ μ Set.univ := by
  let i₀ : Fin n := ⟨0, hn⟩
  let f : Fin n → X → ℝ≥0∞ := fun i _ => if i = i₀ then 1 else 0
  calc cap μ n A
    _ ≤ ∑ i : Fin n, ∫⁻ x, f i x ∂μ :=
        cap_le_of_witness μ f
          (fun i => by dsimp [f]; split_ifs <;> exact measurable_const)
          (fun z _ => by simp [f])
    _ = μ Set.univ := by
        rw [Finset.sum_eq_single i₀]
        · simp [f]
        · intro i _ hi; simp [f, hi]
        · intro h; exact (h (Finset.mem_univ i₀)).elim

/-- If `cap ζ n M = 0`, then `M` is covered by `n` sets whose `i`-th projections are `ζ`-null. -/
private lemma null_cover_of_cap_eq_zero {Z : Type*} [MeasurableSpace Z]
    (ζ : Measure Z) {n : ℕ} {M : Set (Fin n → Z)} (hcap : cap ζ n M = 0) :
    ∃ Ms : Fin n → Set (Fin n → Z),
      (∀ i, ζ ((fun z : Fin n → Z => z i) '' Ms i) = 0) ∧ M ⊆ ⋃ i, Ms i := by
  have hex : ∀ k : ℕ, ∃ f : Fin n → Z → ℝ≥0∞,
      (∀ i, Measurable (f i)) ∧ (∀ z ∈ M, 1 ≤ ∑ i, f i (z i)) ∧
      ∑ i, ∫⁻ x, f i x ∂ζ < (2 : ℝ≥0∞)⁻¹ ^ k := by
    intro k
    have hpos : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ k :=
      ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) k
    have hlt : cap ζ n M < (2 : ℝ≥0∞)⁻¹ ^ k := by rw [hcap]; exact hpos
    rcases (sInf_lt_iff.mp hlt) with ⟨t, ⟨f, hf, hM, rfl⟩, ht⟩
    exact ⟨f, hf, hM, ht⟩
  choose f hf_meas hf_cov hf_int using hex
  let g : Fin n → Z → ℝ≥0∞ := fun i x => ∑' k, f k i x
  let N : Fin n → Set Z := fun i => { x | g i x = ⊤ }
  have hN_zero : ∀ i, ζ (N i) = 0 := by
    intro i
    have hlt_top : ∫⁻ x, g i x ∂ζ < ⊤ := by
      have htsum : ∫⁻ x, g i x ∂ζ = ∑' k, ∫⁻ x, f k i x ∂ζ :=
        lintegral_tsum fun k => (hf_meas k i).aemeasurable
      rw [htsum]
      calc ∑' k, ∫⁻ x, f k i x ∂ζ
        _ ≤ ∑' k, ∑ j, ∫⁻ x, f k j x ∂ζ :=
            ENNReal.tsum_le_tsum fun k =>
              Finset.single_le_sum (f := fun j => ∫⁻ x, f k j x ∂ζ)
                (fun _ _ => bot_le) (Finset.mem_univ i)
        _ ≤ ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k :=
            ENNReal.tsum_le_tsum fun k => (hf_int k).le
        _ = (1 - (2 : ℝ≥0∞)⁻¹)⁻¹ := ENNReal.tsum_geometric _
        _ < ⊤ := by
            rw [ENNReal.inv_lt_top]
            exact tsub_pos_iff_lt.mpr (by
              rw [ENNReal.inv_lt_one]
              norm_num)
    have hae := ae_lt_top (Measurable.tsum fun k => hf_meas k i) hlt_top.ne
    rw [ae_iff] at hae
    convert hae using 2
    ext x; simp [N, g]
  refine ⟨fun i => { z : Fin n → Z | z i ∈ N i }, ?_, ?_⟩
  · intro i
    refine measure_mono_null ?_ (hN_zero i)
    rintro x ⟨z, hz, rfl⟩
    exact hz
  · intro z hz
    have htop : ∑ i : Fin n, g i (z i) = ⊤ := by
      have h1 : (⊤ : ℝ≥0∞) = ∑' (_k : ℕ), (1 : ℝ≥0∞) := by
        symm
        exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
      rw [eq_top_iff, h1]
      calc ∑' (_k : ℕ), (1 : ℝ≥0∞)
        _ ≤ ∑' k, ∑ i : Fin n, f k i (z i) := ENNReal.tsum_le_tsum fun k => hf_cov k z hz
        _ = ∑ i : Fin n, ∑' k, f k i (z i) :=
            Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    rcases ENNReal.sum_eq_top.mp htop with ⟨i, _, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Helper: truncating an `ℝ≥0∞` witness to `[0, 1]` real functions preserves the covering condition
and does not increase the integral sum. -/
private lemma exists_bounded_real_witness {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {n : ℕ} {A : Set (Fin n → X)}
    {L : ℝ} (hL : 0 ≤ L) (hcap : cap μ n A ≤ ENNReal.ofReal L) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Fin n → X → ℝ,
      (∀ i, Measurable (f i)) ∧ (∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) ∧
      (∀ z ∈ A, 1 ≤ ∑ i, f i (z i)) ∧
      ∑ i, ∫ x, f i x ∂μ ≤ L + ε := by
  have hlt : cap μ n A < ENNReal.ofReal (L + ε) := by
    refine lt_of_le_of_lt hcap ?_
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr (by linarith)
  rcases (sInf_lt_iff.mp hlt) with ⟨t, ⟨u, hu_meas, hu_cov, rfl⟩, ht⟩
  let f : Fin n → X → ℝ := fun i x => (min (u i x) 1).toReal
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ((hu_meas i).min measurable_const).ennreal_toReal
  · intro i x
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)
  · intro z hz
    by_cases h1 : ∃ i, 1 ≤ u i (z i)
    · rcases h1 with ⟨i, hi⟩
      have hfi : f i (z i) = 1 := by
        simp [f, min_eq_right hi]
      calc (1 : ℝ) = f i (z i) := hfi.symm
        _ ≤ ∑ j, f j (z j) :=
            Finset.single_le_sum (f := fun j => f j (z j))
              (fun j _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)
    · push Not at h1
      have hsum_eq : ENNReal.ofReal (∑ i, f i (z i)) = ∑ i, u i (z i) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hlt1 : u i (z i) < 1 := h1 i
        have hne : u i (z i) ≠ ⊤ := ne_top_of_lt (hlt1.trans ENNReal.one_lt_top)
        simp [min_eq_left hlt1.le, ENNReal.ofReal_toReal hne]
      have hge : ENNReal.ofReal 1 ≤ ENNReal.ofReal (∑ i, f i (z i)) := by
        rw [ENNReal.ofReal_one, hsum_eq]
        exact hu_cov z hz
      exact (ENNReal.ofReal_le_ofReal_iff
        (Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg)).mp hge
  · have hsum_le : ENNReal.ofReal (∑ i, ∫ x, f i x ∂μ) ≤ ENNReal.ofReal (L + ε) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        integral_nonneg fun x => ENNReal.toReal_nonneg)]
      calc ∑ i, ENNReal.ofReal (∫ x, f i x ∂μ)
        _ = ∑ i, ∫⁻ x, ENNReal.ofReal (f i x) ∂μ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hint : Integrable (f i) μ :=
              Integrable.of_bound ((hu_meas i).min measurable_const |>.ennreal_toReal.aestronglyMeasurable)
                1 (Eventually.of_forall fun x => by
                  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
                  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp))
            exact (ofReal_integral_eq_lintegral_ofReal hint
              (Eventually.of_forall fun x => ENNReal.toReal_nonneg))
        _ ≤ ∑ i, ∫⁻ x, u i x ∂μ := by
            refine Finset.sum_le_sum fun i _ => lintegral_mono fun x => ?_
            have hne : min (u i x) 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
            simp only [f, ENNReal.ofReal_toReal hne]
            exact min_le_left _ _
        _ ≤ ENNReal.ofReal (L + ε) := ht.le
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).mp hsum_le

/-- Finite convex combinations from the tail `k ≥ m` of a sequence of function tuples. -/
private def IsTailConv {X : Type*} {n : ℕ} (f : ℕ → Fin n → X → ℝ) (m : ℕ)
    (w : Fin n → X → ℝ) : Prop :=
  ∃ (s : Finset ℕ) (c : ℕ → ℝ),
    (∀ k ∈ s, m ≤ k) ∧ (∀ k ∈ s, 0 ≤ c k) ∧ (∑ k ∈ s, c k = 1) ∧
    ∀ i x, w i x = ∑ k ∈ s, c k * f k i x

private lemma isTailConv_self {X : Type*} {n : ℕ} (f : ℕ → Fin n → X → ℝ) (m : ℕ) :
    IsTailConv f m (f m) :=
  ⟨{m}, fun _ => 1, by simp, by simp, by simp, fun _ _ => by simp⟩

private lemma isTailConv_mono {X : Type*} {n : ℕ} {f : ℕ → Fin n → X → ℝ}
    {m m' : ℕ} (hmm' : m ≤ m') {w : Fin n → X → ℝ} (hw : IsTailConv f m' w) :
    IsTailConv f m w := by
  rcases hw with ⟨s, c, hs, hc0, hc1, hweq⟩
  exact ⟨s, c, fun k hk => hmm'.trans (hs k hk), hc0, hc1, hweq⟩

private lemma isTailConv_midpoint {X : Type*} {n : ℕ} {f : ℕ → Fin n → X → ℝ}
    {m : ℕ} {u v : Fin n → X → ℝ} (hu : IsTailConv f m u) (hv : IsTailConv f m v) :
    IsTailConv f m (fun i x => (u i x + v i x) / 2) := by
  classical
  rcases hu with ⟨s₁, c₁, hs₁, hc₁0, hc₁1, hu_eq⟩
  rcases hv with ⟨s₂, c₂, hs₂, hc₂0, hc₂1, hv_eq⟩
  let c : ℕ → ℝ := fun k => ((if k ∈ s₁ then c₁ k else 0) + (if k ∈ s₂ then c₂ k else 0)) / 2
  refine ⟨s₁ ∪ s₂, c, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases Finset.mem_union.mp hk with h1 | h2
    · exact hs₁ k h1
    · exact hs₂ k h2
  · intro k _
    dsimp [c]
    have h1 : 0 ≤ (if k ∈ s₁ then c₁ k else 0) := by split_ifs with h <;> [exact hc₁0 k h; exact le_rfl]
    have h2 : 0 ≤ (if k ∈ s₂ then c₂ k else 0) := by split_ifs with h <;> [exact hc₂0 k h; exact le_rfl]
    linarith
  · have hsum1 : ∑ k ∈ s₁ ∪ s₂, (if k ∈ s₁ then c₁ k else 0) = 1 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.union_inter_cancel_left]
      exact hc₁1
    have hsum2 : ∑ k ∈ s₁ ∪ s₂, (if k ∈ s₂ then c₂ k else 0) = 1 := by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.union_inter_cancel_right]
      exact hc₂1
    simp only [c, ← Finset.sum_div, Finset.sum_add_distrib, hsum1, hsum2]
    norm_num
  · intro i x
    have hsum1 : ∑ k ∈ s₁ ∪ s₂, (if k ∈ s₁ then c₁ k else 0) * f k i x = u i x := by
      rw [hu_eq i x]
      have : ∀ k ∈ s₁ ∪ s₂, (if k ∈ s₁ then c₁ k else 0) * f k i x =
          if k ∈ s₁ then c₁ k * f k i x else 0 := fun k _ => by split_ifs <;> simp
      rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.union_inter_cancel_left]
    have hsum2 : ∑ k ∈ s₁ ∪ s₂, (if k ∈ s₂ then c₂ k else 0) * f k i x = v i x := by
      rw [hv_eq i x]
      have : ∀ k ∈ s₁ ∪ s₂, (if k ∈ s₂ then c₂ k else 0) * f k i x =
          if k ∈ s₂ then c₂ k * f k i x else 0 := fun k _ => by split_ifs <;> simp
      rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.union_inter_cancel_right]
    have hrew : ∀ k ∈ s₁ ∪ s₂, c k * f k i x =
        ((if k ∈ s₁ then c₁ k else 0) * f k i x + (if k ∈ s₂ then c₂ k else 0) * f k i x) / 2 := by
      intro k _; dsimp [c]; ring
    rw [Finset.sum_congr rfl hrew, ← Finset.sum_div, Finset.sum_add_distrib, hsum1, hsum2]

/-- Upward continuity (Choquet axiom C2) of `cap μ n` on arbitrary increasing sequences. -/
private lemma cap_iUnion_of_monotone {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {n : ℕ} (hn : 0 < n)
    (A : ℕ → Set (Fin n → X)) (hmono : Monotone A) :
    cap μ n (⋃ k, A k) = ⨆ k, cap μ n (A k) := by
  refine le_antisymm ?_ (iSup_le fun k => cap_mono μ (Set.subset_iUnion A k))
  let L_enn : ℝ≥0∞ := ⨆ k, cap μ n (A k)
  have hL_lt_top : L_enn < ⊤ :=
    lt_of_le_of_lt (iSup_le fun k => cap_le_measure_univ μ hn (A k)) (measure_lt_top μ Set.univ)
  let L : ℝ := L_enn.toReal
  have hL_nonneg : 0 ≤ L := ENNReal.toReal_nonneg
  have hL_eq : ENNReal.ofReal L = L_enn := ENNReal.ofReal_toReal hL_lt_top.ne
  have hex : ∀ k : ℕ, ∃ f : Fin n → X → ℝ,
      (∀ i, Measurable (f i)) ∧ (∀ i x, 0 ≤ f i x ∧ f i x ≤ 1) ∧
      (∀ z ∈ A k, 1 ≤ ∑ i, f i (z i)) ∧
      ∑ i, ∫ x, f i x ∂μ ≤ L + 1 / ((k : ℝ) + 1) := by
    intro k
    have hle : cap μ n (A k) ≤ ENNReal.ofReal L := by
      rw [hL_eq]; exact le_iSup (fun k => cap μ n (A k)) k
    exact exists_bounded_real_witness μ hL_nonneg hle (by positivity)
  choose f hf_meas hf_bnd hf_cov hf_int using hex
  -- Properties inherited by tail convex combinations
  have hconv_props : ∀ m w, IsTailConv f m w →
      (∀ i, Measurable (w i)) ∧ (∀ i x, 0 ≤ w i x ∧ w i x ≤ 1) ∧
      (∀ z ∈ A m, 1 ≤ ∑ i, w i (z i)) ∧
      ∑ i, ∫ x, w i x ∂μ ≤ L + 1 / ((m : ℝ) + 1) := by
    intro m w ⟨s, c, hs, hc0, hc1, hweq⟩
    have hw_meas : ∀ i, Measurable (w i) := by
      intro i
      have : w i = fun x => ∑ k ∈ s, c k * f k i x := funext (hweq i)
      rw [this]
      exact Finset.measurable_sum s fun k _ => measurable_const.mul (hf_meas k i)
    have hw_bnd : ∀ i x, 0 ≤ w i x ∧ w i x ≤ 1 := by
      intro i x
      rw [hweq i x]
      refine ⟨Finset.sum_nonneg fun k hk => mul_nonneg (hc0 k hk) (hf_bnd k i x).1, ?_⟩
      calc ∑ k ∈ s, c k * f k i x
        _ ≤ ∑ k ∈ s, c k * 1 := Finset.sum_le_sum fun k hk =>
            mul_le_mul_of_nonneg_left (hf_bnd k i x).2 (hc0 k hk)
        _ = 1 := by simp [hc1]
    have hw_cov : ∀ z ∈ A m, 1 ≤ ∑ i, w i (z i) := by
      intro z hz
      simp_rw [hweq]
      rw [Finset.sum_comm]
      calc (1 : ℝ) = ∑ k ∈ s, c k * 1 := by simp [hc1]
        _ ≤ ∑ k ∈ s, ∑ i, c k * f k i (z i) := by
            refine Finset.sum_le_sum fun k hk => ?_
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left (hf_cov k z (hmono (hs k hk) hz)) (hc0 k hk)
    have hw_int : ∑ i, ∫ x, w i x ∂μ ≤ L + 1 / ((m : ℝ) + 1) := by
      have hf_intble : ∀ k i, Integrable (f k i) μ := fun k i =>
        Integrable.of_bound (hf_meas k i).aestronglyMeasurable 1 (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hf_bnd k i x).1]; exact (hf_bnd k i x).2)
      have hstep : ∀ i, ∫ x, w i x ∂μ = ∑ k ∈ s, c k * ∫ x, f k i x ∂μ := by
        intro i
        have : w i = fun x => ∑ k ∈ s, c k * f k i x := funext (hweq i)
        rw [this, integral_finsetSum s (fun k _ => (hf_intble k i).const_mul (c k))]
        refine Finset.sum_congr rfl fun k _ => integral_const_mul (c k) (f k i)
      simp_rw [hstep]
      rw [Finset.sum_comm]
      calc ∑ k ∈ s, ∑ i, c k * ∫ x, f k i x ∂μ
        _ = ∑ k ∈ s, c k * ∑ i, ∫ x, f k i x ∂μ := by
            refine Finset.sum_congr rfl fun k _ => (Finset.mul_sum ..).symm
        _ ≤ ∑ k ∈ s, c k * (L + 1 / ((m : ℝ) + 1)) := by
            refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left ?_ (hc0 k hk)
            refine (hf_int k).trans ?_
            gcongr
            exact_mod_cast hs k hk
        _ = L + 1 / ((m : ℝ) + 1) := by rw [← Finset.sum_mul, hc1, one_mul]
    exact ⟨hw_meas, hw_bnd, hw_cov, hw_int⟩
  -- Quadratic L² energy functional Q
  let Q : (Fin n → X → ℝ) → ℝ := fun w => ∑ i, ∫ x, (w i x) ^ 2 ∂μ
  have hQ_nonneg : ∀ w, 0 ≤ Q w := fun w =>
    Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hQ_para : ∀ u v : Fin n → X → ℝ,
      (∀ i, Measurable (u i)) → (∀ i x, 0 ≤ u i x ∧ u i x ≤ 1) →
      (∀ i, Measurable (v i)) → (∀ i x, 0 ≤ v i x ∧ v i x ≤ 1) →
      Q (fun i x => (u i x + v i x) / 2) + (1 / 4) * Q (fun i x => u i x - v i x) =
        (1 / 2) * Q u + (1 / 2) * Q v := by
    intro u v hu_m hu_b hv_m hv_b
    have hint_sq : ∀ (h : X → ℝ), Measurable h → (∀ x, |h x| ≤ 2) → Integrable (fun x => (h x) ^ 2) μ := by
      intro h hm hb
      refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable 4 (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (h x), hb x, sq_abs (h x)]
    have hu_sq : ∀ i, Integrable (fun x => (u i x) ^ 2) μ := fun i =>
      hint_sq (u i) (hu_m i) fun x => by
        rw [abs_of_nonneg (hu_b i x).1]; linarith [(hu_b i x).2]
    have hv_sq : ∀ i, Integrable (fun x => (v i x) ^ 2) μ := fun i =>
      hint_sq (v i) (hv_m i) fun x => by
        rw [abs_of_nonneg (hv_b i x).1]; linarith [(hv_b i x).2]
    have hmid_sq : ∀ i, Integrable (fun x => ((u i x + v i x) / 2) ^ 2) μ := fun i =>
      hint_sq (fun x => (u i x + v i x) / 2) (((hu_m i).add (hv_m i)).div_const 2) fun x => by
        rw [abs_of_nonneg (by linarith [(hu_b i x).1, (hv_b i x).1])]
        linarith [(hu_b i x).2, (hv_b i x).2]
    have hdiff_sq : ∀ i, Integrable (fun x => (u i x - v i x) ^ 2) μ := fun i =>
      hint_sq (fun x => u i x - v i x) ((hu_m i).sub (hv_m i)) fun x => by
        rw [abs_le]
        constructor <;> linarith [(hu_b i x).1, (hu_b i x).2, (hv_b i x).1, (hv_b i x).2]
    simp only [Q, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hmid_sq i) ((hdiff_sq i).const_mul _),
      ← integral_add ((hu_sq i).const_mul _) ((hv_sq i).const_mul _)]
    congr 1; ext x; ring
  -- Infimal energy d m of tail m
  let S : ℕ → Set ℝ := fun m => { r | ∃ w, IsTailConv f m w ∧ Q w = r }
  have hS_ne : ∀ m, (S m).Nonempty := fun m => ⟨Q (f m), f m, isTailConv_self f m, rfl⟩
  have hS_bdd : ∀ m, BddBelow (S m) := fun m => ⟨0, by rintro _ ⟨w, _, rfl⟩; exact hQ_nonneg w⟩
  let d : ℕ → ℝ := fun m => sInf (S m)
  have hd_mono : Monotone d := by
    intro m m' hmm'
    apply csInf_le_csInf (hS_bdd m) (hS_ne m')
    rintro r ⟨w, hw, rfl⟩
    exact ⟨w, isTailConv_mono hmm' hw, rfl⟩
  have hd_bdd : BddAbove (Set.range d) := by
    refine ⟨(n : ℝ) * (μ Set.univ).toReal, ?_⟩
    rintro _ ⟨m, rfl⟩
    refine le_trans (csInf_le (hS_bdd m) ⟨f m, isTailConv_self f m, rfl⟩) ?_
    calc Q (f m)
      _ ≤ ∑ _i : Fin n, ∫ _x, (1 : ℝ) ∂μ := by
          refine Finset.sum_le_sum fun i _ => integral_mono ?_ (integrable_const 1) fun x => ?_
          · refine Integrable.of_bound ((hf_meas m i).pow_const 2).aestronglyMeasurable 1
              (Eventually.of_forall fun x => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [(hf_bnd m i x).1, (hf_bnd m i x).2]
          · nlinarith [(hf_bnd m i x).1, (hf_bnd m i x).2]
      _ = (n : ℝ) * (μ Set.univ).toReal := by simp [Measure.real]
  -- Pick almost-minimizers w m ∈ S m
  have hw_ex : ∀ m, ∃ w, IsTailConv f m w ∧ Q w < d m + (1 / 2 : ℝ) ^ m := by
    intro m
    have hlt : d m < d m + (1 / 2 : ℝ) ^ m := lt_add_of_pos_right _ (by positivity)
    rcases (csInf_lt_iff (hS_bdd m) (hS_ne m)).mp hlt with ⟨r, ⟨w, hw, rfl⟩, hr⟩
    exact ⟨w, hw, hr⟩
  choose w hw_conv hw_Q using hw_ex
  -- Cauchy estimate for Q (w m - w m')
  have hQ_diff : ∀ m m', m ≤ m' →
      Q (fun i x => w m i x - w m' i x) ≤
        2 * (d m' - d m) + 2 * (1 / 2 : ℝ) ^ m + 2 * (1 / 2 : ℝ) ^ m' := by
    intro m m' hmm'
    have hw_m' : IsTailConv f m (w m') := isTailConv_mono hmm' (hw_conv m')
    have hmid_conv : IsTailConv f m (fun i x => (w m i x + w m' i x) / 2) :=
      isTailConv_midpoint (hw_conv m) hw_m'
    have hdm_le : d m ≤ Q (fun i x => (w m i x + w m' i x) / 2) :=
      csInf_le (hS_bdd m) ⟨_, hmid_conv, rfl⟩
    have hpm := hconv_props m (w m) (hw_conv m)
    have hpm' := hconv_props m' (w m') (hw_conv m')
    have hpara := hQ_para (w m) (w m') hpm.1 hpm.2.1 hpm'.1 hpm'.2.1
    have h1 := hw_Q m
    have h2 := hw_Q m'
    linarith
  -- Since d converges, for every j there is N j so Q (w m - w m') ≤ (1/4)^j for m, m' ≥ N j
  have hd_tendsto : Tendsto d atTop (𝓝 (⨆ m, d m)) := tendsto_atTop_ciSup hd_mono hd_bdd
  have hN_ex : ∀ j : ℕ, ∃ N : ℕ, ∀ m m', N ≤ m → m ≤ m' →
      Q (fun i x => w m i x - w m' i x) ≤ (1 / 4 : ℝ) ^ j := by
    intro j
    have hε : 0 < (1 / 4 : ℝ) ^ j / 6 := by positivity
    have h1 : ∀ᶠ m in atTop, (⨆ k, d k) - d m < (1 / 4 : ℝ) ^ j / 6 := by
      have hMetric := (Metric.tendsto_atTop.mp hd_tendsto) ((1 / 4 : ℝ) ^ j / 6) hε
      rcases hMetric with ⟨N₁, hN₁⟩
      exact eventually_atTop.mpr ⟨N₁, fun m hm => by
        have := hN₁ m hm
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (le_ciSup hd_bdd m)), neg_sub] at this
        exact this⟩
    have h2 : ∀ᶠ m in atTop, (1 / 2 : ℝ) ^ m < (1 / 4 : ℝ) ^ j / 6 := by
      have ht : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      exact ht.eventually (gt_mem_nhds hε)
    rcases (eventually_atTop.mp (h1.and h2)) with ⟨N, hN⟩
    refine ⟨N, fun m m' hNm hmm' => ?_⟩
    have ⟨hdm, hpowm⟩ := hN m hNm
    have ⟨_, hpowm'⟩ := hN m' (hNm.trans hmm')
    have hdm'_le : d m' ≤ ⨆ k, d k := le_ciSup hd_bdd m'
    have hdiff := hQ_diff m m' hmm'
    linarith
  choose N hN using hN_ex
  -- Build strictly increasing subsequence idx with idx j ≥ N j and idx j ≥ j
  let idx : ℕ → ℕ := Nat.rec (N 0) (fun j prev => max (prev + 1) (N (j + 1)))
  have hidx_ge_N : ∀ j, N j ≤ idx j := by
    intro j; cases j with
    | zero => exact le_rfl
    | succ j => exact le_max_right _ _
  have hidx_step : ∀ j, idx j < idx (j + 1) := fun j =>
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hidx_ge : ∀ j, j ≤ idx j := by
    intro j; induction j with
    | zero => exact Nat.zero_le _
    | succ j ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hidx_step j))
  have hQ_step : ∀ j, Q (fun i x => w (idx j) i x - w (idx (j + 1)) i x) ≤ (1 / 4 : ℝ) ^ j :=
    fun j => hN j (idx j) (idx (j + 1)) (hidx_ge_N j) (hidx_step j).le
  -- Summability of L¹ step differences → a.e. absolute convergence
  let stepDiff : ℕ → Fin n → X → ℝ := fun j i x => |w (idx (j + 1)) i x - w (idx j) i x|
  have hstep_meas : ∀ j i, Measurable (stepDiff j i) := fun j i =>
    ((hconv_props _ _ (hw_conv (idx (j + 1)))).1 i).sub
      ((hconv_props _ _ (hw_conv (idx j))).1 i) |>.abs
  have hstep_int_le : ∀ j i, ∫⁻ x, ENNReal.ofReal (stepDiff j i x) ∂μ ≤
      ENNReal.ofReal ((1 + (μ Set.univ).toReal) * (1 / 2 : ℝ) ^ j) := by
    intro j i
    have hdiff_meas : Measurable (fun x => w (idx j) i x - w (idx (j + 1)) i x) :=
      ((hconv_props _ _ (hw_conv (idx j))).1 i).sub
        ((hconv_props _ _ (hw_conv (idx (j + 1)))).1 i)
    have hdiff_bnd : ∀ x, |w (idx j) i x - w (idx (j + 1)) i x| ≤ 1 := by
      intro x
      have hb1 := (hconv_props _ _ (hw_conv (idx j))).2.1 i x
      have hb2 := (hconv_props _ _ (hw_conv (idx (j + 1)))).2.1 i x
      rw [abs_le]; constructor <;> linarith
    have hint_step : Integrable (stepDiff j i) μ :=
      Integrable.of_bound (hstep_meas j i).aestronglyMeasurable 1 (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_abs, abs_sub_comm]; exact hdiff_bnd x)
    have hint_sq : Integrable (fun x => (w (idx j) i x - w (idx (j + 1)) i x) ^ 2) μ :=
      Integrable.of_bound (hdiff_meas.pow_const 2).aestronglyMeasurable 1 (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [abs_nonneg (w (idx j) i x - w (idx (j + 1)) i x), hdiff_bnd x,
          sq_abs (w (idx j) i x - w (idx (j + 1)) i x)])
    rw [← ofReal_integral_eq_lintegral_ofReal hint_step (Eventually.of_forall fun x => abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    have hpt : ∀ x, stepDiff j i x ≤
        (2 : ℝ) ^ j * (w (idx j) i x - w (idx (j + 1)) i x) ^ 2 + (1 / 2 : ℝ) ^ j := by
      intro x
      dsimp [stepDiff]
      rw [abs_sub_comm]
      set u := w (idx j) i x - w (idx (j + 1)) i x
      have hpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hmul : (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
      have hsq : 0 ≤ ((2 : ℝ) ^ j * |u| - 1) ^ 2 := sq_nonneg _
      have h1 : 2 * (2 : ℝ) ^ j * |u| ≤ ((2 : ℝ) ^ j) ^ 2 * u ^ 2 + 1 := by
        nlinarith [sq_abs u]
      have h2 : (2 : ℝ) ^ j * |u| ≤ (2 : ℝ) ^ j * ((2 : ℝ) ^ j * u ^ 2 + (1 / 2 : ℝ) ^ j) := by
        have : (2 : ℝ) ^ j * ((2 : ℝ) ^ j * u ^ 2 + (1 / 2 : ℝ) ^ j) =
            ((2 : ℝ) ^ j) ^ 2 * u ^ 2 + 1 := by
          calc (2 : ℝ) ^ j * ((2 : ℝ) ^ j * u ^ 2 + (1 / 2 : ℝ) ^ j)
            _ = ((2 : ℝ) ^ j) ^ 2 * u ^ 2 + (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j := by ring
            _ = ((2 : ℝ) ^ j) ^ 2 * u ^ 2 + 1 := by rw [hmul]
        rw [this]
        nlinarith [abs_nonneg u]
      exact le_of_mul_le_mul_left h2 hpos
    calc ∫ x, stepDiff j i x ∂μ
      _ ≤ ∫ x, ((2 : ℝ) ^ j * (w (idx j) i x - w (idx (j + 1)) i x) ^ 2 + (1 / 2 : ℝ) ^ j) ∂μ :=
          integral_mono hint_step ((hint_sq.const_mul _).add (integrable_const _)) hpt
      _ = (2 : ℝ) ^ j * (∫ x, (w (idx j) i x - w (idx (j + 1)) i x) ^ 2 ∂μ) +
            (1 / 2 : ℝ) ^ j * (μ Set.univ).toReal := by
          rw [integral_add (hint_sq.const_mul _) (integrable_const _), integral_const_mul]
          simp [Measure.real, mul_comm]
      _ ≤ (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j + (1 / 2 : ℝ) ^ j * (μ Set.univ).toReal := by
          gcongr
          calc ∫ x, (w (idx j) i x - w (idx (j + 1)) i x) ^ 2 ∂μ
            _ ≤ Q (fun i' x => w (idx j) i' x - w (idx (j + 1)) i' x) :=
                Finset.single_le_sum
                  (f := fun i' => ∫ x, (w (idx j) i' x - w (idx (j + 1)) i' x) ^ 2 ∂μ)
                  (fun i' _ => integral_nonneg fun _ => sq_nonneg _)
                  (Finset.mem_univ i)
            _ ≤ (1 / 4 : ℝ) ^ j := hQ_step j
      _ = (1 + (μ Set.univ).toReal) * (1 / 2 : ℝ) ^ j := by
          have : (2 : ℝ) ^ j * (1 / 4 : ℝ) ^ j = (1 / 2 : ℝ) ^ j := by
            rw [← mul_pow]; norm_num
          rw [this]; ring
  let bad : Fin n → Set X := fun i =>
    { x | ∑' j, ENNReal.ofReal (stepDiff j i x) = ⊤ }
  have hbad_meas : ∀ i, MeasurableSet (bad i) := fun i =>
    (Measurable.tsum fun j => (hstep_meas j i).ennreal_ofReal) (measurableSet_singleton ⊤)
  have hbad_zero : ∀ i, μ (bad i) = 0 := by
    intro i
    have hlt_top : ∫⁻ x, (∑' j, ENNReal.ofReal (stepDiff j i x)) ∂μ < ⊤ := by
      rw [lintegral_tsum fun j => (hstep_meas j i).ennreal_ofReal.aemeasurable]
      calc ∑' j, ∫⁻ x, ENNReal.ofReal (stepDiff j i x) ∂μ
        _ ≤ ∑' j, ENNReal.ofReal ((1 + (μ Set.univ).toReal) * (1 / 2 : ℝ) ^ j) :=
            ENNReal.tsum_le_tsum fun j => hstep_int_le j i
        _ = ∑' j, ENNReal.ofReal (1 + (μ Set.univ).toReal) * ((2 : ℝ≥0∞)⁻¹ ^ j) := by
            congr 1; ext j
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
            congr 2
            rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
            norm_num
        _ = ENNReal.ofReal (1 + (μ Set.univ).toReal) * ∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ j :=
            ENNReal.tsum_mul_left
        _ = ENNReal.ofReal (1 + (μ Set.univ).toReal) * (1 - (2 : ℝ≥0∞)⁻¹)⁻¹ := by
            rw [ENNReal.tsum_geometric]
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
            rw [ENNReal.inv_lt_top]
            exact tsub_pos_iff_lt.mpr (by rw [ENNReal.inv_lt_one]; norm_num))
    have hae := ae_lt_top (Measurable.tsum fun j => (hstep_meas j i).ennreal_ofReal) hlt_top.ne
    rw [ae_iff] at hae
    convert hae using 2
    ext x; simp [bad]
  -- Pointwise convergence outside `bad i`
  have hconv_ae : ∀ i x, x ∉ bad i →
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ Tendsto (fun j => w (idx j) i x) atTop (𝓝 r) := by
    intro i x hx
    have hne : (∑' j, ENNReal.ofReal (stepDiff j i x)) ≠ ⊤ := hx
    have hsum : Summable (fun j => dist (w (idx j) i x) (w (idx (j + 1)) i x)) := by
      let u : ℕ → ℝ≥0 := fun j => ⟨stepDiff j i x, abs_nonneg _⟩
      have hu : Summable u := ENNReal.tsum_coe_ne_top_iff_summable.mp (by
        convert hne using 1
        congr 1; ext j
        exact (ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)).symm)
      have hsumm : Summable (fun j => stepDiff j i x) := NNReal.summable_coe.mpr hu
      refine hsumm.congr fun j => ?_
      dsimp [stepDiff]
      rw [Real.dist_eq, abs_sub_comm]
    rcases cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum) with ⟨r, hr⟩
    refine ⟨r, ?_, ?_, hr⟩
    · exact ge_of_tendsto' hr fun j => (hconv_props _ _ (hw_conv (idx j))).2.1 i x |>.1
    · exact le_of_tendsto' hr fun j => (hconv_props _ _ (hw_conv (idx j))).2.1 i x |>.2
  -- Define limit functions g : Fin n → X → ℝ≥0∞
  let g : Fin n → X → ℝ≥0∞ := fun i x =>
    if x ∈ bad i then 1 else liminf (fun j => ENNReal.ofReal (w (idx j) i x)) atTop
  have hg_meas : ∀ i, Measurable (g i) := fun i =>
    Measurable.ite (hbad_meas i) measurable_const
      (Measurable.liminf fun j => ((hconv_props _ _ (hw_conv (idx j))).1 i).ennreal_ofReal)
  have hg_val : ∀ i x, x ∉ bad i → ∀ r, Tendsto (fun j => w (idx j) i x) atTop (𝓝 r) →
      g i x = ENNReal.ofReal r := by
    intro i x hx r hr
    simp only [g, if_neg hx]
    exact (ENNReal.continuous_ofReal.tendsto r |>.comp hr).liminf_eq
  -- Covering condition on ⋃ k, A k
  have hg_cov : ∀ z ∈ ⋃ k, A k, 1 ≤ ∑ i, g i (z i) := by
    intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨k₀, hk₀⟩
    by_cases hbad : ∃ i, z i ∈ bad i
    · rcases hbad with ⟨i, hi⟩
      calc (1 : ℝ≥0∞) = g i (z i) := by simp [g, hi]
        _ ≤ ∑ j, g j (z j) :=
            Finset.single_le_sum (f := fun j => g j (z j)) (fun _ _ => bot_le) (Finset.mem_univ i)
    · push Not at hbad
      have hconv_z : ∀ i, ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧
          Tendsto (fun j => w (idx j) i (z i)) atTop (𝓝 r) := fun i => hconv_ae i (z i) (hbad i)
      choose r hr0 _ hr_tend using hconv_z
      have hsum_tend : Tendsto (fun j => ∑ i, w (idx j) i (z i)) atTop (𝓝 (∑ i, r i)) :=
        tendsto_finsetSum _ fun i _ => hr_tend i
      have hsum_ge : 1 ≤ ∑ i, r i := by
        refine ge_of_tendsto hsum_tend ?_
        filter_upwards [eventually_ge_atTop k₀] with j hj
        have hzk : z ∈ A (idx j) := hmono (hj.trans (hidx_ge j)) hk₀
        exact (hconv_props _ _ (hw_conv (idx j))).2.2.1 z hzk
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal (∑ i, r i) := ENNReal.ofReal_le_ofReal hsum_ge
        _ = ∑ i, ENNReal.ofReal (r i) := ENNReal.ofReal_sum_of_nonneg fun i _ => hr0 i
        _ = ∑ i, g i (z i) := Finset.sum_congr rfl fun i _ => (hg_val i (z i) (hbad i) (r i) (hr_tend i)).symm
  -- Integral bound via Dominated Convergence
  have hg_int : ∑ i, ∫⁻ x, g i x ∂μ ≤ L_enn := by
    let gr : Fin n → X → ℝ := fun i x => (g i x).toReal
    have hgr_le1 : ∀ i x, 0 ≤ gr i x ∧ gr i x ≤ 1 := by
      intro i x
      refine ⟨ENNReal.toReal_nonneg, ?_⟩
      by_cases hx : x ∈ bad i
      · simp [gr, g, hx]
      · rcases hconv_ae i x hx with ⟨r, hr0, hr1, hr⟩
        dsimp only [gr]
        rw [hg_val i x hx r hr, ENNReal.toReal_ofReal hr0]
        exact hr1
    have hgr_eq_g : ∀ i x, ENNReal.ofReal (gr i x) = g i x := by
      intro i x
      by_cases hx : x ∈ bad i
      · simp [gr, g, hx]
      · rcases hconv_ae i x hx with ⟨r, hr0, _, hr⟩
        dsimp only [gr]
        rw [hg_val i x hx r hr, ENNReal.toReal_ofReal hr0]
    have hint_tend : ∀ i, Tendsto (fun j => ∫ x, w (idx j) i x ∂μ) atTop (𝓝 (∫ x, gr i x ∂μ)) := by
      intro i
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun j => ((hconv_props _ _ (hw_conv (idx j))).1 i).aestronglyMeasurable)
        (integrable_const 1)
        (fun j => Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg ((hconv_props _ _ (hw_conv (idx j))).2.1 i x).1]
          exact ((hconv_props _ _ (hw_conv (idx j))).2.1 i x).2)
        ?_
      have hae : ∀ᵐ x ∂μ, x ∉ bad i := by
        rw [ae_iff]; simpa using hbad_zero i
      filter_upwards [hae] with x hx
      rcases hconv_ae i x hx with ⟨r, hr0, _, hr⟩
      have hgr_r : gr i x = r := by
        dsimp only [gr]
        rw [hg_val i x hx r hr, ENNReal.toReal_ofReal hr0]
      rwa [hgr_r]
    have hsum_tend : Tendsto (fun j => ∑ i, ∫ x, w (idx j) i x ∂μ) atTop
        (𝓝 (∑ i, ∫ x, gr i x ∂μ)) := tendsto_finsetSum _ fun i _ => hint_tend i
    have hupper_tend : Tendsto (fun j : ℕ => L + 1 / ((Nat.cast (idx j) : ℝ) + 1)) atTop (𝓝 L) := by
      have h0 : Tendsto (fun j : ℕ => 1 / ((Nat.cast (idx j) : ℝ) + 1)) atTop (𝓝 0) := by
        have hinf : Tendsto (fun j : ℕ => (Nat.cast (idx j) : ℝ) + 1) atTop atTop := by
          refine tendsto_atTop_mono (f := fun j : ℕ => (j : ℝ) + 1) (fun j => ?_)
            (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
          have : (j : ℝ) ≤ (Nat.cast (idx j) : ℝ) := Nat.cast_le.mpr (hidx_ge j)
          linarith
        exact tendsto_const_nhds.div_atTop hinf
      simpa using tendsto_const_nhds.add h0
    have hsum_le_L : ∑ i, ∫ x, gr i x ∂μ ≤ L :=
      le_of_tendsto_of_tendsto hsum_tend hupper_tend
        (Eventually.of_forall fun j => (hconv_props _ _ (hw_conv (idx j))).2.2.2)
    calc ∑ i, ∫⁻ x, g i x ∂μ
      _ = ∑ i, ∫⁻ x, ENNReal.ofReal (gr i x) ∂μ := by
          refine Finset.sum_congr rfl fun i _ => lintegral_congr fun x => (hgr_eq_g i x).symm
      _ = ∑ i, ENNReal.ofReal (∫ x, gr i x ∂μ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hint : Integrable (gr i) μ :=
            Integrable.of_bound ((hg_meas i).ennreal_toReal.aestronglyMeasurable) 1
              (Eventually.of_forall fun x => by
                rw [Real.norm_eq_abs, abs_of_nonneg (hgr_le1 i x).1]; exact (hgr_le1 i x).2)
          exact (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun x => (hgr_le1 i x).1)).symm
      _ = ENNReal.ofReal (∑ i, ∫ x, gr i x ∂μ) :=
          (ENNReal.ofReal_sum_of_nonneg fun i _ => integral_nonneg fun x => (hgr_le1 i x).1).symm
      _ ≤ ENNReal.ofReal L := ENNReal.ofReal_le_ofReal hsum_le_L
      _ = L_enn := hL_eq
  exact (cap_le_of_witness μ g hg_meas hg_cov).trans hg_int

/-- Approximating the indicator of a closed set in a metric space from above by continuous `[0, 1]` functions. -/
private lemma exists_approx_closed {Y : Type*} [PseudoMetricSpace Y]
    {F : Set Y} (hF : IsClosed F) (hFne : F.Nonempty) :
    ∃ g : ℕ → C(Y, ℝ),
      (∀ m y, 0 ≤ g m y ∧ g m y ≤ 1) ∧
      (∀ m, ∀ y ∈ F, g m y = 1) ∧
      (∀ y, Tendsto (fun m => g m y) atTop (𝓝 (F.indicator (fun _ => (1 : ℝ)) y))) := by
  let g : ℕ → C(Y, ℝ) := fun m =>
    ⟨fun y => max 0 (1 - ((m : ℝ) + 1) * Metric.infDist y F),
      continuous_const.max (continuous_const.sub (continuous_const.mul (Metric.continuous_infDist_pt F)))⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · intro m y
    refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
    have : 0 ≤ ((m : ℝ) + 1) * Metric.infDist y F := mul_nonneg (by positivity) Metric.infDist_nonneg
    linarith
  · intro m y hy
    simp [g, Metric.infDist_zero_of_mem hy]
  · intro y
    by_cases hy : y ∈ F
    · simp only [Set.indicator_of_mem hy, g, ContinuousMap.coe_mk, Metric.infDist_zero_of_mem hy,
        mul_zero, sub_zero, max_eq_right zero_le_one]
      exact tendsto_const_nhds
    · simp only [Set.indicator_of_notMem hy]
      have hdpos : 0 < Metric.infDist y F := by
        rcases eq_or_lt_of_le (Metric.infDist_nonneg (x := y) (s := F)) with hd0 | hdpos
        · exfalso
          exact hy ((hF.mem_iff_infDist_zero hFne).mpr hd0.symm)
        · exact hdpos
      obtain ⟨M, hM⟩ := exists_nat_gt (1 / Metric.infDist y F)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop M] with m hm
      have h1 : 1 ≤ ((m : ℝ) + 1) * Metric.infDist y F := by
        have hm' : (M : ℝ) ≤ m := Nat.cast_le.mpr hm
        have hlt : 1 / Metric.infDist y F < (m : ℝ) + 1 := by linarith
        have := (div_lt_iff₀ hdpos).mp hlt
        linarith
      simp only [g, ContinuousMap.coe_mk]
      exact (max_eq_left (by linarith)).symm

/-- On a compact Polish space, if `∫ f dν ≤ ∫ f dμ` for all nonnegative continuous `f`, then `ν ≤ μ`. -/
private lemma measure_le_of_forall_continuous_integral_le
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (ν μ : Measure X) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (h : ∀ f : C(X, ℝ), (∀ x, 0 ≤ f x) → ∫ x, f x ∂ν ≤ ∫ x, f x ∂μ) :
    ν ≤ μ := by
  let _ : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  have hclosed : ∀ F : Set X, IsClosed F → ν F ≤ μ F := by
    intro F hF
    rcases F.eq_empty_or_nonempty with rfl | hFne
    · simp
    · obtain ⟨g, hg_bnd, _, hg_tend⟩ := exists_approx_closed hF hFne
      have ht_ν : Tendsto (fun m => ∫ x, g m x ∂ν) atTop
          (𝓝 (∫ x, F.indicator (fun _ => (1 : ℝ)) x ∂ν)) :=
        tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
          (fun m => (g m).continuous.aestronglyMeasurable) (integrable_const 1)
          (fun m => Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hg_bnd m x).1]; exact (hg_bnd m x).2)
          (Eventually.of_forall hg_tend)
      have ht_μ : Tendsto (fun m => ∫ x, g m x ∂μ) atTop
          (𝓝 (∫ x, F.indicator (fun _ => (1 : ℝ)) x ∂μ)) :=
        tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
          (fun m => (g m).continuous.aestronglyMeasurable) (integrable_const 1)
          (fun m => Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs, abs_of_nonneg (hg_bnd m x).1]; exact (hg_bnd m x).2)
          (Eventually.of_forall hg_tend)
      have hle_real : ∫ x, F.indicator (fun _ => (1 : ℝ)) x ∂ν ≤
          ∫ x, F.indicator (fun _ => (1 : ℝ)) x ∂μ :=
        le_of_tendsto_of_tendsto ht_ν ht_μ
          (Eventually.of_forall fun m => h (g m) fun x => (hg_bnd m x).1)
      rw [integral_indicator_const _ hF.measurableSet, integral_indicator_const _ hF.measurableSet] at hle_real
      simp only [smul_eq_mul, mul_one, Measure.real] at hle_real
      exact (ENNReal.toReal_le_toReal (measure_ne_top ν F) (measure_ne_top μ F)).mp hle_real
  rw [Measure.le_iff]
  intro A hA
  have hreg := MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite ν
  rw [hreg.measure_eq_iSup hA]
  refine iSup₂_le fun K hK => iSup_le fun ⟨_, hKcl⟩ => ?_
  exact (hclosed K hKcl).trans (measure_mono hK)

/-- The real vector space of bounded functions `α → ℝ`. -/
private def BoundedFun (α : Type*) : Submodule ℝ (α → ℝ) where
  carrier := { g | ∃ C : ℝ, ∀ x, |g x| ≤ C }
  add_mem' := by
    rintro g₁ g₂ ⟨C₁, h₁⟩ ⟨C₂, h₂⟩
    exact ⟨C₁ + C₂, fun x => (abs_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))⟩
  zero_mem' := ⟨0, fun _ => by simp⟩
  smul_mem' := by
    rintro c g ⟨C, h⟩
    exact ⟨|c| * C, fun x => by
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (h x) (abs_nonneg c)⟩

/-- Compact Duality (Piece A): On a compact Polish space `X` with finite Borel measure `μ` and
`n ≥ 1`, for every closed (= compact) set `K ⊆ Xⁿ`, there is a measure `γ` on `Xⁿ` with marginals
`≤ μ` such that `cap μ n K ≤ γ K`. -/
private lemma compact_duality {X : Type*} [TopologicalSpace X] [PolishSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 0 < n) (K : Set (Fin n → X)) (hK : IsClosed K) :
    ∃ γ : Measure (Fin n → X),
      (∀ i, γ.map (fun z : Fin n → X => z i) ≤ μ) ∧ cap μ n K ≤ γ K := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · refine ⟨0, fun i => by simp [Measure.zero_le], by simp [cap_empty]⟩
  let E := Fin n → X
  -- Sublinear functional p on BoundedFun E defined via nonnegative continuous marginals
  let S_p : BoundedFun E → Set ℝ := fun g =>
    { r : ℝ | ∃ f : Fin n → C(X, ℝ), (∀ i x, 0 ≤ f i x) ∧
      (∀ z : E, g.1 z ≤ ∑ i, f i (z i)) ∧ r = ∑ i, ∫ x, f i x ∂μ }
  let i₀ : Fin n := ⟨0, hn⟩
  have hS_ne : ∀ g : BoundedFun E, (S_p g).Nonempty := by
    intro ⟨g, C, hC⟩
    let M : ℝ := max C 0
    let f : Fin n → C(X, ℝ) := fun i => if i = i₀ then ContinuousMap.const X M else 0
    refine ⟨∑ i, ∫ x, f i x ∂μ, f, ?_, ?_, rfl⟩
    · intro i x
      dsimp [f]; split_ifs
      · exact le_max_right C 0
      · exact le_rfl
    · intro z
      have hsum : ∑ i : Fin n, f i (z i) = M := by
        rw [Finset.sum_eq_single i₀]
        · simp [f]
        · intro i _ hi; simp [f, hi]
        · intro h; exact (h (Finset.mem_univ i₀)).elim
      rw [hsum]
      exact (le_abs_self (g z)).trans ((hC z).trans (le_max_left C 0))
  have hS_bdd : ∀ g : BoundedFun E, BddBelow (S_p g) := by
    intro g
    refine ⟨0, ?_⟩
    rintro _ ⟨f, hf0, _, rfl⟩
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => hf0 i x
  let p : BoundedFun E → ℝ := fun g => sInf (S_p g)
  have hp_nonneg : ∀ g, 0 ≤ p g := fun g => le_csInf (hS_ne g) fun _ ⟨f, hf0, _, hr⟩ =>
    hr ▸ Finset.sum_nonneg fun i _ => integral_nonneg fun x => hf0 i x
  have hp_le : ∀ g (f : Fin n → C(X, ℝ)), (∀ i x, 0 ≤ f i x) →
      (∀ z : E, g.1 z ≤ ∑ i, f i (z i)) → p g ≤ ∑ i, ∫ x, f i x ∂μ :=
    fun g f hf0 hdom => csInf_le (hS_bdd g) ⟨f, hf0, hdom, rfl⟩
  have hp_hom_le : ∀ c : ℝ, 0 < c → ∀ g : BoundedFun E, p (c • g) ≤ c * p g := by
    intro c hc g
    rw [← div_le_iff₀' hc]
    refine le_csInf (hS_ne g) ?_
    rintro _ ⟨f, hf0, hdom, rfl⟩
    rw [div_le_iff₀' hc]
    have hmul : c * ∑ i, ∫ x, f i x ∂μ = ∑ i, ∫ x, (c • f i) x ∂μ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simpa using (integral_const_mul c (f i)).symm
    rw [hmul]
    refine hp_le (c • g) (fun i => c • f i)
      (fun i x => mul_nonneg hc.le (hf0 i x))
      (fun z => ?_)
    have hsum : ∑ i, (c • f i) (z i) = c * ∑ i, f i (z i) := by
      rw [Finset.mul_sum]; rfl
    rw [hsum]
    exact mul_le_mul_of_nonneg_left (hdom z) hc.le
  have hp_hom : ∀ c : ℝ, 0 < c → ∀ g : BoundedFun E, p (c • g) = c * p g := by
    intro c hc g
    apply le_antisymm (hp_hom_le c hc g)
    have h1 := hp_hom_le c⁻¹ (inv_pos.mpr hc) (c • g)
    rw [inv_smul_smul₀ hc.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hc.le
    rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h2
  -- Indicator of K in BoundedFun E
  let v₀ : BoundedFun E :=
    ⟨K.indicator (fun _ => (1 : ℝ)), 1, fun z => by
      by_cases hz : z ∈ K <;> simp [hz]⟩
  rcases hKne with ⟨z₀, hz₀⟩
  have hv₀_z₀ : v₀.1 z₀ = 1 := by simp [v₀, hz₀]
  -- Linear functional on span ℝ {v₀} dominated by p
  let W : Submodule ℝ (BoundedFun E) := Submodule.span ℝ {v₀}
  let ψ : W →ₗ[ℝ] ℝ :=
    { toFun := fun u => u.1.1 z₀ * p v₀
      map_add' := fun u v => by simp [add_mul]
      map_smul' := fun c u => by simp [mul_assoc] }
  have hψ_le : ∀ u : W, ψ u ≤ p u.1 := by
    intro ⟨u, hu⟩
    rcases Submodule.mem_span_singleton.mp hu with ⟨t, rfl⟩
    have hval : ψ ⟨t • v₀, hu⟩ = t * p v₀ := by
      simp [ψ, hv₀_z₀]
    rw [hval]
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact (mul_nonpos_of_nonpos_of_nonneg ht.le (hp_nonneg v₀)).trans (hp_nonneg _)
    · simp [hp_nonneg]
    · rw [hp_hom t ht v₀]
  -- Apply Hahn-Banach
  obtain ⟨Λ_full, hΛ_ext, hΛ_le⟩ :=
    exists_extension_of_le_sublinear ⟨W, ψ⟩ p hp_hom
      (by
        intro g₁ g₂
        have : ∀ r₁ ∈ S_p g₁, ∀ r₂ ∈ S_p g₂, p (g₁ + g₂) ≤ r₁ + r₂ := by
          rintro _ ⟨f₁, hf₁0, hd₁, rfl⟩ _ ⟨f₂, hf₂0, hd₂, rfl⟩
          have hsum_int : ∑ i, ∫ x, (f₁ i + f₂ i) x ∂μ =
              (∑ i, ∫ x, f₁ i x ∂μ) + (∑ i, ∫ x, f₂ i x ∂μ) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun i _ =>
              integral_add
                ((f₁ i).continuous.integrable_of_hasCompactSupport
                  (HasCompactSupport.of_compactSpace _))
                ((f₂ i).continuous.integrable_of_hasCompactSupport
                  (HasCompactSupport.of_compactSpace _))
          rw [← hsum_int]
          refine hp_le (g₁ + g₂) (fun i => f₁ i + f₂ i)
            (fun i x => add_nonneg (hf₁0 i x) (hf₂0 i x))
            (fun z => ?_)
          have hadd : ∑ i, (f₁ i + f₂ i) (z i) = (∑ i, f₁ i (z i)) + ∑ i, f₂ i (z i) := by
            simp [Finset.sum_add_distrib]
          rw [hadd]
          exact add_le_add (hd₁ z) (hd₂ z)
        have h1 : ∀ r₁ ∈ S_p g₁, p (g₁ + g₂) - r₁ ≤ p g₂ := fun r₁ hr₁ =>
          le_csInf (hS_ne g₂) fun r₂ hr₂ => sub_le_iff_le_add'.mpr (this r₁ hr₁ r₂ hr₂)
        have h2 : p (g₁ + g₂) - p g₂ ≤ p g₁ :=
          le_csInf (hS_ne g₁) fun r₁ hr₁ => sub_le_comm.mp (h1 r₁ hr₁)
        linarith)
      hψ_le
  -- Positivity of Λ_full
  have hΛ_nonneg : ∀ g : BoundedFun E, (∀ z, 0 ≤ g.1 z) → 0 ≤ Λ_full g := by
    intro g hg
    have hp_neg : p (-g) ≤ 0 := by
      calc p (-g)
        _ ≤ ∑ i : Fin n, ∫ x, (0 : C(X, ℝ)) x ∂μ :=
            hp_le (-g) (fun _ => 0) (fun _ _ => le_rfl) (fun z => by
              simp; exact hg z)
        _ = 0 := by simp
    have : -Λ_full g ≤ 0 := by
      calc -Λ_full g = Λ_full (-g) := (map_neg Λ_full g).symm
        _ ≤ p (-g) := hΛ_le (-g)
        _ ≤ 0 := hp_neg
    linarith
  have hΛ_mono : ∀ g₁ g₂ : BoundedFun E, (∀ z, g₁.1 z ≤ g₂.1 z) → Λ_full g₁ ≤ Λ_full g₂ := by
    intro g₁ g₂ hle
    have h0 : 0 ≤ Λ_full (g₂ - g₁) := hΛ_nonneg (g₂ - g₁) fun z => sub_nonneg.mpr (hle z)
    rw [map_sub] at h0
    linarith
  -- Restrict Λ_full to C_c(E, ℝ) as a PositiveLinearMap
  let toB : C_c(E, ℝ) →ₗ[ℝ] BoundedFun E :=
    { toFun := fun g => ⟨g, ‖g.toBoundedContinuousFunction‖, fun z => by
        simpa [Real.norm_eq_abs] using g.toBoundedContinuousFunction.norm_coe_le_norm z⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Λ : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun g => Λ_full (toB g)
      map_add' := fun g₁ g₂ => by simp [map_add]
      map_smul' := fun c g => by simp [map_smul]
      monotone' := fun g₁ g₂ hle => hΛ_mono (toB g₁) (toB g₂) hle }
  let γ : Measure E := RealRMK.rieszMeasure Λ
  have : IsFiniteMeasure γ := inferInstance
  refine ⟨γ, ?_, ?_⟩
  · -- Marginals ≤ μ
    intro i
    have : IsFiniteMeasure (γ.map (fun z : E => z i)) := Measure.isFiniteMeasure_map γ _
    refine measure_le_of_forall_continuous_integral_le (γ.map (fun z : E => z i)) μ fun f hf0 => ?_
    let g : C_c(E, ℝ) :=
      ⟨⟨fun z => f (z i), f.continuous.comp (continuous_apply i)⟩,
        HasCompactSupport.of_compactSpace _⟩
    have hint_map : ∫ x, f x ∂(γ.map (fun z : E => z i)) = ∫ z, g z ∂γ := by
      rw [integral_map (φ := fun z : E => z i) (continuous_apply i).measurable.aemeasurable
        f.continuous.aestronglyMeasurable]
      rfl
    rw [hint_map, RealRMK.integral_rieszMeasure Λ g]
    have hdom : p (toB g) ≤ ∫ x, f x ∂μ := by
      let fs : Fin n → C(X, ℝ) := fun j => if j = i then f else 0
      calc p (toB g)
        _ ≤ ∑ j, ∫ x, fs j x ∂μ :=
            hp_le (toB g) fs
              (fun j x => by dsimp [fs]; split_ifs <;> [exact hf0 x; exact le_rfl])
              (fun z => by
                have : ∑ j, fs j (z j) = f (z i) := by
                  rw [Finset.sum_eq_single i]
                  · simp [fs]
                  · intro j _ hj; simp [fs, hj]
                  · intro h; exact (h (Finset.mem_univ i)).elim
                rw [this]; rfl)
        _ = ∫ x, f x ∂μ := by
            rw [Finset.sum_eq_single i]
            · simp [fs]
            · intro j _ hj; simp [fs, hj]
            · intro h; exact (h (Finset.mem_univ i)).elim
    exact (hΛ_le (toB g)).trans hdom
  · -- Lower bound cap μ n K ≤ γ K
    have hcap_le_p : cap μ n K ≤ ENNReal.ofReal (p v₀) := by
      have hp_eq : ∀ r ∈ S_p v₀, cap μ n K ≤ ENNReal.ofReal r := by
        rintro _ ⟨f, hf0, hdom, rfl⟩
        calc cap μ n K
          _ ≤ ∑ i, ∫⁻ x, ENNReal.ofReal (f i x) ∂μ :=
              cap_le_of_witness μ (fun i x => ENNReal.ofReal (f i x))
                (fun i => (f i).continuous.measurable.ennreal_ofReal)
                (fun z hz => by
                  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hf0 i (z i)]
                  have h1 : 1 ≤ ∑ i, f i (z i) := by
                    have := hdom z
                    simpa [v₀, hz] using this
                  exact ENNReal.ofReal_one.symm.trans_le (ENNReal.ofReal_le_ofReal h1))
          _ = ∑ i, ENNReal.ofReal (∫ x, f i x ∂μ) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              exact (ofReal_integral_eq_lintegral_ofReal
                ((f i).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
                (Eventually.of_forall fun x => hf0 i x)).symm
          _ = ENNReal.ofReal (∑ i, ∫ x, f i x ∂μ) :=
              (ENNReal.ofReal_sum_of_nonneg fun i _ => integral_nonneg fun x => hf0 i x).symm
      have hcap_ne_top : cap μ n K ≠ ⊤ :=
        (lt_of_le_of_lt (cap_le_measure_univ μ hn K) (measure_lt_top μ Set.univ)).ne
      rw [← ENNReal.ofReal_toReal hcap_ne_top]
      refine ENNReal.ofReal_le_ofReal (le_csInf (hS_ne v₀) fun r hr => ?_)
      rcases hr with ⟨f, hf0, hdom, rfl⟩
      have hr0 : 0 ≤ ∑ i, ∫ x, f i x ∂μ :=
        Finset.sum_nonneg fun i _ => integral_nonneg fun x => hf0 i x
      exact ENNReal.toReal_le_of_le_ofReal hr0 (hp_eq _ ⟨f, hf0, hdom, rfl⟩)
    -- Now show ENNReal.ofReal (p v₀) ≤ γ K using continuous approximation of 1_K
    let _ : MetricSpace E := TopologicalSpace.metrizableSpaceMetric E
    obtain ⟨gm, hgm_bnd, hgm_K, hgm_tend⟩ := exists_approx_closed hK ⟨z₀, hz₀⟩
    have hge : ∀ m, p v₀ ≤ ∫ z, gm m z ∂γ := by
      intro m
      let gmc : C_c(E, ℝ) := ⟨gm m, HasCompactSupport.of_compactSpace _⟩
      have h1 : p v₀ = Λ_full v₀ := by
        have hv₀W : v₀ ∈ W := Submodule.subset_span (Set.mem_singleton v₀)
        have := hΛ_ext ⟨v₀, hv₀W⟩
        simpa [ψ, hv₀_z₀] using this.symm
      rw [h1, show (∫ z, gm m z ∂γ) = Λ gmc from RealRMK.integral_rieszMeasure Λ gmc]
      exact hΛ_mono v₀ (toB gmc) fun z => by
        by_cases hz : z ∈ K
        · simp [v₀, hz, toB, gmc, hgm_K m z hz]
        · simp [v₀, hz, toB, gmc, (hgm_bnd m z).1]
    have ht_γ : Tendsto (fun m => ∫ z, gm m z ∂γ) atTop
        (𝓝 (∫ z, K.indicator (fun _ => (1 : ℝ)) z ∂γ)) :=
      tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun m => (gm m).continuous.aestronglyMeasurable) (integrable_const 1)
        (fun m => Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hgm_bnd m z).1]; exact (hgm_bnd m z).2)
        (Eventually.of_forall hgm_tend)
    have hle_real : p v₀ ≤ (γ K).toReal := by
      have h := ge_of_tendsto' ht_γ hge
      rw [integral_indicator_const _ hK.measurableSet] at h
      simpa [Measure.real] using h
    exact hcap_le_p.trans (by
      rw [← ENNReal.ofReal_toReal (measure_ne_top γ K)]
      exact ENNReal.ofReal_le_ofReal hle_real)

/-- Choquet capacitability + compactness on a compact Polish space `X`:
if `M` is Borel with `cap μ n M > 0`, then there is a measure `γ` on `Xⁿ` with marginals `≤ μ`
and `γ M > 0`. -/
private lemma compact_polish_case {X : Type*} [TopologicalSpace X] [PolishSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {n : ℕ} (hn : 0 < n) (M : Set (Fin n → X)) (hM : MeasurableSet M)
    (hpos : 0 < cap μ n M) :
    ∃ γ : Measure (Fin n → X), 0 < γ M ∧ ∀ i, γ.map (fun z : Fin n → X => z i) ≤ μ := by
  let E := Fin n → X
  have hM_ne : M.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, cap_empty] at hpos
    exact lt_irrefl _ hpos
  -- Obtain continuous surjection φ : (ℕ → ℕ) → M
  have hAn : AnalyticSet M := hM.analyticSet
  rw [AnalyticSet] at hAn
  have hφ_ex : ∃ φ : (ℕ → ℕ) → E, Continuous φ ∧ Set.range φ = M :=
    hAn.resolve_left hM_ne.ne_empty
  rcases hφ_ex with ⟨φ, hφ_cont, hφ_range⟩
  -- Pick threshold c ∈ (0, cap μ n M)
  have hcap_lt_top : cap μ n M < ⊤ :=
    lt_of_le_of_lt (cap_le_measure_univ μ hn M) (measure_lt_top μ Set.univ)
  obtain ⟨c, hc0, hc_lt⟩ := exists_between hpos
  have hc_lt_top : c < ⊤ := hc_lt.trans hcap_lt_top
  -- Inductively build b : ℕ → ℕ such that cap μ n (φ '' {α | ∀ j < m, α j ≤ b j}) > c
  let cyl : (m : ℕ) → (Fin m → ℕ) → Set (ℕ → ℕ) :=
    fun m bs => { α : ℕ → ℕ | ∀ j : Fin m, α j.1 ≤ bs j }
  have hstep : ∀ (m : ℕ) (bs : Fin m → ℕ),
      c < cap μ n (φ '' cyl m bs) →
      ∃ k : ℕ, c < cap μ n (φ '' cyl (m + 1) (Fin.snoc (α := fun _ => ℕ) bs k)) := by
    intro m bs hlt
    let A : ℕ → Set E := fun k => φ '' cyl (m + 1) (Fin.snoc (α := fun _ => ℕ) bs k)
    have hA_mono : Monotone A := by
      intro k₁ k₂ hk
      refine Set.image_mono fun α hα j => ?_
      refine Fin.lastCases ?_ ?_ j
      · have hlast : α m ≤ k₁ := by simpa [Fin.snoc_last] using hα (Fin.last m)
        simpa [Fin.snoc_last] using hlast.trans hk
      · intro j'
        simpa [Fin.snoc_castSucc] using hα j'.castSucc
    have hA_union : ⋃ k, A k = φ '' cyl m bs := by
      ext z; constructor
      · rintro ⟨_, ⟨k, rfl⟩, α, hα, rfl⟩
        exact ⟨α, fun j => by simpa [Fin.snoc_castSucc] using hα j.castSucc, rfl⟩
      · rintro ⟨α, hα, rfl⟩
        refine Set.mem_iUnion.mpr ⟨α m, α, fun j => ?_, rfl⟩
        refine Fin.lastCases ?_ ?_ j
        · simp [Fin.snoc_last]
        · intro j'; simpa [Fin.snoc_castSucc] using hα j'
    have hsup : c < ⨆ k, cap μ n (A k) := by
      rw [← cap_iUnion_of_monotone μ hn A hA_mono, hA_union]
      exact hlt
    exact lt_iSup_iff.mp hsup
  -- Construct dependent sequence of prefixes (bs m : Fin m → ℕ)
  let build : (m : ℕ) → { bs : Fin m → ℕ // c < cap μ n (φ '' cyl m bs) } :=
    Nat.rec
      ⟨Fin.elim0, by
        have : φ '' cyl 0 Fin.elim0 = M := by
          rw [← hφ_range]
          ext z; simp [cyl]
        rwa [this]⟩
      (fun m prev =>
        ⟨Fin.snoc (α := fun _ => ℕ) prev.1 (Classical.choose (hstep m prev.1 prev.2)),
          Classical.choose_spec (hstep m prev.1 prev.2)⟩)
  have hbuild_compat : ∀ m (j : Fin m), (build (m + 1)).1 j.castSucc = (build m).1 j := by
    intro m j
    exact Fin.snoc_castSucc (α := fun _ => ℕ) _ (build m).1 j
  let b : ℕ → ℕ := fun j => (build (j + 1)).1 (Fin.last j)
  have hbuild_eq : ∀ m (j : Fin m), (build m).1 j = b j.1 := by
    intro m
    induction m with
    | zero => intro j; exact j.elim0
    | succ m ih =>
        intro j
        refine Fin.lastCases ?_ ?_ j
        · rfl
        · intro j'
          rw [hbuild_compat m j', ih j']
          rfl
  let E_m : ℕ → Set (ℕ → ℕ) := fun m => { α | ∀ j < m, α j ≤ b j }
  have hEm_eq : ∀ m, E_m m = cyl m (build m).1 := by
    intro m; ext α; simp only [E_m, cyl, Set.mem_ofPred_eq]
    constructor
    · intro h j; rw [hbuild_eq m j]; exact h j.1 j.2
    · intro h j hj; have := h ⟨j, hj⟩; rwa [hbuild_eq m ⟨j, hj⟩] at this
  let K : ℕ → Set E := fun m => closure (φ '' E_m m)
  have hK_cl : ∀ m, IsClosed (K m) := fun m => isClosed_closure
  have hK_anti : Antitone K := by
    intro m₁ m₂ hm
    refine closure_mono (Set.image_mono fun α hα j hj => hα j (lt_of_lt_of_le hj hm))
  have hK_cap : ∀ m, c < cap μ n (K m) := fun m =>
    lt_of_lt_of_le (by rw [hEm_eq m]; exact (build m).2) (cap_mono μ subset_closure)
  -- Key Choquet inclusion: ⋂ m, K m ⊆ M
  have hInter_sub : (⋂ m, K m) ⊆ M := by
    let _ : MetricSpace E := TopologicalSpace.metrizableSpaceMetric E
    intro z hz
    have hα_ex : ∀ m : ℕ, ∃ α ∈ E_m m, dist (φ α) z < 1 / ((m : ℝ) + 1) := by
      intro m
      have hzm : z ∈ closure (φ '' E_m m) := Set.mem_iInter.mp hz m
      rcases Metric.mem_closure_iff.mp hzm (1 / ((m : ℝ) + 1)) (by positivity) with ⟨y, ⟨α, hα, rfl⟩, hy⟩
      exact ⟨α, hα, by rwa [dist_comm]⟩
    choose α hα_mem hα_dist using hα_ex
    obtain ⟨U, hU⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
    -- Coordinatewise convergence along ultrafilter U
    have hcoord : ∀ j : ℕ, ∃ a : ℕ, Tendsto (fun m => α m j) U (𝓝 a) := by
      intro j
      have hcomp : IsCompact (Set.Iic (b j)) := (Set.finite_Iic (b j)).isCompact
      have hev : ∀ᶠ m in (U : Filter ℕ), α m j ∈ Set.Iic (b j) :=
        hU (eventually_atTop.mpr ⟨j + 1, fun m hm => hα_mem m j (Nat.lt_of_succ_le hm)⟩)
      rcases hcomp.ultrafilter_le_nhds' (U.map (fun m => α m j)) (by rwa [Ultrafilter.mem_map])
        with ⟨a, _, ha⟩
      exact ⟨a, ha⟩
    choose a ha using hcoord
    have hα_tend : Tendsto α U (𝓝 a) := tendsto_pi_nhds.mpr ha
    have hφ_tend1 : Tendsto (fun m => φ (α m)) U (𝓝 (φ a)) := (hφ_cont.tendsto a).comp hα_tend
    have hφ_tend2 : Tendsto (fun m => φ (α m)) atTop (𝓝 z) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, fun m hm => (hα_dist m).trans ?_⟩
      rw [div_lt_iff₀ (by positivity)]
      have hm' : (N : ℝ) ≤ m := Nat.cast_le.mpr hm
      have h1 : 1 / ε < (m : ℝ) + 1 := by linarith
      have := (div_lt_iff₀ hε).mp h1
      linarith
    have hz_eq : φ a = z := tendsto_nhds_unique hφ_tend1 (hφ_tend2.mono_left hU)
    rw [← hφ_range]
    exact ⟨a, hz_eq⟩
  -- For each m, use compact_duality to get γ_m charging K_m
  have hγ_ex : ∀ m, ∃ γ : Measure E,
      (∀ i, γ.map (fun z : E => z i) ≤ μ) ∧ cap μ n (K m) ≤ γ (K m) :=
    fun m => compact_duality μ hn (K m) (hK_cl m)
  choose γs hγs_marg hγs_K using hγ_ex
  -- Wrap γs as FiniteMeasure E with uniformly bounded mass ≤ (μ univ).toNNReal
  let C : ℝ≥0 := (μ Set.univ).toNNReal
  have hγs_mass : ∀ m, γs m Set.univ ≤ μ Set.univ := fun m => by
    let i₀ : Fin n := ⟨0, hn⟩
    have h1 := hγs_marg m i₀ Set.univ
    rw [Measure.map_apply (continuous_apply i₀).measurable MeasurableSet.univ] at h1
    simpa using h1
  have hγs_fin : ∀ m, IsFiniteMeasure (γs m) := fun m =>
    ⟨lt_of_le_of_lt (hγs_mass m) (measure_lt_top μ Set.univ)⟩
  let fms : ℕ → FiniteMeasure E := fun m => ⟨γs m, hγs_fin m⟩
  have hfms_mem : ∀ m, fms m ∈ { ν : FiniteMeasure E | ν.mass ≤ C } := by
    intro m
    show (fms m).mass ≤ C
    rw [← ENNReal.coe_le_coe, FiniteMeasure.ennreal_mass]
    dsimp only [fms, C]
    rw [ENNReal.coe_toNNReal (measure_ne_top μ Set.univ)]
    exact hγs_mass m
  -- Compactness of {ν : FiniteMeasure E | ν.mass ≤ C} via Prokhorov
  have hcomp_fm : IsCompact { ν : FiniteMeasure E | ν.mass ≤ C } :=
    isCompact_setOfPred_finiteMeasure_le_of_compactSpace E C
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (atTop : Filter ℕ)
  obtain ⟨fm, _, hfm_tend⟩ := hcomp_fm.ultrafilter_le_nhds' (U.map fms)
    (by simp [Ultrafilter.mem_map]; exact Eventually.of_forall hfms_mem)
  let γ : Measure E := (fm : Measure E)
  have : IsFiniteMeasure γ := fm.property
  have hγ_tend : ∀ g : E →ᵇ ℝ, Tendsto (fun m => ∫ z, g z ∂(γs m)) U (𝓝 (∫ z, g z ∂γ)) :=
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hfm_tend)
  -- Verify marginals of γ are ≤ μ
  have hγ_marg : ∀ i, γ.map (fun z : E => z i) ≤ μ := by
    intro i
    have : IsFiniteMeasure (γ.map (fun z : E => z i)) := Measure.isFiniteMeasure_map γ _
    refine measure_le_of_forall_continuous_integral_le _ μ fun f hf0 => ?_
    let g : E →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨fun z => f (z i), f.continuous.comp (continuous_apply i)⟩
    have hlim := hγ_tend g
    have hle_m : ∀ m, ∫ z, g z ∂(γs m) ≤ ∫ x, f x ∂μ := by
      intro m
      have := hγs_fin m
      have hmap : ∫ z, g z ∂(γs m) = ∫ x, f x ∂((γs m).map (fun z : E => z i)) := by
        rw [integral_map (φ := fun z : E => z i) (continuous_apply i).measurable.aemeasurable f.continuous.aestronglyMeasurable]
        rfl
      rw [hmap]
      have : IsFiniteMeasure ((γs m).map (fun z : E => z i)) := Measure.isFiniteMeasure_map (γs m) _
      exact integral_mono_measure (hγs_marg m i) (Eventually.of_forall hf0)
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have hle_γ : ∫ z, g z ∂γ ≤ ∫ x, f x ∂μ := le_of_tendsto' hlim hle_m
    rw [integral_map (φ := fun z : E => z i) (continuous_apply i).measurable.aemeasurable f.continuous.aestronglyMeasurable]
    exact hle_γ
  -- Verify c ≤ γ (K m₀) for every m₀
  have hγ_Km : ∀ m₀, c ≤ γ (K m₀) := by
    intro m₀
    have hKne : (K m₀).Nonempty := by
      by_contra h
      have h0 := hK_cap m₀
      rw [Set.not_nonempty_iff_eq_empty.mp h, cap_empty] at h0
      exact not_lt_of_ge bot_le h0
    let _ : MetricSpace E := TopologicalSpace.metrizableSpaceMetric E
    obtain ⟨gr, hgr_bnd, hgr_K, hgr_tend⟩ := exists_approx_closed (hK_cl m₀) hKne
    have hge_r : ∀ r, c.toReal ≤ ∫ z, gr r z ∂γ := by
      intro r
      let gb : E →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact (gr r)
      refine ge_of_tendsto (hγ_tend gb) ?_
      refine hU (eventually_atTop.mpr ⟨m₀, fun m hm => ?_⟩)
      have := hγs_fin m
      have hKm_sub : K m ⊆ K m₀ := hK_anti hm
      calc c.toReal
        _ ≤ (γs m (K m)).toReal :=
            ENNReal.toReal_mono (measure_ne_top (γs m) _) ((hK_cap m).le.trans (hγs_K m))
        _ = ∫ z, (K m).indicator (fun _ => (1 : ℝ)) z ∂(γs m) := by
            rw [integral_indicator_const _ (hK_cl m).measurableSet]
            simp [Measure.real]
        _ ≤ ∫ z, gb z ∂(γs m) := by
            refine integral_mono
              ((integrable_const (1 : ℝ)).indicator (hK_cl m).measurableSet)
              ((gr r).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
              fun z => ?_
            by_cases hz : z ∈ K m
            · simp [hz, gb, hgr_K r z (hKm_sub hz)]
            · simp [hz, gb, (hgr_bnd r z).1]
    have ht_γ : Tendsto (fun r => ∫ z, gr r z ∂γ) atTop
        (𝓝 (∫ z, (K m₀).indicator (fun _ => (1 : ℝ)) z ∂γ)) :=
      tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
        (fun r => (gr r).continuous.aestronglyMeasurable) (integrable_const 1)
        (fun r => Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hgr_bnd r z).1]; exact (hgr_bnd r z).2)
        (Eventually.of_forall hgr_tend)
    have hle_real : c.toReal ≤ (γ (K m₀)).toReal := by
      have h := ge_of_tendsto' ht_γ hge_r
      rw [integral_indicator_const _ (hK_cl m₀).measurableSet] at h
      simpa [Measure.real] using h
    exact (ENNReal.toReal_le_toReal hc_lt_top.ne (measure_ne_top γ _)).mp hle_real
  -- Intersecting K m₀ gives c ≤ γ (⋂ m, K m) ≤ γ M
  have hγ_inter : c ≤ γ (⋂ m, K m) := by
    rw [hK_anti.measure_iInter (fun m => (hK_cl m).measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top γ _⟩]
    exact le_iInf hγ_Km
  exact ⟨γ, lt_of_lt_of_le hc0 (hγ_inter.trans (measure_mono hInter_sub)), hγ_marg⟩

end Helpers

theorem solution {Z : Type*} [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] (ζ : Measure Z) [IsProbabilityMeasure ζ] (n : ℕ) (M : Set (Fin n → Z))
    (hM : MeasurableSet M) :
    (∃ Ms : Fin n → Set (Fin n → Z),
        (∀ i, ζ ((fun z : Fin n → Z => z i) '' Ms i) = 0) ∧ M ⊆ ⋃ i, Ms i) ∨
      (∃ γ : Measure (Fin n → Z), 0 < γ M ∧
        ∀ i, γ.map (fun z : Fin n → Z => z i) ≤ ζ) := by
  -- Handle n = 0 separately
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases M.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
    · exact Or.inl ⟨Fin.elim0, fun i => i.elim0, Set.empty_subset _⟩
    · refine Or.inr ⟨Measure.dirac z₀, ?_, fun i => i.elim0⟩
      rw [Measure.dirac_apply' _ hM, Set.indicator_of_mem hz₀]
      exact zero_lt_one
  -- For n ≥ 1, branch on whether cap ζ n M = 0
  rcases eq_or_lt_of_le (bot_le : 0 ≤ cap ζ n M) with hzero | hpos
  · exact Or.inl (null_cover_of_cap_eq_zero ζ hzero.symm)
  · right
    -- Step 1: By inner regularity of ζ on Polish space Z, pick compact L_k with ζ (L_kᶜ) ≤ 1/(k+1)
    have hreg := MeasureTheory.innerRegular_isCompact_isClosed_measurableSet_of_finite ζ
    have hL_ex : ∀ k : ℕ, ∃ L : Set Z, IsCompact L ∧ ζ Lᶜ ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) := by
      intro k
      have hpos_k : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
        ENNReal.ofReal_pos.mpr (by positivity)
      have hlt : 1 - ENNReal.ofReal (1 / ((k : ℝ) + 1)) < ζ Set.univ := by
        rw [measure_univ]
        exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos_k.ne'
      rcases hreg MeasurableSet.univ _ hlt with ⟨L, _, ⟨hLcomp, hLcl⟩, hLmeas⟩
      refine ⟨L, hLcomp, ?_⟩
      rw [measure_compl hLcl.measurableSet (measure_ne_top ζ L), measure_univ]
      exact tsub_le_iff_left.mpr (by
        have := hLmeas.le
        rwa [tsub_le_iff_left, add_comm] at this)
    choose L hL_comp hL_compl using hL_ex
    -- Monotone increasing compact sets C k = ⋃ j ≤ k, L j
    let C : ℕ → Set Z := fun k => ⋃ j ∈ Finset.range (k + 1), L j
    have hC_comp : ∀ k, IsCompact (C k) := fun k =>
      (Finset.range (k + 1)).isCompact_biUnion fun j _ => hL_comp j
    have hC_mono : Monotone C := fun k₁ k₂ hk =>
      Set.biUnion_subset_biUnion_left (Finset.range_mono (Nat.add_le_add_right hk 1))
    let U_C : Set Z := ⋃ k, C k
    have hUC_meas : MeasurableSet U_C :=
      MeasurableSet.iUnion fun k => (hC_comp k).isClosed.measurableSet
    have hUC_compl : ζ U_Cᶜ = 0 := by
      refine le_antisymm ?_ bot_le
      have htend : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
        rw [← ENNReal.ofReal_zero]
        refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
        exact tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      refine ge_of_tendsto' htend fun k => ?_
      have hsub : U_Cᶜ ⊆ (L k)ᶜ := by
        intro x hx hxk
        apply hx
        exact Set.mem_iUnion.mpr ⟨k, Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_self k)) hxk⟩
      exact (measure_mono hsub).trans (hL_compl k)
    -- Step 2: cap ζ n M = cap ζ n (M ∩ {z | ∀ i, z i ∈ U_C}) = ⨆ k, cap ζ n (M ∩ {z | ∀ i, z i ∈ C k})
    classical
    let box : Set Z → Set (Fin n → Z) := fun S => { z | ∀ i, z i ∈ S }
    have hcap_UC : cap ζ n M = cap ζ n (M ∩ box U_C) := by
      refine le_antisymm ?_ (cap_mono ζ Set.inter_subset_left)
      refine le_sInf ?_
      rintro _ ⟨f, hf_meas, hcov, rfl⟩
      let f' : Fin n → Z → ℝ≥0∞ := fun i x => if x ∈ U_C then f i x else 1
      calc cap ζ n M
        _ ≤ ∑ i, ∫⁻ x, f' i x ∂ζ :=
            cap_le_of_witness ζ f'
              (fun i => Measurable.ite hUC_meas (hf_meas i) measurable_const)
              (fun z hz => by
                by_cases hbox : z ∈ box U_C
                · have hsum : ∑ i, f' i (z i) = ∑ i, f i (z i) :=
                    Finset.sum_congr rfl fun i _ => if_pos (hbox i)
                  rw [hsum]
                  exact hcov z ⟨hz, hbox⟩
                · simp only [box, Set.mem_ofPred_eq, not_forall] at hbox
                  rcases hbox with ⟨i, hi⟩
                  calc (1 : ℝ≥0∞) = f' i (z i) := by simp [f', hi]
                    _ ≤ ∑ j, f' j (z j) :=
                        Finset.single_le_sum (f := fun j => f' j (z j))
                          (fun _ _ => bot_le) (Finset.mem_univ i))
        _ = ∑ i, ∫⁻ x, f i x ∂ζ := by
            refine Finset.sum_congr rfl fun i _ => lintegral_congr_ae ?_
            have hae : ∀ᵐ x ∂ζ, x ∈ U_C := by
              rw [ae_iff]; exact hUC_compl
            filter_upwards [hae] with x hx
            simp [f', hx]
    have hbox_union : M ∩ box U_C = ⋃ k, (M ∩ box (C k)) := by
      ext z; constructor
      · rintro ⟨hzM, hzU⟩
        have hpick : ∀ i : Fin n, ∃ k, z i ∈ C k := fun i => Set.mem_iUnion.mp (hzU i)
        choose ks hks using hpick
        let k := Finset.univ.sup ks
        refine Set.mem_iUnion.mpr ⟨k, hzM, fun i => ?_⟩
        exact hC_mono (Finset.le_sup (f := ks) (Finset.mem_univ i)) (hks i)
      · rintro ⟨_, ⟨k, rfl⟩, hzM, hzk⟩
        exact ⟨hzM, fun i => Set.mem_iUnion.mpr ⟨k, hzk i⟩⟩
    have hsup_pos : 0 < ⨆ k, cap ζ n (M ∩ box (C k)) := by
      rw [← cap_iUnion_of_monotone ζ hn (fun k => M ∩ box (C k))
        (fun k₁ k₂ hk => Set.inter_subset_inter_right M fun z hz i => hC_mono hk (hz i)),
        ← hbox_union, ← hcap_UC]
      exact hpos
    rcases lt_iSup_iff.mp hsup_pos with ⟨k, hk_pos⟩
    -- Step 3: Restrict to the compact Polish space X = C k
    let X := C k
    have : CompactSpace X := isCompact_iff_compactSpace.mp (hC_comp k)
    have : PolishSpace X := (hC_comp k).isClosed.polishSpace
    let μ : Measure X := ζ.comap (Subtype.val : X → Z)
    have hC_meas : MeasurableSet (C k) := (hC_comp k).isClosed.measurableSet
    have hμ_map : μ.map (Subtype.val : X → Z) = ζ.restrict (C k) :=
      map_comap_subtype_coe hC_meas ζ
    have : IsFiniteMeasure μ := by
      constructor
      rw [comap_subtype_coe_apply hC_meas]
      exact measure_lt_top ζ _
    let emb : (Fin n → X) → (Fin n → Z) := fun x i => (x i : Z)
    have hemb_cont : Continuous emb := continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)
    let MX : Set (Fin n → X) := emb ⁻¹' M
    have hMX_meas : MeasurableSet MX := hM.preimage hemb_cont.measurable
    -- Show cap ζ n (M ∩ box (C k)) ≤ cap μ n MX
    have hcap_MX_pos : 0 < cap μ n MX := by
      refine lt_of_lt_of_le hk_pos ?_
      refine le_sInf ?_
      rintro _ ⟨f, hf_meas, hcov, rfl⟩
      let fZ : Fin n → Z → ℝ≥0∞ := fun i z =>
        if hz : z ∈ C k then f i ⟨z, hz⟩ else 0
      have hfZ_meas : ∀ i, Measurable (fZ i) := by
        intro i s hs
        have himg : MeasurableSet ((Subtype.val : X → Z) '' (f i ⁻¹' s)) :=
          (MeasurableEmbedding.subtype_coe hC_meas).measurableSet_image.mpr (hf_meas i hs)
        by_cases h0 : (0 : ℝ≥0∞) ∈ s
        · have heq : fZ i ⁻¹' s = ((Subtype.val : X → Z) '' (f i ⁻¹' s)) ∪ (C k)ᶜ := by
            ext z; simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_compl_iff]
            by_cases hz : z ∈ C k
            · simp only [fZ, dif_pos hz, hz, not_true_eq_false, or_false]
              exact ⟨fun h => ⟨⟨z, hz⟩, h, rfl⟩, by rintro ⟨⟨y, hy⟩, hfy, rfl⟩; exact hfy⟩
            · simp only [fZ, dif_neg hz, hz, not_false_eq_true, or_true, h0]
          rw [heq]
          exact himg.union hC_meas.compl
        · have heq : fZ i ⁻¹' s = (Subtype.val : X → Z) '' (f i ⁻¹' s) := by
            ext z; simp only [Set.mem_preimage, Set.mem_image]
            by_cases hz : z ∈ C k
            · simp only [fZ, dif_pos hz]
              exact ⟨fun h => ⟨⟨z, hz⟩, h, rfl⟩, by rintro ⟨⟨y, hy⟩, hfy, rfl⟩; exact hfy⟩
            · simp only [fZ, dif_neg hz, h0, false_iff, not_exists, not_and]
              rintro ⟨y, hy⟩ _ hyz
              exact hz (hyz ▸ hy)
          rw [heq]
          exact himg
      calc cap ζ n (M ∩ box (C k))
        _ ≤ ∑ i, ∫⁻ z, fZ i z ∂ζ :=
            cap_le_of_witness ζ fZ hfZ_meas fun z ⟨hzM, hzC⟩ => by
              let x : Fin n → X := fun i => ⟨z i, hzC i⟩
              have hxMX : x ∈ MX := hzM
              have hsum : ∑ i, fZ i (z i) = ∑ i, f i (x i) :=
                Finset.sum_congr rfl fun i _ => dif_pos (hzC i)
              rw [hsum]
              exact hcov x hxMX
        _ = ∑ i, ∫⁻ x, f i x ∂μ := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have h1 : ∫⁻ z, fZ i z ∂ζ = ∫⁻ z, fZ i z ∂(ζ.restrict (C k)) := by
              rw [← lintegral_indicator hC_meas]
              refine lintegral_congr fun z => ?_
              by_cases hz : z ∈ C k <;> simp [fZ, hz]
            rw [h1, ← hμ_map, lintegral_map (hfZ_meas i) continuous_subtype_val.measurable]
            refine lintegral_congr fun x => ?_
            simp [fZ]
    -- Step 4: Apply compact_polish_case on X and push forward γX to Zⁿ
    obtain ⟨γX, hγX_pos, hγX_marg⟩ := compact_polish_case μ hn MX hMX_meas hcap_MX_pos
    refine ⟨γX.map emb, ?_, ?_⟩
    · rw [Measure.map_apply hemb_cont.measurable hM]
      exact hγX_pos
    · intro i
      have hcomp : (fun z : Fin n → Z => z i) ∘ emb = (Subtype.val : X → Z) ∘ (fun x : Fin n → X => x i) := rfl
      rw [Measure.map_map (continuous_apply i).measurable hemb_cont.measurable, hcomp,
        ← Measure.map_map continuous_subtype_val.measurable (continuous_apply i).measurable]
      calc (γX.map (fun x : Fin n → X => x i)).map Subtype.val
        _ ≤ μ.map Subtype.val := Measure.map_mono (hγX_marg i) continuous_subtype_val.measurable
        _ = ζ.restrict (C k) := hμ_map
        _ ≤ ζ := Measure.restrict_le_self
