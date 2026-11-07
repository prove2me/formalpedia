-- Prove2me | solution 1 for HomogBiLimit.OutputFeedback.lemma_2_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T09:42:15.215213+00:00
-- url     : https://prove2.me/submissions/891315f6-fa37-4d5a-9b82-ba8ac034062f

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

open HomogBiLimit.OutputFeedback

namespace HBLSol213

/-- Homogeneous norm `N_r(x) = ∑ |xᵢ|^{1/rᵢ}`. -/
noncomputable def hN {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, |x i| ^ (1 / r i)

lemma dil_dil {n : ℕ} (r : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : Fin n → ℝ) :
    dil r a (dil r b x) = dil r (a * b) x := by
  funext i; simp only [dil]; rw [Real.mul_rpow ha hb]; ring

lemma dil_one {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ) : dil r 1 x = x := by
  funext i; simp [dil]

lemma hN_nonneg {n : ℕ} (r : Fin n → ℝ) (x : Fin n → ℝ) : 0 ≤ hN r x :=
  Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)

lemma hN_dil {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) {l : ℝ} (hl : 0 < l)
    (x : Fin n → ℝ) : hN r (dil r l x) = l * hN r x := by
  simp only [hN, dil, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hl _),
    Real.mul_rpow (Real.rpow_nonneg hl.le _) (abs_nonneg _), ← Real.rpow_mul hl.le,
    mul_one_div_cancel (hr i).ne', Real.rpow_one]

lemma hN_eq_zero_iff {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) :
    hN r x = 0 ↔ x = 0 := by
  constructor
  · intro h; funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) (1 / r i))).1 h i (Finset.mem_univ _)
    rw [Real.rpow_eq_zero (abs_nonneg _) (one_div_pos.2 (hr i)).ne'] at this
    simpa using this
  · rintro rfl
    exact Finset.sum_eq_zero (fun i _ => by
      simp only [Pi.zero_apply, abs_zero]; exact Real.zero_rpow (one_div_pos.2 (hr i)).ne')

lemma hN_continuous {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) : Continuous (hN r) :=
  continuous_finsetSum _ (fun i _ =>
    (continuous_apply i).abs.rpow_const (fun _ => Or.inr (one_div_pos.2 (hr i)).le))

lemma abs_le_of_hN_le {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) {x : Fin n → ℝ} {b : ℝ}
    (hb : hN r x ≤ b) (i : Fin n) : |x i| ≤ b ^ (r i) := by
  have h1 : |x i| ^ (1 / r i) ≤ b :=
    le_trans (Finset.single_le_sum (f := fun i => |x i| ^ (1 / r i))
      (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)) hb
  have h2 : |x i| = (|x i| ^ (1 / r i)) ^ (r i) := by
    rw [← Real.rpow_mul (abs_nonneg _), one_div_mul_cancel (hr i).ne', Real.rpow_one]
  rw [h2]
  exact Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) h1 (hr i).le

lemma isBounded_hN_le {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (b : ℝ) :
    Bornology.IsBounded {x : Fin n → ℝ | hN r x ≤ b} := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨∑ i, |b| ^ (r i), fun x hx => ?_⟩
  have hb0 : 0 ≤ b := le_trans (hN_nonneg r x) hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg
    (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _))]
  intro i
  rw [Real.norm_eq_abs]
  refine le_trans (abs_le_of_hN_le hr hx i) ?_
  rw [abs_of_nonneg hb0]
  exact Finset.single_le_sum (f := fun i => b ^ (r i))
    (fun j _ => Real.rpow_nonneg hb0 _) (Finset.mem_univ i)

lemma repr {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < hN r x ∧ hN r (dil r (hN r x)⁻¹ x) = 1 ∧ dil r (hN r x) (dil r (hN r x)⁻¹ x) = x := by
  have ht : 0 < hN r x :=
    lt_of_le_of_ne (hN_nonneg r x) (fun h => hx ((hN_eq_zero_iff hr x).1 h.symm))
  refine ⟨ht, ?_, ?_⟩
  · rw [hN_dil hr (inv_pos.2 ht), inv_mul_cancel₀ ht.ne']
  · rw [dil_dil r ht.le (inv_pos.2 ht).le, mul_inv_cancel₀ ht.ne', dil_one]

lemma dil_ne_zero {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) {μ : ℝ} (hμ : 0 < μ)
    {y : Fin n → ℝ} (hy : y ≠ 0) : dil r μ y ≠ 0 := by
  intro h
  have h1 := hN_dil hr hμ y
  rw [h, (hN_eq_zero_iff hr 0).2 rfl] at h1
  have : hN r y = 0 := by
    rcases mul_eq_zero.1 h1.symm with h2 | h2
    · exact absurd h2 hμ.ne'
    · exact h2
  exact hy ((hN_eq_zero_iff hr y).1 this)

/-- Compactness argument. -/
lemma cover {n : ℕ} {A : Set (Fin n → ℝ)} (hA : IsCompact A) {η γ : (Fin n → ℝ) → ℝ}
    (hη : Continuous η) (hγ : Continuous γ) (hγ0 : ∀ x ∈ A, 0 ≤ γ x)
    (h : ∀ x ∈ A, γ x = 0 → η x < 0) :
    ∃ c δ : ℝ, 0 ≤ c ∧ 0 < δ ∧ ∀ x ∈ A, η x - c * γ x ≤ -δ := by
  let V : ℕ → Set (Fin n → ℝ) :=
    fun k => {x | η x - (k : ℝ) * γ x < -(1 / ((k : ℝ) + 1))} ∪ Aᶜ
  have hVo : ∀ k, IsOpen (V k) := fun k =>
    (isOpen_lt (hη.sub (continuous_const.mul hγ)) continuous_const).union
      hA.isClosed.isOpen_compl
  have hcov : A ⊆ ⋃ k, V k := by
    intro x hx
    rcases (hγ0 x hx).eq_or_lt with h0 | hpos
    · have h1 := h x hx h0.symm
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (neg_pos.2 h1)
      refine Set.mem_iUnion.2 ⟨k, Or.inl ?_⟩
      simp only [Set.mem_setOf_eq]
      rw [← h0]; linarith
    · obtain ⟨k, hk⟩ := exists_nat_gt ((η x + 1) / γ x)
      refine Set.mem_iUnion.2 ⟨k, Or.inl ?_⟩
      simp only [Set.mem_setOf_eq]
      have h1 : η x + 1 < k * γ x := by rwa [div_lt_iff₀ hpos] at hk
      have h2 : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [k.cast_nonneg (α := ℝ)]
      linarith
  have hmono : Monotone V := by
    intro k m hkm x hx
    rcases hx with hx | hx
    · by_cases hxA : x ∈ A
      · left
        simp only [Set.mem_setOf_eq] at hx ⊢
        have hkm' : (k : ℝ) ≤ m := Nat.cast_le.2 hkm
        have h3 : 1 / ((m : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        nlinarith [mul_nonneg (sub_nonneg.2 hkm') (hγ0 x hxA)]
      · right; exact hxA
    · right; exact hx
  obtain ⟨k, hk⟩ := hA.elim_directed_cover V hVo hcov hmono.directed_le
  refine ⟨k, 1 / ((k : ℝ) + 1), k.cast_nonneg, by positivity, fun x hx => ?_⟩
  rcases hk hx with h1 | h1
  · exact le_of_lt h1
  · exact absurd hx h1

lemma limit_homog {n : ℕ} {r : Fin n → ℝ} {φ φ₀ : (Fin n → ℝ) → ℝ} {d : ℝ}
    {y : Fin n → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ l : ℝ, 0 < l ∧
      |φ (dil r l (dil r μ y)) / l ^ d - φ₀ (dil r μ y)| ≤ ε ∧
      |φ (dil r (l * μ) y) / (l * μ) ^ d - φ₀ y| ≤ ε) :
    φ₀ (dil r μ y) = μ ^ d * φ₀ y := by
  have hμd : 0 < μ ^ d := Real.rpow_pos_of_pos hμ d
  have key : ∀ ε : ℝ, 0 < ε → |φ₀ (dil r μ y) - μ ^ d * φ₀ y| ≤ ε * (1 + μ ^ d) := by
    intro ε hε
    obtain ⟨l, hl, h1, h2⟩ := h ε hε
    rw [dil_dil r hl.le hμ.le] at h1
    set P := φ (dil r (l * μ) y)
    have hld : 0 < l ^ d := Real.rpow_pos_of_pos hl d
    have he : P / l ^ d = μ ^ d * (P / (l * μ) ^ d) := by
      rw [Real.mul_rpow hl.le hμ.le]; field_simp
    rw [he] at h1
    have h3 : |μ ^ d * (P / (l * μ) ^ d) - μ ^ d * φ₀ y| ≤ μ ^ d * ε := by
      rw [← mul_sub, abs_mul, abs_of_pos hμd]
      exact mul_le_mul_of_nonneg_left h2 hμd.le
    calc |φ₀ (dil r μ y) - μ ^ d * φ₀ y|
        ≤ |φ₀ (dil r μ y) - μ ^ d * (P / (l * μ) ^ d)| +
          |μ ^ d * (P / (l * μ) ^ d) - μ ^ d * φ₀ y| := abs_sub_le _ _ _
      _ ≤ ε + μ ^ d * ε := by rw [abs_sub_comm] at h1; exact add_le_add h1 h3
      _ = ε * (1 + μ ^ d) := by ring
  by_contra hne
  have hD : 0 < |φ₀ (dil r μ y) - μ ^ d * φ₀ y| := abs_pos.2 (sub_ne_zero.2 hne)
  have h1 := key (|φ₀ (dil r μ y) - μ ^ d * φ₀ y| / (2 * (1 + μ ^ d))) (by positivity)
  have h2 : |φ₀ (dil r μ y) - μ ^ d * φ₀ y| / (2 * (1 + μ ^ d)) * (1 + μ ^ d) =
      |φ₀ (dil r μ y) - μ ^ d * φ₀ y| / 2 := by field_simp
  rw [h2] at h1
  linarith

lemma zero_homog {n : ℕ} {r : Fin n → ℝ} {φ φ₀ : (Fin n → ℝ) → ℝ} {d : ℝ}
    (hφ : IsHomogZero φ r d φ₀) {y : Fin n → ℝ} (hy : y ≠ 0) {μ : ℝ} (hμ : 0 < μ) :
    φ₀ (dil r μ y) = μ ^ d * φ₀ y := by
  obtain ⟨hr, -, -, -, -, hlim⟩ := hφ
  apply limit_homog hμ
  intro ε hε
  have hC : IsCompact ({y, dil r μ y} : Set (Fin n → ℝ)) := (Set.toFinite _).isCompact
  have h0 : (0 : Fin n → ℝ) ∉ ({y, dil r μ y} : Set (Fin n → ℝ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hy, Ne.symm (dil_ne_zero hr hμ hy)⟩
  obtain ⟨l₀, hl₀, hl⟩ := hlim _ hC h0 ε hε
  have hm : 0 < max 1 μ := lt_max_of_lt_left one_pos
  have hlpos : 0 < l₀ / max 1 μ := div_pos hl₀ hm
  refine ⟨l₀ / max 1 μ, hlpos, hl _ hlpos ?_ _ (by simp), hl _ (mul_pos hlpos hμ) ?_ y (by simp)⟩
  · exact div_le_self hl₀.le (le_max_left _ _)
  · rw [div_mul_eq_mul_div, div_le_iff₀ hm]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hl₀.le

lemma infty_homog {n : ℕ} {r : Fin n → ℝ} {φ φ₀ : (Fin n → ℝ) → ℝ} {d : ℝ}
    (hφ : IsHomogInfty φ r d φ₀) {y : Fin n → ℝ} (hy : y ≠ 0) {μ : ℝ} (hμ : 0 < μ) :
    φ₀ (dil r μ y) = μ ^ d * φ₀ y := by
  obtain ⟨hr, -, -, -, -, hlim⟩ := hφ
  apply limit_homog hμ
  intro ε hε
  have hC : IsCompact ({y, dil r μ y} : Set (Fin n → ℝ)) := (Set.toFinite _).isCompact
  have h0 : (0 : Fin n → ℝ) ∉ ({y, dil r μ y} : Set (Fin n → ℝ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨Ne.symm hy, Ne.symm (dil_ne_zero hr hμ hy)⟩
  obtain ⟨l₀, hl₀, hl⟩ := hlim _ hC h0 ε hε
  have hm : 1 ≤ max 1 μ⁻¹ := le_max_left _ _
  have hlpos : 0 < l₀ * max 1 μ⁻¹ := mul_pos hl₀ (by linarith)
  refine ⟨l₀ * max 1 μ⁻¹, hlpos, hl _ ?_ _ (by simp), hl _ ?_ y (by simp)⟩
  · exact le_mul_of_one_le_right hl₀.le hm
  · have h1 : 1 ≤ max 1 μ⁻¹ * μ := by
      calc (1 : ℝ) = μ⁻¹ * μ := (inv_mul_cancel₀ hμ.ne').symm
        _ ≤ max 1 μ⁻¹ * μ := mul_le_mul_of_nonneg_right (le_max_right _ _) hμ.le
    rw [mul_assoc]
    exact le_mul_of_one_le_right hl₀.le h1

lemma zero_nonneg {n : ℕ} {r : Fin n → ℝ} {φ φ₀ : (Fin n → ℝ) → ℝ} {d : ℝ}
    (hφ : IsHomogZero φ r d φ₀) (hpos : ∀ x, 0 ≤ φ x) {y : Fin n → ℝ} (hy : y ≠ 0) :
    0 ≤ φ₀ y := by
  obtain ⟨hr, -, -, -, -, hlim⟩ := hφ
  by_contra hneg
  push_neg at hneg
  obtain ⟨l₀, hl₀, hl⟩ := hlim {y} isCompact_singleton
    (by simpa [eq_comm] using hy) (-φ₀ y / 2) (by linarith)
  have h1 := hl l₀ hl₀ le_rfl y rfl
  have h2 : 0 ≤ φ (dil r l₀ y) / l₀ ^ d := div_nonneg (hpos _) (Real.rpow_nonneg hl₀.le _)
  rw [abs_le] at h1
  linarith [h1.2]

lemma infty_nonneg {n : ℕ} {r : Fin n → ℝ} {φ φ₀ : (Fin n → ℝ) → ℝ} {d : ℝ}
    (hφ : IsHomogInfty φ r d φ₀) (hpos : ∀ x, 0 ≤ φ x) {y : Fin n → ℝ} (hy : y ≠ 0) :
    0 ≤ φ₀ y := by
  obtain ⟨hr, -, -, -, -, hlim⟩ := hφ
  by_contra hneg
  push_neg at hneg
  obtain ⟨l₀, hl₀, hl⟩ := hlim {y} isCompact_singleton
    (by simpa [eq_comm] using hy) (-φ₀ y / 2) (by linarith)
  have h1 := hl l₀ le_rfl y rfl
  have h2 : 0 ≤ φ (dil r l₀ y) / l₀ ^ d := div_nonneg (hpos _) (Real.rpow_nonneg hl₀.le _)
  rw [abs_le] at h1
  linarith [h1.2]

lemma isCompact_sphere {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    IsCompact {y : Fin n → ℝ | hN r y = 1} :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_eq (hN_continuous hr) continuous_const)
    ((isBounded_hN_le hr 1).subset (fun y hy => le_of_eq hy))

lemma zero_not_mem_sphere {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    (0 : Fin n → ℝ) ∉ {y : Fin n → ℝ | hN r y = 1} := by
  simp [(hN_eq_zero_iff hr 0).2 rfl]

lemma estimate {A B a b c ε δ : ℝ} (hc : 0 ≤ c) (hA : |A - a| ≤ ε) (hB : |B - b| ≤ ε)
    (hab : a - c * b ≤ -δ) (hε : ε * (1 + c) < δ) : A - c * B < 0 := by
  rw [abs_le] at hA hB
  nlinarith [mul_le_mul_of_nonneg_left hB.1 hc]

lemma near_zero {n : ℕ} {r : Fin n → ℝ} {d : ℝ} {η η₀ γ γ₀ : (Fin n → ℝ) → ℝ}
    (hη : IsHomogZero η r d η₀) (hγ : IsHomogZero γ r d γ₀) {c δ : ℝ} (hc : 0 ≤ c)
    (hδ : 0 < δ) (hS : ∀ y, hN r y = 1 → η₀ y - c * γ₀ y ≤ -δ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ x, x ≠ 0 → hN r x ≤ l₀ → η x - c * γ x < 0 := by
  have hr := hη.1
  have hε : 0 < δ / (2 * (1 + c)) := by positivity
  obtain ⟨l₁, hl₁, h1⟩ := hη.2.2.2.2.2 _ (isCompact_sphere hr) (zero_not_mem_sphere hr) _ hε
  obtain ⟨l₂, hl₂, h2⟩ := hγ.2.2.2.2.2 _ (isCompact_sphere hr) (zero_not_mem_sphere hr) _ hε
  refine ⟨min l₁ l₂, lt_min hl₁ hl₂, fun x hx hxl => ?_⟩
  obtain ⟨ht, hy, hxy⟩ := repr hr hx
  set t := hN r x
  set y := dil r t⁻¹ x
  have e1 := h1 t ht (le_trans hxl (min_le_left _ _)) y hy
  have e2 := h2 t ht (le_trans hxl (min_le_right _ _)) y hy
  rw [hxy] at e1 e2
  have htd : 0 < t ^ d := Real.rpow_pos_of_pos ht d
  have hlt : η x / t ^ d - c * (γ x / t ^ d) < 0 := by
    refine estimate hc e1 e2 (hS y hy) ?_
    have : δ / (2 * (1 + c)) * (1 + c) = δ / 2 := by field_simp
    rw [this]; linarith
  have : η x - c * γ x = (η x / t ^ d - c * (γ x / t ^ d)) * t ^ d := by
    field_simp
  rw [this]
  exact mul_neg_of_neg_of_pos hlt htd

lemma near_infty {n : ℕ} {r : Fin n → ℝ} {d : ℝ} {η η₀ γ γ₀ : (Fin n → ℝ) → ℝ}
    (hη : IsHomogInfty η r d η₀) (hγ : IsHomogInfty γ r d γ₀) {c δ : ℝ} (hc : 0 ≤ c)
    (hδ : 0 < δ) (hS : ∀ y, hN r y = 1 → η₀ y - c * γ₀ y ≤ -δ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ x, x ≠ 0 → l₀ ≤ hN r x → η x - c * γ x < 0 := by
  have hr := hη.1
  have hε : 0 < δ / (2 * (1 + c)) := by positivity
  obtain ⟨l₁, hl₁, h1⟩ := hη.2.2.2.2.2 _ (isCompact_sphere hr) (zero_not_mem_sphere hr) _ hε
  obtain ⟨l₂, hl₂, h2⟩ := hγ.2.2.2.2.2 _ (isCompact_sphere hr) (zero_not_mem_sphere hr) _ hε
  refine ⟨max l₁ l₂, lt_max_of_lt_left hl₁, fun x hx hxl => ?_⟩
  obtain ⟨ht, hy, hxy⟩ := repr hr hx
  set t := hN r x
  set y := dil r t⁻¹ x
  have e1 := h1 t (le_trans (le_max_left _ _) hxl) y hy
  have e2 := h2 t (le_trans (le_max_right _ _) hxl) y hy
  rw [hxy] at e1 e2
  have htd : 0 < t ^ d := Real.rpow_pos_of_pos ht d
  have hlt : η x / t ^ d - c * (γ x / t ^ d) < 0 := by
    refine estimate hc e1 e2 (hS y hy) ?_
    have : δ / (2 * (1 + c)) * (1 + c) = δ / 2 := by field_simp
    rw [this]; linarith
  have : η x - c * γ x = (η x / t ^ d - c * (γ x / t ^ d)) * t ^ d := by
    field_simp
  rw [this]
  exact mul_neg_of_neg_of_pos hlt htd

end HBLSol213

open HBLSol213 in
theorem solution {n : ℕ} (η η₀ ηinf γ γ₀ γinf : (Fin n → ℝ) → ℝ)
    (r₀ rinf : Fin n → ℝ) (d₀ dinf : ℝ)
    (hη : IsHomogBiLimit η r₀ d₀ η₀ rinf dinf ηinf)
    (hγ : IsHomogBiLimit γ r₀ d₀ γ₀ rinf dinf γinf)
    (hγ_nonneg : ∀ x, 0 ≤ γ x)
    (h : ∀ x, x ≠ 0 → γ x = 0 → η x < 0)
    (h₀ : ∀ x, x ≠ 0 → γ₀ x = 0 → η₀ x < 0)
    (hinf : ∀ x, x ≠ 0 → γinf x = 0 → ηinf x < 0) :
    ∃ cstar : ℝ, ∀ c : ℝ, cstar ≤ c → ∀ x : Fin n → ℝ, x ≠ 0 →
      η x - c * γ x < 0 ∧ η₀ x - c * γ₀ x < 0 ∧ ηinf x - c * γinf x < 0 := by
  obtain ⟨hη0, hηi⟩ := hη
  obtain ⟨hγ0, hγi⟩ := hγ
  have hr₀ := hη0.1
  have hri := hηi.1
  have hγ₀nn : ∀ y, y ≠ 0 → 0 ≤ γ₀ y := fun y hy => zero_nonneg hγ0 hγ_nonneg hy
  have hγinn : ∀ y, y ≠ 0 → 0 ≤ γinf y := fun y hy => infty_nonneg hγi hγ_nonneg hy
  -- zero approximation on the sphere
  obtain ⟨c₀, δ₀, hc₀, hδ₀, hS₀⟩ := cover (isCompact_sphere hr₀) hη0.2.2.2.1 hγ0.2.2.2.1
    (fun y hy => hγ₀nn y (fun h0 => zero_not_mem_sphere hr₀ (h0 ▸ hy)))
    (fun y hy => h₀ y (fun h0 => zero_not_mem_sphere hr₀ (h0 ▸ hy)))
  obtain ⟨ci, δi, hci, hδi, hSi⟩ := cover (isCompact_sphere hri) hηi.2.2.2.1 hγi.2.2.2.1
    (fun y hy => hγinn y (fun h0 => zero_not_mem_sphere hri (h0 ▸ hy)))
    (fun y hy => hinf y (fun h0 => zero_not_mem_sphere hri (h0 ▸ hy)))
  obtain ⟨l₀, hl₀, hz⟩ := near_zero hη0 hγ0 hc₀ hδ₀ hS₀
  obtain ⟨li, hli, hi⟩ := near_infty hηi hγi hci hδi hSi
  -- middle region
  set M : Set (Fin n → ℝ) := {x | l₀ ≤ hN r₀ x ∧ hN rinf x ≤ li}
  have hMc : IsCompact M :=
    Metric.isCompact_of_isClosed_isBounded
      ((isClosed_le continuous_const (hN_continuous hr₀)).inter
        (isClosed_le (hN_continuous hri) continuous_const))
      ((isBounded_hN_le hri li).subset (fun x hx => hx.2))
  have hMne : ∀ x ∈ M, x ≠ 0 := by
    intro x hx h0
    have := hx.1
    rw [h0, (hN_eq_zero_iff hr₀ 0).2 rfl] at this
    linarith
  obtain ⟨c₁, δ₁, hc₁, hδ₁, hM⟩ := cover hMc hη0.2.2.1 hγ0.2.2.1
    (fun x _ => hγ_nonneg x) (fun x hx => h x (hMne x hx))
  refine ⟨max c₀ (max ci c₁), fun c hc x hx => ⟨?_, ?_, ?_⟩⟩
  · have hmono : ∀ c' : ℝ, c' ≤ c → η x - c * γ x ≤ η x - c' * γ x := fun c' hc' => by
      nlinarith [mul_le_mul_of_nonneg_right hc' (hγ_nonneg x)]
    rcases le_total (hN r₀ x) l₀ with h1 | h1
    · exact lt_of_le_of_lt (hmono c₀ (le_trans (le_max_left _ _) hc)) (hz x hx h1)
    rcases le_total li (hN rinf x) with h2 | h2
    · exact lt_of_le_of_lt (hmono ci (le_trans (le_trans (le_max_left _ _)
        (le_max_right _ _)) hc)) (hi x hx h2)
    · have := hM x ⟨h1, h2⟩
      have h3 := hmono c₁ (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hc)
      linarith
  · obtain ⟨ht, hy, hxy⟩ := repr hr₀ hx
    have hy0 : dil r₀ (hN r₀ x)⁻¹ x ≠ 0 := fun h0 => zero_not_mem_sphere hr₀ (h0 ▸ hy)
    have e1 := zero_homog hη0 hy0 ht
    have e2 := zero_homog hγ0 hy0 ht
    rw [hxy] at e1 e2
    have h3 := hS₀ _ hy
    have htd : 0 < hN r₀ x ^ d₀ := Real.rpow_pos_of_pos ht d₀
    have h4 : η₀ x - c₀ * γ₀ x < 0 := by
      rw [e1, e2]
      have : hN r₀ x ^ d₀ * η₀ (dil r₀ (hN r₀ x)⁻¹ x) -
          c₀ * (hN r₀ x ^ d₀ * γ₀ (dil r₀ (hN r₀ x)⁻¹ x)) =
          hN r₀ x ^ d₀ * (η₀ (dil r₀ (hN r₀ x)⁻¹ x) - c₀ * γ₀ (dil r₀ (hN r₀ x)⁻¹ x)) := by
        ring
      rw [this]
      exact mul_neg_of_pos_of_neg htd (by linarith)
    have := mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) hc) (hγ₀nn x hx)
    linarith
  · obtain ⟨ht, hy, hxy⟩ := repr hri hx
    have hy0 : dil rinf (hN rinf x)⁻¹ x ≠ 0 := fun h0 => zero_not_mem_sphere hri (h0 ▸ hy)
    have e1 := infty_homog hηi hy0 ht
    have e2 := infty_homog hγi hy0 ht
    rw [hxy] at e1 e2
    have h3 := hSi _ hy
    have htd : 0 < hN rinf x ^ dinf := Real.rpow_pos_of_pos ht dinf
    have h4 : ηinf x - ci * γinf x < 0 := by
      rw [e1, e2]
      have : hN rinf x ^ dinf * ηinf (dil rinf (hN rinf x)⁻¹ x) -
          ci * (hN rinf x ^ dinf * γinf (dil rinf (hN rinf x)⁻¹ x)) =
          hN rinf x ^ dinf * (ηinf (dil rinf (hN rinf x)⁻¹ x) -
            ci * γinf (dil rinf (hN rinf x)⁻¹ x)) := by
        ring
      rw [this]
      exact mul_neg_of_pos_of_neg htd (by linarith)
    have := mul_le_mul_of_nonneg_right
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hc) (hγinn x hx)
    linarith
