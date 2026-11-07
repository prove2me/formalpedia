-- Prove2me | solution 1 for HomogBiLimit.OutputFeedback.proposition_2_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T09:48:24.690444+00:00
-- url     : https://prove2.me/submissions/c0367e31-c179-4e5f-8d2f-e95b5294cdcc

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

open HomogBiLimit.OutputFeedback

namespace HBLSol210

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

lemma oneD_zero {ζ ζ₀ : ℝ → ℝ} {rζ dζ : ℝ}
    (h : IsHomogZero (fun v : Fin 1 → ℝ => ζ (v 0)) (fun _ => rζ) dζ (fun v => ζ₀ (v 0))) :
    0 < rζ ∧ 0 ≤ dζ ∧ Continuous ζ ∧ Continuous ζ₀ ∧
    (∀ w : ℝ, w ≠ 0 → ∀ μ : ℝ, 0 < μ → ζ₀ (μ ^ rζ * w) = μ ^ dζ * ζ₀ w) ∧
    (∀ ε : ℝ, 0 < ε → ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, 0 < l → l ≤ l₀ →
      ∀ u : ℝ, (u = 1 ∨ u = -1) → |ζ (l ^ rζ * u) / l ^ dζ - ζ₀ u| ≤ ε) := by
  have hc : Continuous (fun w : ℝ => (fun _ : Fin 1 => w)) :=
    continuous_pi (fun _ => continuous_id)
  refine ⟨h.1 0, h.2.1, h.2.2.1.comp hc, h.2.2.2.1.comp hc, ?_, ?_⟩
  · intro w hw μ hμ
    have hy : (fun _ : Fin 1 => w) ≠ 0 := fun h0 => hw (congrFun h0 0)
    have := zero_homog h hy hμ
    simpa [dil] using this
  · intro ε hε
    have hC : IsCompact ({fun _ => 1, fun _ => -1} : Set (Fin 1 → ℝ)) :=
      (Set.toFinite _).isCompact
    have h0 : (0 : Fin 1 → ℝ) ∉ ({fun _ => 1, fun _ => -1} : Set (Fin 1 → ℝ)) := by
      intro hm
      rcases hm with h0 | h0
      · have := congrFun h0 0; simp at this
      · have := congrFun (Set.mem_singleton_iff.1 h0) 0; simp at this
    obtain ⟨l₀, hl₀, hl⟩ := h.2.2.2.2.2 _ hC h0 ε hε
    refine ⟨l₀, hl₀, fun l hlp hll u hu => ?_⟩
    have hmem : (fun _ : Fin 1 => u) ∈ ({fun _ => 1, fun _ => -1} : Set (Fin 1 → ℝ)) := by
      rcases hu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    simpa [dil] using hl l hlp hll _ hmem

lemma oneD_infty {ζ ζ₀ : ℝ → ℝ} {rζ dζ : ℝ}
    (h : IsHomogInfty (fun v : Fin 1 → ℝ => ζ (v 0)) (fun _ => rζ) dζ (fun v => ζ₀ (v 0))) :
    0 < rζ ∧ 0 ≤ dζ ∧ Continuous ζ ∧ Continuous ζ₀ ∧
    (∀ w : ℝ, w ≠ 0 → ∀ μ : ℝ, 0 < μ → ζ₀ (μ ^ rζ * w) = μ ^ dζ * ζ₀ w) ∧
    (∀ ε : ℝ, 0 < ε → ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
      ∀ u : ℝ, (u = 1 ∨ u = -1) → |ζ (l ^ rζ * u) / l ^ dζ - ζ₀ u| ≤ ε) := by
  have hc : Continuous (fun w : ℝ => (fun _ : Fin 1 => w)) :=
    continuous_pi (fun _ => continuous_id)
  refine ⟨h.1 0, h.2.1, h.2.2.1.comp hc, h.2.2.2.1.comp hc, ?_, ?_⟩
  · intro w hw μ hμ
    have hy : (fun _ : Fin 1 => w) ≠ 0 := fun h0 => hw (congrFun h0 0)
    have := infty_homog h hy hμ
    simpa [dil] using this
  · intro ε hε
    have hC : IsCompact ({fun _ => 1, fun _ => -1} : Set (Fin 1 → ℝ)) :=
      (Set.toFinite _).isCompact
    have h0 : (0 : Fin 1 → ℝ) ∉ ({fun _ => 1, fun _ => -1} : Set (Fin 1 → ℝ)) := by
      intro hm
      rcases hm with h0 | h0
      · have := congrFun h0 0; simp at this
      · have := congrFun (Set.mem_singleton_iff.1 h0) 0; simp at this
    obtain ⟨l₀, hl₀, hl⟩ := h.2.2.2.2.2 _ hC h0 ε hε
    refine ⟨l₀, hl₀, fun l hll u hu => ?_⟩
    have hmem : (fun _ : Fin 1 => u) ∈ ({fun _ => 1, fun _ => -1} : Set (Fin 1 → ℝ)) := by
      rcases hu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    simpa [dil] using hl l hll _ hmem

lemma scale_id {ζ ζ₀ : ℝ → ℝ} {rζ dζ : ℝ} (hr : 0 < rζ)
    (hhom : ∀ w : ℝ, w ≠ 0 → ∀ μ : ℝ, 0 < μ → ζ₀ (μ ^ rζ * w) = μ ^ dζ * ζ₀ w)
    {w : ℝ} (hw : w ≠ 0) {μ : ℝ} (hμ : 0 < μ) :
    ∃ u ν : ℝ, (u = 1 ∨ u = -1) ∧ 0 < ν ∧ ν = |w| ^ (1 / rζ) ∧
      μ ^ rζ * w = (μ * ν) ^ rζ * u ∧ ζ₀ w = ν ^ dζ * ζ₀ u ∧
      ζ (μ ^ rζ * w) / μ ^ dζ - ζ₀ w =
        ν ^ dζ * (ζ ((μ * ν) ^ rζ * u) / (μ * ν) ^ dζ - ζ₀ u) := by
  have hwpos : 0 < |w| := abs_pos.2 hw
  obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = |w| ^ (1 / rζ) := ⟨_, rfl⟩
  have hν : 0 < ν := by rw [hνdef]; exact Real.rpow_pos_of_pos hwpos _
  have hνr : ν ^ rζ = |w| := by
    rw [hνdef, ← Real.rpow_mul hwpos.le, one_div_mul_cancel hr.ne', Real.rpow_one]
  have hu : ∃ u : ℝ, (u = 1 ∨ u = -1) ∧ w = |w| * u := by
    rcases lt_or_gt_of_ne hw with h | h
    · exact ⟨-1, Or.inr rfl, by rw [abs_of_neg h]; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [abs_of_pos h]; ring⟩
  obtain ⟨u, hu1, hwu⟩ := hu
  have hu0 : u ≠ 0 := by rcases hu1 with rfl | rfl <;> norm_num
  have e1 : μ ^ rζ * w = (μ * ν) ^ rζ * u := by
    calc μ ^ rζ * w = μ ^ rζ * (|w| * u) := by rw [← hwu]
      _ = (μ * ν) ^ rζ * u := by rw [Real.mul_rpow hμ.le hν.le, hνr]; ring
  have e2 : ζ₀ w = ν ^ dζ * ζ₀ u := by
    have := hhom u hu0 ν hν
    rw [hνr, ← hwu] at this
    exact this
  refine ⟨u, ν, hu1, hν, hνdef, e1, e2, ?_⟩
  rw [e1, e2, Real.mul_rpow (z := dζ) hμ.le hν.le]
  have : 0 < μ ^ dζ := Real.rpow_pos_of_pos hμ _
  have : 0 < ν ^ dζ := Real.rpow_pos_of_pos hν _
  field_simp

lemma extend_zero {f : ℝ → ℝ} (hf : Continuous f) {R ε : ℝ} (hR : 0 < R)
    (h : ∀ w : ℝ, w ≠ 0 → |w| ≤ R → |f w| ≤ ε) : |f 0| ≤ ε := by
  have hcl : IsClosed {w : ℝ | |f w| ≤ ε} :=
    isClosed_le (continuous_abs.comp hf) continuous_const
  have ht : Filter.Tendsto (fun k : ℕ => R / (k : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat R
  refine hcl.mem_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  refine h _ (div_ne_zero hR.ne' hkpos.ne') ?_
  rw [abs_of_pos (div_pos hR hkpos)]
  exact div_le_self hR.le hk'

lemma nu_pow_le {rζ dζ : ℝ} (hr : 0 < rζ) (hd : 0 ≤ dζ) {w R ν : ℝ} (hwR : |w| ≤ R)
    (hνdef : ν = |w| ^ (1 / rζ)) : ν ^ dζ ≤ R ^ (dζ / rζ) := by
  rw [hνdef, ← Real.rpow_mul (abs_nonneg _)]
  have : 1 / rζ * dζ = dζ / rζ := by ring
  rw [this]
  exact Real.rpow_le_rpow (abs_nonneg _) hwR (div_nonneg hd hr.le)

lemma unif_zero {ζ ζ₀ : ℝ → ℝ} {rζ dζ : ℝ} (hr : 0 < rζ) (hd : 0 ≤ dζ)
    (hζ : Continuous ζ) (hζ₀ : Continuous ζ₀)
    (hhom : ∀ w : ℝ, w ≠ 0 → ∀ μ : ℝ, 0 < μ → ζ₀ (μ ^ rζ * w) = μ ^ dζ * ζ₀ w)
    (hest : ∀ ε : ℝ, 0 < ε → ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, 0 < l → l ≤ l₀ →
      ∀ u : ℝ, (u = 1 ∨ u = -1) → |ζ (l ^ rζ * u) / l ^ dζ - ζ₀ u| ≤ ε)
    {R : ℝ} (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ → ∀ w : ℝ, |w| ≤ R →
      |ζ (μ ^ rζ * w) / μ ^ dζ - ζ₀ w| ≤ ε := by
  have hRd : 0 < R ^ (dζ / rζ) := Real.rpow_pos_of_pos hR _
  obtain ⟨l₁, hl₁, h1⟩ := hest (ε / R ^ (dζ / rζ)) (div_pos hε hRd)
  have hRν : 0 < R ^ (1 / rζ) := Real.rpow_pos_of_pos hR _
  refine ⟨l₁ / R ^ (1 / rζ), div_pos hl₁ hRν, fun μ hμ hμ₀ => ?_⟩
  have hnz : ∀ w : ℝ, w ≠ 0 → |w| ≤ R → |ζ (μ ^ rζ * w) / μ ^ dζ - ζ₀ w| ≤ ε := by
    intro w hw hwR
    obtain ⟨u, ν, hu, hν, hνdef, -, -, heq⟩ := scale_id (ζ := ζ) hr hhom hw hμ
    rw [heq, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hν _)]
    have hνR : ν ≤ R ^ (1 / rζ) := by
      rw [hνdef]; exact Real.rpow_le_rpow (abs_nonneg _) hwR (by positivity)
    have hνd := nu_pow_le hr hd hwR hνdef
    have hμν : μ * ν ≤ l₁ := by
      calc μ * ν ≤ (l₁ / R ^ (1 / rζ)) * R ^ (1 / rζ) :=
            mul_le_mul hμ₀ hνR hν.le (by positivity)
        _ = l₁ := by field_simp
    have := h1 (μ * ν) (mul_pos hμ hν) hμν u hu
    calc ν ^ dζ * |ζ ((μ * ν) ^ rζ * u) / (μ * ν) ^ dζ - ζ₀ u|
        ≤ R ^ (dζ / rζ) * (ε / R ^ (dζ / rζ)) := mul_le_mul hνd this (abs_nonneg _) hRd.le
      _ = ε := by field_simp
  intro w hwR
  rcases eq_or_ne w 0 with rfl | hw
  · exact extend_zero (f := fun w => ζ (μ ^ rζ * w) / μ ^ dζ - ζ₀ w)
      (((hζ.comp (continuous_const.mul continuous_id)).div_const _).sub hζ₀) hR hnz
  · exact hnz w hw hwR

lemma unif_infty {ζ ζ₀ : ℝ → ℝ} {rζ dζ : ℝ} (hr : 0 < rζ) (hd : 0 < dζ)
    (hζ : Continuous ζ) (hζ₀ : Continuous ζ₀)
    (hhom : ∀ w : ℝ, w ≠ 0 → ∀ μ : ℝ, 0 < μ → ζ₀ (μ ^ rζ * w) = μ ^ dζ * ζ₀ w)
    (hest : ∀ ε : ℝ, 0 < ε → ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
      ∀ u : ℝ, (u = 1 ∨ u = -1) → |ζ (l ^ rζ * u) / l ^ dζ - ζ₀ u| ≤ ε)
    {R : ℝ} (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, μ₀ ≤ μ → ∀ w : ℝ, |w| ≤ R →
      |ζ (μ ^ rζ * w) / μ ^ dζ - ζ₀ w| ≤ ε := by
  have hRd : 0 < R ^ (dζ / rζ) := Real.rpow_pos_of_pos hR _
  obtain ⟨l₁, hl₁, h1⟩ := hest (ε / R ^ (dζ / rζ)) (div_pos hε hRd)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -(l₁ ^ rζ)) (b := l₁ ^ rζ)).exists_bound_of_continuousOn
    hζ.continuousOn
  have hM : ∀ u : ℝ, (u = 1 ∨ u = -1) → |ζ₀ u| ≤ |ζ₀ 1| + |ζ₀ (-1)| := by
    rintro u (rfl | rfl)
    · linarith [abs_nonneg (ζ₀ (-1))]
    · linarith [abs_nonneg (ζ₀ 1)]
  have hMnn : 0 ≤ |ζ₀ 1| + |ζ₀ (-1)| := by positivity
  have hQ : 0 < (|B| + l₁ ^ dζ * (|ζ₀ 1| + |ζ₀ (-1)|) + 1) / ε := by
    have : 0 ≤ l₁ ^ dζ := Real.rpow_nonneg hl₁.le _
    positivity
  set Q := (|B| + l₁ ^ dζ * (|ζ₀ 1| + |ζ₀ (-1)|) + 1) / ε with hQdef
  refine ⟨max 1 (Q ^ (1 / dζ)), lt_of_lt_of_le one_pos (le_max_left _ _), fun μ hμ => ?_⟩
  have hμpos : 0 < μ := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hμ)
  have hμdpos : 0 < μ ^ dζ := Real.rpow_pos_of_pos hμpos _
  have hμd : Q ≤ μ ^ dζ := by
    calc Q = (Q ^ (1 / dζ)) ^ dζ := by
          rw [← Real.rpow_mul hQ.le, one_div_mul_cancel hd.ne', Real.rpow_one]
      _ ≤ μ ^ dζ := Real.rpow_le_rpow (Real.rpow_nonneg hQ.le _)
          (le_trans (le_max_right _ _) hμ) hd.le
  have hnz : ∀ w : ℝ, w ≠ 0 → |w| ≤ R → |ζ (μ ^ rζ * w) / μ ^ dζ - ζ₀ w| ≤ ε := by
    intro w hw hwR
    obtain ⟨u, ν, hu, hν, hνdef, he1, he2, heq⟩ := scale_id (ζ := ζ) hr hhom hw hμpos
    have hνd := nu_pow_le hr hd.le hwR hνdef
    rcases le_total l₁ (μ * ν) with hl | hl
    · rw [heq, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hν _)]
      have := h1 (μ * ν) hl u hu
      calc ν ^ dζ * |ζ ((μ * ν) ^ rζ * u) / (μ * ν) ^ dζ - ζ₀ u|
          ≤ R ^ (dζ / rζ) * (ε / R ^ (dζ / rζ)) := mul_le_mul hνd this (abs_nonneg _) hRd.le
        _ = ε := by field_simp
    · have hb1 : |ζ (μ ^ rζ * w)| ≤ |B| := by
        rw [he1]
        have h0 : 0 ≤ (μ * ν) ^ rζ := Real.rpow_nonneg (by positivity) _
        have h2 : (μ * ν) ^ rζ ≤ l₁ ^ rζ := Real.rpow_le_rpow (by positivity) hl hr.le
        have hmem : (μ * ν) ^ rζ * u ∈ Set.Icc (-(l₁ ^ rζ)) (l₁ ^ rζ) := by
          rcases hu with rfl | rfl
          · constructor <;> linarith
          · constructor <;> linarith
        exact le_trans (by simpa using hB _ hmem) (le_abs_self B)
      have hνl : ν ≤ l₁ / μ := by rw [le_div_iff₀ hμpos]; linarith
      have hb2 : |ζ₀ w| ≤ l₁ ^ dζ * (|ζ₀ 1| + |ζ₀ (-1)|) / μ ^ dζ := by
        rw [he2, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hν _)]
        have h3 : ν ^ dζ ≤ l₁ ^ dζ / μ ^ dζ := by
          rw [← Real.div_rpow hl₁.le hμpos.le]
          exact Real.rpow_le_rpow hν.le hνl hd.le
        calc ν ^ dζ * |ζ₀ u| ≤ (l₁ ^ dζ / μ ^ dζ) * (|ζ₀ 1| + |ζ₀ (-1)|) :=
              mul_le_mul h3 (hM u hu) (abs_nonneg _) (by positivity)
          _ = l₁ ^ dζ * (|ζ₀ 1| + |ζ₀ (-1)|) / μ ^ dζ := by ring
      have hb3 : |ζ (μ ^ rζ * w) / μ ^ dζ| ≤ |B| / μ ^ dζ := by
        rw [abs_div, abs_of_pos hμdpos]
        exact div_le_div_of_nonneg_right hb1 hμdpos.le
      have hsum : |B| / μ ^ dζ + l₁ ^ dζ * (|ζ₀ 1| + |ζ₀ (-1)|) / μ ^ dζ ≤ ε := by
        rw [← add_div, div_le_iff₀ hμdpos]
        have := mul_le_mul_of_nonneg_left hμd hε.le
        rw [hQdef, mul_div_cancel₀ _ hε.ne'] at this
        linarith
      rw [abs_le] at hb3 hb2 ⊢
      constructor <;> linarith [hb3.1, hb3.2, hb2.1, hb2.2]
  intro w hwR
  rcases eq_or_ne w 0 with rfl | hw
  · exact extend_zero (f := fun w => ζ (μ ^ rζ * w) / μ ^ dζ - ζ₀ w)
      (((hζ.comp (continuous_const.mul continuous_id)).div_const _).sub hζ₀) hR hnz
  · exact hnz w hw hwR

end HBLSol210

open HBLSol210 in
theorem solution {n : ℕ} (φ φ₀ φinf : (Fin n → ℝ) → ℝ) (ζ ζ₀ ζinf : ℝ → ℝ) :
    (∀ (rφ : Fin n → ℝ) (dφ rζ dζ : ℝ),
      0 < dφ → IsHomogZero φ rφ dφ φ₀ →
      IsHomogZero (fun v : Fin 1 → ℝ => ζ (v 0)) (fun _ => rζ) dζ (fun v => ζ₀ (v 0)) →
      (∃ x, ζ₀ (φ₀ x) ≠ 0) →
      IsHomogZero (fun x => ζ (φ x)) rφ (dζ * dφ / rζ) (fun x => ζ₀ (φ₀ x))) ∧
    (∀ (rφ : Fin n → ℝ) (dφ rζ dζ : ℝ),
      0 < dφ → 0 < dζ → IsHomogInfty φ rφ dφ φinf →
      IsHomogInfty (fun v : Fin 1 → ℝ => ζ (v 0)) (fun _ => rζ) dζ (fun v => ζinf (v 0)) →
      (∃ x, ζinf (φinf x) ≠ 0) →
      IsHomogInfty (fun x => ζ (φ x)) rφ (dζ * dφ / rζ) (fun x => ζinf (φinf x))) := by
  constructor
  · intro rφ dφ rζ dζ hdφ hφ hζh hnz
    obtain ⟨hrζ, hdζ, hζc, hζ₀c, hhom, hest⟩ := oneD_zero hζh
    obtain ⟨hrφ, -, hφc, hφ₀c, -, hφlim⟩ := hφ
    refine ⟨hrφ, by positivity, hζc.comp hφc, hζ₀c.comp hφ₀c, hnz, ?_⟩
    intro C hC h0C ε hε
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hφ₀c.continuousOn
    have hR : 0 < |B| + 1 := by positivity
    have huc := (isCompact_Icc (a := -(|B| + 1)) (b := |B| + 1)).uniformContinuousOn_of_continuous
      hζ₀c.continuousOn
    obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (by linarith)
    obtain ⟨μ₀, hμ₀, hU⟩ := unif_zero hrζ hdζ hζc hζ₀c hhom hest hR (ε := ε / 2) (by linarith)
    obtain ⟨l₁, hl₁, h1⟩ := hφlim C hC h0C (min (δ / 2) 1) (by positivity)
    have he : 0 < dφ / rζ := div_pos hdφ hrζ
    refine ⟨min l₁ (μ₀ ^ (1 / (dφ / rζ))), lt_min hl₁ (Real.rpow_pos_of_pos hμ₀ _),
      fun l hl hll x hx => ?_⟩
    show |ζ (φ (dil rφ l x)) / l ^ (dζ * dφ / rζ) - ζ₀ (φ₀ x)| ≤ ε
    obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = l ^ (dφ / rζ) := ⟨_, rfl⟩
    have hμ : 0 < μ := by rw [hμdef]; exact Real.rpow_pos_of_pos hl _
    have hμle : μ ≤ μ₀ := by
      calc μ = l ^ (dφ / rζ) := hμdef
        _ ≤ (μ₀ ^ (1 / (dφ / rζ))) ^ (dφ / rζ) :=
            Real.rpow_le_rpow hl.le (le_trans hll (min_le_right _ _)) he.le
        _ = μ₀ := by rw [← Real.rpow_mul hμ₀.le, one_div_mul_cancel he.ne', Real.rpow_one]
    have hμr : μ ^ rζ = l ^ dφ := by
      rw [hμdef, ← Real.rpow_mul hl.le]; congr 1; field_simp
    have hμd : μ ^ dζ = l ^ (dζ * dφ / rζ) := by
      rw [hμdef, ← Real.rpow_mul hl.le]; congr 1; ring
    have hlpos : 0 < l ^ dφ := Real.rpow_pos_of_pos hl _
    obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = φ (dil rφ l x) / l ^ dφ := ⟨_, rfl⟩
    have hw : φ (dil rφ l x) = μ ^ rζ * w := by rw [hμr, hwdef]; field_simp
    have hwx := h1 l hl (le_trans hll (min_le_left _ _)) x hx
    rw [← hwdef] at hwx
    have hBx : |φ₀ x| ≤ |B| := le_trans (by simpa using hB x hx) (le_abs_self B)
    have hwm : |w - φ₀ x| ≤ 1 := le_trans hwx (min_le_right _ _)
    have hwR : |w| ≤ |B| + 1 := by
      have := abs_sub_abs_le_abs_sub w (φ₀ x); linarith
    rw [hw, ← hμd]
    have a1 := hU μ hμ hμle w hwR
    have a2 : |ζ₀ w - ζ₀ (φ₀ x)| < ε / 2 := by
      have hm1 : w ∈ Set.Icc (-(|B| + 1)) (|B| + 1) := abs_le.1 hwR
      have hm2 : φ₀ x ∈ Set.Icc (-(|B| + 1)) (|B| + 1) := abs_le.1 (by linarith)
      have := hδu w hm1 (φ₀ x) hm2 (by
        rw [Real.dist_eq]; linarith [min_le_left (δ / 2) 1])
      rwa [Real.dist_eq] at this
    calc |ζ (μ ^ rζ * w) / μ ^ dζ - ζ₀ (φ₀ x)|
        ≤ |ζ (μ ^ rζ * w) / μ ^ dζ - ζ₀ w| + |ζ₀ w - ζ₀ (φ₀ x)| := abs_sub_le _ _ _
      _ ≤ ε := by linarith
  · intro rφ dφ rζ dζ hdφ hdζ hφ hζh hnz
    obtain ⟨hrζ, -, hζc, hζ₀c, hhom, hest⟩ := oneD_infty hζh
    obtain ⟨hrφ, -, hφc, hφ₀c, -, hφlim⟩ := hφ
    refine ⟨hrφ, by positivity, hζc.comp hφc, hζ₀c.comp hφ₀c, hnz, ?_⟩
    intro C hC h0C ε hε
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hφ₀c.continuousOn
    have hR : 0 < |B| + 1 := by positivity
    have huc := (isCompact_Icc (a := -(|B| + 1)) (b := |B| + 1)).uniformContinuousOn_of_continuous
      hζ₀c.continuousOn
    obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / 2) (by linarith)
    obtain ⟨μ₀, hμ₀, hU⟩ := unif_infty hrζ hdζ hζc hζ₀c hhom hest hR (ε := ε / 2) (by linarith)
    obtain ⟨l₁, hl₁, h1⟩ := hφlim C hC h0C (min (δ / 2) 1) (by positivity)
    have he : 0 < dφ / rζ := div_pos hdφ hrζ
    refine ⟨max l₁ (μ₀ ^ (1 / (dφ / rζ))), lt_max_of_lt_left hl₁, fun l hll x hx => ?_⟩
    show |ζ (φ (dil rφ l x)) / l ^ (dζ * dφ / rζ) - ζinf (φinf x)| ≤ ε
    have hl : 0 < l := lt_of_lt_of_le hl₁ (le_trans (le_max_left _ _) hll)
    obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = l ^ (dφ / rζ) := ⟨_, rfl⟩
    have hμ : 0 < μ := by rw [hμdef]; exact Real.rpow_pos_of_pos hl _
    have hμle : μ₀ ≤ μ := by
      calc μ₀ = (μ₀ ^ (1 / (dφ / rζ))) ^ (dφ / rζ) := by
            rw [← Real.rpow_mul hμ₀.le, one_div_mul_cancel he.ne', Real.rpow_one]
        _ ≤ l ^ (dφ / rζ) := Real.rpow_le_rpow (Real.rpow_nonneg hμ₀.le _)
            (le_trans (le_max_right _ _) hll) he.le
        _ = μ := hμdef.symm
    have hμr : μ ^ rζ = l ^ dφ := by
      rw [hμdef, ← Real.rpow_mul hl.le]; congr 1; field_simp
    have hμd : μ ^ dζ = l ^ (dζ * dφ / rζ) := by
      rw [hμdef, ← Real.rpow_mul hl.le]; congr 1; ring
    have hlpos : 0 < l ^ dφ := Real.rpow_pos_of_pos hl _
    obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = φ (dil rφ l x) / l ^ dφ := ⟨_, rfl⟩
    have hw : φ (dil rφ l x) = μ ^ rζ * w := by rw [hμr, hwdef]; field_simp
    have hwx := h1 l (le_trans (le_max_left _ _) hll) x hx
    rw [← hwdef] at hwx
    have hBx : |φinf x| ≤ |B| := le_trans (by simpa using hB x hx) (le_abs_self B)
    have hwm : |w - φinf x| ≤ 1 := le_trans hwx (min_le_right _ _)
    have hwR : |w| ≤ |B| + 1 := by
      have := abs_sub_abs_le_abs_sub w (φinf x); linarith
    rw [hw, ← hμd]
    have a1 := hU μ hμle w hwR
    have a2 : |ζinf w - ζinf (φinf x)| < ε / 2 := by
      have hm1 : w ∈ Set.Icc (-(|B| + 1)) (|B| + 1) := abs_le.1 hwR
      have hm2 : φinf x ∈ Set.Icc (-(|B| + 1)) (|B| + 1) := abs_le.1 (by linarith)
      have := hδu w hm1 (φinf x) hm2 (by
        rw [Real.dist_eq]; linarith [min_le_left (δ / 2) 1])
      rwa [Real.dist_eq] at this
    calc |ζ (μ ^ rζ * w) / μ ^ dζ - ζinf (φinf x)|
        ≤ |ζ (μ ^ rζ * w) / μ ^ dζ - ζinf w| + |ζinf w - ζinf (φinf x)| := abs_sub_le _ _ _
      _ ≤ ε := by linarith
