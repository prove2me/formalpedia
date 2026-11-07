-- Prove2me | solution 1 for HomogBiLimit.OutputFeedback.proposition_2_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T09:55:57.527421+00:00
-- url     : https://prove2.me/submissions/39d7b2f1-ca4d-488a-b541-a0a1ad058af1

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

open HomogBiLimit.OutputFeedback

namespace HBLSol212

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

lemma zero_not_mem_sphere {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    (0 : Fin n → ℝ) ∉ {y : Fin n → ℝ | hN r y = 1} := by
  simp [(hN_eq_zero_iff hr 0).2 rfl]

lemma isCompact_sphere {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    IsCompact {y : Fin n → ℝ | hN r y = 1} :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_eq (hN_continuous hr) continuous_const)
    ((isBounded_hN_le hr 1).subset (fun y hy => le_of_eq hy))

lemma isCompact_ball {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (b : ℝ) :
    IsCompact {y : Fin n → ℝ | hN r y ≤ b} :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_le (hN_continuous hr) continuous_const)
    (isBounded_hN_le hr b)

lemma abs_sub_le_add' (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]

lemma abs_add_le' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]; constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]

lemma repr' {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) {z : Fin n → ℝ} (hz : z ≠ 0) :
    ∃ t y, 0 < t ∧ t = hN r z ∧ hN r y = 1 ∧ z = dil r t y := by
  obtain ⟨ht, hy, hzy⟩ := repr hr hz
  exact ⟨_, _, ht, rfl, hy, hzy.symm⟩

lemma hN_single {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (i : Fin n) (s : ℝ) :
    hN r (Pi.single i s) = |s| ^ (1 / r i) := by
  unfold hN
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, abs_zero, Real.zero_rpow (one_div_pos.2 (hr j)).ne']
  · intro h; exact absurd (Finset.mem_univ i) h

lemma hN_update_le {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (i : Fin n)
    (x : Fin n → ℝ) {σ : ℝ} (hσ : |σ| ≤ |x i|) : hN r (Function.update x i σ) ≤ hN r x := by
  unfold hN
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [Function.update_apply]
  split_ifs with h
  · subst h; exact Real.rpow_le_rpow (abs_nonneg _) hσ (one_div_pos.2 (hr j)).le
  · exact le_rfl

lemma hN_update_ge {n : ℕ} (r : Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) (σ : ℝ) :
    |σ| ^ (1 / r i) ≤ hN r (Function.update x i σ) := by
  have := Finset.single_le_sum (f := fun j => |Function.update x i σ j| ^ (1 / r j))
    (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
  unfold hN
  simpa using this

lemma abs_le_of_mem_uIcc {σ b : ℝ} (h : σ ∈ Set.uIcc 0 b) : |σ| ≤ |b| := by
  rw [Set.mem_uIcc] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 h2)]; exact h2
  · rw [abs_of_nonpos h2, abs_of_nonpos (le_trans h1 h2)]; linarith

lemma extend_zero_n {n : ℕ} {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) (i : Fin n)
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f) {R ε : ℝ} (hR : 0 < R)
    (h : ∀ z, z ≠ 0 → hN r z ≤ R → |f z| ≤ ε) : |f 0| ≤ ε := by
  have hcl : IsClosed {z : Fin n → ℝ | |f z| ≤ ε} :=
    isClosed_le (continuous_abs.comp hf) continuous_const
  have hc : 0 < R ^ (r i) := Real.rpow_pos_of_pos hR _
  have ht : Filter.Tendsto (fun k : ℕ => (Pi.single i (R ^ (r i) / (k : ℝ)) : Fin n → ℝ))
      Filter.atTop (nhds 0) := by
    have := ((continuous_single i (A := fun _ : Fin n => ℝ)).tendsto 0).comp
      (tendsto_const_div_atTop_nhds_zero_nat (R ^ (r i)))
    rw [Pi.single_zero] at this
    exact this
  refine hcl.mem_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hpos : 0 < R ^ (r i) / (k : ℝ) := div_pos hc hkpos
  apply h
  · intro h0
    have := congrFun h0 i
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hpos.ne' this
  · rw [hN_single hr, abs_of_pos hpos]
    calc (R ^ (r i) / (k : ℝ)) ^ (1 / r i) ≤ (R ^ (r i)) ^ (1 / r i) :=
          Real.rpow_le_rpow hpos.le (div_le_self hc.le hk') (one_div_pos.2 (hr i)).le
      _ = R := by rw [← Real.rpow_mul hR.le, mul_one_div_cancel (hr i).ne', Real.rpow_one]

lemma int_bound {h : ℝ → ℝ} (hc : Continuous h) {b a M ε₁ : ℝ} (ha : 0 < a)
    (hM : ∀ σ ∈ Set.uIcc 0 b, |h σ| ≤ M) (hε : ∀ σ ∈ Set.uIcc 0 b, a ≤ |σ| → |h σ| ≤ ε₁)
    (hε0 : 0 ≤ ε₁) (hM0 : 0 ≤ M) :
    |∫ σ in (0 : ℝ)..b, h σ| ≤ M * a + ε₁ * |b| := by
  have hii : ∀ u v : ℝ, IntervalIntegrable h MeasureTheory.volume u v :=
    fun u v => hc.intervalIntegrable u v
  rcases le_or_gt |b| a with hb | hb
  · have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := b) (C := M)
      (f := h) (fun σ hσ => by rw [Real.norm_eq_abs]; exact hM σ (Set.uIoc_subset_uIcc hσ))
    rw [Real.norm_eq_abs, sub_zero] at this
    nlinarith [abs_nonneg b, mul_le_mul_of_nonneg_left hb hM0, mul_nonneg hε0 (abs_nonneg b)]
  · rcases le_or_gt 0 b with hb0 | hb0
    · rw [abs_of_nonneg hb0] at hb
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 a) (hii a b)]
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := a) (C := M)
        (f := h) (fun σ hσ => by
          rw [Real.norm_eq_abs]; apply hM; rw [Set.mem_uIoc] at hσ; rw [Set.mem_uIcc]; left
          rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith)
      have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := ε₁)
        (f := h) (fun σ hσ => by
          rw [Real.norm_eq_abs]; rw [Set.mem_uIoc] at hσ
          have hσ' : a < σ ∧ σ ≤ b := by
            rcases hσ with h | ⟨h1, h2⟩
            · exact h
            · exfalso; linarith
          exact hε σ (by rw [Set.mem_uIcc]; left; constructor <;> linarith)
            (by rw [abs_of_pos (by linarith)]; linarith))
      rw [Real.norm_eq_abs, sub_zero, abs_of_pos ha] at h1
      rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < b - a)] at h2
      rw [abs_of_nonneg hb0]
      calc _ ≤ |∫ σ in (0 : ℝ)..a, h σ| + |∫ σ in a..b, h σ| := abs_add_le' _ _
        _ ≤ M * a + ε₁ * (b - a) := add_le_add h1 h2
        _ ≤ M * a + ε₁ * b := by nlinarith
    · rw [abs_of_neg hb0] at hb
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 (-a)) (hii (-a) b)]
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := -a) (C := M)
        (f := h) (fun σ hσ => by
          rw [Real.norm_eq_abs]; apply hM; rw [Set.mem_uIoc] at hσ; rw [Set.mem_uIcc]; right
          rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith)
      have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -a) (b := b) (C := ε₁)
        (f := h) (fun σ hσ => by
          rw [Real.norm_eq_abs]; rw [Set.mem_uIoc] at hσ
          have hσ' : b < σ ∧ σ ≤ -a := by
            rcases hσ with ⟨h1, h2⟩ | h
            · exfalso; linarith
            · exact h
          exact hε σ (by rw [Set.mem_uIcc]; right; constructor <;> linarith)
            (by rw [abs_of_neg (by linarith)]; linarith))
      rw [Real.norm_eq_abs, sub_zero, abs_neg, abs_of_pos ha] at h1
      rw [Real.norm_eq_abs, abs_of_neg (by linarith : b - -a < 0)] at h2
      rw [abs_of_neg hb0]
      calc _ ≤ |∫ σ in (0 : ℝ)..(-a), h σ| + |∫ σ in (-a)..b, h σ| := abs_add_le' _ _
        _ ≤ M * a + ε₁ * (-(b - -a)) := add_le_add h1 h2
        _ ≤ M * a + ε₁ * (-b) := by nlinarith

lemma update_dil {n : ℕ} (r : Fin n → ℝ) (i : Fin n) (l : ℝ) (x : Fin n → ℝ) (σ : ℝ) :
    Function.update (dil r l x) i (l ^ r i * σ) = dil r l (Function.update x i σ) := by
  funext j
  simp only [dil, Function.update_apply]
  split_ifs with h
  · subst h; rfl
  · rfl

lemma integral_scale {n : ℕ} (φ : (Fin n → ℝ) → ℝ) {r : Fin n → ℝ} (i : Fin n) {l : ℝ}
    (hl : 0 < l) (x : Fin n → ℝ) (d : ℝ) :
    (∫ s in (0 : ℝ)..(dil r l x) i, φ (Function.update (dil r l x) i s)) / l ^ (d + r i) =
      ∫ σ in (0 : ℝ)..x i, φ (dil r l (Function.update x i σ)) / l ^ d := by
  have hc : 0 < l ^ r i := Real.rpow_pos_of_pos hl _
  have h1 : (∫ σ in (0 : ℝ)..x i, φ (dil r l (Function.update x i σ))) =
      (l ^ r i)⁻¹ * ∫ s in (0 : ℝ)..(dil r l x) i, φ (Function.update (dil r l x) i s) := by
    simp_rw [← update_dil]
    rw [intervalIntegral.integral_comp_mul_left (fun s => φ (Function.update (dil r l x) i s))
      hc.ne', mul_zero, smul_eq_mul]
    rfl
  rw [intervalIntegral.integral_div, h1, Real.rpow_add hl]
  have : 0 < l ^ d := Real.rpow_pos_of_pos hl _
  field_simp

lemma cont_int {n : ℕ} (i : Fin n) {g : (Fin n → ℝ) → ℝ} (hg : Continuous g) :
    Continuous (fun x : Fin n → ℝ => ∫ s in (0 : ℝ)..x i, g (Function.update x i s)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun x s => g (Function.update x i s))
    (hg.comp (continuous_fst.update i continuous_snd)) (continuous_apply i)

lemma nontriv {n : ℕ} (i : Fin n) {g : (Fin n → ℝ) → ℝ} (hg : Continuous g)
    (hne : ∃ x, g x ≠ 0) : ∃ x, (∫ s in (0 : ℝ)..x i, g (Function.update x i s)) ≠ 0 := by
  obtain ⟨x, hx⟩ := hne
  by_contra hall
  push_neg at hall
  have hG : Continuous (fun s => g (Function.update x i s)) :=
    hg.comp (continuous_const.update i continuous_id)
  have hF : (fun t => ∫ s in (0 : ℝ)..t, g (Function.update x i s)) = fun _ => 0 := by
    funext t
    have := hall (Function.update x i t)
    simpa [Function.update_idem] using this
  have hd := (hG.integral_hasStrictDerivAt 0 (x i)).hasDerivAt
  rw [hF] at hd
  have := hd.unique (hasDerivAt_const (x i) (0 : ℝ))
  simp only [Function.update_eq_self] at this
  exact hx this

lemma dil_zero {n : ℕ} (r : Fin n → ℝ) (l : ℝ) : dil r l 0 = 0 := by
  funext j; simp [dil]

lemma dil_continuous {n : ℕ} (r : Fin n → ℝ) (l : ℝ) : Continuous (dil r l) :=
  continuous_pi (fun j => continuous_const.mul (continuous_apply j))

end HBLSol212

open HBLSol212 in
theorem solution {n : ℕ} (φ φ₀ φinf : (Fin n → ℝ) → ℝ) (i : Fin n) :
    (∀ (r₀ : Fin n → ℝ) (d₀ : ℝ), IsHomogZero φ r₀ d₀ φ₀ →
      IsHomogZero (fun x => ∫ s in (0 : ℝ)..x i, φ (Function.update x i s)) r₀ (d₀ + r₀ i)
        (fun x => ∫ s in (0 : ℝ)..x i, φ₀ (Function.update x i s))) ∧
    (∀ (rinf : Fin n → ℝ) (dinf : ℝ), IsHomogInfty φ rinf dinf φinf →
      IsHomogInfty (fun x => ∫ s in (0 : ℝ)..x i, φ (Function.update x i s)) rinf
        (dinf + rinf i)
        (fun x => ∫ s in (0 : ℝ)..x i, φinf (Function.update x i s))) := by
  constructor
  · intro r d hφ
    obtain ⟨hr, hd, hφc, hφ₀c, hne, hlim⟩ := hφ
    refine ⟨hr, by linarith [hr i], cont_int i hφc, cont_int i hφ₀c, nontriv i hφ₀c hne, ?_⟩
    intro C hC h0C ε hε
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (hN_continuous hr).continuousOn
    have hR₁ : (1 : ℝ) ≤ max 1 B := le_max_left _ _
    set R₁ := max 1 B with hR₁def
    have hxR : ∀ x ∈ C, hN r x ≤ R₁ := fun x hx => by
      have := hB x hx; rw [Real.norm_eq_abs] at this
      exact le_trans (le_trans (le_abs_self _) this) (le_max_right _ _)
    obtain ⟨Ms, hMs⟩ := (isCompact_sphere hr).exists_bound_of_continuousOn hφ₀c.continuousOn
    obtain ⟨M₂, hM₂⟩ := (isCompact_ball hr R₁).exists_bound_of_continuousOn hφ₀c.continuousOn
    obtain ⟨la, hla, hla'⟩ := hlim _ (isCompact_sphere hr) (zero_not_mem_sphere hr) 1 one_pos
    have hR₁d : 0 ≤ R₁ ^ d := Real.rpow_nonneg (by linarith) _
    set M := (|Ms| + 1) * R₁ ^ d + |M₂| with hMdef
    have hM0 : 0 ≤ M := by positivity
    have hbound : ∀ l, 0 < l → l ≤ la / R₁ → ∀ z, hN r z ≤ R₁ →
        |φ (dil r l z) / l ^ d - φ₀ z| ≤ M := by
      intro l hl hll
      have hnz : ∀ z, z ≠ 0 → hN r z ≤ R₁ → |φ (dil r l z) / l ^ d - φ₀ z| ≤ M := by
        intro z hz hzR
        have hz2 : |φ₀ z| ≤ |M₂| := by
          have := hM₂ z hzR; rw [Real.norm_eq_abs] at this; exact le_trans this (le_abs_self _)
        obtain ⟨t, y, ht, htz, hy, rfl⟩ := repr' hr hz
        have hltl : l * t ≤ la := by
          calc l * t ≤ (la / R₁) * R₁ :=
                mul_le_mul hll (htz ▸ hzR) ht.le (div_pos hla (by linarith)).le
            _ = la := by field_simp
        have hly := hla' (l * t) (mul_pos hl ht) hltl y hy
        have e : φ (dil r l (dil r t y)) / l ^ d = t ^ d * (φ (dil r (l * t) y) / (l * t) ^ d) := by
          rw [dil_dil r hl.le ht.le, Real.mul_rpow hl.le ht.le]
          have : 0 < l ^ d := Real.rpow_pos_of_pos hl _
          have : 0 < t ^ d := Real.rpow_pos_of_pos ht _
          field_simp
        have hyb : |φ₀ y| ≤ |Ms| := by
          have := hMs y hy; rw [Real.norm_eq_abs] at this; exact le_trans this (le_abs_self _)
        have hq : |φ (dil r (l * t) y) / (l * t) ^ d| ≤ |Ms| + 1 := by
          have := abs_sub_abs_le_abs_sub (φ (dil r (l * t) y) / (l * t) ^ d) (φ₀ y); linarith
        have htd : t ^ d ≤ R₁ ^ d := Real.rpow_le_rpow ht.le (htz ▸ hzR) hd
        rw [e]
        calc |t ^ d * (φ (dil r (l * t) y) / (l * t) ^ d) - φ₀ (dil r t y)|
            ≤ |t ^ d * (φ (dil r (l * t) y) / (l * t) ^ d)| + |φ₀ (dil r t y)| :=
              abs_sub_le_add' _ _
          _ ≤ R₁ ^ d * (|Ms| + 1) + |M₂| := by
              refine add_le_add ?_ hz2
              rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
              exact mul_le_mul htd hq (abs_nonneg _) hR₁d
          _ = M := by rw [hMdef]; ring
      intro z hzR
      rcases eq_or_ne z 0 with rfl | hz
      · exact extend_zero_n hr i (f := fun z => φ (dil r l z) / l ^ d - φ₀ z)
          (((hφc.comp (dil_continuous r l)).div_const _).sub hφ₀c) (by linarith) hnz
      · exact hnz z hz hzR
    have ha : 0 < ε / (2 * (M + 1)) := by positivity
    set a := ε / (2 * (M + 1)) with hadef
    have hMa : M * a ≤ ε / 2 := by
      have h1 : (M + 1) * a = ε / 2 := by
        rw [hadef]; have : M + 1 ≠ 0 := by linarith
        field_simp
      nlinarith
    have hρ : 0 < a ^ (1 / r i) := Real.rpow_pos_of_pos ha _
    set S : Set (Fin n → ℝ) := {z | a ^ (1 / r i) ≤ hN r z ∧ hN r z ≤ R₁} with hSdef
    have hS : IsCompact S :=
      Metric.isCompact_of_isClosed_isBounded
        ((isClosed_le continuous_const (hN_continuous hr)).inter
          (isClosed_le (hN_continuous hr) continuous_const))
        ((isBounded_hN_le hr R₁).subset (fun x hx => hx.2))
    have h0S : (0 : Fin n → ℝ) ∉ S := by
      intro h0
      have := h0.1
      rw [(hN_eq_zero_iff hr 0).2 rfl] at this
      linarith
    have hRi : 0 < R₁ ^ (r i) := Real.rpow_pos_of_pos (by linarith) _
    have hε₁ : 0 < ε / (2 * (R₁ ^ (r i) + 1)) := by positivity
    obtain ⟨lb, hlb, hlb'⟩ := hlim S hS h0S _ hε₁
    refine ⟨min (la / R₁) lb, lt_min (div_pos hla (by linarith)) hlb, fun l hl hll x hx => ?_⟩
    show |(∫ s in (0 : ℝ)..(dil r l x) i, φ (Function.update (dil r l x) i s)) / l ^ (d + r i) -
      ∫ s in (0 : ℝ)..x i, φ₀ (Function.update x i s)| ≤ ε
    have hcu : Continuous (fun σ : ℝ => Function.update x i σ) :=
      continuous_const.update i continuous_id
    have hc1 : Continuous (fun σ => φ (dil r l (Function.update x i σ)) / l ^ d) :=
      (hφc.comp ((dil_continuous r l).comp hcu)).div_const _
    have hc2 : Continuous (fun σ => φ₀ (Function.update x i σ)) := hφ₀c.comp hcu
    rw [integral_scale φ i hl x d, ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _)]
    have hxi : |x i| ≤ R₁ ^ (r i) := abs_le_of_hN_le hr (hxR x hx) i
    refine le_trans (int_bound (h := fun σ => φ (dil r l (Function.update x i σ)) / l ^ d -
      φ₀ (Function.update x i σ)) (hc1.sub hc2) ha ?_ ?_ hε₁.le hM0) ?_
    · intro σ hσ
      exact hbound l hl (le_trans hll (min_le_left _ _)) _
        (le_trans (hN_update_le hr i x (abs_le_of_mem_uIcc hσ)) (hxR x hx))
    · intro σ hσ haσ
      have hz : Function.update x i σ ∈ S :=
        ⟨le_trans (Real.rpow_le_rpow ha.le haσ (one_div_pos.2 (hr i)).le) (hN_update_ge r i x σ),
          le_trans (hN_update_le hr i x (abs_le_of_mem_uIcc hσ)) (hxR x hx)⟩
      exact hlb' l hl (le_trans hll (min_le_right _ _)) _ hz
    · have h3 : ε / (2 * (R₁ ^ (r i) + 1)) * |x i| ≤ ε / 2 := by
        calc ε / (2 * (R₁ ^ (r i) + 1)) * |x i| ≤ ε / (2 * (R₁ ^ (r i) + 1)) * R₁ ^ (r i) :=
              mul_le_mul_of_nonneg_left hxi hε₁.le
          _ ≤ ε / (2 * (R₁ ^ (r i) + 1)) * (R₁ ^ (r i) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) hε₁.le
          _ = ε / 2 := by
              have : R₁ ^ (r i) + 1 ≠ 0 := by linarith
              field_simp
      linarith
  · intro r d hφ
    obtain ⟨hr, hd, hφc, hφ₀c, hne, hlim⟩ := hφ
    refine ⟨hr, by linarith [hr i], cont_int i hφc, cont_int i hφ₀c, nontriv i hφ₀c hne, ?_⟩
    intro C hC h0C ε hε
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn (hN_continuous hr).continuousOn
    have hR₁ : (1 : ℝ) ≤ max 1 B := le_max_left _ _
    set R₁ := max 1 B with hR₁def
    have hxR : ∀ x ∈ C, hN r x ≤ R₁ := fun x hx => by
      have := hB x hx; rw [Real.norm_eq_abs] at this
      exact le_trans (le_trans (le_abs_self _) this) (le_max_right _ _)
    obtain ⟨Ms, hMs⟩ := (isCompact_sphere hr).exists_bound_of_continuousOn hφ₀c.continuousOn
    obtain ⟨M₂, hM₂⟩ := (isCompact_ball hr R₁).exists_bound_of_continuousOn hφ₀c.continuousOn
    obtain ⟨la, hla, hla'⟩ := hlim _ (isCompact_sphere hr) (zero_not_mem_sphere hr) 1 one_pos
    obtain ⟨B₀, hB₀⟩ := (isCompact_ball hr la).exists_bound_of_continuousOn hφc.continuousOn
    have hR₁d : 0 ≤ R₁ ^ d := Real.rpow_nonneg (by linarith) _
    set M := (|Ms| + 1) * R₁ ^ d + |B₀| + |M₂| with hMdef
    have hM0 : 0 ≤ M := by positivity
    have hdiv : ∀ l : ℝ, 1 ≤ l → ∀ X : ℝ, |X / l ^ d| ≤ |X| := by
      intro l hl X
      have h1 : 1 ≤ l ^ d := Real.one_le_rpow hl hd
      rw [abs_div, abs_of_pos (show 0 < l ^ d by linarith)]
      exact div_le_self (abs_nonneg _) h1
    have hbound : ∀ l, max 1 la ≤ l → ∀ z, hN r z ≤ R₁ →
        |φ (dil r l z) / l ^ d - φinf z| ≤ M := by
      intro l hll z hzR
      have hl1 : 1 ≤ l := le_trans (le_max_left _ _) hll
      have hl : 0 < l := by linarith
      have hz2 : |φinf z| ≤ |M₂| := by
        have := hM₂ z hzR; rw [Real.norm_eq_abs] at this; exact le_trans this (le_abs_self _)
      have hmain : |φ (dil r l z) / l ^ d| ≤ (|Ms| + 1) * R₁ ^ d + |B₀| := by
        have hsmall : ∀ w, hN r w ≤ la → |φ w / l ^ d| ≤ |B₀| := by
          intro w hw
          have := hB₀ w hw; rw [Real.norm_eq_abs] at this
          exact le_trans (hdiv l hl1 _) (le_trans this (le_abs_self _))
        rcases eq_or_ne z 0 with rfl | hz
        · rw [dil_zero]
          have := hsmall 0 (by rw [(hN_eq_zero_iff hr 0).2 rfl]; exact hla.le)
          have : 0 ≤ (|Ms| + 1) * R₁ ^ d := by positivity
          linarith
        obtain ⟨t, y, ht, htz, hy, rfl⟩ := repr' hr hz
        rw [dil_dil r hl.le ht.le]
        rcases le_total la (l * t) with hlt | hlt
        · have hly := hla' (l * t) hlt y hy
          have e : φ (dil r (l * t) y) / l ^ d = t ^ d * (φ (dil r (l * t) y) / (l * t) ^ d) := by
            rw [Real.mul_rpow hl.le ht.le]
            have : 0 < l ^ d := Real.rpow_pos_of_pos hl _
            have : 0 < t ^ d := Real.rpow_pos_of_pos ht _
            field_simp
          have hyb : |φinf y| ≤ |Ms| := by
            have := hMs y hy; rw [Real.norm_eq_abs] at this; exact le_trans this (le_abs_self _)
          have hq : |φ (dil r (l * t) y) / (l * t) ^ d| ≤ |Ms| + 1 := by
            have := abs_sub_abs_le_abs_sub (φ (dil r (l * t) y) / (l * t) ^ d) (φinf y); linarith
          have htd : t ^ d ≤ R₁ ^ d := Real.rpow_le_rpow ht.le (htz ▸ hzR) hd
          rw [e, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht _)]
          have := mul_le_mul htd hq (abs_nonneg _) hR₁d
          linarith [abs_nonneg B₀]
        · have := hsmall (dil r (l * t) y) (by rw [hN_dil hr (mul_pos hl ht), hy, mul_one]; exact hlt)
          have : 0 ≤ (|Ms| + 1) * R₁ ^ d := by positivity
          linarith
      calc |φ (dil r l z) / l ^ d - φinf z| ≤ |φ (dil r l z) / l ^ d| + |φinf z| := abs_sub_le_add' _ _
        _ ≤ M := by rw [hMdef]; linarith
    have ha : 0 < ε / (2 * (M + 1)) := by positivity
    set a := ε / (2 * (M + 1)) with hadef
    have hMa : M * a ≤ ε / 2 := by
      have h1 : (M + 1) * a = ε / 2 := by
        rw [hadef]; have : M + 1 ≠ 0 := by linarith
        field_simp
      nlinarith
    set S : Set (Fin n → ℝ) := {z | a ^ (1 / r i) ≤ hN r z ∧ hN r z ≤ R₁} with hSdef
    have hρ : 0 < a ^ (1 / r i) := Real.rpow_pos_of_pos ha _
    have hS : IsCompact S :=
      Metric.isCompact_of_isClosed_isBounded
        ((isClosed_le continuous_const (hN_continuous hr)).inter
          (isClosed_le (hN_continuous hr) continuous_const))
        ((isBounded_hN_le hr R₁).subset (fun x hx => hx.2))
    have h0S : (0 : Fin n → ℝ) ∉ S := by
      intro h0
      have := h0.1
      rw [(hN_eq_zero_iff hr 0).2 rfl] at this
      linarith
    have hRi : 0 < R₁ ^ (r i) := Real.rpow_pos_of_pos (by linarith) _
    have hε₁ : 0 < ε / (2 * (R₁ ^ (r i) + 1)) := by positivity
    obtain ⟨lb, hlb, hlb'⟩ := hlim S hS h0S _ hε₁
    refine ⟨max (max 1 la) lb, lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _)),
      fun l hll x hx => ?_⟩
    have hl : 0 < l := lt_of_lt_of_le one_pos
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hll)
    show |(∫ s in (0 : ℝ)..(dil r l x) i, φ (Function.update (dil r l x) i s)) / l ^ (d + r i) -
      ∫ s in (0 : ℝ)..x i, φinf (Function.update x i s)| ≤ ε
    have hcu : Continuous (fun σ : ℝ => Function.update x i σ) :=
      continuous_const.update i continuous_id
    have hc1 : Continuous (fun σ => φ (dil r l (Function.update x i σ)) / l ^ d) :=
      (hφc.comp ((dil_continuous r l).comp hcu)).div_const _
    have hc2 : Continuous (fun σ => φinf (Function.update x i σ)) := hφ₀c.comp hcu
    rw [integral_scale φ i hl x d, ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
      (hc2.intervalIntegrable _ _)]
    have hxi : |x i| ≤ R₁ ^ (r i) := abs_le_of_hN_le hr (hxR x hx) i
    refine le_trans (int_bound (h := fun σ => φ (dil r l (Function.update x i σ)) / l ^ d -
      φinf (Function.update x i σ)) (hc1.sub hc2) ha ?_ ?_ hε₁.le hM0) ?_
    · intro σ hσ
      exact hbound l (le_trans (le_max_left _ _) hll) _
        (le_trans (hN_update_le hr i x (abs_le_of_mem_uIcc hσ)) (hxR x hx))
    · intro σ hσ haσ
      have hz : Function.update x i σ ∈ S :=
        ⟨le_trans (Real.rpow_le_rpow ha.le haσ (one_div_pos.2 (hr i)).le) (hN_update_ge r i x σ),
          le_trans (hN_update_le hr i x (abs_le_of_mem_uIcc hσ)) (hxR x hx)⟩
      exact hlb' l (le_trans (le_max_right _ _) hll) _ hz
    · have h3 : ε / (2 * (R₁ ^ (r i) + 1)) * |x i| ≤ ε / 2 := by
        calc ε / (2 * (R₁ ^ (r i) + 1)) * |x i| ≤ ε / (2 * (R₁ ^ (r i) + 1)) * R₁ ^ (r i) :=
              mul_le_mul_of_nonneg_left hxi hε₁.le
          _ ≤ ε / (2 * (R₁ ^ (r i) + 1)) * (R₁ ^ (r i) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) hε₁.le
          _ = ε / 2 := by
              have : R₁ ^ (r i) + 1 ≠ 0 := by linarith
              field_simp
      linarith
