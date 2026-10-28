-- Prove2me | solution 1 for MultivarScores.L2Rule.lpm_injective
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:08:04.98616+00:00
-- url     : https://prove2.me/submissions/068459e9-0a2e-4ad6-907d-60c4bae9121a

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

open MeasureTheory MultivarScores.L2Rule Set Filter Topology

namespace LPMAux

/-- One-dimensional LPM kernel `φ_k(t) = t^k / k! · 𝟙{t ≥ 0}`. -/
noncomputable def φ (k : ℕ) (t : ℝ) : ℝ := t ^ k / (k.factorial : ℝ) * if 0 ≤ t then 1 else 0

lemma φ_of_neg {k : ℕ} {t : ℝ} (ht : t < 0) : φ k t = 0 := by
  simp [φ, not_le.2 ht]

lemma φ_of_nonneg {k : ℕ} {t : ℝ} (ht : 0 ≤ t) : φ k t = t ^ k / (k.factorial : ℝ) := by
  simp [φ, ht]

lemma φ_nonneg (k : ℕ) (t : ℝ) : 0 ≤ φ k t := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [φ_of_neg ht]
  · rw [φ_of_nonneg ht]; positivity

lemma φ_mono (k : ℕ) {a b : ℝ} (hab : a ≤ b) : φ k a ≤ φ k b := by
  rcases lt_or_ge a 0 with ha | ha
  · rw [φ_of_neg ha]; exact φ_nonneg k b
  · rw [φ_of_nonneg ha, φ_of_nonneg (ha.trans hab)]
    gcongr

lemma φ_meas (k : ℕ) : Measurable (φ k) := by
  unfold φ
  refine ((measurable_id.pow_const k).div_const _).mul ?_
  exact Measurable.ite (p := fun t : ℝ => 0 ≤ t) measurableSet_Ici measurable_const
    measurable_const

lemma φ_le_succ (k : ℕ) (t : ℝ) : φ k t ≤ (k + 1 : ℝ) * φ (k + 1) (t + 1) := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [φ_of_neg ht]; exact mul_nonneg (by positivity) (φ_nonneg _ _)
  · rw [φ_of_nonneg ht, φ_of_nonneg (by linarith), Nat.factorial_succ]
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have h1 : t ^ k ≤ (t + 1) ^ (k + 1) :=
      calc t ^ k ≤ (t + 1) ^ k := by gcongr; linarith
        _ ≤ (t + 1) ^ (k + 1) := pow_le_pow_right₀ (by linarith) (Nat.le_succ k)
    rw [Nat.cast_mul, Nat.cast_succ]
    rw [show ((k : ℝ) + 1) * ((t + 1) ^ (k + 1) / (((k : ℝ) + 1) * k.factorial)) =
      (t + 1) ^ (k + 1) / k.factorial by field_simp]
    exact div_le_div_of_nonneg_right h1 hk.le

lemma pow_succ_sub_bounds (k : ℕ) {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) :
    (k + 1 : ℝ) * y ^ k * (x - y) ≤ x ^ (k + 1) - y ^ (k + 1) ∧
      x ^ (k + 1) - y ^ (k + 1) ≤ (k + 1 : ℝ) * x ^ k * (x - y) := by
  rw [← geom_sum₂_mul x y (k + 1)]
  have hx : 0 ≤ x := hy.trans hxy
  have hd : 0 ≤ x - y := by linarith
  have hlo : ∀ i ∈ Finset.range (k + 1), y ^ k ≤ x ^ i * y ^ (k + 1 - 1 - i) := by
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    calc y ^ k = y ^ i * y ^ (k + 1 - 1 - i) := by
            rw [← pow_add]; congr 1; omega
      _ ≤ x ^ i * y ^ (k + 1 - 1 - i) := by gcongr
  have hhi : ∀ i ∈ Finset.range (k + 1), x ^ i * y ^ (k + 1 - 1 - i) ≤ x ^ k := by
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    calc x ^ i * y ^ (k + 1 - 1 - i) ≤ x ^ i * x ^ (k + 1 - 1 - i) := by gcongr
      _ = x ^ k := by rw [← pow_add]; congr 1; omega
  have s1 := Finset.card_nsmul_le_sum _ _ _ hlo
  have s2 := Finset.sum_le_card_nsmul _ _ _ hhi
  simp only [Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at s1 s2
  constructor
  · exact mul_le_mul_of_nonneg_right s1 hd
  · exact mul_le_mul_of_nonneg_right s2 hd

/-- Slope sandwich: `δ φ_k(t) ≤ φ_{k+1}(t+δ) − φ_{k+1}(t) ≤ δ φ_k(t+δ)` for `δ ≥ 0`. -/
lemma slope_bounds (k : ℕ) (t : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    δ * φ k t ≤ φ (k + 1) (t + δ) - φ (k + 1) t ∧
      φ (k + 1) (t + δ) - φ (k + 1) t ≤ δ * φ k (t + δ) := by
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hfs : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rcases le_or_gt 0 t with ht | ht
  · have ht' : 0 ≤ t + δ := by linarith
    rw [φ_of_nonneg ht, φ_of_nonneg ht', φ_of_nonneg ht, φ_of_nonneg ht', hfs]
    obtain ⟨b1, b2⟩ := pow_succ_sub_bounds k ht (by linarith : t ≤ t + δ)
    have e : t + δ - t = δ := by ring
    rw [e] at b1 b2
    constructor
    · rw [← sub_div, le_div_iff₀ (by positivity)]
      have : δ * (t ^ k / k.factorial) * (((k : ℝ) + 1) * k.factorial) =
          ((k : ℝ) + 1) * t ^ k * δ := by field_simp
      linarith
    · rw [← sub_div, div_le_iff₀ (by positivity)]
      have : δ * ((t + δ) ^ k / k.factorial) * (((k : ℝ) + 1) * k.factorial) =
          ((k : ℝ) + 1) * (t + δ) ^ k * δ := by field_simp
      linarith
  · rw [φ_of_neg ht, φ_of_neg ht, mul_zero, sub_zero]
    rcases lt_or_ge (t + δ) 0 with ht' | ht'
    · rw [φ_of_neg ht', φ_of_neg ht', mul_zero]; exact ⟨le_refl _, le_refl _⟩
    · refine ⟨φ_nonneg _ _, ?_⟩
      rw [φ_of_nonneg ht', φ_of_nonneg ht', hfs]
      have hle : t + δ ≤ δ := by linarith
      have h1 : (t + δ) ^ (k + 1) ≤ δ * (t + δ) ^ k := by
        rw [pow_succ']; exact mul_le_mul_of_nonneg_right hle (pow_nonneg ht' _)
      have h2 : (t + δ) ^ (k + 1) / (((k : ℝ) + 1) * k.factorial) ≤
          (t + δ) ^ (k + 1) / k.factorial := by
        apply div_le_div_of_nonneg_left (pow_nonneg ht' _) hk
        nlinarith
      calc (t + δ) ^ (k + 1) / (((k : ℝ) + 1) * k.factorial)
          ≤ (t + δ) ^ (k + 1) / k.factorial := h2
        _ ≤ δ * (t + δ) ^ k / k.factorial := div_le_div_of_nonneg_right h1 hk.le
        _ = δ * ((t + δ) ^ k / k.factorial) := by ring

/-- Right-continuity of `φ_k` along `t + 1/(n+1)`. -/
lemma φ_right_tendsto (k : ℕ) (t : ℝ) :
    Tendsto (fun n : ℕ => φ k (t + 1 / ((n : ℝ) + 1))) atTop (𝓝 (φ k t)) := by
  have hδ : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 (t + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at hδ
  rcases le_or_gt 0 t with ht | ht
  · have hev : ∀ n : ℕ, φ k (t + 1 / ((n : ℝ) + 1)) = (t + 1 / ((n : ℝ) + 1)) ^ k / k.factorial :=
      fun n => φ_of_nonneg (by positivity)
    simp_rw [hev, φ_of_nonneg ht]
    exact (hδ.pow k).div_const _
  · have hev : ∀ᶠ n : ℕ in atTop, φ k (t + 1 / ((n : ℝ) + 1)) = 0 := by
      have := hδ.eventually (gt_mem_nhds ht)
      filter_upwards [this] with n hn using φ_of_neg hn
    rw [φ_of_neg ht]
    exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

/-- Slope of `φ_{k+1}` converges to `φ_k` from the right. -/
lemma slope_tendsto (k : ℕ) (t : ℝ) :
    Tendsto (fun n : ℕ => (φ (k + 1) (t + 1 / ((n : ℝ) + 1)) - φ (k + 1) t) / (1 / ((n : ℝ) + 1)))
      atTop (𝓝 (φ k t)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (φ_right_tendsto k t)
    (fun n => ?_) (fun n => ?_)
  · have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hδ, mul_comm]; exact (slope_bounds k t hδ.le).1
  · have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [div_le_iff₀ hδ, mul_comm]; exact (slope_bounds k t hδ.le).2

lemma slope_nonneg_le (k : ℕ) (t : ℝ) (n : ℕ) :
    0 ≤ (φ (k + 1) (t + 1 / ((n : ℝ) + 1)) - φ (k + 1) t) / (1 / ((n : ℝ) + 1)) ∧
    (φ (k + 1) (t + 1 / ((n : ℝ) + 1)) - φ (k + 1) t) / (1 / ((n : ℝ) + 1)) ≤
      (k + 1 : ℝ) * φ (k + 1) (t + 2) := by
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hδ1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  obtain ⟨b1, b2⟩ := slope_bounds k t hδ.le
  constructor
  · apply div_nonneg _ hδ.le
    linarith [mul_nonneg hδ.le (φ_nonneg k t)]
  · rw [div_le_iff₀ hδ]
    calc φ (k + 1) (t + 1 / ((n : ℝ) + 1)) - φ (k + 1) t
        ≤ 1 / ((n : ℝ) + 1) * φ k (t + 1 / ((n : ℝ) + 1)) := b2
      _ ≤ 1 / ((n : ℝ) + 1) * φ k (t + 1) := by
          gcongr; exact φ_mono k (by linarith)
      _ ≤ 1 / ((n : ℝ) + 1) * ((k + 1 : ℝ) * φ (k + 1) (t + 1 + 1)) := by
          gcongr; exact φ_le_succ k (t + 1)
      _ = (k + 1 : ℝ) * φ (k + 1) (t + 2) * (1 / ((n : ℝ) + 1)) := by ring_nf

/-- Multivariate LPM kernel `K_k(z, s) = ∏ⱼ φ_k(zⱼ − sⱼ)`. -/
noncomputable def K {d : ℕ} (k : ℕ) (z s : E d) : ℝ := ∏ j, φ k (z j - s j)

lemma K_eq {d : ℕ} (k : ℕ) (z s : E d) :
    (∏ j, ((z j - s j) ^ k / (k.factorial : ℝ) * if s j ≤ z j then 1 else 0)) = K k z s := by
  unfold K φ
  refine Finset.prod_congr rfl fun j _ => ?_
  simp [sub_nonneg]

lemma K_nonneg {d : ℕ} (k : ℕ) (z s : E d) : 0 ≤ K k z s :=
  Finset.prod_nonneg fun j _ => φ_nonneg _ _

lemma K_meas {d : ℕ} (k : ℕ) (z : E d) : Measurable (K k z) := by
  unfold K
  refine Finset.measurable_prod _ fun j _ => ?_
  exact (φ_meas k).comp (measurable_const.sub (measurable_pi_apply j))

lemma K_le_succ {d : ℕ} (k : ℕ) (z s : E d) :
    K k z s ≤ (k + 1 : ℝ) ^ d * K (k + 1) (fun j => z j + 1) s := by
  unfold K
  calc ∏ j, φ k (z j - s j) ≤ ∏ j : Fin d, ((k + 1 : ℝ) * φ (k + 1) (z j + 1 - s j)) := by
        refine Finset.prod_le_prod (fun j _ => φ_nonneg _ _) fun j _ => ?_
        have := φ_le_succ k (z j - s j)
        rwa [show z j - s j + 1 = z j + 1 - s j by ring] at this
    _ = (k + 1 : ℝ) ^ d * ∏ j, φ (k + 1) (z j + 1 - s j) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Expansion of the product of differences as a signed sum of shifted kernels. -/
lemma prod_diff_expand {d : ℕ} (k : ℕ) (z s : E d) (δ : ℝ) :
    ∏ j, (φ k (z j + δ - s j) - φ k (z j - s j)) =
      ∑ x : Fin d → Bool, (∏ j, if x j then (1 : ℝ) else -1) *
        K k (fun j => if x j then z j + δ else z j) s := by
  have h1 : ∀ j, φ k (z j + δ - s j) - φ k (z j - s j) =
      ∑ b : Bool, (if b then φ k (z j + δ - s j) else -φ k (z j - s j)) := by
    intro j; simp [Fintype.sum_bool, sub_eq_add_neg]
  simp_rw [h1]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold K
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hx : x j <;> simp [hx]

lemma integral_prod_diff {d : ℕ} (k : ℕ) (P : Measure (E d))
    (hP : ∀ z, Integrable (K k z) P) (z : E d) (δ : ℝ) :
    Integrable (fun s => ∏ j, (φ k (z j + δ - s j) - φ k (z j - s j))) P ∧
    ∫ s, ∏ j, (φ k (z j + δ - s j) - φ k (z j - s j)) ∂P =
      ∑ x : Fin d → Bool, (∏ j, if x j then (1 : ℝ) else -1) *
        ∫ s, K k (fun j => if x j then z j + δ else z j) s ∂P := by
  simp_rw [prod_diff_expand]
  have hi : ∀ x ∈ (Finset.univ : Finset (Fin d → Bool)), Integrable (fun s =>
      (∏ j, if x j then (1 : ℝ) else -1) * K k (fun j => if x j then z j + δ else z j) s) P :=
    fun x _ => (hP _).const_mul _
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  simp_rw [integral_const_mul]

/-- One induction step: equality of order-`k+1` LPMs gives equality of order-`k` LPMs. -/
lemma step {d : ℕ} (k : ℕ) (P Q : Measure (E d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q]
    (hP : ∀ z, Integrable (K (k + 1) z) P) (hQ : ∀ z, Integrable (K (k + 1) z) Q)
    (heq : ∀ z, ∫ s, K (k + 1) z s ∂P = ∫ s, K (k + 1) z s ∂Q) :
    (∀ z, Integrable (K k z) P) ∧ (∀ z, Integrable (K k z) Q) ∧
      (∀ z, ∫ s, K k z s ∂P = ∫ s, K k z s ∂Q) := by
  have hint : ∀ (μ : Measure (E d)), (∀ z, Integrable (K (k + 1) z) μ) →
      ∀ z, Integrable (K k z) μ := by
    intro μ hμ z
    refine ((hμ (fun j => z j + 1)).const_mul ((k + 1 : ℝ) ^ d)).mono'
      (K_meas k z).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (K_nonneg _ _ _)]
    exact K_le_succ k z s
  refine ⟨hint P hP, hint Q hQ, fun z => ?_⟩
  -- difference quotients
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let D : ℕ → E d → ℝ := fun n s =>
    ∏ j, ((φ (k + 1) (z j - s j + δ n) - φ (k + 1) (z j - s j)) / δ n)
  have hD : ∀ n s, D n s =
      (δ n)⁻¹ ^ d * ∏ j, (φ (k + 1) (z j + δ n - s j) - φ (k + 1) (z j - s j)) := by
    intro n s
    simp only [D]
    rw [show (δ n)⁻¹ ^ d = ∏ _j : Fin d, (δ n)⁻¹ by simp, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [show z j + δ n - s j = z j - s j + δ n by ring, div_eq_inv_mul]
  have hDint : ∀ (μ : Measure (E d)), (∀ z, Integrable (K (k + 1) z) μ) → ∀ n,
      ∫ s, D n s ∂μ = (δ n)⁻¹ ^ d * ∑ x : Fin d → Bool, (∏ j, if x j then (1 : ℝ) else -1) *
        ∫ s, K (k + 1) (fun j => if x j then z j + δ n else z j) s ∂μ := by
    intro μ hμ n
    simp_rw [hD]
    rw [integral_const_mul, (integral_prod_diff (k + 1) μ hμ z (δ n)).2]
  have hDeq : ∀ n, ∫ s, D n s ∂P = ∫ s, D n s ∂Q := by
    intro n
    rw [hDint P hP, hDint Q hQ]
    simp_rw [heq]
  have hlim : ∀ (μ : Measure (E d)), (∀ z, Integrable (K (k + 1) z) μ) →
      Tendsto (fun n => ∫ s, D n s ∂μ) atTop (𝓝 (∫ s, K k z s ∂μ)) := by
    intro μ hμ
    refine tendsto_integral_of_dominated_convergence
      (fun s => (k + 1 : ℝ) ^ d * K (k + 1) (fun j => z j + 2) s) (fun n => ?_)
      ((hμ _).const_mul _) (fun n => Eventually.of_forall fun s => ?_)
      (Eventually.of_forall fun s => ?_)
    · simp only [D]
      refine (Finset.measurable_prod _ fun j _ => ?_).aestronglyMeasurable
      have hm : Measurable (fun s : E d => z j - s j) :=
        measurable_const.sub (measurable_pi_apply j)
      exact ((((φ_meas (k + 1)).comp (hm.add_const _)).sub
        ((φ_meas (k + 1)).comp hm)).div_const _)
    · simp only [D]
      rw [Real.norm_eq_abs, abs_of_nonneg
        (Finset.prod_nonneg fun j _ => (slope_nonneg_le k (z j - s j) n).1)]
      unfold K
      calc ∏ j, ((φ (k + 1) (z j - s j + δ n) - φ (k + 1) (z j - s j)) / δ n)
          ≤ ∏ j : Fin d, ((k + 1 : ℝ) * φ (k + 1) (z j + 2 - s j)) := by
            refine Finset.prod_le_prod (fun j _ => (slope_nonneg_le k (z j - s j) n).1)
              fun j _ => ?_
            have := (slope_nonneg_le k (z j - s j) n).2
            rwa [show z j - s j + 2 = z j + 2 - s j by ring] at this
        _ = (k + 1 : ℝ) ^ d * ∏ j, φ (k + 1) (z j + 2 - s j) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · simp only [D]
      unfold K
      exact tendsto_finsetProd _ fun j _ => slope_tendsto k (z j - s j)
  have h1 := hlim P hP
  have h2 := hlim Q hQ
  simp_rw [hDeq] at h1
  exact tendsto_nhds_unique h1 h2


lemma mvs_isCountablySpanning_Iic : IsCountablySpanning (range (Iic : ℝ → Set ℝ)) := by
  refine ⟨fun n : ℕ => Iic (n : ℝ), fun n => ⟨n, rfl⟩, ?_⟩
  ext x
  simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
  exact ⟨⌈x⌉₊, Nat.le_ceil x⟩

lemma mvs_ext_of_Iic {d : ℕ} (P Q : Measure (E d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (h : ∀ z, P (Iic z) = Q (Iic z)) : P = Q := by
  let C : Set (Set (E d)) := pi univ '' pi univ (fun _ : Fin d => range (Iic : ℝ → Set ℝ))
  have hgen : (inferInstance : MeasurableSpace (E d)) = MeasurableSpace.generateFrom C := by
    refine (generateFrom_eq_pi (fun _ => ?_) (fun _ => mvs_isCountablySpanning_Iic)).symm
    rw [← borel_eq_generateFrom_Iic]; exact BorelSpace.measurable_eq.symm
  refine ext_of_generate_finite C hgen (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ (by simp)
  rintro s ⟨t, ht, rfl⟩
  have : ∀ i, ∃ a, t i = Iic a := fun i => by
    obtain ⟨a, ha⟩ := ht i (mem_univ i); exact ⟨a, ha.symm⟩
  choose a ha using this
  have : (pi univ t) = Iic a := by
    rw [← pi_univ_Iic]; congr 1; funext i; exact ha i
  rw [this]; exact h a

lemma K_zero {d : ℕ} (z s : E d) : K 0 z s = (Iic z).indicator 1 s := by
  unfold K
  by_cases hs : s ≤ z
  · rw [indicator_of_mem (show s ∈ Iic z from hs)]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [φ_of_nonneg (sub_nonneg.2 (hs j))]; simp
  · rw [indicator_of_notMem (show s ∉ Iic z from hs)]
    have : ∃ j, z j < s j := by
      by_contra hc; push Not at hc; exact hs fun j => hc j
    obtain ⟨j, hj⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ j) (φ_of_neg (by linarith))

lemma main {d : ℕ} (P Q : Measure (E d)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ∀ k : ℕ, (∀ z, Integrable (K k z) P) → (∀ z, Integrable (K k z) Q) →
      (∀ z, ∫ s, K k z s ∂P = ∫ s, K k z s ∂Q) → P = Q := by
  intro k
  induction k with
  | zero =>
    intro _ _ heq
    refine mvs_ext_of_Iic P Q fun z => ?_
    have := heq z
    simp_rw [K_zero] at this
    rw [integral_indicator_one measurableSet_Iic, integral_indicator_one measurableSet_Iic,
      measureReal_def, measureReal_def] at this
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 this
  | succ k ih =>
    intro hP hQ heq
    obtain ⟨a, b, c⟩ := step k P Q hP hQ heq
    exact ih a b c

end LPMAux

open LPMAux in
theorem solution {d : ℕ} (k : ℕ) (PX PY : Measure (E d))
    [IsProbabilityMeasure PX] [IsProbabilityMeasure PY]
    (hX : ∀ z : E d, Integrable
      (fun s : E d => ∏ j, ((z j - s j) ^ k / (k.factorial : ℝ) * if s j ≤ z j then 1 else 0)) PX)
    (hY : ∀ z : E d, Integrable
      (fun s : E d => ∏ j, ((z j - s j) ^ k / (k.factorial : ℝ) * if s j ≤ z j then 1 else 0)) PY)
    (heq : ∀ z, lpm k PX z = lpm k PY z) :
    PX = PY := by
  simp_rw [K_eq] at hX hY
  refine main PX PY k (fun z => hX z) (fun z => hY z) fun z => ?_
  have := heq z
  unfold lpm at this
  simp_rw [K_eq] at this
  exact this
