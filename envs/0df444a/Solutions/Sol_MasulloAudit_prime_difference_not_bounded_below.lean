-- Prove2me | solution 1 for MasulloAudit.prime_difference_not_bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:15:43.10118+00:00
-- url     : https://prove2.me/submissions/442be044-f05b-47ee-a958-a5902ac3ac36

import Mathlib

set_option autoImplicit false

open MeasureTheory Set

namespace A1PrimeDiff

local notation "μw" s => (volume.withDensity fun u : ℝ => ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2)))

lemma weight_measurable (s : ℝ) :
    Measurable fun u : ℝ => ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2)) := by
  fun_prop

lemma weight_mono {s : ℝ} (hs : 0 ≤ s) {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) :
    (1 + a ^ 2) ^ (s / 2) ≤ (1 + b ^ 2) ^ (s / 2) :=
  Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

lemma measure_le (s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) {W : ℝ}
    (h : ∀ u ∈ A, (1 + u ^ 2) ^ (s / 2) ≤ W) :
    (μw s) A ≤ ENNReal.ofReal W * volume A := by
  rw [withDensity_apply _ hA]
  calc ∫⁻ u in A, ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2))
      ≤ ∫⁻ _ in A, ENNReal.ofReal W :=
        setLIntegral_mono' hA fun u hu => ENNReal.ofReal_le_ofReal (h u hu)
    _ = ENNReal.ofReal W * volume A := setLIntegral_const _ _

lemma le_measure (s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) {W : ℝ}
    (h : ∀ u ∈ A, W ≤ (1 + u ^ 2) ^ (s / 2)) :
    ENNReal.ofReal W * volume A ≤ (μw s) A := by
  rw [withDensity_apply _ hA]
  calc ENNReal.ofReal W * volume A = ∫⁻ _ in A, ENNReal.ofReal W := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ u in A, ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2)) :=
        setLIntegral_mono' hA fun u hu => ENNReal.ofReal_le_ofReal (h u hu)

/-- Upper bound for the weighted measure of the two boundary layers. -/
lemma boundary_le {s : ℝ} (hs : 0 ≤ s) {p T : ℝ} (hp : 0 < p) (hpT : p ≤ T) :
    (μw s) (Icc (-p) p ∪ Icc (T - p) (T + p)) ≤
      ENNReal.ofReal ((16 : ℝ) ^ (s / 2) * (1 + (T / 2) ^ 2) ^ (s / 2) * (4 * p)) := by
  have hmeas : MeasurableSet (Icc (-p) p ∪ Icc (T - p) (T + p)) :=
    measurableSet_Icc.union measurableSet_Icc
  have hW : ∀ u ∈ Icc (-p) p ∪ Icc (T - p) (T + p),
      (1 + u ^ 2) ^ (s / 2) ≤ (16 : ℝ) ^ (s / 2) * (1 + (T / 2) ^ 2) ^ (s / 2) := by
    intro u hu
    have hu2 : u ^ 2 ≤ (T + p) ^ 2 := by
      rcases hu with hu | hu
      · exact sq_le_sq' (by linarith [hu.1]) (by linarith [hu.2])
      · exact sq_le_sq' (by linarith [hu.1]) hu.2
    have h1 : (1 + u ^ 2) ^ (s / 2) ≤ (16 * (1 + (T / 2) ^ 2)) ^ (s / 2) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      have h2 : (T + p) ^ 2 ≤ (2 * T) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      nlinarith
    rwa [Real.mul_rpow (by norm_num) (by positivity)] at h1
  have hvol : volume (Icc (-p) p ∪ Icc (T - p) (T + p)) ≤ ENNReal.ofReal (4 * p) := by
    calc volume (Icc (-p) p ∪ Icc (T - p) (T + p))
        ≤ volume (Icc (-p) p) + volume (Icc (T - p) (T + p)) := measure_union_le _ _
      _ = ENNReal.ofReal (2 * p) + ENNReal.ofReal (2 * p) := by
          rw [Real.volume_Icc, Real.volume_Icc]
          congr 2 <;> ring
      _ = ENNReal.ofReal (4 * p) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
  calc (μw s) (Icc (-p) p ∪ Icc (T - p) (T + p))
      ≤ ENNReal.ofReal ((16 : ℝ) ^ (s / 2) * (1 + (T / 2) ^ 2) ^ (s / 2)) *
          volume (Icc (-p) p ∪ Icc (T - p) (T + p)) := measure_le s hmeas hW
    _ ≤ ENNReal.ofReal ((16 : ℝ) ^ (s / 2) * (1 + (T / 2) ^ 2) ^ (s / 2)) *
          ENNReal.ofReal (4 * p) := by gcongr
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

/-- Lower bound for the weighted measure of the bulk interval. -/
lemma bulk_ge {s : ℝ} (hs : 0 ≤ s) {T : ℝ} (hT : 0 < T) :
    ENNReal.ofReal ((1 + (T / 2) ^ 2) ^ (s / 2) * (T / 2)) ≤ (μw s) (Ioc 0 T) := by
  have hsub : Ioc (T / 2) T ⊆ Ioc 0 T := Ioc_subset_Ioc (by linarith) le_rfl
  have hW : ∀ u ∈ Ioc (T / 2) T, (1 + (T / 2) ^ 2) ^ (s / 2) ≤ (1 + u ^ 2) ^ (s / 2) := by
    intro u hu
    exact weight_mono hs (pow_le_pow_left₀ (by linarith) hu.1.le 2)
  calc ENNReal.ofReal ((1 + (T / 2) ^ 2) ^ (s / 2) * (T / 2))
      = ENNReal.ofReal ((1 + (T / 2) ^ 2) ^ (s / 2)) * volume (Ioc (T / 2) T) := by
        rw [Real.volume_Ioc, ENNReal.ofReal_mul (by positivity)]
        congr 2; ring
    _ ≤ (μw s) (Ioc (T / 2) T) := le_measure s measurableSet_Ioc hW
    _ ≤ (μw s) (Ioc 0 T) := measure_mono hsub

lemma bulk_ne_top (s : ℝ) (hs : 0 ≤ s) (T : ℝ) : (μw s) (Ioc 0 T) ≠ ⊤ := by
  have hW : ∀ u ∈ Ioc (0 : ℝ) T, (1 + u ^ 2) ^ (s / 2) ≤ (1 + T ^ 2) ^ (s / 2) := by
    intro u hu
    exact weight_mono hs (pow_le_pow_left₀ hu.1.le hu.2 2)
  refine ne_top_of_le_ne_top ?_ (measure_le s measurableSet_Ioc hW)
  rw [Real.volume_Ioc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The difference of the indicator of `(0, T]` and its translate by `ℓ` is dominated by the
indicator of the two boundary layers. -/
lemma diff_indicator_le {ℓ T : ℝ} (u : ℝ) :
    ‖(Ioc 0 T).indicator (fun _ => (1 : ℂ)) u - (Ioc 0 T).indicator (fun _ => (1 : ℂ)) (u - ℓ)‖ ≤
      ‖(Icc (-|ℓ|) |ℓ| ∪ Icc (T - |ℓ|) (T + |ℓ|)).indicator (fun _ => (1 : ℂ)) u‖ := by
  have h1 : ℓ ≤ |ℓ| := le_abs_self ℓ
  have h2 : -|ℓ| ≤ ℓ := neg_abs_le ℓ
  by_cases hu : u ∈ Icc (-|ℓ|) |ℓ| ∪ Icc (T - |ℓ|) (T + |ℓ|)
  · rw [indicator_of_mem hu]
    by_cases ha : u ∈ Ioc 0 T <;> by_cases hb : u - ℓ ∈ Ioc 0 T <;> simp [ha, hb]
  · rw [indicator_of_notMem hu]
    have hiff : u ∈ Ioc 0 T ↔ u - ℓ ∈ Ioc 0 T := by
      simp only [mem_union, mem_Icc, mem_Ioc, not_or, not_and_or, not_le] at hu ⊢
      obtain ⟨ha | ha, hb | hb⟩ := hu
      · constructor <;> rintro ⟨h3, h4⟩ <;> constructor <;> linarith
      · constructor <;> rintro ⟨h3, h4⟩ <;> constructor <;> linarith
      · constructor <;> rintro ⟨h3, h4⟩ <;> constructor <;> linarith
      · constructor <;> rintro ⟨h3, h4⟩ <;> constructor <;> linarith
    by_cases ha : u ∈ Ioc 0 T
    · rw [indicator_of_mem ha, indicator_of_mem (hiff.mp ha)]; simp
    · rw [indicator_of_notMem ha, indicator_of_notMem (fun h => ha (hiff.mpr h))]; simp

/-- Core estimate: for every `c > 0` there is `T > 0` such that the weighted measure of the
boundary layers is smaller than `c²` times the weighted measure of `(0, T]`. -/
lemma exists_ratio {s : ℝ} (hs : 0 ≤ s) {p : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧
      (μw s) (Icc (-p) p ∪ Icc (T - p) (T + p)) < ENNReal.ofReal (c ^ 2) * (μw s) (Ioc 0 T) := by
  set K : ℝ := (16 : ℝ) ^ (s / 2) with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (8 * K / c ^ 2)
  have hNpos : (0 : ℝ) < N := lt_trans (by positivity) hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
    rintro rfl; simp at hNpos)
  have h8 : 8 * K < c ^ 2 * N := by
    have := (div_lt_iff₀ (by positivity)).mp hN
    linarith
  have hT : 0 < (N : ℝ) * p := by positivity
  have hpT : p ≤ (N : ℝ) * p := by nlinarith
  refine ⟨N * p, hT, ?_⟩
  set w0 : ℝ := (1 + ((N : ℝ) * p / 2) ^ 2) ^ (s / 2) with hw0
  have hw0pos : 0 < w0 := by positivity
  calc (μw s) (Icc (-p) p ∪ Icc (N * p - p) (N * p + p))
      ≤ ENNReal.ofReal (K * w0 * (4 * p)) := boundary_le hs hp hpT
    _ < ENNReal.ofReal (c ^ 2 * (w0 * (N * p / 2))) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        nlinarith [mul_pos (mul_pos hw0pos hp) (sub_pos.mpr h8)]
    _ = ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (w0 * (N * p / 2)) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal (c ^ 2) * (μw s) (Ioc 0 (N * p)) := by
        gcongr
        exact bulk_ge hs hT

/-- Function-level statement with the explicit witness `1_{(0, T]}`. -/
lemma exists_witness {s : ℝ} (hs : 0 ≤ s) {ℓ : ℝ} (hℓ : ℓ ≠ 0) {c : ℝ} (hc : 0 < c) :
    ∃ T : ℝ, 0 < T ∧
      eLpNorm (fun u => (Ioc 0 T).indicator (fun _ => (1 : ℂ)) u -
          (Ioc 0 T).indicator (fun _ => (1 : ℂ)) (u - ℓ)) 2 (μw s) <
        ENNReal.ofReal c * eLpNorm ((Ioc 0 T).indicator (fun _ => (1 : ℂ))) 2 (μw s) := by
  obtain ⟨T, hT, hlt⟩ := exists_ratio hs (abs_pos.mpr hℓ) hc
  refine ⟨T, hT, ?_⟩
  have hexp : (1 / (2 : ENNReal).toReal) = (1 / 2 : ℝ) := by norm_num
  have hA : MeasurableSet (Icc (-|ℓ|) |ℓ| ∪ Icc (T - |ℓ|) (T + |ℓ|)) :=
    measurableSet_Icc.union measurableSet_Icc
  have hD : eLpNorm (fun u => (Ioc 0 T).indicator (fun _ => (1 : ℂ)) u -
          (Ioc 0 T).indicator (fun _ => (1 : ℂ)) (u - ℓ)) 2 (μw s) ≤
        (μw s) (Icc (-|ℓ|) |ℓ| ∪ Icc (T - |ℓ|) (T + |ℓ|)) ^ (1 / 2 : ℝ) := by
    refine (eLpNorm_mono (diff_indicator_le (ℓ := ℓ) (T := T))).trans_eq ?_
    rw [eLpNorm_indicator_const hA (by norm_num) (by norm_num), hexp, enorm_one, one_mul]
  have hF : eLpNorm ((Ioc 0 T).indicator (fun _ => (1 : ℂ))) 2 (μw s) =
      (μw s) (Ioc 0 T) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_indicator_const measurableSet_Ioc (by norm_num) (by norm_num), hexp, enorm_one,
      one_mul]
  have hcc : ENNReal.ofReal c = ENNReal.ofReal (c ^ 2) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
      Real.sqrt_sq hc.le]
  rw [hF, hcc, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact hD.trans_lt (ENNReal.rpow_lt_rpow hlt (by norm_num))

end A1PrimeDiff

open A1PrimeDiff in
theorem solution (s ℓ c : ℝ) (hs : 0 ≤ s) (hℓ : ℓ ≠ 0) (hc : 0 < c) :
    ∃ f : ℝ → ℂ,
      MemLp f 2 (volume.withDensity fun u : ℝ => ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2))) ∧
      eLpNorm (fun u => f u - f (u - ℓ)) 2
          (volume.withDensity fun u : ℝ => ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2))) <
        ENNReal.ofReal c *
          eLpNorm f 2 (volume.withDensity fun u : ℝ => ENNReal.ofReal ((1 + u ^ 2) ^ (s / 2))) := by
  obtain ⟨T, _, hlt⟩ := exists_witness hs hℓ hc
  exact ⟨(Ioc 0 T).indicator (fun _ => (1 : ℂ)),
    memLp_indicator_const 2 measurableSet_Ioc 1 (Or.inr (bulk_ne_top s hs T)), hlt⟩
