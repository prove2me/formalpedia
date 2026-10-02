-- Prove2me | solution 1 for LearnStability.Characterization.lemma20_subsample_rule
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T17:56:42.289911+00:00
-- url     : https://prove2.me/submissions/b000c11e-b0af-4a47-80be-4879a1ae18f8

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_LearnStability_Characterization_RuleProperties
import Definitions.Def_LearnStability_Characterization_Stability

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LearnStability.Characterization.L20aux

variable {Z : Type*} [MeasurableSpace Z]

noncomputable def splitE (k n : ℕ) : (Fin (k + n) → Z) ≃ᵐ ((Fin k → Z) × (Fin n → Z)) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Z) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => Z))

lemma splitE_fst (k n : ℕ) (S : Fin (k + n) → Z) (i : Fin k) :
    (splitE k n S).1 i = S (Fin.castAdd n i) := by
  rfl

lemma splitE_symm_castAdd (k n : ℕ) (p : (Fin k → Z) × (Fin n → Z)) (i : Fin k) :
    (splitE k n).symm p (Fin.castAdd n i) = p.1 i := by
  have h := splitE_fst k n ((splitE k n).symm p) i
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact h.symm

lemma splitE_snd (k n : ℕ) (S : Fin (k + n) → Z) (j : Fin n) :
    (splitE k n S).2 j = S (Fin.natAdd k j) := by
  rfl

lemma splitE_symm_natAdd (k n : ℕ) (p : (Fin k → Z) × (Fin n → Z)) (j : Fin n) :
    (splitE k n).symm p (Fin.natAdd k j) = p.2 j := by
  have h := splitE_snd k n ((splitE k n).symm p) j
  rw [MeasurableEquiv.apply_symm_apply] at h
  exact h.symm

lemma splitE_mp (D : Measure Z) [IsProbabilityMeasure D] (k n : ℕ) :
    MeasurePreserving (splitE k n) (Measure.pi fun _ : Fin (k + n) => D)
      ((Measure.pi fun _ : Fin k => D).prod (Measure.pi fun _ : Fin n => D)) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Fin k ⊕ Fin n => D)).comp
    ((measurePreserving_piCongrLeft (fun _ : Fin (k + n) => D) finSumFinEquiv).symm _)

lemma iid_abs (D : Measure Z) [IsProbabilityMeasure D] (φ : Z → ℝ) (hφ : Measurable φ)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ z, |φ z| ≤ B) (n : ℕ) :
    ∫ s, |∑ j, φ (s j) - n * ∫ z, φ z ∂D| ∂(Measure.pi fun _ : Fin n => D)
      ≤ B * Real.sqrt n := by
  set μ := Measure.pi fun _ : Fin n => D with hμ
  set X : (Fin n → Z) → ℝ := fun s => ∑ j, φ (s j) with hX
  have hXm : Measurable X := Finset.measurable_sum _ fun j _ => hφ.comp (measurable_pi_apply j)
  have hXb : ∀ s, |X s| ≤ n * B := by
    intro s
    calc |X s| ≤ ∑ j : Fin n, |φ (s j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n, B := Finset.sum_le_sum fun j _ => hB _
      _ = n * B := by simp
  have hmeanφ : ∀ j : Fin n, ∫ s, φ (s j) ∂μ = ∫ z, φ z ∂D := by
    intro j
    rw [← (measurePreserving_eval (fun _ : Fin n => D) j).map_eq,
      integral_map (measurable_pi_apply j).aemeasurable hφ.aestronglyMeasurable]
  have hφint : Integrable φ D :=
    Integrable.of_bound hφ.aestronglyMeasurable B (Filter.Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using hB z)
  have hmean : ∫ s, X s ∂μ = n * ∫ z, φ z ∂D := by
    rw [hX, integral_finsetSum]
    · simp [hmeanφ]
    · intro j _
      exact Integrable.of_bound (hφ.comp (measurable_pi_apply j)).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hB (s j))
  have hvar : variance X μ ≤ n * B ^ 2 := by
    have hXeq : X = ∑ i : Fin n, fun ω : Fin n → Z => φ (ω i) := by
      funext s; simp [hX, Finset.sum_apply]
    have hmemLp : MemLp φ 2 D := MemLp.of_bound hφ.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB z)
    rw [hXeq, variance_sum_pi (μ := fun _ : Fin n => D) (X := fun _ => φ) (fun _ => hmemLp)]
    have hv : variance φ D ≤ B ^ 2 := by
      have := variance_le_sq_of_bounded (μ := D) (a := -B) (b := B)
        (Filter.Eventually.of_forall fun z => Set.mem_Icc.2 (abs_le.1 (hB z))) hφ.aemeasurable
      calc _ ≤ ((B - -B) / 2) ^ 2 := this
        _ = B ^ 2 := by ring
    calc ∑ i : Fin n, variance φ D ≤ ∑ i : Fin n, B ^ 2 := Finset.sum_le_sum fun _ _ => hv
      _ = n * B ^ 2 := by simp
  have hVint : variance X μ = ∫ s, (X s - ∫ s', X s' ∂μ) ^ 2 ∂μ :=
    variance_eq_integral hXm.aemeasurable
  rw [hmean] at hVint
  have hIφ : |∫ z, φ z ∂D| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := D) (C := B) (f := φ)
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hB z)
    simpa [Real.norm_eq_abs] using this
  have hYb : ∀ s, |X s - n * ∫ z, φ z ∂D| ≤ 2 * (n * B) := by
    intro s
    have h1 := hXb s
    have h2 : |(n : ℝ) * ∫ z, φ z ∂D| ≤ n * B := by
      rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_left hIφ (Nat.cast_nonneg _)
    calc |X s - n * ∫ z, φ z ∂D| ≤ |X s| + |(n : ℝ) * ∫ z, φ z ∂D| := abs_sub _ _
      _ ≤ 2 * (n * B) := by linarith
  have hYm : Measurable fun s => X s - n * ∫ z, φ z ∂D := hXm.sub measurable_const
  have hc0 : 0 ≤ B * Real.sqrt n := mul_nonneg hB0 (Real.sqrt_nonneg _)
  rcases hc0.lt_or_eq with hc | hc
  · set c := B * Real.sqrt n with hcdef
    have hc2 : c ^ 2 = n * B ^ 2 := by
      rw [hcdef, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
    have hpt : ∀ s, |X s - n * ∫ z, φ z ∂D|
        ≤ ((X s - n * ∫ z, φ z ∂D) ^ 2 + c ^ 2) / (2 * c) := by
      intro s
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (|X s - n * ∫ z, φ z ∂D| - c), sq_abs (X s - n * ∫ z, φ z ∂D)]
    have hint1 : Integrable (fun s => |X s - n * ∫ z, φ z ∂D|) μ :=
      Integrable.of_bound hYm.abs.aestronglyMeasurable (2 * (n * B))
        (Filter.Eventually.of_forall fun s => by simpa [Real.norm_eq_abs] using hYb s)
    have hint2 : Integrable (fun s => (X s - n * ∫ z, φ z ∂D) ^ 2) μ :=
      Integrable.of_bound (hYm.pow_const 2).aestronglyMeasurable ((2 * (n * B)) ^ 2)
        (Filter.Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hYb s) 2)
    calc ∫ s, |X s - n * ∫ z, φ z ∂D| ∂μ
        ≤ ∫ s, ((X s - n * ∫ z, φ z ∂D) ^ 2 + c ^ 2) / (2 * c) ∂μ :=
          integral_mono hint1 ((hint2.add (integrable_const _)).div_const _) hpt
      _ = ((∫ s, (X s - n * ∫ z, φ z ∂D) ^ 2 ∂μ) + c ^ 2) / (2 * c) := by
          rw [integral_div, integral_add hint2 (integrable_const _)]
          simp
      _ ≤ (n * B ^ 2 + c ^ 2) / (2 * c) := by
          rw [← hVint]; gcongr
      _ = c := by rw [← hc2]; field_simp; ring
  · have hz : ∀ s, |X s - n * ∫ z, φ z ∂D| = 0 := by
      intro s
      have hnB : (n : ℝ) * B = 0 := by
        rcases mul_eq_zero.1 hc.symm with h | h
        · rw [h, mul_zero]
        · have : (n : ℝ) = 0 := by
            have := Real.sqrt_eq_zero'.1 h
            exact le_antisymm this (Nat.cast_nonneg _)
          rw [this, zero_mul]
      have := hYb s
      rw [hnB, mul_zero] at this
      exact le_antisymm this (abs_nonneg _)
    exact le_trans (le_of_eq (integral_eq_zero_of_ae (Filter.Eventually.of_forall hz))) hc0

variable {H : Type*}

lemma abs_risk_le (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B) (D : Measure Z)
    [IsProbabilityMeasure D] (h : H) : |risk f D h| ≤ B := by
  have := norm_integral_le_of_norm_le_const (μ := D) (C := B) (f := f h)
    (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hP.bounded h z)
  simpa [risk, Real.norm_eq_abs] using this

lemma abs_sum_le (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B) {m : ℕ}
    (S : Fin m → Z) (h : H) : |∑ i, f h (S i)| ≤ m * B := by
  calc |∑ i, f h (S i)| ≤ ∑ i, |f h (S i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, B := Finset.sum_le_sum fun i _ => hP.bounded h (S i)
    _ = m * B := by simp

lemma abs_empRisk_le (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B) (hB0 : 0 ≤ B)
    {m : ℕ} (S : Fin m → Z) (h : H) : |empRisk f S h| ≤ B := by
  unfold empRisk
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hB0]
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    rw [abs_div, Nat.abs_cast, div_le_iff₀ hm']
    linarith [abs_sum_le f B hP S h]

lemma meas_restr (k m : ℕ) (hk : k ≤ m) :
    Measurable (fun S : Fin m → Z => fun i : Fin k => S (Fin.castLE hk i)) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply _

lemma meas_risk (f : H → Z → ℝ) (A : Rule H Z) (hA : MeasurableRule f A) (D : Measure Z)
    [IsProbabilityMeasure D] (k : ℕ) : Measurable (fun s : Fin k → Z => risk f D (A k s)) :=
  ((hA k).stronglyMeasurable.integral_prod_right' (ν := D)).measurable

lemma marg (D : Measure Z) [IsProbabilityMeasure D] (k m : ℕ) (hk : k ≤ m)
    (g : (Fin k → Z) → ℝ) :
    ∫ S, g (fun i => S (Fin.castLE hk i)) ∂(Measure.pi fun _ : Fin m => D)
      = ∫ s, g s ∂(Measure.pi fun _ : Fin k => D) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : (fun S : Fin (k + n) → Z => g (fun i => S (Fin.castLE hk i)))
      = fun S => (fun p : (Fin k → Z) × (Fin n → Z) => g p.1) (splitE k n S) := by
    funext S; congr 1
  rw [h1, (splitE_mp D k n).integral_comp' (fun p : (Fin k → Z) × (Fin n → Z) => g p.1),
    integral_fun_fst]
  simp

lemma ratio_le (B : ℝ) (hB0 : 0 ≤ B) (k n : ℕ) (hk1 : 1 ≤ k) (hkm : ((k : ℝ)) ^ 2 ≤ ((k + n : ℕ) : ℝ)) :
    (2 * B * k + B * Real.sqrt n) / ((k + n : ℕ) : ℝ) ≤ 3 * B / Real.sqrt ((k + n : ℕ) : ℝ) := by
  set M : ℝ := ((k + n : ℕ) : ℝ) with hM
  have hMpos : 0 < M := by rw [hM]; exact_mod_cast (by omega : 0 < k + n)
  have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hMpos
  have hs2 : Real.sqrt M ^ 2 = M := Real.sq_sqrt hMpos.le
  have hks : (k : ℝ) ≤ Real.sqrt M := Real.le_sqrt_of_sq_le hkm
  have hns : Real.sqrt n ≤ Real.sqrt M := by
    apply Real.sqrt_le_sqrt; rw [hM]; push_cast; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hsum : 2 * B * k + B * Real.sqrt n ≤ 3 * B * Real.sqrt M := by
    nlinarith [mul_le_mul_of_nonneg_left hks hB0, mul_le_mul_of_nonneg_left hns hB0]
  rw [div_le_div_iff₀ hMpos hs]
  nlinarith [mul_le_mul_of_nonneg_right hsum hs.le]

lemma ratio_le2 (B : ℝ) (hB0 : 0 ≤ B) (k m : ℕ) (hm : 1 ≤ m) (hkm : ((k : ℝ)) ^ 2 ≤ (m : ℝ)) :
    2 * B * k / (m : ℝ) ≤ 2 * B / Real.sqrt m := by
  have hMpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hMpos
  have hs2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hMpos.le
  have hks : (k : ℝ) ≤ Real.sqrt m := Real.le_sqrt_of_sq_le hkm
  rw [div_le_div_iff₀ hMpos hs]
  nlinarith [mul_le_mul_of_nonneg_left hks hB0, mul_le_mul_of_nonneg_left hks (mul_nonneg hB0 hs.le)]

lemma gen_bound [Nonempty H] (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) (D : Measure Z) [IsProbabilityMeasure D]
    (k m : ℕ) (hk : k ≤ m) (hk1 : 1 ≤ k) (hkm : ((k : ℝ)) ^ 2 ≤ (m : ℝ)) :
    ∫ S, |risk f D (A k (fun i => S (Fin.castLE hk i)))
        - empRisk f S (A k (fun i => S (Fin.castLE hk i)))| ∂(Measure.pi fun _ : Fin m => D)
      ≤ 3 * B / Real.sqrt m := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _)
    (hP.bounded (Classical.arbitrary H) (nonempty_of_isProbabilityMeasure D).some)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  set M : ℝ := ((k + n : ℕ) : ℝ) with hM
  have hMpos : 0 < M := by rw [hM]; exact_mod_cast (by omega : 0 < k + n)
  set G : (Fin (k + n) → Z) → ℝ := fun S => |risk f D (A k (fun i => S (Fin.castLE hk i)))
        - empRisk f S (A k (fun i => S (Fin.castLE hk i)))| with hG
  have hGm : Measurable G := by
    have hr := meas_restr (Z := Z) k (k + n) hk
    refine (((meas_risk f A hA D k).comp hr).sub ?_).abs
    unfold empRisk
    refine (Finset.measurable_sum _ fun i _ => ?_).div_const _
    exact (hA k).comp (hr.prodMk (measurable_pi_apply i))
  have hGb : ∀ S, ‖G S‖ ≤ 2 * B := by
    intro S
    rw [Real.norm_eq_abs, hG, abs_abs]
    refine (abs_sub _ _).trans ?_
    linarith [abs_risk_le f B hP D (A k (fun i => S (Fin.castLE hk i))),
      abs_empRisk_le f B hP hB0 S (A k (fun i => S (Fin.castLE hk i)))]
  have h1 : ∫ S, G S ∂(Measure.pi fun _ : Fin (k + n) => D)
      = ∫ p, G ((splitE k n).symm p) ∂((Measure.pi fun _ : Fin k => D).prod
          (Measure.pi fun _ : Fin n => D)) := by
    rw [← (splitE_mp D k n).integral_comp' (fun p => G ((splitE k n).symm p))]
    simp
  have hint : Integrable (fun p => G ((splitE k n).symm p))
      ((Measure.pi fun _ : Fin k => D).prod (Measure.pi fun _ : Fin n => D)) :=
    Integrable.of_bound (hGm.comp (splitE k n).symm.measurable).aestronglyMeasurable (2 * B)
      (Filter.Eventually.of_forall fun p => hGb _)
  set C : ℝ := (2 * B * k + B * Real.sqrt n) / M with hC
  have hinner : ∀ s1 : Fin k → Z,
      ∫ s2, G ((splitE k n).symm (s1, s2)) ∂(Measure.pi fun _ : Fin n => D) ≤ C := by
    intro s1
    set h := A k s1 with hh
    have hGeq : ∀ s2 : Fin n → Z, G ((splitE k n).symm (s1, s2))
        = |risk f D h - ((∑ i, f h (s1 i)) + ∑ j, f h (s2 j)) / M| := by
      intro s2
      have hr : (fun i : Fin k => (splitE k n).symm (s1, s2) (Fin.castLE hk i)) = s1 :=
        funext fun i => splitE_symm_castAdd k n (s1, s2) i
      simp only [hG, empRisk]
      rw [hr, Fin.sum_univ_add]
      simp only [splitE_symm_castAdd, splitE_symm_natAdd]
      rfl
    have hsl : Measurable fun s2 : Fin n → Z => G ((splitE k n).symm (s1, s2)) :=
      (hGm.comp (splitE k n).symm.measurable).comp measurable_prodMk_left
    have hsli : Integrable (fun s2 : Fin n → Z => G ((splitE k n).symm (s1, s2)))
        (Measure.pi fun _ : Fin n => D) :=
      Integrable.of_bound hsl.aestronglyMeasurable (2 * B)
        (Filter.Eventually.of_forall fun p => hGb _)
    have hFb := abs_risk_le f B hP D h
    have hab := abs_sum_le f B hP s1 h
    have hbm : Measurable fun s2 : Fin n → Z => |∑ j, f h (s2 j) - n * risk f D h| :=
      ((Finset.measurable_sum _ fun j _ => (hP.measurable h).comp (measurable_pi_apply j)).sub
        measurable_const).abs
    have hbi : Integrable (fun s2 : Fin n → Z => |∑ j, f h (s2 j) - n * risk f D h|)
        (Measure.pi fun _ : Fin n => D) :=
      Integrable.of_bound hbm.aestronglyMeasurable (2 * (n * B))
        (Filter.Eventually.of_forall fun s2 => by
          rw [Real.norm_eq_abs, abs_abs]
          have h2 : |(n : ℝ) * risk f D h| ≤ n * B := by
            rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_left hFb (Nat.cast_nonneg _)
          have h3 := abs_sum_le f B hP s2 h
          calc _ ≤ |∑ j, f h (s2 j)| + |(n : ℝ) * risk f D h| := abs_sub _ _
            _ ≤ 2 * (n * B) := by linarith)
    have hpt : ∀ s2 : Fin n → Z, G ((splitE k n).symm (s1, s2))
        ≤ (2 * B * k + |∑ j, f h (s2 j) - n * risk f D h|) / M := by
      intro s2
      rw [hGeq s2, le_div_iff₀ hMpos]
      have key : (risk f D h - ((∑ i, f h (s1 i)) + ∑ j, f h (s2 j)) / M) * M
          = (k * risk f D h - ∑ i, f h (s1 i)) - (∑ j, f h (s2 j) - n * risk f D h) := by
        rw [hM]; field_simp; push_cast; ring
      rw [show ∀ x : ℝ, |x| * M = |x * M| from fun x => by rw [abs_mul, abs_of_pos hMpos], key]
      have h4 : |(k : ℝ) * risk f D h| ≤ k * B := by
        rw [abs_mul, Nat.abs_cast]; exact mul_le_mul_of_nonneg_left hFb (Nat.cast_nonneg _)
      calc _ ≤ |(k : ℝ) * risk f D h - ∑ i, f h (s1 i)| + |∑ j, f h (s2 j) - n * risk f D h| :=
            abs_sub _ _
        _ ≤ (|(k : ℝ) * risk f D h| + |∑ i, f h (s1 i)|) + |∑ j, f h (s2 j) - n * risk f D h| := by
            gcongr; exact abs_sub _ _
        _ ≤ 2 * B * k + |∑ j, f h (s2 j) - n * risk f D h| := by linarith
    have hiid : ∫ s2, |∑ j, f h (s2 j) - n * risk f D h| ∂(Measure.pi fun _ : Fin n => D)
        ≤ B * Real.sqrt n :=
      iid_abs D (f h) (hP.measurable h) B hB0 (fun z => hP.bounded h z) n
    calc ∫ s2, G ((splitE k n).symm (s1, s2)) ∂(Measure.pi fun _ : Fin n => D)
        ≤ ∫ s2, (2 * B * k + |∑ j, f h (s2 j) - n * risk f D h|) / M
            ∂(Measure.pi fun _ : Fin n => D) :=
          integral_mono hsli (((integrable_const _).add hbi).div_const _) hpt
      _ = (2 * B * k + ∫ s2, |∑ j, f h (s2 j) - n * risk f D h|
            ∂(Measure.pi fun _ : Fin n => D)) / M := by
          rw [integral_div, integral_add (integrable_const _) hbi]
          simp
      _ ≤ C := by
          rw [hC]; gcongr
  have hgoal : ∫ S, G S ∂(Measure.pi fun _ : Fin (k + n) => D) ≤ C := by
    rw [h1, integral_prod _ hint]
    have := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : Fin k => D) (C := C)
      (f := fun s1 => ∫ s2, G ((splitE k n).symm (s1, s2)) ∂(Measure.pi fun _ : Fin n => D))
      (Filter.Eventually.of_forall fun s1 => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s2 => abs_nonneg _)]
        exact hinner s1)
    simp only [probReal_univ, mul_one] at this
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  exact hgoal.trans (ratio_le B hB0 k n hk1 hkm)

lemma stab_sum (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B) (A : Rule H Z)
    (k m : ℕ) (hk : k ≤ m) (S S' : Fin m → Z) (z' : Z) :
    ∑ i, |f (A k (fun j => Function.update S i (S' i) (Fin.castLE hk j))) z'
        - f (A k (fun j => S (Fin.castLE hk j))) z'| ≤ 2 * B * k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.sum_univ_add]
  have h2 : ∀ j : Fin n, (fun l : Fin k => Function.update S (Fin.natAdd k j)
      (S' (Fin.natAdd k j)) (Fin.castLE hk l)) = fun l => S (Fin.castLE hk l) := by
    intro j; funext l; apply Function.update_of_ne; intro h
    have h' := congrArg Fin.val h
    have hl := l.2
    simp only [Fin.val_castLE, Fin.val_natAdd] at h'
    omega
  simp only [h2, sub_self, abs_zero, Finset.sum_const_zero, add_zero]
  calc _ ≤ ∑ i : Fin k, 2 * B := Finset.sum_le_sum fun i _ => (abs_sub _ _).trans (by
          linarith [hP.bounded (A k (fun j => Function.update S (Fin.castAdd n i)
            (S' (Fin.castAdd n i)) (Fin.castLE hk j))) z',
            hP.bounded (A k (fun j => S (Fin.castLE hk j))) z'])
    _ = 2 * B * k := by simp; ring

end LearnStability.Characterization.L20aux

open MeasureTheory LearnStability.Characterization in
theorem solution {H Z : Type*} [MeasurableSpace Z] [Nonempty H]
    (f : H → Z → ℝ) (B : ℝ) (hP : StandingAssumptions f B)
    (A : Rule H Z) (hA : MeasurableRule f A) :
    ∃ A' : Rule H Z, MeasurableRule f A' ∧
      UniversallyGeneralizes f A' (fun m => 3 * B / Real.sqrt m) ∧
      (∀ D : Measure Z, IsProbabilityMeasure D → ∀ ε : ℕ → ℝ,
        Consistent f A D ε → Consistent f A' D (fun m => ε (Nat.sqrt m))) ∧
      UniformROStable f A' (fun m => 2 * B / Real.sqrt m) := by
  refine ⟨fun m S => A (Nat.sqrt m) (fun i => S (Fin.castLE (Nat.sqrt_le_self m) i)),
    ?_, ?_, ?_, ?_⟩
  · intro m
    exact (hA (Nat.sqrt m)).comp
      (((L20aux.meas_restr _ _ (Nat.sqrt_le_self m)).comp measurable_fst).prodMk measurable_snd)
  · intro D hD m hm
    have hsq : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast Nat.sqrt_le' m
    exact L20aux.gen_bound f B hP A hA D (Nat.sqrt m) m (Nat.sqrt_le_self m)
      (Nat.sqrt_pos.2 hm) hsq
  · intro D hD ε hcons m hm
    have := L20aux.marg D (Nat.sqrt m) m (Nat.sqrt_le_self m)
      (fun s => risk f D (A (Nat.sqrt m) s) - optRisk f D)
    unfold sampleLaw
    rw [this]
    exact hcons _ (Nat.sqrt_pos.2 hm)
  · intro m hm S S' z'
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hP.bounded (Classical.arbitrary H) z')
    have hsq : ((Nat.sqrt m : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast Nat.sqrt_le' m
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have := L20aux.stab_sum f B hP A (Nat.sqrt m) m (Nat.sqrt_le_self m) S S' z'
    calc _ ≤ 2 * B * (Nat.sqrt m : ℕ) / (m : ℝ) := by gcongr
      _ ≤ 2 * B / Real.sqrt m := L20aux.ratio_le2 B hB0 _ m hm hsq
