-- Prove2me | solution 1 for HighDimProb.Deviations.m_star_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:13:25.269126+00:00
-- url     : https://prove2.me/submissions/6c7f94b0-8b75-4cca-a8ce-608c9890db07

import Mathlib
import Definitions.Def_HighDimProb_Deviations_IsIsotropic
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm
import Definitions.Def_HighDimProb_Deviations_GaussianWidth

open MeasureTheory ProbabilityTheory

namespace HighDimProb.Deviations

open scoped ENNReal

/-- Geometric probability measure on `ℕ`: mass `2^{-(k+1)}` at `k`. -/
noncomputable def aux_msb_P : Measure ℕ :=
  Measure.sum (fun k : ℕ => ((2:ℝ≥0∞)⁻¹ ^ (k+1)) • Measure.dirac k)

lemma aux_msb_lintegral (f : ℕ → ℝ≥0∞) :
    ∫⁻ k, f k ∂aux_msb_P = ∑' k, (2:ℝ≥0∞)⁻¹ ^ (k+1) * f k := by
  simp only [aux_msb_P, lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]

instance aux_msb_prob : IsProbabilityMeasure aux_msb_P := by
  constructor
  have h := aux_msb_lintegral (fun _ => 1)
  rw [lintegral_const, one_mul] at h
  rw [h]
  simp only [mul_one, pow_succ]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

lemma aux_msb_wt (k : ℕ) : (2:ℝ≥0∞)⁻¹ ^ (k+1) = ENNReal.ofReal ((1/2:ℝ) ^ (k+1)) := by
  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
  simp

lemma aux_msb_lint_norm (g : ℕ → ℝ) :
    ∫⁻ k, ‖g k‖ₑ ∂aux_msb_P = ∑' k, ENNReal.ofReal ((1/2:ℝ) ^ (k+1) * |g k|) := by
  rw [aux_msb_lintegral]
  congr 1
  funext k
  rw [aux_msb_wt, ← ofReal_norm, Real.norm_eq_abs,
    ENNReal.ofReal_mul (by positivity)]

lemma aux_msb_int_sq : Integrable (fun k : ℕ => ((k:ℝ)) ^ 2) aux_msb_P := by
  refine ⟨measurable_from_nat.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [aux_msb_lint_norm]
  have hs : Summable (fun k : ℕ => (1/2:ℝ) ^ (k+1) * |((k:ℝ)) ^ 2|) := by
    have := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 (r := 1/2)
      (by rw [Real.norm_eq_abs]; norm_num)
    refine (this.mul_left (1/2)).congr ?_
    intro k
    rw [abs_of_nonneg (by positivity), pow_succ]
    ring
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  exact ENNReal.ofReal_lt_top

lemma aux_msb_not_int (s : ℝ) (hs : 0 < s) :
    ¬ Integrable (fun k : ℕ => Real.exp (s * ((k:ℝ)) ^ 2)) aux_msb_P := by
  intro hI
  have h1 := hI.2
  unfold HasFiniteIntegral at h1
  rw [aux_msb_lint_norm] at h1
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top h1.ne
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      ENNReal.ofReal ((1/2:ℝ) ^ (k+1) * |Real.exp (s * ((k:ℝ)) ^ 2)|) < 1 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  set k : ℕ := max N (⌈3 / s⌉₊ + 1) with hk
  have hkN : N ≤ k := le_max_left _ _
  have hk1 : (⌈3 / s⌉₊ + 1 : ℕ) ≤ k := le_max_right _ _
  have hkpos : 1 ≤ k := le_trans (by omega) hk1
  have hks : 3 ≤ s * (k:ℝ) := by
    have h3 : (3 / s) ≤ (k:ℝ) := by
      have := Nat.le_ceil (3 / s)
      have h2 : ((⌈3 / s⌉₊ + 1 : ℕ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
      push_cast at h2
      linarith
    rw [div_le_iff₀ hs] at h3
    linarith
  have hexp4 : (4:ℝ) ≤ Real.exp (s * k) := by
    have := Real.add_one_le_exp (s * k)
    linarith
  have hexpk : (4:ℝ) ^ k ≤ Real.exp (s * ((k:ℝ)) ^ 2) := by
    have : Real.exp (s * ((k:ℝ)) ^ 2) = Real.exp (s * k) ^ k := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) hexp4 k
  have hge : (1:ℝ) ≤ (1/2:ℝ) ^ (k+1) * |Real.exp (s * ((k:ℝ)) ^ 2)| := by
    rw [abs_of_pos (Real.exp_pos _)]
    have h4 : (1/2:ℝ) ^ (k+1) * (4:ℝ) ^ k = 2 ^ k / 2 := by
      rw [pow_succ, show (4:ℝ) = 2 * 2 by norm_num, mul_pow]
      have e : (1/2:ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
      linear_combination (2 ^ k / 2 : ℝ) * e
    have h2k : (2:ℝ) ≤ 2 ^ k := by
      calc (2:ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hkpos
    calc (1:ℝ) ≤ 2 ^ k / 2 := by linarith
      _ = (1/2:ℝ) ^ (k+1) * (4:ℝ) ^ k := h4.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hexpk (by positivity)
  have := hN k hkN
  rw [ENNReal.ofReal_lt_one] at this
  linarith

/-- normalizing constant -/
noncomputable def aux_msb_c : ℝ := ∫ k, ((k:ℝ)) ^ 2 ∂aux_msb_P

lemma aux_msb_P0 : (2:ℝ≥0∞)⁻¹ ≤ aux_msb_P {0} := by
  have h := Measure.le_iff'.1
    (Measure.le_sum (fun k : ℕ => ((2:ℝ≥0∞)⁻¹ ^ (k+1)) • Measure.dirac k) 1) {1}
  have h0 := Measure.le_iff'.1
    (Measure.le_sum (fun k : ℕ => ((2:ℝ≥0∞)⁻¹ ^ (k+1)) • Measure.dirac k) 0) {0}
  simpa [aux_msb_P] using h0

lemma aux_msb_P1 : 0 < aux_msb_P {1} := by
  have h := Measure.le_iff'.1
    (Measure.le_sum (fun k : ℕ => ((2:ℝ≥0∞)⁻¹ ^ (k+1)) • Measure.dirac k) 1) {1}
  refine lt_of_lt_of_le ?_ h
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_singleton 1),
    mul_one]
  exact ENNReal.pow_pos (by simp) _

lemma aux_msb_c_pos : 0 < aux_msb_c := by
  unfold aux_msb_c
  rw [integral_pos_iff_support_of_nonneg (fun k => by positivity) aux_msb_int_sq]
  refine lt_of_lt_of_le aux_msb_P1 (measure_mono ?_)
  intro k hk
  simp only [Set.mem_singleton_iff] at hk
  subst hk
  simp

noncomputable def aux_msb_X (k : ℕ) : ℝ := (k:ℝ) / Real.sqrt aux_msb_c

noncomputable def aux_msb_A : Fin 1 → ℕ → EuclideanSpace ℝ (Fin 1) :=
  fun _ k => EuclideanSpace.single 0 (aux_msb_X k)

lemma aux_msb_inner (i : Fin 1) (k : ℕ) (x : EuclideanSpace ℝ (Fin 1)) :
    inner (𝕜 := ℝ) (aux_msb_A i k) x = aux_msb_X k * x 0 := by
  simp [aux_msb_A, EuclideanSpace.inner_single_left]

lemma aux_msb_sq (i : Fin 1) (k : ℕ) (x : EuclideanSpace ℝ (Fin 1)) :
    (inner (𝕜 := ℝ) (aux_msb_A i k) x) ^ 2 = ((k:ℝ)) ^ 2 * ((x 0) ^ 2 / aux_msb_c) := by
  rw [aux_msb_inner, aux_msb_X, mul_pow, div_pow, Real.sq_sqrt aux_msb_c_pos.le]
  ring

lemma aux_msb_norm_sq (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ ^ 2 = (x 0) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]

lemma aux_msb_iso (i : Fin 1) : IsIsotropic aux_msb_P (aux_msb_A i) := by
  intro x
  simp_rw [aux_msb_sq]
  refine ⟨aux_msb_int_sq.mul_const _, ?_⟩
  rw [integral_mul_const, aux_msb_norm_sq]
  change aux_msb_c * _ = _
  field_simp [aux_msb_c_pos.ne']

lemma aux_msb_sg (i : Fin 1) : subgaussianVectorNorm aux_msb_P (aux_msb_A i) ≤ 0 := by
  unfold subgaussianVectorNorm
  have h : ∀ x : {v : EuclideanSpace ℝ (Fin 1) // ‖v‖ = 1},
      HighDimProb.Concentration.subgaussianNorm aux_msb_P
        (fun ω => inner (𝕜 := ℝ) (aux_msb_A i ω) x.1) = 0 := by
    intro x
    unfold HighDimProb.Concentration.subgaussianNorm
    have hx : (x.1 0) ^ 2 = 1 := by
      rw [← aux_msb_norm_sq, x.2]; norm_num
    have hempty : {t : ℝ | 0 < t ∧ Integrable (fun ω => Real.exp
        ((inner (𝕜 := ℝ) (aux_msb_A i ω) x.1) ^ 2 / t ^ 2)) aux_msb_P ∧
        ∫ ω, Real.exp ((inner (𝕜 := ℝ) (aux_msb_A i ω) x.1) ^ 2 / t ^ 2) ∂aux_msb_P ≤ 2}
        = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨ht, hI, -⟩
      apply aux_msb_not_int (1 / (aux_msb_c * t ^ 2)) (by
        have := aux_msb_c_pos; positivity)
      refine hI.congr (Filter.Eventually.of_forall ?_)
      intro k
      simp only
      rw [aux_msb_sq, hx]
      congr 1
      field_simp
    rw [hempty, Real.sInf_empty]
  simp_rw [h]
  rw [Real.iSup_const_zero]

noncomputable def aux_msb_T : Set (EuclideanSpace ℝ (Fin 1)) :=
  {0, EuclideanSpace.single 0 1}

lemma aux_msb_Tf : aux_msb_T.Finite :=
  Set.Finite.insert _ (Set.finite_singleton _)

lemma aux_msb_Tb : Bornology.IsBounded aux_msb_T :=
  aux_msb_Tf.isBounded

instance aux_msb_Tfin : Finite aux_msb_T :=
  aux_msb_Tf.to_subtype

lemma aux_msb_width : ∃ w : ℝ, gaussianWidth aux_msb_T = (w : EReal) := by
  have : Nonempty {s : Finset aux_msb_T // s.Nonempty} :=
    ⟨⟨{⟨0, by simp [aux_msb_T]⟩}, Finset.singleton_nonempty _⟩⟩
  obtain ⟨S, hS⟩ := exists_eq_ciSup_of_finite (ι := {s : Finset aux_msb_T // s.Nonempty})
    (f := fun S => ((∫ ω, S.1.sup' S.2 (fun i => (fun x : aux_msb_T => fun g =>
      inner (𝕜 := ℝ) g x.1) i ω) ∂(stdGaussian (EuclideanSpace ℝ (Fin 1))) : ℝ) : EReal))
  exact ⟨_, by unfold gaussianWidth expSup; exact hS.symm⟩

lemma aux_msb_diamT : 0 < Metric.diam aux_msb_T := by
  unfold aux_msb_T
  rw [Metric.diam_pair, dist_zero_left, PiLp.norm_single]
  norm_num

end HighDimProb.Deviations

open HighDimProb.Deviations

theorem solution : ¬ (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (hm : 0 < m) (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P →
        (∀ i, IsIsotropic P (A i)) →
        ∀ (K : ℝ), 0 ≤ K → (∀ i, subgaussianVectorNorm P (A i) ≤ K) →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))), Bornology.IsBounded T →
        ∀ (w : ℝ), gaussianWidth T = (w : EReal) →
          Integrable
              (fun ω => Metric.diam (T ∩ {x | ∀ i, inner (𝕜 := ℝ) (A i ω) x = 0})) P ∧
          ∫ ω, Metric.diam (T ∩ {x | ∀ i, inner (𝕜 := ℝ) (A i ω) x = 0}) ∂P ≤
            C * K ^ 2 * w / Real.sqrt (m : ℝ)) := by
  rintro ⟨C, _hC, h⟩
  obtain ⟨w, hw⟩ := aux_msb_width
  obtain ⟨hint, hle⟩ := h aux_msb_P (m := 1) (n := 1) one_pos aux_msb_A
    iIndepFun.of_subsingleton aux_msb_iso 0 le_rfl aux_msb_sg aux_msb_T aux_msb_Tb w hw
  have hrhs : C * (0:ℝ) ^ 2 * w / Real.sqrt ((1:ℕ) : ℝ) = 0 := by simp
  rw [hrhs] at hle
  have hpos : 0 < ∫ ω, Metric.diam (aux_msb_T ∩
      {x | ∀ i, inner (𝕜 := ℝ) (aux_msb_A i ω) x = 0}) ∂aux_msb_P := by
    rw [integral_pos_iff_support_of_nonneg (fun _ => Metric.diam_nonneg) hint]
    refine lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) aux_msb_P0) (measure_mono ?_)
    intro k hk
    simp only [Set.mem_singleton_iff] at hk
    subst hk
    rw [Function.mem_support]
    have hset : aux_msb_T ∩ {x | ∀ i, inner (𝕜 := ℝ) (aux_msb_A i 0) x = 0} = aux_msb_T := by
      apply Set.inter_eq_left.2
      intro x _ i
      rw [aux_msb_inner]
      simp [aux_msb_X]
    rw [hset]
    exact aux_msb_diamT.ne'
  linarith
