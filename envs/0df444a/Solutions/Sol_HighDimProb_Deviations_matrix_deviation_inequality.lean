-- Prove2me | solution 1 for HighDimProb.Deviations.matrix_deviation_inequality
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:14:22.698614+00:00
-- url     : https://prove2.me/submissions/19d87df4-e5da-4324-bf8a-3ee0335d4343

import Mathlib
import Definitions.Def_HighDimProb_Deviations_ExpSup
import Definitions.Def_HighDimProb_Deviations_IsIsotropic
import Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm
import Definitions.Def_HighDimProb_Deviations_GaussianComplexity

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MDICex8b

/-- Geometric law on `ℕ`: mass `2⁻¹^(k+1)` at `k`. -/
noncomputable def P : Measure ℕ :=
  Measure.sum (fun k : ℕ => ((2⁻¹ : ENNReal) ^ (k + 1)) • Measure.dirac k)

theorem lintegral_P (f : ℕ → ENNReal) :
    ∫⁻ k, f k ∂P = ∑' k, (2⁻¹ : ENNReal) ^ (k + 1) * f k := by
  simp [P, lintegral_sum_measure, lintegral_smul_measure, lintegral_dirac]

theorem P_univ : P Set.univ = 1 := by
  have h := lintegral_P (fun _ => 1)
  simp only [lintegral_const, one_mul, mul_one] at h
  rw [h]
  simp_rw [pow_succ']
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance : IsProbabilityMeasure P := ⟨P_univ⟩

theorem P_singleton (k : ℕ) : (2⁻¹ : ENNReal) ^ (k + 1) ≤ P {k} := by
  rw [P, Measure.sum_apply _ (measurableSet_singleton k)]
  refine le_trans ?_ (ENNReal.le_tsum k)
  simp

theorem integrable_of_summable (f : ℕ → ℝ)
    (h : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) * |f k|)) : Integrable f P := by
  refine ⟨(measurable_of_countable f).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_P]
  have e : ∀ k : ℕ, (2⁻¹ : ENNReal) ^ (k + 1) * ‖f k‖ₑ
      = ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1) * |f k|) := by
    intro k
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      ← Real.enorm_eq_ofReal_abs]
    congr 2
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  simp_rw [e]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) h]
  exact ENNReal.ofReal_lt_top

theorem summable_sq : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) * |((k : ℝ) ^ 2)|) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
    (r := 1 / 2) (by norm_num [abs_of_pos])
  refine (h.mul_left (1 / 2)).congr (fun k => ?_)
  rw [abs_of_nonneg (by positivity), pow_succ]
  ring

theorem integrable_sq : Integrable (fun k : ℕ => (k : ℝ) ^ 2) P :=
  integrable_of_summable _ summable_sq

/-- `M = E k²`. -/
noncomputable def M : ℝ := ∫ k, (k : ℝ) ^ 2 ∂P

theorem M_pos : 0 < M := by
  unfold M
  rw [integral_pos_iff_support_of_nonneg (fun k => by positivity) integrable_sq]
  refine lt_of_lt_of_le ?_ (measure_mono (s := {1}) ?_)
  · exact lt_of_lt_of_le (ENNReal.pow_pos (by norm_num) _) (P_singleton 1)
  · intro k hk
    simp only [Set.mem_singleton_iff] at hk
    subst hk
    simp

noncomputable def X (k : ℕ) : ℝ := (k : ℝ) / Real.sqrt M

theorem X_sq (k : ℕ) : X k ^ 2 = (k : ℝ) ^ 2 / M := by
  rw [X, div_pow, Real.sq_sqrt M_pos.le]

theorem integrable_X_sq : Integrable (fun k => X k ^ 2) P := by
  simp_rw [X_sq]
  exact integrable_sq.div_const _

theorem integral_X_sq : ∫ k, X k ^ 2 ∂P = 1 := by
  simp_rw [X_sq]
  rw [integral_div]
  exact div_self M_pos.ne'

theorem exp_unbounded (c : ℝ) (hc : 0 < c) (B : ℝ) :
    ∃ k : ℕ, B < (1 / 2 : ℝ) ^ (k + 1) * Real.exp (c * (k : ℝ) ^ 2) := by
  refine ⟨⌈(|B| + 2) / c⌉₊ + 1, ?_⟩
  set k : ℕ := ⌈(|B| + 2) / c⌉₊ + 1 with hk
  have hk1 : (1 : ℝ) ≤ k := by rw [hk]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈(|B| + 2) / c⌉₊]
  have hck : |B| + 2 ≤ c * k := by
    have := Nat.le_ceil ((|B| + 2) / c)
    rw [div_le_iff₀ hc] at this
    have : (⌈(|B| + 2) / c⌉₊ : ℝ) ≤ k := by rw [hk]; push_cast; linarith
    nlinarith
  have h2 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by norm_num)
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have h3 : Real.exp (-((k : ℝ) + 1)) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    have : Real.exp (-((k : ℝ) + 1)) = Real.exp (-1) ^ (k + 1) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h2 _
  have h4 : Real.exp (-((k : ℝ) + 1)) * Real.exp (c * (k : ℝ) ^ 2)
      = Real.exp (c * (k : ℝ) ^ 2 - k - 1) := by
    rw [← Real.exp_add]; ring_nf
  have h5 : c * (k : ℝ) ^ 2 - k - 1 + 1 ≤ Real.exp (c * (k : ℝ) ^ 2 - k - 1) :=
    Real.add_one_le_exp _
  have h6 : B < c * (k : ℝ) ^ 2 - k := by
    have : (|B| + 2) * k ≤ c * k * k := mul_le_mul_of_nonneg_right hck (by linarith)
    nlinarith [le_abs_self B, abs_nonneg B]
  calc B < Real.exp (-((k : ℝ) + 1)) * Real.exp (c * (k : ℝ) ^ 2) := by rw [h4]; linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le

theorem not_integrable_exp (c : ℝ) (hc : 0 < c) :
    ¬ Integrable (fun k : ℕ => Real.exp (c * (k : ℝ) ^ 2)) P := by
  intro hI
  have hfin := hI.2
  unfold HasFiniteIntegral at hfin
  rw [lintegral_P] at hfin
  beta_reduce at hfin
  obtain ⟨k, hk⟩ := exp_unbounded c hc
    (∑' j : ℕ, (2⁻¹ : ENNReal) ^ (j + 1) * ‖Real.exp (c * (j : ℝ) ^ 2)‖ₑ).toReal
  have hle := ENNReal.le_tsum
    (f := fun k : ℕ => (2⁻¹ : ENNReal) ^ (k + 1) * ‖Real.exp (c * (k : ℝ) ^ 2)‖ₑ) k
  have e : (2⁻¹ : ENNReal) ^ (k + 1) * ‖Real.exp (c * (k : ℝ) ^ 2)‖ₑ
      = ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1) * Real.exp (c * (k : ℝ) ^ 2)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
      Real.enorm_eq_ofReal (Real.exp_pos _).le]
    congr 2
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  rw [e] at hle
  have := (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 hle
  linarith

/-- The (single) row. -/
noncomputable def A : Fin 1 → ℕ → EuclideanSpace ℝ (Fin 1) :=
  fun _ k => EuclideanSpace.single 0 (X k)

theorem inner_A (i : Fin 1) (k : ℕ) (x : EuclideanSpace ℝ (Fin 1)) :
    inner (𝕜 := ℝ) (A i k) x = X k * x 0 := by
  simp [A, EuclideanSpace.inner_single_left]

theorem norm_sq_fin1 (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ ^ 2 = x 0 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_one, Real.norm_eq_abs,
    sq_abs]

theorem iso (i : Fin 1) : HighDimProb.Deviations.IsIsotropic P (A i) := by
  intro x
  simp_rw [inner_A, mul_pow]
  refine ⟨integrable_X_sq.mul_const _, ?_⟩
  rw [integral_mul_const, integral_X_sq, one_mul, norm_sq_fin1]

theorem sg_zero (i : Fin 1) : HighDimProb.Deviations.subgaussianVectorNorm P (A i) ≤ 0 := by
  unfold HighDimProb.Deviations.subgaussianVectorNorm
  apply Real.iSup_nonpos
  intro v
  have hv : v.1 0 ^ 2 = 1 := by rw [← norm_sq_fin1, v.2, one_pow]
  unfold HighDimProb.Concentration.subgaussianNorm
  apply le_of_eq
  convert Real.sInf_empty
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro ht hI _
  apply not_integrable_exp (1 / (M * t ^ 2)) (by have := M_pos; positivity)
  refine hI.congr (Filter.Eventually.of_forall fun k => ?_)
  simp only [inner_A, mul_pow, hv, mul_one, X_sq]
  congr 1
  field_simp

theorem expSup_subsingleton {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) {Idx : Type}
    [Subsingleton Idx] (i0 : Idx) (Y : Idx → Ω → ℝ) :
    HighDimProb.Deviations.expSup Q Y = ((∫ ω, Y i0 ω ∂Q : ℝ) : EReal) := by
  unfold HighDimProb.Deviations.expSup
  have key : ∀ (S : {s : Finset Idx // s.Nonempty}) (ω : Ω),
      S.1.sup' S.2 (fun i => Y i ω) = Y i0 ω := by
    intro S ω
    obtain ⟨i, hi⟩ := S.2
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun j _ => le_of_eq (by rw [Subsingleton.elim j i0])
    · rw [Subsingleton.elim i0 i]; exact Finset.le_sup' (fun i => Y i ω) hi
  simp only [key]
  have : Nonempty {s : Finset Idx // s.Nonempty} := ⟨⟨{i0}, Finset.singleton_nonempty _⟩⟩
  exact iSup_const

noncomputable def e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

theorem lhs_pos :
    0 < ∫ k, |Real.sqrt (∑ i : Fin 1, (inner (𝕜 := ℝ) (A i k) e) ^ 2) -
        Real.sqrt ((1 : ℕ) : ℝ) * ‖e‖| ∂P := by
  have hfun : (fun k : ℕ => |Real.sqrt (∑ i : Fin 1, (inner (𝕜 := ℝ) (A i k) e) ^ 2) -
        Real.sqrt ((1 : ℕ) : ℝ) * ‖e‖|) = fun k : ℕ => |(k : ℝ) / Real.sqrt M - 1| := by
    funext k
    simp only [inner_A, e, Fin.sum_univ_one, EuclideanSpace.single_apply, if_true, mul_one,
      Real.sqrt_sq_eq_abs, Nat.cast_one, Real.sqrt_one, one_mul, EuclideanSpace.norm_single,
      norm_one, X]
    rw [abs_of_nonneg (a := (k : ℝ) / Real.sqrt M) (by have := M_pos; positivity)]
  rw [hfun]
  have hint : Integrable (fun k : ℕ => |(k : ℝ) / Real.sqrt M - 1|) P := by
    refine Integrable.mono' ((integrable_sq.div_const (Real.sqrt M)).add (integrable_const 1))
      (measurable_of_countable _).aestronglyMeasurable (Filter.Eventually.of_forall fun k => ?_)
    have hM : 0 < Real.sqrt M := Real.sqrt_pos.2 M_pos
    have hk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp
      · have : (1 : ℝ) ≤ k := by exact_mod_cast h
        nlinarith
    rw [Real.norm_eq_abs, abs_abs]
    refine le_trans (abs_sub _ _) ?_
    rw [abs_of_nonneg (a := (k : ℝ) / Real.sqrt M) (by positivity), abs_one]
    have := (div_le_div_iff_of_pos_right hM).2 hk
    simp only [Pi.add_apply]
    linarith
  rw [integral_pos_iff_support_of_nonneg (fun k => abs_nonneg _) hint]
  refine lt_of_lt_of_le ?_ (measure_mono (s := {0}) ?_)
  · exact lt_of_lt_of_le (ENNReal.pow_pos (by norm_num) _) (P_singleton 0)
  · intro k hk
    simp only [Set.mem_singleton_iff] at hk
    subst hk
    simp

end MDICex8b

open MeasureTheory ProbabilityTheory HighDimProb.Deviations in
theorem solution : ¬ (∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        {m n : ℕ} (A : Fin m → Ω → EuclideanSpace ℝ (Fin n)),
        iIndepFun A P →
        (∀ i, IsIsotropic P (A i)) →
        ∀ (K : ℝ), 0 ≤ K → (∀ i, subgaussianVectorNorm P (A i) ≤ K) →
        ∀ (T : Set (EuclideanSpace ℝ (Fin n))) (γ : ℝ),
          gaussianComplexity T = (γ : EReal) →
          expSup P (fun x : T => fun ω =>
              |Real.sqrt (∑ i, (inner (𝕜 := ℝ) (A i ω) x.1) ^ 2) -
                Real.sqrt m * ‖x.1‖|) ≤
            ((C * K ^ 2 * γ : ℝ) : EReal)) := by
  rintro ⟨C, -, h⟩
  have hγ := MDICex8b.expSup_subsingleton (stdGaussian (EuclideanSpace ℝ (Fin 1)))
    (⟨MDICex8b.e, rfl⟩ : ({MDICex8b.e} : Set (EuclideanSpace ℝ (Fin 1))))
    (fun x g => |inner (𝕜 := ℝ) g x.1|)
  have hb := h MDICex8b.P (m := 1) (n := 1) MDICex8b.A (iIndepFun.of_subsingleton)
    MDICex8b.iso 0 le_rfl MDICex8b.sg_zero {MDICex8b.e} _ hγ
  rw [MDICex8b.expSup_subsingleton MDICex8b.P
    (⟨MDICex8b.e, rfl⟩ : ({MDICex8b.e} : Set (EuclideanSpace ℝ (Fin 1))))] at hb
  have hp := MDICex8b.lhs_pos
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
    EReal.coe_zero] at hb
  have : ((∫ k, |Real.sqrt (∑ i : Fin 1, (inner (𝕜 := ℝ) (MDICex8b.A i k) MDICex8b.e) ^ 2) -
        Real.sqrt ((1 : ℕ) : ℝ) * ‖MDICex8b.e‖| ∂MDICex8b.P : ℝ) : EReal) ≤ 0 := hb
  rw [EReal.coe_nonpos] at this
  linarith
