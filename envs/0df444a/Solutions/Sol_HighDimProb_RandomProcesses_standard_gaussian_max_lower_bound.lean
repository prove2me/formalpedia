-- Prove2me | solution 1 for HighDimProb.RandomProcesses.standard_gaussian_max_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T11:46:24.276986+00:00
-- url     : https://prove2.me/submissions/5bcfbd65-28d9-4c34-95e5-2f37987a7e3d

import Mathlib

-- Inlined module: SudakovGaussianTail
section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace GaussianMaxProof

noncomputable def gaussianTailConstant : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-1)

lemma gaussianTailConstant_pos : 0 < gaussianTailConstant := by
  unfold gaussianTailConstant
  positivity

lemma gaussianPDF_lower_on_unit_interval (t : ℝ) (ht : 0 ≤ t)
    (x : ℝ) (hx : x ∈ Icc t (t + 1)) :
    gaussianTailConstant * Real.exp (-(t ^ 2)) ≤ gaussianPDFReal 0 1 x := by
  have hx0 : 0 ≤ x := ht.trans hx.1
  have hs : x ^ 2 ≤ (t + 1) ^ 2 := pow_le_pow_left₀ hx0 hx.2 2
  have he : -1 + -(t ^ 2) ≤ -(x ^ 2) / 2 := by
    nlinarith [sq_nonneg (t - 1)]
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  unfold gaussianTailConstant
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (by positivity)

lemma standardGaussian_tail_lower (t : ℝ) (ht : 0 ≤ t) :
    gaussianTailConstant * Real.exp (-(t ^ 2)) ≤ (gaussianReal 0 1).real (Ici t) := by
  have hinterval : gaussianTailConstant * Real.exp (-(t ^ 2)) ≤
      (gaussianReal 0 1).real (Icc t (t + 1)) := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
        (fun x _ => gaussianPDFReal_nonneg 0 1 x))]
    calc
      gaussianTailConstant * Real.exp (-(t ^ 2)) =
          ∫ _x in Icc t (t + 1), gaussianTailConstant * Real.exp (-(t ^ 2)) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
        simp
      _ ≤ ∫ x in Icc t (t + 1), gaussianPDFReal 0 1 x :=
        setIntegral_mono_on (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
          (integrable_gaussianPDFReal 0 1).integrableOn measurableSet_Icc
          (gaussianPDF_lower_on_unit_interval t ht)
  exact hinterval.trans (measureReal_mono (fun _ hx => hx.1))

lemma standardGaussian_nonpositive_prob_pos :
    0 < (gaussianReal 0 1).real (Iic 0) := by
  have hp : 0 < (gaussianReal 0 1).real (Icc (-1) 0) := by
    rw [Measure.real, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
        (fun x _ => gaussianPDFReal_nonneg 0 1 x))]
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (gaussianPDFReal_nonneg 0 1))
      (integrable_gaussianPDFReal 0 1).integrableOn).mpr
    simp only [Function.support, ne_eq]
    have he : {x : ℝ | ¬ gaussianPDFReal 0 1 x = 0} = univ := by
      ext x
      simp [(gaussianPDFReal_pos 0 1 x (by norm_num)).ne']
    rw [he]
    norm_num
  exact hp.trans_le (measureReal_mono (fun _ hx => hx.2))

end GaussianMaxProof
end

-- Inlined module: SudakovGaussianMaxProbability
section

open MeasureTheory ProbabilityTheory Set

namespace GaussianMaxProof

lemma standardGaussian_all_below_pow_bound (n : ℕ) (hn : 1 ≤ n) :
    ((gaussianReal 0 1).real (Iio (Real.sqrt (Real.log (n + 1 : ℝ)))) ^ n) ≤
      Real.exp (-(gaussianTailConstant / 2)) := by
  let t := Real.sqrt (Real.log (n + 1 : ℝ))
  let p := (gaussianReal 0 1).real (Iio t)
  let q := (gaussianReal 0 1).real (Ici t)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hN : 0 < (n + 1 : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (n + 1 : ℝ) := Real.log_nonneg (by
    have hnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hq : gaussianTailConstant / (n + 1 : ℝ) ≤ q := by
    have h := standardGaussian_tail_lower t ht
    rw [show t ^ 2 = Real.log (n + 1 : ℝ) from Real.sq_sqrt hlog,
      Real.exp_neg, Real.exp_log hN] at h
    simpa [q, div_eq_mul_inv] using h
  have hpq : p = 1 - q := by
    have h := probReal_compl_eq_one_sub (μ := gaussianReal 0 1) (s := Ici t) measurableSet_Ici
    simpa [p, q] using h
  have hpow : p ^ n ≤ Real.exp (-(n : ℝ) * q) := by
    calc
      p ^ n ≤ (Real.exp (-q)) ^ n :=
        pow_le_pow_left₀ (by positivity) (by rw [hpq]; exact Real.one_sub_le_exp_neg q) n
      _ = Real.exp (-(n : ℝ) * q) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hnq : gaussianTailConstant / 2 ≤ (n : ℝ) * q := by
    have hhalf : gaussianTailConstant / 2 ≤ (n : ℝ) *
        (gaussianTailConstant / (n + 1 : ℝ)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hN).mpr
      have hnc : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have ha := gaussianTailConstant_pos
      nlinarith
    exact hhalf.trans (mul_le_mul_of_nonneg_left hq hn0.le)
  exact hpow.trans (Real.exp_le_exp.mpr (by linarith))

noncomputable def gaussianFirstNonpositive (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  univ.pi (Fin.cons (Iic 0) (fun _ : Fin n => univ))

noncomputable def gaussianFirstNonpositiveAllBelow (n : ℕ) (t : ℝ) :
    Set (Fin (n + 1) → ℝ) :=
  univ.pi (Fin.cons (Iic 0) (fun _ : Fin n => Iio t))

lemma gaussian_good_event_probability (n : ℕ) (t : ℝ) :
    (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)).real
      (gaussianFirstNonpositive n \ gaussianFirstNonpositiveAllBelow n t) =
    (gaussianReal 0 1).real (Iic 0) *
      (1 - (gaussianReal 0 1).real (Iio t) ^ n) := by
  have hsubset : gaussianFirstNonpositiveAllBelow n t ⊆ gaussianFirstNonpositive n := by
    intro x hx i hi
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [gaussianFirstNonpositiveAllBelow] using hx 0 (mem_univ 0)
    · simp [Fin.cons_succ]
  have hmeas : MeasurableSet (gaussianFirstNonpositiveAllBelow n t) := by
    apply MeasurableSet.univ_pi
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact measurableSet_Iic
    · exact measurableSet_Iio
  rw [measureReal_sdiff hsubset hmeas]
  simp only [Measure.real, gaussianFirstNonpositive, gaussianFirstNonpositiveAllBelow,
    Measure.pi_pi, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    measure_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    one_pow, mul_one, ENNReal.toReal_mul, ENNReal.toReal_pow]
  ring

end GaussianMaxProof
end

-- Inlined module: SudakovProcessBasics
section

open MeasureTheory ProbabilityTheory

namespace GaussianMaxProof

lemma hasGaussianLaw_finite {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : ι → Ω → ℝ) (hXG : IsGaussianProcess X P) :
    HasGaussianLaw (fun ω i => X i ω) P := by
  let L : (↥(Finset.univ : Finset ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    { toFun x i := x ⟨i, Finset.mem_univ i⟩
      map_add' x y := rfl
      map_smul' c x := rfl }
  exact (hXG.hasGaussianLaw Finset.univ).map L


lemma integrable_finset_sup' {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, Integrable (X i) P) :
    Integrable (fun ω => s.sup' hs (fun i => X i ω)) P := by
  have hi : Integrable (s.sup' hs X) P :=
    Finset.sup'_induction hs X (p := fun Z : Ω → ℝ => Integrable Z P)
      (fun _ hf _ hg => hf.sup hg) hX
  convert hi using 1
  funext ω
  exact (Finset.sup'_apply hs X ω).symm


end GaussianMaxProof
end

-- Inlined module: SudakovGaussianMaxExpectation
section

open MeasureTheory ProbabilityTheory Set

namespace GaussianMaxProof

lemma standardGaussian_expected_max_ge_event (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    t * (gaussianReal 0 1).real (Iic 0) *
        (1 - (gaussianReal 0 1).real (Iio t) ^ n) ≤
      ∫ x : Fin (n + 1) → ℝ, Finset.univ.sup' Finset.univ_nonempty x
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  let M := fun x : Fin (n + 1) → ℝ => Finset.univ.sup' Finset.univ_nonempty x
  let E := gaussianFirstNonpositive n \ gaussianFirstNonpositiveAllBelow n t
  have hA : MeasurableSet (gaussianFirstNonpositive n) := by
    apply MeasurableSet.univ_pi
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact measurableSet_Iic
    · exact MeasurableSet.univ
  have hB : MeasurableSet (gaussianFirstNonpositiveAllBelow n t) := by
    apply MeasurableSet.univ_pi
    intro i
    refine Fin.cases ?_ (fun _ => ?_) i
    · exact measurableSet_Iic
    · exact measurableSet_Iio
  have hE : MeasurableSet E := hA.diff hB
  have hi (i : Fin (n + 1)) : Integrable (fun x : Fin (n + 1) → ℝ => x i) μ :=
    integrable_eval IsGaussian.integrable_id
  have hiM : Integrable M μ := integrable_finset_sup' μ Finset.univ Finset.univ_nonempty
    (fun i (x : Fin (n + 1) → ℝ) => x i) (fun i _ => hi i)
  have hind : Integrable (E.indicator (fun _ => t)) μ :=
    (integrable_const t).indicator hE
  have hpoint (x : Fin (n + 1) → ℝ) : E.indicator (fun _ => t) x ≤ M x - x 0 := by
    have hM0 : x 0 ≤ M x := Finset.le_sup' (f := x) (Finset.mem_univ 0)
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      have hx0 : x 0 ≤ 0 := by
        simpa [gaussianFirstNonpositive] using hx.1 0 (mem_univ 0)
      have htail : ∃ i : Fin n, t ≤ x i.succ := by
        by_contra h
        push Not at h
        apply hx.2
        intro j hj
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa [gaussianFirstNonpositiveAllBelow] using hx0
        · exact h i
      obtain ⟨i, hi⟩ := htail
      have hMi : x i.succ ≤ M x := Finset.le_sup' (f := x) (Finset.mem_univ _)
      linarith
    · rw [indicator_of_notMem hx]
      linarith
  have h := integral_mono hind (hiM.sub (hi 0)) hpoint
  rw [integral_indicator_const t hE] at h
  simp only [Pi.sub_apply] at h
  rw [integral_sub hiM (hi 0)] at h
  have hm : (∫ x : Fin (n + 1) → ℝ, x 0 ∂μ) = 0 := by
    rw [integral_eval, integral_id_gaussianReal]
  rw [hm, sub_zero] at h
  rw [show μ.real E = (gaussianReal 0 1).real (Iic 0) *
    (1 - (gaussianReal 0 1).real (Iio t) ^ n) from gaussian_good_event_probability n t] at h
  simpa only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using h

noncomputable def gaussianMaxConstant : ℝ :=
  (gaussianReal 0 1).real (Iic 0) * (1 - Real.exp (-(gaussianTailConstant / 2)))

lemma gaussianMaxConstant_pos : 0 < gaussianMaxConstant := by
  apply mul_pos standardGaussian_nonpositive_prob_pos
  apply sub_pos.mpr
  rw [Real.exp_lt_one_iff]
  linarith [gaussianTailConstant_pos]

lemma standardGaussian_max_lower_fin_succ (n : ℕ) (hn : 1 ≤ n) :
    gaussianMaxConstant * Real.sqrt (Real.log (n + 1 : ℝ)) ≤
      ∫ x : Fin (n + 1) → ℝ, Finset.univ.sup' Finset.univ_nonempty x
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have h := standardGaussian_expected_max_ge_event n (Real.sqrt (Real.log (n + 1 : ℝ)))
    (Real.sqrt_nonneg _)
  have hp := standardGaussian_all_below_pow_bound n hn
  have hr : 0 ≤ (gaussianReal 0 1).real (Iic 0) := by positivity
  unfold gaussianMaxConstant
  calc
    _ ≤ Real.sqrt (Real.log (n + 1 : ℝ)) * (gaussianReal 0 1).real (Iic 0) *
        (1 - (gaussianReal 0 1).real (Iio (Real.sqrt (Real.log (n + 1 : ℝ)))) ^ n) := by
      nlinarith [mul_nonneg (Real.sqrt_nonneg (Real.log (n + 1 : ℝ))) hr]
    _ ≤ _ := h

end GaussianMaxProof
end

-- Inlined module: SudakovGaussianMax
section

open MeasureTheory ProbabilityTheory

namespace GaussianMaxProof

lemma standardGaussian_max_lower_fin (n : ℕ) [Nonempty (Fin n)] :
    gaussianMaxConstant * Real.sqrt (Real.log (n : ℝ)) ≤
      ∫ x : Fin n → ℝ, Finset.univ.sup' Finset.univ_nonempty x
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  classical
  cases n with
  | zero => exact isEmptyElim (Classical.ofNonempty : Fin 0)
  | succ n =>
    cases n with
    | zero =>
      have hM (x : Fin 1 → ℝ) : Finset.univ.sup' Finset.univ_nonempty x = x 0 := by
        apply Finset.sup'_eq_of_forall
        intro i _
        have hi : i = 0 := Subsingleton.elim _ _
        rw [hi]
      simp_rw [hM]
      rw [integral_eval, integral_id_gaussianReal]
      simp
    | succ n =>
      simpa only [Nat.cast_add, Nat.cast_one] using
        standardGaussian_max_lower_fin_succ (n + 1) (by omega)

theorem standard_gaussian_max_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ {ι : Type} [Fintype ι] [Nonempty ι],
        c * Real.sqrt (Real.log (Fintype.card ι)) ≤
          ∫ x : ι → ℝ, Finset.univ.sup' Finset.univ_nonempty x
            ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  classical
  refine ⟨gaussianMaxConstant, gaussianMaxConstant_pos, ?_⟩
  intro ι _ _
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  letI : Nonempty (Fin (Fintype.card ι)) := ⟨e.symm (Classical.ofNonempty)⟩
  let E := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  have hp := measurePreserving_piCongrLeft (fun _ : ι => gaussianReal 0 1) e
  have hmax (x : Fin (Fintype.card ι) → ℝ) :
      Finset.univ.sup' Finset.univ_nonempty (E x) =
        Finset.univ.sup' Finset.univ_nonempty x := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      have hi : E x i = x (e.symm i) := by
        simpa using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e x (e.symm i)
      rw [hi]
      exact Finset.le_sup' (f := x) (Finset.mem_univ _)
    · apply Finset.sup'_le
      intro i _
      have hi : E x (e i) = x i :=
        MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => ℝ) e x i
      rw [← hi]
      exact Finset.le_sup' (f := E x) (Finset.mem_univ _)
  have h := standardGaussian_max_lower_fin (Fintype.card ι)
  have hint := hp.integral_comp' (fun x : ι → ℝ => Finset.univ.sup' Finset.univ_nonempty x)
  change (∫ x : Fin (Fintype.card ι) → ℝ, Finset.univ.sup' Finset.univ_nonempty (E x)
    ∂Measure.pi (fun _ : Fin (Fintype.card ι) => gaussianReal 0 1)) =
    (∫ x : ι → ℝ, Finset.univ.sup' Finset.univ_nonempty x
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) at hint
  simp only [hmax] at hint
  exact h.trans_eq hint

end GaussianMaxProof
end

open MeasureTheory ProbabilityTheory

theorem solution :
  ∃ c : ℝ, 0 < c ∧
    ∀ {ι : Type} [Fintype ι] [Nonempty ι],
      c * Real.sqrt (Real.log (Fintype.card ι)) ≤
        ∫ x : ι → ℝ, Finset.univ.sup' Finset.univ_nonempty x
          ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  exact GaussianMaxProof.standard_gaussian_max_lower_bound
