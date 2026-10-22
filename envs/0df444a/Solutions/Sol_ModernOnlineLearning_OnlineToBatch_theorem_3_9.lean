-- Prove2me | solution 1 for ModernOnlineLearning.OnlineToBatch.theorem_3_9
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T06:10:40.769051+00:00
-- url     : https://prove2.me/submissions/d074a1bd-2f52-4f1d-9b51-b476fa8b48e7

import Mathlib
open MeasureTheory ProbabilityTheory Filter

private lemma exp_chord (B y s : ℝ) (hB : 0 < B) (hy : |y| ≤ B) :
    Real.exp (s*y) ≤ Real.cosh (s*B)+(y/B)*Real.sinh (s*B) := by
  have hyl := (abs_le.mp hy).1
  have hyu := (abs_le.mp hy).2
  let a := (B+y)/(2*B)
  let b := (B-y)/(2*B)
  have ha : 0 ≤ a := by dsimp [a]; exact div_nonneg (by linarith) (by positivity)
  have hb : 0 ≤ b := by dsimp [b]; exact div_nonneg (by linarith) (by positivity)
  have hab : a+b=1 := by dsimp [a,b]; field_simp <;> ring
  have h := convexOn_exp.2 (x := s*B) (Set.mem_univ _) (y := -(s*B)) (Set.mem_univ _) ha hb hab
  simp only [smul_eq_mul] at h
  have he : a*(s*B)+b*(-(s*B))=s*y := by dsimp [a,b]; field_simp <;> ring
  rw [he] at h
  convert! h using 1
  rw [Real.cosh_eq, Real.sinh_eq]
  dsimp [a,b]
  field_simp
  ring

private lemma exp_norm_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (C s : ℝ) (hC : ∀ᵐ ω ∂μ, |f ω| ≤ C) :
    ∀ᵐ ω ∂μ, ‖Real.exp (s*f ω)‖ ≤ Real.exp (|s| * C) := by
  filter_upwards [hC] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |s*f ω| := le_abs_self _
    _ = |s| * |f ω| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hω (abs_nonneg _)

private lemma weighted_cond_zero {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm : m ≤ mΩ)
    (F D : Ω → ℝ) (hF : StronglyMeasurable[m] F)
    (hD : Integrable D μ) (hFD : Integrable (F*D) μ)
    (hzero : μ[D | m] =ᵐ[μ] 0) : ∫ ω, F ω * D ω ∂μ = 0 := by
  have he := condExp_mul_of_stronglyMeasurable_left hF hFD hD
  have hz : μ[F*D | m] =ᵐ[μ] 0 := by
    filter_upwards [he,hzero] with ω he hz
    simpa [hz] using he
  have hi := integral_congr_ae hz
  rw [integral_condExp hm] at hi
  simpa using hi

private lemma martingale_subgaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℕ)
    (ℱ : Filtration (Fin (T+1)) ‹MeasurableSpace Ω›) (Z : Fin (T+1) → Ω → ℝ)
    (B : ℝ) (hB : 0 < B) (hZ : Martingale Z ℱ μ)
    (hdiff : ∀ t : Fin T, ∀ᵐ ω ∂μ, |Z t.succ ω-Z t.castSucc ω| ≤ B) :
    HasSubgaussianMGF (fun ω => Z (Fin.last T) ω-Z 0 ω)
      (NNReal.mk ((T:ℝ)*B^2) (by positivity)) μ := by
  let M : Fin (T+1) → Ω → ℝ := fun t ω => Z t ω-Z 0 ω
  have hbound (i : Fin (T+1)) : ∀ᵐ ω ∂μ, |M i ω| ≤ (i.val:ℝ)*B := by
    induction i using Fin.induction with
    | zero => simp [M]
    | succ i ih =>
      filter_upwards [ih, hdiff i] with ω hω hdi
      have ha : |M i.succ ω| ≤ |Z i.succ ω-Z i.castSucc ω|+|M i.castSucc ω| := by
        simpa [M, sub_add_sub_cancel] using abs_add_le (Z i.succ ω-Z i.castSucc ω) (Z i.castSucc ω-Z 0 ω)
      simp only [Fin.val_castSucc] at hω
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      nlinarith
  have hMmeas (i : Fin (T+1)) : StronglyMeasurable[ℱ i] (M i) :=
    (hZ.stronglyAdapted i).sub ((hZ.stronglyAdapted 0).mono (ℱ.mono (Fin.zero_le i)))
  have hInt (i : Fin (T+1)) (s : ℝ) : Integrable (fun ω => Real.exp (s*M i ω)) μ := by
    apply Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable
      (((hMmeas i).mono (ℱ.le i)).aestronglyMeasurable.const_mul s))
      (Real.exp (|s| * ((i.val:ℝ)*B)))
    exact exp_norm_bound μ (M i) _ s (hbound i)
  have hmgf (s : ℝ) (i : Fin (T+1)) :
      (∫ ω, Real.exp (s*M i ω) ∂μ) ≤ Real.exp ((i.val:ℝ)*(s*B)^2/2) := by
    induction i using Fin.induction with
    | zero => simp [M]
    | succ i ih =>
      let F : Ω → ℝ := fun ω => Real.exp (s*M i.castSucc ω)
      let D : Ω → ℝ := Z i.succ-Z i.castSucc
      have hD : Integrable D μ := (hZ.integrable i.succ).sub (hZ.integrable i.castSucc)
      have hFm : StronglyMeasurable[ℱ i.castSucc] F := Real.continuous_exp.comp_stronglyMeasurable ((hMmeas i.castSucc).const_mul s)
      have hFD : Integrable (F*D) μ := hD.bdd_mul
        ((hFm.mono (ℱ.le i.castSucc)).aestronglyMeasurable)
        (exp_norm_bound μ (M i.castSucc) _ s (hbound i.castSucc))
      have hDzero : μ[D | ℱ i.castSucc] =ᵐ[μ] 0 := by
        have hc := condExp_sub (hZ.integrable i.succ) (hZ.integrable i.castSucc) (ℱ i.castSucc)
        have hz := hZ.condExp_ae_eq (show i.castSucc ≤ i.succ by change i.val ≤ i.val+1; omega)
        rw [condExp_of_stronglyMeasurable (ℱ.le i.castSucc) (hZ.stronglyAdapted i.castSucc)
          (hZ.integrable i.castSucc)] at hc
        filter_upwards [hc,hz] with ω hc hz
        simpa [D,hz] using hc
      have hweighted := weighted_cond_zero μ (ℱ.le i.castSucc) F D hFm hD hFD hDzero
      have hFi : Integrable F μ := hInt i.castSucc s
      have hdom : ∀ᵐ ω ∂μ, Real.exp (s*M i.succ ω) ≤
          Real.cosh (s*B)*F ω+(Real.sinh (s*B)/B)*(F ω*D ω) := by
        filter_upwards [hdiff i] with ω hdi
        have h := mul_le_mul_of_nonneg_left (exp_chord B (D ω) s hB hdi) (Real.exp_pos (s*M i.castSucc ω)).le
        have hsplit : M i.succ ω=M i.castSucc ω+D ω := by dsimp [M,D]; ring
        rw [hsplit, mul_add, Real.exp_add]
        dsimp [F] at h ⊢
        convert! h using 1 <;> ring
      have hstep := integral_mono_ae (hInt i.succ s)
        ((hFi.const_mul _).add (hFD.const_mul _)) hdom
      simp only [Pi.add_apply, Pi.mul_apply] at hstep
      have hadd := integral_add (hFi.const_mul (Real.cosh (s*B)))
        (hFD.const_mul (Real.sinh (s*B)/B))
      simp only [Pi.mul_apply] at hadd
      rw [hadd, integral_const_mul, integral_const_mul, hweighted, mul_zero, add_zero] at hstep
      have hcosh := mul_le_mul_of_nonneg_right (Real.cosh_le_exp_half_sq (s*B))
        (integral_nonneg (μ := μ) (fun ω => (Real.exp_pos (s*M i.castSucc ω)).le))
      have hih := mul_le_mul_of_nonneg_left ih (Real.exp_pos ((s*B)^2/2)).le
      calc
        _ ≤ Real.exp ((s*B)^2/2) * Real.exp ((i.val:ℝ)*(s*B)^2/2) := hstep.trans (hcosh.trans hih)
        _ = _ := by rw [← Real.exp_add]; congr 1; simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]; ring
  refine ⟨hInt (Fin.last T), ?_⟩
  intro s
  have h := hmgf s (Fin.last T)
  convert! h using 1
  simp only [Fin.val_last, NNReal.coe_mk]
  congr 1
  ring



theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (T : ℕ) (ℱ : MeasureTheory.Filtration (Fin (T + 1)) ‹MeasurableSpace Ω›)
    (Z : Fin (T + 1) → Ω → ℝ) (B ε : ℝ)
    (hT : 1 ≤ T) (hB : 0 < B) (hε : 0 ≤ ε)
    (hZ : MeasureTheory.Martingale Z ℱ μ)
    (hZint : ∀ t : Fin (T + 1), MeasureTheory.Integrable (Z t) μ)
    (hdiff : ∀ t : Fin T,
      ∀ᵐ ω ∂μ, |Z ⟨t.val + 1, Nat.succ_lt_succ t.isLt⟩ ω -
        Z ⟨t.val, Nat.lt_trans t.isLt (Nat.lt_succ_self T)⟩ ω| ≤ B) :
    μ.real {ω | ε ≤ Z (Fin.last T) ω - Z ⟨0, Nat.zero_lt_succ T⟩ ω} ≤
      Real.exp (-(ε ^ 2) / (2 * B ^ 2 * (T : ℝ))) ∧
    μ.real {ω | ε ≤ Z ⟨0, Nat.zero_lt_succ T⟩ ω - Z (Fin.last T) ω} ≤
      Real.exp (-(ε ^ 2) / (2 * B ^ 2 * (T : ℝ))) := by
  have hd : ∀ t : Fin T, ∀ᵐ ω ∂μ, |Z t.succ ω-Z t.castSucc ω| ≤ B := hdiff
  have h := martingale_subgaussian μ T ℱ Z B hB hZ hd
  constructor
  · convert! h.measure_ge_le hε using 1
    simp only [NNReal.coe_mk]
    congr 1
    congr 1
    ring
  · have hn := h.neg.measure_ge_le hε
    simp only [Pi.neg_apply, neg_sub] at hn
    convert! hn using 1
    simp only [NNReal.coe_mk]
    congr 1
    congr 1
    ring

