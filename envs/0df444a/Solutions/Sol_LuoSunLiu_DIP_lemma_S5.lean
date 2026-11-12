-- Prove2me | solution 1 for LuoSunLiu.DIP.lemma_S5
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T04:24:16.268604+00:00
-- url     : https://prove2.me/submissions/bb3d2bca-52df-4add-bfc2-3d6c14daa081

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_LuoSunLiu_DIP_PLB
import Theorems.Thm_BanditAlgorithm_self_normalized_martingale_bound
import Theorems.Thm_LuoSunLiu_DIP_lemma_S3

set_option autoImplicit false

section Helpers

open MeasureTheory ProbabilityTheory Matrix LuoSunLiu.DIP

private lemma self_normalized_martingale_bound_univ
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (ℱ : Filtration ℕ mΩ)
    (A : ℕ → Ω → Fin d → ℝ) (η : ℕ → Ω → ℝ)
    (hA : ∀ t : ℕ, Measurable[ℱ t] (A (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (hB_meas : MeasurableSet {ω : Ω | ∃ t : ℕ,
        2 * Real.log (1 / δ)
            + Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam A t ω).det / lam ^ d)
          ≤ BanditAlgorithm.selfNormalizedSum d η A t ω ⬝ᵥ
              (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
                BanditAlgorithm.selfNormalizedSum d η A t ω}) :
    P.real {ω : Ω | ∃ t : ℕ,
        2 * Real.log (1 / δ)
            + Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam A t ω).det / lam ^ d)
          ≤ BanditAlgorithm.selfNormalizedSum d η A t ω ⬝ᵥ
              (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
                BanditAlgorithm.selfNormalizedSum d η A t ω} ≤ δ := by
  obtain ⟨s, hs_meas, ⟨e⟩⟩ := MeasureTheory.exists_subset_real_measurableEquiv Ω
  let Ω' : Type := ↥s
  have : StandardBorelSpace Ω' := hs_meas.standardBorel
  let P' : Measure Ω' := P.map e
  have : IsProbabilityMeasure P' := Measure.isProbabilityMeasure_map e.measurable.aemeasurable
  let ℱ' : Filtration ℕ (inferInstance : MeasurableSpace Ω') :=
    { seq := fun t => MeasurableSpace.map e (ℱ t)
      mono' := fun _ _ hij _ hS => ℱ.mono hij _ hS
      le' := fun t S hS => by
        have hpre : MeasurableSet (e ⁻¹' S) := ℱ.le t _ hS
        simpa using e.symm.measurable hpre }
  let A' : ℕ → Ω' → Fin d → ℝ := fun t ω' => A t (e.symm ω')
  let η' : ℕ → Ω' → ℝ := fun t ω' => η t (e.symm ω')
  have hA' : ∀ t : ℕ, Measurable[ℱ' t] (A' (t + 1)) := by
    intro t U hU
    change MeasurableSet[ℱ t] (e ⁻¹' ((A' (t + 1)) ⁻¹' U))
    have hpre : e ⁻¹' ((A' (t + 1)) ⁻¹' U) = (A (t + 1)) ⁻¹' U := by
      ext ω; simp [A']
    rw [hpre]
    exact hA t hU
  have hη' : ∀ t : ℕ, Measurable[ℱ' (t + 1)] (η' (t + 1)) := by
    intro t U hU
    change MeasurableSet[ℱ (t + 1)] (e ⁻¹' ((η' (t + 1)) ⁻¹' U))
    have hpre : e ⁻¹' ((η' (t + 1)) ⁻¹' U) = (η (t + 1)) ⁻¹' U := by
      ext ω; simp [η']
    rw [hpre]
    exact hη t hU
  have hsg' : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ' t) (ℱ'.le t) (η' (t + 1)) 1 P' := by
    intro t
    have hη'_amb : Measurable (η' (t + 1)) := (hη' t).mono (ℱ'.le (t + 1)) le_rfl
    have hint' : ∀ r : ℝ, Integrable (fun ω' => Real.exp (r * η' (t + 1) ω')) P' := by
      intro r
      have hmeas : Measurable (fun ω' : Ω' => Real.exp (r * η' (t + 1) ω')) :=
        Real.measurable_exp.comp (measurable_const.mul hη'_amb)
      rw [integrable_map_measure hmeas.aestronglyMeasurable e.measurable.aemeasurable]
      have hcomp : ((fun ω' : Ω' => Real.exp (r * η' (t + 1) ω')) ∘ e) =
          (fun ω : Ω => Real.exp (r * η (t + 1) ω)) := by
        funext ω; simp [η']
      rw [hcomp]
      exact (hsg t).integrable_exp_mul r
    refine ProbabilityTheory.Kernel.HasSubgaussianMGF.of_rat ?_ ?_
    · intro r
      rw [ProbabilityTheory.condExpKernel_comp_trim (ℱ'.le t)]
      exact hint' r
    · intro q
      let f' : Ω' → ℝ := fun ω' => Real.exp ((q : ℝ) * η' (t + 1) ω')
      let f : Ω → ℝ := fun ω => Real.exp ((q : ℝ) * η (t + 1) ω)
      let C : ℝ := Real.exp (((1 : NNReal) : ℝ) * (q : ℝ) ^ 2 / 2)
      have hf'_meas : Measurable f' :=
        Real.measurable_exp.comp (measurable_const.mul hη'_amb)
      have hf'_int : Integrable f' P' := hint' q
      have hf_int : Integrable f P := (hsg t).integrable_exp_mul q
      have : IsFiniteMeasure (P'.trim (ℱ'.le t)) := isFiniteMeasure_trim (ℱ'.le t)
      have : IsFiniteMeasure (P.trim (ℱ.le t)) := isFiniteMeasure_trim (ℱ.le t)
      have hce_le : P'[f' | ℱ' t] ≤ᵐ[P'.trim (ℱ'.le t)] fun _ => C := by
        refine ae_le_of_forall_setIntegral_le
          (Integrable.trim (ℱ'.le t) integrable_condExp stronglyMeasurable_condExp)
          (integrable_const C) ?_
        intro S hS _
        have hS_amb : MeasurableSet S := ℱ'.le t S hS
        have hS_pre : MeasurableSet[ℱ t] (e ⁻¹' S) := hS
        calc
          ∫ ω' in S, P'[f' | ℱ' t] ω' ∂(P'.trim (ℱ'.le t))
              = ∫ ω' in S, P'[f' | ℱ' t] ω' ∂P' :=
                (setIntegral_trim (ℱ'.le t) stronglyMeasurable_condExp hS).symm
          _ = ∫ ω' in S, f' ω' ∂P' := setIntegral_condExp (ℱ'.le t) hf'_int hS
          _ = ∫ ω in e ⁻¹' S, f ω ∂P := by
                simpa [f', f, η'] using
                  setIntegral_map hS_amb hf'_meas.aestronglyMeasurable e.measurable.aemeasurable
          _ = ∫ ω in e ⁻¹' S, P[f | ℱ t] ω ∂P :=
                (setIntegral_condExp (ℱ.le t) hf_int hS_pre).symm
          _ ≤ ∫ ω in e ⁻¹' S, C ∂P :=
                setIntegral_mono_ae_restrict integrable_condExp.integrableOn
                  (integrable_const C).integrableOn
                  (ae_restrict_of_ae ((hsg t).ae_condExp_le q))
          _ = ∫ ω' in S, C ∂P' := by
                symm
                have hc_meas : Measurable (fun _ : Ω' => C) := measurable_const
                simpa using setIntegral_map hS_amb hc_meas.aestronglyMeasurable
                  e.measurable.aemeasurable
          _ = ∫ ω' in S, C ∂(P'.trim (ℱ'.le t)) :=
                setIntegral_trim (ℱ'.le t) stronglyMeasurable_const hS
      have hkern := ProbabilityTheory.condExp_ae_eq_trim_integral_condExpKernel (ℱ'.le t) hf'_int
      filter_upwards [hce_le, hkern] with ω' hle hkeq
      simpa [ProbabilityTheory.mgf, f', C, hkeq] using hle
  have hbound' :=
    BanditAlgorithm.self_normalized_martingale_bound ℱ' A' η' hA' hη' hsg' hlam hδ
  let B : Set Ω := {ω : Ω | ∃ t : ℕ,
      2 * Real.log (1 / δ)
          + Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam A t ω).det / lam ^ d)
        ≤ BanditAlgorithm.selfNormalizedSum d η A t ω ⬝ᵥ
            (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
              BanditAlgorithm.selfNormalizedSum d η A t ω}
  let B' : Set Ω' := {ω' : Ω' | ∃ t : ℕ,
      2 * Real.log (1 / δ)
          + Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam A' t ω').det / lam ^ d)
        ≤ BanditAlgorithm.selfNormalizedSum d η' A' t ω' ⬝ᵥ
            (BanditAlgorithm.regularizedDesignMatrix d lam A' t ω')⁻¹ *ᵥ
              BanditAlgorithm.selfNormalizedSum d η' A' t ω'}
  have hBB' : B' = e.symm ⁻¹' B := rfl
  have hB'_meas : MeasurableSet B' := by
    rw [hBB']
    exact e.symm.measurable hB_meas
  have hpreB : e ⁻¹' B' = B := by
    rw [hBB']
    ext ω
    simp
  have hP_eq : P.real B = P'.real B' := by
    simp [Measure.real, P', Measure.map_apply e.measurable hB'_meas, hpreB]
  rw [hP_eq]
  exact hbound'

private lemma vecMulVec_eq_diagonal_of_oneSparse {d : ℕ} {a : Fin d → ℝ} (ha : IsOneSparse a) :
    vecMulVec a a = Matrix.diagonal (fun i => a i ^ 2) := by
  obtain ⟨k, c, _, rfl⟩ := ha
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [vecMulVec_apply, sq]
  · simp only [vecMulVec_apply, Matrix.diagonal_apply, hij, ↓reduceIte]
    by_cases hik : i = k
    · subst hik
      have hjk : j ≠ i := Ne.symm hij
      simp [hjk]
    · simp [Pi.single_apply, hik]

private lemma regDesign_eq_diagonal {d : ℕ} {Ω : Type*} (lam : ℝ) (A : ℕ → Ω → Fin d → ℝ)
    (m : ℕ) (ω : Ω) (hA : ∀ s : ℕ, 1 ≤ s → IsOneSparse (A s ω)) :
    BanditAlgorithm.regularizedDesignMatrix d lam A m ω =
      Matrix.diagonal (fun i => lam + ∑ s ∈ Finset.range m, A (s + 1) ω i ^ 2) := by
  unfold BanditAlgorithm.regularizedDesignMatrix
  have h1 : lam • (1 : Matrix (Fin d) (Fin d) ℝ) = Matrix.diagonal (fun _ => lam) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hsum : (∑ s ∈ Finset.range m, vecMulVec (A (s + 1) ω) (A (s + 1) ω)) =
      ∑ s ∈ Finset.range m, Matrix.diagonal (fun i => A (s + 1) ω i ^ 2) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    exact vecMulVec_eq_diagonal_of_oneSparse (hA (s + 1) (Nat.succ_pos s))
  rw [h1, hsum]
  ext i j
  by_cases hij : i = j <;> simp [hij, Matrix.sum_apply]

private lemma inv_diagonal_pos {d : ℕ} (v : Fin d → ℝ) (hv : ∀ i, 0 < v i) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun i => (v i)⁻¹) := by
  rw [Matrix.inv_diagonal]
  let u : (Fin d → ℝ)ˣ :=
    ⟨v, fun i => (v i)⁻¹, funext fun i => mul_inv_cancel₀ (hv i).ne',
      funext fun i => inv_mul_cancel₀ (hv i).ne'⟩
  change Matrix.diagonal (Ring.inverse (u : Fin d → ℝ)) = _
  rw [Ring.inverse_unit]
  rfl

private lemma dot_diag_mulVec {d : ℕ} (v x : Fin d → ℝ) :
    x ⬝ᵥ Matrix.diagonal v *ᵥ x = ∑ i, v i * x i ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma mNorm_diag_add_le {d : ℕ} (v x y : Fin d → ℝ) (hv : ∀ i, 0 ≤ v i) :
    mNorm (Matrix.diagonal v) (x + y) ≤
      mNorm (Matrix.diagonal v) x + mNorm (Matrix.diagonal v) y := by
  unfold mNorm
  rw [dot_diag_mulVec, dot_diag_mulVec, dot_diag_mulVec]
  let a : Fin d → ℝ := fun i => Real.sqrt (v i) * x i
  let b : Fin d → ℝ := fun i => Real.sqrt (v i) * y i
  have ha2 : ∑ i, v i * x i ^ 2 = ∑ i, a i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc
      v i * x i ^ 2 = (Real.sqrt (v i)) ^ 2 * x i ^ 2 := by rw [Real.sq_sqrt (hv i)]
      _ = a i ^ 2 := by ring
  have hb2 : ∑ i, v i * y i ^ 2 = ∑ i, b i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    calc
      v i * y i ^ 2 = (Real.sqrt (v i)) ^ 2 * y i ^ 2 := by rw [Real.sq_sqrt (hv i)]
      _ = b i ^ 2 := by ring
  have hab2 : ∑ i, v i * (x + y) i ^ 2 = ∑ i, (a i + b i) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    calc
      v i * (x i + y i) ^ 2 = (Real.sqrt (v i)) ^ 2 * (x i + y i) ^ 2 := by
        rw [Real.sq_sqrt (hv i)]
      _ = (a i + b i) ^ 2 := by ring
  rw [ha2, hb2, hab2]
  have hcs_sq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hA_nonneg : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB_nonneg : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcs : ∑ i, a i * b i ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
    by_cases hpos : 0 ≤ ∑ i, a i * b i
    · rw [← Real.sqrt_mul hA_nonneg, ← Real.sqrt_sq hpos]
      exact Real.sqrt_le_sqrt hcs_sq
    · exact (le_of_lt (not_le.mp hpos)).trans
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hsum_le : ∑ i, (a i + b i) ^ 2 ≤
      (Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2)) ^ 2 := by
    have hexp1 : ∑ i, (a i + b i) ^ 2 =
        (∑ i, a i ^ 2) + 2 * (∑ i, a i * b i) + (∑ i, b i ^ 2) := by
      have : ∀ i, (a i + b i) ^ 2 = a i ^ 2 + 2 * (a i * b i) + b i ^ 2 := fun i => by ring
      simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hexp2 : (Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2)) ^ 2 =
        (∑ i, a i ^ 2) + 2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2)) +
          (∑ i, b i ^ 2) := by
      calc
        (Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2)) ^ 2
            = (Real.sqrt (∑ i, a i ^ 2)) ^ 2 +
                2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2)) +
                (Real.sqrt (∑ i, b i ^ 2)) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hA_nonneg, Real.sq_sqrt hB_nonneg]
    linarith
  calc
    Real.sqrt (∑ i, (a i + b i) ^ 2)
        ≤ Real.sqrt ((Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2)) ^ 2) :=
          Real.sqrt_le_sqrt hsum_le
    _ = Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2) :=
          Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end Helpers

open MeasureTheory ProbabilityTheory Matrix LuoSunLiu.DIP in
theorem solution {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (ξ : ℕ → Ω → Fin d → ℝ) (𝒜 : ℕ → Ω → Finset (Fin d → ℝ)) (A : ℕ → Ω → Fin d → ℝ)
    (Z η : ℕ → Ω → ℝ) (C1 amax lam δ : ℝ)
    (hPLB : IsPLBModel P ℱ ξ 𝒜 A Z η 1) (hCond2 : Condition2 ξ C1)
    (hCond3 : Condition3 𝒜 amax) (hC1 : 0 ≤ C1) (hamax : 0 < amax) (hlam : 0 < lam)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ E : Set Ω, MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ P E ∧
      ∀ ω ∈ E, ∀ t : ℕ, 2 ≤ t →
        mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω)
            (shadowParam A ξ t ω - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ≤
          C1 * Real.sqrt (lam * d) +
            Real.sqrt (2 * Real.log (1 / δ) +
              d * Real.log ((d * lam + ((t : ℝ) - 1) * amax ^ 2) / (d * lam))) := by
  have hA_sparse : ∀ (ω : Ω) (s : ℕ), 1 ≤ s → IsOneSparse (A s ω) := by
    intro ω s hs
    exact (hCond3 s hs ω (A s ω) ((hPLB s hs).1 ω).1).1
  have hA_norm : ∀ (ω : Ω) (s : ℕ), 1 ≤ s → ∑ i : Fin d, A s ω i ^ 2 ≤ amax ^ 2 := by
    intro ω s hs
    have hsq_le := (hCond3 s hs ω (A s ω) ((hPLB s hs).1 ω).1).2
    have hsum_nonneg : 0 ≤ ∑ i : Fin d, A s ω i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc
      ∑ i : Fin d, A s ω i ^ 2 = (Real.sqrt (∑ i : Fin d, A s ω i ^ 2)) ^ 2 :=
        (Real.sq_sqrt hsum_nonneg).symm
      _ ≤ amax ^ 2 := sq_le_sq' (by linarith [Real.sqrt_nonneg (∑ i : Fin d, A s ω i ^ 2)]) hsq_le
  have hA_meas : ∀ s : ℕ, Measurable[ℱ s] (A (s + 1)) := by
    intro s
    simpa using (hPLB (s + 1) (Nat.succ_pos s)).2.1
  have hη_meas : ∀ s : ℕ, Measurable[ℱ (s + 1)] (η (s + 1)) := by
    intro s
    exact (hPLB (s + 1) (Nat.succ_pos s)).2.2.1
  have hsg : ∀ s : ℕ, HasCondSubgaussianMGF (ℱ s) (ℱ.le s) (η (s + 1)) 1 P := by
    intro s
    simpa using (hPLB (s + 1) (Nat.succ_pos s)).2.2.2
  have hA_amb : ∀ s : ℕ, Measurable (A (s + 1)) :=
    fun s => (hA_meas s).mono (ℱ.le s) le_rfl
  have hη_amb : ∀ s : ℕ, Measurable (η (s + 1)) :=
    fun s => (hη_meas s).mono (ℱ.le (s + 1)) le_rfl
  let vDiag : ℕ → Ω → Fin d → ℝ :=
    fun m ω i => lam + ∑ s ∈ Finset.range m, A (s + 1) ω i ^ 2
  have hv_pos : ∀ (m : ℕ) (ω : Ω) (i : Fin d), 0 < vDiag m ω i := by
    intro m ω i
    exact add_pos_of_pos_of_nonneg hlam (Finset.sum_nonneg fun s _ => sq_nonneg _)
  have hV_eq : ∀ (m : ℕ) (ω : Ω),
      BanditAlgorithm.regularizedDesignMatrix d lam A m ω = Matrix.diagonal (vDiag m ω) :=
    fun m ω => regDesign_eq_diagonal lam A m ω (hA_sparse ω)
  have hV_det : ∀ (m : ℕ) (ω : Ω),
      (BanditAlgorithm.regularizedDesignMatrix d lam A m ω).det = ∏ i : Fin d, vDiag m ω i := by
    intro m ω
    rw [hV_eq m ω, Matrix.det_diagonal]
  have hV_inv : ∀ (m : ℕ) (ω : Ω),
      (BanditAlgorithm.regularizedDesignMatrix d lam A m ω)⁻¹ =
        Matrix.diagonal (fun i => (vDiag m ω i)⁻¹) := by
    intro m ω
    rw [hV_eq m ω, inv_diagonal_pos (vDiag m ω) (hv_pos m ω)]
  let B : Set Ω := {ω : Ω | ∃ m : ℕ,
      2 * Real.log (1 / δ)
          + Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam A m ω).det / lam ^ d)
        ≤ BanditAlgorithm.selfNormalizedSum d η A m ω ⬝ᵥ
            (BanditAlgorithm.regularizedDesignMatrix d lam A m ω)⁻¹ *ᵥ
              BanditAlgorithm.selfNormalizedSum d η A m ω}
  have hB_meas : MeasurableSet B := by
    have hB_eq : B = ⋃ m : ℕ, {ω : Ω |
        2 * Real.log (1 / δ) + Real.log ((∏ i : Fin d, vDiag m ω i) / lam ^ d) ≤
          ∑ i : Fin d, (vDiag m ω i)⁻¹ * (BanditAlgorithm.selfNormalizedSum d η A m ω i) ^ 2} := by
      ext ω
      simp only [B, Set.mem_iUnion, Set.mem_ofPred_eq]
      refine exists_congr fun m => ?_
      rw [hV_det m ω, hV_inv m ω, dot_diag_mulVec]
    rw [hB_eq]
    refine MeasurableSet.iUnion fun m => ?_
    have hv_meas : ∀ i : Fin d, Measurable (fun ω : Ω => vDiag m ω i) := by
      intro i
      refine measurable_const.add (Finset.measurable_sum (Finset.range m) fun s _ => ?_)
      exact ((measurable_pi_apply i).comp (hA_amb s)).pow_const 2
    have hS_meas : ∀ i : Fin d,
        Measurable (fun ω : Ω => BanditAlgorithm.selfNormalizedSum d η A m ω i) := by
      intro i
      have hSi : (fun ω : Ω => BanditAlgorithm.selfNormalizedSum d η A m ω i) =
          fun ω : Ω => ∑ s ∈ Finset.range m, η (s + 1) ω * A (s + 1) ω i := by
        funext ω
        simp [BanditAlgorithm.selfNormalizedSum]
      rw [hSi]
      refine Finset.measurable_sum (Finset.range m) fun s _ => ?_
      exact (hη_amb s).mul ((measurable_pi_apply i).comp (hA_amb s))
    have hL : Measurable (fun ω : Ω =>
        2 * Real.log (1 / δ) + Real.log ((∏ i : Fin d, vDiag m ω i) / lam ^ d)) :=
      measurable_const.add
        (Real.measurable_log.comp
          ((Finset.measurable_prod Finset.univ fun i _ => hv_meas i).div_const (lam ^ d)))
    have hR : Measurable (fun ω : Ω =>
        ∑ i : Fin d, (vDiag m ω i)⁻¹ * (BanditAlgorithm.selfNormalizedSum d η A m ω i) ^ 2) :=
      Finset.measurable_sum Finset.univ fun i _ =>
        (hv_meas i).inv.mul ((hS_meas i).pow_const 2)
    exact measurableSet_le hL hR
  have hPB_real : P.real B ≤ δ :=
    self_normalized_martingale_bound_univ ℱ A η hA_meas hη_meas hsg hlam hδ hB_meas
  refine ⟨Bᶜ, hB_meas.compl, ?_, ?_⟩
  · have hPB : P B ≤ ENNReal.ofReal δ :=
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P B) (le_of_lt hδ.1)).2 hPB_real
    rw [prob_compl_eq_one_sub hB_meas]
    calc
      ENNReal.ofReal (1 - δ) = ENNReal.ofReal 1 - ENNReal.ofReal δ :=
        ENNReal.ofReal_sub 1 (le_of_lt hδ.1)
      _ = 1 - ENNReal.ofReal δ := by simp
      _ ≤ 1 - P B := tsub_le_tsub_left hPB 1
  · intro ω hω t ht
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, t = m + 1 := ⟨t - 1, (Nat.sub_add_cancel (by omega)).symm⟩
    have hm1 : 1 ≤ m := by omega
    have htsub : (m + 1) - 1 = m := Nat.add_sub_cancel m 1
    rw [htsub]
    have hnotB : ¬ (2 * Real.log (1 / δ) +
          Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam A m ω).det / lam ^ d) ≤
        BanditAlgorithm.selfNormalizedSum d η A m ω ⬝ᵥ
          (BanditAlgorithm.regularizedDesignMatrix d lam A m ω)⁻¹ *ᵥ
            BanditAlgorithm.selfNormalizedSum d η A m ω) := by
      intro hle
      exact hω ⟨m, hle⟩
    have hSN_le : BanditAlgorithm.selfNormalizedSum d η A m ω ⬝ᵥ
          (BanditAlgorithm.regularizedDesignMatrix d lam A m ω)⁻¹ *ᵥ
            BanditAlgorithm.selfNormalizedSum d η A m ω ≤
        2 * Real.log (1 / δ) +
          Real.log ((BanditAlgorithm.regularizedDesignMatrix d lam A m ω).det / lam ^ d) :=
      le_of_lt (not_le.mp hnotB)
    let V := BanditAlgorithm.regularizedDesignMatrix d lam A m ω
    let S := BanditAlgorithm.selfNormalizedSum d η A m ω
    let u := shadowParam A ξ (m + 1) ω -
      V⁻¹ *ᵥ ∑ s ∈ Finset.Icc 1 m, (A s ω ⬝ᵥ ξ s ω) • A s ω
    have hdecomp : shadowParam A ξ (m + 1) ω -
        BanditAlgorithm.regularizedLeastSquares d lam A Z m ω = u + (-(V⁻¹ *ᵥ S)) := by
      unfold BanditAlgorithm.regularizedLeastSquares
      change shadowParam A ξ (m + 1) ω - V⁻¹ *ᵥ ∑ s ∈ Finset.range m, Z (s + 1) ω • A (s + 1) ω =
        u + (-(V⁻¹ *ᵥ S))
      have hZsum : ∑ s ∈ Finset.range m, Z (s + 1) ω • A (s + 1) ω =
          (∑ s ∈ Finset.Icc 1 m, (A s ω ⬝ᵥ ξ s ω) • A s ω) + S := by
        have h1 : ∑ s ∈ Finset.range m, Z (s + 1) ω • A (s + 1) ω =
            (∑ s ∈ Finset.range m, (A (s + 1) ω ⬝ᵥ ξ (s + 1) ω) • A (s + 1) ω) + S := by
          unfold S BanditAlgorithm.selfNormalizedSum
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun s _ => ?_
          have hZs := ((hPLB (s + 1) (Nat.succ_pos s)).1 ω).2
          rw [hZs, dotProduct_comm, add_smul]
        have h2 : ∑ s ∈ Finset.Icc 1 m, (A s ω ⬝ᵥ ξ s ω) • A s ω =
            ∑ s ∈ Finset.range m, (A (s + 1) ω ⬝ᵥ ξ (s + 1) ω) • A (s + 1) ω := by
          have hIcc : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := rfl
          rw [hIcc, Finset.sum_Ico_eq_sum_range]
          simp [add_comm]
        rw [h1, h2]
      rw [hZsum, Matrix.mulVec_add]
      ext i
      simp [u]
      ring
    have htri : mNorm V (shadowParam A ξ (m + 1) ω -
          BanditAlgorithm.regularizedLeastSquares d lam A Z m ω) ≤
        mNorm V u + mNorm V (-(V⁻¹ *ᵥ S)) := by
      rw [hdecomp]
      simpa [V, hV_eq m ω] using
        mNorm_diag_add_le (vDiag m ω) u (-(V⁻¹ *ᵥ S)) (fun i => le_of_lt (hv_pos m ω i))
    have hu_bound : mNorm V u ≤ C1 * Real.sqrt (lam * d) := by
      refine LuoSunLiu.DIP.lemma_S3 A ξ C1 lam hC1 hlam m ω ?_ ?_
      · intro s hs
        exact hA_sparse ω s (Finset.mem_Icc.mp hs).1
      · intro s hs i
        exact hCond2 s (Finset.mem_Icc.mp hs).1 ω i
    have hS_quad : (-(V⁻¹ *ᵥ S)) ⬝ᵥ V *ᵥ (-(V⁻¹ *ᵥ S)) = S ⬝ᵥ V⁻¹ *ᵥ S := by
      have hVi : V⁻¹ = Matrix.diagonal (fun i => (vDiag m ω i)⁻¹) := hV_inv m ω
      have hVd : V = Matrix.diagonal (vDiag m ω) := hV_eq m ω
      rw [hVi, hVd, dot_diag_mulVec, dot_diag_mulVec]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.neg_apply, Matrix.mulVec_diagonal]
      have hvi_ne : vDiag m ω i ≠ 0 := (hv_pos m ω i).ne'
      field_simp [hvi_ne]
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
    have hdlam_pos : 0 < (d : ℝ) * lam := mul_pos hd_pos hlam
    let M : ℝ := ((d : ℝ) * lam + (m : ℝ) * amax ^ 2) / ((d : ℝ) * lam)
    have hM_pos : 0 < M := by
      refine div_pos ?_ hdlam_pos
      exact add_pos_of_pos_of_nonneg hdlam_pos
        (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg amax))
    have hdet_log : Real.log (V.det / lam ^ d) ≤ (d : ℝ) * Real.log M := by
      have hdet_ratio : V.det / lam ^ d = ∏ i : Fin d, (vDiag m ω i / lam) := by
        rw [hV_det m ω]
        have hlam_pow : (lam ^ d : ℝ) = ∏ _ : Fin d, lam := by simp
        rw [hlam_pow, ← Finset.prod_div_distrib]
      rw [hdet_ratio, Real.log_prod fun i _ => (div_pos (hv_pos m ω i) hlam).ne']
      have hpt : ∀ i : Fin d, Real.log (vDiag m ω i / lam) ≤
          Real.log M + (vDiag m ω i / lam / M - 1) := by
        intro i
        have hxi_pos : 0 < vDiag m ω i / lam := div_pos (hv_pos m ω i) hlam
        have hlog_split : Real.log (vDiag m ω i / lam) =
            Real.log M + Real.log (vDiag m ω i / lam / M) := by
          rw [← Real.log_mul hM_pos.ne' (div_pos hxi_pos hM_pos).ne',
            mul_div_cancel₀ _ hM_pos.ne']
        linarith [Real.log_le_sub_one_of_pos (div_pos hxi_pos hM_pos)]
      have hsum_log : ∑ i : Fin d, Real.log (vDiag m ω i / lam) ≤
          (d : ℝ) * Real.log M + ((∑ i : Fin d, (vDiag m ω i / lam)) / M - (d : ℝ)) := by
        calc
          ∑ i : Fin d, Real.log (vDiag m ω i / lam)
              ≤ ∑ i : Fin d, (Real.log M + (vDiag m ω i / lam / M - 1)) :=
                Finset.sum_le_sum fun i _ => hpt i
          _ = (d : ℝ) * Real.log M + ((∑ i : Fin d, (vDiag m ω i / lam)) / M - (d : ℝ)) := by
                simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
      have hsum_v : ∑ i : Fin d, vDiag m ω i ≤ (d : ℝ) * lam + (m : ℝ) * amax ^ 2 := by
        have hv_expand : ∑ i : Fin d, vDiag m ω i =
            (d : ℝ) * lam + ∑ s ∈ Finset.range m, ∑ i : Fin d, A (s + 1) ω i ^ 2 := by
          simp only [vDiag, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.sum_comm]
        rw [hv_expand]
        have hinner : ∑ s ∈ Finset.range m, ∑ i : Fin d, A (s + 1) ω i ^ 2 ≤
            ∑ _ ∈ Finset.range m, amax ^ 2 :=
          Finset.sum_le_sum fun s _ => hA_norm ω (s + 1) (Nat.succ_pos s)
        simpa using add_le_add_right hinner ((d : ℝ) * lam)
      have hsum_x : ∑ i : Fin d, (vDiag m ω i / lam) ≤ (d : ℝ) * M := by
        rw [← Finset.sum_div]
        have hdM : (d : ℝ) * M = ((d : ℝ) * lam + (m : ℝ) * amax ^ 2) / lam := by
          dsimp [M]
          field_simp [hd_pos.ne', hlam.ne']
        rw [hdM]
        exact div_le_div_of_nonneg_right hsum_v (le_of_lt hlam)
      have hdiv_le : (∑ i : Fin d, (vDiag m ω i / lam)) / M ≤ (d : ℝ) :=
        (div_le_iff₀ hM_pos).2 hsum_x
      linarith
    have hS_norm_le : mNorm V (-(V⁻¹ *ᵥ S)) ≤
        Real.sqrt (2 * Real.log (1 / δ) + (d : ℝ) * Real.log M) := by
      unfold mNorm
      rw [hS_quad]
      exact Real.sqrt_le_sqrt (hSN_le.trans (add_le_add_right hdet_log (2 * Real.log (1 / δ))))
    have hm_cast : (((m + 1 : ℕ) : ℝ) - 1) = (m : ℝ) := by push_cast; ring
    rw [hm_cast]
    exact htri.trans (add_le_add hu_bound hS_norm_le)
