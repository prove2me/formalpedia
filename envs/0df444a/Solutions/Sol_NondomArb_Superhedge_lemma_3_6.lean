-- Prove2me | solution 1 for NondomArb.Superhedge.lemma_3_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T07:16:21.118749+00:00
-- url     : https://prove2.me/submissions/310a9585-0e40-4888-aabb-99795b9328ae

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic
import Definitions.Def_NondomArb_Superhedge_OnePeriod
import Theorems.Thm_NondomArb_Superhedge_lemma_3_3
open MeasureTheory Filter Topology NondomArb.Superhedge.OnePeriod
open NondomArb.Superhedge

namespace L36Aux

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

lemma theta_integrable {Pset : Set (Measure Ω)} {ΔS : Ω → (Fin d → ℝ)} {f : Ω → ℝ}
    {R : Measure Ω} (hR : R ∈ Theta Pset ΔS f) (hΔS : Measurable ΔS) (hf : Measurable f) :
    Integrable ΔS R ∧ Integrable f R := by
  obtain ⟨_, _, hfin⟩ := hR
  refine ⟨⟨hΔS.aestronglyMeasurable, ?_⟩, ⟨hf.aestronglyMeasurable, ?_⟩⟩
  · refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfin
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by linarith [abs_nonneg (f ω)])
  · refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hfin
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (by linarith [norm_nonneg (ΔS ω)])

/-- `μ` is dominated by some element of `𝒫`. -/
def Dom (Pset : Set (Measure Ω)) (μ : Measure Ω) : Prop := ∃ P ∈ Pset, μ ≪ P

lemma dom_add {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset) {μ₁ μ₂ : Measure Ω}
    (h1 : Dom Pset μ₁) (h2 : Dom Pset μ₂) : Dom Pset (μ₁ + μ₂) := by
  obtain ⟨P1, hP1, hac1⟩ := h1
  obtain ⟨P2, hP2, hac2⟩ := h2
  have h12 : (1/2 : NNReal) ≤ 1 := by norm_num
  refine ⟨(1/2 : NNReal) • P1 + (1 - 1/2 : NNReal) • P2, hP.2.2 P1 hP1 P2 hP2 _ h12, ?_⟩
  intro s hs
  have hne : (1 - 1/2 : NNReal) ≠ 0 := by
    rw [ne_eq, tsub_eq_zero_iff_le, not_le]; norm_num
  simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    add_eq_zero, mul_eq_zero, ENNReal.coe_eq_zero] at hs ⊢
  refine ⟨hac1 ?_, hac2 ?_⟩
  · rcases hs.1 with h0 | h0
    · norm_num at h0
    · exact h0
  · rcases hs.2 with h0 | h0
    · exact absurd h0 hne
    · exact h0

lemma dom_smul {Pset : Set (Measure Ω)} {μ : Measure Ω} (h : Dom Pset μ) (c : NNReal) :
    Dom Pset (c • μ) := by
  obtain ⟨P, hP0, hac⟩ := h
  refine ⟨P, hP0, fun s hs => ?_⟩
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [hac hs, mul_zero]

lemma dom_sum {Pset : Set (Measure Ω)} (hP : IsConvexModelSet Pset) {ι : Type*}
    (s : Finset ι) (μ : ι → Measure Ω) (h : ∀ i ∈ s, Dom Pset (μ i)) :
    Dom Pset (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨P, hP0⟩ := hP.1
    exact ⟨P, hP0, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact dom_add hP (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- From `0 ∈ ri C`: a ball of the linear span around the origin lies in `C`. -/
lemma ball_of_ri (C : Set (Fin d → ℝ)) (h : (0 : Fin d → ℝ) ∈ intrinsicInterior ℝ C) :
    ∃ ε > 0, ∀ v ∈ Submodule.span ℝ C, ‖v‖ < ε → v ∈ C := by
  obtain ⟨y, hy, hy0⟩ := mem_intrinsicInterior.mp h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hy)
  have h0A : (0 : Fin d → ℝ) ∈ affineSpan ℝ C := hy0 ▸ y.2
  have hspan : ∀ v ∈ Submodule.span ℝ C, v ∈ affineSpan ℝ C := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact subset_affineSpan ℝ C hx
    | zero => exact h0A
    | add x z _ _ hx hz =>
      have := AffineSubspace.vadd_mem_of_mem_direction
        (AffineSubspace.vsub_mem_direction hx h0A) hz
      simpa [vsub_eq_sub, vadd_eq_add] using this
    | smul a x _ hx =>
      have := AffineSubspace.vadd_mem_of_mem_direction
        (Submodule.smul_mem _ a (AffineSubspace.vsub_mem_direction hx h0A)) h0A
      simpa [vsub_eq_sub, vadd_eq_add] using this
  refine ⟨ε, hε, fun v hv hvε => ?_⟩
  have hmem : (⟨v, hspan v hv⟩ : affineSpan ℝ C) ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, Subtype.dist_eq, hy0, dist_zero_right]; exact hvε
  exact hball hmem

end L36Aux

namespace L36Aux

variable {Ω : Type*} [MeasurableSpace Ω]

lemma mix_integrable {F : Type*} [NormedAddCommGroup F] {ι : Type*} (s : Finset ι)
    {g : Ω → F} {P1 P2 : ι → Measure Ω} (w1 w2 : ι → NNReal)
    (h1 : ∀ i, Integrable g (P1 i)) (h2 : ∀ i, Integrable g (P2 i)) :
    Integrable g (∑ i ∈ s, (w1 i • P1 i + w2 i • P2 i)) :=
  integrable_finsetSum_measure.mpr fun i _ =>
    ((h1 i).smul_measure_nnreal).add_measure ((h2 i).smul_measure_nnreal)

lemma mix_integral' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {ι : Type*} (s : Finset ι) {g : Ω → F} {P1 P2 : ι → Measure Ω} (w1 w2 : ι → NNReal)
    (h1 : ∀ i, Integrable g (P1 i)) (h2 : ∀ i, Integrable g (P2 i)) :
    ∫ ω, g ω ∂ (∑ i ∈ s, (w1 i • P1 i + w2 i • P2 i)) =
      ∑ i ∈ s, (w1 i • ∫ ω, g ω ∂ (P1 i) + w2 i • ∫ ω, g ω ∂ (P2 i)) := by
  rw [integral_finsetSum_measure fun i _ =>
    ((h1 i).smul_measure_nnreal).add_measure ((h2 i).smul_measure_nnreal)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_add_measure (h1 i).smul_measure_nnreal (h2 i).smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]

end L36Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω))
    (hP : IsConvexModelSet Pset) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) (hΔS : Measurable ΔS)
    (hNA : NA Pset ΔS) (f : Ω → ℝ) (hf : Measurable f) :
    ∃ c : ℝ, 0 < c ∧ ∀ R ∈ Theta Pset ΔS f, ∃ Q ∈ MartMeasures Pset ΔS, Integrable f Q ∧
      |∫ ω, f ω ∂ Q - ∫ ω, f ω ∂ R| ≤ c * (1 + |∫ ω, f ω ∂ R|) * ‖∫ ω, ΔS ω ∂ R‖ := by
  classical
  set Γ : Set (Fin d → ℝ) := {v | ∃ R ∈ Theta Pset ΔS f, v = ∫ ω, ΔS ω ∂ R} with hΓ
  obtain ⟨ε, hε, hball⟩ := L36Aux.ball_of_ri Γ (lemma_3_3 Pset hP ΔS hΔS hNA f hf).1
  set V := Submodule.span ℝ Γ with hV
  let b := Module.finBasis ℝ V
  set k := Module.finrank ℝ V with hk
  have hbpos : ∀ i, 0 < ‖((b i : V) : Fin d → ℝ)‖ := fun i => by
    rw [norm_pos_iff]; intro h; exact b.ne_zero i (Subtype.ext h)
  let sc : Fin k → ℝ := fun i => ε / (2 * ‖((b i : V) : Fin d → ℝ)‖)
  have hsc : ∀ i, 0 < sc i := fun i => div_pos hε (mul_pos two_pos (hbpos i))
  have hpt : ∀ i (σ : ℝ), |σ| = 1 → (σ * sc i) • ((b i : V) : Fin d → ℝ) ∈ Γ := by
    intro i σ hσ
    refine hball _ (Submodule.smul_mem _ _ (b i).2) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_mul, hσ, one_mul, abs_of_pos (hsc i)]
    have : sc i * ‖((b i : V) : Fin d → ℝ)‖ = ε / 2 := by
      simp only [sc]; field_simp; exact div_self (hbpos i).ne'
    rw [this]; linarith
  choose Pp hPp hPpv using fun i => hpt i 1 (by norm_num)
  choose Pm hPm hPmv using fun i => hpt i (-1) (by norm_num)
  have hPpi := fun i => L36Aux.theta_integrable (hPp i) hΔS hf
  have hPmi := fun i => L36Aux.theta_integrable (hPm i) hΔS hf
  let co : Fin k → V →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  let K : ℝ := ∑ i, ‖co i‖ / sc i
  let F : ℝ := ∑ i, (|∫ ω, f ω ∂ (Pp i)| + |∫ ω, f ω ∂ (Pm i)|)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => div_nonneg (co i).opNorm_nonneg (hsc i).le
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => by positivity
  have hFp : ∀ i, |∫ ω, f ω ∂ (Pp i)| ≤ F := fun i => by
    have := Finset.single_le_sum (f := fun i => |∫ ω, f ω ∂ (Pp i)| + |∫ ω, f ω ∂ (Pm i)|)
      (fun i _ => by positivity) (Finset.mem_univ i)
    linarith [abs_nonneg (∫ ω, f ω ∂ (Pm i))]
  have hFm : ∀ i, |∫ ω, f ω ∂ (Pm i)| ≤ F := fun i => by
    have := Finset.single_le_sum (f := fun i => |∫ ω, f ω ∂ (Pp i)| + |∫ ω, f ω ∂ (Pm i)|)
      (fun i _ => by positivity) (Finset.mem_univ i)
    linarith [abs_nonneg (∫ ω, f ω ∂ (Pp i))]
  refine ⟨K * (F + 1) + 1, by positivity, fun R hR => ?_⟩
  obtain ⟨hRΔS, hRf⟩ := L36Aux.theta_integrable hR hΔS hf
  have hvΓ : ∫ ω, ΔS ω ∂ R ∈ Γ := ⟨R, hR, rfl⟩
  let v : V := ⟨-∫ ω, ΔS ω ∂ R, V.neg_mem (Submodule.subset_span hvΓ)⟩
  let β : Fin k → ℝ := fun i => b.coord i v / sc i
  have hrepr : ∑ i, β i • (sc i • ((b i : V) : Fin d → ℝ)) = -∫ ω, ΔS ω ∂ R := by
    have h1 := b.sum_repr v
    have h2 := congrArg (fun x : V => (x : Fin d → ℝ)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    rw [← show ((v : V) : Fin d → ℝ) = -∫ ω, ΔS ω ∂ R from rfl, ← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    congr 1
    simp only [β, Module.Basis.coord_apply]
    field_simp [(hsc i).ne']
  let wp : Fin k → NNReal := fun i => Real.toNNReal (β i)
  let wm : Fin k → NNReal := fun i => Real.toNNReal (-β i)
  have hwpm : ∀ i, (wp i : ℝ) - (wm i : ℝ) = β i := fun i => by
    simp only [wp, wm, Real.coe_toNNReal']
    rcases le_total 0 (β i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hwpm' : ∀ i, (wp i : ℝ) + (wm i : ℝ) = |β i| := fun i => by
    simp only [wp, wm, Real.coe_toNNReal']
    rcases le_total 0 (β i) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
    · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  let μ : Measure Ω := ∑ i, (wp i • Pp i + wm i • Pm i)
  let mN : NNReal := ∑ i, (wp i + wm i)
  have hμuniv : μ Set.univ = (mN : ENNReal) := by
    simp only [μ, mN, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply,
      Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [ENNReal.ofNNReal_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    haveI := (hPp i).1; haveI := (hPm i).1
    rw [measure_univ, measure_univ, mul_one, mul_one, ENNReal.coe_add]
  let Q : Measure Ω := (1 + mN)⁻¹ • (R + μ)
  have hμΔS : Integrable ΔS μ :=
    L36Aux.mix_integrable _ wp wm (fun i => (hPpi i).1) (fun i => (hPmi i).1)
  have hμf : Integrable f μ :=
    L36Aux.mix_integrable _ wp wm (fun i => (hPpi i).2) (fun i => (hPmi i).2)
  have hQΔS : Integrable ΔS Q := (hRΔS.add_measure hμΔS).smul_measure_nnreal
  have hQf : Integrable f Q := (hRf.add_measure hμf).smul_measure_nnreal
  have hμΔSint : ∫ ω, ΔS ω ∂ μ = -∫ ω, ΔS ω ∂ R := by
    rw [L36Aux.mix_integral' _ wp wm (fun i => (hPpi i).1) (fun i => (hPmi i).1), ← hrepr]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hPpv i, ← hPmv i, NNReal.smul_def, NNReal.smul_def, smul_smul, smul_smul, ← add_smul,
      smul_smul]
    congr 1
    rw [← hwpm i]; ring
  have hm1 : (1 + mN : NNReal) ≠ 0 := by positivity
  refine ⟨Q, ⟨⟨?_⟩, ?_, hQΔS, ?_⟩, hQf, ?_⟩
  · haveI := hR.1
    simp only [Q, Measure.smul_apply, Measure.add_apply, measure_univ, hμuniv,
      ENNReal.smul_def, smul_eq_mul]
    rw [← ENNReal.coe_one, ← ENNReal.coe_add, ← ENNReal.coe_mul, inv_mul_cancel₀ hm1]
  · refine L36Aux.dom_smul (L36Aux.dom_add hP hR.2.1 (L36Aux.dom_sum hP _ _ fun i _ =>
      L36Aux.dom_add hP (L36Aux.dom_smul (hPp i).2.1 _) (L36Aux.dom_smul (hPm i).2.1 _))) _
  · simp only [Q]
    rw [integral_smul_nnreal_measure, integral_add_measure hRΔS hμΔS, hμΔSint, add_neg_cancel,
      smul_zero]
  · -- the estimate
    set a := ∫ ω, f ω ∂ R with ha
    set N := ‖∫ ω, ΔS ω ∂ R‖ with hN
    set m : ℝ := (mN : ℝ) with hm
    have hm0 : 0 ≤ m := mN.2
    have hmsum : m = ∑ i, |β i| := by
      simp only [hm, mN, NNReal.coe_sum, NNReal.coe_add]
      exact Finset.sum_congr rfl fun i _ => hwpm' i
    set Ef := ∫ ω, f ω ∂ μ with hEf
    have hEf_eq : Ef = ∑ i, ((wp i : ℝ) * ∫ ω, f ω ∂ (Pp i) + (wm i : ℝ) * ∫ ω, f ω ∂ (Pm i)) := by
      rw [hEf, L36Aux.mix_integral' _ wp wm (fun i => (hPpi i).2) (fun i => (hPmi i).2)]
      simp only [NNReal.smul_def, smul_eq_mul]
    have hEf_le : |Ef| ≤ m * F := by
      rw [hEf_eq]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hm, show ((mN : ℝ)) = ∑ i, ((wp i : ℝ) + wm i) by simp [mN], Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, NNReal.abs_eq, NNReal.abs_eq, add_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hFp i) (wp i).2)
        (mul_le_mul_of_nonneg_left (hFm i) (wm i).2)
    have hm_le : m ≤ K * N := by
      rw [hmsum, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [β]
      rw [abs_div, abs_of_pos (hsc i), div_le_iff₀ (hsc i)]
      have h1 : |b.coord i v| ≤ ‖co i‖ * ‖v‖ := by
        have := (co i).le_opNorm v
        rwa [Real.norm_eq_abs] at this
      have h2 : ‖v‖ = N := by
        show ‖((v : V) : Fin d → ℝ)‖ = N
        simp [v, hN]
      rw [h2] at h1
      calc |b.coord i v| ≤ ‖co i‖ * N := h1
        _ = ‖co i‖ / sc i * N * sc i := by field_simp [(hsc i).ne']
    have hQint : ∫ ω, f ω ∂ Q = (1 + m)⁻¹ * (a + Ef) := by
      simp only [Q]
      rw [integral_smul_nnreal_measure, integral_add_measure hRf hμf, NNReal.smul_def,
        smul_eq_mul, NNReal.coe_inv, NNReal.coe_add, NNReal.coe_one]
    have h1m : 0 < 1 + m := by linarith
    have hdiff : ∫ ω, f ω ∂ Q - a = (Ef - m * a) / (1 + m) := by
      rw [hQint]; field_simp; ring
    have hN0 : 0 ≤ N := norm_nonneg _
    have hstep1 : |∫ ω, f ω ∂ Q - a| ≤ m * F + m * |a| := by
      rw [hdiff, abs_div, abs_of_pos h1m, div_le_iff₀ h1m]
      have : |Ef - m * a| ≤ m * F + m * |a| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hm0]
        linarith
      nlinarith [abs_nonneg a, abs_nonneg (Ef - m * a)]
    have hstep2 : m * F + m * |a| ≤ K * (F + 1) * (1 + |a|) * N := by
      have e1 : m * F + m * |a| ≤ m * ((F + 1) * (1 + |a|)) := by
        have : F + |a| ≤ (F + 1) * (1 + |a|) := by nlinarith [abs_nonneg a]
        nlinarith
      have e2 : m * ((F + 1) * (1 + |a|)) ≤ K * N * ((F + 1) * (1 + |a|)) :=
        mul_le_mul_of_nonneg_right hm_le (by positivity)
      nlinarith
    have hstep3 : K * (F + 1) * (1 + |a|) * N ≤ (K * (F + 1) + 1) * (1 + |a|) * N := by
      have : 0 ≤ (1 + |a|) * N := by positivity
      nlinarith
    linarith
