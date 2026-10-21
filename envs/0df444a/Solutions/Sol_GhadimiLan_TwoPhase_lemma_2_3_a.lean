-- Prove2me | solution 1 for GhadimiLan.TwoPhase.lemma_2_3_a
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T11:35:30.020641+00:00
-- url     : https://prove2.me/submissions/22a2431e-c414-430f-909e-a063a7d2f1f5

import Mathlib
import Definitions.Def_GhadimiLan_TwoPhase_Model
/- Formalization: Alexander Richard Towell (queelius), with OpenAI Codex assistance.
   Mathematics: Saeed Ghadimi and Guanghui Lan, arXiv:1309.5549v1, Lemma 2.3(a).
   Platform formulation and positive-variance repair: mikedeng1.
   Statement review: Shuze Chen. No mathematical novelty or human proof-review claim. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
namespace MartingaleVariance
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
lemma inner_integrable {μ : Measure Ω} {f g : Ω → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω => ⟪f ω,g ω⟫_ℝ) μ := by
  exact (hf.norm.integrable_mul hg.norm).mono' (hf.1.inner hg.1)
    (Filter.Eventually.of_forall fun ω => norm_inner_le_norm (f ω) (g ω))
lemma orthogonal (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (f g : Ω → E) (hf : StronglyMeasurable[m] f) (hf2 : MemLp f 2 μ)
    (hg2 : MemLp g 2 μ) (hg : Integrable g μ)
    (hz : μ[g|m] =ᵐ[μ] fun _ => 0) : (∫ ω, ⟪f ω,g ω⟫_ℝ ∂μ) = 0 := by
  let : MeasurableSpace Ω := mΩ
  have h := condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hf (inner_integrable hf2 hg2) hg
  change μ[fun ω => ⟪f ω,g ω⟫_ℝ|m] =ᵐ[μ] fun ω => ⟪f ω, μ[g|m] ω⟫_ℝ at h
  have he : μ[fun ω => ⟪f ω,g ω⟫_ℝ|m] =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards [h,hz] with ω hω hzω
    simpa only [hzω,inner_zero_right] using hω
  rw [← integral_condExp hm, integral_congr_ae he]
  simp
end MartingaleVariance

theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (ζ : ℕ → Ω → GhadimiLan.RSG.E n) (σi : ℕ → ℝ)
    (hadapt : ∀ i, 1 ≤ i → StronglyMeasurable[ℱ i] (ζ i))
    (hint : ∀ i, 1 ≤ i → Integrable (ζ i) μ)
    (hzero : ∀ i, 1 ≤ i → condExp (ℱ (i - 1)) μ (ζ i) =ᵐ[μ] (fun _ => (0 : GhadimiLan.RSG.E n)))
    (hvarint : ∀ i, 1 ≤ i → Integrable (fun ω => ‖ζ i ω‖ ^ 2) μ)
    (hvar : ∀ i, 1 ≤ i → (∫ ω, ‖ζ i ω‖ ^ 2 ∂μ) ≤ σi i ^ 2) :
    ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => ‖∑ i ∈ Finset.Icc 1 N, ζ i ω‖ ^ 2) μ ∧
      (∫ ω, ‖∑ i ∈ Finset.Icc 1 N, ζ i ω‖ ^ 2 ∂μ) ≤ ∑ i ∈ Finset.Icc 1 N, σi i ^ 2 ∧
      (0 < (∑ i ∈ Finset.Icc 1 N, σi i ^ 2) → ∀ lam : ℝ, 0 ≤ lam →
          μ {ω | lam * (∑ i ∈ Finset.Icc 1 N, σi i ^ 2) ≤ ‖∑ i ∈ Finset.Icc 1 N, ζ i ω‖ ^ 2} ≤
              (ENNReal.ofReal lam)⁻¹) := by
  classical
  have hlp (i : ℕ) (hi : 1 ≤ i) : MemLp (ζ i) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (hint i hi).1).2 (hvarint i hi)
  have hort (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) :
      (∫ ω, ⟪ζ i ω,ζ j ω⟫_ℝ ∂μ) = 0 := by
    have hj : 1 ≤ j := by omega
    exact MartingaleVariance.orthogonal μ (ℱ.le (j-1)) (ζ i) (ζ j)
      ((hadapt i hi).mono (ℱ.mono (by omega))) (hlp i hi) (hlp j hj) (hint j hj) (hzero j hj)
  intro N _
  let S := Finset.Icc 1 N
  have hl (i : ℕ) (hi : i ∈ S) : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hpair (i : ℕ) (hi : i ∈ S) (j : ℕ) (hj : j ∈ S) :
      Integrable (fun ω => ⟪ζ i ω,ζ j ω⟫_ℝ) μ :=
    MartingaleVariance.inner_integrable (hlp i (hl i hi)) (hlp j (hl j hj))
  have hsum := memLp_finsetSum S (fun i hi => hlp i (hl i hi))
  have hsint : Integrable (fun ω => ‖∑ i ∈ S, ζ i ω‖ ^ 2) μ := hsum.integrable_norm_pow (by decide)
  have hexact : (∫ ω, ‖∑ i ∈ S, ζ i ω‖ ^ 2 ∂μ) = ∑ i ∈ S, ∫ ω, ‖ζ i ω‖ ^ 2 ∂μ := by
    simp_rw [← real_inner_self_eq_norm_sq, sum_inner, inner_sum]
    rw [integral_finsetSum S (fun i hi => integrable_finsetSum S (fun j hj => hpair i hi j hj))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum S (fun j hj => hpair i hi j hj),Finset.sum_eq_single i]
    · intro j hj hji
      rcases lt_or_gt_of_ne hji with h|h
      · convert hort j i (hl j hj) h using 1
        simp only [real_inner_comm]
      · exact hort i j (hl i hi) h
    · intro h
      exact (h hi).elim
  have hb : (∫ ω, ‖∑ i ∈ S, ζ i ω‖ ^ 2 ∂μ) ≤ ∑ i ∈ S, σi i ^ 2 := by
    rw [hexact]
    exact Finset.sum_le_sum fun i hi => hvar i (hl i hi)
  refine ⟨hsint,hb,?_⟩
  intro hB lam hlam
  by_cases hzero : lam = 0
  · simp [hzero]
  have hpos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hzero)
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => sq_nonneg ‖∑ i ∈ S, ζ i ω‖) hsint
    (lam*(∑ i ∈ S, σi i ^ 2))
  have hr : μ.real {ω | lam * (∑ i ∈ S, σi i ^ 2) ≤ ‖∑ i ∈ S, ζ i ω‖ ^ 2} ≤ lam⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hpos).2
    have hle := hm.trans hb
    nlinarith
  have he := ENNReal.ofReal_le_ofReal hr
  rw [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_inv_of_pos hpos] at he
  exact he
