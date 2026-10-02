-- Prove2me | solution 1 for HighDimProb.QuadraticForms.bilinear_mgf_reduction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-01T17:11:32.545221+00:00
-- url     : https://prove2.me/submissions/0efd55e4-199c-472e-a329-75da2c449f94

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Real

-- Scalar MGF conversion adapted from Nickrobbins95's accepted General Hoeffding proof
-- (submission 565f5a69-62e2-4ba5-b641-a7dcb105f2ee).
namespace HansonWrightMGF

lemma hdpc_exp_le_add_exp_sq (x : ℝ) : exp x ≤ x + exp (x ^ 2) := by
  rcases le_or_gt |x| 1 with hx | hx
  · have h1 := Real.abs_exp_sub_one_sub_id_le hx
    have h2 := Real.add_one_le_exp (x ^ 2)
    have h3 := (abs_le.1 h1).2
    linarith
  · rcases le_or_gt 0 x with h0 | h0
    · have hx1 : 1 < x := by rwa [abs_of_nonneg h0] at hx
      have h4 : x ≤ x ^ 2 := by nlinarith
      have h5 := exp_le_exp.2 h4
      linarith
    · have hx1 : x < -1 := by
        rw [abs_of_neg h0] at hx; linarith
      have h4 : exp x ≤ 1 := Real.exp_le_one_iff.2 h0.le
      have h5 := Real.add_one_le_exp (x ^ 2)
      nlinarith

lemma hdpc_pt1 (l b σ : ℝ) :
    exp (l * (σ * b)) ≤ exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (b ^ 2) / 2) := by
  have h1 : l * (σ * b) ≤ l ^ 2 * σ ^ 2 / 2 + b ^ 2 / 2 := by
    nlinarith [sq_nonneg (l * σ - b)]
  have h2 : exp (b ^ 2 / 2) ≤ 1 / 2 + exp (b ^ 2) / 2 := by
    have hz : exp (b ^ 2) = exp (b ^ 2 / 2) ^ 2 := by rw [sq (exp _), ← exp_add]; ring_nf
    nlinarith [sq_nonneg (exp (b ^ 2 / 2) - 1)]
  calc exp (l * (σ * b)) ≤ exp (l ^ 2 * σ ^ 2 / 2 + b ^ 2 / 2) := exp_le_exp.2 h1
    _ = exp (l ^ 2 * σ ^ 2 / 2) * exp (b ^ 2 / 2) := exp_add _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (exp_pos _).le

lemma hdpc_pt2 (l b σ : ℝ) (hq : l ^ 2 * σ ^ 2 ≤ 1) :
    exp (l * (σ * b)) ≤ l * (σ * b) + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (b ^ 2) := by
  have h1 := hdpc_exp_le_add_exp_sq (l * (σ * b))
  have h2 : (l * (σ * b)) ^ 2 = l ^ 2 * σ ^ 2 * b ^ 2 + (1 - l ^ 2 * σ ^ 2) * 0 := by ring
  have hq0 : 0 ≤ l ^ 2 * σ ^ 2 := by positivity
  have h3 := convexOn_exp.2 (Set.mem_univ (b ^ 2)) (Set.mem_univ (0 : ℝ)) hq0 (sub_nonneg.2 hq)
    (by ring : l ^ 2 * σ ^ 2 + (1 - l ^ 2 * σ ^ 2) = 1)
  simp only [smul_eq_mul] at h3
  rw [h2] at h1
  rw [exp_zero] at h3
  linarith

lemma hdpc_subG {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y) (hmean : ∫ ω, Y ω ∂P = 0) (σ : ℝ) (hσ : 0 < σ)
    (hint : Integrable (fun ω => exp (Y ω ^ 2 / σ ^ 2)) P)
    (hle : ∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P ≤ 2) :
    HasSubgaussianMGF Y (2 * σ ^ 2).toNNReal P := by
  have hYσ : ∀ ω, σ * (Y ω / σ) = Y ω := fun ω => by field_simp
  have hYσ2 : ∀ ω, (Y ω / σ) ^ 2 = Y ω ^ 2 / σ ^ 2 := fun ω => div_pow _ _ _
  have hpt1 : ∀ l ω, exp (l * Y ω) ≤
      exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2) := by
    intro l ω
    have h := hdpc_pt1 l (Y ω / σ) σ
    rwa [hYσ, hYσ2] at h
  have hintE : ∀ l, Integrable (fun ω => exp (l * Y ω)) P := by
    intro l
    refine Integrable.mono' (((integrable_const (1 / 2 : ℝ)).add (hint.div_const 2)).const_mul
      (exp (l ^ 2 * σ ^ 2 / 2))) ((hY.const_mul l).exp.aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact hpt1 l ω
  have hYint : Integrable Y P := by
    refine Integrable.mono' (hint.const_mul σ) hY.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |Y ω / σ| ≤ exp ((Y ω / σ) ^ 2) := by
      nlinarith [sq_nonneg (|Y ω / σ| - 1 / 2), sq_abs (Y ω / σ),
        add_one_le_exp ((Y ω / σ) ^ 2)]
    rw [hYσ2, abs_div, abs_of_pos hσ, div_le_iff₀ hσ] at h1
    linarith [mul_comm σ (exp (Y ω ^ 2 / σ ^ 2))]
  refine ⟨hintE, fun l => ?_⟩
  have htarget : ((2 * σ ^ 2).toNNReal : ℝ) * l ^ 2 / 2 = l ^ 2 * σ ^ 2 := by
    rw [Real.coe_toNNReal _ (by positivity)]; ring
  rw [htarget, mgf]
  rcases le_or_gt (l ^ 2 * σ ^ 2) 1 with hq | hq
  · have hpt2 : ∀ ω, exp (l * Y ω) ≤
        l * Y ω + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2) := by
      intro ω
      have h := hdpc_pt2 l (Y ω / σ) σ hq
      rwa [hYσ, hYσ2] at h
    have hI1 : Integrable (fun ω => l * Y ω + (1 - l ^ 2 * σ ^ 2)) P :=
      (hYint.const_mul l).add (integrable_const _)
    have hI2 : Integrable (fun ω => l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2)) P := hint.const_mul _
    calc ∫ ω, exp (l * Y ω) ∂P
        ≤ ∫ ω, (l * Y ω + (1 - l ^ 2 * σ ^ 2) + l ^ 2 * σ ^ 2 * exp (Y ω ^ 2 / σ ^ 2)) ∂P :=
          integral_mono (hintE l) (hI1.add hI2) hpt2
      _ = l * ∫ ω, Y ω ∂P + (1 - l ^ 2 * σ ^ 2) +
            l ^ 2 * σ ^ 2 * ∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P := by
          rw [integral_add hI1 hI2, integral_add (hYint.const_mul l) (integrable_const _),
            integral_const_mul, integral_const_mul, integral_const]
          simp
      _ ≤ 1 + l ^ 2 * σ ^ 2 := by
          rw [hmean]
          have hq0 : 0 ≤ l ^ 2 * σ ^ 2 := by positivity
          nlinarith
      _ ≤ exp (l ^ 2 * σ ^ 2) := by linarith [add_one_le_exp (l ^ 2 * σ ^ 2)]
  · have hI : Integrable
        (fun ω => exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2)) P :=
      ((integrable_const (1 / 2 : ℝ)).add (hint.div_const 2)).const_mul _
    calc ∫ ω, exp (l * Y ω) ∂P
        ≤ ∫ ω, exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + exp (Y ω ^ 2 / σ ^ 2) / 2) ∂P :=
          integral_mono (hintE l) hI (hpt1 l)
      _ = exp (l ^ 2 * σ ^ 2 / 2) * (1 / 2 + (∫ ω, exp (Y ω ^ 2 / σ ^ 2) ∂P) / 2) := by
          rw [integral_const_mul, integral_add (integrable_const _) (hint.div_const 2),
            integral_const, integral_div]
          simp
      _ ≤ exp (l ^ 2 * σ ^ 2 / 2) * exp (l ^ 2 * σ ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
          have h1 := add_one_le_exp (1 / 2 : ℝ)
          have h2 : exp (1 / 2 : ℝ) ≤ exp (l ^ 2 * σ ^ 2 / 2) := exp_le_exp.2 (by linarith)
          linarith
      _ = exp (l ^ 2 * σ ^ 2) := by rw [← exp_add]; ring_nf

lemma hdpc_const_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : HasSubgaussianMGF Y c.toNNReal P) (r : ℝ) :
    HasSubgaussianMGF (fun ω => r * Y ω) (r ^ 2 * c).toNNReal P := by
  have h1 := h.const_mul r
  convert h1 using 1
  apply NNReal.eq
  rw [Real.coe_toNNReal _ (by positivity)]
  show r ^ 2 * c = r ^ 2 * (c.toNNReal : ℝ)
  rw [Real.coe_toNNReal _ hc]


end HansonWrightMGF


open MeasureTheory ProbabilityTheory Real HighDimProb.Concentration

namespace HansonWrightMGF

lemma subgaussianMGF_of_norm_bound {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY : Measurable Y) (hmean : ∫ ω, Y ω ∂P = 0)
    (hsg : ∃ s > 0, Integrable (fun ω => exp (Y ω ^ 2 / s ^ 2)) P ∧
      ∫ ω, exp (Y ω ^ 2 / s ^ 2) ∂P ≤ 2)
    {K : ℝ} (hK : 0 < K) (hnorm : subgaussianNorm P Y ≤ K) :
    HasSubgaussianMGF Y (8 * K ^ 2).toNNReal P := by
  obtain ⟨s0, hs0, hint0, hle0⟩ := hsg
  have hne : ({s : ℝ | 0 < s ∧ Integrable (fun ω => exp (Y ω ^ 2 / s ^ 2)) P ∧
      ∫ ω, exp (Y ω ^ 2 / s ^ 2) ∂P ≤ 2}).Nonempty := ⟨s0, hs0, hint0, hle0⟩
  have hlt : subgaussianNorm P Y < 2 * K := by linarith
  unfold subgaussianNorm at hlt
  obtain ⟨s, ⟨hs, hints, hles⟩, hs2⟩ := exists_lt_of_csInf_lt hne hlt
  have hmono : ∀ ω, exp (Y ω ^ 2 / (2 * K) ^ 2) ≤ exp (Y ω ^ 2 / s ^ 2) := fun ω =>
    exp_le_exp.2 (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (pow_le_pow_left₀ hs.le hs2.le 2))
  have hint2 : Integrable (fun ω => exp (Y ω ^ 2 / (2 * K) ^ 2)) P :=
    hints.mono' ((hY.pow_const 2).div_const _).exp.aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact hmono ω)
  have hle2 := (integral_mono hint2 hints hmono).trans hles
  have h := hdpc_subG P Y hY hmean (2 * K) (by positivity) hint2 hle2
  have heq : 2 * (2 * K) ^ 2 = 8 * K ^ 2 := by ring
  simpa only [heq] using h

lemma linear_mgf {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (hind : iIndepFun Y P) {K : ℝ}
    (hsub : ∀ j, HasSubgaussianMGF (Y j) (8 * K ^ 2).toNNReal P)
    (a : ι → ℝ) (l : ℝ) :
    Integrable (fun ω => exp (l * ∑ j, a j * Y j ω)) P ∧
      ∫ ω, exp (l * ∑ j, a j * Y j ω) ∂P ≤
        exp (4 * l ^ 2 * K ^ 2 * ∑ j, a j ^ 2) := by
  classical
  have hind' : iIndepFun (fun j ω => a j * Y j ω) P :=
    hind.comp (fun j x => a j * x) (fun _ => measurable_const.mul measurable_id)
  have hsub' : ∀ j ∈ (Finset.univ : Finset ι),
      HasSubgaussianMGF (fun ω => a j * Y j ω) (a j ^ 2 * (8 * K ^ 2)).toNNReal P :=
    fun j _ => hdpc_const_mul (by positivity) (hsub j) (a j)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind' hsub'
  refine ⟨hsum.integrable_exp_mul l, ?_⟩
  have hbound := hsum.mgf_le l
  have hcoef : ((∑ j, (a j ^ 2 * (8 * K ^ 2)).toNNReal : NNReal) : ℝ) =
      (∑ j, a j ^ 2) * (8 * K ^ 2) := by
    rw [NNReal.coe_sum]
    rw [Finset.sum_congr rfl (fun j _ => Real.coe_toNNReal _
      (by positivity : (0 : ℝ) ≤ a j ^ 2 * (8 * K ^ 2))), Finset.sum_mul]
  rw [mgf, hcoef] at hbound
  convert hbound using 1 <;> ring

end HansonWrightMGF


/-- Integrating out the independent subgaussian vector reduces a bilinear MGF to
an exponential moment of the squared Euclidean norm of the coefficient vector.
The integrability hypothesis on that moment also proves integrability on the left. -/
theorem solution {n m : ℕ} {Ω Ω' : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (X : Fin n → Ω → ℝ) (Y : Fin m → Ω' → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hind : iIndepFun Y Q) (hmean : ∀ j, ∫ ω, Y j ω ∂Q = 0)
    (hsg : ∀ j, ∃ s > 0, Integrable (fun ω => exp (Y j ω ^ 2 / s ^ 2)) Q ∧
      ∫ ω, exp (Y j ω ^ 2 / s ^ 2) ∂Q ≤ 2)
    (A : Matrix (Fin n) (Fin m) ℝ) {K : ℝ} (hK : 0 < K)
    (hnorm : ∀ j, HighDimProb.Concentration.subgaussianNorm Q (Y j) ≤ K)
    (l : ℝ)
    (hbound : Integrable (fun ω =>
      exp (4 * l ^ 2 * K ^ 2 * ∑ j, (∑ i, A i j * X i ω) ^ 2)) P) :
    Integrable (fun z : Ω × Ω' =>
      exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2)) (P.prod Q) ∧
    (∫ z : Ω × Ω', exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2) ∂P.prod Q) ≤
      ∫ ω, exp (4 * l ^ 2 * K ^ 2 * ∑ j, (∑ i, A i j * X i ω) ^ 2) ∂P := by
  classical
  have hsub := fun j => HansonWrightMGF.subgaussianMGF_of_norm_bound Q (Y j)
    (hY j) (hmean j) (hsg j) hK (hnorm j)
  have hrepr : ∀ x y, (∑ i, ∑ j, A i j * X i x * Y j y) =
      ∑ j, (∑ i, A i j * X i x) * Y j y := by
    intro x y
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  have hsection : ∀ x,
      Integrable (fun y => exp (l * ∑ i, ∑ j, A i j * X i x * Y j y)) Q ∧
      (∫ y, exp (l * ∑ i, ∑ j, A i j * X i x * Y j y) ∂Q) ≤
        exp (4 * l ^ 2 * K ^ 2 * ∑ j, (∑ i, A i j * X i x) ^ 2) := by
    intro x
    simp_rw [hrepr]
    exact HansonWrightMGF.linear_mgf Q Y hind hsub (fun j => ∑ i, A i j * X i x) l
  have hmeas : Measurable (fun z : Ω × Ω' =>
      exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2)) := by
    apply Measurable.exp
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    exact (measurable_const.mul ((hX i).comp measurable_fst)).mul
      ((hY j).comp measurable_snd)
  have hinner : Integrable (fun x =>
      ∫ y, exp (l * ∑ i, ∑ j, A i j * X i x * Y j y) ∂Q) P := by
    refine hbound.mono' hmeas.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable ?_
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => (exp_pos _).le))]
    exact (hsection x).2
  have hfull : Integrable (fun z : Ω × Ω' =>
      exp (l * ∑ i, ∑ j, A i j * X i z.1 * Y j z.2)) (P.prod Q) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun x => (hsection x).1), ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_pos (exp_pos _)] using hinner
  refine ⟨hfull, ?_⟩
  rw [integral_prod _ hfull]
  exact integral_mono hinner hbound (fun x => (hsection x).2)

