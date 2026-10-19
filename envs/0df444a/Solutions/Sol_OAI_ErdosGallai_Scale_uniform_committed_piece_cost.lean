-- Prove2me | solution 1 for OAI.ErdosGallai.Scale.uniform_committed_piece_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T02:06:55.887665+00:00
-- url     : https://prove2.me/submissions/00f28e0e-ef99-40ff-b02b-85ad3ef345da

import Mathlib
import Definitions.Def_CycleDecomposition
import Definitions.Def_OAIQWEGC000
import Theorems.Thm_OAI_ErdosGallai_lovasz_path_cycle_decomposition

section
-- module Solutions.OAIQW_ErdosGallai.Compat
namespace OAI.ErdosGallai
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434


end OAI.ErdosGallai
end

section
-- module Solutions.OAIQW_ErdosGallai.Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15

section

namespace ErdosGallai.Sampling
open MeasureTheory ProbabilityTheory Finset Real

section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

lemma exp_half_bound : exp (1 / 2 : ℝ) ≤ 5 / 3 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  nlinarith [exp_one_lt_d9, exp_pos (1 / 2 : ℝ)]

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

theorem bernoulli_sum_upper_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | 2 * p * s.card ≤ ∑ i ∈ s, X i ω} ≤ exp (-p * s.card / 3) := by
  have hInt : Integrable (fun ω => exp ((1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (2 * p * s.card)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(1 / 2 : ℝ) * (2 * p * s.card)) *
        exp ((s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (-p * s.card + (s.card : ℝ) * p * (exp (1 / 2 : ℝ) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

section ProductSamples
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

lemma sampleIndicator_measurable {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (v : V) : Measurable (sampleIndicator v) :=
  measurable_of_finite _

lemma sampleIndicator_values {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (v : V) (ω : V → Bool) :
    sampleIndicator v ω = 0 ∨ sampleIndicator v ω = 1 := by
  simp only [sampleIndicator]; split <;> simp

lemma sampleIndicator_indep {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) :
    iIndepFun (sampleIndicator (V := V)) (sampleMeasure V p) := by
  exact iIndepFun_pi (X := fun _ : V => fun b : Bool => if b then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma sampleIndicator_integral {V : Type cycleUniverse9} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) (v : V) :
    ∫ ω, sampleIndicator v ω ∂sampleMeasure V p = (p : ℝ) := by
  have hl := (measurePreserving_eval (fun _ : V => bernoulliMeasure true false p) v).hasLaw
  have hi := hl.integral_comp (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  simpa [sampleMeasure, sampleIndicator, integral_bernoulliMeasure] using hi

lemma sampleIndicator_sum (S : Finset V) (ω : V → Bool) :
    (∑ v ∈ S, sampleIndicator v ω) = ((S ∩ sampleVertices ω).card : ℝ) := by
  simp only [sampleIndicator,  Finset.sum_boole]
  congr 2
  ext v
  simp [sampleVertices]

lemma sample_card_lower_tail (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | ((S ∩ sampleVertices ω).card : ℝ) ≤ (p : ℝ) * S.card / 2} ≤
      exp (-(p : ℝ) * S.card / 8) := by
  simpa only [sampleIndicator_sum] using bernoulli_sum_lower_tail S
    sampleIndicator_measurable (sampleIndicator_indep p) sampleIndicator_values
    (p : ℝ) p.property.1 (sampleIndicator_integral p)

lemma sample_card_upper_tail (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | 2 * (p : ℝ) * S.card ≤ ((S ∩ sampleVertices ω).card : ℝ)} ≤
      exp (-(p : ℝ) * S.card / 3) := by
  simpa only [sampleIndicator_sum] using bernoulli_sum_upper_tail S
    sampleIndicator_measurable (sampleIndicator_indep p) sampleIndicator_values
    (p : ℝ) p.property.1 (sampleIndicator_integral p)

lemma sample_miss_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | Disjoint S (sampleVertices ω)} = (1 - (p : ℝ)) ^ S.card := by
  have heq : {ω | Disjoint S (sampleVertices ω)} =
      Set.univ.pi (fun v : V => if v ∈ S then {false} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    simp only [Finset.disjoint_left, sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v
      by_cases hv : v ∈ S
      · simp only [hv, ↓reduceIte, Set.mem_singleton_iff]
        cases hi : ω v <;> simp_all
      · simp [hv]
    · intro h v hv ht
      have := h v
      simp_all
  rw [heq, Measure.real, sampleMeasure, Measure.pi_pi, ENNReal.toReal_prod]
  have hpv (v : V) :
      ((bernoulliMeasure true false p) (if v ∈ S then {false} else Set.univ)).toReal =
        if v ∈ S then 1 - (p : ℝ) else 1 := by
    by_cases hv : v ∈ S
    · simp only [hv, ↓reduceIte]
      change (bernoulliMeasure true false p).real {false} = _
      exact bernoulliMeasure_real_apply_of_notMem_of_mem p (by simp) (by simp) (by simp)
    · simp [hv]
  simp_rw [hpv]
  simp

lemma sample_miss_bound (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | Disjoint S (sampleVertices ω)} ≤ exp (-(p : ℝ) * S.card) := by
  rw [sample_miss_probability]
  calc
    (1 - (p : ℝ)) ^ S.card ≤ exp (-(p : ℝ)) ^ S.card := by
      apply pow_le_pow_left₀ (sub_nonneg.mpr p.property.2)
      linarith [add_one_le_exp (-(p : ℝ))]
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma sample_contains_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p) {ω | S ⊆ sampleVertices ω} = ENNReal.ofReal (p : ℝ) ^ S.card := by
  have heq : {ω | S ⊆ sampleVertices ω} =
      Set.univ.pi (fun v : V => if v ∈ S then {true} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    simp only [Finset.subset_iff, sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h v
      by_cases hv : v ∈ S <;> simp_all
    · intro h v hv
      simpa [hv] using h v
  rw [heq, sampleMeasure, Measure.pi_pi]
  have hpv (v : V) :
      bernoulliMeasure true false p (if v ∈ S then {true} else Set.univ) =
        if v ∈ S then ENNReal.ofReal (p : ℝ) else 1 := by
    by_cases hv : v ∈ S
    · simp only [hv, ↓reduceIte]
      rw [bernoulliMeasure_apply_of_mem_of_notMem p (by simp) (by simp) (by simp)]
      exact ENNReal.ofReal_coe_nnreal.symm
    · simp [hv]
  simp_rw [hpv]
  simp

lemma sample_contains_real_probability (p : unitInterval) (S : Finset V) :
    (sampleMeasure V p).real {ω | S ⊆ sampleVertices ω} = (p : ℝ) ^ S.card := by
  rw [Measure.real, sample_contains_probability, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal p.property.1]

lemma sample_blocks_independent {I : Type cycleUniverse10} (p : unitInterval) (S : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepSet (fun i => {ω | S i ⊆ sampleVertices ω}) (sampleMeasure V p) := by
  classical
  rw [iIndepSet_iff_meas_biInter (fun _ => MeasurableSet.of_discrete)]
  intro t
  have heq : (⋂ i ∈ t, {ω | S i ⊆ sampleVertices ω}) =
      {ω | t.biUnion S ⊆ sampleVertices ω} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Finset.biUnion_subset]
  rw [heq, sample_contains_probability, Finset.card_biUnion]
  · simp_rw [sample_contains_probability]
    exact (Finset.prod_pow_eq_pow_sum t (fun i => (S i).card) _).symm
  · intro i _ j _ hij
    exact hS hij

lemma blockIndicator_values (S : Finset V) (ω : V → Bool) :
    blockIndicator S ω = 0 ∨ blockIndicator S ω = 1 := by
  classical
  by_cases h : S ⊆ sampleVertices ω <;> simp [blockIndicator, h]

lemma blockIndicator_integral (p : unitInterval) (S : Finset V) :
    ∫ ω, blockIndicator S ω ∂sampleMeasure V p = (p : ℝ) ^ S.card := by
  rw [blockIndicator, integral_indicator_const _ MeasurableSet.of_discrete,
    sample_contains_real_probability]
  simp

lemma sample_blocks_lower_tail {I : Type cycleUniverse11} (p : unitInterval) (S : I → Finset V)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) (d : ℕ)
    (hd : ∀ i, (S i).card = d) (t : Finset I) :
    (sampleMeasure V p).real {ω | (∑ i ∈ t, blockIndicator (S i) ω) ≤
      (p : ℝ) ^ d * t.card / 2} ≤ exp (-(p : ℝ) ^ d * t.card / 8) := by
  apply bernoulli_sum_lower_tail t (fun _ => measurable_of_finite _)
    (sample_blocks_independent p S hS).iIndepFun_indicator
    (fun i => blockIndicator_values (S i)) ((p : ℝ) ^ d) (pow_nonneg p.property.1 _)
  intro i
  change (∫ ω, blockIndicator (S i) ω ∂sampleMeasure V p) = _
  rw [blockIndicator_integral, hd]

lemma sample_weight_sum (A : Finset V) (w : V → ℝ) (ω : V → Bool) :
    (∑ v ∈ A ∩ sampleVertices ω, w v) = ∑ v ∈ A, w v * sampleIndicator v ω := by
  rw [← Finset.sum_ite_mem]
  apply Finset.sum_congr rfl
  intro v _
  simp only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and, sampleIndicator]
  split <;> simp_all

lemma sample_weight_integral (p : unitInterval) (A : Finset V) (w : V → ℝ) :
    ∫ ω, (∑ v ∈ A ∩ sampleVertices ω, w v) ∂sampleMeasure V p =
      (p : ℝ) * ∑ v ∈ A, w v := by
  simp_rw [sample_weight_sum]
  rw [integral_finsetSum A (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_const_mul, sampleIndicator_integral]
  rw [← Finset.sum_mul, mul_comm]

lemma nonnegative_markov_quarter {Ω : Type cycleUniverse12} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hi : Integrable X μ) (hn : ∀ ω, 0 ≤ X ω) {B : ℝ} (hB : 0 < B)
    (he : ∫ ω, X ω ∂μ ≤ B) : μ.real {ω | 4 * B < X ω} ≤ 1 / 4 := by
  have hb := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hn) hi (4 * B)
  have hm : μ.real {ω | 4 * B < X ω} ≤ μ.real {ω | 4 * B ≤ X ω} :=
    measureReal_mono (fun ω (h : 4 * B < X ω) => h.le)
  nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 4 * B)]

lemma sample_weight_markov (p : unitInterval) (hp : 0 < (p : ℝ))
    (A : Finset V) (w : V → ℝ) (hw : ∀ v ∈ A, 0 ≤ w v)
    {B : ℝ} (hB : 0 < B) (hs : ∑ v ∈ A, w v ≤ B) :
    (sampleMeasure V p).real {ω | 4 * (p : ℝ) * B < ∑ v ∈ A ∩ sampleVertices ω, w v} ≤
      1 / 4 := by
  have ht := nonnegative_markov_quarter (μ := sampleMeasure V p)
    (X := fun ω => ∑ v ∈ A ∩ sampleVertices ω, w v) Integrable.of_finite
    (fun ω => Finset.sum_nonneg (fun v hv => hw v (Finset.mem_inter.mp hv).1))
    (mul_pos hp hB) (by rw [sample_weight_integral]; exact mul_le_mul_of_nonneg_left hs hp.le)
  simpa only [mul_assoc] using ht

theorem exists_small_weighted_hitting_set {I : Type cycleUniverse13} (A : Finset V) (hA : A.Nonempty)
    (good : Finset I) (K : I → Finset V) (hKA : ∀ i ∈ good, K i ⊆ A)
    (w : V → ℝ) (hw : ∀ v ∈ A, 0 ≤ w v) {B d : ℝ}
    (hB : 0 < B) (hs : ∑ v ∈ A, w v ≤ B)
    (hd : ∀ i ∈ good, d ≤ (K i).card)
    (q : unitInterval) (hq : 0 < (q : ℝ))
    (hmiss : (good.card : ℝ) * exp (-(q : ℝ) * d) < 1 / 2) :
    ∃ S : Finset V, S ⊆ A ∧ (S.card : ℝ) ≤ 4 * (q : ℝ) * A.card ∧
      (∑ v ∈ S, w v) ≤ 4 * (q : ℝ) * B ∧ ∀ i ∈ good, ¬Disjoint (K i) S := by
  classical
  let μ := sampleMeasure V q
  let E₁ : Set (V → Bool) := {ω | 4 * (q : ℝ) * A.card < ((A ∩ sampleVertices ω).card : ℝ)}
  let E₂ : Set (V → Bool) := {ω | 4 * (q : ℝ) * B < ∑ v ∈ A ∩ sampleVertices ω, w v}
  let E₃ : Set (V → Bool) := ⋃ i ∈ good, {ω | Disjoint (K i) (sampleVertices ω)}
  have h₁ : μ.real E₁ ≤ 1 / 4 := by
    have ht := sample_weight_markov q hq A (fun _ => (1 : ℝ)) (by simp)
      (show (0 : ℝ) < A.card by exact_mod_cast hA.card_pos) (by simp)
    simpa [μ, E₁] using ht
  have h₂ : μ.real E₂ ≤ 1 / 4 := sample_weight_markov q hq A w hw hB hs
  have h₃ : μ.real E₃ < 1 / 2 := by
    calc
      μ.real E₃ ≤ ∑ i ∈ good, μ.real {ω | Disjoint (K i) (sampleVertices ω)} :=
        measureReal_biUnion_finset_le good _
      _ ≤ ∑ i ∈ good, exp (-(q : ℝ) * d) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sample_miss_bound q (K i)).trans (exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left (hd i hi) (neg_nonpos.mpr hq.le)))
      _ = (good.card : ℝ) * exp (-(q : ℝ) * d) := by simp
      _ < _ := hmiss
  have hf : μ.real (E₁ ∪ E₂ ∪ E₃) < 1 := by
    have ha := measureReal_union_le (μ := μ) (E₁ ∪ E₂) E₃
    have hb := measureReal_union_le (μ := μ) E₁ E₂
    linarith
  have hne : E₁ ∪ E₂ ∪ E₃ ≠ Set.univ := by
    intro h
    rw [h] at hf
    have hu : μ.real Set.univ = 1 := by simp [μ, Measure.real]
    linarith
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  have hn := hω
  simp only [Set.mem_union, not_or] at hn
  refine ⟨A ∩ sampleVertices ω, Finset.inter_subset_left, le_of_not_gt hn.1.1,
    le_of_not_gt hn.1.2, ?_⟩
  intro i hi hdj
  apply hn.2
  simp only [E₃, Set.mem_iUnion, Set.mem_ofPred_eq]
  refine ⟨i, hi, ?_⟩
  apply Finset.disjoint_left.mpr
  intro v hv hvs
  exact Finset.disjoint_left.mp hdj hv (Finset.mem_inter.mpr ⟨hKA i hi hv, hvs⟩)

end ProductSamples

section FiniteUnion
variable {Ω : Type cycleUniverse14} {I : Type cycleUniverse15} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma exists_avoiding_finite_events (s : Finset I) (E : I → Set Ω)
    (h : ∑ i ∈ s, μ.real (E i) < 1) : ∃ ω, ∀ i ∈ s, ω ∉ E i := by
  by_contra hn
  push Not at hn
  have cover : (⋃ i ∈ s, E i) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi, he⟩ := hn ω
    exact ⟨i, hi, he⟩
  have hu := measureReal_biUnion_finset_le (μ := μ) s E
  rw [cover] at hu
  have : μ.real Set.univ = 1 := by simp [Measure.real]
  rw [this] at hu
  linarith

end FiniteUnion
end ErdosGallai.Sampling
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.SamplingCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7

section
namespace ErdosGallai.Sampling
open Finset MeasureTheory ProbabilityTheory Real
open scoped symmDiff
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

lemma cutColor_lt {V : Type cycleUniverse2} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (e : V × V) : cutColor e < 2 * Fintype.card V := by
  have h₁ := (Fintype.equivFin V e.1).isLt
  have h₂ := (Fintype.equivFin V e.2).isLt
  dsimp [cutColor]
  omega

lemma same_cutColor_blocks_disjoint (A B : Finset V) (hAB : Disjoint A B)
    {e f : V × V} (he₁ : e.1 ∈ A) (he₂ : e.2 ∈ B)
    (hf₁ : f.1 ∈ A) (hf₂ : f.2 ∈ B) (hc : cutColor e = cutColor f) (hef : e ≠ f) :
    Disjoint ({e.1, e.2} : Finset V) {f.1, f.2} := by
  have h₁ : e.1 ≠ f.1 := by
    intro h
    have ht : e.2 = f.2 := (Fintype.equivFin V).injective (Fin.ext (by
      dsimp [cutColor] at hc
      rw [h] at hc
      omega))
    exact hef (Prod.ext h ht)
  have h₂ : e.2 ≠ f.2 := by
    intro h
    have ht : e.1 = f.1 := (Fintype.equivFin V).injective (Fin.ext (by
      dsimp [cutColor] at hc
      rw [h] at hc
      omega))
    exact hef (Prod.ext ht h)
  have h₃ : e.1 ≠ f.2 := fun h => Finset.disjoint_left.mp hAB he₁ (h ▸ hf₂)
  have h₄ : e.2 ≠ f.1 := fun h => Finset.disjoint_left.mp hAB hf₁ (h ▸ he₂)
  simp [Finset.disjoint_left, h₁, h₂, h₃, h₄]

lemma blockIndicator_sum_card (E : Finset (V × V)) (ω : V → Bool) :
    (∑ e ∈ E, blockIndicator ({e.1, e.2} : Finset V) ω) =
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) := by
  classical
  simp only [blockIndicator, Set.indicator_apply, Set.mem_ofPred_eq,
    Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact Finset.sum_boole _ _

lemma sampled_matching_lower_tail (p : unitInterval) (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ B)
    (c : ℕ) (hc : ∀ e ∈ E, cutColor e = c) :
    (sampleMeasure V p).real {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) ≤
        (p : ℝ) ^ 2 * E.card / 2} ≤ exp (-(p : ℝ) ^ 2 * E.card / 8) := by
  classical
  let S : E → Finset V := fun e => {e.val.1, e.val.2}
  have hS : Pairwise fun e f : E => Disjoint (S e) (S f) := by
    intro e f hef
    exact same_cutColor_blocks_disjoint A B hAB (hE e e.property).1 (hE e e.property).2
      (hE f f.property).1 (hE f f.property).2 ((hc e e.property).trans (hc f f.property).symm)
      (fun h => hef (Subtype.ext h))
  have hd : ∀ e : E, (S e).card = 2 := by
    intro e
    apply Finset.card_pair
    intro h
    exact Finset.disjoint_left.mp hAB (hE e e.property).1 (h ▸ (hE e e.property).2)
  have ht := sample_blocks_lower_tail p S hS 2 hd Finset.univ
  have heq (ω : V → Bool) : (∑ e : E, blockIndicator (S e) ω) =
      (∑ e ∈ E, blockIndicator ({e.1, e.2} : Finset V) ω) := by
    exact Finset.sum_attach E (fun e => blockIndicator ({e.1, e.2} : Finset V) ω)
  simp_rw [heq, blockIndicator_sum_card] at ht
  simpa using ht

lemma sum_cutColor_class_card (E : Finset (V × V)) :
    (∑ i ∈ Finset.range (2 * Fintype.card V), (E.filter (fun e => cutColor e = i)).card) =
      E.card := by
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_true_of_mem
  intro e _
  exact Finset.mem_range.mpr (cutColor_lt e)

theorem sampled_bipartite_cut_lower_tail (p : unitInterval)
    (hr : 0 < Fintype.card V) (A B : Finset V) (hAB : Disjoint A B)
    (E : Finset (V × V)) (hE : ∀ e ∈ E, e.1 ∈ A ∧ e.2 ∈ B) :
    (sampleMeasure V p).real {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
        (p : ℝ) ^ 2 * E.card / 4} ≤
      2 * (Fintype.card V : ℝ) * exp (-(p : ℝ) ^ 2 * E.card / (32 * Fintype.card V)) := by
  classical
  let r : ℝ := Fintype.card V
  have hrR : 0 < r := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast hr
  let colors := Finset.range (2 * Fintype.card V)
  let C (i : ℕ) := E.filter (fun e => cutColor e = i)
  let m (i : ℕ) : ℝ := (C i).card
  let L := colors.filter (fun i => (E.card : ℝ) / (4 * r) ≤ m i)
  let retained (i : ℕ) (ω : V → Bool) : ℝ :=
    ((C i |>.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ)
  have hsum : ∑ i ∈ colors, m i = (E.card : ℝ) := by
    dsimp [colors, m, C]
    exact_mod_cast sum_cutColor_class_card E
  have hretain (ω : V → Bool) : ∑ i ∈ colors, retained i ω =
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) := by
    have ht := sum_cutColor_class_card
      (E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω))
    simpa only [retained, C, colors, Finset.filter_filter, and_comm, Nat.cast_sum] using
      (show (∑ i ∈ Finset.range (2 * Fintype.card V),
        (((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).filter
          (fun e => cutColor e = i)).card : ℝ)) = _ by exact_mod_cast ht)
  have hlarge : (E.card : ℝ) / 2 ≤ ∑ i ∈ L, m i := by
    have hb : ∑ i ∈ colors, m i ≤
        ∑ i ∈ colors, ((if i ∈ L then m i else 0) + (E.card : ℝ) / (4 * r)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hiL : i ∈ L
      · simp only [hiL, ↓reduceIte]
        have : 0 ≤ (E.card : ℝ) / (4 * r) := by positivity
        linarith
      · have hiM : m i < (E.card : ℝ) / (4 * r) := by
          simpa only [L, Finset.mem_filter, hi, true_and, not_le] using hiL
        simp only [hiL, ↓reduceIte, zero_add]
        exact hiM.le
    rw [hsum, Finset.sum_add_distrib, Finset.sum_ite_mem] at hb
    have hsub : colors ∩ L = L := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hsub] at hb
    have hconst : ∑ _i ∈ colors, (E.card : ℝ) / (4 * r) = (E.card : ℝ) / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, colors, Finset.card_range, Nat.cast_mul,
        Nat.cast_ofNat]
      dsimp [r] at *
      field_simp
      ; ring
    rw [hconst] at hb
    linarith
  let Bad (i : ℕ) : Set (V → Bool) :=
    {ω | retained i ω ≤ (p : ℝ) ^ 2 * m i / 2}
  have hcover : {ω |
      ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
        (p : ℝ) ^ 2 * E.card / 4} ⊆ ⋃ i ∈ L, Bad i := by
    intro ω hfail
    by_contra hnot
    have hiok : ∀ i ∈ L, (p : ℝ) ^ 2 * m i / 2 ≤ retained i ω := by
      intro i hi
      have hn : ω ∉ Bad i := fun h => hnot (Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨hi, h⟩⟩)
      exact (lt_of_not_ge hn).le
    have hs₁ : (p : ℝ) ^ 2 / 2 * (∑ i ∈ L, m i) ≤ ∑ i ∈ L, retained i ω := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      calc
        _ = (p : ℝ) ^ 2 * m i / 2 := by ring
        _ ≤ retained i ω := hiok i hi
    have hs₂ : (∑ i ∈ L, retained i ω) ≤ ∑ i ∈ colors, retained i ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => Nat.cast_nonneg _)
    rw [hretain] at hs₂
    have hs₃ := mul_le_mul_of_nonneg_left hlarge (by positivity : 0 ≤ (p : ℝ) ^ 2 / 2)
    change ((E.filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω)).card : ℝ) <
      (p : ℝ) ^ 2 * E.card / 4 at hfail
    nlinarith
  have hbad (i : ℕ) (hi : i ∈ L) : (sampleMeasure V p).real (Bad i) ≤
      exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by
    have ht := sampled_matching_lower_tail p A B hAB (C i)
      (fun e he => hE e (Finset.mem_filter.mp he).1) i
      (fun e he => (Finset.mem_filter.mp he).2)
    have hm : (E.card : ℝ) / (4 * r) ≤ m i := (Finset.mem_filter.mp hi).2
    have he : -(p : ℝ) ^ 2 * m i / 8 ≤ -(p : ℝ) ^ 2 * E.card / (32 * r) := by
      have ht := mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr (sq_nonneg (p : ℝ)))
      calc
        _ ≤ (-(p : ℝ) ^ 2 * ((E.card : ℝ) / (4 * r))) / 8 := by linarith
        _ = _ := by ring
    exact ht.trans (exp_le_exp.mpr he)
  calc
    _ ≤ (sampleMeasure V p).real (⋃ i ∈ L, Bad i) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ i ∈ L, (sampleMeasure V p).real (Bad i) := measureReal_biUnion_finset_le L Bad
    _ ≤ ∑ i ∈ L, exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := Finset.sum_le_sum hbad
    _ = (L.card : ℝ) * exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by simp
    _ ≤ 2 * r * exp (-(p : ℝ) ^ 2 * E.card / (32 * r)) := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      have ht := Finset.card_le_card (Finset.filter_subset (fun i => (E.card : ℝ) / (4 * r) ≤ m i) colors)
      have ht' : L.card ≤ 2 * Fintype.card V := by
        simpa only [colors, Finset.card_range] using ht
      change (L.card : ℝ) ≤ 2 * (Fintype.card V : ℝ)
      exact_mod_cast ht'

lemma card_interedges_eq_sum_neighborsIn {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B : Finset V) : (P.interedges A B).card = ∑ v ∈ A, (neighborsIn P v B).card := by
  simp only [SimpleGraph.interedges, Rel.interedges, neighborsIn, Finset.card_filter]
  rw [Finset.sum_product]

lemma neighborsIn_partition_card {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (v : V) (A W : Finset V) (hAW : A ⊆ W) :
    (neighborsIn P v W).card = (neighborsIn P v A).card + (neighborsIn P v (W \ A)).card := by
  have hu : neighborsIn P v W = neighborsIn P v A ∪ neighborsIn P v (W \ A) := by
    ext x; simp only [neighborsIn, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · intro ⟨hx, ha⟩
      by_cases hxA : x ∈ A
      · exact Or.inl ⟨hxA, ha⟩
      · exact Or.inr ⟨⟨hx, hxA⟩, ha⟩
    · rintro (⟨hx, ha⟩ | ⟨⟨hx, _⟩, ha⟩)
      · exact ⟨hAW hx, ha⟩
      · exact ⟨hx, ha⟩
  rw [hu, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 (Finset.mem_filter.mp hx).1

lemma interedges_sym2_injective {V : Type cycleUniverse5} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B : Finset V) (hAB : Disjoint A B) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges A B : Set (V × V)) := by
  intro e he f hf hef
  rcases Sym2.mk_eq_mk_iff.mp hef with h | h
  · exact h
  · exact False.elim <| Finset.disjoint_left.mp hAB (P.mem_interedges_iff.mp he).1
      ((congrArg Prod.fst h).symm ▸ (P.mem_interedges_iff.mp hf).2.1)

lemma cut_perturbation_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A T : Finset V) (_hAW : A ⊆ W) (_hTW : T ⊆ W) :
    (P.interedges T (W \ T)).card ≤ (P.interedges A (W \ A)).card +
      Fintype.card V * (A ∆ T).card := by
  classical
  let f := fun e : V × V => s(e.1, e.2)
  let E := (P.interedges A (W \ A)).image f
  let D := (((A ∆ T) ×ˢ (Finset.univ : Finset V)).image f)
  have hinj := interedges_sym2_injective P T (W \ T) (Finset.disjoint_left.mpr (by
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx))
  have hsub : (P.interedges T (W \ T)).image f ⊆ E ∪ D := by
    intro e he
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
    rcases P.mem_interedges_iff.mp hxy with ⟨hxT, hyWT, hxy⟩
    obtain ⟨hyW, hyT⟩ := Finset.mem_sdiff.mp hyWT
    by_cases hxA : x ∈ A
    · by_cases hyA : y ∈ A
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨(y,x), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
        · exact Finset.mem_symmDiff.mpr (Or.inl ⟨hyA, hyT⟩)
        · exact Sym2.eq_swap
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨(x,y), P.mem_interedges_iff.mpr
          ⟨hxA, Finset.mem_sdiff.mpr ⟨hyW, hyA⟩, hxy⟩, rfl⟩
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr
        ⟨Finset.mem_symmDiff.mpr (Or.inr ⟨hxT, hxA⟩), Finset.mem_univ _⟩, rfl⟩
  calc
    _ = ((P.interedges T (W \ T)).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (E ∪ D).card := Finset.card_le_card hsub
    _ ≤ E.card + D.card := Finset.card_union_le _ _
    _ ≤ (P.interedges A (W \ A)).card + (((A ∆ T) ×ˢ (Finset.univ : Finset V))).card :=
      Nat.add_le_add (Finset.card_image_le) Finset.card_image_le
    _ = _ := by simp [mul_comm]

lemma card_le_add_symmDiff {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (A T : Finset V) : A.card ≤ T.card + (A ∆ T).card := by
  have hs : A ⊆ T ∪ (A ∆ T) := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_left _ hxT
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inl ⟨hx,hxT⟩))
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma sdiff_card_le_add_symmDiff {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W A T : Finset V) :
    (W \ A).card ≤ (W \ T).card + (A ∆ T).card := by
  have hs : W \ A ⊆ (W \ T) ∪ (A ∆ T) := by
    intro x hx
    obtain ⟨hxW,hxA⟩ := Finset.mem_sdiff.mp hx
    by_cases hxT : x ∈ T
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inr ⟨hxT,hxA⟩))
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxW,hxT⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma cut_card_lower_of_neighbors (P : SimpleGraph V) [DecidableRel P.Adj]
    (A B Q : Finset V) (hQA : Q ⊆ A) (c : ℝ)
    (hc : ∀ v ∈ Q, c ≤ (neighborsIn P v B).card) :
    c * Q.card ≤ ((P.interedges A B).card : ℝ) := by
  rw [card_interedges_eq_sum_neighborsIn, Nat.cast_sum]
  calc
    _ = ∑ v ∈ Q, c := by simp [mul_comm]
    _ ≤ ∑ v ∈ Q, ((neighborsIn P v B).card : ℝ) := Finset.sum_le_sum hc
    _ ≤ ∑ v ∈ A, ((neighborsIn P v B).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hQA (fun _ _ _ => Nat.cast_nonneg _)

lemma bad_sampled_cut_size_and_exceptional (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A : Finset V) (hAW : A ⊆ W) (_ha : 0 < (A.card : ℝ))
    {p h τ : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ : τ < p*h/4)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hbad : ((P.interedges A (W \ A)).card : ℝ) < τ * A.card) :
    p*h/4 < (A.card : ℝ) ∧
      ((A \ A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))).card : ℝ) ≤
        4*τ*A.card/(p*h) := by
  have hpart (v : V) : ((neighborsIn P v W).card : ℝ) =
      ((neighborsIn P v A).card : ℝ) + ((neighborsIn P v (W \ A)).card : ℝ) := by
    exact_mod_cast neighborsIn_partition_card P v A W hAW
  constructor
  · by_contra hn
    have ha' : (A.card : ℝ) ≤ p*h/4 := le_of_not_gt hn
    have hlo : p*h/4 * A.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
      apply cut_card_lower_of_neighbors P A (W \ A) A (Finset.Subset.refl _) (p*h/4)
      intro v _
      have hc : ((neighborsIn P v A).card : ℝ) ≤ A.card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset (P.Adj v) A)
      have hd := hdeg v
      have he := hpart v
      linarith
    nlinarith
  · let Q := A \ A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))
    have hl : p*h/4 * Q.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
      apply cut_card_lower_of_neighbors P A (W \ A) Q Finset.sdiff_subset (p*h/4)
      intro v hv
      obtain ⟨hvA,hvG⟩ := Finset.mem_sdiff.mp hv
      have hn : ((neighborsIn P v A).card : ℝ) < p*h/4 := by
        simpa only [Finset.mem_filter, hvA, true_and, not_le] using hvG
      have hd := hdeg v
      have he := hpart v
      linarith
    change (Q.card : ℝ) ≤ _
    apply (le_div_iff₀ (mul_pos hp hh)).mpr
    nlinarith

lemma neighborhoodUnion_leakage (P : SimpleGraph V) [DecidableRel P.Adj]
    (S W A : Finset V) :
    (((neighborhoodUnion P S ∩ W) \ A).card : ℝ) ≤
      ∑ v ∈ S, ((neighborsIn P v (W \ A)).card : ℝ) := by
  have heq : (neighborhoodUnion P S ∩ W) \ A =
      S.biUnion (fun v => neighborsIn P v (W \ A)) := by
    ext x
    simp only [neighborhoodUnion, neighborsIn, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  rw [heq]
  exact_mod_cast Finset.card_biUnion_le

lemma hitting_neighborhoodUnion (P : SimpleGraph V) [DecidableRel P.Adj]
    (good S A : Finset V) (hhit : ∀ v ∈ good, ¬Disjoint (neighborsIn P v A) S) :
    good ⊆ neighborhoodUnion P S := by
  intro v hv
  obtain ⟨x,hxK,hxS⟩ := Finset.not_disjoint_iff.mp (hhit v hv)
  apply Finset.mem_biUnion.mpr
  refine ⟨x,hxS,?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, P.adj_symm (Finset.mem_filter.mp hxK).2⟩

theorem exists_approximating_witness (P : SimpleGraph V) [DecidableRel P.Adj]
    (W A : Finset V) (hAW : A ⊆ W) (ha : 0 < (A.card : ℝ))
    {p h τ M : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < p*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hmiss : (Fintype.card V : ℝ) * exp (-p*M/4) < 1/2)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hbad : ((P.interedges A (W \ A)).card : ℝ) < τ * A.card) :
    p*h/4 < (A.card : ℝ) ∧ ∃ S : Finset V, S ⊆ A ∧
      (S.card : ℝ) ≤ 4 * A.card * M / h ∧
      ((A ∆ (neighborhoodUnion P S ∩ W)).card : ℝ) ≤
        (4*τ/(p*h) + 4*τ*M/h) * A.card := by
  classical
  obtain ⟨hlarge, hexc⟩ := bad_sampled_cut_size_and_exceptional P W A hAW ha hp hh hτ hdeg hbad
  refine ⟨hlarge, ?_⟩
  let good := A.filter (fun v => p*h/4 ≤ ((neighborsIn P v A).card : ℝ))
  let w : V → ℝ := fun v => ((neighborsIn P v (W \ A)).card : ℝ)
  let q : unitInterval := ⟨M/h, div_nonneg hM.le hh.le, (div_le_one hh).mpr hMh⟩
  have hq : 0 < (q : ℝ) := div_pos hM hh
  have hm : (good.card : ℝ) * exp (-(q : ℝ) * (p*h/4)) < 1/2 := by
    have heq : -(q : ℝ) * (p*h/4) = -p*M/4 := by
      dsimp [q]
      field_simp [hh.ne']
    rw [heq]
    have hg : (good.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ good
    exact (mul_le_mul_of_nonneg_right hg (exp_pos _).le).trans_lt hmiss
  have hsum : ∑ v ∈ A, w v ≤ τ * A.card := by
    dsimp [w]
    rw [← Nat.cast_sum, ← card_interedges_eq_sum_neighborsIn]
    exact hbad.le
  obtain ⟨S,hSA,hSc,hSw,hSh⟩ := exists_small_weighted_hitting_set A
    (Finset.card_pos.mp (by exact_mod_cast ha)) good (fun v => neighborsIn P v A)
    (fun v _ => Finset.filter_subset _ _) w (fun _ _ => Nat.cast_nonneg _)
    (mul_pos hτ0 ha) hsum
    (fun v hv => (Finset.mem_filter.mp hv).2) q hq hm
  refine ⟨S,hSA,?_,?_⟩
  · convert hSc using 1 ; dsimp [q] ; ring
  · let T := neighborhoodUnion P S ∩ W
    have hgood : good ⊆ neighborhoodUnion P S := hitting_neighborhoodUnion P good S A hSh
    have hsub : A ∆ T ⊆ (A \ good) ∪ (T \ A) := by
      intro v hv
      rcases Finset.mem_symmDiff.mp hv with ⟨hvA,hvT⟩ | ⟨hvT,hvA⟩
      · apply Finset.mem_union_left
        apply Finset.mem_sdiff.mpr
        refine ⟨hvA,?_⟩
        intro hvG
        exact hvT (Finset.mem_inter.mpr ⟨hgood hvG, hAW hvA⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvT,hvA⟩)
    have hδ : ((A ∆ T).card : ℝ) ≤ ((A \ good).card : ℝ) + ((T \ A).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hleak : ((T \ A).card : ℝ) ≤ 4*(q : ℝ)*(τ*A.card) :=
      (neighborhoodUnion_leakage P S W A).trans hSw
    change ((A ∆ T).card : ℝ) ≤ _
    change ((A \ good).card : ℝ) ≤ _ at hexc
    calc
      _ ≤ 4*τ*A.card/(p*h) + 4*(q : ℝ)*(τ*A.card) := add_le_add hexc hleak |>.trans' hδ
      _ = _ := by dsimp [q]; ring

theorem cutExpansionOn_of_witnesses (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) {p h τ M : ℝ} (hp : 0 < p) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < p*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hmiss : (Fintype.card V : ℝ) * exp (-p*M/4) < 1/2)
    (hε : 4*τ/(p*h) + 4*τ*M/h ≤ 1/2)
    (hperturb : τ + Fintype.card V * (4*τ/(p*h) + 4*τ*M/h) ≤ p^2*h/8)
    (hexp : CutExpansion P h)
    (hdeg : ∀ v, p*h/2 ≤ ((neighborsIn P v W).card : ℝ))
    (hwitness : ∀ S : Finset V, (S.card : ℝ) ≤ 4*Fintype.card V*M/h →
      let U := neighborhoodUnion P S
      p*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ) →
      (p^2/4) * ((P.interedges U Uᶜ).card : ℝ) ≤
        ((P.interedges (U ∩ W) (W \ (U ∩ W))).card : ℝ)) :
    CutExpansionOn P W τ := by
  classical
  have hsmall (A : Finset V) (hAW : A ⊆ W)
      (hsize : (A.card : ℝ) ≤ (W \ A).card) :
      τ * A.card ≤ ((P.interedges A (W \ A)).card : ℝ) := by
    by_contra hn
    have hbad := lt_of_not_ge hn
    have ha : 0 < (A.card : ℝ) := by
      by_contra hn
      have hz : (A.card : ℝ) = 0 := (le_of_not_gt hn).antisymm (Nat.cast_nonneg _)
      rw [hz, mul_zero] at hbad
      exact (Nat.cast_nonneg _).not_gt hbad
    obtain ⟨hlarge,S,hSA,hSc,hδ⟩ := exists_approximating_witness P W A hAW ha
      hp hh hτ0 hτ hM hMh hmiss hdeg hbad
    let U := neighborhoodUnion P S
    let T := U ∩ W
    let δ : ℝ := (A ∆ T).card
    have hδ' : δ ≤ (A.card : ℝ)/2 := by
      have ht := mul_le_mul_of_nonneg_right hε ha.le
      dsimp [δ,T,U]
      linarith
    have hmin : (A.card : ℝ)/2 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ) := by
      apply le_min
      · have ht : (A.card : ℝ) ≤ (T.card : ℝ) + δ := by
          dsimp [δ]
          exact_mod_cast card_le_add_symmDiff A T
        have hTU : (T.card : ℝ) ≤ U.card := by
          exact_mod_cast Finset.card_le_card (Finset.inter_subset_left : T ⊆ U)
        linarith
      · have ht : ((W \ A).card : ℝ) ≤ ((W \ T).card : ℝ) + δ := by
          dsimp [δ]
          exact_mod_cast sdiff_card_le_add_symmDiff W A T
        have hs : W \ T ⊆ Uᶜ := by
          intro v hv
          obtain ⟨hvW,hvT⟩ := Finset.mem_sdiff.mp hv
          apply Finset.mem_compl.mpr
          intro hvU
          exact hvT (Finset.mem_inter.mpr ⟨hvU,hvW⟩)
        have hh' : ((W \ T).card : ℝ) ≤ Uᶜ.card := by exact_mod_cast Finset.card_le_card hs
        linarith
    have hsbound : (S.card : ℝ) ≤ 4*Fintype.card V*M/h := by
      apply hSc.trans
      have hac : (A.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ A
      gcongr
    have hw := hwitness S hsbound (by dsimp [U] at hmin; linarith)
    have he := hexp U
    have hlo : p^2*h*A.card/8 ≤ ((P.interedges T (W \ T)).card : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hmin hh.le
      have ht := mul_le_mul_of_nonneg_left (hm.trans he) (by positivity : 0 ≤ p^2/4)
      change p^2/4 * ((P.interedges U Uᶜ).card : ℝ) ≤ _ at hw
      nlinarith
    have hupper : ((P.interedges T (W \ T)).card : ℝ) ≤
        ((P.interedges A (W \ A)).card : ℝ) + Fintype.card V * δ := by
      dsimp [δ]
      exact_mod_cast cut_perturbation_card P W A T hAW Finset.inter_subset_right
    have hd := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ (Fintype.card V : ℝ))
    have hp' := mul_le_mul_of_nonneg_right hperturb ha.le
    change (Fintype.card V : ℝ) * δ ≤ _ at hd
    nlinarith
  intro A hAW
  by_cases hs : (A.card : ℝ) ≤ (W \ A).card
  · rw [min_eq_left hs]
    exact hsmall A hAW hs
  · have hs' : ((W \ A).card : ℝ) ≤ A.card := (lt_of_not_ge hs).le
    rw [min_eq_right hs']
    have heq : W \ (W \ A) = A := Finset.sdiff_sdiff_eq_self hAW
    have ht := hsmall (W \ A) Finset.sdiff_subset (by simpa only [heq] using hs')
    rw [heq] at ht
    let : Std.Symm P.Adj := P.symm
    have hcomm : (P.interedges (W \ A) A).card = (P.interedges A (W \ A)).card :=
      Rel.card_interedges_comm (W \ A) A
    rwa [hcomm] at ht

lemma cutExpansion_minDegree (P : SimpleGraph V) [DecidableRel P.Adj]
    {h : ℝ} (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) (v : V) :
    h ≤ ((neighborsIn P v Finset.univ).card : ℝ) := by
  have ht := hexp {v}
  have hc : (1 : ℝ) ≤ ((({v} : Finset V)ᶜ).card : ℝ) := by
    have : 1 ≤ (({v} : Finset V)ᶜ).card := by
      rw [Finset.card_compl, Finset.card_singleton]
      omega
    exact_mod_cast this
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hc, mul_one] at ht
  rw [card_interedges_eq_sum_neighborsIn, Finset.sum_singleton] at ht
  have heq : neighborsIn P v ({v} : Finset V)ᶜ = neighborsIn P v Finset.univ := by
    ext x
    simp only [neighborsIn, Finset.mem_filter, Finset.mem_compl, Finset.mem_singleton,
      Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨fun he => P.irrefl (he ▸ h), h⟩⟩
  rwa [heq] at ht

lemma sample_neighbors_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h : ℝ} (hdeg : ∀ v, h ≤ ((neighborsIn P v Finset.univ).card : ℝ))
    (v : V) :
    (sampleMeasure V p).real {ω | ((neighborsIn P v (sampleVertices ω)).card : ℝ) < (p : ℝ)*h/2} ≤
      exp (-(p : ℝ)*h/8) := by
  have heq (ω : V → Bool) : neighborsIn P v (sampleVertices ω) =
      neighborsIn P v Finset.univ ∩ sampleVertices ω := by
    ext x; simp [neighborsIn, and_comm]
  simp_rw [heq]
  have hs : {ω | (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) < (p : ℝ)*h/2} ⊆
      {ω | (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) ≤
        (p : ℝ)*(neighborsIn P v Finset.univ).card/2} := by
    intro ω hω
    change (((neighborsIn P v Finset.univ) ∩ sampleVertices ω).card : ℝ) < (p : ℝ)*h/2 at hω
    exact hω.le.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hdeg v) p.property.1) (by norm_num))
  have he : -(p : ℝ)*(neighborsIn P v Finset.univ).card/8 ≤ -(p : ℝ)*h/8 := by
    have ht := mul_le_mul_of_nonneg_left (hdeg v) p.property.1
    linarith
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((sample_card_lower_tail p _).trans (exp_le_exp.mpr he))

lemma card_small_subsets_le (s : ℕ) (hr : 0 < Fintype.card V) :
    (((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s)).card ≤
      (s+1) * Fintype.card V ^ s := by
  classical
  have heq : (((Finset.univ : Finset V).powerset).filter (fun S => S.card ≤ s)) =
      (Finset.range (s+1)).biUnion (fun t => (Finset.univ : Finset V).powersetCard t) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨S.card, by omega, rfl⟩,
      fun ⟨t,ht,he⟩ => by omega⟩
  rw [heq]
  calc
    _ ≤ ∑ t ∈ Finset.range (s+1), ((Finset.univ : Finset V).powersetCard t).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Finset.range (s+1), Fintype.card V ^ s := by
      apply Finset.sum_le_sum
      intro t ht
      rw [Finset.card_powersetCard, Finset.card_univ]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_right hr (by simpa using ht))
    _ = _ := by simp [mul_comm]

lemma card_witnessFamily_le (P : SimpleGraph V) [DecidableRel P.Adj]
    (s : ℕ) (hr : 0 < Fintype.card V) :
    (witnessFamily P s).card ≤ (s+1) * Fintype.card V ^ s :=
  Finset.card_image_le.trans (card_small_subsets_le s hr)

lemma sampled_witness_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h) (hexp : CutExpansion P h)
    (hr : 0 < Fintype.card V) (U : Finset V)
    (hU : (p : ℝ)*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ)) :
    (sampleMeasure V p).real {ω |
      ((P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω))).card : ℝ) <
        (p : ℝ)^2/4 * (P.interedges U Uᶜ).card} ≤
      2 * (Fintype.card V : ℝ) * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
  have hAB : Disjoint U Uᶜ := Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_compl.mp hy) hx)
  have heq (ω : V → Bool) :
      P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω)) =
        (P.interedges U Uᶜ).filter (fun e => e.1 ∈ sampleVertices ω ∧ e.2 ∈ sampleVertices ω) := by
    ext ⟨x,y⟩
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_compl]
    aesop
  have ht := sampled_bipartite_cut_lower_tail p hr U Uᶜ hAB (P.interedges U Uᶜ)
    (fun e he => ⟨(P.mem_interedges_iff.mp he).1, (P.mem_interedges_iff.mp he).2.1⟩)
  have hl : (p : ℝ)*h^2/8 ≤ ((P.interedges U Uᶜ).card : ℝ) := by
    have ht := mul_le_mul_of_nonneg_left hU hh
    have hu := hexp U
    nlinarith
  have he : -(p : ℝ)^2 * (P.interedges U Uᶜ).card/(32*Fintype.card V) ≤
      -(p : ℝ)^3*h^2/(256*Fintype.card V) := by
    have hrR : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hr
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hs := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (p : ℝ)^2)
    nlinarith
  simp_rw [heq]
  have hc : (p : ℝ)^2/4 * (P.interedges U Uᶜ).card = (p : ℝ)^2 * (P.interedges U Uᶜ).card/4 := by ring
  rw [hc]
  exact ht.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr he) (by positivity))

theorem vertex_sampling_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    (p : unitInterval) {h τ M : ℝ} (hp : 0 < (p : ℝ)) (hh : 0 < h) (hτ0 : 0 < τ)
    (hτ : τ < (p : ℝ)*h/4) (hM : 0 < M) (hMh : M ≤ h)
    (hr : 2 ≤ Fintype.card V)
    (hmiss : (Fintype.card V : ℝ) * exp (-(p : ℝ)*M/4) < 1/2)
    (hε : 4*τ/((p : ℝ)*h) + 4*τ*M/h ≤ 1/2)
    (hperturb : τ + Fintype.card V * (4*τ/((p : ℝ)*h) + 4*τ*M/h) ≤ (p : ℝ)^2*h/8)
    (hexp : CutExpansion P h) :
    (sampleMeasure V p).real {ω | ¬SampleGood P (p : ℝ) h τ ω} ≤
      exp (-(p : ℝ)*Fintype.card V/3) +
      Fintype.card V * exp (-(p : ℝ)*h/8) +
      2*Fintype.card V * ((⌈4*Fintype.card V*M/h⌉₊+1 : ℕ) : ℝ) *
        (Fintype.card V : ℝ)^⌈4*Fintype.card V*M/h⌉₊ *
        exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
  classical
  let μ := sampleMeasure V p
  let s := ⌈4*(Fintype.card V : ℝ)*M/h⌉₊
  let large := (witnessFamily P s).filter
    (fun U => (p : ℝ)*h/8 ≤ min (U.card : ℝ) (Uᶜ.card : ℝ))
  let B₀ : Set (V → Bool) := {ω | 2*(p : ℝ)*Fintype.card V < ((sampleVertices ω).card : ℝ)}
  let B₁ (v : V) : Set (V → Bool) :=
    {ω | ((neighborsIn P v (sampleVertices ω)).card : ℝ) < (p : ℝ)*h/2}
  let B₂ (U : Finset V) : Set (V → Bool) := {ω |
    ((P.interedges (U ∩ sampleVertices ω) (sampleVertices ω \ (U ∩ sampleVertices ω))).card : ℝ) <
      (p : ℝ)^2/4 * (P.interedges U Uᶜ).card}
  have h₀ : μ.real B₀ ≤ exp (-(p : ℝ)*Fintype.card V/3) := by
    have hs : B₀ ⊆ {ω | 2*(p : ℝ)*Fintype.card V ≤ ((sampleVertices ω).card : ℝ)} := by
      intro ω hω
      change 2*(p : ℝ)*Fintype.card V < ((sampleVertices ω).card : ℝ) at hω
      exact hω.le
    have ht := sample_card_upper_tail p (Finset.univ : Finset V)
    simp only [Finset.card_univ, Finset.univ_inter] at ht
    exact (measureReal_mono hs (measure_ne_top _ _)).trans ht
  have h₁ : μ.real (⋃ v ∈ (Finset.univ : Finset V), B₁ v) ≤
      Fintype.card V * exp (-(p : ℝ)*h/8) := by
    calc
      _ ≤ ∑ v : V, μ.real (B₁ v) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _v : V, exp (-(p : ℝ)*h/8) := Finset.sum_le_sum (fun v _ =>
        sample_neighbors_lower_tail P p (cutExpansion_minDegree P hexp hr) v)
      _ = _ := by simp
  have h₂ : μ.real (⋃ U ∈ large, B₂ U) ≤
      2*Fintype.card V * ((s+1 : ℕ) : ℝ) * (Fintype.card V : ℝ)^s *
        exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
    calc
      _ ≤ ∑ U ∈ large, μ.real (B₂ U) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _U ∈ large, 2*(Fintype.card V : ℝ)*exp (-(p : ℝ)^3*h^2/(256*Fintype.card V)) := by
        apply Finset.sum_le_sum
        intro U hU
        exact sampled_witness_cut_lower_tail P p hh.le hexp (by omega) U (Finset.mem_filter.mp hU).2
      _ = (large.card : ℝ) * (2*Fintype.card V * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V))) := by simp
      _ ≤ (((s+1 : ℕ) : ℝ) * (Fintype.card V : ℝ)^s) *
          (2*Fintype.card V * exp (-(p : ℝ)^3*h^2/(256*Fintype.card V))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have ht : large.card ≤ (s+1)*Fintype.card V^s :=
          (Finset.card_le_card (Finset.filter_subset _ _)).trans
            (card_witnessFamily_le P s (by omega))
        exact_mod_cast ht
      _ = _ := by ring
  have hcover : {ω | ¬SampleGood P (p : ℝ) h τ ω} ⊆
      (B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) ∪ (⋃ U ∈ large, B₂ U) := by
    intro ω hω
    by_contra hn
    have hn₀ : ω ∉ B₀ := fun h => hn (Or.inl (Or.inl h))
    have hn₁ (v : V) : ω ∉ B₁ v := fun h => hn (Or.inl (Or.inr
      (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨Finset.mem_univ _, h⟩⟩)))
    have hn₂ (U : Finset V) (hU : U ∈ large) : ω ∉ B₂ U := fun h => hn (Or.inr
      (Set.mem_iUnion.mpr ⟨U, Set.mem_iUnion.mpr ⟨hU,h⟩⟩))
    apply hω
    have hd (v : V) : (p : ℝ)*h/2 ≤ ((neighborsIn P v (sampleVertices ω)).card : ℝ) :=
      le_of_not_gt (hn₁ v)
    refine ⟨le_of_not_gt hn₀, hd, ?_⟩
    apply cutExpansionOn_of_witnesses P (sampleVertices ω) hp hh hτ0 hτ hM hMh
      hmiss hε hperturb hexp hd
    intro S hS
    dsimp only
    intro hU
    let U := neighborhoodUnion P S
    have hSc : S.card ≤ s := by
      have ht := hS.trans (Nat.le_ceil (4*(Fintype.card V : ℝ)*M/h))
      dsimp [s]
      exact_mod_cast ht
    have hmem : U ∈ large := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hU⟩
      apply Finset.mem_image.mpr
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hSc⟩, rfl⟩
    exact le_of_not_gt (hn₂ U hmem)
  calc
    _ ≤ μ.real ((B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) ∪ (⋃ U ∈ large, B₂ U)) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ μ.real (B₀ ∪ (⋃ v ∈ (Finset.univ : Finset V), B₁ v)) + μ.real (⋃ U ∈ large, B₂ U) :=
      measureReal_union_le _ _
    _ ≤ μ.real B₀ + μ.real (⋃ v ∈ (Finset.univ : Finset V), B₁ v) + μ.real (⋃ U ∈ large, B₂ U) :=
      add_le_add (measureReal_union_le _ _) le_rfl
    _ ≤ _ := add_le_add (add_le_add h₀ h₁) h₂

end ErdosGallai.Sampling

end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ReservoirSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
namespace ErdosGallai.Sampling

lemma eventually_monomial_lt (K c a b : ℝ) (hc : 0 < c) (hab : a < b) :
    ∀ᶠ D : ℝ in atTop, K * D^a < c * D^b := by
  have ht : Tendsto (fun D : ℝ => K * D^(a-b)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).const_mul K
    simpa only [neg_sub, mul_zero] using hh
  filter_upwards [eventually_gt_atTop (0 : ℝ), ht.eventually_lt_const hc] with D hD htD
  have hb : 0 < D^b := Real.rpow_pos_of_pos hD b
  have heq : D^a = D^(a-b) * D^b := by rw [← Real.rpow_add hD]; congr 1; ring
  rw [heq, ← mul_assoc]
  exact mul_lt_mul_of_pos_right htD hb

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

lemma eventually_log_le_small_power : ∀ᶠ D : ℝ in atTop, log D ≤ D^(1/10 : ℝ) := by
  filter_upwards [(isLittleO_log_rpow_atTop (show (0 : ℝ) < 1/10 by norm_num)).eventuallyLE,
    eventually_ge_atTop (1 : ℝ)] with D hD h1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg h1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] using hD

lemma samplingScaleError_tendsto (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    Tendsto (samplingScaleError c p) atTop (𝓝 0) := by
  have h0 := tendsto_monomial_exp_neg_power 0 (9/10) (p/3) (by norm_num) (by positivity)
  have h1 := tendsto_monomial_exp_neg_power (51/50) (9/10) (p*c/8) (by norm_num) (by positivity)
  have h2 := (tendsto_monomial_exp_neg_power (23/20) (39/50) (p^3*c^2/512)
    (by norm_num) (by positivity)).const_mul (2*(4/c+2))
  unfold samplingScaleError
  simpa [neg_div, Real.rpow_zero] using (h0.add h1).add h2

lemma sampling_witness_error_le (c p D : ℝ) (r : ℕ) (hc : 0 < c) (hp : 0 < p)
    (hD : 1 ≤ D) (hrpos : 0 < (r : ℝ)) (hrhi : (r : ℝ) ≤ D^(51/50 : ℝ))
    (hlog : log D ≤ D^(1/10 : ℝ))
    (hcost : ((51/50)*(4/c+2))*D^(23/100 : ℝ) ≤
      (p^3*c^2/512)*D^(39/50 : ℝ)) :
    let h := c*D^(9/10 : ℝ)
    let M := D^(1/100 : ℝ)
    2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
        exp (-p^3*h^2/(256*r)) ≤
      (2*(4/c+2))*(D^(23/20 : ℝ)*exp (-(p^3*c^2/512)*D^(39/50 : ℝ))) := by
  let h := c*D^(9/10 : ℝ)
  let M := D^(1/100 : ℝ)
  let K := 4/c+2
  have hK : 0 < K := by dsimp [K]; positivity
  have hDpos : 0 < D := by linarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hMpos : 0 < M := Real.rpow_pos_of_pos hDpos _
  have hrNat : 0 < r := by exact_mod_cast hrpos
  have hs : ((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) ≤ K*D^(13/100 : ℝ) := by
    have hnorm : 4*D^(51/50 : ℝ)*M/h = (4/c)*D^(13/100 : ℝ) := by
      dsimp [M,h]
      rw [show (13/100 : ℝ) = (51/50+1/100)-9/10 by norm_num,
        Real.rpow_sub hDpos, Real.rpow_add hDpos]
      field_simp
    calc
      _ ≤ 4*r*M/h+2 := by
        have hs := (Nat.ceil_lt_add_one (show 0 ≤ 4*(r : ℝ)*M/h by positivity)).le
        push_cast
        linarith
      _ ≤ 4*D^(51/50 : ℝ)*M/h+2 := by gcongr
      _ = (4/c)*D^(13/100 : ℝ)+2 := by rw [hnorm]
      _ ≤ K*D^(13/100 : ℝ) := by
        have hd := Real.one_le_rpow hD (show (0 : ℝ) ≤ 13/100 by norm_num)
        dsimp [K]
        nlinarith
  have hln : log (r : ℝ) ≤ (51/50)*log D := by
    simpa only [Real.log_rpow hDpos] using Real.log_le_log hrpos hrhi
  have hecost : (⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ) ≤
      (p^3*c^2/512)*D^(39/50 : ℝ) := by
    have hs' : (⌈4*r*M/h⌉₊ : ℝ) ≤ K*D^(13/100 : ℝ) := by push_cast at hs; linarith
    calc
      _ ≤ K*D^(13/100 : ℝ)*((51/50)*log D) := by
        apply mul_le_mul hs' hln
        · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
        · positivity
      _ ≤ K*D^(13/100 : ℝ)*((51/50)*D^(1/10 : ℝ)) := by gcongr
      _ = ((51/50)*K)*D^(23/100 : ℝ) := by
        have he := Real.rpow_add hDpos (13/100 : ℝ) (1/10)
        norm_num at he
        rw [he]
        ring
      _ ≤ _ := hcost
  have hratio : c^2*D^(39/50 : ℝ) ≤ h^2/(r : ℝ) := by
    have he : c^2*D^(39/50 : ℝ) = h^2/D^(51/50 : ℝ) := by
      dsimp [h]
      rw [show (39/50 : ℝ) = (9/10)*2-51/50 by norm_num,
        Real.rpow_sub hDpos]
      have he2 := Real.rpow_mul_natCast hDpos.le (9/10 : ℝ) 2
      norm_num only [Nat.cast_ofNat] at he2
      rw [show (9/10 : ℝ)*2=9/5 by norm_num, he2]
      ring
    rw [he]
    exact div_le_div_of_nonneg_left (sq_nonneg h) hrpos hrhi
  have hexpcost : exp ((⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ) - p^3*h^2/(256*r)) ≤
      exp (-(p^3*c^2/512)*D^(39/50 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_left hratio (show 0 ≤ p^3/256 by positivity)
    have hid : (p^3/256)*(h^2/(r : ℝ)) =p^3*h^2/(256*r) := by ring
    rw [hid] at hn
    nlinarith
  have hpoly : 2*(r : ℝ)*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ) ≤
      2*K*D^(23/20 : ℝ) := by
    calc
      _ ≤ 2*D^(51/50 : ℝ)*(K*D^(13/100 : ℝ)) := by gcongr
      _ = _ := by
        have he := Real.rpow_add hDpos (51/50 : ℝ) (13/100)
        norm_num at he
        rw [he]
        ring
  have hwitness : 2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
      exp (-p^3*h^2/(256*r)) ≤
      (2*K)*(D^(23/20 : ℝ)*exp (-(p^3*c^2/512)*D^(39/50 : ℝ))) := by
    have heq : (r : ℝ)^⌈4*r*M/h⌉₊*exp (-p^3*h^2/(256*r)) =
        exp ((⌈4*r*M/h⌉₊ : ℝ)*log (r : ℝ)-p^3*h^2/(256*r)) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hrpos]
      simp only [neg_mul,  Real.exp_neg, div_eq_mul_inv]
    rw [mul_assoc (2*(r : ℝ)*_) _ _, heq]
    exact (mul_le_mul hpoly hexpcost (exp_pos _).le (by positivity)).trans_eq (by ring)
  exact hwitness

lemma eventually_samplingScaleReady (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℕ,
      D^(9/10 : ℝ) ≤ r → (r : ℝ) ≤ D^(51/50 : ℝ) → SamplingScaleReady c p D r := by
  let K := 4/c+2
  have hK : 0 < K := by dsimp [K]; positivity
  have hmiss : Tendsto (fun D : ℝ => D^(51/50 : ℝ) * exp (-p/4*D^(1/100 : ℝ)))
      atTop (𝓝 0) := by
    convert tendsto_monomial_exp_neg_power (51/50) (1/100) (p/4)
      (by norm_num) (by positivity) using 1 ; simp [neg_div]
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show (0 : ℝ) < 9/10 by norm_num)).eventually_ge_atTop 2,
    eventually_monomial_lt 1 (p*c/4) (37/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt 1 c (1/100) (9/10) hc (by norm_num),
    hmiss.eventually_lt_const (show (0 : ℝ) < 1/2 by norm_num),
    eventually_monomial_lt (4/(p*c)) (1/4) (-4/25) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt (4/c) (1/4) (-3/20) 0 (by norm_num) (by norm_num),
    eventually_monomial_lt 1 (p^2*c/24) (37/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt (4/(p*c)) (p^2*c/24) (43/50) (9/10) (by positivity) (by norm_num),
    eventually_monomial_lt (4/c) (p^2*c/24) (87/100) (9/10) (by positivity) (by norm_num),
    eventually_log_le_small_power,
    eventually_monomial_lt ((51/50)*K) (p^3*c^2/512) (23/100) (39/50)
      (by positivity) (by norm_num)] with D hD h2 hτ hM hm hε₁ hε₂ ht₀ ht₁ ht₂ hlog hcost
  intro r hrlo hrhi
  have hDpos : 0 < D := by linarith
  have hr2 : 2 ≤ r := by exact_mod_cast h2.trans hrlo
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  let h := c*D^(9/10 : ℝ)
  let τ := D^(37/50 : ℝ)
  let M := D^(1/100 : ℝ)
  have hh : 0 < h := by dsimp [h]; positivity
  have hτpos : 0 < τ := Real.rpow_pos_of_pos hDpos _
  have hMpos : 0 < M := Real.rpow_pos_of_pos hDpos _
  have he₁ : 4*τ/(p*h) = (4/(p*c))*D^(-4/25 : ℝ) := by
    dsimp [τ,h]
    rw [show (-4/25 : ℝ) =37/50-9/10 by norm_num, Real.rpow_sub hDpos]
    field_simp
  have he₂ : 4*τ*M/h = (4/c)*D^(-3/20 : ℝ) := by
    dsimp [τ,M,h]
    rw [show (-3/20 : ℝ) =(37/50+1/100)-9/10 by norm_num,
      Real.rpow_sub hDpos, Real.rpow_add hDpos]
    field_simp
  have hm₁ : D^(51/50 : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)) =
      (4/(p*c))*D^(43/50 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  have hm₂ : D^(51/50 : ℝ)*((4/c)*D^(-3/20 : ℝ)) =
      (4/c)*D^(87/100 : ℝ) := by
    rw [mul_left_comm, ← Real.rpow_add hDpos]
    norm_num
  refine ⟨hr2, ?_, (by simpa only [one_mul] using hM.le), ?_, ?_, ?_, ?_⟩
  · change τ < p*h/4
    dsimp [τ,h]
    simpa only [one_mul, div_mul_eq_mul_div, mul_assoc] using hτ
  · change (r : ℝ)*exp (-p*M/4) < 1/2
    calc
      _ ≤ D^(51/50 : ℝ)*exp (-p*M/4) := mul_le_mul_of_nonneg_right hrhi (exp_pos _).le
      _ < _ := by simpa [M, div_mul_eq_mul_div] using hm
  · change 4*τ/(p*h)+4*τ*M/h ≤ 1/2
    rw [he₁, he₂]
    simp only [Real.rpow_zero, mul_one] at hε₁ hε₂
    linarith
  · change τ+(r : ℝ)*(4*τ/(p*h)+4*τ*M/h) ≤ p^2*h/8
    rw [he₁,he₂]
    have ht : (r : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)+(4/c)*D^(-3/20 : ℝ)) ≤
        (4/(p*c))*D^(43/50 : ℝ)+(4/c)*D^(87/100 : ℝ) := by
      calc
        _ ≤ D^(51/50 : ℝ)*((4/(p*c))*D^(-4/25 : ℝ)+(4/c)*D^(-3/20 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hrhi; positivity
        _ = _ := by rw [mul_add, hm₁, hm₂]
    dsimp [τ,h]
    nlinarith
  · change exp (-p*r/3)+r*exp (-p*h/8)+
      2*r*((⌈4*r*M/h⌉₊+1 : ℕ) : ℝ)*(r : ℝ)^⌈4*r*M/h⌉₊*
        exp (-p^3*h^2/(256*r)) ≤ samplingScaleError c p D
    have hwitness := sampling_witness_error_le c p D r hc hp hD hrpos hrhi hlog hcost.le
    have hsize : exp (-p*r/3) ≤ exp (-p/3*D^(9/10 : ℝ)) := by
      apply exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_left hrlo hp.le
      nlinarith
    have hdegree : (r : ℝ)*exp (-p*h/8) ≤
        D^(51/50 : ℝ)*exp (-(p*c/8)*D^(9/10 : ℝ)) := by
      have heq : -p*h/8=-(p*c/8)*D^(9/10 : ℝ) := by dsimp [h]; ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hrhi (exp_pos _).le
    exact add_le_add (add_le_add hsize hdegree) hwitness

end ErdosGallai.Sampling

namespace ErdosGallai.Sampling
open Filter MeasureTheory Real

universe u

theorem vertex_sampling_uniform (c : ℝ) (hc : 0 < c) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (_hp1 : (p : ℝ) < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj],
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      CutExpansion P (c*D^(9/10 : ℝ)) →
      (sampleMeasure V p).real {ω | ¬SampleGood P (p : ℝ) (c*D^(9/10 : ℝ))
        (D^(37/50 : ℝ)) ω} ≤ ε := by
  have hevent : ∀ᶠ D : ℝ in atTop,
      1 ≤ D ∧
      (∀ r : ℕ, D^(9/10 : ℝ) ≤ r → (r : ℝ) ≤ D^(51/50 : ℝ) →
        SamplingScaleReady c (p : ℝ) D r) ∧
      samplingScaleError c (p : ℝ) D ≤ ε := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_samplingScaleReady c (p : ℝ) hc hp,
      (samplingScaleError_tendsto c (p : ℝ) hc hp).eventually_le_const hε] with D h1 h2 h3
    exact ⟨h1,h2,h3⟩
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ hrlo hrhi hexp
  obtain ⟨h1, hready, herr⟩ := hD₀ D hD
  have hDpos : 0 < D := by linarith
  obtain ⟨hr,hτ,hM,hmiss,he,hperturb,hbound⟩ := hready (Fintype.card V) hrlo hrhi
  exact (vertex_sampling_failure_bound P p hp (by positivity) (by positivity)
    hτ (by positivity) hM hr hmiss he hperturb hexp).trans (hbound.trans herr)

end ErdosGallai.Sampling

open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Sampling

lemma ofReal_unitInterval (p : unitInterval) :
    ENNReal.ofReal (p : ℝ) = (unitInterval.toNNReal p : ENNReal) := by
  unfold ENNReal.ofReal
  apply congrArg (fun x : NNReal => (x : ENNReal))
  apply Subtype.ext
  exact Real.coe_toNNReal _ p.property.1

lemma labelIs_preserving (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) (i : Fin 3) :
    MeasurePreserving (labelIs i) (reservoirLabelPMF p hp).toMeasure
      (bernoulliMeasure true false p) := by
  have hnon : 0 ≤ (p : ℝ) := p.property.1
  have hnon' : 0 ≤ 1-3*(p : ℝ) := by linarith
  refine ⟨measurable_of_finite _, ?_⟩
  apply Measure.ext_iff_singleton.mpr
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  rw [PMF.toMeasure_apply_fintype]
  simp only [reservoirLabelPMF]
  cases b <;> fin_cases i <;>
    simp [labelIs, Fin.sum_univ_four,  PMF.ofFintype_apply]
  all_goals
    first
    | exact ofReal_unitInterval p
    | rw [← ENNReal.ofReal_add hnon hnon,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ (p : ℝ)+(p : ℝ)) hnon']
      convert ofReal_unitInterval (unitInterval.symm p) using 1
      congr 1
      change (p : ℝ)+(p : ℝ)+(1-3*(p : ℝ)) = 1-(p : ℝ)
      ring

end ErdosGallai.Sampling

namespace ErdosGallai.Sampling
open Finset MeasureTheory ProbabilityTheory
noncomputable section
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

lemma reservoirSample_preserving {V : Type cycleUniverse3} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (p : unitInterval) (hp : 3*(p : ℝ) ≤ 1) (i : Fin 3) :
    MeasurePreserving (reservoirSample i) (reservoirMeasure V p hp) (sampleMeasure V p) := by
  exact measurePreserving_pi _ _ (fun _ => labelIs_preserving p hp i)

lemma reservoirSamples_disjoint {V : Type cycleUniverse4} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (ω : V → Fin 4) (i j : Fin 3) (hij : i ≠ j) :
    Disjoint (sampleVertices (reservoirSample i ω)) (sampleVertices (reservoirSample j ω)) := by
  apply Finset.disjoint_left.mpr
  intro v hi hj
  simp only [sampleVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    reservoirSample, labelIs, decide_eq_true_eq] at hi hj
  exact hij (Fin.castSucc_injective 3 (hi.symm.trans hj))

universe u

theorem three_reservoirs_uniform (c : ℝ) (hc : 0 < c) (p : unitInterval)
    (hp : 0 < (p : ℝ)) (hp3 : 3*(p : ℝ) ≤ 1) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : Fin 3 → SimpleGraph V) [∀ i, DecidableRel (P i).Adj],
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      (∀ i, CutExpansion (P i) (c*D^(9/10 : ℝ))) →
      ∃ W : Fin 3 → Finset V,
        (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
        (∀ i, ((W i).card : ℝ) ≤ 2*(p : ℝ)*Fintype.card V) ∧
        (∀ i v, (p : ℝ)*(c*D^(9/10 : ℝ))/2 ≤ ((neighborsIn (P i) v (W i)).card : ℝ)) ∧
        (∀ i, CutExpansionOn (P i) (W i) (D^(37/50 : ℝ))) := by
  have hp1 : (p : ℝ) < 1 := by linarith
  obtain ⟨D₀,hD₀⟩ := vertex_sampling_uniform.{u} c hc p hp hp1 (1/4) (by norm_num)
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ hlo hhi hcut
  let μ := reservoirMeasure V p hp3
  let B : Fin 3 → Set (V → Fin 4) := fun i =>
    {ω | ¬SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ)) (reservoirSample i ω)}
  have hB : ∀ i, μ.real (B i) ≤ 1/4 := by
    intro i
    have hm := (reservoirSample_preserving (V := V) p hp3 i).measure_preimage
      ((Set.Finite.measurableSet (Set.toFinite {ω | ¬SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ))
        (D^(37/50 : ℝ)) ω})).nullMeasurableSet)
    change (μ (B i)).toReal ≤ 1/4
    rw [show μ (B i) = (sampleMeasure V p) {ω | ¬SampleGood (P i) (p : ℝ)
      (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ)) ω} from hm]
    exact hD₀ D hD V (P i) hlo hhi (hcut i)
  have hi : ∑ i ∈ (Finset.univ : Finset (Fin 3)), μ.real (B i) < 1 := by
    calc
      _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 3)), (1/4 : ℝ) := by
        exact Finset.sum_le_sum (fun i _ => hB i)
      _ < 1 := by norm_num
  obtain ⟨ω,hω⟩ := exists_avoiding_finite_events (μ := μ) Finset.univ B hi
  have hgood : ∀ i, SampleGood (P i) (p : ℝ) (c*D^(9/10 : ℝ)) (D^(37/50 : ℝ))
      (reservoirSample i ω) := by
    intro i
    exact not_not.mp (hω i (Finset.mem_univ i))
  refine ⟨fun i => sampleVertices (reservoirSample i ω), reservoirSamples_disjoint ω,
    fun i => (hgood i).1, fun i => (hgood i).2.1, fun i => (hgood i).2.2⟩

end
end ErdosGallai.Sampling

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.EdgeSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Splitting
open MeasureTheory ProbabilityTheory Finset Real

section BernoulliBounds
variable {Ω : Type cycleUniverse1} {I : Type cycleUniverse2} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma indicator_mem_Icc {Ω : Type cycleUniverse3} [_contextInstance1 : MeasurableSpace Ω] {X : Ω → ℝ} (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (ω : Ω) :
    X ω ∈ Set.Icc (0 : ℝ) 1 := by rcases hX ω with h | h <;> simp [h]

lemma mgf_indicator {X : Ω → ℝ} (hm : Measurable X)
    (hX : ∀ ω, X ω = 0 ∨ X ω = 1) (p t : ℝ) (hp : ∫ ω, X ω ∂μ = p) :
    mgf X μ t = 1 + p * (exp t - 1) := by
  have hXi : Integrable X μ := Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ (indicator_mem_Icc hX))
  have heq : (fun ω => exp (t * X ω)) = fun ω => (1 : ℝ) + (exp t - 1) * X ω := by
    funext ω
    rcases hX ω with h | h <;> simp [h]
  rw [mgf, heq, integral_add (integrable_const _) (hXi.const_mul _), integral_const_mul,
    hp, integral_const]
  simp [mul_comm]

lemma mgf_indicator_sum_bound {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p t : ℝ) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    mgf (∑ i ∈ s, X i) μ t ≤ exp ((s.card : ℝ) * p * (exp t - 1)) := by
  by_cases hs : s.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
  rw [hi.mgf_sum hm]
  have heq : (∏ i ∈ s, mgf (X i) μ t) = (1 + p * (exp t - 1)) ^ s.card := by
    simp_rw [mgf_indicator (hm _) (hX _) p t (hp _)]
    simp
  rw [heq]
  have hn : 0 ≤ 1 + p * (exp t - 1) := by
    obtain ⟨i, _⟩ := hs
    rw [← mgf_indicator (hm i) (hX i) p t (hp i)]
    exact mgf_nonneg
  calc
    (1 + p * (exp t - 1)) ^ s.card ≤ exp (p * (exp t - 1)) ^ s.card :=
      pow_le_pow_left₀ hn (by linarith [add_one_le_exp (p * (exp t - 1))]) _
    _ = _ := by rw [← exp_nat_mul]; congr 1; ring

lemma exp_neg_half_bound : exp (-(1 / 2 : ℝ)) ≤ 5 / 8 := by
  have he : exp (1 / 2 : ℝ) * exp (1 / 2 : ℝ) = exp 1 := by
    rw [← exp_add]; norm_num
  have hlow : (8 / 5 : ℝ) ≤ exp (1 / 2 : ℝ) := by
    nlinarith [exp_one_gt_d9, exp_pos (1 / 2 : ℝ)]
  rw [exp_neg]
  exact (inv_le_comm₀ (exp_pos _) (by norm_num)).mpr (by norm_num at *; exact hlow)

theorem bernoulli_sum_lower_tail {X : I → Ω → ℝ} (s : Finset I)
    (hm : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp0 : 0 ≤ p) (hp : ∀ i, ∫ ω, X i ω ∂μ = p) :
    μ.real {ω | (∑ i ∈ s, X i ω) ≤ p * s.card / 2} ≤ exp (-p * s.card / 8) := by
  have hInt : Integrable (fun ω => exp (-(1 / 2 : ℝ) * (∑ i ∈ s, X i) ω)) μ :=
    hi.integrable_exp_mul_sum hm (fun i _ => integrable_exp_mul_of_mem_Icc
      (hm i).aemeasurable (ae_of_all _ (indicator_mem_Icc (hX i))))
  have hb := measure_le_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (p * s.card / 2)
    (by norm_num : -(1 / 2 : ℝ) ≤ 0) hInt
  simp only [Finset.sum_apply] at hb
  apply hb.trans
  calc
    _ ≤ exp (-(-(1 / 2 : ℝ)) * (p * s.card / 2)) *
        exp ((s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      exact mul_le_mul_of_nonneg_left (mgf_indicator_sum_bound s hm hi hX p _ hp) (exp_pos _).le
    _ = exp (p * s.card / 4 + (s.card : ℝ) * p * (exp (-(1 / 2 : ℝ)) - 1)) := by
      rw [← exp_add]; congr 1; ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left exp_neg_half_bound
        (mul_nonneg (Nat.cast_nonneg s.card) hp0)]

end BernoulliBounds

noncomputable section
variable {V : Type cycleUniverse4} [Fintype V] [DecidableEq V]

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

lemma colorIndicator_indep {V : Type cycleUniverse6} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) :
    iIndepFun (colorIndicator (V := V) i) (edgeColorMeasure V l) := by
  exact iIndepFun_pi (X := fun _ : Sym2 V => fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (fun _ => (measurable_of_finite _).aemeasurable)

lemma colorIndicator_integral {V : Type cycleUniverse7} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {l : ℕ} [NeZero l] (i : Fin l) (e : Sym2 V) :
    ∫ ω, colorIndicator i e ω ∂edgeColorMeasure V l = 1/(l : ℝ) := by
  have hl := (measurePreserving_eval
    (fun _ : Sym2 V => (PMF.uniformOfFintype (Fin l)).toMeasure) e).hasLaw
  have hi := hl.integral_comp (f := fun j : Fin l => if j = i then (1 : ℝ) else 0)
    (measurable_of_finite _).aestronglyMeasurable
  rw [PMF.integral_eq_sum] at hi
  simpa [edgeColorMeasure, colorIndicator, PMF.uniformOfFintype_apply] using hi

lemma colorGraph_interedges {V : Type cycleUniverse8} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S T : Finset V) :
    (colorGraph P ω i).interedges S T =
      (P.interedges S T).filter (fun e => ω s(e.1,e.2) = i) := by
  ext ⟨x,y⟩
  simp only [SimpleGraph.mem_interedges_iff, Finset.mem_filter]
  change (x ∈ S ∧ y ∈ T ∧ (P.Adj x y ∧ ω s(x,y) = i)) ↔ _
  tauto

lemma color_cut_sum (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} (ω : Sym2 V → Fin l) (i : Fin l) (S : Finset V) :
    (∑ e ∈ (P.interedges S Sᶜ).image (fun e => s(e.1,e.2)), colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
  rw [Finset.sum_image (boundary_sym2_injective P S)]
  simp only [colorIndicator, Finset.sum_boole, colorGraph_interedges]

lemma color_cut_lower_tail (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] (i : Fin l) (S : Finset V) {h : ℝ}
    (hexp : CutExpansion P h) (hS : S.card ≤ Sᶜ.card) :
    (edgeColorMeasure V l).real {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ≤
        exp (-h*S.card/(8*l)) := by
  let E := (P.interedges S Sᶜ).image (fun e => s(e.1,e.2))
  have hcard : E.card = (P.interedges S Sᶜ).card :=
    Finset.card_image_of_injOn (boundary_sym2_injective P S)
  have hl : 0 < (l : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne l)
  have hcut : h * S.card ≤ (E.card : ℝ) := by
    rw [hcard]
    have he := hexp S
    rwa [min_eq_left (by exact_mod_cast hS)] at he
  have hb := bernoulli_sum_lower_tail (μ := edgeColorMeasure V l) E
    (fun e => measurable_of_finite (colorIndicator i e)) (colorIndicator_indep i)
    (fun e ω => by simp only [colorIndicator]; split <;> simp)
    (1/(l : ℝ)) (by positivity) (colorIndicator_integral i)
  apply (measureReal_mono (show {ω |
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} ⊆
      {ω | (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2} from ?_)).trans
      (hb.trans ?_)
  · intro ω hω
    change (∑ e ∈ E, colorIndicator i e ω) ≤ (1/(l : ℝ))*E.card/2
    rw [show (∑ e ∈ E, colorIndicator i e ω) =
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) from color_cut_sum P ω i S]
    calc
      _ ≤ h*S.card/(2*l) := le_of_lt hω
      _ ≤ (E.card : ℝ)/(2*l) := div_le_div_of_nonneg_right hcut (by positivity)
      _ = _ := by ring
  · apply exp_le_exp.mpr
    have he := div_le_div_of_nonneg_right hcut (show 0 ≤ 8*(l : ℝ) by positivity)
    calc
      _ = -((E.card : ℝ)/(8*l)) := by ring
      _ ≤ -(h*S.card/(8*l)) := neg_le_neg he
      _ = _ := by ring

lemma cutExpansion_of_small_cuts (P : SimpleGraph V) [DecidableRel P.Adj] {h : ℝ}
    (hcut : ∀ S : Finset V, S.Nonempty → S.card ≤ Sᶜ.card →
      h*S.card ≤ ((P.interedges S Sᶜ).card : ℝ)) : CutExpansion P h := by
  intro S
  by_cases he : S = ∅
  · simp [he]
  by_cases hc : Sᶜ = ∅
  · simp [hc]
  by_cases hs : S.card ≤ Sᶜ.card
  · rw [min_eq_left (by exact_mod_cast hs)]
    exact hcut S (Finset.nonempty_iff_ne_empty.mpr he) hs
  · rw [min_eq_right (by exact_mod_cast le_of_not_ge hs)]
    have hi := hcut Sᶜ (Finset.nonempty_iff_ne_empty.mpr hc) (by simpa using le_of_not_ge hs)
    have hcomm : (P.interedges Sᶜ S).card = (P.interedges S Sᶜ).card := by
      have := P.symm
      exact Rel.card_interedges_comm Sᶜ S
    simpa only [compl_compl, hcomm] using hi

lemma sum_nonempty_subsets_power (q : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset V)).erase ∅, q^S.card) =
      (1+q)^(Fintype.card V)-1 := by
  have hs := Finset.sum_erase_add (s := Finset.univ) (fun S : Finset V => q^S.card)
    (Finset.mem_univ (∅ : Finset V))
  have hp := Finset.prod_one_add (s := (Finset.univ : Finset V)) (f := fun _ => q)
  simp only [Finset.prod_const, Finset.card_univ, Finset.powerset_univ] at hp
  simp only [Finset.card_empty, pow_zero] at hs
  linarith

theorem edge_splitting_failure_bound (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h) :
    (edgeColorMeasure V l).real {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ≤
      l * (exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) := by
  let cuts : Finset (Finset V) := Finset.univ.erase ∅
  let B (i : Fin l) (S : Finset V) : Set (Sym2 V → Fin l) :=
    {ω | S.card ≤ Sᶜ.card ∧
      (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)}
  let q : ℝ := exp (-h/(8*l))
  have cover : {ω | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S := by
    intro ω hω
    rcases hω with ⟨i, hi⟩
    by_contra hn
    apply hi
    apply cutExpansion_of_small_cuts
    intro S hS hs
    have hb : ω ∉ B i S := by
      intro hm
      apply hn
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ _,
        Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr
          ⟨Finset.mem_erase.mpr ⟨hS.ne_empty, Finset.mem_univ _⟩, hm⟩⟩⟩⟩
    have hc : h*S.card/(2*l) ≤ (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) := by
      exact le_of_not_gt (fun hf => hb ⟨hs, hf⟩)
    convert hc using 1 ; ring
  have hbound (i : Fin l) (S : Finset V) :
      (edgeColorMeasure V l).real (B i S) ≤ q^S.card := by
    by_cases hs : S.card ≤ Sᶜ.card
    · calc
        _ ≤ (edgeColorMeasure V l).real {ω |
            (((colorGraph P ω i).interedges S Sᶜ).card : ℝ) < h*S.card/(2*l)} :=
          measureReal_mono (fun _ hw => hw.2)
        _ ≤ exp (-h*S.card/(8*l)) := color_cut_lower_tail P i S hexp hs
        _ = q^S.card := by dsimp [q]; rw [← exp_nat_mul]; congr 1; ring
    · have he : B i S = ∅ := by ext ω; simp [B,hs]
      rw [he, measureReal_empty]
      exact pow_nonneg (exp_pos _).le _
  calc
    _ ≤ (edgeColorMeasure V l).real
        (⋃ i ∈ (Finset.univ : Finset (Fin l)), ⋃ S ∈ cuts, B i S) :=
      measureReal_mono cover (measure_ne_top _ _)
    _ ≤ ∑ i : Fin l, (edgeColorMeasure V l).real (⋃ S ∈ cuts, B i S) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ i : Fin l, ∑ S ∈ cuts, (edgeColorMeasure V l).real (B i S) :=
      Finset.sum_le_sum (fun _ _ => measureReal_biUnion_finset_le _ _)
    _ ≤ ∑ _i : Fin l, ∑ S ∈ cuts, q^S.card := by
      apply Finset.sum_le_sum; intro i _; exact Finset.sum_le_sum (fun S _ => hbound i S)
    _ = (l : ℝ)*((1+q)^(Fintype.card V)-1) := by
      simp only [cuts, sum_nonempty_subsets_power, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ ≤ l*(exp ((Fintype.card V : ℝ)*q)-1) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg l)
      apply sub_le_sub_right
      calc
        _ ≤ (exp q)^(Fintype.card V) :=
          pow_le_pow_left₀ (by dsimp [q]; positivity) (by linarith [add_one_le_exp q]) _
        _ = _ := (exp_nat_mul _ _).symm

theorem edge_splitting_of_error_lt_one (P : SimpleGraph V) [DecidableRel P.Adj]
    {l : ℕ} [NeZero l] {h : ℝ} (hexp : CutExpansion P h)
    (herror : (l : ℝ)*(exp ((Fintype.card V : ℝ)*exp (-h/(8*l)))-1) < 1) :
    ∃ ω : Sym2 V → Fin l,
      (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
      (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
      (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have he := (edge_splitting_failure_bound P hexp).trans_lt herror
  have hh : ∃ ω : Sym2 V → Fin l, ∀ i, CutExpansion (colorGraph P ω i) (h/(2*l)) := by
    by_contra hn
    push Not at hn
    have hall : {ω : Sym2 V → Fin l | ∃ i, ¬CutExpansion (colorGraph P ω i) (h/(2*l))} =
        Set.univ := Set.eq_univ_of_forall hn
    simp only [hall, Measure.real, measure_univ, ENNReal.toReal_one] at he
    exact (lt_irrefl _ he)
  obtain ⟨ω, hω⟩ := hh
  refine ⟨ω, hω, ?_, ?_⟩
  · intro x y
    exact ⟨fun hxy => ⟨ω s(x,y), hxy, rfl⟩, fun ⟨_, hxy, _⟩ => hxy⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro e hei hej
    induction e using Sym2.ind with | _ x y =>
      have hi : (colorGraph P ω i).Adj x y := by simpa using hei
      have hj : (colorGraph P ω j).Adj x y := by simpa using hej
      exact hij (hi.2.symm.trans hj.2)

end

open Filter Asymptotics
open scoped Topology

lemma tendsto_monomial_exp_neg_power (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    Tendsto (fun D : ℝ => D^a * exp (-c * D^b)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a/b) c hc).comp
    (tendsto_rpow_atTop hb)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with D hD
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hD.le, mul_div_cancel₀ _ hb.ne']

lemma edgeSplittingScaleError_tendsto (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    Tendsto (edgeSplittingScaleError c l) atTop (𝓝 0) := by
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have ht := tendsto_monomial_exp_neg_power (51/50) (9/10) (c/(8*l))
    (by norm_num) (by positivity)
  have hh := ((Real.continuous_exp.tendsto 0).comp ht).sub_const 1 |>.const_mul (l : ℝ)
  unfold edgeSplittingScaleError
  convert hh using 1 <;> norm_num

universe u

theorem edge_splitting_uniform (c : ℝ) (hc : 0 < c) (l : ℕ) (hl : 0 < l) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (P : SimpleGraph V) [DecidableRel P.Adj] (h : ℝ),
      c*D^(9/10 : ℝ) ≤ h → D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) → CutExpansion P h →
      ∃ ω : Sym2 V → Fin l,
        (∀ i, CutExpansion (colorGraph P ω i) (h/(2*l))) ∧
        (∀ x y, P.Adj x y ↔ ∃ i, (colorGraph P ω i).Adj x y) ∧
        (∀ i j, i ≠ j → Disjoint (colorGraph P ω i).edgeSet (colorGraph P ω j).edgeSet) := by
  have : NeZero l := ⟨hl.ne'⟩
  have hlR : 0 < (l : ℝ) := by exact_mod_cast hl
  have hevent := (edgeSplittingScaleError_tendsto c hc l hl).eventually_lt_const
    (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨D₀,hD₀⟩ := hevent.exists_forall_of_atTop
  refine ⟨D₀, ?_⟩
  intro D hD V _ _ P _ h hh _hrlo hrhi hexp
  apply edge_splitting_of_error_lt_one P hexp
  apply lt_of_le_of_lt _ (hD₀ D hD)
  unfold edgeSplittingScaleError
  apply mul_le_mul_of_nonneg_left _ hlR.le
  apply sub_le_sub_right
  apply exp_le_exp.mpr
  apply mul_le_mul hrhi _ (exp_pos _).le ((Nat.cast_nonneg (Fintype.card V)).trans hrhi)
  apply exp_le_exp.mpr
  have he := div_le_div_of_nonneg_right hh (show 0 ≤ 8*(l : ℝ) by positivity)
  calc
    -h/(8*l) = -(h/(8*l)) := by ring
    _ ≤ -(c*D^(9/10 : ℝ)/(8*l)) := neg_le_neg he
    _ = -(c/(8*l))*D^(9/10 : ℝ) := by ring

end ErdosGallai.Splitting

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Representatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai.Representatives
noncomputable section
open Finset
variable {I : Type cycleUniverse1} {V : Type cycleUniverse2} [DecidableEq I] [DecidableEq V] [Nonempty V]

lemma choose_with_mates (A : Finset I) (mate : I → I)
    (hmate : Function.Involutive mate) (hfix : ∀ i, mate i ≠ i)
    (N : I → Finset V) (k : ℕ)
    (hroom : ∀ i ∈ A, A.card ≤ ((N i).card - 1) * k) :
    ∃ f : I → V, (∀ i ∈ A, f i ∈ N i) ∧
      (∀ i ∈ A, mate i ∈ A → f i ≠ f (mate i)) ∧
      (∀ v, (A.filter (fun i => f i = v)).card ≤ k) := by
  induction A using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.choice inferInstance, by simp⟩
  | @insert i A hi ih =>
    obtain ⟨f,hf,hsep,hcap⟩ := ih (by
      intro j hj
      exact (Finset.card_le_card (Finset.subset_insert i A)).trans (hroom j (by simp [hj])))
    have hlt : A.card < ((N i).erase (f (mate i))).card * k := by
      have h := hroom i (by simp)
      have hcard := Finset.pred_card_le_card_erase (s := N i) (a := f (mate i))
      have hmul := Nat.mul_le_mul_right k hcard
      rw [Finset.card_insert_of_notMem hi] at h
      omega
    obtain ⟨v,hv,hload⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (f := f) hlt
    have hvN := (Finset.mem_erase.mp hv).2
    have hvne := (Finset.mem_erase.mp hv).1
    let g := Function.update f i v
    have gi : g i = v := by simp [g]
    have gold : ∀ j, j ≠ i → g j = f j := by
      intro j hj
      simp [g, hj]
    refine ⟨g, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [gi] using hvN
      · rw [gold j (ne_of_mem_of_not_mem hj hi)]
        exact hf j hj
    · intro j hj hmj
      by_cases hji : j = i
      · subst j
        rw [gi, gold (mate i) (hfix i)]
        exact hvne
      · rw [gold j hji]
        by_cases hmi : mate j = i
        · rw [hmi, gi]
          have hjm : j = mate i := by rw [← hmi, hmate]
          simpa [hjm] using hvne.symm
        · rw [gold (mate j) hmi]
          exact hsep j (Finset.mem_of_mem_insert_of_ne hj hji)
            (Finset.mem_of_mem_insert_of_ne hmj hmi)
    · intro w
      have hold : A.filter (fun j => g j = w) = A.filter (fun j => f j = w) := by
        apply Finset.filter_congr
        intro j hj
        rw [gold j (ne_of_mem_of_not_mem hj hi)]
      rw [Finset.filter_insert, hold]
      by_cases hvw : v = w
      · simp only [gi, hvw, ite_eq_left]
        rw [Finset.card_insert_of_notMem (fun h => hi (Finset.mem_filter.mp h).1)]
        simpa only [hvw] using Nat.succ_le_of_lt hload
      · simp only [gi, hvw, ite_false]
        exact hcap w

theorem two_distinct_representatives (S : Finset I) (N : I → Finset V) (k : ℕ)
    (hroom : ∀ i ∈ S, 2*S.card ≤ ((N i).card-1)*k) :
    ∃ f : I × Fin 2 → V,
      (∀ i ∈ S, ∀ t, f (i,t) ∈ N i) ∧
      (∀ i ∈ S, f (i,0) ≠ f (i,1)) ∧
      (∀ v, ((S ×ˢ Finset.univ).filter (fun i => f i = v)).card ≤ k) := by
  let mate : I × Fin 2 → I × Fin 2 := fun i => (i.1, 1-i.2)
  have hm : Function.Involutive mate := by
    rintro ⟨i,t⟩
    fin_cases t <;> rfl
  have hfix : ∀ i, mate i ≠ i := by
    rintro ⟨i,t⟩
    fin_cases t <;> (intro h; have hh := congrArg Prod.snd h; norm_num [mate] at hh)
  obtain ⟨f,hf,hsep,hcap⟩ := choose_with_mates (S ×ˢ Finset.univ) mate hm hfix
    (fun i => N i.1) k (by
      intro i hi
      simpa [Finset.card_product, mul_comm] using hroom i.1 (Finset.mem_product.mp hi).1)
  refine ⟨f, ?_, ?_, hcap⟩
  · intro i hi t
    exact hf (i,t) (by simp [hi])
  · intro i hi
    exact hsep (i,0) (by simp [hi]) (by simp [mate, hi])

theorem reservoir_representatives (S : Finset I) (N : I → Finset V)
    (r d : ℝ) (hr : (S.card : ℝ) ≤ r) (hd : 4 ≤ d)
    (hN : ∀ i ∈ S, d/2 ≤ ((N i).card : ℝ)) :
    ∃ f : I × Fin 2 → V,
      (∀ i ∈ S, ∀ t, f (i,t) ∈ N i) ∧
      (∀ i ∈ S, f (i,0) ≠ f (i,1)) ∧
      (∀ v, ((S ×ˢ Finset.univ).filter (fun i => f i = v)).card ≤ ⌈8*r/d⌉₊) := by
  apply two_distinct_representatives
  intro i hi
  have hd0 : 0 < d := by linarith
  have hr0 : 0 ≤ r := le_trans (Nat.cast_nonneg _) hr
  have hNi := hN i hi
  have hNi1 : 1 ≤ (N i).card := by exact_mod_cast (by linarith : (1 : ℝ) ≤ (N i).card)
  have hn : d/4 ≤ (((N i).card - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hNi1]
    push_cast
    linarith
  have hk : 8*r/d ≤ (⌈8*r/d⌉₊ : ℝ) := Nat.le_ceil _
  have hk0 : 0 ≤ (⌈8*r/d⌉₊ : ℝ) := Nat.cast_nonneg _
  have hprod : 2*(S.card : ℝ) ≤ (((N i).card - 1 : ℕ) : ℝ)*(⌈8*r/d⌉₊ : ℝ) := by
    calc
      _ ≤ 2*r := by linarith
      _ = (d/4)*(8*r/d) := by field_simp; ring
      _ ≤ (d/4)*(⌈8*r/d⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hn hk0
  exact_mod_cast hprod

end
end ErdosGallai.Representatives

namespace ErdosGallai
noncomputable section
open Finset Real Filter
attribute [local instance] Classical.propDecidable

universe u

theorem reservoir_preparation (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      D^(9/10 : ℝ) ≤ (Fintype.card V : ℝ) →
      (Fintype.card V : ℝ) ≤ D^(51/50 : ℝ) →
      Splitting.CutExpansion P (c*D^(9/10 : ℝ)) →
      ∃ (ω : Sym2 V → Fin 3) (W : Fin 3 → Finset V) (f : Fin 3 → V × Fin 2 → V),
        (∀ i, Splitting.colorGraph P ω i ≤ G) ∧
        (∀ i j, i ≠ j → Disjoint (Splitting.colorGraph P ω i).edgeSet
            (Splitting.colorGraph P ω j).edgeSet) ∧
        (∀ i, Splitting.CutExpansion (Splitting.colorGraph P ω i)
          (reservoirExpansionCoefficient c * D^(9/10 : ℝ))) ∧
        (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
        (∀ i, 2 ≤ (W i).card) ∧
        (∀ i, ((W i).card : ℝ) ≤ 2*reservoirProbability η*Fintype.card V) ∧
        (∀ i, (W i).card < Fintype.card V) ∧
        ((∑ i, (W i).card : ℕ) : ℝ) ≤ η * Fintype.card V ∧
        (∀ i, Sampling.CutExpansionOn (Splitting.colorGraph P ω i) (W i)
          (D^(37/50 : ℝ))) ∧
        (∀ i v, v ∉ W i → ∀ t, f i (v,t) ∈ W i ∧
          (Splitting.colorGraph P ω i).Adj v (f i (v,t))) ∧
        (∀ i v, v ∉ W i → f i (v,0) ≠ f i (v,1)) ∧
        (∀ i w, (((W i)ᶜ ×ˢ Finset.univ).filter (fun x => f i x = w)).card ≤
          ⌈8*(Fintype.card V : ℝ) /
            (reservoirProbability η * (reservoirExpansionCoefficient c * D^(9/10 : ℝ)))⌉₊) := by
  let c₀ := min c 1
  let a := reservoirExpansionCoefficient c
  let q := reservoirProbability η
  have hc₀ : 0 < c₀ := lt_min hc (by norm_num)
  have ha : 0 < a := by dsimp [a, reservoirExpansionCoefficient]; positivity
  have hq : 0 < q := by dsimp [q, reservoirProbability]; positivity
  have hq12 : q ≤ 1/12 := min_le_right _ _
  have hqη : q ≤ η/12 := min_le_left _ _
  have hq3 : 3*q ≤ 1 := by linarith
  have hq6 : 6*q ≤ η := by linarith
  have hq2 : 2*q < 1 := by linarith
  let p : unitInterval := ⟨q, hq.le, by linarith⟩
  obtain ⟨D₁,hD₁⟩ := Splitting.edge_splitting_uniform.{u} c₀ hc₀ 3 (by norm_num)
  obtain ⟨D₂,hD₂⟩ := Sampling.three_reservoirs_uniform.{u} a ha p hq hq3
  have ht : ∀ᶠ D : ℝ in atTop, 4/(q*a) ≤ D^(9/10 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9/10)).eventually
      (eventually_ge_atTop _)
  obtain ⟨D₃,hD₃⟩ := ht.exists_forall_of_atTop
  refine ⟨max 1 (max D₁ (max D₂ D₃)), ?_⟩
  intro D hD V _ _ G P _ hPG hlo hhi hexp
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hD
  have hDsplit : D₁ ≤ D := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hD
  have hDsample : D₂ ≤ D :=
    (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hD
  have hDpower : D₃ ≤ D :=
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hD
  have hpow : 0 < D^(9/10 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hd : 4 ≤ q*(a*D^(9/10 : ℝ)) := by
    have hh := (div_le_iff₀ (mul_pos hq ha)).mp (hD₃ D hDpower)
    nlinarith
  have hr : 0 < (Fintype.card V : ℝ) := hpow.trans_le hlo
  have : Nonempty V := Fintype.card_pos_iff.mp (by exact_mod_cast hr)
  have hexp₀ : Splitting.CutExpansion P (c₀*D^(9/10 : ℝ)) := by
    intro U
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left c 1) hpow.le)
      (le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans (hexp U)
  obtain ⟨ω,hcut,hcover,hdisj⟩ := hD₁ D hDsplit V P
    (c₀*D^(9/10 : ℝ)) le_rfl hlo hhi hexp₀
  have hcut' : ∀ i, Sampling.CutExpansion (Splitting.colorGraph P ω i)
      (a*D^(9/10 : ℝ)) := by
    intro i
    have heq : a*D^(9/10 : ℝ) = c₀*D^(9/10 : ℝ)/(2*(3 : ℝ)) := by
      dsimp [a, reservoirExpansionCoefficient, c₀]
      ring
    rw [heq]
    exact hcut i
  obtain ⟨W,hWdisj,hWsize,hWneigh,hWcut⟩ := hD₂ D hDsample V
    (fun i => Splitting.colorGraph P ω i) hlo hhi hcut'
  have hWtwo : ∀ i, 2 ≤ (W i).card := by
    intro i
    let v : V := Classical.choice inferInstance
    have hn := hWneigh i v
    have hsub : Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i) ⊆ W i :=
      Finset.filter_subset _ _
    have hh := Finset.card_le_card hsub
    have hn' : (2 : ℝ) ≤ (Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)).card := by
      change q*(a*D^(9/10 : ℝ))/2 ≤ _ at hn
      linarith
    have hn'' : 2 ≤ (Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)).card := by
      exact_mod_cast hn'
    omega
  have hWlt : ∀ i, (W i).card < Fintype.card V := by
    intro i
    have hh := (hWsize i).trans_lt (mul_lt_of_lt_one_left hr hq2)
    exact_mod_cast hh
  have hWsum : ((∑ i, (W i).card : ℕ) : ℝ) ≤ η * Fintype.card V := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hWsize i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    rw [Nat.cast_sum]
    exact hh.trans (by dsimp [p]; nlinarith [mul_le_mul_of_nonneg_right hq6 hr.le])
  have hrep : ∀ i, ∃ f : V × Fin 2 → V,
      (∀ v ∈ (W i)ᶜ, ∀ t, f (v,t) ∈ Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i)) ∧
      (∀ v ∈ (W i)ᶜ, f (v,0) ≠ f (v,1)) ∧
      (∀ w, (((W i)ᶜ ×ˢ Finset.univ).filter (fun x => f x = w)).card ≤
        ⌈8*(Fintype.card V : ℝ)/(q*(a*D^(9/10 : ℝ)))⌉₊) := by
    intro i
    exact Representatives.reservoir_representatives (W i)ᶜ
      (fun v => Sampling.neighborsIn (Splitting.colorGraph P ω i) v (W i))
      (Fintype.card V) (q*(a*D^(9/10 : ℝ)))
      (by exact_mod_cast (Finset.card_le_univ ((W i)ᶜ))) hd
      (fun v _ => hWneigh i v)
  choose f hf hsep hcap using hrep
  refine ⟨ω,W,f,?_,hdisj,?_,hWdisj,hWtwo,hWsize,hWlt,hWsum,hWcut,?_,?_,hcap⟩
  · intro i x y hxy
    exact hPG hxy.1
  · exact hcut'
  · intro i v hv t
    exact Finset.mem_filter.mp (hf i v (Finset.mem_compl.mpr hv) t)
  · intro i v hv
    exact hsep i v (Finset.mem_compl.mpr hv)

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Routing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

open Finset

variable {V : Type} [Fintype V] [DecidableEq V]

lemma boundary_sym2_injective (P : SimpleGraph V) [DecidableRel P.Adj]
    (U : Finset V) :
    Set.InjOn (fun e : V × V => s(e.1, e.2)) (P.interedges U Uᶜ : Set (V × V)) := by
  intro e he f hf hef
  rcases (Sym2.mk_eq_mk_iff.mp hef) with h | h
  · exact h
  · have he1 := (P.mem_interedges_iff.mp he).1
    have hf2 := (P.mem_interedges_iff.mp hf).2.1
    have hfirst : e.1 = f.2 := congrArg Prod.fst h
    exact False.elim ((Finset.mem_compl.mp hf2) (hfirst ▸ he1))

theorem routing_union_growth_step_of_boundary
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h)
    (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (B Bnext : Finset V)
    (W : V → Finset V)
    (hmono : B ⊆ Bnext)
    (hsmall : (B.card : ℝ) ≤ (Fintype.card V : ℝ) / 2)
    (hF : (((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card : ℝ) ≤
      h * (B.card : ℝ) / 4)
    (hW : ∀ v ∈ B, ((W v).card : ℝ) ≤ h / 4)
    (hextend : ∀ v ∈ B, ∀ w ∉ B, P.Adj v w → s(v, w) ∉ F →
      w ∉ W v → w ∈ Bnext) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ) ≤
      (Bnext.card : ℝ) := by
  let E := P.interedges B Bᶜ
  let Ebad := E.filter (fun e => s(e.1, e.2) ∈ F)
  let Vbad := B.biUnion (fun v => ({v} : Finset V) ×ˢ (W v))
  let Enew := (Finset.univ : Finset V) ×ˢ (Bnext \ B)
  have hcover : E ⊆ Ebad ∪ Vbad ∪ Enew := by
    intro e he
    rcases P.mem_interedges_iff.mp he with ⟨hv, hw, hadj⟩
    have hnw : e.2 ∉ B := Finset.mem_compl.mp hw
    by_cases hdel : s(e.1, e.2) ∈ F
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he, hdel⟩))
    by_cases hforbid : e.2 ∈ W e.1
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      exact ⟨e.1, hv, Finset.mem_product.mpr ⟨by simp, hforbid⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr
        ⟨hextend e.1 hv e.2 hnw hadj hdel hforbid, hnw⟩⟩
  have hcount : E.card ≤ Ebad.card + Vbad.card + Enew.card :=
    (Finset.card_le_card hcover).trans <|
      (Finset.card_union_le _ _).trans <|
        Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hforbidden : Vbad.card ≤ ∑ v ∈ B, (W v).card := by
    simpa [Vbad, Finset.card_product] using
      (Finset.card_biUnion_le (s := B) (t := fun v => ({v} : Finset V) ×ˢ W v))
  have hnew : Enew.card = Fintype.card V * (Bnext \ B).card := by
    simp [Enew]
  have hraw : E.card ≤ Ebad.card + (∑ v ∈ B, (W v).card) +
      Fintype.card V * (Bnext \ B).card := by omega
  have hsum : (∑ v ∈ B, ((W v).card : ℝ)) ≤ (h / 4) * B.card := by
    calc
      _ ≤ ∑ _v ∈ B, h / 4 := Finset.sum_le_sum hW
      _ = _ := by simp [mul_comm]
  have hcomplN : B.card + Bᶜ.card = Fintype.card V := by
    rw [Finset.card_compl]
    exact Nat.add_sub_of_le (Finset.card_le_univ B)
  have hcompl : (B.card : ℝ) + (Bᶜ.card : ℝ) = (Fintype.card V : ℝ) := by
    exact_mod_cast hcomplN
  have hlecompl : (B.card : ℝ) ≤ (Bᶜ.card : ℝ) := by linarith
  have hcut : h * (B.card : ℝ) ≤ (E.card : ℝ) := by
    simpa [min_eq_left hlecompl, E] using hexp B
  have hdiffN : (Bnext \ B).card + B.card = Bnext.card := by
    rw [Finset.card_sdiff_of_subset hmono]
    exact Nat.sub_add_cancel (Finset.card_le_card hmono)
  have hdiff : ((Bnext \ B).card : ℝ) + (B.card : ℝ) = (Bnext.card : ℝ) := by
    exact_mod_cast hdiffN
  have hrawR : (E.card : ℝ) ≤ (Ebad.card : ℝ) +
      (∑ v ∈ B, ((W v).card : ℝ)) +
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    exact_mod_cast hraw
  have hreach : h * (B.card : ℝ) / 2 ≤
      (Fintype.card V : ℝ) * ((Bnext \ B).card : ℝ) := by
    nlinarith [hcut, hrawR, hF, hsum]
  have hdiv : h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) ≤
      ((Bnext \ B).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (Fintype.card V : ℝ))).mpr
    nlinarith [hreach]
  calc
    (1 + h / (2 * (Fintype.card V : ℝ))) * (B.card : ℝ)
        = (B.card : ℝ) + h * (B.card : ℝ) / (2 * (Fintype.card V : ℝ)) := by ring
    _ ≤ (B.card : ℝ) + ((Bnext \ B).card : ℝ) := add_le_add (le_refl _) hdiv
    _ = (Bnext.card : ℝ) := by linarith

lemma root_mem_walkBall (G : SimpleGraph V) (s : V) (t : ℕ) :
    s ∈ walkBall G s t := by
  exact (mem_walkBall G s s t).mpr ⟨.nil, by simp⟩

lemma walkBall_mono (G : SimpleGraph V) (s : V) {t u : ℕ} (htu : t ≤ u) :
    walkBall G s t ⊆ walkBall G s u := by
  intro v hv
  obtain ⟨p, hp⟩ := (mem_walkBall G s v t).mp hv
  exact (mem_walkBall G s v u).mpr ⟨p, hp.trans htu⟩

lemma walk_avoids_end {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s v : V} (p : (avoidGraph P F W).Walk s v) (hs : s ∉ W) : v ∉ W := by
  induction p with
  | nil => exact hs
  | cons hadj p ih => exact ih hadj.2.2.2

lemma ball_avoids (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    (s : V) (hs : s ∉ W) (t : ℕ) : Disjoint (walkBall (avoidGraph P F W) s t) W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  obtain ⟨p, _⟩ := (mem_walkBall _ _ _ _).mp hv
  exact walk_avoids_end P F W p hs

lemma walkBall_step (G : SimpleGraph V) (s v w : V) (t : ℕ)
    (hv : v ∈ walkBall G s t) (hadj : G.Adj v w) :
    w ∈ walkBall G s (t + 1) := by
  obtain ⟨p, hp⟩ := (mem_walkBall _ _ _ _).mp hv
  apply (mem_walkBall _ _ _ _).mpr
  exact ⟨p.concat hadj, by simpa using Nat.add_le_add_right hp 1⟩

lemma CutExpansion.le_order (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V) :
    h ≤ (Fintype.card V : ℝ) := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
  have hcomplN : 1 ≤ ({v} : Finset V)ᶜ.card := by
    simp only [Finset.card_compl, Finset.card_singleton]
    omega
  have hcompl : (1 : ℝ) ≤ (({v} : Finset V)ᶜ.card : ℝ) := by exact_mod_cast hcomplN
  have hc := hexp {v}
  simp only [Finset.card_singleton, Nat.cast_one, min_eq_left hcompl, mul_one] at hc
  have hupper := P.card_interedges_le_mul ({v} : Finset V) ({v} : Finset V)ᶜ
  simp only [Finset.card_singleton, one_mul] at hupper
  have hle := (Finset.card_le_univ (({v} : Finset V)ᶜ))
  exact hc.trans (by exact_mod_cast hupper.trans hle)

lemma routingG_growth (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    r / 2 < (1 + h / (2 * r)) ^ routingG r h := by
  have hr0 : 0 < r := by linarith
  let x := h / (2 * r)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 2 * r)).mpr
    linarith
  have hlog : h / (4 * r) ≤ Real.log (1 + h / (2 * r)) := by
    have heq : h / (4 * r) = x / 2 := by dsimp [x]; ring
    rw [heq]
    calc
      x / 2 ≤ 2 * x / (x + 2) := by
        apply (le_div_iff₀ (by linarith : 0 < x + 2)).mpr
        nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hxle)]
      _ ≤ Real.log (1 + x) := Real.le_log_one_add_of_nonneg hx0
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2le : Real.log 2 ≤ 1 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at htwo ⊢
    exact htwo
  have hlogpos : 0 < Real.log (2 * r) := Real.log_pos (by linarith)
  have hbase : Real.log (2 * r) ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2pos).mpr
    nlinarith
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) :=
    Nat.le_ceil _
  have hlogpow : 2 * Real.log (2 * r) ≤
      Real.log ((1 + h / (2 * r)) ^ routingG r h) := by
    rw [Real.log_pow]
    calc
      2 * Real.log (2 * r) ≤ 2 * Real.logb 2 (2 * r) := by linarith
      _ = (8 * (r / h) * Real.logb 2 (2 * r)) * (h / (4 * r)) := by
        field_simp
        ; ring
      _ ≤ (routingG r h : ℝ) * (h / (4 * r)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      _ ≤ (routingG r h : ℝ) * Real.log (1 + h / (2 * r)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  have hsmall : Real.log (r / 2) < 2 * Real.log (2 * r) := by
    have := Real.log_le_log (by positivity : 0 < r / 2) (by linarith : r / 2 ≤ 2 * r)
    linarith
  apply (Real.log_lt_log_iff (by positivity : 0 < r / 2) (by positivity)).mp
  exact hsmall.trans_le hlogpow

lemma incidentEdges_union {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (F E : Finset (Sym2 V)) (v : V) :
    incidentEdges (F ∪ E) v = incidentEdges F v ∪ incidentEdges E v := by
  simp [incidentEdges, Finset.filter_union]

lemma incidentEdges_union_card_le (F E : Finset (Sym2 V)) (v : V) :
    (incidentEdges (F ∪ E) v).card ≤ (incidentEdges F v).card + (incidentEdges E v).card := by
  rw [incidentEdges_union]
  exact Finset.card_union_le _ _

lemma incidentEdges_sum_le (F : Finset (Sym2 V)) :
    ∑ v : V, (incidentEdges F v).card ≤ 2 * F.card := by
  have heq : ∑ v : V, (incidentEdges F v).card = ∑ e ∈ F, e.toFinset.card := by
    simp only [incidentEdges, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    simp [← Sym2.mem_toFinset]
  rw [heq]
  calc
    _ ≤ ∑ _e ∈ F, 2 := Finset.sum_le_sum (fun e _ => by
      rw [Sym2.card_toFinset]
      split <;> norm_num)
    _ = 2 * F.card := by simp [mul_comm]

lemma incidentEdges_path_start_le_one {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset s).card ≤ 1 := by
  have hsub : incidentEdges p.edges.toFinset s ⊆ {s(s, p.snd)} := by
    intro e he
    obtain ⟨heP, hs⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hev⟩ := Sym2.mem_iff_exists.mp hs
    subst e
    have hv := hp.eq_snd_of_mem_edges (List.mem_toFinset.mp heP)
    simp [hv]
  exact (Finset.card_le_card hsub).trans (by simp)

lemma incidentEdges_path_end_le_one (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) :
    (incidentEdges p.edges.toFinset t).card ≤ 1 := by
  simpa using incidentEdges_path_start_le_one G p.reverse hp.reverse

lemma incidentEdges_walk_eq_empty_of_not_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (G : SimpleGraph V) {s t v : V}
    (p : G.Walk s t) (hv : v ∉ p.support) : incidentEdges p.edges.toFinset v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heP, hve⟩ := Finset.mem_filter.mp he
  have hm := p.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, List.mem_toFinset.mp heP, hve⟩)
  exact hv hm

lemma incidentEdges_path_le_two (G : SimpleGraph V) {s t : V}
    (p : G.Walk s t) (hp : p.IsPath) (v : V) :
    (incidentEdges p.edges.toFinset v).card ≤ 2 := by
  by_cases hv : v ∈ p.support
  · have htake := incidentEdges_path_end_le_one G (p.takeUntil v hv) (hp.takeUntil hv)
    have hdrop := incidentEdges_path_start_le_one G (p.dropUntil v hv) (hp.dropUntil hv)
    have heq : p.edges.toFinset = (p.takeUntil v hv).edges.toFinset ∪ (p.dropUntil v hv).edges.toFinset := by
      have he := congrArg (fun q : G.Walk s t => q.edges.toFinset) (p.take_spec hv)
      simpa only [SimpleGraph.Walk.edges_append, List.toFinset_append] using he.symm
    rw [heq]
    exact (incidentEdges_union_card_le _ _ v).trans (by omega)
  · rw [incidentEdges_walk_eq_empty_of_not_mem G p hv]
    simp

lemma deleted_boundary_card_le_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (B : Finset V) (F : Finset (Sym2 V)) :
    ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤
      ∑ v ∈ B, (incidentEdges F v).card := by
  let T := B.biUnion (fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  have hc : ((P.interedges B Bᶜ).filter (fun e => s(e.1, e.2) ∈ F)).card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun e : V × V => (e.1, s(e.1, e.2)))
    · intro e he
      obtain ⟨heP, heF⟩ := Finset.mem_filter.mp he
      apply Finset.mem_biUnion.mpr
      refine ⟨e.1, (P.mem_interedges_iff.mp heP).1, Finset.mem_product.mpr ⟨by simp, ?_⟩⟩
      exact Finset.mem_filter.mpr ⟨heF, by simp⟩
    · intro e he f hf heq
      have hsym := congrArg Prod.snd heq
      exact boundary_sym2_injective P B (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf).1 hsym
  have hT : T.card ≤ ∑ v ∈ B, (incidentEdges F v).card := by
    simpa [T] using Finset.card_biUnion_le (s := B)
      (t := fun v => ({v} : Finset V) ×ˢ incidentEdges F v)
  exact hc.trans hT

lemma walkBall_growth_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hexp : CutExpansion P h) (hr : 0 < (Fintype.card V : ℝ))
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) (t : ℕ)
    (hsmall : ((walkBall (avoidGraph P F W) s t).card : ℝ) ≤ (Fintype.card V : ℝ) / 2) :
    (1 + h / (2 * (Fintype.card V : ℝ))) * (walkBall (avoidGraph P F W) s t).card ≤
      ((walkBall (avoidGraph P F W) s (t + 1)).card : ℝ) := by
  classical
  apply routing_union_growth_step_of_boundary P h hexp hr F _ _ (fun _ => W)
      (walkBall_mono _ s (Nat.le_succ t)) hsmall
  · calc
      _ ≤ ∑ v ∈ walkBall (avoidGraph P F W) s t, ((incidentEdges F v).card : ℝ) := by
        exact_mod_cast deleted_boundary_card_le_incidents P (walkBall (avoidGraph P F W) s t) F
      _ ≤ ∑ _v ∈ walkBall (avoidGraph P F W) s t, h / 4 := Finset.sum_le_sum (fun v _ => hF v)
      _ = _ := by simp; ring
  · exact fun _ _ => hW
  · intro v hv w _ hadj hdel hw
    have hnv := Finset.disjoint_left.mp (ball_avoids P F W s hs t) hv
    exact walkBall_step _ s v w t hv ⟨hadj, hdel, hnv, hw⟩

lemma walkBall_large_of_incidents (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s : V) (hs : s ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    (Fintype.card V : ℝ) / 2 <
      (walkBall (avoidGraph P F W) s (routingG (Fintype.card V) h)).card := by
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < Fintype.card V := by linarith
  let g := routingG (Fintype.card V) h
  let c : ℝ := 1 + h / (2 * (Fintype.card V : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  by_contra hnot
  have hend := le_of_not_gt hnot
  have hpow : ∀ j ≤ g, c ^ j ≤ (walkBall (avoidGraph P F W) s j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have H := Finset.card_pos.mpr ⟨s, root_mem_walkBall (avoidGraph P F W) s 0⟩
      have H' : 1 ≤ (walkBall (avoidGraph P F W) s 0).card := H
      simpa using (Nat.cast_le (α := ℝ)).mpr H'
    | succ j ih =>
      intro hj
      have hmono : ((walkBall (avoidGraph P F W) s j).card : ℝ) ≤
          (walkBall (avoidGraph P F W) s g).card := by
        exact_mod_cast Finset.card_le_card (walkBall_mono (avoidGraph P F W) s (by omega : j ≤ g))
      have hsmall := hmono.trans hend
      calc
        c ^ (j + 1) = c * c ^ j := by rw [pow_succ]; ring
        _ ≤ c * (walkBall (avoidGraph P F W) s j).card := mul_le_mul_of_nonneg_left (ih (by omega)) hc
        _ ≤ (walkBall (avoidGraph P F W) s (j + 1)).card :=
          walkBall_growth_of_incidents P h hexp hr0 F W s hs hF hW j hsmall
  have hg := routingG_growth (Fintype.card V) h (by linarith) hh (hexp.le_order P h hr)
  exact (not_lt_of_ge ((hpow g le_rfl).trans hend)) hg

lemma exists_short_avoiding_path (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : (avoidGraph P F W).Walk s t, q.IsPath ∧
      q.length ≤ 2 * routingG (Fintype.card V) h := by
  classical
  let g := routingG (Fintype.card V) h
  let B₁ := walkBall (avoidGraph P F W) s g
  let B₂ := walkBall (avoidGraph P F W) t g
  have h₁ := walkBall_large_of_incidents P h hh hexp hr F W s hs hF hW
  have h₂ := walkBall_large_of_incidents P h hh hexp hr F W t ht hF hW
  have hmeet : (B₁ ∩ B₂).Nonempty := by
    apply Finset.card_pos.mp
    have hc := Finset.card_union_add_card_inter B₁ B₂
    have hu := Finset.card_le_univ (B₁ ∪ B₂)
    have hsum : (Fintype.card V : ℝ) < (B₁.card : ℝ) + (B₂.card : ℝ) := by
      dsimp [B₁, B₂, g]; linarith
    have hsumN : Fintype.card V < B₁.card + B₂.card := by exact_mod_cast hsum
    omega
  obtain ⟨v, hv⟩ := hmeet
  obtain ⟨p₁, hp₁⟩ := (mem_walkBall _ s v g).mp (Finset.mem_inter.mp hv).1
  obtain ⟨p₂, hp₂⟩ := (mem_walkBall _ t v g).mp (Finset.mem_inter.mp hv).2
  let w := p₁.append p₂.reverse
  refine ⟨w.bypass, w.bypass_isPath, w.length_bypass_le_length.trans ?_⟩
  dsimp [w]
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  omega

lemma two_routingG_le_length (r h : ℝ) : 2 * routingG r h ≤ routingLength r h := by
  dsimp [routingLength]
  exact Nat.le_mul_of_pos_right _ (by omega)

lemma routingLength_bounds (r h : ℝ) (hr : 1 ≤ r) (hh : 0 < h) :
    1 ≤ routingLength r h ∧ r ≤ (routingLength r h : ℝ) * h := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 1 ≤ Real.logb 2 (2 * r) := by
    rw [Real.logb]
    apply (le_div_iff₀ hl2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ 2 * r)
  have hg : 8 * (r / h) * Real.logb 2 (2 * r) ≤ (routingG r h : ℝ) := Nat.le_ceil _
  have hgh : 8 * r ≤ (routingG r h : ℝ) * h := by
    calc
      8 * r = (8 * (r / h)) * h := by field_simp
      _ ≤ (8 * (r / h) * Real.logb 2 (2 * r)) * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        simpa using mul_le_mul_of_nonneg_left hlog (show 0 ≤ 8 * (r / h) by positivity)
      _ ≤ (routingG r h : ℝ) * h := mul_le_mul_of_nonneg_right hg hh.le
  have hgpos : 0 < routingG r h := by
    have hgR : (0 : ℝ) < routingG r h := by nlinarith
    exact_mod_cast hgR
  have hgle : routingG r h ≤ routingLength r h := (by omega : routingG r h ≤ 2 * routingG r h).trans (two_routingG_le_length r h)
  refine ⟨by omega, ?_⟩
  have hgleR : (routingG r h : ℝ) ≤ routingLength r h := by exact_mod_cast hgle
  nlinarith

lemma routing_budget (L k b z h r : ℝ) (hL : 1 ≤ L) (hk : 1 ≤ k)
    (hb : 1 ≤ b) (hz : 0 ≤ z) (hh : 0 < h) (_hr : 0 ≤ r)
    (hreach : r ≤ L * h) (hbudget : 64 * (L ^ 2 * (k + b) + z) ≤ h) :
    h / 8 + 2 + k ≤ h / 4 ∧ z + b * L ≤ h / 8 ∧ 64 * L * k * r ≤ h ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have hk0 : 0 ≤ k := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hLs : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hLLs : L ≤ L ^ 2 := by nlinarith
  have hbig : 64 * (k + b) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_right hLs (by linarith : 0 ≤ k + b)]
      _ ≤ _ := hbudget
  have hbL : 64 * (b * L + z) ≤ h := by
    calc
      _ ≤ 64 * (L ^ 2 * (k + b) + z) := by nlinarith [mul_le_mul_of_nonneg_left hLLs hb0, mul_nonneg (sq_nonneg L) hk0]
      _ ≤ _ := hbudget
  have hkL : 64 * L ^ 2 * k ≤ h := by nlinarith [mul_nonneg (sq_nonneg L) hb0]
  refine ⟨by linarith, by linarith, ?_⟩
  calc
    64 * L * k * r ≤ 64 * L * k * (L * h) := mul_le_mul_of_nonneg_left hreach (by positivity)
    _ = (64 * L ^ 2 * k) * h := by ring
    _ ≤ h * h := mul_le_mul_of_nonneg_right hkL hh.le
    _ = h ^ 2 := by ring

lemma saturated_card_le (F : Finset (Sym2 V)) (h : ℝ) (hh : 0 < h)
    (hF : 128 * (F.card : ℝ) ≤ h ^ 2) : (saturated F h).card ≤ h / 8 := by
  classical
  have hs : h / 8 * (saturated F h).card ≤ ∑ v : V, ((incidentEdges F v).card : ℝ) := by
    calc
      _ = ∑ _v ∈ saturated F h, h / 8 := by simp [mul_comm]
      _ ≤ ∑ v ∈ saturated F h, ((incidentEdges F v).card : ℝ) := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
  have hsum : (∑ v : V, ((incidentEdges F v).card : ℝ)) ≤ 2 * (F.card : ℝ) := by
    exact_mod_cast incidentEdges_sum_le F
  nlinarith

lemma pathInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : SimpleGraph V} {s t : V} (q : P.Walk s t) :
    (pathInterior q).card ≤ q.length := by
  have hp := List.toFinset_card_le q.support
  rw [q.length_support] at hp
  have hstart : s ∈ q.support.toFinset ∩ ({s, t} : Finset V) := by simp
  have hint := Finset.card_pos.mpr ⟨s, hstart⟩
  have hd := Finset.card_sdiff_add_card_inter q.support.toFinset ({s, t} : Finset V)
  dsimp [pathInterior]
  omega

lemma avoidGraph_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V) :
    avoidGraph P F W ≤ P := fun _ _ h => h.1

lemma walk_avoids_support (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) (hs : s ∉ W) :
    Disjoint q.support.toFinset W := by
  apply Finset.disjoint_left.mpr
  intro v hv
  exact walk_avoids_end P F W (q.takeUntil v (List.mem_toFinset.mp hv)) hs

lemma walk_avoids_edges {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : SimpleGraph V) (F : Finset (Sym2 V)) (W : Finset V)
    {s t : V} (q : (avoidGraph P F W).Walk s t) :
    Disjoint q.edges.toFinset F := by
  apply Finset.disjoint_left.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | hf v w => exact (q.adj_of_mem_edges (List.mem_toFinset.mp he)).2.1

lemma exists_short_path_with_avoidance (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (F : Finset (Sym2 V)) (W : Finset V) (s t : V) (hs : s ∉ W) (ht : t ∉ W)
    (hF : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4)
    (hW : (W.card : ℝ) ≤ h / 4) :
    ∃ q : P.Walk s t, q.IsPath ∧ q.length ≤ routingLength (Fintype.card V) h ∧
      Disjoint q.edges.toFinset F ∧ Disjoint q.support.toFinset W := by
  obtain ⟨q, hp, hl⟩ := exists_short_avoiding_path P h hh hexp hr F W s t hs ht hF hW
  refine ⟨q.mapLe (avoidGraph_le P F W), hp.mapLe _, ?_, ?_, ?_⟩
  · simpa using hl.trans (two_routingG_le_length (Fintype.card V) h)
  · simpa using walk_avoids_edges P F W q
  · simpa using walk_avoids_support P F W q hs

lemma route_degree_update {P : SimpleGraph V} {s t : V} (q : P.Walk s t)
    (hp : q.IsPath) (F : Finset (Sym2 V)) (h : ℝ) (load : V → ℕ)
    (hdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 8 + 2 + load v)
    (havoid : Disjoint q.support.toFinset (saturated F h \ {s, t})) (v : V) :
    ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      h / 8 + 2 + load v + (if v = s ∨ v = t then 1 else 0) := by
  classical
  have hadd : ((incidentEdges (F ∪ q.edges.toFinset) v).card : ℝ) ≤
      (incidentEdges F v).card + (incidentEdges q.edges.toFinset v).card := by
    exact_mod_cast incidentEdges_union_card_le F q.edges.toFinset v
  by_cases hv : v = s ∨ v = t
  · rw [ite_eq_left hv]
    have hqN : (incidentEdges q.edges.toFinset v).card ≤ 1 := by
      rcases hv with rfl | rfl
      · exact incidentEdges_path_start_le_one P q hp
      · exact incidentEdges_path_end_le_one P q hp
    have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 1 := by exact_mod_cast hqN
    linarith [hdegree v]
  · rw [ite_eq_right hv]
    by_cases hmem : v ∈ q.support
    · have hns : v ∉ saturated F h := by
        intro hsat
        apply Finset.disjoint_left.mp havoid (List.mem_toFinset.mpr hmem)
        exact Finset.mem_sdiff.mpr ⟨hsat, by simpa using hv⟩
      have hsmall : ((incidentEdges F v).card : ℝ) < h / 8 := by
        simpa [saturated] using hns
      have hq : ((incidentEdges q.edges.toFinset v).card : ℝ) ≤ 2 := by
        exact_mod_cast incidentEdges_path_le_two P q hp v
      have : (0 : ℝ) ≤ load v := by positivity
      linarith
    · rw [incidentEdges_walk_eq_empty_of_not_mem P q hmem] at hadd
      simp only [Finset.card_empty, Nat.cast_zero, add_zero] at hadd
      linarith [hdegree v]

section Families
variable {I T : Type} [Fintype I] [DecidableEq I] [DecidableEq T]
variable {P : SimpleGraph V} {x y : I → V}

lemma endpointLoad_mono {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {A B : Finset I} (hAB : A ⊆ B) (x y : I → V) (v : V) :
    endpointLoad A x y v ≤ endpointLoad B x y v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hAB)

lemma endpointLoad_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (i : I) (hi : i ∉ A) (x y : I → V) (v : V) :
    endpointLoad (insert i A) x y v = endpointLoad A x y v +
      (if v = x i ∨ v = y i then 1 else 0) := by
  classical
  by_cases hv : v = x i ∨ v = y i
  · have hv' : x i = v ∨ y i = v := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv', hi]
  · have hv' : ¬ (x i = v ∨ y i = v) := by simpa [eq_comm] using hv
    simp [endpointLoad, Finset.filter_insert, hv, hv']

lemma endpointLoad_sum {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] (A : Finset I) (x y : I → V) (hxy : ∀ i ∈ A, x i ≠ y i) :
    ∑ v : V, endpointLoad A x y v = 2 * A.card := by
  classical
  simp only [endpointLoad, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have heq : ∀ i ∈ A, (∑ v : V, if x i = v ∨ y i = v then 1 else 0) = 2 := by
    intro i hi
    have hf : (Finset.univ.filter fun v => x i = v ∨ y i = v) = ({x i, y i} : Finset V) := by
      ext v
      simp [eq_comm]
    have hc : ({x i, y i} : Finset V).card = 2 := by simp [hxy i hi]
    rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    _ = ∑ _i ∈ A, 2 := Finset.sum_congr rfl heq
    _ = _ := by simp [mul_comm]

lemma usedEdges_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ i, P.Walk (x i) (y i)) (L : ℕ)
    (hq : ∀ i ∈ A, (q i).length ≤ L) : (usedEdges A q).card ≤ L * A.card := by
  calc
    _ ≤ ∑ i ∈ A, (q i).edges.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A, L := Finset.sum_le_sum (fun i hi => by
      have hc := List.toFinset_card_le (q i).edges
      simpa using hc.trans (by simpa using hq i hi))
    _ = _ := by simp [mul_comm]

lemma usedEdges_update_insert {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} [_contextInstance4 : Fintype I] [_contextInstance5 : DecidableEq I] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (i : I) (hi : i ∉ A)
    (q : ∀ j, P.Walk (x j) (y j)) (p : P.Walk (x i) (y i)) :
    usedEdges (insert i A) (Function.update q i p) = usedEdges A q ∪ p.edges.toFinset := by
  classical
  rw [usedEdges, Finset.biUnion_insert]
  simp only [Function.update_self]
  rw [Finset.union_comm]
  congr 1
  apply Finset.biUnion_congr rfl
  intro j hj
  have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
  rw [Function.update_of_ne hji]

lemma teamInterior_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {I : Type} {T : Type} [_contextInstance5 : Fintype I] [_contextInstance6 : DecidableEq I] [_contextInstance7 : DecidableEq T] {P : SimpleGraph V} {x : I → V} {y : I → V} (A : Finset I) (q : ∀ j, P.Walk (x j) (y j))
    (team : I → T) (i : I) (L : ℕ) (b : ℝ)
    (hq : ∀ j ∈ A, (q j).length ≤ L)
    (hb : ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b) :
    ((teamInterior A q team i).card : ℝ) ≤ b * L := by
  have hc : (teamInterior A q team i).card ≤ L * (A.filter (fun j => team j = team i)).card := by
    calc
      _ ≤ ∑ j ∈ A.filter (fun j => team j = team i), (pathInterior (q j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ A.filter (fun j => team j = team i), L := Finset.sum_le_sum (fun j hj =>
        (pathInterior_card_le (q j)).trans (hq j (Finset.mem_filter.mp hj).1))
      _ = _ := by simp [mul_comm]
  have hcard : ((A.filter (fun j => team j = team i)).card : ℝ) ≤ b := by
    apply le_trans _ hb
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))
  have hcR : ((teamInterior A q team i).card : ℝ) ≤ (L : ℝ) * (A.filter (fun j => team j = team i)).card := by exact_mod_cast hc
  calc
    _ ≤ (L : ℝ) * b := hcR.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
    _ = _ := mul_comm _ _

theorem routing (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (hxy : ∀ i, x i ≠ y i) (team : I → T) (Z : I → Finset V)
    (k b z : ℝ) (hk : 1 ≤ k) (hb : 1 ≤ b) (hz : 0 ≤ z)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hteam : ∀ i, ((Finset.univ.filter (fun j => team j = team i)).card : ℝ) ≤ b)
    (hZ : ∀ i, ((Z i).card : ℝ) ≤ z)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ) ^ 2 * (k + b) + z) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h ∧
        Disjoint (pathInterior (q i)) (Z i)) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) ∧
      (∀ i j, i ≠ j → team i = team j → Disjoint (pathInterior (q i)) (pathInterior (q j))) := by
  classical
  let L := routingLength (Fintype.card V) h
  have hrR : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hr
  obtain ⟨hL, hreach⟩ := routingLength_bounds (Fintype.card V) h (by linarith) hh
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  obtain ⟨hdegBudget, hforbidBudget, hnumBudget⟩ := routing_budget L k b z h (Fintype.card V)
    hLR hk hb hz hh (by positivity) hreach hbudget
  have hloadA : ∀ (A : Finset I) v, (endpointLoad A x y v : ℝ) ≤ k := by
    intro A v
    have hm : (endpointLoad A x y v : ℝ) ≤ endpointLoad Finset.univ x y v := by
      exact_mod_cast endpointLoad_mono (Finset.subset_univ A) x y v
    exact hm.trans (hload v)
  have htotal : 2 * (Fintype.card I : ℝ) ≤ k * Fintype.card V := by
    have heq := endpointLoad_sum Finset.univ x y (fun i _ => hxy i)
    have heqR : (∑ v : V, (endpointLoad Finset.univ x y v : ℝ)) = 2 * Fintype.card I := by
      exact_mod_cast heq
    rw [← heqR]
    calc
      _ ≤ ∑ _v : V, k := Finset.sum_le_sum (fun v _ => hload v)
      _ = _ := by simp [mul_comm]
  have hdefault : ∀ i, ∃ p : P.Walk (x i) (y i), p.IsPath := by
    intro i
    obtain ⟨p, hp, _⟩ := exists_short_path_with_avoidance P h hh hexp hr ∅ ∅ (x i) (y i)
      (by simp) (by simp) (by intro v; simp [incidentEdges]; positivity) (by simp; positivity)
    exact ⟨p, hp⟩
  choose defaultPath hdefaultPath using hdefault
  have hpartial : ∀ A : Finset I, ∃ q : ∀ i, P.Walk (x i) (y i), PartialRoutes P x y team Z L h A q := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨defaultPath, ?_⟩
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
      · intro v
        simp only [usedEdges, Finset.biUnion_empty, incidentEdges, Finset.filter_empty,
          Finset.card_empty, Nat.cast_zero, endpointLoad, add_zero]
        linarith
    | @insert i A hi ih =>
      obtain ⟨q, hq⟩ := ih
      let F := usedEdges A q
      let S := saturated F h
      let B := teamInterior A q team i
      let W := (S ∪ Z i ∪ B) \ {x i, y i}
      have hFcard : 128 * (F.card : ℝ) ≤ h ^ 2 := by
        have hc : (F.card : ℝ) ≤ (L : ℝ) * A.card := by
          exact_mod_cast usedEdges_card_le A q L hq.short
        have ha : (A.card : ℝ) ≤ Fintype.card I := by exact_mod_cast Finset.card_le_univ A
        have hsize : 2 * (A.card : ℝ) ≤ k * Fintype.card V := by linarith
        have hmult := mul_le_mul_of_nonneg_left hsize (show 0 ≤ (L : ℝ) by positivity)
        nlinarith [hnumBudget]
      have hS : (S.card : ℝ) ≤ h / 8 := saturated_card_le F h hh hFcard
      have hB : (B.card : ℝ) ≤ b * L := teamInterior_card_le A q team i L b hq.short (hteam i)
      have hW : (W.card : ℝ) ≤ h / 4 := by
        have hc : W.card ≤ S.card + (Z i).card + B.card :=
          (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_right (Finset.card_union_le _ _) _))
        have hcR : (W.card : ℝ) ≤ (S.card : ℝ) + (Z i).card + B.card := by exact_mod_cast hc
        linarith [hZ i]
      have hFdegree : ∀ v, ((incidentEdges F v).card : ℝ) ≤ h / 4 := by
        intro v
        have hd := hq.degree v
        have hl := hloadA A v
        dsimp [F]
        linarith
      obtain ⟨p, hp, hpL, hpF, hpW⟩ := exists_short_path_with_avoidance P h hh hexp hr F W (x i) (y i)
        (by simp [W]) (by simp [W]) hFdegree hW
      have hpZ : Disjoint (pathInterior p) (Z i) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvZ
        obtain ⟨hvp, hvends⟩ := Finset.mem_sdiff.mp hv
        apply Finset.disjoint_left.mp hpW hvp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hvZ), hvends⟩
      have hpS : Disjoint p.support.toFinset (saturated F h \ {x i, y i}) := by
        apply Finset.disjoint_left.mpr
        intro v hv hvS
        obtain ⟨hs, he⟩ := Finset.mem_sdiff.mp hvS
        apply Finset.disjoint_left.mp hpW hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hs), he⟩
      have hpEdge : ∀ j ∈ A, Disjoint p.edges.toFinset (q j).edges.toFinset := by
        intro j hj
        apply Finset.disjoint_left.mpr
        intro e hep heq
        exact Finset.disjoint_left.mp hpF hep (Finset.mem_biUnion.mpr ⟨j, hj, heq⟩)
      have hpTeam : ∀ j ∈ A, team i = team j → Disjoint (pathInterior p) (pathInterior (q j)) := by
        intro j hj htm
        apply Finset.disjoint_left.mpr
        intro v hvp hvq
        obtain ⟨hvp', hvends⟩ := Finset.mem_sdiff.mp hvp
        apply Finset.disjoint_left.mp hpW hvp'
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_right _ ?_, hvends⟩
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, htm.symm⟩, hvq⟩
      let q' := Function.update q i p
      have hsame : q' i = p := Function.update_self i p q
      have hother : ∀ j ∈ A, q' j = q j := by
        intro j hj
        apply Function.update_of_ne
        intro hji
        exact hi (hji ▸ hj)
      refine ⟨q', ?_⟩
      constructor
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hp
        · simpa only [hother j hj] using hq.simple j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpL
        · simpa only [hother j hj] using hq.short j hj
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [hsame] using hpZ
        · simpa only [hother j hj] using hq.avoids j hj
      · intro j hj k hk hjk
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpEdge k hkA
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpEdge j hjA).symm
          · simpa only [hother j hjA, hother k hkA] using hq.edge_disjoint j hjA k hkA hjk
      · intro j hj k hk hjk htm
        rcases Finset.mem_insert.mp hj with rfl | hjA
        · have hkA : k ∈ A := (Finset.mem_insert.mp hk).resolve_left (Ne.symm hjk)
          simpa only [hsame, hother k hkA] using hpTeam k hkA htm
        · rcases Finset.mem_insert.mp hk with rfl | hkA
          · simpa only [hsame, hother j hjA] using (hpTeam j hjA htm.symm).symm
          · simpa only [hother j hjA, hother k hkA] using hq.team_disjoint j hjA k hkA hjk htm
      · intro v
        have heq : usedEdges (insert i A) q' = F ∪ p.edges.toFinset := usedEdges_update_insert A i hi q p
        rw [heq]
        have hu := route_degree_update p hp F h (endpointLoad A x y) hq.degree hpS v
        have hloadEq : (endpointLoad (insert i A) x y v : ℝ) =
            endpointLoad A x y v + (if v = x i ∨ v = y i then (1 : ℝ) else 0) := by
          rw [endpointLoad_insert A i hi]
          split_ifs <;> simp
        rw [hloadEq]
        simpa only [add_assoc] using hu
  obtain ⟨q, hq⟩ := hpartial Finset.univ
  exact ⟨q, fun i => ⟨hq.simple i (by simp), hq.short i (by simp), hq.avoids i (by simp)⟩,
    fun i j hij => hq.edge_disjoint i (by simp) j (by simp) hij,
    fun i j hij htm => hq.team_disjoint i (by simp) j (by simp) hij htm⟩

end Families
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ReservoirCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
open Real Filter Asymptotics

lemma routing_length_upper (r h : ℝ) (hr : 2 ≤ r) (hh : 0 < h) (hhr : h ≤ r) :
    (routingLength r h : ℝ) ≤ 108*(r/h)*(logb 2 r)^2 := by
  have hr0 : 0 < r := by linarith
  have hl : 1 ≤ logb 2 r := by
    simpa using Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by norm_num : (0:ℝ) < 2) hr
  have hR : 1 ≤ r/h := (le_div_iff₀ hh).mpr (by simpa using hhr)
  have hlog : logb 2 (2*r) = 1 + logb 2 r := by
    rw [Real.logb_mul (by norm_num) hr0.ne']
    norm_num
  have hg := Nat.ceil_lt_add_one (show 0 ≤ 8*(r/h)*logb 2 (2*r) by rw [hlog]; positivity)
  have hd := Nat.ceil_lt_add_one (show 0 ≤ logb 2 r by linarith)
  change (routingG r h : ℝ) < 8*(r/h)*logb 2 (2*r)+1 at hg
  change (routingDepth r : ℝ) < logb 2 r + 1 at hd
  rw [hlog] at hg
  have hprod : 1 ≤ (r/h)*logb 2 r := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hl)]
  have hg' : (routingG r h : ℝ) ≤ 18*(r/h)*logb 2 r := by nlinarith
  have hd' : (1 + routingDepth r : ℝ) ≤ 3*logb 2 r := by linarith
  have hm := mul_le_mul hg' hd' (by positivity) (by positivity)
  dsimp [routingLength]
  push_cast
  nlinarith

lemma eventually_logb_le_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, logb 2 D ≤ D^ε := by
  have ho := (isLittleO_log_rpow_atTop hε).const_mul_left (1 / log 2)
  filter_upwards [ho.eventuallyLE, eventually_ge_atTop (1:ℝ)] with D hD h1
  simpa [Real.logb, div_eq_mul_inv, mul_comm, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg h1), abs_of_nonneg (Real.rpow_nonneg (by linarith) ε),
    abs_of_pos (show 0 < (log 2)⁻¹ by positivity),
    abs_of_pos (Real.log_pos (by norm_num : (1:ℝ) < 2))] using hD

lemma eventually_constant_le_power (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C ≤ D^ε :=
  (tendsto_rpow_atTop hε).eventually (eventually_ge_atTop C)

lemma eventually_const_mul_power_le (C α β : ℝ) (hab : α < β) :
    ∀ᶠ D : ℝ in atTop, C*D^α ≤ D^β := by
  filter_upwards [eventually_constant_le_power C (β-α) (by linarith),
    eventually_gt_atTop (0:ℝ)] with D hc hD
  calc
    C*D^α ≤ D^(β-α)*D^α := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hD.le _)
    _ = D^β := by rw [← Real.rpow_add hD]; congr 1; ring

theorem eventually_routing_length (c β γ δ : ℝ) (hc : 0 < c) (hβ : 0 < β)
    (hδ : 0 < δ) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 2 ≤ r → r ≤ D^β → c*D^γ ≤ r →
      (routingLength r (c*D^γ) : ℝ) ≤ D^(β-γ+δ) := by
  filter_upwards [eventually_logb_le_power (δ/4) (by positivity),
    eventually_constant_le_power (108*β^2/c) (δ/2) (by positivity),
    eventually_gt_atTop (1:ℝ)] with D hlog hconst hD r hr hrD hhr
  have hD0 : 0 < D := by linarith
  have hpowγ : 0 < D^γ := Real.rpow_pos_of_pos hD0 _
  have hden : 0 < c*D^γ := mul_pos hc hpowγ
  have hlog0 : 0 ≤ logb 2 r := (Real.logb_pos (by norm_num) (by linarith)).le
  have hlogR : logb 2 r ≤ β*D^(δ/4) := by
    have hh := Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
      (by linarith : 0 < r) hrD
    rw [Real.logb_rpow_eq_mul_logb_of_pos hD0] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlog hβ.le)
  have hratio : r/(c*D^γ) ≤ D^(β-γ)/c := by
    calc
      _ ≤ D^β/(c*D^γ) := div_le_div_of_nonneg_right hrD hden.le
      _ = _ := by rw [Real.rpow_sub hD0]; ring
  have hsq : (logb 2 r)^2 ≤ β^2*D^(δ/2) := by
    calc
      _ ≤ (β*D^(δ/4))^2 := pow_le_pow_left₀ hlog0 hlogR 2
      _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hD0.le]; congr 2; ring
  calc
    (routingLength r (c*D^γ) : ℝ) ≤ 108*(r/(c*D^γ))*(logb 2 r)^2 :=
      routing_length_upper r (c*D^γ) hr hden hhr
    _ ≤ 108*(D^(β-γ)/c)*(β^2*D^(δ/2)) := by gcongr
    _ = (108*β^2/c)*D^(β-γ+δ/2) := by rw [Real.rpow_add hD0]; ring
    _ ≤ D^(δ/2)*D^(β-γ+δ/2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hD0.le _)
    _ = D^(β-γ+δ) := by rw [← Real.rpow_add hD0]; congr 1; ring

lemma eventually_reservoir_capacity (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∀ᶠ D : ℝ in atTop, ∀ r : ℝ, 0 ≤ r → r ≤ D^(51/50:ℝ) →
      (⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ) ≤ D^(13/100:ℝ) := by
  filter_upwards [eventually_const_mul_power_le (8/(p*c)+1) (3/25) (13/100) (by norm_num),
    eventually_gt_atTop (1:ℝ)] with D hbound hD r hr hrD
  have hD0 : 0 < D := by linarith
  have hden : 0 < p*(c*D^(9/10:ℝ)) := by positivity
  have hone : 1 ≤ D^(3/25:ℝ) := Real.one_le_rpow hD.le (by norm_num)
  have hx : 8*r/(p*(c*D^(9/10:ℝ))) ≤ (8/(p*c))*D^(3/25:ℝ) := by
    calc
      _ ≤ 8*D^(51/50:ℝ)/(p*(c*D^(9/10:ℝ))) := by gcongr
      _ = _ := by
        have heq : D^(3/25:ℝ) = D^(51/50:ℝ)/D^(9/10:ℝ) := by
          rw [← Real.rpow_sub hD0]; norm_num
        rw [heq]; ring
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ 8*r/(p*(c*D^(9/10:ℝ))) by positivity)
  nlinarith only [hx, hceil, hone, hbound]

theorem residue_routing_margin (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ r rᵢ : ℝ,
      0 ≤ r → r ≤ D^(51/50:ℝ) → 2 ≤ rᵢ → rᵢ ≤ r → D^(37/50:ℝ) ≤ rᵢ →
      64*((routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1)) ≤ D^(37/50:ℝ) := by
  have hev : ∀ᶠ D : ℝ in atTop, ∀ r rᵢ : ℝ,
      0 ≤ r → r ≤ D^(51/50:ℝ) → 2 ≤ rᵢ → rᵢ ≤ r → D^(37/50:ℝ) ≤ rᵢ →
      64*((routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1)) ≤ D^(37/50:ℝ) := by
    filter_upwards [eventually_routing_length 1 (51/50) (37/50) (1/100)
      (by norm_num) (by norm_num) (by norm_num),
      eventually_reservoir_capacity c p hc hp,
      eventually_const_mul_power_le 128 (71/100) (37/50) (by norm_num),
      eventually_gt_atTop (1:ℝ)] with D hlen hcap hcost hD r rᵢ hr hrD hri2 hrir htau
    have hD0 : 0 < D := by linarith
    have hL := hlen rᵢ hri2 (hrir.trans hrD) (by simpa using htau)
    norm_num at hL
    have hk := hcap r hr hrD
    have hone : 1 ≤ D^(13/100:ℝ) := Real.one_le_rpow hD.le (by norm_num)
    have hprod : (routingLength rᵢ (D^(37/50:ℝ)) : ℝ)^2*
        ((⌈8*r/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ)+1) ≤ 2*D^(71/100:ℝ) := by
      calc
        _ ≤ (D^(29/100:ℝ))^2 * (2*D^(13/100:ℝ)) := by gcongr; linarith
        _ = _ := by
          rw [← Real.rpow_mul_natCast hD0.le]
          norm_num
          rw [mul_left_comm, ← Real.rpow_add hD0]
          norm_num
    nlinarith only [hprod, hcost]
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

lemma subtype_image_compl {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (W : Finset V) (U : Finset (W : Set V)) :
    Uᶜ.image Subtype.val = W \ U.image Subtype.val := by
  ext v
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_sdiff]
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨x.property,?_⟩
    rintro ⟨y,hy,he⟩
    exact hx (Subtype.ext he ▸ hy)
  · rintro ⟨hv,hvU⟩
    refine ⟨⟨v,hv⟩,?_,rfl⟩
    intro hx
    exact hvU ⟨⟨v,hv⟩,hx,rfl⟩

lemma induced_interedges_card (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (U : Finset (W : Set V)) :
    (((P.induce (W : Set V)).interedges U Uᶜ).card : ℝ) =
      ((P.interedges (U.image Subtype.val) (W \ U.image Subtype.val)).card : ℝ) := by
  classical
  let f : ↥(W : Set V) × ↥(W : Set V) → V × V := fun e => (e.1.val,e.2.val)
  have hf : Function.Injective f := by
    intro a b h
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have heq : ((P.induce (W : Set V)).interedges U Uᶜ).image f =
      P.interedges (U.image Subtype.val) (W \ U.image Subtype.val) := by
    rw [← subtype_image_compl W U]
    ext e
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_image]
    constructor
    · rintro ⟨a,⟨ha,hb,hab⟩,rfl⟩
      exact ⟨⟨a.1,ha,rfl⟩,⟨a.2,hb,rfl⟩,hab⟩
    · rintro ⟨⟨x,hx,hxe⟩,⟨y,hy,hye⟩,he⟩
      refine ⟨(x,y),⟨hx,hy,?_⟩,Prod.ext hxe hye⟩
      change P.Adj x.val y.val
      simpa only [hxe,hye] using he
  rw [← heq, Finset.card_image_of_injective _ hf]

lemma cutExpansion_induce (P : SimpleGraph V) [DecidableRel P.Adj]
    (W : Finset V) (h : ℝ) (hexp : CutExpansionOn P W h) :
    CutExpansion (P.induce (W : Set V)) h := by
  classical
  intro U
  have hsub : U.image Subtype.val ⊆ W := by
    rintro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact a.property
  have h := hexp (U.image Subtype.val) hsub
  have he : W \ U.image Subtype.val = Uᶜ.image Subtype.val :=
    (subtype_image_compl W U).symm
  rw [he] at h
  simp only [Finset.card_image_of_injective _ Subtype.val_injective] at h
  rw [induced_interedges_card,he]
  exact h

theorem routing_allow_equal {I : Type} [Fintype I]
    (P : SimpleGraph V) [DecidableRel P.Adj]
    (h : ℝ) (hh : 0 < h) (hexp : CutExpansion P h) (hr : 2 ≤ Fintype.card V)
    (x y : I → V) (k : ℝ) (hk : 1 ≤ k)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hbudget : 64 * ((routingLength (Fintype.card V) h : ℝ)^2 * (k+1)) ≤ h) :
    ∃ q : ∀ i, P.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength (Fintype.card V) h) ∧
      (∀ i j, i ≠ j → Disjoint (q i).edges.toFinset (q j).edges.toFinset) := by
  classical
  let J := {i : I // x i ≠ y i}
  have hjload (v : V) :
      (endpointLoad Finset.univ (fun i : J => x i.val) (fun i : J => y i.val) v : ℝ) ≤ k := by
    apply le_trans _ (hload v)
    exact_mod_cast (show endpointLoad Finset.univ (fun i : J => x i.val)
        (fun i : J => y i.val) v ≤ endpointLoad Finset.univ x y v from by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
      · intro a _ b _ hab
        exact Subtype.ext hab)
  obtain ⟨q,hq,hd,_⟩ := routing P h hh hexp hr
    (fun i : J => x i.val) (fun i : J => y i.val) (fun i => i.property)
    (fun i : J => i) (fun _ => ∅) k 1 0 hk (by norm_num) (by norm_num) hjload
    (by
      intro i
      have he : (univ.filter (fun j : J => j = i)) = {i} := by ext j; simp
      rw [he]; simp) (by intro i; simp) (by simpa only [add_zero] using hbudget)
  let Q : ∀ i, P.Walk (x i) (y i) := fun i =>
    if hi : x i = y i then (SimpleGraph.Walk.nil : P.Walk (x i) (x i)).copy rfl hi
    else q ⟨i,hi⟩
  refine ⟨Q,?_,?_⟩
  · intro i
    by_cases hi : x i = y i
    · simp [Q,hi]
    · simpa only [Q,dite_eq_right hi] using ⟨(hq ⟨i,hi⟩).1,(hq ⟨i,hi⟩).2.1⟩
  · intro i j hij
    by_cases hi : x i = y i
    · simp [Q,hi]
    by_cases hj : x j = y j
    · simp [Q,hj]
    simp only [Q,dite_eq_right hi,dite_eq_right hj]
    exact hd ⟨i,hi⟩ ⟨j,hj⟩ (fun he => hij (congrArg Subtype.val he))

theorem routing_in_reservoir {I : Type} [Fintype I]
    (G P : SimpleGraph V) [DecidableRel P.Adj] (hPG : P ≤ G)
    (W : Finset V) (h : ℝ) (hh : 0 < h)
    (hexp : CutExpansionOn P W h) (hr : 2 ≤ W.card)
    (x y : I → V) (hx : ∀ i, x i ∈ W) (hy : ∀ i, y i ∈ W)
    (k : ℝ) (hk : 1 ≤ k)
    (hload : ∀ v, (endpointLoad Finset.univ x y v : ℝ) ≤ k)
    (hbudget : 64 * ((routingLength W.card h : ℝ)^2 * (k+1)) ≤ h) :
    ∃ q : ∀ i, G.Walk (x i) (y i),
      (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card h ∧
        ∀ v ∈ (q i).support, v ∈ W) ∧
      Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) := by
  classical
  let X : I → (W : Set V) := fun i => ⟨x i,hx i⟩
  let Y : I → (W : Set V) := fun i => ⟨y i,hy i⟩
  have hl (v : (W : Set V)) : (endpointLoad univ X Y v : ℝ) ≤ k := by
    simpa only [endpointLoad,X,Y,Subtype.ext_iff] using hload v.val
  obtain ⟨q,hq,hd⟩ := routing_allow_equal (P.induce (W : Set V)) h hh
    (cutExpansion_induce P W h hexp) (by simpa using hr) X Y k hk hl
    (by simpa using hbudget)
  let f : (P.induce (W : Set V)) →g G :=
    { toFun := Subtype.val, map_rel' := fun ha => hPG ha }
  have hf : Function.Injective f := Subtype.val_injective
  have hcard : Fintype.card ↥(W : Set V) = W.card := Fintype.card_coe W
  let Q : ∀ i, G.Walk (x i) (y i) := fun i => (q i).map f
  refine ⟨Q,?_,?_⟩
  · intro i
    refine ⟨(hq i).1.map hf,?_,?_⟩
    · simpa only [Q,SimpleGraph.Walk.length_map, hcard] using (hq i).2
    · intro v hv
      have hv' : v ∈ (q i).support.map f := by simpa only [Q,SimpleGraph.Walk.support_map] using hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv'
      exact a.property
  · intro i j hij
    change Disjoint ((q i).map f).edgeSet ((q j).map f).edgeSet
    rw [SimpleGraph.Walk.edgeSet_map,SimpleGraph.Walk.edgeSet_map]
    rw [Set.disjoint_image_iff (Sym2.map.injective hf)]
    apply Set.disjoint_left.mpr
    intro e he he'
    exact Finset.disjoint_left.mp (hd i j hij)
      (by simpa using he) (by simpa using he')

theorem uniform_reservoir_routing (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V),
      (∀ i, x i ∈ W) → (∀ i, y i ∈ W) →
      (∀ v, endpointLoad univ x y v ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ q : ∀ i, G.Walk (x i) (y i),
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(37/50:ℝ)) ∧
          ∀ v ∈ (q i).support, v ∈ W) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) := by
  obtain ⟨D₀,hD₀,hmargin⟩ := residue_routing_margin c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y hx hy hl
  have hDpos : 0 < D := lt_trans (by norm_num) (hD₀.trans_le hD)
  have horder : (D^(37/50:ℝ)) ≤ (W.card : ℝ) := by
    simpa using (cutExpansion_induce P W _ hexp).le_order (P.induce (W:Set V)) _
      (by simpa using hW)
  have hWupper : (W.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast W.card_le_univ
  have hrpos : 0 < (Fintype.card V : ℝ) := by
    have hWreal : (2:ℝ) ≤ W.card := by exact_mod_cast hW
    linarith
  have hk : 1 ≤ (⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊ : ℝ) := by
    have hceil : 0 < ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊ :=
      Nat.ceil_pos.mpr (by positivity)
    exact_mod_cast hceil
  apply routing_in_reservoir G P hPG W (D^(37/50:ℝ)) (by positivity) hexp hW
    x y hx hy _ hk (by intro v; exact_mod_cast hl v)
  exact hmargin D hD _ _ hrpos.le hr (by exact_mod_cast hW) hWupper horder

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

theorem occurrence_slots {A : Type cycleUniverse1} {V : Type cycleUniverse2} [Fintype A] (f : A → V) (k : ℕ)
    (h : ∀ v, Fintype.card {a // f a = v} ≤ k) :
    ∃ slot : A → Fin k, Function.Injective (fun a => (f a, slot a)) := by
  classical
  have he : ∀ v, Nonempty ({a // f a = v} ↪ Fin k) := by
    intro v
    exact Function.Embedding.nonempty_of_card_le (by simpa using h v)
  let e := fun v => Classical.choice (he v)
  refine ⟨fun a => e (f a) ⟨a,rfl⟩, ?_⟩
  intro a b hab
  have hf : f a = f b := congrArg Prod.fst hab
  have hs : e (f a) ⟨a,rfl⟩ = e (f b) ⟨b,rfl⟩ := congrArg Prod.snd hab
  have hσ : (⟨f a, e (f a) ⟨a,rfl⟩⟩ : Σ _ : V, Fin k) =
      ⟨f b, e (f b) ⟨b,rfl⟩⟩ := Sigma.ext hf (heq_of_eq hs)
  let E : (Σ v, {a // f a = v}) ↪ (Σ _ : V, Fin k) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl V) e
  have heq : (⟨f a, ⟨a,rfl⟩⟩ : Σ v, {a // f a = v}) = ⟨f b, ⟨b,rfl⟩⟩ :=
    E.injective hσ
  exact congrArg (fun z : Σ v, {a // f a = v} => z.2.val) heq

theorem endpoint_occurrence_slots {I : Type cycleUniverse5} {V : Type cycleUniverse6} [Fintype I]
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (hload : ∀ v, (univ.filter (fun i => x i = v ∨ y i = v)).card ≤ 2) :
    ∃ slot : I × Fin 2 → Fin 2,
      Function.Injective (fun a => (endpointOccurrence x y a, slot a)) := by
  classical
  apply occurrence_slots
  intro v
  let f : {a : I × Fin 2 // endpointOccurrence x y a = v} →
      {i : I // x i = v ∨ y i = v} := fun a =>
    ⟨a.val.1, by
      by_cases h0 : a.val.2 = 0
      · exact Or.inl (by simpa [endpointOccurrence,h0] using a.property)
      · exact Or.inr (by simpa [endpointOccurrence,h0] using a.property)⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hi : a.val.1 = b.val.1 := congrArg Subtype.val hab
    apply Prod.ext hi
    by_contra ht
    have hcases : (a.val.2 = 0 ∧ b.val.2 ≠ 0) ∨ (a.val.2 ≠ 0 ∧ b.val.2 = 0) := by
      have ha := (a.val.2).isLt
      have hb := (b.val.2).isLt
      have hne : (a.val.2).val ≠ (b.val.2).val := fun h => ht (Fin.ext h)
      simp only [Fin.ext_iff, Fin.val_zero]
      omega
    rcases hcases with h | h
    · have ha : x a.val.1 = v := by simpa [endpointOccurrence,h.1] using a.property
      have hb : y b.val.1 = v := by simpa [endpointOccurrence,h.2] using b.property
      exact hne _ (ha.trans (hi ▸ hb).symm)
    · have ha : y a.val.1 = v := by simpa [endpointOccurrence,h.1] using a.property
      have hb : x b.val.1 = v := by simpa [endpointOccurrence,h.2] using b.property
      exact hne _ ((hi ▸ hb).trans ha.symm)
  exact (Fintype.card_le_of_injective f hf).trans (by simpa only [Fintype.card_subtype] using hload v)

theorem reserved_edges_injective {A : Type cycleUniverse7} {V : Type cycleUniverse8} (S W : Set V)
    (f : A → V) (slot : A → Fin 2) (r : V × Fin 2 → V)
    (hslots : Function.Injective (fun a => (f a,slot a)))
    (hout : ∀ a, f a ∈ S) (hin : ∀ v ∈ S, ∀ t, r (v,t) ∈ W)
    (hdisj : Disjoint S W) (hr : ∀ v ∈ S, r (v,0) ≠ r (v,1)) :
    Function.Injective (fun a => s(f a,r (f a,slot a))) := by
  intro a b hab
  rcases Sym2.eq_iff.mp hab with he | he
  · have hf : f a = f b := he.1
    have hh : r (f a,slot a) = r (f b,slot b) := he.2
    apply hslots
    apply Prod.ext hf
    have hrinj : Function.Injective (fun t : Fin 2 => r (f a,t)) := by
      intro i j hij
      have h0 := hr (f a) (hout a)
      fin_cases i <;> fin_cases j
      · rfl
      · exact (h0 hij).elim
      · exact (h0 hij.symm).elim
      · rfl
    exact hrinj (by simpa only [hf] using hh)
  · have hf : f a = r (f b,slot b) := he.1
    exact False.elim (Set.disjoint_left.mp hdisj (hout a)
      (hf.symm ▸ hin (f b) (hout b) (slot b)))

theorem assigned_representative_load {A : Type cycleUniverse9} {V : Type cycleUniverse10} [Fintype A] [DecidableEq V]
    (S : Finset V) (f : A → V) (slot : A → Fin 2) (r : V × Fin 2 → V)
    (hslots : Function.Injective (fun a => (f a,slot a)))
    (hout : ∀ a, f a ∈ S) (k : ℕ)
    (hcap : ∀ v, ((S ×ˢ univ).filter (fun a => r a = v)).card ≤ k) :
    ∀ v, (univ.filter (fun a => r (f a,slot a) = v)).card ≤ k := by
  classical
  intro v
  apply le_trans (Finset.card_le_card_of_injOn (fun a => (f a,slot a)) ?_ ?_) (hcap v)
  · intro a ha
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hout a,mem_univ _⟩, (mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact hslots hab

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset
attribute [local instance] Classical.propDecidable

theorem choose_reservoir_endpoints {V I : Type} [Fintype V] [Fintype I]
    [DecidableEq V] (P : SimpleGraph V) (W : Finset V)
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (houtx : ∀ i, x i ∉ W) (houty : ∀ i, y i ∉ W)
    (hload : ∀ v, endpointLoad univ x y v ≤ 2)
    (r : V × Fin 2 → V)
    (hr : ∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t)))
    (hrne : ∀ v, v ∉ W → r (v,0) ≠ r (v,1))
    (k : ℕ) (hcap : ∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤ k) :
    ∃ a b : I → V,
      (∀ i, a i ∈ W ∧ P.Adj (x i) (a i)) ∧
      (∀ i, b i ∈ W ∧ P.Adj (y i) (b i)) ∧
      Function.Injective (fun z : I × Fin 2 =>
        if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
      (∀ v, endpointLoad univ a b v ≤ k) ∧
      (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) := by
  classical
  obtain ⟨slot,hslot⟩ := endpoint_occurrence_slots x y hne (fun v => by
    convert hload v using 1
    congr 1
    ext i
    simp only [ Finset.mem_filter, Finset.mem_univ, true_and])
  let occ := endpointOccurrence x y
  have ho : ∀ z : I × Fin 2, occ z ∉ W := by
    rintro ⟨i,t⟩
    by_cases h : t = 0
    · simpa [occ,endpointOccurrence,h] using houtx i
    · simpa [occ,endpointOccurrence,h] using houty i
  let a := fun i => r (x i,slot (i,0))
  let b := fun i => r (y i,slot (i,1))
  have hsp := reserved_edges_injective (Wᶜ : Finset V) W occ slot r hslot
    (fun z => Finset.mem_compl.mpr (ho z))
    (fun v hv t => (hr v (Finset.mem_compl.mp hv) t).1)
    (Set.disjoint_left.mpr (fun _ hv hw => (Finset.mem_compl.mp hv) hw))
    (fun v hv => hrne v (Finset.mem_compl.mp hv))
  have hcap' := assigned_representative_load Wᶜ occ slot r hslot
    (fun z => Finset.mem_compl.mpr (ho z)) k hcap
  refine ⟨a,b,(fun i => hr _ (houtx i) _),(fun i => hr _ (houty i) _),?_,?_,?_,?_⟩
  · have heq : (fun z : I × Fin 2 =>
        if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) =
        (fun z => s(occ z,r (occ z,slot z))) := by
      funext z
      rcases z with ⟨i,t⟩
      fin_cases t <;> simp [occ,endpointOccurrence,a,b]
    rw [heq]
    exact hsp
  · intro v
    apply le_trans (Finset.card_le_card_of_injOn
      (fun i => (i,if a i = v then (0 : Fin 2) else 1)) ?_ ?_) (hcap' v)
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      by_cases hi0 : a i = v
      · simp [hi0,occ,endpointOccurrence,a]
      · have hi1 : b i = v := hi'.resolve_left hi0
        simpa [hi0,occ,endpointOccurrence,b] using hi1
    · intro i hi j hj he
      exact congrArg Prod.fst he
  · intro i; exact ⟨slot (i,0),rfl⟩
  · intro i; exact ⟨slot (i,1),rfl⟩

theorem uniform_assigned_reservoir_routing (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V),
      (∀ i, x i ≠ y i) → (∀ i, x i ∉ W) → (∀ i, y i ∉ W) →
      (∀ v, endpointLoad univ x y v ≤ 2) →
      ∀ r : V × Fin 2 → V,
      (∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t))) →
      (∀ v, v ∉ W → r (v,0) ≠ r (v,1)) →
      (∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ (a b : I → V) (q : ∀ i, G.Walk (a i) (b i)),
        (∀ i, G.Adj (x i) (a i) ∧ G.Adj (y i) (b i)) ∧
        Function.Injective (fun z : I × Fin 2 =>
          if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
        (∀ i, (q i).IsPath ∧ (q i).length ≤ routingLength W.card (D^(37/50:ℝ)) ∧
          ∀ v ∈ (q i).support, v ∈ W) ∧
        Pairwise (fun i j => Disjoint (q i).edgeSet (q j).edgeSet) ∧
        (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) ∧
        (∀ i, (q i).edgeSet ⊆ P.edgeSet) := by
  obtain ⟨D₀,hD₀,hroute⟩ := uniform_reservoir_routing c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y hne hx hy hl r hrep hrepne hcap
  obtain ⟨a,b,ha,hb,hs,hl',ha',hb'⟩ :=
    choose_reservoir_endpoints P W x y hne hx hy hl r hrep hrepne _ hcap
  obtain ⟨q,hq,hd⟩ := hroute D hD V P P le_rfl W hexp hW hr I a b
    (fun i => (ha i).1) (fun i => (hb i).1) hl'
  let Q : ∀ i, G.Walk (a i) (b i) := fun i => (q i).mapLe hPG
  refine ⟨a,b,Q,(fun i => ⟨hPG (ha i).2,hPG (hb i).2⟩),hs,?_,?_,ha',hb',?_⟩
  · intro i
    refine ⟨(hq i).1.mapLe hPG,?_,?_⟩
    · simpa only [Q, SimpleGraph.Walk.length_mapLe] using (hq i).2.1
    · simpa only [Q, SimpleGraph.Walk.support_mapLe_eq_support] using (hq i).2.2
  · intro i j hij
    simpa only [Q, SimpleGraph.Walk.edgeSet_mapLe_eq_edgeSet] using hd hij
  · intro i
    rw [show (Q i).edgeSet = (q i).edgeSet from (q i).edgeSet_mapLe_eq_edgeSet hPG]
    intro e he
    exact (q i).edges_subset_edgeSet he

end
end ErdosGallai

namespace ErdosGallai
open SimpleGraph

variable {V : Type cycleUniverse11} {G : SimpleGraph V} {x y a b : V}

lemma reservoirReturn_isPath (Q : G.Walk x y) (P : G.Walk a b)
    (hQ : Q.IsPath) (hQpos : 0 < Q.length) (hP : P.IsPath)
    (hdisj : Q.support.Disjoint P.support) (hx : G.Adj x a) (hy : G.Adj y b) :
    (reservoirReturn P hx hy).IsPath := by
  have hxy : x ≠ y := by
    intro h
    subst y
    have := hQ.nil_iff_eq.mpr rfl
    have hz : Q.length = 0 := this.length_eq_zero
    omega
  have hxP : x ∉ P.reverse.support := by
    simpa using hdisj Q.start_mem_support
  have hyP : y ∉ P.reverse.support := by
    simpa using hdisj Q.end_mem_support
  exact (hP.reverse.concat hxP hx.symm).cons (by simpa using And.intro hyP hxy.symm)

theorem reservoir_path_closure (Q : G.Walk x y) (P : G.Walk a b)
    (hQ : Q.IsPath) (hQpos : 0 < Q.length) (hP : P.IsPath)
    (hdisj : Q.support.Disjoint P.support) (hx : G.Adj x a) (hy : G.Adj y b) :
    (Q.append (reservoirReturn P hx hy)).IsCycle ∧
    (Q.append (reservoirReturn P hx hy)).edgeSet =
      Q.edgeSet ∪ P.edgeSet ∪ {s(x,a), s(y,b)} ∧
    3 ≤ (Q.append (reservoirReturn P hx hy)).length := by
  have hreturn := reservoirReturn_isPath Q P hQ hQpos hP hdisj hx hy
  have htail : Q.support.tail.Disjoint (reservoirReturn P hx hy).support.tail := by
    rw [List.disjoint_left]
    intro v hv
    have hvQ := List.mem_of_mem_tail hv
    have hvP : v ∉ P.support := hdisj hvQ
    have hvx : v ≠ x := by
      have hn := hQ.support_nodup
      rw [← Q.cons_tail_support, List.nodup_cons] at hn
      exact fun heq => hn.1 (heq ▸ hv)
    simpa [reservoirReturn] using And.intro hvP hvx
  have hcycle := hQ.isCycle_append hreturn htail (Or.inr (by simp [reservoirReturn]))
  refine ⟨hcycle, ?_, ?_⟩
  · ext e
    simp only [Walk.edgeSet_append, reservoirReturn, Walk.edgeSet_cons,
      Walk.edgeSet_concat, Walk.edgeSet_reverse, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rw [Sym2.eq_swap (a := x) (b := a)]
    tauto
  · simpa [reservoirReturn] using (by omega : 3 ≤ Q.length + (P.length + 1 + 1))

end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

lemma spoke_sets_pairwise {I : Type cycleUniverse12} {E : Type cycleUniverse13} (e : I × Fin 2 → E)
    (he : Function.Injective e) :
    Pairwise (fun i j => Disjoint ({e (i,0), e (i,1)} : Set E) {e (j,0), e (j,1)}) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro a hai haj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hai haj
  rcases hai with hai | hai <;> rcases haj with haj | haj
  all_goals exact hij (congrArg Prod.fst (he (hai.symm.trans haj)))

lemma pairwise_union_three {I : Type cycleUniverse14} {E : Type cycleUniverse15} (A B S : I → Set E)
    (hA : Pairwise fun i j => Disjoint (A i) (A j))
    (hB : Pairwise fun i j => Disjoint (B i) (B j))
    (hS : Pairwise fun i j => Disjoint (S i) (S j))
    (hAB : ∀ i j, Disjoint (A i) (B j))
    (hAS : ∀ i j, Disjoint (A i) (S j))
    (hBS : ∀ i j, Disjoint (B i) (S j)) :
    Pairwise (fun i j => Disjoint (A i ∪ B i ∪ S i) (A j ∪ B j ∪ S j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro e ((ha | hb) | hs) ((ha' | hb') | hs')
  all_goals first
    | exact Set.disjoint_left.mp (hA hij) ha ha'
    | exact Set.disjoint_left.mp (hB hij) hb hb'
    | exact Set.disjoint_left.mp (hS hij) hs hs'
    | exact Set.disjoint_left.mp (hAB i j) ha hb'
    | exact Set.disjoint_left.mp (hAS i j) ha hs'
    | exact Set.disjoint_left.mp (hBS i j) hb hs'
    | exact Set.disjoint_left.mp (hAB j i) ha' hb
    | exact Set.disjoint_left.mp (hAS j i) ha' hs
    | exact Set.disjoint_left.mp (hBS j i) hb' hs

theorem reservoir_cycle_family {V : Type cycleUniverse16} {I : Type cycleUniverse17} {G : SimpleGraph V}
    {x y a b : I → V} (Q : ∀ i, G.Walk (x i) (y i))
    (P : ∀ i, G.Walk (a i) (b i))
    (hx : ∀ i, G.Adj (x i) (a i)) (hy : ∀ i, G.Adj (y i) (b i))
    (hQ : ∀ i, (Q i).IsPath) (hQpos : ∀ i, 0 < (Q i).length)
    (hP : ∀ i, (P i).IsPath)
    (hsep : ∀ i, (Q i).support.Disjoint (P i).support)
    (hQQ : Pairwise fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet)
    (hPP : Pairwise fun i j => Disjoint (P i).edgeSet (P j).edgeSet)
    (hspoke : Function.Injective (fun z : I × Fin 2 =>
      if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)))
    (hQP : ∀ i j, Disjoint (Q i).edgeSet (P j).edgeSet)
    (hQS : ∀ i j, Disjoint (Q i).edgeSet {s(x j,a j),s(y j,b j)})
    (hPS : ∀ i j, Disjoint (P i).edgeSet {s(x j,a j),s(y j,b j)}) :
    let C := fun i => (Q i).append (reservoirReturn (P i) (hx i) (hy i))
    (∀ i, (C i).IsCycle) ∧
    Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
    (⋃ i, (C i).edgeSet) =
      (⋃ i, (Q i).edgeSet) ∪ (⋃ i, (P i).edgeSet) ∪
        (⋃ i, ({s(x i,a i),s(y i,b i)} : Set (Sym2 V))) := by
  dsimp only
  have hC := fun i => reservoir_path_closure (Q i) (P i) (hQ i) (hQpos i)
    (hP i) (hsep i) (hx i) (hy i)
  refine ⟨fun i => (hC i).1, ?_, ?_⟩
  · have hSS : Pairwise (fun i j => Disjoint
        ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)) {s(x j,a j),s(y j,b j)}) := by
      simpa using spoke_sets_pairwise _ hspoke
    simpa only [fun i => (hC i).2.1] using
      pairwise_union_three (fun i => (Q i).edgeSet) (fun i => (P i).edgeSet)
        (fun i => ({s(x i,a i),s(y i,b i)} : Set (Sym2 V)))
        hQQ hPP hSS hQP hQS hPS
  · simp only [fun i => (hC i).2.1, Set.iUnion_union_distrib]

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ReservoirRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37 cycleUniverse38 cycleUniverse39 cycleUniverse40 cycleUniverse41 cycleUniverse42 cycleUniverse43 cycleUniverse44 cycleUniverse45 cycleUniverse46 cycleUniverse47 cycleUniverse48 cycleUniverse49 cycleUniverse50 cycleUniverse51 cycleUniverse52 cycleUniverse53 cycleUniverse54 cycleUniverse55 cycleUniverse56

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walks_edges_disjoint_of_support {V : Type cycleUniverse1} {G H : SimpleGraph V}
    {x y a b : V} (p : G.Walk x y) (q : H.Walk a b)
    (h : p.support.Disjoint q.support) : Disjoint p.edgeSet q.edgeSet := by
  apply Set.disjoint_left.mpr
  intro e he he'
  induction e using Sym2.ind with
  | _ u v =>
    exact h (p.fst_mem_support_of_mem_edges he) (q.fst_mem_support_of_mem_edges he')

lemma walk_edges_disjoint_spokes_of_outside {V : Type cycleUniverse2} {I : Type cycleUniverse3} {G : SimpleGraph V}
    {u v : V} (Q : G.Walk u v) (W : Set V) (x y a b : I → V)
    (hQ : ∀ z ∈ Q.support, z ∉ W) (ha : ∀ i, a i ∈ W) (hb : ∀ i, b i ∈ W) :
    ∀ i, Disjoint Q.edgeSet ({s(x i,a i), s(y i,b i)} : Set (Sym2 V)) := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he he'
  rcases he' with rfl | he'
  · exact hQ _ (Q.snd_mem_support_of_mem_edges he) (ha i)
  · have heq : e = s(y i,b i) := he'
    subst e
    exact hQ _ (Q.snd_mem_support_of_mem_edges he) (hb i)

lemma walk_edges_disjoint_spokes_of_inside {V : Type cycleUniverse4} {I : Type cycleUniverse5} {G : SimpleGraph V}
    {u v : V} (Q : G.Walk u v) (W : Set V) (x y a b : I → V)
    (hQ : ∀ z ∈ Q.support, z ∈ W) (hx : ∀ i, x i ∉ W) (hy : ∀ i, y i ∉ W) :
    ∀ i, Disjoint Q.edgeSet ({s(x i,a i), s(y i,b i)} : Set (Sym2 V)) := by
  intro i
  apply Set.disjoint_left.mpr
  intro e he he'
  rcases he' with rfl | he'
  · exact hx i (hQ _ (Q.fst_mem_support_of_mem_edges he))
  · have heq : e = s(y i,b i) := he'
    subst e
    exact hy i (hQ _ (Q.fst_mem_support_of_mem_edges he))

theorem uniform_reservoir_completion (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G P : SimpleGraph V) [DecidableRel P.Adj], P ≤ G →
      ∀ W : Finset V, CutExpansionOn P W (D^(37/50:ℝ)) → 2 ≤ W.card →
      (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      ∀ (I : Type) [Fintype I] (x y : I → V) (Q : ∀ i, G.Walk (x i) (y i)),
      (∀ i, (Q i).IsPath) → (∀ i, 0 < (Q i).length) →
      (∀ i v, v ∈ (Q i).support → v ∉ W) →
      Pairwise (fun i j => Disjoint (Q i).edgeSet (Q j).edgeSet) →
      (∀ v, endpointLoad univ x y v ≤ 2) →
      ∀ r : V × Fin 2 → V,
      (∀ v, v ∉ W → ∀ t, r (v,t) ∈ W ∧ P.Adj v (r (v,t))) →
      (∀ v, v ∉ W → r (v,0) ≠ r (v,1)) →
      (∀ v, ((Wᶜ ×ˢ univ).filter (fun z => r z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      ∃ (a b : I → V) (q : ∀ i, G.Walk (a i) (b i))
        (C : ∀ i, G.Walk (x i) (x i)),
        (∀ i, (C i).IsCycle) ∧
        Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
        (∀ i, (C i).edgeSet = (Q i).edgeSet ∪ (q i).edgeSet ∪
          {s(x i,a i),s(y i,b i)}) ∧
        (∀ i, (q i).edgeSet ⊆ P.edgeSet ∧ ∀ v ∈ (q i).support, v ∈ W) ∧
        Function.Injective (fun z : I × Fin 2 =>
          if z.2 = 0 then s(x z.1,a z.1) else s(y z.1,b z.1)) ∧
        (∀ i, ∃ t, a i = r (x i,t)) ∧ (∀ i, ∃ t, b i = r (y i,t)) := by
  obtain ⟨D₀,hD₀,hrouting⟩ := uniform_assigned_reservoir_routing c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P _ hPG W hexp hW hr I _ x y Q hQ hpos hout hQQ hl r hrep hrepne hcap
  have hne : ∀ i, x i ≠ y i := by
    intro i hi
    have hz := ((hQ i).nil_iff_eq.mpr hi).length_eq_zero
    have := hpos i
    omega
  have hx : ∀ i, x i ∉ W := fun i => hout i _ (Q i).start_mem_support
  have hy : ∀ i, y i ∉ W := fun i => hout i _ (Q i).end_mem_support
  obtain ⟨a,b,q,hab,hsp,hq,hdd,ha',hb',hPedge⟩ :=
    hrouting D hD V G P hPG W hexp hW hr I x y hne hx hy hl r hrep hrepne hcap
  have ha : ∀ i, a i ∈ W := fun i => (hq i).2.2 _ (q i).start_mem_support
  have hb : ∀ i, b i ∈ W := fun i => (hq i).2.2 _ (q i).end_mem_support
  have hdisj : ∀ i j, (Q i).support.Disjoint (q j).support := by
    intro i j
    exact List.disjoint_left.mpr (fun v hv hv' => hout i v hv ((hq j).2.2 v hv'))
  let C := fun i => (Q i).append (reservoirReturn (q i) (hab i).1 (hab i).2)
  have hfamily := reservoir_cycle_family Q q (fun i => (hab i).1) (fun i => (hab i).2)
    hQ hpos (fun i => (hq i).1) (fun i => hdisj i i) hQQ hdd hsp
    (fun i j => walks_edges_disjoint_of_support _ _ (hdisj i j))
    (fun i => walk_edges_disjoint_spokes_of_outside (Q i) W x y a b (hout i) ha hb)
    (fun i => walk_edges_disjoint_spokes_of_inside (q i) W x y a b (hq i).2.2 hx hy)
  refine ⟨a,b,q,C,hfamily.1,hfamily.2.1,?_,?_,hsp,ha',hb'⟩
  · intro i
    exact (reservoir_path_closure (Q i) (q i) (hQ i) (hpos i) (hq i).1
      (hdisj i i) (hab i).1 (hab i).2).2.1
  · intro i
    exact ⟨hPedge i,(hq i).2.2⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph
attribute [local instance] Classical.propDecidable

lemma reservoirColor_avoids {V : Type cycleUniverse9} (W : Fin 3 → Set V)
    (hW : Pairwise fun i j => Disjoint (W i) (W j)) (e : Sym2 V) :
    ∀ v ∈ e, v ∉ W (reservoirColor W hW e) :=
  (exists_edge_reservoir_avoided W hW e).choose_spec

lemma complementaryReservoirGraph_edges {V : Type cycleUniverse11} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) :
    (complementaryReservoirGraph G W hW i).edgeSet =
      {e | e ∈ G.edgeSet ∧ reservoirColor W hW e = i} := by
  ext e
  induction e using Sym2.ind with
  | _ x y => rfl

theorem complementary_reservoir_graphs {V : Type cycleUniverse12} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j)) :
    (∀ i, complementaryReservoirGraph G W hW i ≤ G) ∧
    (∀ i x y, (complementaryReservoirGraph G W hW i).Adj x y →
      x ∉ W i ∧ y ∉ W i) ∧
    Pairwise (fun i j => Disjoint (complementaryReservoirGraph G W hW i).edgeSet
      (complementaryReservoirGraph G W hW j).edgeSet) ∧
    (⋃ i, (complementaryReservoirGraph G W hW i).edgeSet) = G.edgeSet := by
  refine ⟨fun _ _ _ h => h.1, ?_, ?_, ?_⟩
  · intro i x y h
    have hx := reservoirColor_avoids W hW s(x,y) x (Sym2.mem_mk_left x y)
    have hy := reservoirColor_avoids W hW s(x,y) y (Sym2.mem_mk_right x y)
    rw [h.2] at hx hy
    exact ⟨hx,hy⟩
  · intro i j hij
    rw [complementaryReservoirGraph_edges, complementaryReservoirGraph_edges]
    exact Set.disjoint_left.mpr fun _ he hj => hij (he.2.symm.trans hj.2)
  · ext e
    simp only [Set.mem_iUnion, complementaryReservoirGraph_edges, Set.mem_ofPred]
    constructor
    · rintro ⟨i,he,_⟩; exact he
    · intro he; exact ⟨reservoirColor W hW e, he, rfl⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma mem_reservoirSpokes {V : Type cycleUniverse15} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) (e : Sym2 V) :
    e ∈ reservoirSpokes W r ↔ ∃ v ∉ W, ∃ t : Fin 2, e = s(v,r (v,t)) := by
  simp only [reservoirSpokes, Finset.mem_image, Finset.mem_product,
    Finset.mem_compl, Finset.mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨v,t,hv,he⟩
    exact ⟨v,hv,t,he.symm⟩
  · rintro ⟨v,hv,t,he⟩
    exact ⟨v,t,hv,he.symm⟩

lemma reservoirSpokes_card_le {V : Type cycleUniverse16} [Fintype V] [DecidableEq V]
    (W : Finset V) (r : V × Fin 2 → V) :
    (reservoirSpokes W r).card ≤ 2 * Fintype.card V := by
  apply (Finset.card_image_le).trans
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  have := Finset.card_le_univ Wᶜ
  omega

lemma reservoirSpokes_subset {V : Type cycleUniverse17} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (W : Finset V) (r : V × Fin 2 → V)
    (hr : ∀ v, v ∉ W → ∀ t, P.Adj v (r (v,t))) :
    (reservoirSpokes W r : Set (Sym2 V)) ⊆ P.edgeSet := by
  intro e he
  obtain ⟨v,hv,t,rfl⟩ := (mem_reservoirSpokes W r e).mp he
  exact hr v hv t

lemma reservoirInternal_spokes_disjoint {V : Type cycleUniverse18} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (W : Finset V) (r : V × Fin 2 → V) :
    Disjoint (reservoirInternal P W) (reservoirSpokes W r : Set (Sym2 V)) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨v,hv,t,rfl⟩ := (mem_reservoirSpokes W r e).mp he'
  exact hv (he.2 _ (Sym2.mem_mk_left _ _))

theorem reservoir_reservations {V : Type cycleUniverse19} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : Fin 3 → SimpleGraph V) (W : Fin 3 → Finset V)
    (r : Fin 3 → V × Fin 2 → V)
    (hPG : ∀ i, P i ≤ G)
    (hPP : Pairwise fun i j => Disjoint (P i).edgeSet (P j).edgeSet)
    (hr : ∀ i v, v ∉ W i → ∀ t, (P i).Adj v (r i (v,t))) :
    let R := fun i => reservoirInternal (P i) (W i)
    let O := fun i => (reservoirSpokes (W i) (r i) : Set (Sym2 V))
    (∀ i, R i ⊆ G.edgeSet ∧ O i ⊆ G.edgeSet) ∧
    Pairwise (fun i j => Disjoint (R i ∪ O i) (R j ∪ O j)) ∧
    (∀ i, Disjoint (R i) (O i)) ∧
    Disjoint (⋃ i, R i) (⋃ i, O i) ∧
    (∑ i, (reservoirSpokes (W i) (r i)).card) ≤ 6 * Fintype.card V := by
  dsimp only
  have hR : ∀ i, reservoirInternal (P i) (W i) ⊆ (P i).edgeSet := fun _ _ he => he.1
  have hO := fun i => reservoirSpokes_subset (P i) (W i) (r i) (hr i)
  have hU : ∀ i, reservoirInternal (P i) (W i) ∪
      (reservoirSpokes (W i) (r i) : Set (Sym2 V)) ⊆ (P i).edgeSet :=
    fun i => Set.union_subset (hR i) (hO i)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    exact ⟨(hR i).trans (SimpleGraph.edgeSet_mono (hPG i)),
      (hO i).trans (SimpleGraph.edgeSet_mono (hPG i))⟩
  · intro i j hij
    exact (hPP hij).mono (hU i) (hU j)
  · exact fun i => reservoirInternal_spokes_disjoint (P i) (W i) (r i)
  · rw [Set.disjoint_iUnion_left]
    intro i
    rw [Set.disjoint_iUnion_right]
    intro j
    by_cases hij : i = j
    · subst j
      exact reservoirInternal_spokes_disjoint (P i) (W i) (r i)
    · exact (hPP hij).mono (hR i) (hO j)
  · calc
      _ ≤ ∑ _i : Fin 3, 2 * Fintype.card V :=
        Finset.sum_le_sum (fun i _ => reservoirSpokes_card_le (W i) (r i))
      _ = _ := by simp; omega

lemma complementary_walk_outside {V : Type cycleUniverse20} {G : SimpleGraph V}
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i : Fin 3) {x y : V} (q : (complementaryReservoirGraph G W hW i).Walk x y)
    (hq : 0 < q.length) : ∀ v ∈ q.support, v ∉ W i := by
  have hn : ¬ q.Nil := by
    intro h
    have hz := h.length_eq_zero
    omega
  intro v hv
  obtain ⟨e,he,hve⟩ := SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hn |>.mp hv
  have heG := q.edges_subset_edgeSet he
  have hecol : reservoirColor W hW e = i := by
    rw [complementaryReservoirGraph_edges] at heG
    exact heG.2
  exact hecol ▸ reservoirColor_avoids W hW e v hve

theorem complementary_reservation_ledger {V : Type cycleUniverse21} (G : SimpleGraph V)
    (W : Fin 3 → Set V) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (E : Set (Sym2 V)) (hE : E ⊆ G.edgeSet) :
    let H := G.deleteEdges E
    let K := fun i => complementaryReservoirGraph H W hW i
    Pairwise (fun i j => Disjoint (K i).edgeSet (K j).edgeSet) ∧
    (∀ i, Disjoint (K i).edgeSet E) ∧
    ((⋃ i, (K i).edgeSet) ∪ E = G.edgeSet) := by
  dsimp only
  have hh := complementary_reservoir_graphs (G.deleteEdges E) W hW
  refine ⟨hh.2.2.1,?_,?_⟩
  · intro i
    apply Set.disjoint_left.mpr
    intro e he he'
    have h := SimpleGraph.edgeSet_mono (hh.1 i) he
    rw [SimpleGraph.edgeSet_deleteEdges] at h
    exact h.2 he'
  · rw [hh.2.2.2, SimpleGraph.edgeSet_deleteEdges]
    exact Set.sdiff_union_of_subset hE

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma edgeRestriction_le {V : Type cycleUniverse23} (G : SimpleGraph V) (E : Set (Sym2 V)) :
    edgeRestriction G E ≤ G := fun _ _ h => h.1

lemma edgeRestriction_edges {V : Type cycleUniverse24} (G : SimpleGraph V) (E : Set (Sym2 V)) :
    (edgeRestriction G E).edgeSet = G.edgeSet ∩ E := by
  ext e
  induction e using Sym2.ind with | _ x y => rfl

lemma edgeRestriction_edges_of_subset {V : Type cycleUniverse25} (G : SimpleGraph V) (E : Set (Sym2 V))
    (hE : E ⊆ G.edgeSet) : (edgeRestriction G E).edgeSet = E := by
  rw [edgeRestriction_edges, Set.inter_eq_right.mpr hE]

lemma unusedSpokes_card_le {V : Type cycleUniverse33} {I : Type cycleUniverse34} [Fintype V] (S : Finset (Sym2 V))
    (C : I → Set (Sym2 V)) : (unusedSpokes (↑S) C).card ≤ S.card := by
  apply Finset.card_le_card
  intro e he
  simp only [unusedSpokes, Set.mem_toFinset, Finset.mem_coe, Set.mem_sdiff] at he
  exact he.1

theorem residue_edge_ledger {V : Type cycleUniverse35} {B : Type cycleUniverse36} {I : Type cycleUniverse37} [Fintype V]
    (G : SimpleGraph V) (R : B → Set (Sym2 V)) (S : Set (Sym2 V))
    (C : I → Set (Sym2 V))
    (hR : ∀ b, R b ⊆ G.edgeSet) (hS : S ⊆ G.edgeSet)
    (hRR : Pairwise fun b c => Disjoint (R b) (R c))
    (hRS : ∀ b, Disjoint (R b) S)
    (hC : ∀ i, C i ⊆ G.edgeSet)
    (_hCC : Pairwise fun i j => Disjoint (C i) (C j))
    (hcover : G.edgeSet \ ((⋃ b, R b) ∪ S) ⊆ completedEdges C) :
    (∀ b, (residualInternalGraph G R C b).edgeSet = R b \ completedEdges C) ∧
    Pairwise (fun b c => Disjoint (residualInternalGraph G R C b).edgeSet
      (residualInternalGraph G R C c).edgeSet) ∧
    (∀ b i, Disjoint (residualInternalGraph G R C b).edgeSet (C i)) ∧
    (∀ b, Disjoint (residualInternalGraph G R C b).edgeSet (↑(unusedSpokes S C) : Set _)) ∧
    (∀ i, Disjoint (C i) (↑(unusedSpokes S C) : Set _)) ∧
    (completedEdges C ∪ (↑(unusedSpokes S C) : Set _) ∪
      (⋃ b, (residualInternalGraph G R C b).edgeSet)) = G.edgeSet := by
  classical
  have hrem (b : B) : (residualInternalGraph G R C b).edgeSet = R b \ completedEdges C := by
    apply edgeRestriction_edges_of_subset
    exact fun e he => hR b he.1
  have hsingle : (↑(unusedSpokes S C) : Set _) = S \ completedEdges C := by
    simp only [unusedSpokes, Set.coe_toFinset]
  have hsub : completedEdges C ⊆ G.edgeSet := by
    rintro e he
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp he
    exact hC i hi
  refine ⟨hrem,?_,?_,?_,?_,?_⟩
  · intro b c hbc
    rw [hrem b,hrem c]
    exact (hRR hbc).mono Set.sdiff_subset Set.sdiff_subset
  · intro b i
    rw [hrem b]
    apply Set.disjoint_left.mpr
    intro e he hi
    exact he.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  · intro b
    rw [hrem b,hsingle]
    exact (hRS b).mono Set.sdiff_subset Set.sdiff_subset
  · intro i
    rw [hsingle]
    apply Set.disjoint_left.mpr
    intro e hi he
    exact he.2 (Set.mem_iUnion.mpr ⟨i,hi⟩)
  · rw [hsingle]
    ext e
    constructor
    · rintro ((he | he) | he)
      · exact hsub he
      · exact hS he.1
      · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
        rw [hrem b] at hb
        exact hR b hb.1
    · intro he
      by_cases hc : e ∈ completedEdges C
      · exact Or.inl (Or.inl hc)
      by_cases hs : e ∈ S
      · exact Or.inl (Or.inr ⟨hs,hc⟩)
      have hr : e ∈ ⋃ b, R b := by
        by_contra hr
        exact hc (hcover ⟨he,by intro hu; exact hu.elim hr hs⟩)
      obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hr
      exact Or.inr (Set.mem_iUnion.mpr ⟨b,by rw [hrem b]; exact ⟨hb,hc⟩⟩)

theorem residue_part_count {V : Type cycleUniverse38} {I : Type cycleUniverse39} [Fintype V] [Fintype I]
    (S : Finset (Sym2 V)) (C : I → Set (Sym2 V))
    (hI : Fintype.card I ≤ 3 * Fintype.card V)
    (hS : S.card ≤ 6 * Fintype.card V) :
    Fintype.card I + (unusedSpokes (↑S) C).card ≤ 9 * Fintype.card V := by
  have := unusedSpokes_card_le S C
  omega

lemma induce_edge_image_of_support_subset {V : Type cycleUniverse40} (H : SimpleGraph V)
    (W : Set V) (hW : H.support ⊆ W) :
    Sym2.map Subtype.val '' (H.induce W).edgeSet = H.edgeSet := by
  ext e
  constructor
  · rintro ⟨d,hd,rfl⟩
    induction d using Sym2.ind with
    | _ x y => exact hd
  · intro he
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ W := hW ⟨y,he⟩
      have hy : y ∈ W := hW ⟨x,he.symm⟩
      exact ⟨s(⟨x,hx⟩,⟨y,hy⟩),he,rfl⟩

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walk_edges_internal {V : Type cycleUniverse44} {G P : SimpleGraph V} {a b : V}
    (W : Set V) (q : G.Walk a b) (he : q.edgeSet ⊆ P.edgeSet)
    (hv : ∀ v ∈ q.support, v ∈ W) :
    q.edgeSet ⊆ reservoirInternal P W := by
  intro e h
  refine ⟨he h,?_⟩
  induction e using Sym2.ind with
  | _ x y =>
    intro v hmem
    rcases (Sym2.mem_iff.mp hmem) with rfl | rfl
    · exact hv _ (q.fst_mem_support_of_mem_edges h)
    · exact hv _ (q.snd_mem_support_of_mem_edges h)

lemma completion_edges_subset {V : Type cycleUniverse45} [Fintype V] [DecidableEq V]
    {G P : SimpleGraph V} (W : Finset V) (r : V × Fin 2 → V)
    {x y a b : V} (Q : G.Walk x y) (q : G.Walk a b) (C : G.Walk x x)
    (K : Set (Sym2 V)) (hQ : Q.edgeSet ⊆ K)
    (hC : C.edgeSet = Q.edgeSet ∪ q.edgeSet ∪ {s(x,a),s(y,b)})
    (hq : q.edgeSet ⊆ P.edgeSet ∧ ∀ v ∈ q.support, v ∈ W)
    (hx : x ∉ W) (hy : y ∉ W)
    (ha : ∃ t, a = r (x,t)) (hb : ∃ t, b = r (y,t)) :
    C.edgeSet ⊆ K ∪ (reservoirInternal P W ∪ (reservoirSpokes W r : Set _)) := by
  rw [hC]
  have hqi := walk_edges_internal (W : Set V) q hq.1 hq.2
  intro e he
  rcases he with (he | he) | he
  · exact Or.inl (hQ he)
  · exact Or.inr (Or.inl (hqi he))
  · apply Or.inr ∘ Or.inr
    rcases (show e = s(x,a) ∨ e = s(y,b) by simpa using he) with rfl | rfl
    · obtain ⟨t,rfl⟩ := ha
      exact (mem_reservoirSpokes W r _).mpr ⟨x,hx,t,rfl⟩
    · obtain ⟨t,rfl⟩ := hb
      exact (mem_reservoirSpokes W r _).mpr ⟨y,hy,t,rfl⟩

lemma completed_subfamilies_disjoint {E : Type cycleUniverse46} {B : Type cycleUniverse47} {I : B → Type cycleUniverse55}
    (K R : B → Set E) (C : ∀ b, I b → Set E)
    (hKK : Pairwise fun b c => Disjoint (K b) (K c))
    (hRR : Pairwise fun b c => Disjoint (R b) (R c))
    (hKR : ∀ b c, Disjoint (K b) (R c))
    (hC : ∀ b i, C b i ⊆ K b ∪ R b)
    (hCC : ∀ b, Pairwise fun i j => Disjoint (C b i) (C b j)) :
    Pairwise (fun s t : Sigma I => Disjoint (C s.1 s.2) (C t.1 t.2)) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ hne
  by_cases hbc : b = c
  · subst c
    apply hCC b
    intro hij
    exact hne (by cases hij; rfl)
  · apply Disjoint.mono (hC b i) (hC c j)
    rw [Set.disjoint_union_left,Set.disjoint_union_right,Set.disjoint_union_right]
    exact ⟨⟨hKK hbc,hKR b c⟩,⟨(hKR c b).symm,hRR hbc⟩⟩

lemma completed_subfamilies_cover {E : Type cycleUniverse48} {B : Type cycleUniverse49} {I : B → Type cycleUniverse56}
    (K : B → Set E) (Q C : ∀ b, I b → Set E)
    (hQ : ∀ b, (⋃ i, Q b i) = K b)
    (hQC : ∀ b i, Q b i ⊆ C b i) :
    (⋃ b, K b) ⊆ ⋃ s : Sigma I, C s.1 s.2 := by
  intro e he
  obtain ⟨b,hb⟩ := Set.mem_iUnion.mp he
  rw [← hQ b] at hb
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hb
  exact Set.mem_iUnion.mpr ⟨⟨b,i⟩,hQC b i hi⟩

lemma endpointLoad_family_card {V I : Type} [Fintype V] [DecidableEq V] [Fintype I]
    (x y : I → V) (hne : ∀ i, x i ≠ y i)
    (hload : ∀ v, endpointLoad univ x y v ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hs := endpointLoad_sum (univ : Finset I) x y (fun i _ => hne i)
  have hb := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset V)) => hload v)
  simp only [Finset.card_univ] at hs
  rw [hs] at hb
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hb
  omega

lemma sigma_three_card_le {V : Type} [Fintype V]
    (I : Fin 3 → Type) [∀ b, Fintype (I b)]
    (hI : ∀ b, Fintype.card (I b) ≤ Fintype.card V) :
    Fintype.card (Sigma I) ≤ 3 * Fintype.card V := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _b : Fin 3, Fintype.card V := Finset.sum_le_sum (fun b _ => hI b)
    _ = _ := by simp [mul_comm]

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem uniform_three_reservoir_completion (c p : ℝ) (hc : 0 < c) (hp : 0 < p) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (G : SimpleGraph V) (P K : Fin 3 → SimpleGraph V)
        [∀ b, DecidableRel (P b).Adj],
      (∀ b, P b ≤ G) →
      Pairwise (fun b d => Disjoint (P b).edgeSet (P d).edgeSet) →
      ∀ (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V),
      (∀ b, CutExpansionOn (P b) (W b) (D^(37/50:ℝ))) →
      (∀ b, 2 ≤ (W b).card) → (Fintype.card V : ℝ) ≤ D^(51/50:ℝ) →
      (∀ b v, v ∉ W b → ∀ t, r b (v,t) ∈ W b ∧ (P b).Adj v (r b (v,t))) →
      (∀ b v, v ∉ W b → r b (v,0) ≠ r b (v,1)) →
      (∀ b v, (((W b)ᶜ ×ˢ univ).filter (fun z => r b z = v)).card ≤
        ⌈8*(Fintype.card V:ℝ)/(p*(c*D^(9/10:ℝ)))⌉₊) →
      let T := fun b => reservoirInternal (P b) (W b) ∪
        (reservoirSpokes (W b) (r b) : Set (Sym2 V))
      Pairwise (fun b d => Disjoint (K b).edgeSet (K d).edgeSet) →
      (∀ b d, Disjoint (K b).edgeSet (T d)) →
      ∀ (I : Fin 3 → Type) [∀ b, Fintype (I b)]
        (x y : ∀ b, I b → V) (Q : ∀ b i, G.Walk (x b i) (y b i)),
      (∀ b i, (Q b i).IsPath) → (∀ b i, 0 < (Q b i).length) →
      (∀ b i v, v ∈ (Q b i).support → v ∉ W b) →
      (∀ b, Pairwise fun i j => Disjoint (Q b i).edgeSet (Q b j).edgeSet) →
      (∀ b, (⋃ i, (Q b i).edgeSet) = (K b).edgeSet) →
      (∀ b v, endpointLoad univ (x b) (y b) v ≤ 2) →
      ∃ C : ∀ b i, G.Walk (x b i) (x b i),
        (∀ b i, (C b i).IsCycle) ∧
        Pairwise (fun s t : Sigma I =>
          Disjoint (C s.1 s.2).edgeSet (C t.1 t.2).edgeSet) ∧
        (∀ b i, (C b i).edgeSet ⊆ (K b).edgeSet ∪ T b) ∧
        (⋃ b, (K b).edgeSet) ⊆ (⋃ s : Sigma I, (C s.1 s.2).edgeSet) ∧
        Fintype.card (Sigma I) ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨D₀,hD₀,hclose⟩ := uniform_reservoir_completion c p hc hp
  refine ⟨D₀,hD₀,?_⟩
  intro D hD V _ _ G P K _ hPG hPP W r hexp hW hn hr hrne hcap
  dsimp only
  intro hKK hKT I _ x y Q hQ hpos hout hQQ hcover hl
  have hex : ∀ b : Fin 3,
      ∃ (a z : I b → V) (q : ∀ i, G.Walk (a i) (z i))
        (C : ∀ i, G.Walk (x b i) (x b i)),
        (∀ i, (C i).IsCycle) ∧
        Pairwise (fun i j => Disjoint (C i).edgeSet (C j).edgeSet) ∧
        (∀ i, (C i).edgeSet = (Q b i).edgeSet ∪ (q i).edgeSet ∪
          {s(x b i,a i),s(y b i,z i)}) ∧
        (∀ i, (q i).edgeSet ⊆ (P b).edgeSet ∧ ∀ v ∈ (q i).support, v ∈ W b) ∧
        Function.Injective (fun z' : I b × Fin 2 =>
          if z'.2 = 0 then s(x b z'.1,a z'.1) else s(y b z'.1,z z'.1)) ∧
        (∀ i, ∃ t, a i = r b (x b i,t)) ∧
        (∀ i, ∃ t, z i = r b (y b i,t)) := by
    intro b
    exact hclose D hD V G (P b) (hPG b) (W b) (hexp b) (hW b) hn
      (I b) (x b) (y b) (Q b) (hQ b) (hpos b) (hout b) (hQQ b) (hl b)
      (r b) (hr b) (hrne b) (hcap b)
  choose a z q C hCy hCC hCe hqe _hsp ha hz using hex
  have hsub : ∀ b i, (C b i).edgeSet ⊆ (K b).edgeSet ∪
      (reservoirInternal (P b) (W b) ∪ (reservoirSpokes (W b) (r b) : Set _)) := by
    intro b i
    apply completion_edges_subset (W b) (r b) (Q b i) (q b i) (C b i)
      (K b).edgeSet _ (hCe b i) (hqe b i)
      (hout b i _ (Q b i).start_mem_support)
      (hout b i _ (Q b i).end_mem_support) (ha b i) (hz b i)
    intro e he
    rw [← hcover b]
    exact Set.mem_iUnion.mpr ⟨i,he⟩
  have hreserv := reservoir_reservations G P W r hPG hPP
    (fun b v hv t => (hr b v hv t).2)
  refine ⟨C,hCy,?_,hsub,?_,?_⟩
  · exact completed_subfamilies_disjoint (fun b => (K b).edgeSet)
      (fun b => reservoirInternal (P b) (W b) ∪
        (reservoirSpokes (W b) (r b) : Set _))
      (fun b i => (C b i).edgeSet) hKK hreserv.2.1 hKT hsub hCC
  · apply completed_subfamilies_cover (fun b => (K b).edgeSet)
      (fun b i => (Q b i).edgeSet) (fun b i => (C b i).edgeSet) hcover
    intro b i e he
    rw [hCe b i]
    exact Or.inl (Or.inl he)
  · apply sigma_three_card_le I
    intro b
    apply endpointLoad_family_card (x b) (y b) _ (hl b)
    intro i hi
    have hz := ((hQ b i).nil_iff_eq.mpr hi).length_eq_zero
    have hp := hpos b i
    omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

lemma coe_allReservoirSpokes {V : Type cycleUniverse51} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) :
    (allReservoirSpokes W r : Set (Sym2 V)) =
      ⋃ b, (reservoirSpokes (W b) (r b) : Set (Sym2 V)) := by
  ext e
  simp [allReservoirSpokes]

lemma allReservoirSpokes_card_le {V : Type cycleUniverse52} [Fintype V] [DecidableEq V]
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V) :
    (allReservoirSpokes W r).card ≤ 6 * Fintype.card V := by
  apply (Finset.card_biUnion_le).trans
  calc
    (∑ b : Fin 3, (reservoirSpokes (W b) (r b)).card) ≤
      ∑ _b : Fin 3, 2 * Fintype.card V :=
        Finset.sum_le_sum (fun b _ => reservoirSpokes_card_le (W b) (r b))
    _ = _ := by simp; omega

theorem three_reservoir_remainder {V : Type cycleUniverse53} {I : Type cycleUniverse54} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) (P : Fin 3 → SimpleGraph V)
    (W : Fin 3 → Finset V) (r : Fin 3 → V × Fin 2 → V)
    (hPG : ∀ b, P b ≤ G)
    (hPP : Pairwise fun b d => Disjoint (P b).edgeSet (P d).edgeSet)
    (hr : ∀ b v, v ∉ W b → ∀ t, (P b).Adj v (r b (v,t)))
    (C : I → Set (Sym2 V)) (hC : ∀ i, C i ⊆ G.edgeSet)
    (hCC : Pairwise fun i j => Disjoint (C i) (C j))
    (hI : Fintype.card I ≤ 3 * Fintype.card V)
    (hcover : G.edgeSet \ ((⋃ b, reservoirInternal (P b) (W b)) ∪
      (allReservoirSpokes W r : Set _)) ⊆ completedEdges C) :
    let R := fun b => reservoirInternal (P b) (W b)
    let H := residualInternalGraph G R C
    let S := unusedSpokes (↑(allReservoirSpokes W r)) C
    (∀ b, (H b).support ⊆ (W b : Set V)) ∧
    (∀ b, Sym2.map Subtype.val '' ((H b).induce (W b : Set V)).edgeSet = (H b).edgeSet) ∧
    (∀ b, (H b).edgeSet = R b \ completedEdges C) ∧
    Pairwise (fun b d => Disjoint (H b).edgeSet (H d).edgeSet) ∧
    (∀ b i, Disjoint (H b).edgeSet (C i)) ∧
    (∀ b, Disjoint (H b).edgeSet (S : Set _)) ∧
    (∀ i, Disjoint (C i) (S : Set _)) ∧
    (completedEdges C ∪ (S : Set _) ∪ (⋃ b, (H b).edgeSet)) = G.edgeSet ∧
    Fintype.card I + S.card ≤ 9 * Fintype.card V := by
  classical
  dsimp only
  obtain ⟨hsub,hTT,_hown,hRS,_hcount⟩ := reservoir_reservations G P W r hPG hPP hr
  have hS : (allReservoirSpokes W r : Set (Sym2 V)) ⊆ G.edgeSet := by
    rw [coe_allReservoirSpokes]
    exact Set.iUnion_subset (fun b => (hsub b).2)
  have hRR : Pairwise fun b d =>
      Disjoint (reservoirInternal (P b) (W b)) (reservoirInternal (P d) (W d)) := by
    intro b d hbd
    exact (hTT hbd).mono Set.subset_union_left Set.subset_union_left
  have hRO : ∀ b, Disjoint (reservoirInternal (P b) (W b))
      (allReservoirSpokes W r : Set (Sym2 V)) := by
    intro b
    rw [coe_allReservoirSpokes]
    exact hRS.mono_left (Set.subset_iUnion (fun d => reservoirInternal (P d) (W d)) b)
  let R := fun b => reservoirInternal (P b) (W b)
  let H := residualInternalGraph G R C
  have hledger := residue_edge_ledger G R (↑(allReservoirSpokes W r)) C
    (fun b => (hsub b).1) hS hRR hRO hC hCC hcover
  have hsupp : ∀ b, (H b).support ⊆ (W b : Set V) := by
    intro b v hv
    obtain ⟨w,hw⟩ := (H b).mem_support.mp hv
    have he : s(v,w) ∈ (H b).edgeSet := hw
    rw [hledger.1 b] at he
    exact he.1.2 _ (Sym2.mem_mk_left _ _)
  refine ⟨hsupp,?_,hledger.1,hledger.2.1,hledger.2.2.1,
    hledger.2.2.2.1,hledger.2.2.2.2.1,hledger.2.2.2.2.2,?_⟩
  · intro b
    exact induce_edge_image_of_support_subset (H b) (W b) (hsupp b)
  · exact residue_part_count (allReservoirSpokes W r) C hI (allReservoirSpokes_card_le W r)

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.PathDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14 cycleUniverse15 cycleUniverse16 cycleUniverse17 cycleUniverse18 cycleUniverse19 cycleUniverse20 cycleUniverse21 cycleUniverse22 cycleUniverse23 cycleUniverse24 cycleUniverse25 cycleUniverse26 cycleUniverse27 cycleUniverse28 cycleUniverse29 cycleUniverse30 cycleUniverse31 cycleUniverse32 cycleUniverse33 cycleUniverse34 cycleUniverse35 cycleUniverse36 cycleUniverse37

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable

lemma PositiveSimplePath.endpoints_ne {V : Type cycleUniverse2} {G : SimpleGraph V}
    (P : PositiveSimplePath G) : P.start ≠ P.finish := by
  intro he
  have hz := P.isPath.nil_iff_eq.mpr he
  have := hz.length_eq_zero
  have := P.positive
  omega

theorem endpoint_path_count {V : Type cycleUniverse3} {I : Type cycleUniverse4} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hload : ∀ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card ≤ 2) :
    Fintype.card I ≤ Fintype.card V := by
  classical
  have hsum : (∑ v : V, (Finset.univ.filter
      (fun i => (P i).start = v ∨ (P i).finish = v)).card) =
      2 * Fintype.card I := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have heq : ∀ i : I,
        (∑ v : V, if (P i).start = v ∨ (P i).finish = v then 1 else 0) = 2 := by
      intro i
      have hf : (Finset.univ.filter fun v =>
          (P i).start = v ∨ (P i).finish = v) = {(P i).start, (P i).finish} := by
        ext v; simp [eq_comm]
      have hc : ({(P i).start, (P i).finish} : Finset V).card = 2 := by
        simp [(P i).endpoints_ne]
      rw [← hc, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    omega
  have hbound := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) => hload v)
  rw [hsum] at hbound
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hbound
  omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem evenAugmentation_degree {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (v : V) :
    (evenAugmentation G).degree (some v) =
      G.degree v + if Even (G.degree v) then 1 else 0 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  simp only [evenAugmentation_some_adj, evenAugmentation_some_none]
  have he : (∑ u : V, if G.Adj v u then 1 else 0) = G.degree v := by
    rw [← G.card_neighborFinset_eq_degree v, G.neighborFinset_eq_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  omega

theorem evenAugmentation_old_odd {V : Type cycleUniverse13} [Fintype V]
    (G : SimpleGraph V) (v : V) : Odd ((evenAugmentation G).degree (some v)) := by
  rw [evenAugmentation_degree]
  by_cases h : Even (G.degree v)
  · simp only [h, ↓reduceIte]
    rcases h with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  · simpa [h] using Nat.not_even_iff_odd.mp h

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem trail_partition_degree_sum {V : Type cycleUniverse14} {I : Type cycleUniverse15} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    G.degree v = ∑ i, (p i).edges.countP (fun e => decide (v ∈ e)) := by
  classical
  have he : G.edgeFinset = Finset.univ.biUnion (fun i => (p i).edges.toFinset) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, ← hc, Set.mem_iUnion,
      Finset.mem_biUnion, Finset.mem_univ, List.mem_toFinset, true_and,
      SimpleGraph.Walk.mem_edgeSet]
  rw [← G.card_incidenceFinset_eq_degree v, G.incidenceFinset_eq_filter, he,
    Finset.filter_biUnion]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    have hfilter : ((p i).edges.filter (fun e => decide (v ∈ e))).toFinset =
        ((p i).edges.toFinset.filter (fun e => v ∈ e)) := by
      simp [List.toFinset_filter]
    rw [← hfilter, List.toFinset_card_of_nodup ((ht i).edges_nodup.filter _),
      List.countP_eq_length_filter]
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    exact Set.disjoint_left.mp (hd hij)
      (by simpa using (Finset.mem_filter.mp hei).1)
      (by simpa using (Finset.mem_filter.mp hej).1)

theorem trail_partition_even_degree_iff {V : Type cycleUniverse16} {I : Type cycleUniverse17} [Fintype V] [Fintype I]
    (G : SimpleGraph V) {a b : I → V} (p : ∀ i, G.Walk (a i) (b i))
    (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet) (v : V) :
    Even (G.degree v) ↔ Even (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card := by
  classical
  rw [trail_partition_degree_sum G p ht hd hc v, Finset.even_sum_iff_even_card_odd]
  have he : (Finset.univ.filter (fun i => Odd ((p i).edges.countP
      (fun e => decide (v ∈ e))))) = (Finset.univ.filter
      (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      ← Nat.not_even_iff_odd, (ht i).even_countP_edges_iff]
    tauto
  rw [he]

private theorem odd_load_one {V : Type cycleUniverse18} [DecidableEq V]
    (S : Finset V) (f : V → ℕ) (ho : ∀ v ∈ S, Odd (f v))
    (hs : ∑ v ∈ S, f v ≤ S.card + 1) : ∀ v ∈ S, f v = 1 := by
  intro v hv
  by_contra hn
  have hv3 : 3 ≤ f v := by rcases ho v hv with ⟨k, hk⟩; omega
  have hlow : ∑ x ∈ S, (1 + if x = v then 2 else 0) ≤ ∑ x ∈ S, f x := by
    apply Finset.sum_le_sum
    intro x hx
    by_cases he : x = v
    · subst x; simpa using hv3
    · simp only [he, ↓reduceIte, add_zero]
      rcases ho x hx with ⟨k, hk⟩
      omega
  have heq : (∑ x ∈ S, (1 + if x = v then 2 else 0)) = S.card + 2 := by
    simp [Finset.sum_add_distrib, hv]
  omega

theorem tight_odd_trail_partition {V : Type cycleUniverse19} {I : Type cycleUniverse20} [Fintype V] [Fintype I]
    (G : SimpleGraph V) (S : Finset V) {a b : I → V}
    (p : ∀ i, G.Walk (a i) (b i)) (ht : ∀ i, (p i).IsTrail)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet)
    (hc : (⋃ i, (p i).edgeSet) = G.edgeSet)
    (ho : ∀ v ∈ S, Odd (G.degree v))
    (hsize : 2 * Fintype.card I ≤ S.card + 1) :
    (∀ i, a i ≠ b i) ∧ (∀ v ∈ S,
      (Finset.univ.filter (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card = 1) := by
  classical
  let load := fun v : V => (Finset.univ.filter
    (fun i => a i ≠ b i ∧ (v = a i ∨ v = b i))).card
  let openParts := Finset.univ.filter (fun i => a i ≠ b i)
  have hlodd : ∀ v ∈ S, Odd (load v) := by
    intro v hv
    rw [← Nat.not_even_iff_odd, ← trail_partition_even_degree_iff G p ht hd hc v]
    exact (Nat.not_even_iff_odd.mpr (ho v hv))
  have htotal : (∑ v : V, load v) = 2 * openParts.card := by
    dsimp [load]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    have he : ∀ i : I, (∑ v : V, if a i ≠ b i ∧ (v = a i ∨ v = b i) then 1 else 0) =
        if a i ≠ b i then 2 else 0 := by
      intro i
      by_cases h : a i = b i
      · simp [h]
      · have hf : (Finset.univ.filter (fun v => a i ≠ b i ∧ (v = a i ∨ v = b i))) =
            {a i, b i} := by ext v; simp [h]
        have hcard : ({a i, b i} : Finset V).card = 2 := by simp [h]
        rw [ite_eq_left h, ← hcard, ← hf, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [he]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    change openParts.card * 2 = 2 * openParts.card
    omega
  have hsub : (∑ v ∈ S, load v) ≤ ∑ v : V, load v :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ S)
  have hlow : S.card ≤ ∑ v ∈ S, load v := by
    simpa using Finset.sum_le_sum (s := S) (f := fun _ => 1) (g := load)
      (fun v hv => by rcases hlodd v hv with ⟨k, hk⟩; omega)
  have hcount : openParts.card ≤ Fintype.card I := Finset.card_le_univ _
  have hpoint := odd_load_one S load hlodd (by omega)
  refine ⟨?_, hpoint⟩
  intro i hi
  have hproper : openParts ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hh : i ∈ openParts := heq.symm ▸ Finset.mem_univ i
    simp [openParts, hi] at hh
  have hlt := Finset.card_lt_card hproper
  simp only [Finset.card_univ] at hlt
  omega

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

theorem delete_vertex_boundary_edges {V : Type cycleUniverse25} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hv : v ∈ p.support) :
    (0 < (p.takeUntil v hv).dropLast.length →
      s((p.takeUntil v hv).penultimate, v) ∈ p.edgeSet) ∧
    (0 < (p.dropUntil v hv).tail.length →
      s(v, (p.dropUntil v hv).snd) ∈ p.edgeSet) := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  constructor
  · intro hpos
    have hn : ¬ t.Nil := by
      intro hz
      change 0 < t.dropLast.length at hpos
      rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hpos
      omega
    have hm := t.mk_penultimate_end_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inl hm
  · intro hpos
    have hn : ¬ d.Nil := by
      intro hz
      change 0 < d.tail.length at hpos
      rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hpos
      omega
    have hm := d.mk_start_snd_mem_edges hn
    have hed : t.edgeSet ∪ d.edgeSet = p.edgeSet := by
      rw [← SimpleGraph.Walk.edgeSet_append, heq]
    exact hed ▸ Or.inr hm

theorem delete_vertex_new_ends_ne {V : Type cycleUniverse26} [DecidableEq V]
    {G : SimpleGraph V} {a b v : V} (p : G.Walk a b) (hp : p.IsPath)
    (hv : v ∈ p.support)
    (hl : 0 < (p.takeUntil v hv).dropLast.length)
    (hr : 0 < (p.dropUntil v hv).tail.length) :
    (p.takeUntil v hv).penultimate ≠ (p.dropUntil v hv).snd := by
  let t := p.takeUntil v hv
  let d := p.dropUntil v hv
  have heq : t.append d = p := p.take_spec hv
  have htn : ¬t.Nil := by
    intro hz
    change 0 < t.dropLast.length at hl
    rw [SimpleGraph.Walk.length_dropLast, hz.length_eq_zero] at hl
    omega
  have hdn : ¬d.Nil := by
    intro hz
    change 0 < d.tail.length at hr
    rw [SimpleGraph.Walk.length_tail, hz.length_eq_zero] at hr
    omega
  have hdj := hp.isTrail.edges_nodup
  rw [← heq, SimpleGraph.Walk.edges_append] at hdj
  have hdis := (List.nodup_append.mp hdj).2.2
  intro hsame
  have ha := t.mk_penultimate_end_mem_edges htn
  have hb := d.mk_start_snd_mem_edges hdn
  apply hdis _ ha _ hb

  rw [show t.penultimate = d.snd from hsame, Sym2.eq_swap]

theorem delete_vertex_new_endpoint_load {V : Type cycleUniverse27} {I : Type cycleUniverse28} [DecidableEq V] [Fintype I]
    {G : SimpleGraph V} {a b : I → V} {v : V}
    (p : ∀ i, G.Walk (a i) (b i)) (hp : ∀ i, (p i).IsPath)
    (hv : ∀ i, v ∈ (p i).support)
    (hd : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet) (x : V) :
    let live := fun z : I × Bool => if z.2 then
      0 < ((p z.1).takeUntil v (hv z.1)).dropLast.length else
      0 < ((p z.1).dropUntil v (hv z.1)).tail.length
    let newEnd := fun z : I × Bool => if z.2 then
      ((p z.1).takeUntil v (hv z.1)).penultimate else
      ((p z.1).dropUntil v (hv z.1)).snd
    (Finset.univ.filter fun z => live z ∧ newEnd z = x).card ≤ 1 := by
  classical
  dsimp only
  apply Finset.card_le_one.mpr
  intro z hz w hw
  obtain ⟨i, bi⟩ := z
  obtain ⟨j, bj⟩ := w
  have hi := (Finset.mem_filter.mp hz).2
  have hj := (Finset.mem_filter.mp hw).2
  have hei : s(v,x) ∈ (p i).edgeSet := by
    cases bi
    · have hx : ((p i).dropUntil v (hv i)).snd = x := hi.2
      simpa only [hx] using (delete_vertex_boundary_edges (p i) (hv i)).2 hi.1
    · have hx : ((p i).takeUntil v (hv i)).penultimate = x := hi.2
      have he := (delete_vertex_boundary_edges (p i) (hv i)).1 hi.1
      simpa only [hx, Sym2.eq_swap] using he
  have hej : s(v,x) ∈ (p j).edgeSet := by
    cases bj
    · have hx : ((p j).dropUntil v (hv j)).snd = x := hj.2
      simpa only [hx] using (delete_vertex_boundary_edges (p j) (hv j)).2 hj.1
    · have hx : ((p j).takeUntil v (hv j)).penultimate = x := hj.2
      have he := (delete_vertex_boundary_edges (p j) (hv j)).1 hj.1
      simpa only [hx, Sym2.eq_swap] using he
  have hij : i = j := by
    by_contra hn
    exact Set.disjoint_left.mp (hd hn) hei hej
  subst j
  congr 1
  cases bi <;> cases bj
  · rfl
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hj.1 hi.1
    exact (he (hj.2.trans hi.2.symm)).elim
  · have he := delete_vertex_new_ends_ne (p i) (hp i) (hv i) hi.1 hj.1
    exact (he (hi.2.trans hj.2.symm)).elim
  · rfl

namespace SimplePathPiece
attribute [local instance] Classical.propDecidable
variable {V : Type cycleUniverse30} {I : Type cycleUniverse31} [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deleted_ends {V : Type cycleUniverse32} {I : Type cycleUniverse33} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v x : V) (j : DeleteIndex p v) :
    (deleted p v j).start = x ∨ (deleted p v j).finish = x ↔
      oldEnd p v x j ∨ newEnd p v x j := by
  rcases j with i | ⟨i,b⟩
  · simp [deleted, oldEnd, newEnd]
  · cases b <;> simp [deleted, oldEnd, newEnd, or_comm]

lemma deleted_edges_subset {V : Type cycleUniverse34} {I : Type cycleUniverse35} [_contextInstance2 : Fintype I] [_contextInstance3 : DecidableEq V] {G : SimpleGraph V} (p : I → SimplePathPiece G) (v : V) (j : DeleteIndex p v) :
    (deleted p v j).walk.edgeSet ⊆ (p (parent p v j)).walk.edgeSet := by
  rcases j with i | ⟨i,b⟩
  · exact Set.Subset.rfl
  · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
    cases b
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inr he).1
    · intro e he
      exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
        h ▸ Or.inl he).1

lemma deleted_disjoint (p : I → SimplePathPiece G) (v : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    Pairwise fun j k => Disjoint (deleted p v j).walk.edgeSet (deleted p v k).walk.edgeSet := by
  intro j k hjk
  by_cases he : parent p v j = parent p v k
  · rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
    · exact (hjk (congrArg Sum.inl (Subtype.ext he))).elim
    · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
    · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
    · have hil : i = l := Subtype.ext he
      subst l
      cases b <;> cases c
      · exact (hjk rfl).elim
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1.symm
      · exact (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.1
      · exact (hjk rfl).elim
  · exact (hd he).mono (deleted_edges_subset p v j) (deleted_edges_subset p v k)

lemma deleted_old_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => oldEnd p v x j).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hjp : (p (parent p v j)).start = x ∨ (p (parent p v j)).finish = x := by
    have h := (Finset.mem_filter.mp hj).2
    rcases j with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have hkp : (p (parent p v k)).start = x ∨ (p (parent p v k)).finish = x := by
    have h := (Finset.mem_filter.mp hk).2
    rcases k with i | ⟨i,b⟩
    · exact h
    · cases b
      · exact Or.inr h
      · exact Or.inl h
  have he := Finset.card_le_one.mp hload (parent p v j)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjp⟩) (parent p v k)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkp⟩)
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩ <;> rcases k with l | ⟨l,c⟩
  · exact congrArg Sum.inl (Subtype.ext he)
  · exact (i.property (show v ∈ (p i.val).walk.support from (show i.val = l.val from he).symm ▸ l.property)).elim
  · exact (l.property (show v ∈ (p l.val).walk.support from (show i.val = l.val from he) ▸ i.property)).elim
  · have hil : i = l := Subtype.ext he
    subst l
    cases b <;> cases c
    · rfl
    · exact (hne _ (hk'.trans hj'.symm)).elim
    · exact (hne _ (hj'.trans hk'.symm)).elim
    · rfl

lemma deleted_new_load (p : I → SimplePathPiece G) (v x : V)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet) :
    (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧ newEnd p v x j).card ≤ 1 := by
  classical
  have h := delete_vertex_new_endpoint_load
    (fun i : Meeting p v => (p i.val).walk) (fun i => (p i.val).isPath)
    (fun i => i.property)
    (fun i j hij => hd (fun he => hij (Subtype.ext he))) x
  apply Finset.card_le_one.mpr
  intro j hj k hk
  have hj' := (Finset.mem_filter.mp hj).2
  have hk' := (Finset.mem_filter.mp hk).2
  rcases j with i | ⟨i,b⟩
  · exact False.elim hj'.2
  rcases k with l | ⟨l,c⟩
  · exact False.elim hk'.2
  apply congrArg Sum.inr
  apply Finset.card_le_one.mp h
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases b <;> exact hj'
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases c <;> exact hk'

theorem deleted_endpoint_load (p : I → SimplePathPiece G) (v x : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hload : (Finset.univ.filter fun i => (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)).card ≤ 2 := by
  classical
  let A := Finset.univ.filter (fun j : DeleteIndex p v => oldEnd p v x j)
  let B := Finset.univ.filter (fun j : DeleteIndex p v =>
    0 < (deleted p v j).walk.length ∧ newEnd p v x j)
  have hsub : (Finset.univ.filter fun j : DeleteIndex p v =>
      0 < (deleted p v j).walk.length ∧
      ((deleted p v j).start = x ∨ (deleted p v j).finish = x)) ⊆ A ∪ B := by
    intro j hj
    obtain ⟨hpos,hend⟩ := (Finset.mem_filter.mp hj).2
    rcases (deleted_ends p v x j).mp hend with ho | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ho⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos,hn⟩)
  have ha := deleted_old_load p v x hne hload
  have hb := deleted_new_load p v x hd
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  dsimp [A,B] at hc
  omega

theorem deleted_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : DeleteIndex p v, (deleted p v j).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    refine ⟨⟨parent p v j, deleted_edges_subset p v j hj⟩,?_⟩
    rcases j with i | ⟨i,b⟩
    · intro hv
      exact i.property (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨e,hj,hv⟩))
    · have h := (delete_vertex_from_path (p i.val).walk (p i.val).isPath i.property).2.2.2.1
      cases b
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inr hj).2
      · exact (show e ∈ {e | e ∈ (p i.val).walk.edgeSet ∧ v ∉ e} from
          h ▸ Or.inl hj).2
  · rintro ⟨⟨i,hi⟩,hv⟩
    by_cases hs : v ∈ (p i).walk.support
    · have h := (delete_vertex_from_path (p i).walk (p i).isPath hs).2.2.2.1
      have he : e ∈ ((p i).walk.takeUntil v hs).dropLast.edgeSet ∪
          ((p i).walk.dropUntil v hs).tail.edgeSet := h.symm ▸ ⟨hi,hv⟩
      rcases he with hl | hr
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,true),hl⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inr (⟨i,hs⟩,false),hr⟩
    · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨i,hs⟩,hi⟩

theorem deleted_positive_union (p : I → SimplePathPiece G) (v : V) :
    (⋃ j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length},
      (deleted p v j.val).walk.edgeSet) =
      {e | (∃ i, e ∈ (p i).walk.edgeSet) ∧ v ∉ e} := by
  rw [← deleted_union p v]
  ext e
  constructor
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    exact Set.mem_iUnion.mpr ⟨j.val,hj⟩
  · intro he
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
    have hp : 0 < (deleted p v j).walk.length := by
      by_contra hn
      have hz : (deleted p v j).walk.length = 0 := by omega
      have hn' := SimpleGraph.Walk.length_eq_zero_iff.mp hz
      have he' := SimpleGraph.Walk.edges_eq_nil.mpr hn'
      have hmem : e ∈ (deleted p v j).walk.edges := hj
      exact List.not_mem_nil (he' ▸ hmem)
    exact Set.mem_iUnion.mpr ⟨⟨j,hp⟩,hj⟩

end SimplePathPiece

end
end ErdosGallai
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.EndpointPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6 cycleUniverse7 cycleUniverse8 cycleUniverse9 cycleUniverse10 cycleUniverse11 cycleUniverse12 cycleUniverse13 cycleUniverse14

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem endpoint_partition_of_family {V : Type cycleUniverse1} {I : Type cycleUniverse2} [Fintype V] [Fintype I]
    {G : SimpleGraph V} (P : I → PositiveSimplePath G)
    (hd : Pairwise fun i j => Disjoint (P i).walk.edgeSet (P j).walk.edgeSet)
    (hc : (⋃ i, (P i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 2) : EndpointPathPartition G := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => P (e j),?_,?_,?_,endpoint_path_count P hl⟩
  · intro i j hij
    exact hd (fun he => hij (e.injective he))
  · rw [← hc]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩; exact ⟨e i,hi⟩
    · rintro ⟨i,hi⟩; exact ⟨e.symm i,by rw [e.apply_symm_apply]; exact hi⟩
  · intro x
    have heq : (Finset.univ.filter fun j => (P (e j)).start = x ∨ (P (e j)).finish = x).card =
        (Finset.univ.filter fun i => (P i).start = x ∨ (P i).finish = x).card := by
      apply Finset.card_bij (fun j _ => e j)
      · intro i hi; simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
      · intro i hi j hj he; exact e.injective he
      · intro i hi; exact ⟨e.symm i,by simpa using hi, by simp⟩
    rw [heq]
    exact hl x

theorem endpoint_partition_mapIso {V : Type cycleUniverse5} {W : Type cycleUniverse6} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : G ≃g H)
    (hp : EndpointPathPartition G) : EndpointPathPartition H := by
  classical
  obtain ⟨k,P,hd,hc,hl,hk⟩ := hp
  apply endpoint_partition_of_family (fun i => (P i).mapIso f)
  · intro i j hij
    change Disjoint ((P i).walk.map f.toHom).edgeSet ((P j).walk.map f.toHom).edgeSet
    simp only [SimpleGraph.Walk.edgeSet_map]
    exact (Set.disjoint_image_iff (Sym2.map.injective f.injective)).mpr (hd hij)
  · have hmap : Sym2.map f.toHom '' G.edgeSet = H.edgeSet := by
      ext e
      induction e using Sym2.inductionOn with | _ u v =>
        constructor
        · rintro ⟨e,he,heq⟩
          induction e using Sym2.inductionOn with | _ a b =>
            have ha : H.Adj (f a) (f b) := f.toHom.map_adj he
            exact heq ▸ ha
        · intro huv
          refine ⟨s(f.symm u, f.symm v), f.symm.toHom.map_adj huv,?_⟩
          simp
    change (⋃ i, ((P i).walk.map f.toHom).edgeSet) = H.edgeSet
    simp_rw [SimpleGraph.Walk.edgeSet_map]
    rw [← Set.image_iUnion,hc,hmap]
  · intro x
    have heq : (Finset.univ.filter fun i => ((P i).mapIso f).start = x ∨
        ((P i).mapIso f).finish = x) =
        (Finset.univ.filter fun i => (P i).start = f.symm x ∨ (P i).finish = f.symm x) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      change (f (P i).start = x ∨ f (P i).finish = x) ↔ _
      exact or_congr (f.toEquiv.eq_symm_apply.symm) (f.toEquiv.eq_symm_apply.symm)
    rw [heq]
    exact hl _

namespace SimplePathPiece
variable {V : Type cycleUniverse7} {I : Type cycleUniverse8} [Fintype V] [Fintype I] [DecidableEq V] {G : SimpleGraph V}

lemma deletedInduced_edges (p : I → SimplePathPiece G) (v : V)
    (j : {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}) :
    Sym2.map (SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}).toHom ''
      (deletedInduced p v j).walk.edgeSet = (deleted p v j.val).walk.edgeSet := by
  calc
    _ = ((deletedInduced p v j).walk.map
        (SimpleGraph.Embedding.induce {x | x ≠ v}).toHom).edgeSet :=
      (SimpleGraph.Walk.edgeSet_map _ _).symm
    _ = _ := congrArg (fun q : G.Walk (deleted p v j.val).start
        (deleted p v j.val).finish => q.edgeSet) (deletedInduced_map p v j)

theorem endpoint_partition_after_deletion (p : I → SimplePathPiece G) (v : V)
    (hne : ∀ i, (p i).start ≠ (p i).finish)
    (hd : Pairwise fun i j => Disjoint (p i).walk.edgeSet (p j).walk.edgeSet)
    (hc : (⋃ i, (p i).walk.edgeSet) = G.edgeSet)
    (hl : ∀ x : V, x ≠ v → (Finset.univ.filter fun i =>
      (p i).start = x ∨ (p i).finish = x).card ≤ 1) :
    EndpointPathPartition (G.induce {x | x ≠ v}) := by
  classical
  let A := {j : DeleteIndex p v // 0 < (deleted p v j).walk.length}
  let f : G.induce {x | x ≠ v} →g G := (SimpleGraph.Embedding.induce _).toHom
  have hf : Function.Injective f := Subtype.val_injective
  apply endpoint_partition_of_family (fun j : A => deletedPositive p v j)
  · intro j k hjk
    have hdis := deleted_disjoint p v hd (fun he => hjk (Subtype.ext he))
    apply Set.disjoint_left.mpr
    intro e hej hek
    have he1 : Sym2.map f e ∈ (deleted p v j.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v j]
      exact ⟨e,hej,rfl⟩
    have he2 : Sym2.map f e ∈ (deleted p v k.val).walk.edgeSet := by
      rw [← deletedInduced_edges p v k]
      exact ⟨e,hek,rfl⟩
    exact Set.disjoint_left.mp hdis he1 he2
  · apply Set.Subset.antisymm
    · intro e he
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp he
      exact (deletedPositive p v j).walk.edges_subset_edgeSet hj
    · intro e he
      have he' : Sym2.map f e ∈ G.edgeSet ∧ v ∉ Sym2.map f e := by
        induction e using Sym2.inductionOn with | _ a b =>
          refine ⟨he,?_⟩
          change v ∉ s(a.val,b.val)
          simpa only [Sym2.map_mk,Sym2.mem_iff,eq_comm] using not_or.mpr ⟨a.property,b.property⟩
      have hmem : Sym2.map f e ∈ ⋃ j : A, (deleted p v j.val).walk.edgeSet := by
        rw [deleted_positive_union]
        refine ⟨?_,he'.2⟩
        exact Set.mem_iUnion.mp (hc.symm ▸ he'.1)
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hmem
      rw [← deletedInduced_edges p v j] at hj
      obtain ⟨e',he',heq⟩ := hj
      have heq' : e' = e := Sym2.map.injective hf heq
      subst e'
      exact Set.mem_iUnion.mpr ⟨j,he'⟩
  · intro x
    have hb := deleted_endpoint_load p v x.val hne hd (hl x.val x.property)
    have hc' : (Finset.univ.filter fun j : A =>
        (deletedPositive p v j).start = x ∨ (deletedPositive p v j).finish = x).card ≤
        (Finset.univ.filter fun j : DeleteIndex p v => 0 < (deleted p v j).walk.length ∧
          ((deleted p v j).start = x.val ∨ (deleted p v j).finish = x.val)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro j hj
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,j.property,?_⟩
        rcases (Finset.mem_filter.mp hj).2 with hs | ht
        · exact Or.inl (congrArg Subtype.val hs)
        · exact Or.inr (congrArg Subtype.val ht)
      · exact fun _ _ _ _ he => Subtype.ext he
    refine le_trans (le_of_eq (congrArg Finset.card ?_)) (hc'.trans hb)
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]

end SimplePathPiece

theorem endpoint_partition_of_augmented_parts {V : Type cycleUniverse12} [Fintype V]
    (G : SimpleGraph V) (hL : LovaszPathCyclePartition (evenAugmentation G)) :
    EndpointPathPartition G := by
  classical
  obtain ⟨k,parts,hparts,hd,hc,hk⟩ := hL
  have hw : ∀ i : Fin k, ∃ (a b : Option V) (p : (evenAugmentation G).Walk a b),
      p.IsTrail ∧ (a ≠ b → p.IsPath) ∧ parts i = p.edgeSet := by
    intro i
    rcases hparts i with ⟨a,b,p,hp,_,he⟩ | ⟨a,p,hp,he⟩
    · exact ⟨a,b,p,hp.isTrail,fun _ => hp,he⟩
    · exact ⟨a,a,p,hp.isTrail,fun h => False.elim (h rfl),he⟩
  choose a b p ht hp he using hw
  have hd' : Pairwise fun i j => Disjoint (p i).edgeSet (p j).edgeSet := by
    simpa only [he] using hd
  have hc' : (⋃ i, (p i).edgeSet) = (evenAugmentation G).edgeSet := by
    simpa only [he] using hc
  let S : Finset (Option V) := Finset.univ.image some
  have hS : S.card = Fintype.card V := by
    simp only [S,Finset.card_image_of_injective _ (Option.some_injective V),Finset.card_univ]
  have ho : ∀ x ∈ S, Odd ((evenAugmentation G).degree x) := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hx
    exact evenAugmentation_old_odd G y
  have hk' : 2 * Fintype.card (Fin k) ≤ S.card + 1 := by
    simpa only [Fintype.card_fin,Fintype.card_option,hS] using hk
  obtain ⟨hopen,hload⟩ := tight_odd_trail_partition (evenAugmentation G) S p ht hd' hc' ho hk'
  let P : Fin k → SimplePathPiece (evenAugmentation G) := fun i =>
    ⟨a i,b i,p i,hp i (hopen i)⟩
  have hload' : ∀ x : Option V, x ≠ none → (Finset.univ.filter fun i =>
      (P i).start = x ∨ (P i).finish = x).card ≤ 1 := by
    intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x =>
      have h := hload (some x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
      have hpred : (Finset.univ.filter fun i => a i ≠ b i ∧
          (some x = a i ∨ some x = b i)) =
          (Finset.univ.filter fun i => (P i).start = some x ∨ (P i).finish = some x) := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,P]
        constructor
        · rintro ⟨_,hi⟩
          exact hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
        · intro hi
          exact ⟨hopen i,hi.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
      apply le_of_eq
      calc
        _ = _ := congrArg Finset.card hpred.symm
        _ = 1 := by
          convert h using 1
          congr 1
          ext i
          simp only [Finset.mem_filter,Finset.mem_univ,true_and]

  have hdel := SimplePathPiece.endpoint_partition_after_deletion P none hopen hd' hc' hload'
  exact endpoint_partition_mapIso (evenAugmentationOldIso G).symm hdel

end
end ErdosGallai

namespace ErdosGallai
noncomputable section

theorem lovasz_path_cycle_partition {V : Type cycleUniverse13} [Fintype V] (G : SimpleGraph V) :
    LovaszPathCyclePartition G :=
  lovasz_path_cycle_decomposition G

theorem endpoint_path_partition {V : Type cycleUniverse14} [Fintype V] (G : SimpleGraph V) :
    EndpointPathPartition G :=
  endpoint_partition_of_augmented_parts G (lovasz_path_cycle_partition (evenAugmentation G))

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
noncomputable section
namespace ErdosGallai

noncomputable section
open SimpleGraph

lemma cycleOrSingleEdge_subset {V : Type} {G : SimpleGraph V}
    {s : Set (Sym2 V)} (hs : CycleOrSingleEdge G s) : s ⊆ G.edgeSet := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact p.edges_subset_edgeSet
  · simpa using he

lemma cycleOrSingleEdge_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) {s : Set (Sym2 V)}
    (hs : CycleOrSingleEdge G s) : CycleOrSingleEdge H (Sym2.map f '' s) := by
  rcases hs with ⟨v,p,hp,rfl⟩ | ⟨e,he,rfl⟩
  · exact Or.inl ⟨f v,p.map f,hp.map hf,(p.edgeSet_map f).symm⟩
  · refine Or.inr ⟨Sym2.map f e, ?_, by simp⟩
    induction e using Sym2.ind with | _ x y =>
      exact f.map_adj he

theorem edgeDecomposition_assemble {V I : Type} [Fintype I] (G : SimpleGraph V)
    (W : I → Type) (H : ∀ i, SimpleGraph (W i))
    (f : ∀ i, H i →g G) (hf : ∀ i, Function.Injective (f i))
    (hdisj : Pairwise (fun i j =>
      Disjoint (Sym2.map (f i) '' (H i).edgeSet) (Sym2.map (f j) '' (H j).edgeSet)))
    (hcover : (⋃ i, Sym2.map (f i) '' (H i).edgeSet) = G.edgeSet)
    (k : I → ℕ) (hparts : ∀ i, EdgeDecomposition (H i) (k i)) :
    EdgeDecomposition G (∑ i, k i) := by
  classical
  choose parts hp hd hu using hparts
  let J := Σ i, Fin (k i)
  let P : J → Set (Sym2 V) := fun j => Sym2.map (f j.1) '' parts j.1 j.2
  have hpart : ∀ j, CycleOrSingleEdge G (P j) := by
    intro j; exact cycleOrSingleEdge_map (f j.1) (hf j.1) (hp j.1 j.2)
  have hsub : ∀ i a, parts i a ⊆ (H i).edgeSet := by
    intro i a; exact cycleOrSingleEdge_subset (hp i a)
  have hdisjP : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    rintro ⟨i,a⟩ ⟨j,b⟩ hij
    by_cases h : i = j
    · subst j
      have hab : a ≠ b := fun he => hij (by cases he; rfl)
      apply Set.disjoint_left.mpr
      rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
      have hxy : x = y := Sym2.map.injective (hf i) (he.trans he'.symm)
      subst y
      exact Set.disjoint_left.mp (hd i hab) hx hy
    · exact (hdisj h).mono (Set.image_mono (hsub i a)) (Set.image_mono (hsub j b))
  have hcoverP : (⋃ j, P j) = G.edgeSet := by
    rw [← hcover]
    ext e
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i,a⟩,x,hx,he⟩
      exact ⟨i,x,hsub i a hx,he⟩
    · rintro ⟨i,x,hx,he⟩
      rw [← hu i] at hx
      obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i,a⟩,x,ha,he⟩
  have hc : Fintype.card J = ∑ i, k i := by simp [J, Fintype.card_sigma]
  rw [← hc]
  exact edgeDecomposition_of_indexed G P hpart hdisjP hcoverP

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

theorem small_residue (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj], P ≤ G →
      D^(9/10:ℝ) ≤ (Fintype.card V:ℝ) →
      (Fintype.card V:ℝ) ≤ D^(51/50:ℝ) →
      Splitting.CutExpansion P (c*D^(9/10:ℝ)) →
      ∃ (k : ℕ) (parts : Fin k → Set (Sym2 V))
        (W : Fin 3 → Finset V) (H : Fin 3 → SimpleGraph V),
        (∀ i, CycleOrSingleEdge G (parts i)) ∧
        Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
        (∀ b, H b ≤ G ∧ (H b).support ⊆ (W b : Set V)) ∧
        (∀ b, (W b).card < Fintype.card V) ∧
        ((∑ b, (W b).card : ℕ):ℝ) ≤ η * Fintype.card V ∧
        Pairwise (fun b d => Disjoint (H b).edgeSet (H d).edgeSet) ∧
        (∀ b i, Disjoint (H b).edgeSet (parts i)) ∧
        ((⋃ i, parts i) ∪ (⋃ b, (H b).edgeSet)) = G.edgeSet ∧
        k ≤ 9 * Fintype.card V := by
  classical
  have ha : 0 < reservoirExpansionCoefficient c := by
    unfold reservoirExpansionCoefficient
    exact div_pos (lt_min hc (by norm_num)) (by norm_num)
  have hp : 0 < reservoirProbability η := by
    unfold reservoirProbability
    exact lt_min (div_pos hη (by norm_num)) (by norm_num)
  obtain ⟨D₁,hprep⟩ := reservoir_preparation c η hc hη
  obtain ⟨D₂,hD₂,hclose⟩ := uniform_three_reservoir_completion
    (reservoirExpansionCoefficient c) (reservoirProbability η) ha hp
  refine ⟨max D₁ D₂, hD₂.trans_le (le_max_right _ _), ?_⟩
  intro D hD V _ _ G P _ hPG hlo hhi hexp
  obtain ⟨ω,W,r,hPG',hPP,hPexp,hWW,hW2,hWsize,hWlt,hWsum,hWexp,hr,hrne,hcap⟩ :=
    hprep D ((le_max_left _ _).trans hD) V G P hPG hlo hhi hexp
  let P' := fun b => Splitting.colorGraph P ω b
  have hWW' : Pairwise fun b d => Disjoint (W b : Set V) (W d : Set V) := by
    intro b d hbd
    exact Finset.disjoint_coe.mpr (hWW b d hbd)
  let R := fun b => reservoirInternal (P' b) (W b)
  let T := fun b => R b ∪ (reservoirSpokes (W b) (r b) : Set (Sym2 V))
  let E : Set (Sym2 V) := ⋃ b, T b
  have hres := reservoir_reservations G P' W r hPG' hPP
    (fun b v hv t => (hr b v hv t).2)
  have hE : E ⊆ G.edgeSet := Set.iUnion_subset fun b =>
    Set.union_subset (hres.1 b).1 (hres.1 b).2
  let K := fun b => complementaryReservoirGraph (G.deleteEdges E)
    (fun b => (W b : Set V)) hWW' b
  have hK := complementary_reservoir_graphs (G.deleteEdges E)
    (fun b => (W b : Set V)) hWW'
  have hKG : ∀ b, K b ≤ G := fun b => (hK.1 b).trans (G.deleteEdges_le E)
  have hledger := complementary_reservation_ledger G (fun b => (W b : Set V)) hWW' E hE
  have hKT : ∀ b d, Disjoint (K b).edgeSet (T d) := fun b d =>
    (hledger.2.1 b).mono_right (Set.subset_iUnion T d)
  have hx : ∀ b : Fin 3, EndpointPathPartition (K b) := fun b => endpoint_path_partition (K b)
  choose k Q hQQ hQc hQl hQn using hx
  let x := fun b i => (Q b i).start
  let y := fun b i => (Q b i).finish
  let q : ∀ b i, G.Walk (x b i) (y b i) := fun b i => (Q b i).walk.mapLe (hKG b)
  have hqp : ∀ b i, (q b i).IsPath := fun b i => (Q b i).isPath.mapLe _
  have hql : ∀ b i, 0 < (q b i).length := by
    intro b i
    simpa [q] using (Q b i).positive
  have hqo : ∀ b i v, v ∈ (q b i).support → v ∉ W b := by
    intro b i v hv
    apply complementary_walk_outside (fun b => (W b : Set V)) hWW' b
      (Q b i).walk (Q b i).positive v
    simpa [q] using hv
  have hqd : ∀ b, Pairwise fun i j => Disjoint (q b i).edgeSet (q b j).edgeSet := by
    intro b i j hij
    simpa [q] using hQQ b hij
  have hqc : ∀ b, (⋃ i, (q b i).edgeSet) = (K b).edgeSet := by
    intro b
    simpa [q] using hQc b
  obtain ⟨C,hCy,hCC,hCsub,hcover,hcount⟩ := hclose D ((le_max_right _ _).trans hD)
    V G P' K hPG' hPP W r hWexp hW2 hhi hr hrne hcap
    hledger.1 hKT (fun b => Fin (k b)) x y q hqp hql hqo hqd hqc
      (by
        intro b v
        dsimp only [endpointLoad,x,y]
        convert hQl b v using 2
        ext i
        simp)
  let I := Σ b, Fin (k b)
  let CE : I → Set (Sym2 V) := fun z => (C z.1 z.2).edgeSet
  have hCE : ∀ i, CE i ⊆ G.edgeSet := fun i => (C i.1 i.2).edges_subset_edgeSet
  have hEeq : E = (⋃ b, R b) ∪ (allReservoirSpokes W r : Set _) := by
    simp only [E,T,coe_allReservoirSpokes,Set.iUnion_union_distrib]
  have hcov : G.edgeSet \ ((⋃ b, R b) ∪ (allReservoirSpokes W r : Set _)) ⊆
      completedEdges CE := by
    rw [← hEeq, ← SimpleGraph.edgeSet_deleteEdges, ← hK.2.2.2]
    exact hcover
  obtain ⟨hsupp,hind,hHe,hHH,hHC,hHS,hCS,hu,hnum⟩ :=
    three_reservoir_remainder G P' W r hPG' hPP
      (fun b v hv t => (hr b v hv t).2) CE hCE hCC hcount hcov
  let H := residualInternalGraph G R CE
  let S := unusedSpokes (↑(allReservoirSpokes W r)) CE
  let J := I ⊕ S
  let parts : J → Set (Sym2 V) := Sum.elim CE (fun e => {e.val})
  have hSsub : (S : Set (Sym2 V)) ⊆ G.edgeSet := by
    intro e he
    have hh : e ∈ (allReservoirSpokes W r : Set _) := by
      have hh := he
      simp only [Finset.mem_coe,S,unusedSpokes,Set.mem_toFinset,Set.mem_sdiff] at hh
      exact hh.1
    exact hE (by rw [hEeq]; exact Or.inr hh)
  have hpart : ∀ j, CycleOrSingleEdge G (parts j) := by
    intro j
    rcases j with i | e
    · exact Or.inl ⟨x i.1 i.2,C i.1 i.2,hCy i.1 i.2,rfl⟩
    · exact Or.inr ⟨e.val,hSsub e.property,rfl⟩
  have hpd : Pairwise fun i j => Disjoint (parts i) (parts j) := by
    intro i j hij
    rcases i with i | e <;> rcases j with j | f
    · exact hCC (fun h => hij (congrArg Sum.inl h))
    · exact (hCS i).mono_right (Set.singleton_subset_iff.mpr f.property)
    · exact (hCS j).symm.mono_left (Set.singleton_subset_iff.mpr e.property)
    · exact Set.disjoint_singleton.mpr (fun h => hij (congrArg Sum.inr (Subtype.ext h)))
  have hpartU : (⋃ j, parts j) = completedEdges CE ∪ (S : Set (Sym2 V)) := by
    ext e
    simp only [Set.mem_iUnion, Set.mem_union, completedEdges, parts]
    constructor
    · rintro ⟨i,hi⟩
      rcases i with i | f
      · exact Or.inl ⟨i,hi⟩
      · exact Or.inr ((Set.mem_singleton_iff.mp hi) ▸ f.property)
    · rintro (⟨i,hi⟩ | he)
      · exact ⟨Sum.inl i,hi⟩
      · exact ⟨Sum.inr ⟨e,he⟩,rfl⟩
  let equiv := Fintype.equivFin J
  refine ⟨Fintype.card J,fun i => parts (equiv.symm i),W,H,?_,?_,?_,hWlt,hWsum,
    hHH,?_,?_,?_⟩
  · exact fun i => hpart _
  · intro i j hij
    exact hpd (fun h => hij (equiv.symm.injective h))
  · intro b
    refine ⟨?_,hsupp b⟩
    exact edgeRestriction_le G _
  · intro b i
    rcases hji : equiv.symm i with j | e
    all_goals simp only [hji, parts, Sum.elim_inl, Sum.elim_inr]
    · exact hHC b j
    · exact (hHS b).mono_right (Set.singleton_subset_iff.mpr e.property)
  · have he : (⋃ i, parts (equiv.symm i)) = ⋃ j, parts j := by
      ext e
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨i,hi⟩ => ⟨equiv.symm i,hi⟩,
        fun ⟨j,hj⟩ => ⟨equiv j,by simpa using hj⟩⟩
    rw [he,hpartU]
    exact hu
  · simpa only [J,Fintype.card_sum,Fintype.card_coe] using hnum

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_spec {V : Type} [Fintype V] (G : SimpleGraph V) :
    EdgeDecomposition G (decompositionCost G) := Nat.find_spec _

lemma decompositionCost_le {V : Type} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : EdgeDecomposition G k) : decompositionCost G ≤ k := Nat.find_min' _ h

theorem edgeDecomposition_adjoin {V I J : Type} [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) (H : ∀ j, SimpleGraph (W j)) (f : ∀ j, H j →g G)
    (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet)
    (k : J → ℕ) (hD : ∀ j, EdgeDecomposition (H j) (k j)) :
    EdgeDecomposition G (Fintype.card I + ∑ j, k j) := by
  classical
  choose P hP hPd hPc using hD
  let R : (I ⊕ Σ j, Fin (k j)) → Set (Sym2 V) :=
    Sum.elim parts (fun z => Sym2.map (f z.1) '' P z.1 z.2)
  have hsub : ∀ j i, P j i ⊆ (H j).edgeSet := fun j i => cycleOrSingleEdge_subset (hP j i)
  have hRp : ∀ z, CycleOrSingleEdge G (R z) := by
    intro z
    rcases z with z | ⟨j,i⟩
    · exact hp z
    · exact cycleOrSingleEdge_map (f j) (hf j) (hP j i)
  have hRd : Pairwise fun z t => Disjoint (R z) (R t) := by
    intro z t hzt
    rcases z with z | ⟨j,i⟩ <;> rcases t with t | ⟨l,a⟩
    · exact hd (fun h => hzt (congrArg Sum.inl h))
    · exact ((hHP l z).mono_left (Set.image_mono (hsub l a))).symm
    · exact (hHP j t).mono_left (Set.image_mono (hsub j i))
    · by_cases hjl : j = l
      · subst l
        have hia : i ≠ a := fun h => hzt (by cases h; rfl)
        apply Set.disjoint_left.mpr
        rintro e ⟨x,hx,he⟩ ⟨y,hy,he'⟩
        have hxy := Sym2.map.injective (hf j) (he.trans he'.symm)
        subst y
        exact Set.disjoint_left.mp (hPd j hia) hx hy
      · exact (hHH hjl).mono (Set.image_mono (hsub j i)) (Set.image_mono (hsub l a))
  have hRu : (⋃ z, R z) = G.edgeSet := by
    rw [← hu]
    ext e
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨z,hz⟩
      rcases z with z | ⟨j,i⟩
      · exact Or.inl ⟨z,hz⟩
      · obtain ⟨x,hx,he⟩ := hz
        exact Or.inr ⟨j,x,hsub j i hx,he⟩
    · rintro (⟨i,hi⟩ | ⟨j,x,hx,he⟩)
      · exact ⟨Sum.inl i,hi⟩
      · rw [← hPc j] at hx
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
        exact ⟨Sum.inr ⟨j,i⟩,x,hi,he⟩
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
    edgeDecomposition_of_indexed G R hRp hRd hRu

lemma decompositionCost_adjoin {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (W : J → Type) [∀ j, Fintype (W j)] (H : ∀ j, SimpleGraph (W j))
    (f : ∀ j, H j →g G) (hf : ∀ j, Function.Injective (f j))
    (hHH : Pairwise fun i j => Disjoint (Sym2.map (f i) '' (H i).edgeSet)
      (Sym2.map (f j) '' (H j).edgeSet))
    (hHP : ∀ j i, Disjoint (Sym2.map (f j) '' (H j).edgeSet) (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, Sym2.map (f j) '' (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) :=
  decompositionCost_le (edgeDecomposition_adjoin G parts hp hd W H f hf hHH hHP hu _
    (fun j => decompositionCost_spec (H j)))

end
end ErdosGallai
namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma edgeDecomposition_map {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f)
    (hu : Sym2.map f '' H.edgeSet = G.edgeSet) {k : ℕ} (hk : EdgeDecomposition H k) :
    EdgeDecomposition G k := by
  have := edgeDecomposition_assemble (I := Unit) G (fun _ : Unit => W) (fun _ => H) (fun _ => f)
    (fun _ => hf) (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
    (by rw [Set.iUnion_const]; exact hu) (fun _ => k) (fun _ => hk)
  simpa using this

lemma decompositionCost_on {V : Type} [Fintype V] (G : SimpleGraph V)
    (A : Finset V) (hA : ∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A) :
    decompositionCost G ≤ decompositionCost (G.induce (A:Set V)) := by
  classical
  let f : G.induce (A:Set V) →g G := ⟨Subtype.val,fun h => h⟩
  have hu : Sym2.map f '' (G.induce (A:Set V)).edgeSet = G.edgeSet := by
    ext e
    constructor
    · rintro ⟨e,he,rfl⟩
      induction e using Sym2.ind with | _ x y => exact he
    · intro he
      induction e using Sym2.ind with
      | _ x y =>
        exact ⟨s(⟨x,(hA he).1⟩,⟨y,(hA he).2⟩),he,rfl⟩
  exact decompositionCost_le (edgeDecomposition_map f Subtype.val_injective hu (decompositionCost_spec _))

end
end ErdosGallai
namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

lemma decompositionCost_adjoin_same {V I J : Type} [Fintype V] [Fintype I] [Fintype J]
    (G : SimpleGraph V) (parts : I → Set (Sym2 V))
    (hp : ∀ i, CycleOrSingleEdge G (parts i))
    (hd : Pairwise fun i j => Disjoint (parts i) (parts j))
    (H : J → SimpleGraph V) (hHG : ∀ j, H j ≤ G)
    (hHH : Pairwise fun i j => Disjoint (H i).edgeSet (H j).edgeSet)
    (hHP : ∀ j i, Disjoint (H j).edgeSet (parts i))
    (hu : (⋃ i, parts i) ∪ (⋃ j, (H j).edgeSet) = G.edgeSet) :
    decompositionCost G ≤ Fintype.card I + ∑ j, decompositionCost (H j) := by
  let f : ∀ j, H j →g G := fun j => ⟨id,fun h => hHG j h⟩
  have he (j) : Sym2.map (f j) '' (H j).edgeSet = (H j).edgeSet := by
    have hf : (f j : V → V) = id := rfl
    rw [hf, Sym2.map_id, Set.image_id]
  apply decompositionCost_adjoin G parts hp hd (fun _ => V) H f (fun _ => Function.injective_id)
  · simpa only [he] using hHH
  · simpa only [he] using hHP
  · simpa only [he] using hu

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem uniform_piece_cost (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ (n : ℕ) (C : ℝ), 0 ≤ C →
      (∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < n →
        (decompositionCost H:ℝ) ≤ C * Fintype.card W) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj], P ≤ G → Fintype.card V ≤ n →
      D^(9/10:ℝ) ≤ (Fintype.card V:ℝ) →
      (Fintype.card V:ℝ) ≤ D^(51/50:ℝ) →
      Splitting.CutExpansion P (c*D^(9/10:ℝ)) →
      (decompositionCost G:ℝ) ≤ (9+C*η)*Fintype.card V := by
  obtain ⟨D₀,hD₀,hres⟩ := small_residue c η hc hη
  refine ⟨D₀,hD₀,?_⟩
  intro D hD n C hC ih V _ _ G P _ hPG hn hlo hhi he
  obtain ⟨k,parts,W,H,hp,hd,hHG,hWlt,hWsum,hHH,hHP,hu,hk⟩ :=
    hres D hD V G P hPG hlo hhi he
  have hcost (b : Fin 3) : (decompositionCost (H b):ℝ) ≤ C * (W b).card := by
    have hA : ∀ ⦃x y⦄, (H b).Adj x y → x ∈ W b ∧ y ∈ W b := by
      intro x y hxy
      exact ⟨(hHG b).2 ⟨y,hxy⟩,(hHG b).2 ⟨x,hxy.symm⟩⟩
    calc
      _ ≤ (decompositionCost ((H b).induce (W b:Set V)):ℝ) :=
        Nat.cast_le.mpr (decompositionCost_on _ _ hA)
      _ ≤ C * Fintype.card (W b:Set V) := ih _ _ (by simpa using (hWlt b).trans_le hn)
      _ = _ := by simp
  have htot := decompositionCost_adjoin_same G parts hp hd H (fun b => (hHG b).1) hHH hHP hu
  have hsum : (∑ b, (decompositionCost (H b):ℝ)) ≤ C * ∑ b, ((W b).card:ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun b _ => hcost b)
  have hsum' := mul_le_mul_of_nonneg_left hWsum hC
  have hk' : (k:ℝ) ≤ 9 * Fintype.card V := by exact_mod_cast hk
  have htot' : (decompositionCost G:ℝ) ≤ k + ∑ b, (decompositionCost (H b):ℝ) := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_sum] using (Nat.cast_le.mpr htot : (decompositionCost G:ℝ) ≤ _)
  push_cast at hsum'
  nlinarith

end
end ErdosGallai

namespace ErdosGallai
noncomputable section
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

theorem uniform_piece_cost_on (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ (n : ℕ) (C : ℝ), 0 ≤ C →
      (∀ (W : Type) [Fintype W] (H : SimpleGraph W), Fintype.card W < n →
        (decompositionCost H:ℝ) ≤ C * Fintype.card W) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G P : SimpleGraph V)
        [DecidableRel P.Adj] (A : Finset V), P ≤ G → A.card ≤ n →
      (∀ ⦃x y⦄, G.Adj x y → x ∈ A ∧ y ∈ A) →
      D^(9/10:ℝ) ≤ (A.card:ℝ) → (A.card:ℝ) ≤ D^(51/50:ℝ) →
      CutExpansionOn P A (c*D^(9/10:ℝ)) →
      (decompositionCost G:ℝ) ≤ (9+C*η)*A.card := by
  obtain ⟨D₀,hD₀,hcost⟩ := uniform_piece_cost c η hc hη
  refine ⟨D₀,hD₀,?_⟩
  intro D hD n C hC ih V _ _ G P _ A hPG hn hA hlo hhi he
  have hcost' := hcost D hD n C hC ih (A:Set V) (G.induce (A:Set V))
    (P.induce (A:Set V)) (fun _ _ h => hPG h) (by simpa using hn)
    (by simpa using hlo) (by simpa using hhi) (cutExpansion_induce P A _ he)
  calc
    _ ≤ (decompositionCost (G.induce (A:Set V)):ℝ) := Nat.cast_le.mpr (decompositionCost_on G A hA)
    _ ≤ _ := by simpa using hcost'

end
end ErdosGallai

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.ScaleHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

lemma StageSplit.mem_children {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) (Q : AssignedPiece V) :
    Q ∈ s.children ↔ ∃ B ∈ s.boxes, Q.vertices = B.vertices ∧ Q.graph = s.remainder B := by
  simp only [StageSplit.children, List.mem_pmap]
  constructor
  · rintro ⟨B,hB,rfl⟩; exact ⟨B,hB,rfl,rfl⟩
  · rintro ⟨B,hB,hv,hg⟩
    refine ⟨B,hB,?_⟩
    cases Q; cases B; simp_all

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma nextLayer_mem (s : SplitSystem V) (j) (L) (Q : AssignedPiece V) :
    Q ∈ nextLayer s j L ↔ ∃ P ∈ L, ∃ B ∈ (s j P).boxes,
      Q.vertices = B.vertices ∧ Q.graph = (s j P).remainder B := by
  simp only [nextLayer,List.mem_flatMap,StageSplit.mem_children]

lemma advance_subset (s : SplitSystem V) (j k) (L) (A : Finset V)
    (hA : ∀ P ∈ L, P.vertices ⊆ A) :
    ∀ Q ∈ advance s j k L, Q.vertices ⊆ A := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,_⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    rw [hv]
    exact ((s (j+k) P).box_subset B hB).trans (ih P hP)

end
end ErdosGallai.Scale
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.CostRegrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe cycleUniverse1 cycleUniverse2

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset

section

namespace ErdosGallai
noncomputable section
open Real Filter

lemma mainEta_pos : 0 < mainEta := by norm_num [mainEta,mainP]

end
end ErdosGallai

end

end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.UniformLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

variable {P : AssignedPiece V} {Dstar : ℝ}

lemma Layers.subset (H : Layers P Dstar) (j) : ∀ Q ∈ H.frontier j, Q.vertices ⊆ P.vertices :=
  advance_subset H.system 0 j [P] P.vertices (by simp)

lemma Layers.box_subset (H : Layers P Dstar) (j) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier j) (hB : B ∈ (H.system j Q).boxes) : B.vertices ⊆ P.vertices :=
  ((H.system j Q).box_subset B hB).trans (H.subset j Q hQ)

end
end ErdosGallai.Scale

end

end
end

end OAI
end

section
-- module Solutions.OAIQW_ErdosGallai.LayerCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset

section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

lemma pastPieces_mem (s : SplitSystem V) (j k : ℕ) (L : List (AssignedPiece V))
    {R : AssignedPiece V} (hR : R ∈ pastPieces s j k L) :
    ∃ l < k, R ∈ levelPieces s (j+l) (advance s j l L) := by
  induction k with
  | zero => simp [pastPieces] at hR
  | succ k ih =>
    rcases List.mem_append.mp hR with h | h
    · obtain ⟨l,hl,hR⟩ := ih h
      exact ⟨l,by omega,hR⟩
    · exact ⟨k,by omega,h⟩

theorem uniform_committed_piece_cost_oai : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (P : AssignedPiece V) (H : Layers P Dstar),
    ∀ (C : ℝ), 0 ≤ C →
    (∀ (Q : Type) [Fintype Q] (G : SimpleGraph Q), Fintype.card Q < P.vertices.card →
      (ErdosGallai.decompositionCost G:ℝ) ≤ C*Fintype.card Q) →
    ∀ k ≤ H.count, ∀ R ∈ pastPieces H.system 0 k [P],
      (decompositionCost R.graph:ℝ) ≤ (9+C*ErdosGallai.mainEta)*R.vertices.card := by
  obtain ⟨D₀,hD₀,hpc⟩ := ErdosGallai.uniform_piece_cost_on 1 ErdosGallai.mainEta (by norm_num) ErdosGallai.mainEta_pos
  refine ⟨D₀,hD₀,?_⟩
  intro Dstar hD V _ _ P H C hC ih k hk R hR
  obtain ⟨j,hjk,hR⟩ := pastPieces_mem H.system 0 k [P] hR
  simp only [Nat.zero_add] at hR
  obtain ⟨Q,hQ,B,hB,hR⟩ := (by simpa [levelPieces,List.mem_flatMap] using hR :
    ∃ Q ∈ H.frontier j, ∃ B ∈ (H.system j Q).boxes, R ∈ (H.system j Q).pieces B)
  have hj : j < H.count := by omega
  have hb := (H.bounded j hj Q hQ).2.2.2.1 B hB R hR
  have hsub := ((H.system j Q).piece_subset B hB R hR).trans (H.box_subset j hQ hB)
  exact hpc (H.scale j) (hD.trans (H.cutoff j hj)) P.vertices.card C hC ih V R.graph R.graph R.vertices
    le_rfl (Finset.card_le_card hsub) R.supported hb.1 hb.2.1 (by
      simpa only [one_mul,ErdosGallai.CutExpansionOn,CutExpansionOn,cutCount,Layers.scale] using hb.2.2)

end
end ErdosGallai.Scale

end

end
end

end OAI
end

theorem solution : type_of% @OAI.ErdosGallai.Scale.uniform_committed_piece_cost_oai := @OAI.ErdosGallai.Scale.uniform_committed_piece_cost_oai
