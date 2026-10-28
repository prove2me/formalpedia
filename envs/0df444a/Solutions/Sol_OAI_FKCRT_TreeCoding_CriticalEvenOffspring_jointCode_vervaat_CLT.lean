-- Prove2me | solution 1 for OAI.FKCRT.TreeCoding.CriticalEvenOffspring.jointCode_vervaat_CLT
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T18:38:30.112569+00:00
-- url     : https://prove2.me/submissions/7d707802-6035-433e-98fd-9a1ee4a5000b

import Mathlib
import Definitions.Def_OAIQ021F004

section
-- module Solutions.OAIQ021_FK.Compat
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `aemeasurable_pi_lambda` (with `f` implicit). -/
theorem _root_.AEMeasurable.of_eval {δ ι : Type*} [Countable ι] {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {μ : MeasureTheory.Measure δ} {f : δ → ∀ i, π i}
    (h : ∀ i, AEMeasurable (fun a => f a i) μ) : AEMeasurable f μ := aemeasurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_WalkBounds
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma martingale_square_submartingale {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ι ‹MeasurableSpace Ω›}
    {f : ι → Ω → ℝ} (hf : Martingale f ℱ μ)
    (h₂ : ∀ i, Integrable (fun ω => (f i ω)^2) μ) :
    Submartingale (fun i ω => (f i ω)^2) ℱ μ := by
  refine ⟨fun i => (hf.stronglyMeasurable i).pow 2, ?_, h₂⟩
  intro i j hij
  have hj := (even_two.convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ (ℱ.le i)
    (continuous_pow 2).lowerSemicontinuous (hf.integrable j) (h₂ j)
  filter_upwards [hj, hf.condExp_ae_eq hij] with ω hJ hM
  simpa only [Function.comp_def, hM] using hJ


lemma martingale_maximal_square_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ μ)
    (h₂ : ∀ i, Integrable (fun ω => (f i ω)^2) μ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |f k ω|} ≤ (∫ ω, (f n ω)^2 ∂μ) / ε^2 := by
  let g := fun i ω => (f i ω)^2
  let E := {ω | ε^2 ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one
    (fun k => g k ω)}
  have hmax := maximal_ineq (martingale_square_submartingale hf h₂)
    (fun i ω => sq_nonneg (f i ω)) (ε := (⟨ε^2, sq_nonneg ε⟩ : ℝ≥0)) n
  have hs : {ω | ∃ k ≤ n, ε ≤ |f k ω|} ⊆ E := by
    rintro ω ⟨k, hk, hω⟩
    change ε^2 ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun k => g k ω)
    apply le_trans _ (Finset.le_sup' (fun k => g k ω) (Finset.mem_range.mpr (show k < n+1 by omega)))
    change ε^2 ≤ (f k ω)^2
    nlinarith [sq_abs (f k ω)]
  have hi : 0 ≤ ∫ ω in E, (f n ω)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  rw [ENNReal.toReal_mul] at ht
  erw [ENNReal.coe_toReal] at ht
  change ε^2 * (μ E).toReal ≤
    (ENNReal.ofReal (∫ ω in E, (f n ω)^2 ∂μ)).toReal at ht
  rw [ENNReal.toReal_ofReal hi] at ht
  have hwhole : (∫ ω in E, (f n ω)^2 ∂μ) ≤ ∫ ω, (f n ω)^2 ∂μ :=
    setIntegral_le_integral (h₂ n) (ae_of_all μ (fun _ => sq_nonneg _))
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  calc
    _ ≤ μ.real E * ε^2 := mul_le_mul_of_nonneg_right (measureReal_mono hs) (sq_nonneg _)
    _ ≤ ∫ ω in E, (f n ω)^2 ∂μ := by simpa [mul_comm, measureReal_def] using ht
    _ ≤ _ := hwhole


lemma independent_sum_second_moment {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX₂ : ∀ k, MemLp (X k) 2 μ) (hX : iIndepFun X μ)
    (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0) (s : Finset ι) :
    (∫ ω, (∑ k ∈ s, X k ω)^2 ∂μ) = ∑ k ∈ s, ∫ ω, (X k ω)^2 ∂μ := by
  have hS : MemLp (fun ω => ∑ k ∈ s, X k ω) 2 μ :=
    memLp_finsetSum _ (fun k _ => hX₂ k)
  have hSz : (∫ ω, ∑ k ∈ s, X k ω ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun k _ => (hX₂ k).integrable (by norm_num))]
    simp only [hzero, Finset.sum_const_zero]
  rw [← variance_of_integral_eq_zero hS.aemeasurable hSz]
  have hvar := IndepFun.variance_sum (s := s) (fun k _ => hX₂ k)
    (fun _ _ _ _ hne => hX.indepFun hne)
  have hfun : (∑ k ∈ s, X k) = (fun ω => ∑ k ∈ s, X k ω) := by ext ω; simp
  rw [hfun] at hvar
  rw [hvar]
  exact Finset.sum_congr rfl (fun k _ => variance_of_integral_eq_zero
    (hX₂ k).aemeasurable (hzero k))


lemma independent_sum_maximal_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₂ : ∀ k, MemLp (X k) 2 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |∑ j ∈ Finset.range k, X j ω|} ≤
      (∑ j ∈ Finset.range n, ∫ ω, (X j ω)^2 ∂μ) / ε^2 := by
  cases n with
  | zero => simp [not_le.mpr hε]
  | succ n =>
    have hmart := independent_sum_martingale X hXm
      (fun k => (hX₂ k).integrable (by norm_num)) hX hzero
    have hmax := martingale_maximal_square_bound hmart
      (fun m => (memLp_finsetSum (Finset.range (m+1))
        (fun k _ => hX₂ k)).integrable_sq) n hε
    rw [independent_sum_second_moment X hX₂ hX hzero] at hmax
    apply le_trans (measureReal_mono ?_) hmax
    rintro ω ⟨k, hk, hω⟩
    cases k with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, abs_zero] at hω
              exact (not_le.mpr hε hω).elim
    | succ k => exact ⟨k, by omega, hω⟩


lemma memLp_integrable_pow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {p j : ℕ} (hX : MemLp X (p : ℝ≥0∞) μ)
    (hj : j ≤ p) : Integrable (fun ω => (X ω)^j) μ := by
  have h := (hX.mono_exponent (show (j : ℝ≥0∞) ≤ p by exact_mod_cast hj)).integrable_norm_pow'
  exact h.mono (hX.aestronglyMeasurable.pow j)
    (ae_of_all μ (fun ω => by simp only [norm_pow, Real.norm_eq_abs, abs_abs, le_refl]))


lemma independent_add_fourth_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hXY : IndepFun X Y μ)
    (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0) :
    (∫ ω, (X ω + Y ω)^4 ∂μ) = (∫ ω, (X ω)^4 ∂μ) +
      6 * (∫ ω, (X ω)^2 ∂μ) * (∫ ω, (Y ω)^2 ∂μ) + (∫ ω, (Y ω)^4 ∂μ) := by
  have hXp : ∀ j ≤ 4, Integrable (fun ω => (X ω)^j) μ :=
    fun j hj => memLp_integrable_pow_le (p := 4) hX hj
  have hYp : ∀ j ≤ 4, Integrable (fun ω => (Y ω)^j) μ :=
    fun j hj => memLp_integrable_pow_le (p := 4) hY hj
  have hind : ∀ i j : ℕ, IndepFun (fun ω => (X ω)^i) (fun ω => (Y ω)^j) μ :=
    fun i j => hXY.comp (measurable_id.pow_const i) (measurable_id.pow_const j)
  have hprod : ∀ i ≤ 4, ∀ j ≤ 4, Integrable (fun ω => (X ω)^i * (Y ω)^j) μ :=
    fun i hi j hj => (hind i j).integrable_mul (hXp i hi) (hYp j hj)
  have hp : (fun ω => (X ω + Y ω)^4) =
      (fun ω => (X ω)^4 + 4 * ((X ω)^3 * (Y ω)^1) +
        6 * ((X ω)^2 * (Y ω)^2) + 4 * ((X ω)^1 * (Y ω)^3) + (Y ω)^4) := by
    funext ω; ring
  rw [hp]
  erw [integral_add (((hXp 4 le_rfl).add ((hprod 3 (by omega) 1 (by omega)).const_mul 4)).add
      ((hprod 2 (by omega) 2 (by omega)).const_mul 6) |>.add
      ((hprod 1 (by omega) 3 (by omega)).const_mul 4)) (hYp 4 le_rfl)]
  erw [integral_add (((hXp 4 le_rfl).add ((hprod 3 (by omega) 1 (by omega)).const_mul 4)).add
      ((hprod 2 (by omega) 2 (by omega)).const_mul 6))
      ((hprod 1 (by omega) 3 (by omega)).const_mul 4)]
  erw [integral_add ((hXp 4 le_rfl).add ((hprod 3 (by omega) 1 (by omega)).const_mul 4))
      ((hprod 2 (by omega) 2 (by omega)).const_mul 6)]
  erw [integral_add (hXp 4 le_rfl) ((hprod 3 (by omega) 1 (by omega)).const_mul 4)]
  simp only [integral_const_mul]
  rw [(hind 3 1).integral_fun_mul_eq_mul_integral (hXp 3 (by omega)).aestronglyMeasurable
      (hYp 1 (by omega)).aestronglyMeasurable,
    (hind 2 2).integral_fun_mul_eq_mul_integral (hXp 2 (by omega)).aestronglyMeasurable
      (hYp 2 (by omega)).aestronglyMeasurable,
    (hind 1 3).integral_fun_mul_eq_mul_integral (hXp 1 (by omega)).aestronglyMeasurable
      (hYp 3 (by omega)).aestronglyMeasurable]
  simp only [pow_one, hX0, hY0, mul_zero, zero_mul, add_zero]
  ring


lemma independent_sum_fourth_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, Measurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ) (n : ℕ) :
    (∫ ω, (∑ k ∈ Finset.range n, X k ω)^4 ∂μ) ≤
      (n : ℝ) * κ + 3 * (n : ℝ)^2 * v^2 := by
  have hX₂ : ∀ k, MemLp (X k) 2 μ := fun k => (hX₄ k).mono_exponent (by norm_num)
  induction n with
  | zero => simp
  | succ n ih =>
    have hS₄ : MemLp (fun ω => ∑ k ∈ Finset.range n, X k ω) 4 μ :=
      memLp_finsetSum _ (fun k _ => hX₄ k)
    have hS0 : (∫ ω, ∑ k ∈ Finset.range n, X k ω ∂μ) = 0 := by
      rw [integral_finsetSum _ (fun k _ => (hX₄ k).integrable (by norm_num))]
      simp only [hzero, Finset.sum_const_zero]
    have hSInd : IndepFun (fun ω => ∑ k ∈ Finset.range n, X k ω) (X n) μ := by
      convert hX.indepFun_finsetSum_of_notMem hXm
        (s := Finset.range n) (i := n) (by simp) using 1
      all_goals try with_reducible_and_instances rfl
      ext ω
      simp
    have hS₂ : (∫ ω, (∑ k ∈ Finset.range n, X k ω)^2 ∂μ) ≤ (n : ℝ) * v := by
      rw [independent_sum_second_moment X hX₂ hX hzero]
      exact (Finset.sum_le_sum (fun k _ => hvar k)).trans_eq (by simp)
    have hmul : (∫ ω, (∑ k ∈ Finset.range n, X k ω)^2 ∂μ) *
        (∫ ω, (X n ω)^2 ∂μ) ≤ (n : ℝ) * v^2 := by
      have h := mul_le_mul hS₂ (hvar n) (integral_nonneg (fun _ => sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg n) hv)
      simpa only [pow_two, mul_assoc] using h
    simp only [Finset.sum_range_succ]
    rw [independent_add_fourth_moment hSInd hS₄ (hX₄ n) hS0 (hzero n)]
    push_cast
    nlinarith [hfour n, sq_nonneg v]


lemma martingale_fourth_submartingale {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ι ‹MeasurableSpace Ω›}
    {f : ι → Ω → ℝ} (hf : Martingale f ℱ μ)
    (h₄ : ∀ i, Integrable (fun ω => (f i ω)^4) μ) :
    Submartingale (fun i ω => (f i ω)^4) ℱ μ := by
  refine ⟨fun i => (hf.stronglyMeasurable i).pow 4, ?_, h₄⟩
  intro i j hij
  have hj := ((show Even (4:ℕ) by norm_num).convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ
    (ℱ.le i) (continuous_pow 4).lowerSemicontinuous (hf.integrable j) (h₄ j)
  filter_upwards [hj, hf.condExp_ae_eq hij] with ω hJ hM
  simpa only [Function.comp_def, hM] using hJ


lemma martingale_maximal_fourth_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ μ)
    (h₄ : ∀ i, Integrable (fun ω => (f i ω)^4) μ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |f k ω|} ≤ (∫ ω, (f n ω)^4 ∂μ) / ε^4 := by
  let g := fun i ω => (f i ω)^4
  let E := {ω | ε^4 ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one
    (fun k => g k ω)}
  have hmax := maximal_ineq (martingale_fourth_submartingale hf h₄)
    (fun i ω => by positivity) (ε := (⟨ε^4, by positivity⟩ : ℝ≥0)) n
  have hs : {ω | ∃ k ≤ n, ε ≤ |f k ω|} ⊆ E := by
    rintro ω ⟨k, hk, hω⟩
    change ε^4 ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun k => g k ω)
    apply le_trans _ (Finset.le_sup' (fun k => g k ω) (Finset.mem_range.mpr (show k < n+1 by omega)))
    change ε^4 ≤ (f k ω)^4
    simpa only [← abs_pow, abs_of_nonneg (show 0 ≤ (f k ω)^4 by positivity)] using
      pow_le_pow_left₀ hε.le hω 4
  have hi : 0 ≤ ∫ ω in E, (f n ω)^4 ∂μ := integral_nonneg (fun _ => by positivity)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  rw [ENNReal.toReal_mul] at ht
  erw [ENNReal.coe_toReal] at ht
  change ε^4 * (μ E).toReal ≤
    (ENNReal.ofReal (∫ ω in E, (f n ω)^4 ∂μ)).toReal at ht
  rw [ENNReal.toReal_ofReal hi] at ht
  have hwhole : (∫ ω in E, (f n ω)^4 ∂μ) ≤ ∫ ω, (f n ω)^4 ∂μ :=
    setIntegral_le_integral (h₄ n) (ae_of_all μ (fun _ => by positivity))
  apply (le_div_iff₀ (pow_pos hε 4)).mpr
  calc
    _ ≤ μ.real E * ε^4 := mul_le_mul_of_nonneg_right (measureReal_mono hs) (by positivity)
    _ ≤ ∫ ω in E, (f n ω)^4 ∂μ := by simpa [mul_comm, measureReal_def] using ht
    _ ≤ _ := hwhole


lemma independent_sum_maximal_fourth_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |∑ j ∈ Finset.range k, X j ω|} ≤
      ((n : ℝ) * κ + 3 * (n : ℝ)^2 * v^2) / ε^4 := by
  cases n with
  | zero => simp [not_le.mpr hε]
  | succ n =>
    have hmart := independent_sum_martingale X hXm
      (fun k => (hX₄ k).integrable (by norm_num)) hX hzero
    have hmax := martingale_maximal_fourth_bound hmart
      (fun m => memLp_integrable_pow_le (p := 4)
        (memLp_finsetSum (Finset.range (m+1)) (fun k _ => hX₄ k)) le_rfl) n hε
    apply le_trans (measureReal_mono ?_) (hmax.trans ?_)
    · rintro ω ⟨k, hk, hω⟩
      cases k with
      | zero => simp only [Finset.range_zero, Finset.sum_empty, abs_zero] at hω
                exact (not_le.mpr hε hω).elim
      | succ k => exact ⟨k, by omega, hω⟩
    · exact div_le_div_of_nonneg_right (independent_sum_fourth_moment_bound X
        (fun k => (hXm k).measurable) hX₄ hX hzero hv hvar hfour (n+1)) (by positivity)


lemma block_maximal_fourth_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ) (B L : ℕ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ b < B, ∃ k ≤ L,
      ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X (b*L+j) ω|} ≤
      (B : ℝ) * ((L : ℝ) * κ + 3 * (L : ℝ)^2 * v^2) / (ε^4 * (n : ℝ)^2) := by
  let E := fun b => {ω | ∃ k ≤ L,
    ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X (b*L+j) ω|}
  have hE : {ω | ∃ b < B, ∃ k ≤ L,
      ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X (b*L+j) ω|} =
      ⋃ b ∈ Finset.range B, E b := by ext ω; simp [E]
  rw [hE]
  apply (measureReal_biUnion_finset_le (Finset.range B) E).trans
  have hb : ∀ b, μ.real (E b) ≤
      ((L : ℝ) * κ + 3 * (L : ℝ)^2 * v^2) / (ε^4 * (n : ℝ)^2) := by
    intro b
    have hind := hX.precomp (g := fun j => b*L+j) (fun _ _ hjk => Nat.add_left_cancel hjk)
    have ht := independent_sum_maximal_fourth_bound (fun j => X (b*L+j))
      (fun j => hXm _) (fun j => hX₄ _) hind (fun j => hzero _) hv
      (fun j => hvar _) (fun j => hfour _) L
      (mul_pos hε (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)))
    have hs : (Real.sqrt (n : ℝ))^4 = (n : ℝ)^2 := by
      rw [show 4 = 2*2 by norm_num, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n)]
    simpa only [mul_pow, hs] using ht
  exact (Finset.sum_le_sum (fun b _ => hb b)).trans_eq (by simp [mul_div_assoc])


lemma block_oscillation_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v) (hκ : 0 ≤ κ)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ)
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ b < m+1, ∃ k ≤ n/m+1,
      ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X (b*(n/m+1)+j) ω|} ≤
      (4*κ + 24*v^2) / (ε^4 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (hm.trans_le hmn)
  have hmnR : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have hL : ((n/m+1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) / m := by
    push_cast
    have hdiv : (1:ℝ) ≤ (n:ℝ)/m := (le_div_iff₀ hmR).mpr (by simpa using hmnR)
    rw [mul_div_assoc]
    linarith [Nat.cast_div_le (m := n) (n := m) (α := ℝ)]
  have hB : ((m+1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    push_cast
    linarith
  have hLL : ((n/m+1 : ℕ) : ℝ)^2 ≤ (2*(n:ℝ)/m)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
  have hbound := block_maximal_fourth_bound X hXm hX₄ hX hzero hv hvar hfour
    (m+1) (n/m+1) (hm.trans_le hmn) hε
  apply hbound.trans
  calc
    _ ≤ (2*(m:ℝ)) * ((2*(n:ℝ)/m)*κ + 3*(2*(n:ℝ)/m)^2*v^2) /
        (ε^4*(n:ℝ)^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul hB
      · exact add_le_add (mul_le_mul_of_nonneg_right hL hκ)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLL (by norm_num))
            (sq_nonneg v))
      · positivity
      · positivity
    _ = 4*κ / (ε^4*(n:ℝ)) + 24*v^2 / (ε^4*(m:ℝ)) := by
      field_simp
      ring
    _ ≤ 4*κ / (ε^4*(m:ℝ)) + 24*v^2 / (ε^4*(m:ℝ)) := by
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hmnR (by positivity))
    _ = _ := by rw [add_div]


lemma tent_sum_eq_one (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hxN : x ≤ N) :
    (∑ i ∈ Finset.range (N+1), max 0 (1 - |x - (i : ℝ)|)) = 1 := by
  induction N with
  | zero => have hx : x = 0 := le_antisymm (by simpa using hxN) hx0
            simp [hx]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hx : x ≤ (N : ℝ)
    · have ht : max 0 (1 - |x - ((N+1 : ℕ) : ℝ)|) = 0 := by
        rw [abs_of_nonpos (by push_cast; linarith), max_eq_left]
        push_cast
        linarith
      rw [ht, add_zero]
      exact ih hx
    · have hx1 : (N : ℝ) < x := lt_of_not_ge hx
      have hsum : (∑ i ∈ Finset.range (N+1), max 0 (1 - |x - (i : ℝ)|)) =
          max 0 (1 - |x - (N : ℝ)|) := by
        apply Finset.sum_eq_single N
        · intro i hi hiN
          have hi' : i < N := by simp only [Finset.mem_range] at hi; omega
          have hiR : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi'
          rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
        · simp
      rw [hsum, abs_of_nonneg (by linarith), max_eq_right (by push_cast at hxN; linarith),
        abs_of_nonpos (by push_cast at hxN ⊢; linarith),
        max_eq_right (by push_cast; linarith)]
      push_cast
      ring


lemma hat_nonneg (N i : ℕ) (t : unitInterval) : 0 ≤ hat N i t := le_max_left _ _


lemma hat_sum (N : ℕ) (t : unitInterval) : (∑ i : Fin (N+1), hat N i.val t) = 1 := by
  have hx0 : 0 ≤ (N : ℝ) * (t : ℝ) := mul_nonneg (Nat.cast_nonneg N) t.property.1
  have hxN : (N : ℝ) * (t : ℝ) ≤ N := by nlinarith [t.property.2, Nat.cast_nonneg N (α := ℝ)]
  change (∑ i : Fin (N+1), (fun j : ℕ => max 0 (1 - |(N : ℝ) * (t : ℝ) - j|)) i.val) = 1
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => max 0 (1 - |(N : ℝ) * (t : ℝ) - j|)) (N+1)).trans
    (tent_sum_eq_one N hx0 hxN)


lemma hat_support {N i : ℕ} {t : unitInterval} (h : hat N i t ≠ 0) :
    |(N : ℝ) * (t : ℝ) - i| < 1 := by
  change max 0 (1 - |(N : ℝ) * (t : ℝ) - i|) ≠ 0 at h
  have hh : 0 < max 0 (1 - |(N : ℝ) * (t : ℝ) - i|) :=
    lt_of_le_of_ne (le_max_left _ _) (Ne.symm h)
  rw [lt_max_iff] at hh
  rcases hh with hh | hh
  · exact (lt_irrefl _ hh).elim
  · linarith


lemma interpolation_apply (N : ℕ) (a : Fin (N+1) → ℝ) (t : unitInterval) :
    interpolation N a t = ∑ i : Fin (N+1), a i * hat N i.val t := by
  simp [interpolation]


lemma interpolation_sub_const_bound (N : ℕ) (a : Fin (N+1) → ℝ) (t : unitInterval)
    {c M : ℝ} (h : ∀ i : Fin (N+1), hat N i.val t ≠ 0 → |a i - c| ≤ M) :
    |interpolation N a t - c| ≤ M := by
  have heq : interpolation N a t - c =
      ∑ i : Fin (N+1), (a i - c) * hat N i.val t := by
    rw [interpolation_apply]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hat_sum, mul_one]
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i : Fin (N+1), M * hat N i.val t := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : hat N i.val t = 0
      · simp [hi]
      · rw [abs_mul, abs_of_nonneg (hat_nonneg N i.val t)]
        exact mul_le_mul_of_nonneg_right (h i hi) (hat_nonneg N i.val t)
    _ = M := by rw [← Finset.mul_sum, hat_sum, mul_one]


lemma interpolation_two_point_bound (N : ℕ) (a : Fin (N+1) → ℝ)
    (s t : unitInterval) {M : ℝ}
    (h : ∀ i j : Fin (N+1), hat N i.val s ≠ 0 → hat N j.val t ≠ 0 → |a i - a j| ≤ M) :
    |interpolation N a s - interpolation N a t| ≤ M := by
  apply interpolation_sub_const_bound
  intro i hi
  rw [abs_sub_comm]
  apply interpolation_sub_const_bound
  intro j hj
  rw [abs_sub_comm]
  exact h i j hi hj


lemma interpolation_diff_bound (N : ℕ) (a b : Fin (N+1) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ i, |a i - b i| ≤ M) :
    ‖interpolation N a - interpolation N b‖ ≤ M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro t
  change |interpolation N a t - interpolation N b t| ≤ M
  have heq : interpolation N a t - interpolation N b t =
      interpolation N (fun i => a i - b i) t := by
    simp only [interpolation_apply, sub_mul, Finset.sum_sub_distrib]
  rw [heq]
  simpa only [sub_zero] using interpolation_sub_const_bound N (fun i => a i - b i) t
    (c := 0) (fun i _ => by simpa only [sub_zero] using h i)


lemma block_anchor_bound (S : ℕ → ℝ) {B L : ℕ} {A : ℝ}
    (h : ∀ b < B, ∀ k ≤ L, |S (b*L+k) - S (b*L)| ≤ A)
    (b d : ℕ) (hbd : b+d ≤ B) :
    |S ((b+d)*L) - S (b*L)| ≤ (d : ℝ) * A := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hc := h (b+d) (by omega) L le_rfl
    have heq : (b+(d+1))*L = (b+d)*L+L := by ring
    have ht := (abs_sub_le (S ((b+(d+1))*L)) (S ((b+d)*L)) (S (b*L))).trans
      (add_le_add (by simpa only [heq] using hc) (ih (by omega)))
    calc
      _ ≤ A+(d : ℝ)*A := ht
      _ = ((d+1 : ℕ) : ℝ)*A := by push_cast; ring


lemma block_grid_bound (S : ℕ → ℝ) {B L : ℕ} (hL : 0 < L) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ b < B, ∀ k ≤ L, |S (b*L+k) - S (b*L)| ≤ A)
    {i j D : ℕ} (hij : i ≤ j) (hj : j/L < B) (hD : j/L-i/L ≤ D) :
    |S i - S j| ≤ ((D : ℝ)+2) * A := by
  have hib : i/L ≤ j/L := Nat.div_le_div_right hij
  have hia := h (i/L) (hib.trans_lt hj) (i%L) (Nat.mod_lt i hL).le
  have hja := h (j/L) hj (j%L) (Nat.mod_lt j hL).le
  rw [Nat.mul_comm (i/L) L, Nat.div_add_mod, Nat.mul_comm L (i/L)] at hia
  rw [Nat.mul_comm (j/L) L, Nat.div_add_mod, Nat.mul_comm L (j/L)] at hja
  have hd : i/L+(j/L-i/L) = j/L := Nat.add_sub_of_le hib
  have hba := block_anchor_bound S h (i/L) (j/L-i/L) (by omega)
  rw [hd, abs_sub_comm] at hba
  have ht := (abs_sub_le (S i) (S ((i/L)*L)) (S j)).trans
    (add_le_add hia ((abs_sub_le (S ((i/L)*L)) (S ((j/L)*L)) (S j)).trans
      (add_le_add hba (by simpa only [abs_sub_comm] using hja))))
  have hDR : ((j/L-i/L : ℕ) : ℝ) ≤ D := Nat.cast_le.mpr hD
  nlinarith [mul_le_mul_of_nonneg_right hDR hA]


lemma div_diff_le_two {i j L : ℕ} (hL : 0 < L) (_hij : i ≤ j)
    (hijL : j ≤ i+2*L) : j/L-i/L ≤ 2 := by
  have hmod := Nat.mod_lt i hL
  have hrep := Nat.div_add_mod i L
  have hjb : j < (i/L+3)*L := by nlinarith
  have hd := (Nat.div_lt_iff_lt_mul hL).mpr hjb
  omega


lemma interpolation_block_modulus (S : ℕ → ℝ) {N B L : ℕ} (hL : 0 < L)
    (hNB : N/L < B) {A δ : ℝ} (hA : 0 ≤ A)
    (hδ : (N : ℝ)*δ+2 ≤ 2*(L : ℝ))
    (h : ∀ b < B, ∀ k ≤ L, |S (b*L+k) - S (b*L)| ≤ A)
    (s t : unitInterval) (hst : dist s t ≤ δ) :
    |interpolation N (fun i => S i.val) s - interpolation N (fun i => S i.val) t| ≤ 4*A := by
  apply interpolation_two_point_bound
  intro i j hi hj
  have hi' := hat_support hi
  have hj' := hat_support hj
  have hmid : |(N : ℝ)*(s : ℝ)-(N : ℝ)*(t : ℝ)| ≤ (N : ℝ)*δ := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    exact mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N)
  have hclose : |(i.val : ℝ)-(j.val : ℝ)| ≤ 2*(L : ℝ) := by
    have htri := (abs_sub_le (i.val : ℝ) ((N : ℝ)*(s : ℝ)) (j.val : ℝ)).trans
      (add_le_add le_rfl (abs_sub_le ((N : ℝ)*(s : ℝ)) ((N : ℝ)*(t : ℝ)) (j.val : ℝ)))
    rw [abs_sub_comm (i.val : ℝ) ((N : ℝ)*(s : ℝ))] at htri
    linarith
  have hiB : i.val/L < B := (Nat.div_le_div_right (show i.val ≤ N by omega)).trans_lt hNB
  have hjB : j.val/L < B := (Nat.div_le_div_right (show j.val ≤ N by omega)).trans_lt hNB
  rcases le_total i.val j.val with hij | hji
  · have hijL : j.val ≤ i.val+2*L := by
      have hh := (abs_le.mp hclose).1
      have hr : (j.val : ℝ) ≤ (i.val : ℝ)+2*(L : ℝ) := by linarith
      exact_mod_cast hr
    simpa only [Nat.cast_ofNat, show (2:ℝ)+2=4 by norm_num] using
      block_grid_bound S hL hA h hij hjB (div_diff_le_two hL hij hijL)
  · rw [abs_sub_comm]
    have hjiL : i.val ≤ j.val+2*L := by
      have hh := (abs_le.mp hclose).2
      have hr : (i.val : ℝ) ≤ (j.val : ℝ)+2*(L : ℝ) := by linarith
      exact_mod_cast hr
    simpa only [Nat.cast_ofNat, show (2:ℝ)+2=4 by norm_num] using
      block_grid_bound S hL hA h hji hiB (div_diff_le_two hL hji hjiL)


lemma measurable_tailValue (R : ℝ) : Measurable (tailValue R) := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
    measurable_id measurable_const


lemma tailValue_sq_le (R x : ℝ) : (tailValue R x)^2 ≤ x^2 := by
  unfold tailValue
  split_ifs <;> simp [sq_nonneg]


lemma tailValue_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    MemLp (fun ω => tailValue R (X ω)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_tailValue R).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable).mpr
  refine hX.integrable_sq.mono'
    (((measurable_tailValue R).comp_aemeasurable hX.aemeasurable).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_sq]
  exact tailValue_sq_le R (X ω)


lemma centeredTail_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    MemLp (centeredTail μ X R) 2 μ :=
  (tailValue_memLp hX R).sub (memLp_const _)


@[simp] lemma centeredTail_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    (∫ ω, centeredTail μ X R ω ∂μ) = 0 := by
  simp only [centeredTail, integral_sub ((tailValue_memLp hX R).integrable (by norm_num))
    (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]


lemma centeredTail_second_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    (∫ ω, (centeredTail μ X R ω)^2 ∂μ) ≤ ∫ ω, (tailValue R (X ω))^2 ∂μ := by
  rw [← variance_of_integral_eq_zero (centeredTail_memLp hX R).aemeasurable
    (centeredTail_integral hX R)]
  change Var[fun ω => tailValue R (X ω) - ∫ z, tailValue R (X z) ∂μ; μ] ≤ _
  rw [variance_sub_const (tailValue_memLp hX R).aestronglyMeasurable,
    variance_eq_sub (tailValue_memLp hX R)]
  exact sub_le_self _ (sq_nonneg _)


lemma tail_second_moment_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Tendsto (fun R : ℕ => ∫ ω, (tailValue R (X ω))^2 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun ω => (X ω)^2)
    (F := fun R : ℕ => fun ω => (tailValue R (X ω))^2) (f := fun _ => 0)
    (fun R => ((tailValue_memLp hX R).integrable_sq).aestronglyMeasurable)
    hX.integrable_sq
    (fun R => ae_of_all μ (fun ω => by
      simpa only [Real.norm_eq_abs, abs_sq] using tailValue_sq_le R (X ω)))
    (ae_of_all μ (fun ω => by
      obtain ⟨N, hN⟩ := exists_nat_gt |X ω|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with R hR
      have hRX : ¬ (R : ℝ) < |X ω| := by exact not_lt.mpr (hN.le.trans (Nat.cast_le.mpr hR))
      simp [tailValue, hRX]))
  simpa only [integral_zero] using h


lemma head_abs_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |x - tailValue R x| ≤ R := by
  unfold tailValue
  split_ifs with h
  · simpa using hR
  · simpa using not_lt.mp h


lemma centeredHead_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (ω : Ω) :
    |centeredHead μ X R ω| ≤ 2 * R := by
  have hm : |∫ z, X z - tailValue R (X z) ∂μ| ≤ R := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (ae_of_all μ (fun z =>
        show ‖X z - tailValue R (X z)‖ ≤ R from head_abs_le hR (X z)))
  exact (abs_sub _ _).trans (by linarith [head_abs_le hR (X ω)])


lemma centered_head_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (R : ℝ) (ω : Ω) :
    centeredHead μ X R ω + centeredTail μ X R ω = X ω := by
  unfold centeredHead centeredTail
  rw [integral_sub (hX.integrable (by norm_num))
    ((tailValue_memLp hX R).integrable (by norm_num)), hX0]
  ring


lemma independent_sum_scaled_maximal_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₂ : ∀ k, MemLp (X k) 2 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {δ : ℝ} (hδ : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ δ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X j ω|} ≤
      δ / ε^2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : (∑ j ∈ Finset.range n, ∫ ω, (X j ω)^2 ∂μ) ≤ (n : ℝ) * δ := by
    exact (Finset.sum_le_sum (fun j _ => hδ j)).trans_eq (by simp)
  apply (independent_sum_maximal_bound X hXm hX₂ hX hzero n
    (mul_pos hε (Real.sqrt_pos.mpr hnR))).trans
  apply (div_le_div_of_nonneg_right hs (sq_nonneg _)).trans_eq
  rw [mul_pow, Real.sq_sqrt hnR.le]
  field_simp


lemma independent_centeredTail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : iIndepFun X μ) (R : ℝ) :
    iIndepFun (fun k => centeredTail μ (X k) R) μ := by
  exact hX.comp (fun k x => tailValue R x - ∫ z, tailValue R (X k z) ∂μ)
    (fun k => (measurable_tailValue R).sub measurable_const)


lemma scaledWalk_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (n : ℕ) :
    @Measurable Ω C(unitInterval, ℝ) _ (borel _) (scaledWalk X n) := by
  let : MeasurableSpace C(unitInterval, ℝ) := borel _
  let : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩
  unfold scaledWalk interpolation
  apply Finset.measurable_sum
  intro i _
  exact ((Finset.measurable_sum _ (fun j _ => hXm j)).div_const _).smul_const _


lemma sum_range_block (S : ℕ → ℝ) (b L k : ℕ) :
    (∑ j ∈ Finset.range (b*L+k), S j) - (∑ j ∈ Finset.range (b*L), S j) =
      ∑ j ∈ Finset.range k, S (b*L+j) := by
  rw [Finset.sum_range_add]
  ring


lemma grid_blocks_parameters {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    n/(n/m+1) < m+1 ∧ (n : ℝ)*(1/(m : ℝ))+2 ≤ 2*((n/m+1 : ℕ) : ℝ) := by
  have hq : 1 ≤ n/m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hmn)
  have hrep := Nat.div_add_mod n m
  have hmod := Nat.mod_lt n hm
  have hn : n < (n/m+1)*m := by nlinarith
  constructor
  · exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr (by nlinarith)
  · have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hnR : (n : ℝ) < ((n/m : ℕ) : ℝ)*(m : ℝ)+(m : ℝ) := by exact_mod_cast (show n < (n/m)*m+m by nlinarith [hn])
    have hdiv : (n : ℝ)/(m : ℝ) < ((n/m : ℕ) : ℝ)+1 :=
      (div_lt_iff₀ hmR).mpr (by linarith)
    have hqR : (1 : ℝ) ≤ ((n/m : ℕ) : ℝ) := by exact_mod_cast hq
    push_cast
    rw [mul_one_div]
    linarith


lemma scaledWalk_modulus_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v) (hκ : 0 ≤ κ)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ)
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ s t : unitInterval, dist s t ≤ 1/(m : ℝ) ∧
      4*ε < |scaledWalk X n ω s - scaledWalk X n ω t|} ≤
      (4*κ+24*v^2)/(ε^4*(m : ℝ)) := by
  classical
  apply le_trans (measureReal_mono ?_) (block_oscillation_bound X hXm hX₄ hX hzero
    hv hκ hvar hfour hm hmn hε)
  rintro ω ⟨s,t,hst,hbad⟩
  by_contra hnone
  simp only [mem_ofPred_eq] at hnone
  push Not at hnone
  have hb : ∀ b < m+1, ∀ k ≤ n/m+1,
      |(∑ j ∈ Finset.range (b*(n/m+1)+k), X j ω)/Real.sqrt n -
       (∑ j ∈ Finset.range (b*(n/m+1)), X j ω)/Real.sqrt n| ≤ ε := by
    intro b hb k hk
    rw [← sub_div, sum_range_block, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hm.trans_le hmn)))).mpr
      ((hnone b hb k hk).le)
  have hp := grid_blocks_parameters hm hmn
  have hgood := interpolation_block_modulus
    (fun i => (∑ j ∈ Finset.range i, X j ω)/Real.sqrt n)
    (Nat.succ_pos _) hp.1 hε.le hp.2 hb s t hst
  exact (not_lt_of_ge hgood) hbad


lemma scaledWalk_maximal_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₂ : ∀ k, MemLp (X k) 2 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v : ℝ} (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε < ‖scaledWalk X n ω‖} ≤ v/ε^2 := by
  classical
  apply le_trans (measureReal_mono ?_)
    (independent_sum_scaled_maximal_bound X hXm hX₂ hX hzero hvar hn hε)
  intro ω hω
  by_contra hnone
  simp only [mem_ofPred_eq] at hnone
  push Not at hnone
  have hbound : ‖scaledWalk X n ω‖ ≤ ε := by
    apply (ContinuousMap.norm_le _ hε.le).mpr
    intro t
    change |scaledWalk X n ω t| ≤ ε
    have h := interpolation_sub_const_bound n
      (fun i => (∑ j ∈ Finset.range i.val, X j ω)/Real.sqrt n) t (c := 0) (M := ε)
    simp only [sub_zero] at h
    apply h
    intro i _
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).mpr
    exact (hnone i.val (by omega)).le
  exact (not_lt_of_ge hbound) hω


lemma centeredHead_measurable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X) (R : ℝ) : Measurable (centeredHead μ X R) :=
  (hX.sub ((measurable_tailValue R).comp hX)).sub measurable_const


lemma centeredHead_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {R : ℝ} (hR : 0 ≤ R) (p : ℝ≥0∞) : MemLp (centeredHead μ X R) p μ :=
  MemLp.of_bound (centeredHead_measurable μ hX R).aestronglyMeasurable (2*R)
    (ae_of_all μ (fun ω => centeredHead_abs_le X hR ω))


lemma centeredHead_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    (∫ ω, centeredHead μ X R ω ∂μ) = 0 := by
  simp only [centeredHead]
  have hi : Integrable (fun ω => X ω-tailValue R (X ω)) μ :=
    (hX.sub (tailValue_memLp hX R)).integrable (by norm_num)
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]


lemma centeredHead_moment_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    (∫ ω, (centeredHead μ X R ω)^j ∂μ) ≤ (2*R)^j := by
  apply (le_abs_self _).trans
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => (centeredHead μ X R ω)^j)
    (ae_of_all μ (fun ω => by
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (centeredHead_abs_le X hR ω) j))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h


lemma independent_centeredHead {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : iIndepFun X μ) (R : ℝ) :
    iIndepFun (fun k => centeredHead μ (X k) R) μ :=
  hX.comp (fun k x => (x-tailValue R x) - ∫ z, X k z-tailValue R (X k z) ∂μ)
    (fun _ => (measurable_id.sub (measurable_tailValue R)).sub measurable_const)


lemma scaledWalk_add {Ω : Type*} (X Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    scaledWalk (X+Y) n ω = scaledWalk X n ω + scaledWalk Y n ω := by
  ext t
  simp only [scaledWalk, interpolation_apply, Pi.add_apply, Finset.sum_add_distrib,
    add_div, add_mul, ContinuousMap.add_apply]


lemma scaledWalk_head_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, MemLp (X k) 2 μ)
    (hX0 : ∀ k, ∫ ω, X k ω ∂μ = 0) (R : ℝ) (n : ℕ) (ω : Ω) :
    scaledWalk (fun k => centeredHead μ (X k) R) n ω +
      scaledWalk (fun k => centeredTail μ (X k) R) n ω = scaledWalk X n ω := by
  rw [← scaledWalk_add]
  congr 2
  funext k ω
  exact centered_head_tail (hX k) (hX0 k) R ω


lemma path_modulus_add_le (f g : C(unitInterval, ℝ)) (s t : unitInterval) :
    |(f+g) s-(f+g) t| ≤ |f s-f t|+2*‖g‖ := by
  have hs := g.norm_coe_le_norm s
  have ht := g.norm_coe_le_norm t
  have h := abs_add_le (f s-f t) (g s-g t)
  simp only [ContinuousMap.add_apply, Real.norm_eq_abs] at *
  have heq : f s+g s-(f t+g t) = (f s-f t)+(g s-g t) := by ring
  rw [heq]
  exact h.trans (by linarith [abs_sub (g s) (g t)])


lemma finiteVariance_scaledWalk_modulus_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, Measurable (X k)) (hX₂ : ∀ k, MemLp (X k) 2 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {R v : ℝ} (hR : 0 ≤ R)
    (htail : ∀ k, ∫ ω, (tailValue R (X k ω))^2 ∂μ ≤ v)
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ s t : unitInterval, dist s t ≤ 1/(m : ℝ) ∧
      6*ε < |scaledWalk X n ω s-scaledWalk X n ω t|} ≤
      (4*(2*R)^4+24*((2*R)^2)^2)/(ε^4*(m : ℝ))+v/ε^2 := by
  let H := fun k => centeredHead μ (X k) R
  let T := fun k => centeredTail μ (X k) R
  have hH := scaledWalk_modulus_bound H
    (fun k => (centeredHead_measurable μ (hXm k) R).stronglyMeasurable)
    (fun k => centeredHead_memLp (hXm k) hR 4) (independent_centeredHead X hX R)
    (fun k => centeredHead_integral (hX₂ k) R) (sq_nonneg _) (by positivity)
    (fun k => centeredHead_moment_bound (X k) hR 2)
    (fun k => centeredHead_moment_bound (X k) hR 4) hm hmn hε
  have hT := scaledWalk_maximal_bound T
    (fun k => (((measurable_tailValue R).comp (hXm k)).sub measurable_const).stronglyMeasurable)
    (fun k => centeredTail_memLp (hX₂ k) R) (independent_centeredTail X hX R)
    (fun k => centeredTail_integral (hX₂ k) R)
    (fun k => (centeredTail_second_moment_le (hX₂ k) R).trans (htail k))
    (hm.trans_le hmn) hε
  apply le_trans (measureReal_mono ?_) ((measureReal_union_le _ _).trans (add_le_add hH hT))
  rintro ω ⟨s,t,hst,hbad⟩
  by_cases hh : 4*ε < |scaledWalk H n ω s-scaledWalk H n ω t|
  · exact Or.inl ⟨s,t,hst,hh⟩
  · apply Or.inr
    by_contra ht
    have hnorm : ‖scaledWalk T n ω‖ ≤ ε := not_lt.mp ht
    have hp := path_modulus_add_le (scaledWalk H n ω) (scaledWalk T n ω) s t
    rw [scaledWalk_head_tail X hX₂ hzero R] at hp
    linarith [not_lt.mp hh]


theorem iid_scaledWalk_modulus {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, Measurable (X k)) (hX₂ : MemLp (X 0) 2 μ)
    (hX : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hzero : ∫ ω, X 0 ω ∂μ = 0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ m : ℕ, 0 < m ∧ ∀ n ≥ m,
      μ.real {ω | ∃ s t : unitInterval, dist s t ≤ 1/(m : ℝ) ∧
        ε < |scaledWalk X n ω s-scaledWalk X n ω t|} ≤ η := by
  let e := ε/6
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨R, hR⟩ := ((tail_second_moment_tendsto_zero hX₂).eventually
    (gt_mem_nhds (show (0:ℝ) < η/2*e^2 by positivity))).exists
  let v := ∫ ω, (tailValue (R : ℝ) (X 0 ω))^2 ∂μ
  have hv : v/e^2 ≤ η/2 := (div_le_iff₀ (sq_pos_of_pos he)).mpr hR.le
  let c := 4*(2*(R : ℝ))^4+24*((2*(R : ℝ))^2)^2
  have hc : Tendsto (fun m : ℕ => c/(e^4*(m : ℝ))) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div] using
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)) :
        Tendsto (fun m : ℕ => (c/e^4)/(m : ℝ)) atTop (𝓝 0))
  obtain ⟨m, hm, hcm⟩ := (eventually_gt_atTop 0 |>.and
    (hc.eventually (gt_mem_nhds (half_pos hη)))).exists
  refine ⟨m,hm,fun n hmn => ?_⟩
  have hb := finiteVariance_scaledWalk_modulus_bound X hXm
    (fun k => (hident k).memLp_iff.mpr hX₂) hX
    (fun k => (hident k).integral_eq.trans hzero) (Nat.cast_nonneg R)
    (fun k => le_of_eq ((hident k).comp ((measurable_tailValue (R : ℝ)).pow_const 2)).integral_eq)
    hm hmn he
  have heq : 6*e = ε := by dsimp [e]; ring
  rw [heq] at hb
  exact hb.trans (by change c/(e^4*(m:ℝ))+v/e^2 ≤ η; linarith)


lemma continuous_interpolation (N : ℕ) : Continuous (interpolation N) := by
  unfold interpolation
  fun_prop


lemma continuous_pathApprox (N : ℕ) : Continuous (pathApprox N) := by
  apply (continuous_interpolation N).comp
  exact continuous_pi (fun i => continuous_eval_const (gridPoint N i))


lemma hat_gridPoint_dist {N : ℕ} (hN : 0 < N) (i : Fin (N+1)) (t : unitInterval)
    (hi : hat N i.val t ≠ 0) : dist (gridPoint N i) t < 1/(N : ℝ) := by
  have hh := hat_support hi
  change |(i.val:ℝ)/(N:ℝ)-(t:ℝ)| < 1/(N:ℝ)
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  rw [div_sub', abs_div, abs_of_pos hNR, div_lt_div_iff_of_pos_right hNR]
  · simpa only [abs_sub_comm, mul_comm] using hh
  · exact hNR.ne'


lemma pathApprox_error_le {N : ℕ} (hN : 0 < N) (f : C(unitInterval, ℝ))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ s t : unitInterval, dist s t ≤ 1/(N : ℝ) → |f s-f t| ≤ ε) :
    ‖pathApprox N f-f‖ ≤ ε := by
  apply (ContinuousMap.norm_le _ hε).mpr
  intro t
  change |interpolation N (fun i => f (gridPoint N i)) t-f t| ≤ ε
  exact interpolation_sub_const_bound _ _ _ (fun i hi => hf _ _ (hat_gridPoint_dist hN i t hi).le)


lemma pathApprox_tendsto (f : C(unitInterval, ℝ)) : Tendsto (fun N => pathApprox N f) atTop (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hu := CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hu (ε/2) (by positivity)
  have ht : Tendsto (fun N : ℕ => 1/(N:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_gt_atTop 0, ht.eventually (gt_mem_nhds hδ)] with N hN hNd
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (pathApprox_error_le hN f (by positivity : 0 ≤ ε/2) ?_) (half_lt_self hε)
  intro s t hst
  exact (hd (hst.trans_lt hNd)).le


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_PathCLT
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions
lemma pathApprox_random_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → C(unitInterval, ℝ))
    (hX : AEMeasurable X μ) :
    TendstoInMeasure μ (fun N ω => pathApprox N (X ω)) atTop X := by
  let : MeasurableSpace C(unitInterval, ℝ) := borel _
  let : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩
  apply tendstoInMeasure_of_tendsto_ae
  · intro N
    exact ((continuous_pathApprox N).measurable.comp_aemeasurable hX).aestronglyMeasurable
  · exact ae_of_all μ (fun ω => pathApprox_tendsto (X ω))

lemma hat_gridPoint {N : ℕ} (hN : 0 < N) (i j : Fin (N+1)) :
    hat N j.val (gridPoint N i) = if i = j then 1 else 0 := by
  have hNR : (N:ℝ) ≠ 0 := by positivity
  change max 0 (1-|(N:ℝ)*((i.val:ℝ)/(N:ℝ))-(j.val:ℝ)|) = _
  rw [mul_div_cancel₀ _ hNR]
  split_ifs with hij
  · subst j
    simp
  · have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hab : 1 ≤ |(i.val:ℝ)-(j.val:ℝ)| := by
      rcases lt_or_gt_of_ne hn with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast Nat.le_of_lt h))]
        have hh : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast h
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast Nat.le_of_lt h))]
        have hh : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast h
        linarith
    exact max_eq_left (by linarith)

lemma interpolation_gridPoint {N : ℕ} (hN : 0 < N) (a : Fin (N+1) → ℝ)
    (i : Fin (N+1)) : interpolation N a (gridPoint N i) = a i := by
  classical
  simp only [interpolation_apply,hat_gridPoint hN]
  simp

lemma coarseWalk_vertex {Ω : Type*} (X : ℕ → Ω → ℝ) (m : ℕ) {n : ℕ} (hn : 0 < n)
    (ω : Ω) (i : Fin (m+1)) :
    (∑ j ∈ Finset.range (i.val*(n/m)), X j ω)/Real.sqrt n =
      scaledWalk X n ω (gridPoint n (coarseIndex m n i)) := by
  symm
  exact interpolation_gridPoint hn _ _

lemma coarse_grid_dist_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (i : Fin (m+1)) :
    dist (gridPoint n (coarseIndex m n i)) (gridPoint m i) ≤ (m:ℝ)/(n:ℝ) := by
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hi : (i.val:ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hil : (i.val:ℝ) ≥ 0 := Nat.cast_nonneg _
  have hr : ((n%m:ℕ):ℝ) ≤ m := by exact_mod_cast (Nat.mod_lt n hm).le
  have hr0 : (0:ℝ) ≤ (n%m:ℕ) := Nat.cast_nonneg _
  have he : (m:ℝ)*((n/m:ℕ):ℝ)+((n%m:ℕ):ℝ) = n := by exact_mod_cast Nat.div_add_mod n m
  change |((i.val*(n/m):ℕ):ℝ)/(n:ℝ)-(i.val:ℝ)/(m:ℝ)| ≤ (m:ℝ)/(n:ℝ)
  rw [Nat.cast_mul,div_sub_div _ _ hnR.ne' hmR.ne',abs_div,abs_of_pos (mul_pos hnR hmR)]
  have hneg : (i.val:ℝ)*((n/m:ℕ):ℝ)*(m:ℝ)-(n:ℝ)*(i.val:ℝ) ≤ 0 := by nlinarith
  rw [abs_of_nonpos hneg, div_le_div_iff₀ (mul_pos hnR hmR) hnR]
  have hp := mul_le_mul hi hr hr0 (Nat.cast_nonneg m)
  have hpN := mul_le_mul_of_nonneg_right hp hnR.le
  have hei := congrArg (fun z : ℝ => (i.val:ℝ)*z*(n:ℝ)) he
  nlinarith

lemma coarseWalk_error_le {Ω : Type*} (X : ℕ → Ω → ℝ) {m n : ℕ}
    (hm : 0 < m) (hn : m*m ≤ n) (ω : Ω) {ε : ℝ} (hε : 0 ≤ ε)
    (hmod : ∀ s t : unitInterval, dist s t ≤ 2/(m:ℝ) →
      |scaledWalk X n ω s-scaledWalk X n ω t| ≤ ε) :
    ‖coarseWalk X m n ω-scaledWalk X n ω‖ ≤ ε := by
  have hn0 : 0 < n := lt_of_lt_of_le (Nat.mul_pos hm hm) hn
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hmn : (m:ℝ)/(n:ℝ) ≤ 1/(m:ℝ) := by
    rw [div_le_div_iff₀ hnR hmR,one_mul]
    exact_mod_cast hn
  apply (ContinuousMap.norm_le _ hε).mpr
  intro t
  change |interpolation m _ t-scaledWalk X n ω t| ≤ ε
  apply interpolation_sub_const_bound
  intro i hi
  rw [coarseWalk_vertex X m hn0 ω i]
  apply hmod
  calc dist (gridPoint n (coarseIndex m n i)) t
      ≤ dist (gridPoint n (coarseIndex m n i)) (gridPoint m i)+dist (gridPoint m i) t := dist_triangle _ _ _
    _ ≤ (m:ℝ)/(n:ℝ)+1/(m:ℝ) := add_le_add (coarse_grid_dist_le hm hn0 i) (hat_gridPoint_dist hm i t hi).le
    _ ≤ 2/(m:ℝ) := by
      calc (m:ℝ)/(n:ℝ)+1/(m:ℝ) ≤ 1/(m:ℝ)+1/(m:ℝ) := add_le_add hmn le_rfl
        _ = 2/(m:ℝ) := by ring

lemma continuous_cumulative (m : ℕ) : Continuous (cumulative m) := by
  apply continuous_pi
  intro i
  unfold cumulative
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

lemma cumulative_nat (m : ℕ) (a : ℕ → ℝ) (i : Fin (m+1)) :
    cumulative m (fun j => a j.val) i = ∑ j ∈ Finset.range i.val, a j := by
  unfold cumulative
  apply Finset.sum_congr rfl
  intro j hj
  exact dite_eq_left (lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.le_of_lt_succ i.isLt))

lemma cumulative_div (m : ℕ) (a : Fin m → ℝ) (c : ℝ) (i : Fin (m+1)) :
    cumulative m (fun j => a j/c) i = cumulative m a i/c := by
  simp only [cumulative, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma sum_range_blocks (f : ℕ → ℝ) (k l : ℕ) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range l, f (i*l+j)) =
      ∑ j ∈ Finset.range (k*l), f j := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ,ih,Nat.succ_mul,Finset.sum_range_add]

lemma cumulative_blocks (m l : ℕ) (f : ℕ → ℝ) (i : Fin (m+1)) :
    cumulative m (fun k => ∑ j : Fin l, f (k.val*l+j.val)) i =
      ∑ j ∈ Finset.range (i.val*l), f j := by
  rw [cumulative_nat m (fun k => ∑ j : Fin l, f (k*l+j.val)) i]
  have hf (k : ℕ) : (∑ j : Fin l, f (k*l+j.val)) = ∑ j ∈ Finset.range l, f (k*l+j) :=
    Fin.sum_univ_eq_sum_range (fun j => f (k*l+j)) l
  simp_rw [hf]
  exact sum_range_blocks f i.val l

lemma coarseWalk_eq_cumulative {Ω : Type*} (X : ℕ → Ω → ℝ) (m n : ℕ) (ω : Ω) :
    interpolation m (cumulative m (fun i => (∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω)/Real.sqrt n)) =
      coarseWalk X m n ω := by
  unfold coarseWalk
  congr 1
  funext i
  rw [cumulative_div,cumulative_blocks m (n/m) (fun j => X j ω) i]

lemma map_uncurry_pi {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → κ → Measure ℝ) [∀ i j, IsProbabilityMeasure (μ i j)] :
    (Measure.pi (fun i => Measure.pi (μ i))).map (fun x (ij : ι×κ) => x ij.1 ij.2) =
      Measure.pi (fun ij : ι×κ => μ ij.1 ij.2) := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (Measurable.of_eval (fun ij =>
    (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))) (.univ_pi hs)]
  have heq : (fun x (ij : ι×κ) => x ij.1 ij.2) ⁻¹' univ.pi s =
      univ.pi (fun i => univ.pi (fun j => s (i,j))) := by
    ext x
    simp
  rw [heq,Measure.pi_pi]
  simp only [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun ij : ι×κ => μ ij.1 ij.2 (s ij))).symm

lemma iIndepFun_uncurry_pi {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] (μ : ι → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ι → κ → Ω → ℝ) (hm : ∀ i j, AEMeasurable (X i j) (μ i))
    (hX : ∀ i, iIndepFun (X i) (μ i)) :
    iIndepFun (fun ij : ι×κ => fun ω : ι → Ω => X ij.1 ij.2 (ω ij.1)) (Measure.pi μ) := by
  have hrow (i) : AEMeasurable (fun ω j => X i j ω) (μ i) :=
    AEMeasurable.of_eval (hm i)
  have hmap : (Measure.pi μ).map (fun ω i j => X i j (ω i)) =
      Measure.pi (fun i => Measure.pi (fun j => (μ i).map (X i j))) := by
    rw [Measure.pi_map_pi (fun i => hrow i)]
    congr 1
    funext i
    exact iIndepFun.map_fun_eq_pi_map (hm i) (hX i)
  have hmflat : ∀ ij : ι×κ, AEMeasurable
      (fun ω : ι → Ω => X ij.1 ij.2 (ω ij.1)) (Measure.pi μ) := fun ij =>
    (hm _ _).comp_quasiMeasurePreserving (measurePreserving_eval μ ij.1).quasiMeasurePreserving
  rw [iIndepFun_iff_map_fun_eq_pi_map hmflat]
  have heq : (fun (ω : ι → Ω) (ij : ι×κ) => X ij.1 ij.2 (ω ij.1)) =
      (fun x (ij : ι×κ) => x ij.1 ij.2) ∘ (fun (ω : ι → Ω) i j => X i j (ω i)) := rfl
  have hrm : AEMeasurable (fun ω : ι → Ω => fun i j => X i j (ω i)) (Measure.pi μ) :=
    AEMeasurable.of_eval (fun i => (hrow i).comp_quasiMeasurePreserving
      (measurePreserving_eval μ i).quasiMeasurePreserving)
  have hflatm : Measurable (fun x : ι → κ → ℝ => fun ij : ι×κ => x ij.1 ij.2) := by fun_prop
  rw [heq, ← AEMeasurable.map_map_of_aemeasurable hflatm.aemeasurable hrm, hmap]
  haveI : ∀ i j, IsProbabilityMeasure ((μ i).map (X i j)) := fun i j => Measure.isProbabilityMeasure_map (hm i j)
  rw [map_uncurry_pi]
  congr 1
  funext ij
  have he := measurePreserving_eval μ ij.1
  change (μ ij.1).map (X ij.1 ij.2) = (Measure.pi μ).map ((X ij.1 ij.2) ∘ Function.eval ij.1)
  have ha : AEMeasurable (X ij.1 ij.2) ((Measure.pi μ).map (Function.eval ij.1)) :=
    he.map_eq.symm ▸ hm ij.1 ij.2
  rw [← AEMeasurable.map_map_of_aemeasurable ha he.measurable.aemeasurable, he.map_eq]

lemma tendstoInDistribution_pi_indep {ι α Ω Ω' : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {l : Filter α} {X : ι → α → Ω → ℝ} {Z : ι → Ω' → ℝ}
    (h : ∀ i, TendstoInDistribution (X i) l (Z i) (fun _ => μ) ν)
    (hX : ∀ n, iIndepFun (fun i => X i n) μ) (hZ : iIndepFun Z ν) :
    TendstoInDistribution (fun n ω i => X i n ω) l (fun ω i => Z i ω) (fun _ => μ) ν := by
  have hm : ∀ n, AEMeasurable (fun ω i => X i n ω) μ :=
    fun n => AEMeasurable.of_eval (fun i => (h i).forall_aemeasurable n)
  have hz : AEMeasurable (fun ω i => Z i ω) ν :=
    AEMeasurable.of_eval (fun i => (h i).aemeasurable_limit)
  refine ⟨hm,hz,?_⟩
  have hp := ProbabilityMeasure.continuous_pi.tendsto
    (fun i => (⟨ν.map (Z i), by first | infer_instance | exact Measure.isProbabilityMeasure_map ((h i).aemeasurable_limit)⟩ :
      ProbabilityMeasure ℝ))
  have ht := hp.comp (tendsto_pi_nhds.mpr (fun i => (h i).tendsto))
  have heq (n : α) : (⟨μ.map (fun ω i => X i n ω),
      by first | infer_instance | exact Measure.isProbabilityMeasure_map (hm n)⟩ : ProbabilityMeasure (ι → ℝ)) =
      ProbabilityMeasure.pi (fun i => (⟨μ.map (X i n),
        by first | infer_instance | exact Measure.isProbabilityMeasure_map ((h i).forall_aemeasurable n)⟩ : ProbabilityMeasure ℝ)) := by
    apply Subtype.ext
    exact iIndepFun.map_fun_eq_pi_map (fun i => (h i).forall_aemeasurable n) (hX n)
  have hzeq : (⟨ν.map (fun ω i => Z i ω), by first | infer_instance | exact Measure.isProbabilityMeasure_map (hz)⟩ :
      ProbabilityMeasure (ι → ℝ)) = ProbabilityMeasure.pi (fun i => (⟨ν.map (Z i),
        by first | infer_instance | exact Measure.isProbabilityMeasure_map ((h i).aemeasurable_limit)⟩ : ProbabilityMeasure ℝ)) := by
    apply Subtype.ext
    exact iIndepFun.map_fun_eq_pi_map (fun i => (h i).aemeasurable_limit) hZ
  simp_rw [heq,hzeq]
  exact ht

lemma identDistrib_pi_indep {ι Ω Ω' : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ι → Ω → ℝ} {Y : ι → Ω' → ℝ}
    (hX : iIndepFun X μ) (hY : iIndepFun Y ν)
    (h : ∀ i, IdentDistrib (X i) (Y i) μ ν) :
    IdentDistrib (fun ω i => X i ω) (fun ω i => Y i ω) μ ν := by
  refine ⟨AEMeasurable.of_eval (fun i => (h i).aemeasurable_fst),
    AEMeasurable.of_eval (fun i => (h i).aemeasurable_snd), ?_⟩
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (h i).aemeasurable_fst) hX,
    iIndepFun.map_fun_eq_pi_map (fun i => (h i).aemeasurable_snd) hY]
  congr 1
  funext i
  exact (h i).map_eq

lemma blockIndex_injective (m l : ℕ) :
    Function.Injective (fun ij : Fin m × Fin l => ij.1.val*l+ij.2.val) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  change i.val*l+j.val = i'.val*l+j'.val at h
  have hii : i.val = i'.val := by
    by_contra hh
    rcases lt_or_gt_of_ne hh with hlt | hgt
    · have hp : (i.val+1)*l ≤ i'.val*l := Nat.mul_le_mul_right l hlt
      nlinarith [j.isLt,j'.isLt]
    · have hp : (i'.val+1)*l ≤ i.val*l := Nat.mul_le_mul_right l hgt
      nlinarith [j.isLt,j'.isLt]
  have hjj : j.val = j'.val := by
    rw [hii] at h
    exact Nat.add_left_cancel h
  exact Prod.ext (Fin.ext hii) (Fin.ext hjj)

lemma identDistrib_iid_blocks {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hm : ∀ k, AEMeasurable (X k) μ) (hind : iIndepFun X μ)
    (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ) (m l : ℕ) :
    IdentDistrib
      (fun ω (i : Fin m) => ∑ j : Fin l, X (i.val*l+j.val) ω)
      (fun ω : Fin m → Ω => fun i => ∑ j : Fin l, X j.val (ω i))
      μ (Measure.pi (fun _ : Fin m => μ)) := by
  have hi₁ : iIndepFun (fun ij : Fin m × Fin l => X (ij.1.val*l+ij.2.val)) μ :=
    hind.precomp (blockIndex_injective m l)
  have hi₂ : iIndepFun (fun ij : Fin m × Fin l => fun ω : Fin m → Ω => X ij.2.val (ω ij.1))
      (Measure.pi (fun _ : Fin m => μ)) :=
    iIndepFun_uncurry_pi (fun _ : Fin m => μ) (fun _ (j : Fin l) => X j.val)
      (fun _ j => hm j.val) (fun _ => hind.precomp Fin.val_injective)
  have he (ij : Fin m × Fin l) :
      IdentDistrib (X (ij.1.val*l+ij.2.val))
        (fun ω : Fin m → Ω => X ij.2.val (ω ij.1)) μ (Measure.pi (fun _ : Fin m => μ)) := by
    have heval : IdentDistrib (fun ω : Fin m → Ω => X ij.2.val (ω ij.1)) (X ij.2.val)
        (Measure.pi (fun _ : Fin m => μ)) μ := by
      have hp := measurePreserving_eval (fun _ : Fin m => μ) ij.1
      refine ⟨(hm _).comp_quasiMeasurePreserving hp.quasiMeasurePreserving,hm _,?_⟩
      change (Measure.pi (fun _ : Fin m => μ)).map ((X ij.2.val) ∘ Function.eval ij.1) = μ.map (X ij.2.val)
      have ha : AEMeasurable (X ij.2.val) ((Measure.pi (fun _ : Fin m => μ)).map (Function.eval ij.1)) :=
        hp.map_eq.symm ▸ hm _
      rw [← AEMeasurable.map_map_of_aemeasurable ha hp.measurable.aemeasurable,hp.map_eq]
    exact ((hid _).trans (hid _).symm).trans heval.symm
  have hvec := identDistrib_pi_indep hi₁ hi₂ he
  exact hvec.comp (u := fun x (i : Fin m) => ∑ j : Fin l, x (i,j)) (by fun_prop)

lemma tendstoInDistribution_transport {α E Ω₁ Ω₂ Ω₃ Ω₄ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ω₃] [MeasurableSpace Ω₄]
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {μ₃ : Measure Ω₃} {μ₄ : Measure Ω₄}
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure μ₃] [IsProbabilityMeasure μ₄]
    {X : α → Ω₁ → E} {Y : α → Ω₂ → E} {Z : Ω₃ → E} {W : Ω₄ → E}
    {l : Filter α} (h : TendstoInDistribution X l Z (fun _ => μ₁) μ₃)
    (hXY : ∀ n, IdentDistrib (X n) (Y n) μ₁ μ₂) (hZW : IdentDistrib Z W μ₃ μ₄) :
    TendstoInDistribution Y l W (fun _ => μ₂) μ₄ := by
  refine ⟨fun n => (hXY n).aemeasurable_snd,hZW.aemeasurable_snd,?_⟩
  have heq (n : α) :
      (⟨μ₂.map (Y n), by first | infer_instance | exact Measure.isProbabilityMeasure_map ((hXY n).aemeasurable_snd)⟩ : ProbabilityMeasure E) =
      ⟨μ₁.map (X n), by first | infer_instance | exact Measure.isProbabilityMeasure_map ((hXY n).aemeasurable_fst)⟩ :=
    Subtype.ext (hXY n).map_eq.symm
  have hz : (⟨μ₄.map W, by first | infer_instance | exact Measure.isProbabilityMeasure_map (hZW.aemeasurable_snd)⟩ : ProbabilityMeasure E) =
      ⟨μ₃.map Z, by first | infer_instance | exact Measure.isProbabilityMeasure_map (hZW.aemeasurable_fst)⟩ :=
    Subtype.ext hZW.map_eq.symm
  simp_rw [heq,hz]
  exact h.tendsto

lemma tendstoInDistribution_reindex {α β E Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : α → Ω → E} {Z : Ω' → E} {l : Filter α} {l' : Filter β} {f : β → α}
    (h : TendstoInDistribution X l Z (fun _ => μ) ν) (hf : Tendsto f l' l) :
    TendstoInDistribution (fun n => X (f n)) l' Z (fun _ => μ) ν :=
  ⟨fun n => h.forall_aemeasurable (f n), h.aemeasurable_limit,h.tendsto.comp hf⟩

lemma identDistrib_comp_measurePreserving {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {μ : Measure Ω} {ν : Measure Ω'} {f : Ω' → Ω} {X : Ω → E}
    (hf : MeasurePreserving f ν μ) (hX : AEMeasurable X μ) :
    IdentDistrib (X ∘ f) X ν μ := by
  refine ⟨hX.comp_quasiMeasurePreserving hf.quasiMeasurePreserving,hX,?_⟩
  have ha : AEMeasurable X (ν.map f) := hf.map_eq.symm ▸ hX
  rw [← AEMeasurable.map_map_of_aemeasurable ha hf.measurable.aemeasurable,hf.map_eq]

lemma iid_block_standard_CLT {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (h0 : ∫ ω, X 0 ω ∂μ = 0) (h1 : ∫ ω, (X 0 ω)^2 ∂μ = 1)
    (hind : iIndepFun X μ) (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {m : ℕ} (Z : Fin m → Ω' → ℝ) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) ν)
    (hindZ : iIndepFun Z ν) :
    TendstoInDistribution
      (fun (l : ℕ) ω (i : Fin m) => (Real.sqrt l)⁻¹ * ∑ j : Fin l, X (i.val*l+j.val) ω)
      atTop (fun ω i => Z i ω) (fun _ => μ) ν := by
  let S : ℕ → Ω → ℝ := fun l ω => (Real.sqrt l)⁻¹ * ∑ k ∈ Finset.range l, X k ω
  have hm (l) : AEMeasurable (S l) μ :=
    (Finset.aemeasurable_fun_sum _ (fun k _ => (hid k).aemeasurable_fst)).const_mul _
  have hv (i : Fin m) : TendstoInDistribution
      (fun l (ω : Fin m → Ω) => S l (ω i)) atTop (Z i)
      (fun _ => Measure.pi (fun _ : Fin m => μ)) ν := by
    have hc := tendstoInDistribution_inv_sqrt_mul_sum (hZ i) h0 h1 hind hid
    apply tendstoInDistribution_transport hc
      (fun l => (identDistrib_comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin m => μ) i) (hm l)).symm)
      (IdentDistrib.refl (hZ i).aemeasurable)
  have hj := tendstoInDistribution_pi_indep hv
    (fun l => iIndepFun_pi (fun _ : Fin m => hm l)) hindZ
  apply tendstoInDistribution_transport hj
    (fun l => ?_) (IdentDistrib.refl (AEMeasurable.of_eval (fun i => (hZ i).aemeasurable)))
  have hblk := (identDistrib_iid_blocks X (fun k => (hid k).aemeasurable_fst) hind hid m l).symm
  have hh := hblk.comp (u := fun x (i : Fin m) => (Real.sqrt l)⁻¹ * x i) (by fun_prop)
  change IdentDistrib (fun ω : Fin m → Ω => fun i => (Real.sqrt l)⁻¹ * ∑ j : Fin l, X j.val (ω i))
    (fun ω i => (Real.sqrt l)⁻¹ * ∑ j : Fin l, X (i.val*l+j.val) ω) _ _ at hh
  have heq : (fun ω : Fin m → Ω => fun i => (Real.sqrt l)⁻¹ * ∑ j : Fin l, X j.val (ω i)) =
      (fun ω : Fin m → Ω => fun i => S l (ω i)) := by
    funext ω i
    dsimp [S]
    rw [Fin.sum_univ_eq_sum_range (fun k => X k (ω i)) l]
  rw [heq] at hh
  exact hh

lemma nat_div_ratio_tendsto {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n/m:ℕ):ℝ)/(n:ℝ)) atTop (𝓝 ((m:ℝ)⁻¹)) := by
  have ht := ((tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_mod_div_atTop_nhds_zero_nat hm)).div_const (m:ℝ)
  have hlim : ((1:ℝ)-0)/(m:ℝ) = (m:ℝ)⁻¹ := by simp
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have he : (n:ℝ) = (m:ℝ)*((n/m:ℕ):ℝ)+((n%m:ℕ):ℝ) := by
    exact_mod_cast (Nat.div_add_mod n m).symm
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

lemma sqrt_nat_div_ratio_tendsto {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => Real.sqrt ((n/m:ℕ):ℝ) / Real.sqrt n) atTop (𝓝 ((Real.sqrt m)⁻¹)) := by
  have ht := (nat_div_ratio_tendsto hm).sqrt
  simpa only [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_inv] using ht

lemma iid_block_scaled_CLT {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (h0 : ∫ ω, X 0 ω ∂μ = 0) (h1 : ∫ ω, (X 0 ω)^2 ∂μ = 1)
    (hind : iIndepFun X μ) (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {m : ℕ} (hm : 0 < m) (Z : Fin m → Ω' → ℝ)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 1) ν) (hindZ : iIndepFun Z ν) :
    TendstoInDistribution
      (fun (n : ℕ) ω (i : Fin m) => (∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω)/Real.sqrt n)
      atTop (fun ω i => (Real.sqrt m)⁻¹ * Z i ω) (fun _ => μ) ν := by
  have hc := tendstoInDistribution_reindex (iid_block_standard_CLT X h0 h1 hind hid Z hZ hindZ)
    (Nat.tendsto_div_const_atTop hm.ne')
  have hr : TendstoInMeasure μ (fun n (_ : Ω) => Real.sqrt ((n/m:ℕ):ℝ)/Real.sqrt n) atTop
      (fun _ => (Real.sqrt m)⁻¹) := by
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (ae_of_all μ (fun _ => sqrt_nat_div_ratio_tendsto hm))
  have hmul := hc.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun x : (Fin m → ℝ) × ℝ => fun i => x.2*x.1 i) (by fun_prop) hr
    (fun _ => aemeasurable_const)
  apply hmul.congr (fun n => ae_of_all μ (fun ω => ?_)) (ae_of_all ν (fun _ => rfl))
  funext i
  change (Real.sqrt ((n/m:ℕ):ℝ)/Real.sqrt n) *
    ((Real.sqrt ((n/m:ℕ):ℝ))⁻¹ * ∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω) = _
  have hsum : (∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω) =
      ∑ j ∈ Finset.range (n/m), X (i.val*(n/m)+j) ω :=
    Fin.sum_univ_eq_sum_range (fun j => X (i.val*(n/m)+j) ω) (n/m)
  rw [hsum]
  by_cases hl : n/m = 0
  · simp [hl]
  · have hlt : (0:ℝ) < (n/m:ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hl)
    have hsn : Real.sqrt ((n/m:ℕ):ℝ) ≠ 0 := (Real.sqrt_pos.mpr hlt).ne'
    field_simp

lemma gridTime_mono (m : ℕ) : Monotone (gridTime m) := by
  intro i j hij
  change (i.val:ℝ)/(m:ℝ) ≤ (j.val:ℝ)/(m:ℝ)
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (Nat.cast_nonneg m)

lemma brownian_mesh_independent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (m : ℕ) :
    iIndepFun (meshIncrement B m) μ :=
  hB.hasIndepIncrements m (gridTime m) (gridTime_mono m)

lemma brownian_mesh_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {m : ℕ} (i : Fin m) :
    HasLaw (meshIncrement B m i) (gaussianReal 0 ((m:ℝ≥0)⁻¹)) μ := by
  have h := hB.hasLaw_sub (gridTime m i.succ) (gridTime m i.castSucc)
  have hd : nndist (gridTime m i.succ).val (gridTime m i.castSucc).val = (m:ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    change |((i.val+1:ℕ):ℝ)/(m:ℝ)-(i.val:ℝ)/(m:ℝ)| = (m:ℝ)⁻¹
    rw [← sub_div, Nat.cast_add, Nat.cast_one]
    simp only [add_sub_cancel_left, one_div, abs_inv, abs_of_nonneg (show (0:ℝ) ≤ m from Nat.cast_nonneg m)]
  change HasLaw (B (gridTime m i.succ) - B (gridTime m i.castSucc)) _ _
  simpa only [hd] using h

lemma brownian_normalized_mesh_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {m : ℕ} (hm : 0 < m) (i : Fin m) :
    HasLaw (fun ω => Real.sqrt m * meshIncrement B m i ω) (gaussianReal 0 1) μ := by
  have h := gaussianReal_const_mul (brownian_mesh_hasLaw hB i) (Real.sqrt m)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  · simp
  · apply NNReal.coe_injective
    simp [Real.sq_sqrt, Nat.cast_nonneg, ne_of_gt hm]

lemma brownianPath_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ t : unitInterval, brownianPath B ω t = B ⟨(t:ℝ),t.property.1⟩ ω := by
  filter_upwards [hB.cont] with ω hω
  intro t
  exact ContinuousMap.mkD_apply_of_continuous (hω.comp (by fun_prop))

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_1
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitInterval_solutions_1
lemma brownianPath_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    AEMeasurable (brownianPath B) μ := by
  have hem : MeasurableEmbedding (fun f : C(unitInterval, ℝ) =>
      fun n : ℕ => f (TopologicalSpace.denseSeq unitInterval n)) := by
    apply Continuous.measurableEmbedding
    · apply continuous_pi
      intro n
      fun_prop
    · intro f g hfg
      apply ContinuousMap.ext
      exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer
        f.continuous g.continuous hfg)
  apply hem.aemeasurable_comp_iff.mp
  apply AEMeasurable.of_eval
  intro n
  apply (hB.aemeasurable _).congr
  filter_upwards [brownianPath_ae_eq hB] with ω hω
  exact (hω _).symm

lemma cumulative_mesh {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (m : ℕ) (ω : Ω) (i : Fin (m+1)) :
    cumulative m (fun j => meshIncrement B m j ω) i = B (gridTime m i) ω-B 0 ω := by
  let g : ℕ → ℝ := fun k => B ⟨(k:ℝ)/(m:ℝ), by positivity⟩ ω
  have he0 : g 0 = B 0 ω := by
    simp only [g,Nat.cast_zero,zero_div]
    rfl
  rw [← he0]
  change cumulative m (fun j => g (j.val+1)-g j.val) i = g i.val-g 0
  rw [cumulative_nat m (fun j => g (j+1)-g j) i,Finset.sum_range_sub]

lemma coarseWalk_CLT {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (h0 : ∫ ω, X 0 ω ∂μ = 0) (h1 : ∫ ω, (X 0 ω)^2 ∂μ = 1)
    (hind : iIndepFun X μ) (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B ν) {m : ℕ} (hm : 0 < m) :
    TendstoInDistribution (coarseWalk X m) atTop (fun ω => pathApprox m (brownianPath B ω))
      (fun _ => μ) ν := by
  have hc := iid_block_scaled_CLT X h0 h1 hind hid hm
    (fun i ω => Real.sqrt m*meshIncrement B m i ω)
    (brownian_normalized_mesh_hasLaw hB.toIsPreBrownianReal hm)
    ((brownian_mesh_independent hB.toIsPreBrownianReal m).comp
      (fun _ x => Real.sqrt m*x) (by fun_prop))
  have hs : Real.sqrt (m:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)).ne'
  have hcm : TendstoInDistribution
      (fun (n : ℕ) ω (i : Fin m) => (∑ j : Fin (n/m), X (i.val*(n/m)+j.val) ω)/Real.sqrt n)
      atTop (fun ω i => meshIncrement B m i ω) (fun _ => μ) ν :=
    hc.congr (fun _ => ae_of_all μ (fun _ => rfl)) (ae_of_all ν (fun ω => by
      funext i
      exact inv_mul_cancel_left₀ hs _))
  have hp := hcm.continuous_comp ((continuous_interpolation m).comp (continuous_cumulative m))
  apply hp.congr (fun n => ae_of_all μ (fun ω => coarseWalk_eq_cumulative X m n ω))
  filter_upwards [brownianPath_ae_eq hB,hB.eval_zero_ae_eq_zero] with ω hω hzero
  change interpolation m _ = interpolation m _
  congr 1
  funext i
  rw [cumulative_mesh,hzero,sub_zero]
  exact (hω (gridPoint m i)).symm

lemma integral_lipschitz_approx_bound {E Ω : Type*} [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → E} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    {F : E → ℝ} {M : ℝ} (hM : ∀ x y, dist (F x) (F y) ≤ M)
    {L : ℝ≥0} (hL : LipschitzWith L F) {δ : ℝ} (hδ : 0 ≤ δ) :
    |(∫ ω, F (X ω) ∂μ) - ∫ ω, F (Y ω) ∂μ| ≤
      L*δ + M*μ.real {ω | δ ≤ dist (X ω) (Y ω)} := by
  have hne : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let x₀ := X (Classical.choice hne)
  have h_int (Z : Ω → E) (hZ : AEMeasurable Z μ) : Integrable (fun ω => F (Z ω)) μ := by
    refine Integrable.of_bound ((hL.continuous.measurable.comp_aemeasurable hZ).aestronglyMeasurable)
      (‖F x₀‖+M) (ae_of_all μ (fun ω => ?_))
    have h := hM (Z ω) x₀
    rw [Real.dist_eq] at h
    simpa only [Real.norm_eq_abs] using
      (show |F (Z ω)| ≤ |F x₀|+M from by linarith [abs_sub_abs_le_abs_sub (F (Z ω)) (F x₀)])
  have hi : Integrable (fun ω => F (X ω)-F (Y ω)) μ :=
    (h_int X hX).sub (h_int Y hY)
  have his := hi.norm
  have hset : NullMeasurableSet {ω | dist (X ω) (Y ω) < δ} μ :=
    nullMeasurableSet_lt (hX.dist hY) aemeasurable_const
  rw [← integral_sub (h_int X hX) (h_int Y hY), ← Real.norm_eq_abs]
  calc
    ‖∫ ω, F (X ω)-F (Y ω) ∂μ‖ ≤ ∫ ω, ‖F (X ω)-F (Y ω)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = (∫ ω in {ω | dist (X ω) (Y ω) < δ}, ‖F (X ω)-F (Y ω)‖ ∂μ) +
        ∫ ω in {ω | δ ≤ dist (X ω) (Y ω)}, ‖F (X ω)-F (Y ω)‖ ∂μ := by
      symm
      simpa only [Set.compl_ofPred, not_lt] using integral_add_compl₀ hset his
    _ ≤ (∫ _ in {ω | dist (X ω) (Y ω) < δ}, (L : ℝ)*δ ∂μ) +
        ∫ _ in {ω | δ ≤ dist (X ω) (Y ω)}, M ∂μ := by
      apply add_le_add
      · apply setIntegral_mono_on₀ his.integrableOn integrableOn_const hset
        intro ω hω
        rw [← dist_eq_norm]
        exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hω.le L.coe_nonneg)
      · apply setIntegral_mono his.integrableOn integrableOn_const
        intro ω
        exact hM _ _
    _ = (L:ℝ)*δ*μ.real {ω | dist (X ω) (Y ω) < δ} +
        M*μ.real {ω | δ ≤ dist (X ω) (Y ω)} := by
      simp only [integral_const, measureReal_restrict_apply, MeasurableSet.univ,
        Set.univ_inter, smul_eq_mul]
      ring
    _ ≤ _ := by
      exact add_le_add (by
        calc (L:ℝ)*δ*μ.real {ω | dist (X ω) (Y ω) < δ}
            ≤ (L:ℝ)*δ*1 := mul_le_mul_of_nonneg_left measureReal_le_one (mul_nonneg L.coe_nonneg hδ)
          _ = (L:ℝ)*δ := mul_one _) le_rfl

theorem tendstoInDistribution_of_approximations {E Ω Ω' : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : ℕ → Ω → E} {Y : Ω' → E} {A : ℕ → ℕ → Ω → E} {B : ℕ → Ω' → E}
    (hX : ∀ n, AEMeasurable (X n) μ) (hY : AEMeasurable Y ν)
    (hAB : ∀ m, TendstoInDistribution (A m) atTop (B m) (fun _ => μ) ν)
    (ha : ∀ δ > 0, ∀ η > 0, ∃ m,
      (∀ᶠ n in atTop, μ.real {ω | δ ≤ dist (X n ω) (A m n ω)} ≤ η) ∧
      ν.real {ω | δ ≤ dist (Y ω) (B m ω)} ≤ η) :
    TendstoInDistribution X atTop Y (fun _ => μ) ν := by
  refine ⟨hX,hY,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨M,hM⟩ ⟨L,hL⟩
  have hne : Nonempty Ω' := nonempty_of_isProbabilityMeasure ν
  have hM0 : 0 ≤ M := by simpa using hM (Y (Classical.choice hne)) (Y (Classical.choice hne))
  change Tendsto (fun n => ∫ ω, F ω ∂(μ.map (X n))) atTop (𝓝 (∫ ω, F ω ∂(ν.map Y)))
  simp_rw [integral_map (hX _) hL.continuous.aestronglyMeasurable,
    integral_map hY hL.continuous.aestronglyMeasurable]
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(8*((L:ℝ)+1))
  let η := ε/(8*(M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hLd : (L:ℝ)*δ ≤ ε/8 := by
    dsimp [δ]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 8*((L:ℝ)+1))]
    nlinarith [L.coe_nonneg]
  have hMe : M*η ≤ ε/8 := by
    dsimp [η]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 8*(M+1))]
    nlinarith
  obtain ⟨m,hm,hb⟩ := ha δ hδ η hη
  have hmid := (tendsto_iff_forall_lipschitz_integral_tendsto.mp (hAB m).tendsto)
    F ⟨M,hM⟩ ⟨L,hL⟩
  change Tendsto (fun n => ∫ ω, F ω ∂(μ.map (A m n))) atTop
    (𝓝 (∫ ω, F ω ∂(ν.map (B m)))) at hmid
  simp_rw [integral_map ((hAB m).forall_aemeasurable _) hL.continuous.aestronglyMeasurable,
    integral_map (hAB m).aemeasurable_limit hL.continuous.aestronglyMeasurable] at hmid
  have hme := (Metric.tendsto_nhds.mp hmid) (ε/4) (by positivity)
  filter_upwards [hm,hme] with n hn hnmid
  have hbnd₁ := integral_lipschitz_approx_bound (hX n) ((hAB m).forall_aemeasurable n) hM hL hδ.le
  have hbnd₂ := integral_lipschitz_approx_bound hY (hAB m).aemeasurable_limit hM hL hδ.le
  have hsum := abs_sub_le (∫ ω, F (X n ω) ∂μ) (∫ ω, F (A m n ω) ∂μ) (∫ ω, F (Y ω) ∂ν)
  have hsum₂ := abs_sub_le (∫ ω, F (A m n ω) ∂μ) (∫ ω, F (B m ω) ∂ν) (∫ ω, F (Y ω) ∂ν)
  rw [abs_sub_comm (∫ ω, F (B m ω) ∂ν) (∫ ω, F (Y ω) ∂ν)] at hsum₂
  rw [Real.dist_eq] at hnmid ⊢
  have hpe₁ := mul_le_mul_of_nonneg_left hn hM0
  have hpe₂ := mul_le_mul_of_nonneg_left hb hM0
  linarith

theorem iid_scaledWalk_CLT {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : ℕ → Ω → ℝ) (hXm : ∀ k, Measurable (X k)) (hX₂ : MemLp (X 0) 2 μ)
    (h0 : ∫ ω, X 0 ω ∂μ = 0) (h1 : ∫ ω, (X 0 ω)^2 ∂μ = 1)
    (hind : iIndepFun X μ) (hid : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B ν) :
    TendstoInDistribution (scaledWalk X) atTop (brownianPath B) (fun _ => μ) ν := by
  apply tendstoInDistribution_of_approximations
    (fun n => (scaledWalk_measurable X hXm n).aemeasurable) (brownianPath_aemeasurable hB)
    (A := fun m => coarseWalk X (m+1)) (B := fun m ω => pathApprox (m+1) (brownianPath B ω))
    (fun m => coarseWalk_CLT X h0 h1 hind hid hB (Nat.succ_pos m))
  intro δ hδ η hη
  obtain ⟨k,hk,hmod⟩ := iid_scaledWalk_modulus X hXm hX₂ hind hid h0 (half_pos hδ) hη
  have hb := (tendstoInMeasure_iff_measureReal_dist.mp
    (pathApprox_random_tendstoInMeasure (brownianPath B) (brownianPath_aemeasurable hB))) δ hδ
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hb.eventually (gt_mem_nhds hη))
  let m := max N (2*k)
  have hmk : 2*k ≤ m+1 := le_trans (le_max_right _ _) (Nat.le_succ _)
  have hNM : N ≤ m+1 := le_trans (le_max_left _ _) (Nat.le_succ _)
  have hmesh : 2/((m+1:ℕ):ℝ) ≤ 1/(k:ℝ) := by
    rw [div_le_div_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos m)) (Nat.cast_pos.mpr hk),one_mul]
    exact_mod_cast hmk
  refine ⟨m,?_,?_⟩
  · filter_upwards [eventually_ge_atTop (max k ((m+1)*(m+1)))] with n hn
    apply le_trans (measureReal_mono ?_) (hmod n (le_trans (le_max_left _ _) hn))
    intro ω hω
    by_contra hh
    change ¬∃ s t : unitInterval, dist s t ≤ 1/(k:ℝ) ∧
      δ/2 < |scaledWalk X n ω s-scaledWalk X n ω t| at hh
    push Not at hh
    have he := coarseWalk_error_le X (Nat.succ_pos m) (le_trans (le_max_right _ _) hn) ω
      (half_pos hδ).le (fun s t hst => hh s t (hst.trans hmesh))
    have hd : dist (scaledWalk X n ω) (coarseWalk X (m+1) n ω) ≤ δ/2 := by
      rw [dist_comm,dist_eq_norm]
      exact he
    exact (not_lt_of_ge hω) (hd.trans_lt (half_lt_self hδ))
  · simpa only [dist_comm] using (hN (m+1) hNM).le

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Offspring
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureForallFinHAddNatHMulOfNatIidBridgeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma CriticalEvenOffspring.integrable_step (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => (k : ℝ) - 1) p.law.toMeasure :=
  p.integrable_id.sub (integrable_const 1)


lemma CriticalEvenOffspring.standardStep_memLp (p : CriticalEvenOffspring) :
    MemLp p.standardStep 2 p.law.toMeasure := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [standardStep, div_pow] using p.integrable_step_sq.div_const (p.sigma^2)


lemma CriticalEvenOffspring.streamStep_memLp (p : CriticalEvenOffspring) (j : ℕ) :
    MemLp (p.streamStep j) 2 p.streamLaw :=
  p.standardStep_memLp.comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) j)


lemma CriticalEvenOffspring.streamStep_indep (p : CriticalEvenOffspring) :
    iIndepFun p.streamStep p.streamLaw :=
  iIndepFun_infinitePi (fun _ => measurable_of_countable p.standardStep)


lemma CriticalEvenOffspring.streamStep_ident (p : CriticalEvenOffspring) (j : ℕ) :
    IdentDistrib (p.streamStep j) (p.streamStep 0) p.streamLaw p.streamLaw :=
  ((measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) j).hasLaw.identDistrib
    (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) 0).hasLaw).comp
      (measurable_of_countable p.standardStep)


lemma CriticalEvenOffspring.streamStep_integral (p : CriticalEvenOffspring) (j : ℕ) :
    ∫ ω, p.streamStep j ω ∂p.streamLaw = 0 := by
  calc
    _ = ∫ k, p.standardStep k ∂p.law.toMeasure :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) j).hasLaw.integral_comp
        (by fun_prop)
    _ = 0 := p.integral_standardStep


lemma CriticalEvenOffspring.streamStep_integral_sq (p : CriticalEvenOffspring) (j : ℕ) :
    ∫ ω, p.streamStep j ω ^ 2 ∂p.streamLaw = 1 := by
  calc
    _ = ∫ k, p.standardStep k ^ 2 ∂p.law.toMeasure :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) j).hasLaw.integral_comp
        (by fun_prop)
    _ = 1 := p.integral_standardStep_sq


attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_2
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitInterval_solutions_2
theorem CriticalEvenOffspring.streamWalk_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν) :
    TendstoInDistribution (scaledWalk p.streamStep) atTop (brownianPath B)
      (fun _ => p.streamLaw) ν :=
  iid_scaledWalk_CLT p.streamStep (fun _ => by unfold streamStep; fun_prop)
    (p.streamStep_memLp 0) (p.streamStep_integral 0) (p.streamStep_integral_sq 0)
    p.streamStep_indep p.streamStep_ident hB


lemma CriticalEvenOffspring.iidWalk_measurable (p : CriticalEvenOffspring) (N : ℕ) :
    @Measurable (Fin N → ℕ) C(unitInterval, ℝ) _ (borel _) (p.iidWalk N) :=
  measurable_of_countable _


lemma CriticalEvenOffspring.stream_restrict_law (p : CriticalEvenOffspring) (N : ℕ) :
    HasLaw (fun ω : ℕ → ℕ => fun i : Fin N => ω i.val) (p.iidLaw N) p.streamLaw := by
  refine ⟨(Measurable.of_eval (fun index => measurable_pi_apply index.val)).aemeasurable, ?_⟩
  simpa only [streamLaw, iidLaw, Measure.infinitePi_eq_pi] using
    (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => p.law.toMeasure)
      (@Fin.val_injective N))


lemma CriticalEvenOffspring.iidWalk_restrict (p : CriticalEvenOffspring) (N : ℕ) (ω : ℕ → ℕ) :
    p.iidWalk N (fun i => ω i.val) = scaledWalk p.streamStep N ω := by
  unfold iidWalk scaledWalk
  congr 1
  funext i
  congr 1
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro j hj
    have hjN : j < N := (Finset.mem_range.mp hj).trans_le (Nat.le_of_lt_succ i.isLt)
    exact ⟨⟨j,hjN⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hj⟩, rfl⟩
  · intro j hj
    rfl


theorem CriticalEvenOffspring.iidWalk_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν) :
    TendstoInDistribution p.iidWalk atTop (brownianPath B) p.iidLaw ν := by
  refine ⟨fun n => (p.iidWalk_measurable n).aemeasurable,
    brownianPath_aemeasurable hB, ?_⟩
  have heq (N : ℕ) : (p.iidLaw N).map (p.iidWalk N) =
      p.streamLaw.map (scaledWalk p.streamStep N) := by
    rw [← (p.stream_restrict_law N).map_eq, Measure.map_map (p.iidWalk_measurable N)
      (Measurable.of_eval (fun index => measurable_pi_apply index.val))]
    congr 1
    funext ω
    exact p.iidWalk_restrict N ω
  simpa only [heq] using (p.streamWalk_CLT hB).tendsto


lemma stopPath_apply (t s : unitInterval) (f : C(unitInterval,ℝ)) :
    stopPath t f s = f (min s t) := rfl


lemma stopPath_lipschitz (t : unitInterval) : LipschitzWith 1 (stopPath t) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul]
  apply (ContinuousMap.dist_le (dist_nonneg)).mpr
  intro s
  exact ContinuousMap.dist_apply_le_dist (min s t)


lemma continuous_stopPath (t : unitInterval) : Continuous (stopPath t) :=
  (stopPath_lipschitz t).continuous


lemma CriticalEvenOffspring.iidWalk_endpoint (p : CriticalEvenOffspring) {N : ℕ}
    (hN : 0 < N) (d : Fin N → ℕ) :
    p.iidWalk N d 1 = (totalStep d:ℝ)/(p.sigma*Real.sqrt N) := by
  have hg : gridPoint N (Fin.last N) = 1 := by
    apply Subtype.ext
    simp [gridPoint,hN.ne']
  unfold iidWalk
  rw [← hg,interpolation_gridPoint hN]
  simp only [Fin.val_last,Fin.is_lt,ite_true]
  simp_rw [standardStep]
  rw [← Finset.sum_div]
  have he : (∑ j : Fin N, ((d j:ℝ)-1)) = (totalStep d:ℝ) := by
    simp [totalStep]
  rw [he,div_div]


lemma CriticalEvenOffspring.iidWalk_agree_prefix (p : CriticalEvenOffspring)
    {N m : ℕ} {d e : Fin N → ℕ} {t : unitInterval}
    (ht : (N:ℝ)*(t:ℝ) ≤ m) (hde : ∀ j : Fin N, j.val < m → d j=e j) :
    stopPath t (p.iidWalk N d) = stopPath t (p.iidWalk N e) := by
  ext s
  change interpolation N _ (min s t) = interpolation N _ (min s t)
  rw [interpolation_apply,interpolation_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hz : hat N i.val (min s t)=0
  · simp only [hz,mul_zero]
  · have hi := hat_support hz
    have hist : ((min s t:unitInterval):ℝ) ≤ (t:ℝ) := by exact min_le_right s t
    have hi' : i.val ≤ m := by
      have hh : (i.val:ℝ) < (m:ℝ)+1 := by
        have hai := (abs_lt.mp hi).1
        have hmul := mul_le_mul_of_nonneg_left hist (Nat.cast_nonneg N (α := ℝ))
        linarith
      exact Nat.le_of_lt_succ (by exact_mod_cast hh)
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val < i.val
    · rw [ite_eq_left hj,ite_eq_left hj,hde j (hj.trans_le hi')]
    · simp only [ite_eq_right hj]


lemma CriticalEvenOffspring.prefixWalk_eq (p : CriticalEvenOffspring) (m r : ℕ)
    {t : unitInterval} (ht : ((m+r:ℕ):ℝ)*(t:ℝ) ≤ m) (d : Fin (m+r) → ℕ) :
    p.prefixWalk m r t (iidSplit m r d).1 = stopPath t (p.iidWalk (m+r) d) := by
  apply p.iidWalk_agree_prefix ht
  intro j hj
  let i : Fin m := ⟨j.val,hj⟩
  have he : Fin.castAdd r i = j := Fin.ext rfl
  rw [← he]
  exact congrFun (congrArg Prod.fst ((iidSplit m r).apply_symm_apply
    ((iidSplit m r d).1,fun _ => 1))) i


lemma CriticalEvenOffspring.iid_site_incompatible (p : CriticalEvenOffspring)
    (N : ℕ) (j : ℤ) (hj : ¬Even ((N : ℤ) + j)) :
    (p.iidLaw N).real {d | totalStep d = j} = 0 := by
  rw [measureReal_eq_zero_iff]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [p.iid_ae_even N] with d hd
  intro heq
  apply hj
  have heven : Even (∑ i, d i : ℕ) := Finset.even_sum d (fun i _ => hd i)
  have hcast : Even ((∑ i, d i : ℕ) : ℤ) := by exact_mod_cast heven
  have hs : (N : ℤ) + j = (∑ i, d i : ℕ) := by
    rw [totalStep_eq_sum_sub] at heq
    omega
  rwa [hs]


theorem CriticalEvenOffspring.iid_site_uniform_bound (p : CriticalEvenOffspring) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (j : ℤ),
      Real.sqrt (n+1) * (p.iidLaw (n+1)).real {d | totalStep d = j} ≤ C := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  have hs := p.sigma_pos
  refine ⟨Real.sqrt (Real.pi / c) / (p.sigma * Real.pi), by positivity, ?_⟩
  intro n j
  by_cases hj : Even (((n+1 : ℕ) : ℤ) + j)
  · have hnorm : ‖∫ t : ℝ, p.siteFourier n j t‖ ≤ Real.sqrt (Real.pi / c) := by
      have hbound : ∀ᵐ t ∂volume, ‖p.siteFourier n j t‖ ≤ Real.exp (-c*t^2) := by
        apply ae_of_all
        intro t
        simpa only [siteFourier, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
          p.cutoff_gaussian_bound hg n t
      simpa only [integral_gaussian] using
        norm_integral_le_of_norm_le (integrable_exp_neg_mul_sq hc) hbound
    rw [p.siteFourier_probability n j hj, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)] at hnorm
    rw [le_div_iff₀ (mul_pos p.sigma_pos Real.pi_pos)]
    nlinarith
  · rw [p.iid_site_incompatible _ _ hj, mul_zero]
    positivity


lemma gaussianProfile_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-y^2/2)) (-x*Real.exp (-x^2/2)) x := by
  convert ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp) using 1 <;>
    simp only [id_eq, Pi.neg_apply, Pi.pow_apply]
  ring


lemma gaussianProfile_deriv_bound (x : ℝ) : |(-x)*Real.exp (-x^2/2)| ≤ 1 := by
  have hx : |x| ≤ Real.exp (x^2/2) := by
    have he := Real.add_one_le_exp (x^2/2)
    have hs := sq_nonneg (|x|-1)
    nlinarith [sq_abs x]
  have heq : -x^2/2 = -(x^2/2) := by ring
  rw [abs_mul,abs_neg,abs_of_pos (Real.exp_pos _), heq, Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos _)).mpr hx


lemma gaussianProfile_lipschitz : LipschitzWith 1 (fun x : ℝ => Real.exp (-x^2/2)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun x => (gaussianProfile_hasDerivAt x).differentiableAt)
  intro x
  rw [(gaussianProfile_hasDerivAt x).deriv]
  exact_mod_cast gaussianProfile_deriv_bound x


lemma gaussianProfile_sub_bound (x y : ℝ) :
    |Real.exp (-x^2/2)-Real.exp (-y^2/2)| ≤ |x-y| := by
  simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using gaussianProfile_lipschitz.dist_le_mul x y


theorem CriticalEvenOffspring.local_limit_oscillation (p : CriticalEvenOffspring) :
    ∃ E : ℕ → ℝ, (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (n : ℕ) (j k : ℤ), Even (((n+1:ℕ):ℤ)+j) → Even (((n+1:ℕ):ℤ)+k) →
        |Real.sqrt (n+1) * ((p.iidLaw (n+1)).real {d | totalStep d = j} -
          (p.iidLaw (n+1)).real {d | totalStep d = k})| ≤
        2*E n + (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
          |(j:ℝ)-(k:ℝ)| /(p.sigma*Real.sqrt (n+1)) := by
  obtain ⟨E,hE,hEt,hbound⟩ := p.uniform_local_limit
  refine ⟨E,hE,hEt,?_⟩
  intro n j k hj hk
  let a := p.sigma*Real.sqrt (n+1)
  let b := Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)
  have ha : 0 < a := mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by positivity))
  have hb : 0 ≤ b := div_nonneg (by positivity) (mul_pos p.sigma_pos Real.pi_pos).le
  have hg : |b*Real.exp (-((j:ℝ)/a)^2/2)-b*Real.exp (-((k:ℝ)/a)^2/2)| ≤
      b*|(j:ℝ)-(k:ℝ)| /a := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hb]
    have h := mul_le_mul_of_nonneg_left (gaussianProfile_sub_bound ((j:ℝ)/a) ((k:ℝ)/a)) hb
    rw [← sub_div,abs_div,abs_of_pos ha] at h
    simpa only [mul_div_assoc] using h
  have hj' := hbound n j hj
  have hk' := hbound n k hk
  have ht₁ := abs_sub_le (Real.sqrt (n+1)*(p.iidLaw (n+1)).real {d | totalStep d = j})
    (b*Real.exp (-((j:ℝ)/a)^2/2))
    (Real.sqrt (n+1)*(p.iidLaw (n+1)).real {d | totalStep d = k})
  have ht₂ := abs_sub_le (b*Real.exp (-((j:ℝ)/a)^2/2))
    (b*Real.exp (-((k:ℝ)/a)^2/2))
    (Real.sqrt (n+1)*(p.iidLaw (n+1)).real {d | totalStep d = k})
  rw [abs_sub_comm (b*Real.exp (-((k:ℝ)/a)^2/2))] at ht₂
  rw [mul_sub]
  change _ ≤ 2*E n + b*|(j:ℝ)-(k:ℝ)| /a
  change |_ - b*Real.exp (-((j:ℝ)/a)^2/2)| ≤ E n at hj'
  change |_ - b*Real.exp (-((k:ℝ)/a)^2/2)| ≤ E n at hk'
  linarith


theorem CriticalEvenOffspring.suffix_site_oscillation (p : CriticalEvenOffspring) :
    ∃ E : ℕ → ℝ, (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (m r : ℕ) (j k : ℤ), Even (((m+(r+1):ℕ):ℤ)+j) →
        Even (((m+(r+1):ℕ):ℤ)+k) →
        ∀ᵐ d ∂p.iidLaw m,
          |(p.iidLaw (r+1)).real {b | totalStep b=j-totalStep d} -
            (p.iidLaw (r+1)).real {b | totalStep b=k-totalStep d}| ≤
          (2*E r + (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
            |(j:ℝ)-(k:ℝ)| /(p.sigma*Real.sqrt (r+1))) / Real.sqrt (r+1) := by
  obtain ⟨E,hE,hEt,hb⟩ := p.local_limit_oscillation
  refine ⟨E,hE,hEt,?_⟩
  intro m r j k hj hk
  filter_upwards [p.iid_ae_even m] with d hd
  have hp : Even ((m:ℤ)+totalStep d) := by
    rw [totalStep_eq_sum_sub]
    have he : (m:ℤ)+((∑ i, d i : ℕ):ℤ)-(m:ℤ) = ((∑ i, d i : ℕ):ℤ) := by ring
    rw [← add_sub_assoc,he]
    exact_mod_cast Finset.even_sum d (fun i _ => hd i)
  have hj' : Even (((r+1:ℕ):ℤ)+(j-totalStep d)) := by
    have he : (((r+1:ℕ):ℤ)+(j-totalStep d)) =
        (((m+(r+1):ℕ):ℤ)+j)-((m:ℤ)+totalStep d) := by push_cast; ring
    rw [he]
    exact hj.sub hp
  have hk' : Even (((r+1:ℕ):ℤ)+(k-totalStep d)) := by
    have he : (((r+1:ℕ):ℤ)+(k-totalStep d)) =
        (((m+(r+1):ℕ):ℤ)+k)-((m:ℤ)+totalStep d) := by push_cast; ring
    rw [he]
    exact hk.sub hp
  have h := hb r (j-totalStep d) (k-totalStep d) hj' hk'
  have hs : 0 < Real.sqrt (r+1) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_mul,abs_of_pos hs] at h
  have he : ((j-totalStep d:ℤ):ℝ)-((k-totalStep d:ℤ):ℝ) = (j:ℝ)-(k:ℝ) := by
    push_cast
    ring
  rw [he] at h
  exact (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using h)


lemma iidSplit_preserving (μ : Measure ℕ) [SigmaFinite μ] (m r : ℕ) :
    MeasurePreserving (iidSplit m r) (Measure.pi (fun _ : Fin (m+r) => μ))
      ((Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi (fun _ : Fin r => μ))) := by
  exact (measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin r => μ)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (m+r) => μ) finSumFinEquiv).symm


lemma iid_prefix_test_endpoint (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (j : ℤ) (F : (Fin m → ℕ) → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hF : ∀ d, |F d| ≤ M) :
    (∫ d, (if totalStep d = j then F (iidSplit m r d).1 else 0)
      ∂(Measure.pi (fun _ : Fin (m+r) => μ))) =
    ∫ a, F a * (Measure.pi (fun _ : Fin r => μ)).real
      {b | totalStep b = j-totalStep a} ∂(Measure.pi (fun _ : Fin m => μ)) := by
  let f : ((Fin m → ℕ) × (Fin r → ℕ)) → ℝ := fun x =>
    if totalStep x.1 + totalStep x.2 = j then F x.1 else 0
  have hf : Integrable f ((Measure.pi (fun _ : Fin m => μ)).prod
      (Measure.pi (fun _ : Fin r => μ))) := by
    apply (integrable_const M).mono' (by measurability)
    filter_upwards [] with x
    dsimp [f]
    split
    · exact hF _
    · simpa only [abs_zero] using hM
  have heq : (fun d => if totalStep d = j then F (iidSplit m r d).1 else 0) =
      f ∘ iidSplit m r := by
    funext d
    simp only [Function.comp_apply,f,totalStep_split]
  rw [heq]
  change (∫ d, f (iidSplit m r d) ∂(Measure.pi (fun _ : Fin (m+r) => μ))) = _
  rw [(iidSplit_preserving μ m r).integral_comp' f,integral_prod f hf]
  apply integral_congr_ae
  filter_upwards [] with a
  have hi : (fun b => f (a,b)) =
      ({b | totalStep b = j-totalStep a} : Set (Fin r → ℕ)).indicator (fun _ => F a) := by
    funext b
    simp only [f, Set.indicator_apply, Set.mem_ofPred_eq]
    simp only [show (totalStep a + totalStep b = j) ↔
      (totalStep b = j-totalStep a) by omega]
  rw [hi, integral_indicator (by measurability),setIntegral_const]
  simp only [smul_eq_mul, mul_comm]


lemma integral_cond_eq_div {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (hE : MeasurableSet E) (F : Ω → ℝ) :
    (∫ ω, F ω ∂cond μ E) = (∫ ω, E.indicator F ω ∂μ)/μ.real E := by
  rw [ProbabilityTheory.cond,integral_smul_measure,integral_indicator hE,ENNReal.toReal_inv]
  simp only [smul_eq_mul,measureReal_def,div_eq_mul_inv,mul_comm]


lemma endpointWindow_apply (s : Finset ℤ) (w : ℤ → ℝ) (z : ℤ) :
    endpointWindow s w z = if z ∈ s then w z else 0 := by
  classical
  simp [endpointWindow]


lemma iid_prefix_test_window (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (s : Finset ℤ) (w : ℤ → ℝ) (F : (Fin m → ℕ) → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hF : ∀ d, |F d| ≤ M) :
    (∫ d, F (iidSplit m r d).1 * endpointWindow s w (totalStep d)
      ∂(Measure.pi (fun _ : Fin (m+r) => μ))) =
    ∫ a, F a * (∑ j ∈ s, w j * (Measure.pi (fun _ : Fin r => μ)).real
      {b | totalStep b = j-totalStep a}) ∂(Measure.pi (fun _ : Fin m => μ)) := by
  classical
  have hif (j : ℤ) : Integrable (fun d : Fin (m+r) → ℕ =>
      if totalStep d=j then F (iidSplit m r d).1 else 0)
      (Measure.pi (fun _ : Fin (m+r) => μ)) := by
    apply (integrable_const M).mono' (by measurability)
    filter_upwards [] with d
    split
    · exact hF _
    · simpa using hM
  have hsite (j : ℤ) : Integrable (fun a : Fin m → ℕ =>
      F a*(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a})
      (Measure.pi (fun _ : Fin m => μ)) := by
    apply (integrable_const M).mono' (by measurability)
    filter_upwards [] with a
    change |F a*(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a}| ≤ M
    rw [abs_mul,abs_of_nonneg measureReal_nonneg]
    exact (mul_le_mul_of_nonneg_right (hF a) measureReal_nonneg).trans
      (mul_le_of_le_one_right hM (measureReal_le_one))
  have he (d : Fin (m+r) → ℕ) :
      F (iidSplit m r d).1 * endpointWindow s w (totalStep d) =
      ∑ j ∈ s, w j*(if totalStep d=j then F (iidSplit m r d).1 else 0) := by
    rw [endpointWindow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split <;> ring
  have he' (a : Fin m → ℕ) :
      F a * (∑ j ∈ s, w j*(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a}) =
      ∑ j ∈ s, w j*(F a*(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a}) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he,he']
  rw [integral_finsetSum s (fun j _ => (hif j).const_mul (w j)),
    integral_finsetSum s (fun j _ => (hsite j).const_mul (w j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,integral_const_mul,iid_prefix_test_endpoint μ m r j F hM hF]


lemma normalized_integral_stability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {k l F : Ω → ℝ} {M a : ℝ}
    (hk : Integrable k μ) (hl : Integrable l μ)
    (hl0 : ∀ᵐ ω ∂μ, 0 ≤ l ω)
    (hK : 0 < ∫ ω, k ω ∂μ) (hL : 0 < ∫ ω, l ω ∂μ)
    (hF : AEStronglyMeasurable F μ) (hM : 0 ≤ M)
    (hFM : ∀ᵐ ω ∂μ, |F ω| ≤ M)
    (ha : ∫ ω, |k ω-l ω| ∂μ ≤ a) :
    |(∫ ω, F ω*k ω ∂μ)/(∫ ω, k ω ∂μ) -
      (∫ ω, F ω*l ω ∂μ)/(∫ ω, l ω ∂μ)| ≤
      2*M*a/(∫ ω, k ω ∂μ) := by
  have hFk : Integrable (fun ω => F ω*k ω) μ :=
    (hk.norm.const_mul M).mono' (hF.mul hk.aestronglyMeasurable) (by
      filter_upwards [hFM] with ω hω
      simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right hω (abs_nonneg (k ω)))
  have hFl : Integrable (fun ω => F ω*l ω) μ :=
    (hl.norm.const_mul M).mono' (hF.mul hl.aestronglyMeasurable) (by
      filter_upwards [hFM] with ω hω
      simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul_of_nonneg_right hω (abs_nonneg (l ω)))
  let K := ∫ ω, k ω ∂μ
  let L := ∫ ω, l ω ∂μ
  let A := ∫ ω, F ω*k ω ∂μ
  let D := ∫ ω, F ω*l ω ∂μ
  have hAD : |A-D| ≤ M*a := by
    rw [show A-D = ∫ ω, F ω*(k ω-l ω) ∂μ by
      simp only [A,D,mul_sub,integral_sub hFk hFl]]
    calc
      _ ≤ ∫ ω, |F ω*(k ω-l ω)| ∂μ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun ω => F ω*(k ω-l ω))
      _ ≤ ∫ ω, M*|k ω-l ω| ∂μ := by
        apply integral_mono_ae
        · simpa only [mul_sub, Pi.sub_apply, Real.norm_eq_abs] using (hFk.sub hFl).norm
        · exact (hk.sub hl).norm.const_mul M
        · filter_upwards [hFM] with ω hω
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
      _ ≤ M*a := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left ha hM
  have hKL : |L-K| ≤ a := by
    calc
      _ = |∫ ω, k ω-l ω ∂μ| := by rw [integral_sub hk hl]; exact abs_sub_comm _ _
      _ ≤ ∫ ω, |k ω-l ω| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => k ω-l ω)
      _ ≤ a := ha
  have hD : |D| ≤ M*L := by
    calc
      _ ≤ ∫ ω, |F ω*l ω| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => F ω*l ω)
      _ ≤ ∫ ω, M*l ω ∂μ := by
        apply integral_mono_ae hFl.norm (hl.const_mul M)
        filter_upwards [hFM,hl0] with ω hω hlω
        change |F ω*l ω| ≤ M*l ω
        rw [abs_mul,abs_of_nonneg hlω]
        exact mul_le_mul_of_nonneg_right hω hlω
      _ = M*L := integral_const_mul _ _
  have hA0 : 0 ≤ a := (integral_nonneg (fun _ => abs_nonneg _)).trans ha
  have hK' : K ≠ 0 := hK.ne'
  have hL' : L ≠ 0 := hL.ne'
  have he : A/K-D/L = (A-D)/K + D*(L-K)/(K*L) := by
    field_simp [hK',hL']
    ring
  change |A/K-D/L| ≤ 2*M*a/K
  rw [he]
  calc
    _ ≤ |(A-D)/K| + |D*(L-K)/(K*L)| := abs_add_le _ _
    _ = |A-D|/K + |D| *|L-K|/(K*L) := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos hK,abs_of_pos (mul_pos hK hL)]
    _ ≤ (M*a)/K + (M*L)*a/(K*L) := by
      exact add_le_add (div_le_div_of_nonneg_right hAD hK.le)
        (div_le_div_of_nonneg_right (mul_le_mul hD hKL (abs_nonneg _) (by positivity))
          (mul_pos hK hL).le)
    _ = _ := by field_simp [hK',hL']; ring


lemma finite_window_stability {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (k : ι → Ω → ℝ) (k₀ F : Ω → ℝ) {M a : ℝ}
    (hw : ∀ j ∈ s, 0 ≤ w j) (hW : 0 < ∑ j ∈ s, w j)
    (hk : ∀ j ∈ s, Integrable (k j) μ) (hk₀ : Integrable k₀ μ)
    (hk0 : ∀ j ∈ s, ∀ᵐ ω ∂μ, 0 ≤ k j ω)
    (hK : 0 < ∫ ω, k₀ ω ∂μ)
    (hL : 0 < ∫ ω, (∑ j ∈ s, w j*k j ω) ∂μ)
    (hF : AEStronglyMeasurable F μ) (hM : 0 ≤ M)
    (hFM : ∀ᵐ ω ∂μ, |F ω| ≤ M)
    (hd : ∀ j ∈ s, ∀ᵐ ω ∂μ, |k₀ ω-k j ω| ≤ a) :
    |(∫ ω, F ω*k₀ ω ∂μ)/(∫ ω, k₀ ω ∂μ) -
      (∫ ω, F ω*(∑ j ∈ s, w j*k j ω) ∂μ)/
        (∫ ω, (∑ j ∈ s, w j*k j ω) ∂μ)| ≤ 2*M*a/(∫ ω, k₀ ω ∂μ) := by
  classical
  let W := ∑ j ∈ s, w j
  let l : Ω → ℝ := fun ω => (∑ j ∈ s, w j*k j ω)/W
  have hl' : Integrable (fun ω => ∑ j ∈ s, w j*k j ω) μ :=
    integrable_finsetSum s (fun j hj => (hk j hj).const_mul (w j))
  have hl : Integrable l μ := hl'.div_const W
  have hl0 : ∀ᵐ ω ∂μ, 0 ≤ l ω := by
    filter_upwards [(s.eventually_all).mpr hk0] with ω hω
    exact div_nonneg (Finset.sum_nonneg (fun j hj => mul_nonneg (hw j hj) (hω j hj))) hW.le
  have hLp : 0 < ∫ ω, l ω ∂μ := by
    dsimp [l]
    rw [integral_div]
    exact div_pos hL hW
  have hdiff : ∀ᵐ ω ∂μ, |k₀ ω-l ω| ≤ a := by
    filter_upwards [(s.eventually_all).mpr hd] with ω hω
    have he : k₀ ω-l ω = (∑ j ∈ s, w j*(k₀ ω-k j ω))/W := by
      dsimp [l]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      dsimp [W]
      field_simp [hW.ne']
    rw [he,abs_div,abs_of_pos hW]
    apply (div_le_iff₀ hW).mpr
    calc
      _ ≤ ∑ j ∈ s, |w j*(k₀ ω-k j ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, w j*a := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul,abs_of_nonneg (hw j hj)]
        exact mul_le_mul_of_nonneg_left (hω j hj) (hw j hj)
      _ = a*W := by rw [← Finset.sum_mul,mul_comm]
  have ha : ∫ ω, |k₀ ω-l ω| ∂μ ≤ a := by
    calc
      _ ≤ ∫ _, a ∂μ := integral_mono_ae (hk₀.sub hl).norm (integrable_const a) (by
        filter_upwards [hdiff] with ω hω
        exact hω)
      _ = a := by simp
  have h := normalized_integral_stability hk₀ hl hl0 hK hLp hF hM hFM ha
  have he : (∫ ω, F ω*l ω ∂μ)/(∫ ω, l ω ∂μ) =
      (∫ ω, F ω*(∑ j ∈ s, w j*k j ω) ∂μ)/
        (∫ ω, (∑ j ∈ s, w j*k j ω) ∂μ) := by
    have hn : (∫ ω, F ω*l ω ∂μ) =
        (∫ ω, F ω*(∑ j ∈ s, w j*k j ω) ∂μ)/W := by
      simp_rw [l, ← mul_div_assoc, integral_div]
    rw [hn]
    dsimp [l]
    rw [integral_div]
    exact div_div_div_cancel_right₀ hW.ne' _ _
  rw [he] at h
  exact h


lemma iid_site_convolution (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (j : ℤ) :
    (Measure.pi (fun _ : Fin (m+r) => μ)).real {d | totalStep d=j} =
      ∫ a, (Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep a}
        ∂(Measure.pi (fun _ : Fin m => μ)) := by
  have h := iid_prefix_test_endpoint μ m r j (fun _ => 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun _ => by norm_num)
  simp only [one_mul] at h
  rw [show (fun d : Fin (m+r) → ℕ => if totalStep d=j then (1:ℝ) else 0) =
      ({d | totalStep d=j} : Set (Fin (m+r) → ℕ)).indicator (fun _ => 1) by funext d; simp [Set.indicator_apply],
    integral_indicator (by measurability),setIntegral_const] at h
  simpa only [smul_eq_mul,mul_one] using h


theorem iid_prefix_window_bound (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (j₀ : ℤ) (s : Finset ℤ) (w : ℤ → ℝ)
    (hj₀ : j₀ ∈ s) (hw : ∀ j ∈ s, 0 ≤ w j) (hw₀ : 0 < w j₀)
    (hP : 0 < (Measure.pi (fun _ : Fin (m+r) => μ)).real {d | totalStep d=j₀})
    (F : (Fin m → ℕ) → ℝ) {M a : ℝ} (hM : 0 ≤ M) (hF : ∀ d, |F d| ≤ M)
    (hd : ∀ j ∈ s, ∀ᵐ d ∂(Measure.pi (fun _ : Fin m => μ)),
      |(Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j₀-totalStep d} -
        (Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep d}| ≤ a) :
    |(∫ d, F (iidSplit m r d).1 ∂cond (Measure.pi (fun _ : Fin (m+r) => μ))
        {d | totalStep d=j₀}) -
      (∫ d, F (iidSplit m r d).1 * endpointWindow s w (totalStep d)
        ∂(Measure.pi (fun _ : Fin (m+r) => μ))) /
      (∫ d, endpointWindow s w (totalStep d) ∂(Measure.pi (fun _ : Fin (m+r) => μ)))| ≤
      2*M*a/(Measure.pi (fun _ : Fin (m+r) => μ)).real {d | totalStep d=j₀} := by
  classical
  let k : ℤ → (Fin m → ℕ) → ℝ := fun j d =>
    (Measure.pi (fun _ : Fin r => μ)).real {b | totalStep b=j-totalStep d}
  have hk (j : ℤ) : Integrable (k j) (Measure.pi (fun _ : Fin m => μ)) := by
    apply (integrable_const (1:ℝ)).mono' (measurable_of_countable (k j)).aestronglyMeasurable
    filter_upwards [] with d
    change |k j d| ≤ 1
    rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hki (j : ℤ) : (∫ d, k j d ∂(Measure.pi (fun _ : Fin m => μ))) =
      (Measure.pi (fun _ : Fin (m+r) => μ)).real {d | totalStep d=j} :=
    (iid_site_convolution μ m r j).symm
  have hW : 0 < ∑ j ∈ s, w j := hw₀.trans_le
    (Finset.single_le_sum hw hj₀)
  have hL : 0 < ∫ d, (∑ j ∈ s, w j*k j d) ∂(Measure.pi (fun _ : Fin m => μ)) := by
    rw [integral_finsetSum s (fun j _ => (hk j).const_mul (w j))]
    simp_rw [integral_const_mul,hki]
    apply (mul_pos hw₀ hP).trans_le
    apply Finset.single_le_sum _ hj₀
    intro j hj
    exact mul_nonneg (hw j hj) measureReal_nonneg
  have h := finite_window_stability s w k (k j₀) F hw hW (fun j _ => hk j) (hk j₀)
    (fun _ _ => ae_of_all _ (fun _ => measureReal_nonneg)) (by rwa [hki]) hL
    (by measurability) hM (ae_of_all _ hF) hd
  have he : (∫ d, F (iidSplit m r d).1 ∂cond (Measure.pi (fun _ : Fin (m+r) => μ))
      {d | totalStep d=j₀}) =
      (∫ d, F d*k j₀ d ∂(Measure.pi (fun _ : Fin m => μ))) /
        (∫ d, k j₀ d ∂(Measure.pi (fun _ : Fin m => μ))) := by
    rw [integral_cond_eq_div _ _ (by measurability)]
    simp only [Set.indicator_apply,Set.mem_ofPred_eq]
    rw [iid_prefix_test_endpoint μ m r j₀ F hM hF,hki]
  have hn := iid_prefix_test_window μ m r s w F hM hF
  have hden := iid_prefix_test_window μ m r s w (fun _ => 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun _ => by norm_num)
  simp only [one_mul] at hden
  rw [he,hn,hden,hki]
  rw [hki] at h
  simpa only [k] using h


lemma softCutoff_continuous (ε : ℝ) : Continuous (softCutoff ε) := by
  unfold softCutoff
  fun_prop


lemma softCutoff_nonneg (ε x : ℝ) : 0 ≤ softCutoff ε x := le_max_left _ _


lemma softCutoff_le_one {ε : ℝ} (hε : 0 < ε) (x : ℝ) : softCutoff ε x ≤ 1 := by
  apply max_le (by norm_num)
  have := div_nonneg (abs_nonneg x) hε.le
  linarith


lemma softCutoff_pos_iff {ε x : ℝ} (hε : 0 < ε) :
    0 < softCutoff ε x ↔ |x| < ε := by
  simp only [softCutoff, lt_max_iff, lt_self_iff_false, false_or,
    sub_pos, div_lt_one hε]


lemma softCutoff_support {ε : ℝ} (hε : 0 < ε) :
    Function.support (softCutoff ε) = Set.Ioo (-ε) ε := by
  ext x
  rw [Function.mem_support, ← (softCutoff_nonneg ε x).lt_iff_ne']
  simp only [softCutoff_pos_iff hε, abs_lt,Set.mem_Ioo]


lemma softCutoff_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEMeasurable Y μ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ω => softCutoff ε (Y ω)) μ := by
  apply (integrable_const (1:ℝ)).mono'
    ((softCutoff_continuous ε).aestronglyMeasurable.comp_aemeasurable hY)
  filter_upwards [] with ω
  change ‖softCutoff ε (Y ω)‖ ≤ (1:ℝ)
  rw [Real.norm_eq_abs,abs_of_nonneg (softCutoff_nonneg _ _)]
  exact softCutoff_le_one hε _


lemma mem_latticeWindow_iff (N : ℕ) {R : ℝ} (j : ℤ) :
    j ∈ latticeWindow N R ↔ Even ((N:ℤ)+j) ∧ |(j:ℝ)| < R := by
  classical
  simp only [latticeWindow, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    have hb : |(j:ℝ)| ≤ (⌈R⌉₊:ℝ) := h.2.le.trans (Nat.le_ceil R)
    have hj := abs_le.mp hb
    have hl : -(⌈R⌉₊ : ℤ) ≤ j := by exact_mod_cast hj.1
    have hr : j ≤ (⌈R⌉₊ : ℤ) := by exact_mod_cast hj.2
    exact ⟨⟨hl,hr⟩,h⟩


lemma softCutoff_scaled_pos_iff {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) (j : ℤ) :
    0 < softCutoff ε ((j:ℝ)/a) ↔ |(j:ℝ)| < ε*a := by
  rw [softCutoff_pos_iff hε,abs_div,abs_of_pos ha,div_lt_iff₀ ha]


lemma endpointWindow_softCutoff (N : ℕ) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (j : ℤ) (hj : Even ((N:ℤ)+j)) :
    endpointWindow (latticeWindow N (ε*a)) (fun k => softCutoff ε ((k:ℝ)/a)) j =
      softCutoff ε ((j:ℝ)/a) := by
  rw [endpointWindow_apply]
  split_ifs with h
  · rfl
  · have hn : ¬|(j:ℝ)| < ε*a := fun hh => h ((mem_latticeWindow_iff N j).mpr ⟨hj,hh⟩)
    have hz := not_lt.mp (fun hh => hn ((softCutoff_scaled_pos_iff hε ha j).mp hh))
    exact (le_antisymm hz (softCutoff_nonneg ε _)).symm


lemma CriticalEvenOffspring.iid_endpointWindow_ae (p : CriticalEvenOffspring)
    (N : ℕ) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    ∀ᵐ d ∂p.iidLaw N,
      endpointWindow (latticeWindow N (ε*a)) (fun k => softCutoff ε ((k:ℝ)/a)) (totalStep d) =
        softCutoff ε ((totalStep d:ℝ)/a) := by
  filter_upwards [p.iid_ae_even N] with d hd
  apply endpointWindow_softCutoff N hε ha
  rw [totalStep_eq_sum_sub]
  have hh : (N:ℤ)+((∑ i, d i : ℕ):ℤ)-(N:ℤ) = ((∑ i, d i : ℕ):ℤ) := by ring
  rw [← add_sub_assoc,hh]
  exact_mod_cast Finset.even_sum d (fun i _ => hd i)


theorem CriticalEvenOffspring.prefix_soft_bound (p : CriticalEvenOffspring) :
    ∃ E : ℕ → ℝ, (∀ n, 0 ≤ E n) ∧ Tendsto E atTop (𝓝 0) ∧
      ∀ (m r : ℕ) (ε : ℝ), 0 < ε →
      Even (((m+(r+1):ℕ):ℤ)-1) →
      1 < ε*(p.sigma*Real.sqrt (m+(r+1))) →
      0 < (p.iidLaw (m+(r+1))).real {d | totalStep d = -1} →
      ∀ (F : (Fin m → ℕ) → ℝ) (M : ℝ), 0 ≤ M → (∀ d, |F d| ≤ M) →
      |(∫ d, F (iidSplit m (r+1) d).1 ∂cond (p.iidLaw (m+(r+1))) {d | totalStep d = -1}) -
        (∫ d, F (iidSplit m (r+1) d).1 *
          softCutoff ε ((totalStep d:ℝ)/(p.sigma*Real.sqrt (m+(r+1)))) ∂p.iidLaw (m+(r+1))) /
        (∫ d, softCutoff ε ((totalStep d:ℝ)/(p.sigma*Real.sqrt (m+(r+1)))) ∂p.iidLaw (m+(r+1)))| ≤
      2*M*((2*E r + (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
        (1+ε*(p.sigma*Real.sqrt (m+(r+1)))) /(p.sigma*Real.sqrt (r+1)))/Real.sqrt (r+1)) /
        (p.iidLaw (m+(r+1))).real {d | totalStep d = -1} := by
  obtain ⟨E,hE,hEt,hb⟩ := p.suffix_site_oscillation
  refine ⟨E,hE,hEt,?_⟩
  intro m r ε hε hpar hw hP F M hM hF
  let N := m+(r+1)
  let a := p.sigma*Real.sqrt N
  have ha : 0 < a := mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by dsimp [N]; positivity))
  let s := latticeWindow N (ε*a)
  let w : ℤ → ℝ := fun j => softCutoff ε ((j:ℝ)/a)
  have hmem : (-1:ℤ) ∈ s := by
    apply (mem_latticeWindow_iff N _).mpr
    refine ⟨by simpa only [sub_eq_add_neg,Int.cast_one] using hpar, ?_⟩
    simpa only [Int.cast_neg,Int.cast_one,abs_neg,abs_one,a,N,Nat.cast_add,Nat.cast_one] using hw
  have hwpos : 0 < w (-1) := by
    apply (softCutoff_scaled_pos_iff hε ha (-1)).mpr
    simpa only [Int.cast_neg,Int.cast_one,abs_neg,abs_one,a,N,Nat.cast_add,Nat.cast_one] using hw
  have hdiff (j : ℤ) (hj : j ∈ s) :
      ∀ᵐ d ∂p.iidLaw m,
        |(p.iidLaw (r+1)).real {b | totalStep b=(-1)-totalStep d} -
          (p.iidLaw (r+1)).real {b | totalStep b=j-totalStep d}| ≤
        (2*E r + (Real.sqrt (2*Real.pi)/(p.sigma*Real.pi)) *
          (1+ε*a)/(p.sigma*Real.sqrt (r+1)))/Real.sqrt (r+1) := by
    have hjp := (mem_latticeWindow_iff N j).mp hj
    have hpar' : Even (((m+(r+1):ℕ):ℤ)+(-1)) := by simpa only [sub_eq_add_neg] using hpar
    filter_upwards [hb m r (-1) j hpar' hjp.1] with d hd
    apply hd.trans
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply add_le_add_right
    apply div_le_div_of_nonneg_right _ (mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by positivity))).le
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (Real.sqrt_nonneg _) (mul_pos p.sigma_pos Real.pi_pos).le)
    calc
      |((-1:ℤ):ℝ)-(j:ℝ)| ≤ |((-1:ℤ):ℝ)|+|(j:ℝ)| := abs_sub _ _
      _ ≤ 1+ε*a := by simp only [Int.cast_neg,Int.cast_one,abs_neg,abs_one]; linarith [hjp.2]
  have h := iid_prefix_window_bound p.law.toMeasure m (r+1) (-1) s w hmem
    (fun j _ => softCutoff_nonneg ε _) hwpos hP F hM hF hdiff
  have he := p.iid_endpointWindow_ae N hε ha
  have hn : (∫ d, F (iidSplit m (r+1) d).1 * endpointWindow s w (totalStep d) ∂p.iidLaw N) =
      ∫ d, F (iidSplit m (r+1) d).1 * softCutoff ε ((totalStep d:ℝ)/a) ∂p.iidLaw N := by
    apply integral_congr_ae
    filter_upwards [he] with d hd
    rw [show endpointWindow s w (totalStep d) = softCutoff ε ((totalStep d:ℝ)/a) from hd]
  have hden := integral_congr_ae he
  change |_- (∫ d, F (iidSplit m (r+1) d).1 * endpointWindow s w (totalStep d) ∂p.iidLaw N) /
    (∫ d, endpointWindow s w (totalStep d) ∂p.iidLaw N)| ≤ _ at h
  rw [hn,hden] at h
  simpa only [a,N,Nat.cast_add,Nat.cast_one,iidLaw] using h

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_BridgeLimit
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_3
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitInterval_solutions_3
lemma bridgePath_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    AEMeasurable (bridgePath B) μ :=
  (brownianPath_aemeasurable hB).sub ((hB.aemeasurable 1).smul aemeasurable_const)

lemma bridgePath_ae_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ t : unitInterval,
      bridgePath B ω t = B ⟨(t:ℝ),t.property.1⟩ ω - (t:ℝ)*B 1 ω := by
  filter_upwards [brownianPath_ae_eq hB] with ω hω
  intro t
  simp only [bridgePath, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_mk, smul_eq_mul, hω, mul_comm]

lemma bridge_joint_gaussian {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) :
    IsGaussianProcess (Sum.elim
      (fun (t : unitInterval) ω => B ⟨(t:ℝ),t.property.1⟩ ω-(t:ℝ)*B 1 ω)
      (fun (_ : Unit) ω => B 1 ω)) μ := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro s
  cases s with
  | inl t =>
    let u : ℝ≥0 := ⟨(t:ℝ),t.property.1⟩
    refine ⟨{u,1},
      { toFun x := x ⟨u, by simp⟩ - (t:ℝ) * x ⟨1, by simp⟩
        map_add' x y := by simp only [Pi.add_apply]; ring
        map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }, ?_⟩
    intro ω
    rfl
  | inr t =>
    refine ⟨{1},
      { toFun x := x ⟨1, by simp⟩
        map_add' := by simp
        map_smul' := by simp }, ?_⟩
    intro ω
    rfl

lemma bridge_covariance_endpoint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (t : unitInterval) :
    cov[fun ω => B ⟨(t:ℝ),t.property.1⟩ ω-(t:ℝ)*B 1 ω, B 1; μ] = 0 := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  let u : ℝ≥0 := ⟨(t:ℝ), unitInterval.nonneg t⟩
  change cov[fun ω => B u ω - (t:ℝ) * B 1 ω, B 1; μ] = 0
  rw [covariance_fun_sub_left (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    ((hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two.const_mul _)
    (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two,
    covariance_const_mul_left, hB.covariance_eval, hB.covariance_eval]
  simp only [min_self, NNReal.coe_one, mul_one]
  change min (t:ℝ) (1:ℝ) - (t:ℝ) = 0
  rw [min_eq_left t.property.2, sub_self]

lemma bridge_process_indep_endpoint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) :
    IndepFun (fun ω (t : unitInterval) =>
      B ⟨(t:ℝ),t.property.1⟩ ω-(t:ℝ)*B 1 ω) (B 1) μ := by
  have h := (bridge_joint_gaussian hB).indepFun_of_covariance_eq_zero
    (fun t => (hB.aemeasurable _).sub ((hB.aemeasurable 1).const_mul _))
    (fun _ => hB.aemeasurable 1) (fun t _ => bridge_covariance_endpoint hB t)
  exact h.comp measurable_id (measurable_pi_apply ())

lemma indepFun_of_measurableEmbedding_left {Ω E F G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    {μ : Measure Ω} {X : Ω → E} {Y : Ω → F} {f : E → G}
    (hf : MeasurableEmbedding f) (h : IndepFun (f ∘ X) Y μ) : IndepFun X Y μ := by
  simp only [IndepFun, Kernel.IndepFun] at h ⊢
  rw [← MeasurableSpace.comap_comp, hf.comap_eq] at h
  exact h

lemma bridgePath_indep_endpoint {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) :
    IndepFun (bridgePath B) (B 1) μ := by
  let D := TopologicalSpace.denseSeq unitInterval
  let f : C(unitInterval,ℝ) → (ℕ → ℝ) := fun g n => g (D n)
  have hf : MeasurableEmbedding f := by
    apply Continuous.measurableEmbedding
    · apply continuous_pi
      intro n
      fun_prop
    · intro a b hab
      apply ContinuousMap.ext
      exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer
        a.continuous b.continuous hab)
  apply indepFun_of_measurableEmbedding_left hf
  have h := (bridge_process_indep_endpoint hB.toIsPreBrownianReal).comp
    (φ := fun a : unitInterval → ℝ => fun n : ℕ => a (D n))
    (by fun_prop) measurable_id
  apply h.congr ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [bridgePath_ae_eq hB] with ω hω
  funext n
  exact (hω (D n)).symm

lemma gaussian_softCutoff_pos {ε : ℝ} (hε : 0 < ε) :
    0 < ∫ x, softCutoff ε x ∂gaussianReal 0 1 := by
  rw [integral_pos_iff_support_of_nonneg (softCutoff_nonneg ε)
    (softCutoff_integrable aemeasurable_id hε), softCutoff_support hε, pos_iff_ne_zero]
  intro h
  have hv := gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num) h
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hv
  linarith

lemma brownian_softCutoff_pos {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {ε : ℝ} (hε : 0 < ε) :
    0 < ∫ ω, softCutoff ε (B 1 ω) ∂μ := by
  change 0 < ∫ ω, (softCutoff ε ∘ B 1) ω ∂μ
  rw [(hB.hasLaw_eval 1).integral_comp (softCutoff_continuous ε).aestronglyMeasurable]
  exact gaussian_softCutoff_pos hε

lemma brownian_dist_bridge_le {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    dist (brownianPath B ω) (bridgePath B ω) ≤ |B 1 ω| := by
  rw [dist_eq_norm]
  change ‖brownianPath B ω -
    (brownianPath B ω - B 1 ω • (⟨fun t : unitInterval => (t:ℝ),continuous_subtype_val⟩ : C(unitInterval,ℝ)))‖ ≤ _
  rw [sub_sub_cancel, norm_smul,Real.norm_eq_abs]
  apply mul_le_of_le_one_right (abs_nonneg _)
  apply (ContinuousMap.norm_le _ (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro t
  simp only [ContinuousMap.coe_mk, Real.norm_eq_abs, abs_of_nonneg t.property.1]
  exact t.property.2

theorem brownian_soft_bridge_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {F : C(unitInterval,ℝ) → ℝ} {M : ℝ} {L : ℝ≥0}
    (hFM : ∀ f, |F f| ≤ M) (hF : LipschitzWith L F) {ε : ℝ} (hε : 0 < ε) :
    |(∫ ω, F (brownianPath B ω)*softCutoff ε (B 1 ω) ∂μ) /
        (∫ ω, softCutoff ε (B 1 ω) ∂μ) -
      ∫ ω, F (bridgePath B ω) ∂μ| ≤ (L:ℝ)*ε := by
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hFM 0)
  have hX := brownianPath_aemeasurable hB
  have hY := bridgePath_aemeasurable hB
  have hg := softCutoff_integrable (hB.aemeasurable 1) hε
  have hFg (Z : Ω → C(unitInterval,ℝ)) (hZ : AEMeasurable Z μ) :
      Integrable (fun ω => F (Z ω)*softCutoff ε (B 1 ω)) μ := by
    apply (hg.norm.const_mul M).mono'
      ((hF.continuous.aestronglyMeasurable.comp_aemeasurable hZ).mul hg.aestronglyMeasurable)
    filter_upwards [] with ω
    change ‖F (Z ω)*softCutoff ε (B 1 ω)‖ ≤ M*‖softCutoff ε (B 1 ω)‖
    simp only [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (hFM _) (abs_nonneg _)
  have hdiff : Integrable (fun ω =>
      (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω)) μ := by
    have h := (hFg _ hX).sub (hFg _ hY)
    apply h.congr
    filter_upwards [] with ω
    change F (brownianPath B ω)*softCutoff ε (B 1 ω) -
      F (bridgePath B ω)*softCutoff ε (B 1 ω) = _
    ring
  have heq := (bridgePath_indep_endpoint hB).integral_fun_comp_mul_comp
    hY (hB.aemeasurable 1) hF.continuous.aestronglyMeasurable
    (softCutoff_continuous ε).aestronglyMeasurable
  have hb : |∫ ω, (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω) ∂μ| ≤
      (L:ℝ)*ε * ∫ ω, softCutoff ε (B 1 ω) ∂μ := by
    calc
      _ ≤ ∫ ω, |(F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω)| ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun ω => (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω))
      _ ≤ ∫ ω, ((L:ℝ)*ε)*softCutoff ε (B 1 ω) ∂μ := by
        apply integral_mono_ae hdiff.norm (hg.const_mul _)
        filter_upwards [] with ω
        change |(F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω)| ≤ _
        rw [abs_mul,abs_of_nonneg (softCutoff_nonneg _ _)]
        by_cases hgω : softCutoff ε (B 1 ω) = 0
        · simp only [hgω,mul_zero,le_refl]
        apply mul_le_mul_of_nonneg_right _ (softCutoff_nonneg _ _)
        have heω : |B 1 ω| < ε := (softCutoff_pos_iff hε).mp
          (lt_of_le_of_ne (softCutoff_nonneg _ _) (Ne.symm hgω))
        calc
          _ ≤ (L:ℝ)*dist (brownianPath B ω) (bridgePath B ω) := by
            simpa only [Real.dist_eq] using hF.dist_le_mul (brownianPath B ω) (bridgePath B ω)
          _ ≤ (L:ℝ)*ε := mul_le_mul_of_nonneg_left
            ((brownian_dist_bridge_le B ω).trans heω.le) L.coe_nonneg
      _ = _ := integral_const_mul _ _
  rw [show (∫ ω, (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω) ∂μ) =
      (∫ ω, F (brownianPath B ω)*softCutoff ε (B 1 ω) ∂μ) -
      (∫ ω, F (bridgePath B ω) ∂μ)*(∫ ω, softCutoff ε (B 1 ω) ∂μ) by
        rw [show (fun ω => (F (brownianPath B ω)-F (bridgePath B ω))*softCutoff ε (B 1 ω)) =
          (fun ω => F (brownianPath B ω)*softCutoff ε (B 1 ω) -
            F (bridgePath B ω)*softCutoff ε (B 1 ω)) by funext ω; ring,
          integral_sub (hFg _ hX) (hFg _ hY),heq]] at hb
  have hpos := brownian_softCutoff_pos hB.toIsPreBrownianReal hε
  have hform :
      (∫ ω, F (brownianPath B ω)*softCutoff ε (B 1 ω) ∂μ) /
          (∫ ω, softCutoff ε (B 1 ω) ∂μ) - (∫ ω, F (bridgePath B ω) ∂μ) =
      ((∫ ω, F (brownianPath B ω)*softCutoff ε (B 1 ω) ∂μ) -
        (∫ ω, F (bridgePath B ω) ∂μ)*(∫ ω, softCutoff ε (B 1 ω) ∂μ)) /
          (∫ ω, softCutoff ε (B 1 ω) ∂μ) := by
    rw [sub_div,mul_div_cancel_right₀ _ hpos.ne']
  rw [hform,abs_div,abs_of_pos hpos]
  exact (div_le_iff₀ hpos).mpr hb

lemma integral_tendsto_of_tendstoInDistribution
    {ι E Ω' : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ∀ i, Measure (Ω i)} {ν : Measure Ω'} [∀ i, IsProbabilityMeasure (μ i)]
    [IsProbabilityMeasure ν] {l : Filter ι} {X : ∀ i, Ω i → E} {Y : Ω' → E}
    (h : TendstoInDistribution X l Y μ ν) {F : E → ℝ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ x, |F x| ≤ M) :
    Tendsto (fun i => ∫ ω, F (X i ω) ∂μ i) l (𝓝 (∫ ω, F (Y ω) ∂ν)) := by
  let f : BoundedContinuousFunction E ℝ := BoundedContinuousFunction.ofNormedAddCommGroup F hF M hM
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h.tendsto f
  change Tendsto (fun i => ∫ x, f x ∂(μ i).map (X i)) l
    (𝓝 (∫ x, f x ∂ν.map Y)) at hh
  simp_rw [integral_map (h.forall_aemeasurable _) f.continuous.aestronglyMeasurable,
    integral_map h.aemeasurable_limit f.continuous.aestronglyMeasurable] at hh
  exact hh

theorem soft_weighted_tendsto
    {ι E Ω' : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : ∀ i, Measure (Ω i)} {ν : Measure Ω'} [∀ i, IsProbabilityMeasure (μ i)]
    [IsProbabilityMeasure ν] {l : Filter ι} {X : ∀ i, Ω i → E} {Y : Ω' → E}
    (h : TendstoInDistribution X l Y μ ν) {F g : E → ℝ}
    (hF : Continuous F) (hg : Continuous g) {M ε : ℝ}
    (hM : ∀ x, |F x| ≤ M) (hε : 0 < ε)
    (hD : 0 < ∫ ω, softCutoff ε (g (Y ω)) ∂ν) :
    Tendsto (fun i => (∫ ω, F (X i ω)*softCutoff ε (g (X i ω)) ∂μ i) /
      (∫ ω, softCutoff ε (g (X i ω)) ∂μ i)) l
      (𝓝 ((∫ ω, F (Y ω)*softCutoff ε (g (Y ω)) ∂ν) /
        (∫ ω, softCutoff ε (g (Y ω)) ∂ν))) := by
  apply Tendsto.div _ _ hD.ne'
  · apply integral_tendsto_of_tendstoInDistribution h (hF.mul ((softCutoff_continuous ε).comp hg)) (M := M)
    intro x
    change |F x * softCutoff ε (g x)| ≤ M
    rw [abs_mul,abs_of_nonneg (softCutoff_nonneg ε _)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (softCutoff_le_one hε _)).trans (hM x)
  · exact integral_tendsto_of_tendstoInDistribution h ((softCutoff_continuous ε).comp hg) (M := 1)
      (fun x => by change |softCutoff ε (g x)| ≤ 1; rw [abs_of_nonneg (softCutoff_nonneg ε _)]; exact softCutoff_le_one hε _)

lemma tendsto_of_soft_windows {A : ℕ → ℝ} {S : ℝ → ℕ → ℝ} {b : ℝ} {T : ℝ → ℝ}
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hd : ∀ ε > 0, ∀ δ > 0, ∀ᶠ n in atTop, |A n-S ε n| ≤ C*ε+δ)
    (hs : ∀ ε > 0, Tendsto (S ε) atTop (𝓝 (T ε)))
    (ht : ∀ ε > 0, |T ε-b| ≤ D*ε) : Tendsto A atTop (𝓝 b) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  let ε := η/(4*(C+D+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hbound : (C+D)*ε ≤ η/4 := by
    dsimp [ε]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 4*(C+D+1))]
    nlinarith
  have hmid := (Metric.tendsto_nhds.mp (hs ε hε)) (η/4) (by positivity)
  filter_upwards [hd ε hε (η/4) (by positivity),hmid] with n hn hm
  rw [Real.dist_eq] at hm ⊢
  have h₁ := abs_sub_le (A n) (S ε n) b
  have h₂ := abs_sub_le (S ε n) (T ε) b
  have h₃ := ht ε hε
  nlinarith

lemma CriticalEvenOffspring.bridgeConstant_pos (p : CriticalEvenOffspring) :
    0 < p.bridgeConstant := div_pos (Real.sqrt_pos.mpr (mul_pos (by norm_num) Real.pi_pos))
      (mul_pos p.sigma_pos Real.pi_pos)

lemma CriticalEvenOffspring.iid_endpoint_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => Real.sqrt ((2*n+1:ℕ):ℝ) *
      (p.iidLaw (2*n+1)).real {d | totalStep d = -1}) atTop (𝓝 p.bridgeConstant) := by
  obtain ⟨E,hE,hEt,hb⟩ := p.uniform_local_limit
  have hN : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have h2 : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hden : Tendsto (fun n : ℕ => p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)).const_mul_atTop p.sigma_pos
  have hx : Tendsto (fun n : ℕ => (-1:ℝ)/(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have harg : Tendsto (fun n : ℕ => -((-1:ℝ)/(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ)))^2/2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2:ℕ)≠0),neg_zero,zero_div] using (hx.pow 2).neg.div_const 2
  have hp := ((Real.continuous_exp.tendsto 0).comp harg).const_mul p.bridgeConstant
  rw [Real.exp_zero,mul_one] at hp
  let A : ℕ → ℝ := fun n => Real.sqrt ((2*n+1:ℕ):ℝ) *
    (p.iidLaw (2*n+1)).real {d | totalStep d = -1}
  let G : ℕ → ℝ := fun n => p.bridgeConstant *
    Real.exp (-((-1:ℝ)/(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ)))^2/2)
  have herr : ∀ n, |A n-G n| ≤ E (2*n) := by
    intro n
    have hpar : Even (((2*n+1:ℕ):ℤ)+(-1)) := by
      refine ⟨(n:ℤ),?_⟩
      push_cast
      ring
    have hh := hb (2*n) (-1) hpar
    simpa only [A,G,bridgeConstant,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
      Int.cast_neg,Int.cast_one] using hh
  have he : Tendsto (fun n => A n-G n) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero (fun _ => abs_nonneg _) herr (hEt.comp h2)
  have hadd := he.add (show Tendsto G atTop (𝓝 p.bridgeConstant) from hp)
  simpa only [sub_add_cancel,zero_add] using hadd

lemma bridge_soft_numeric {M E B σ S T P K ε : ℝ}
    (hM : 0 ≤ M) (hE : 0 ≤ E) (hB : 0 < B) (hσ : 0 < σ)
    (hS : 0 < S) (hT : 0 < T) (hK : 0 < K) (hε : 0 ≤ ε)
    (hden : B/2 ≤ S*P) (hratio : S ≤ K*T) :
    2*M*((2*E+B*(1+ε*(σ*S))/(σ*T))/T)/P ≤
      (4*M*K/B)*(2*E+(B/σ)/T)+4*M*K^2*ε := by
  have hP : 0 < P := (mul_pos_iff_of_pos_left hS).mp ((half_pos hB).trans_le hden)
  have hTP : 0 < T*P := mul_pos hT hP
  have hi : 1/(T*P) ≤ 2*K/B := by
    rw [div_le_div_iff₀ hTP hB]
    have hh := mul_le_mul_of_nonneg_right hratio hP.le
    nlinarith
  have hn : 2*E+B*(1+ε*(σ*S))/(σ*T) ≤ 2*E+(B/σ)/T+B*ε*K := by
    have hh : S/T ≤ K := (div_le_iff₀ hT).mpr hratio
    have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hB.le hε)
    have he : B*(1+ε*(σ*S))/(σ*T) = (B/σ)/T+B*ε*(S/T) := by
      field_simp
    rw [he]
    linarith
  have hn0 : 0 ≤ 2*E+B*(1+ε*(σ*S))/(σ*T) := by positivity
  calc
    _ = (2*M)*(2*E+B*(1+ε*(σ*S))/(σ*T))*(1/(T*P)) := by ring
    _ ≤ (2*M)*(2*E+B*(1+ε*(σ*S))/(σ*T))*(2*K/B) :=
      mul_le_mul_of_nonneg_left hi (mul_nonneg (by positivity) hn0)
    _ ≤ (2*M)*(2*E+(B/σ)/T+B*ε*K)*(2*K/B) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) (by positivity)
    _ = _ := by field_simp [hB.ne']; ring

lemma exists_bridge_cutoff (t : unitInterval) (ht : (t:ℝ) < 1) :
    ∃ k : ℕ, 2 ≤ k ∧ (k:ℝ)*(t:ℝ) ≤ (k:ℝ)-1 := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ht)
  let k := n+2
  have hk : 2 ≤ k := by omega
  have hnk : 1/(k:ℝ) ≤ 1/((n:ℝ)+1) := by
    apply one_div_le_one_div_of_le (by positivity)
    dsimp [k]
    push_cast
    linarith
  have hh : 1/(k:ℝ) < 1-(t:ℝ) := hnk.trans_lt hn
  have hkr : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hx := (div_lt_iff₀ hkr).mp hh
  refine ⟨k,hk,?_⟩
  nlinarith

lemma bridge_split_parameters {t : unitInterval} {k N : ℕ}
    (hk : 2 ≤ k) (ht : (k:ℝ)*(t:ℝ) ≤ (k:ℝ)-1) (hN : k ≤ N) :
    (N-N/k)+(N/k-1+1)=N ∧
      (N:ℝ)*(t:ℝ) ≤ (N-N/k:ℕ) ∧
      Real.sqrt (N:ℝ) ≤ (k:ℝ)*Real.sqrt ((N/k-1+1:ℕ):ℝ) := by
  have hk0 : 0 < k := by omega
  have hkr : 0 < (k:ℝ) := by positivity
  have hq : 1 ≤ N/k := (Nat.le_div_iff_mul_le hk0).mpr (by simpa using hN)
  have hqN : N/k ≤ N := Nat.div_le_self N k
  have hqr : N/k-1+1=N/k := by omega
  refine ⟨by omega,?_,?_⟩
  · have hmul : (k:ℝ)*((N/k:ℕ):ℝ) ≤ N := by
      exact_mod_cast Nat.mul_div_le N k
    have htN := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg N (α := ℝ))
    have hm : ((N-N/k:ℕ):ℝ) = (N:ℝ)-((N/k:ℕ):ℝ) := Nat.cast_sub hqN
    rw [hm]
    nlinarith
  · rw [hqr]
    have hlt : N < k*(N/k+1) := by
      have hh := Nat.mod_lt N hk0
      have he := Nat.mod_add_div N k
      nlinarith
    have hh : N ≤ 2*k*(N/k) := by nlinarith
    have hNR : (N:ℝ) ≤ 2*(k:ℝ)*((N/k:ℕ):ℝ) := by exact_mod_cast hh
    have hkr2 : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hq0 : (0:ℝ) ≤ ((N/k:ℕ):ℝ) := by positivity
    have hsq := Real.sq_sqrt (Nat.cast_nonneg N (α := ℝ))
    have hsq' := Real.sq_sqrt hq0
    have hKsq : (2*(k:ℝ)) ≤ (k:ℝ)^2 := by nlinarith
    have hNN := hNR.trans (mul_le_mul_of_nonneg_right hKsq hq0)
    have hpos : 0 ≤ (k:ℝ)*Real.sqrt ((N/k:ℕ):ℝ) := by positivity
    nlinarith [Real.sqrt_nonneg (N:ℝ)]

lemma bridge_suffix_tendsto {k : ℕ} (hk : 0 < k) :
    Tendsto (fun n : ℕ => (2*n+1)/k-1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (k*(b+2))] with n hn
  have hq : b+2 ≤ (2*n+1)/k := (Nat.le_div_iff_mul_le hk).mpr (by nlinarith)
  omega

theorem CriticalEvenOffspring.stopped_soft_error (p : CriticalEvenOffspring)
    (t : unitInterval) (ht : (t:ℝ)<1) {F : C(unitInterval,ℝ) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hF : ∀ f, |F f| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε > 0, ∀ δ > 0, ∀ᶠ n in atTop,
      |(∫ d, F (stopPath t (p.iidWalk (2*n+1) d)) ∂p.iidBridgeLaw n) -
        (∫ d, F (stopPath t (p.iidWalk (2*n+1) d))*
          softCutoff ε (p.iidWalk (2*n+1) d 1) ∂p.iidLaw (2*n+1)) /
        (∫ d, softCutoff ε (p.iidWalk (2*n+1) d 1) ∂p.iidLaw (2*n+1))| ≤ C*ε+δ := by
  obtain ⟨k,hk,hkt⟩ := exists_bridge_cutoff t ht
  obtain ⟨E,hE,hEt,hb⟩ := p.prefix_soft_bound
  let r : ℕ → ℕ := fun n => (2*n+1)/k-1
  have hr : Tendsto r atTop atTop := bridge_suffix_tendsto (by omega)
  have hT : Tendsto (fun n => Real.sqrt ((r n+1:ℕ):ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1 |>.comp hr))
  have hres : Tendsto (fun n => (4*M*(k:ℝ)/p.bridgeConstant)*
      (2*E (r n)+(p.bridgeConstant/p.sigma)/Real.sqrt ((r n+1:ℕ):ℝ))) atTop (𝓝 0) := by
    have hh := ((hEt.comp hr).const_mul 2).add
      (hT.const_div_atTop (p.bridgeConstant/p.sigma))
    simpa only [mul_zero,add_zero,Function.comp_apply] using hh.const_mul (4*M*(k:ℝ)/p.bridgeConstant)
  refine ⟨4*M*(k:ℝ)^2,by positivity,?_⟩
  intro ε hε δ hδ
  have hN : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp;omega) tendsto_id
  have hscale : Tendsto (fun n : ℕ => ε*(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ))) atTop atTop :=
    ((Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)).const_mul_atTop
      p.sigma_pos).const_mul_atTop hε
  have hden := p.iid_endpoint_limit.eventually (eventually_ge_nhds
    (show p.bridgeConstant/2 < p.bridgeConstant by linarith [p.bridgeConstant_pos]))
  have hsmall := hres.eventually (eventually_lt_nhds hδ)
  filter_upwards [hN.eventually (eventually_ge_atTop k),hscale.eventually (eventually_gt_atTop 1),
    hden,hsmall] with n hn hw hp he
  let m := (2*n+1)-(2*n+1)/k
  obtain ⟨hlen,htm,hratio⟩ := bridge_split_parameters hk hkt hn
  change m+(r n+1)=2*n+1 at hlen
  change ((2*n+1:ℕ):ℝ)*(t:ℝ) ≤ m at htm
  change Real.sqrt ((2*n+1:ℕ):ℝ) ≤ (k:ℝ)*Real.sqrt ((r n+1:ℕ):ℝ) at hratio
  have htm' : ((m+(r n+1):ℕ):ℝ)*(t:ℝ) ≤ m := by simpa only [hlen] using htm
  have hpar : Even (((m+(r n+1):ℕ):ℤ)-1) := by
    rw [hlen]
    refine ⟨(n:ℤ),?_⟩
    push_cast
    ring
  have hw' : 1 < ε*(p.sigma*Real.sqrt (m+(r n+1))) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (show 1 < ε*(p.sigma*Real.sqrt ((m+(r n+1):ℕ):ℝ)) from hlen ▸ hw)
  have hp' : 0 < (p.iidLaw (m+(r n+1))).real {d | totalStep d = -1} := by
    rw [hlen]
    exact p.iid_endpoint_positive n
  have hh := hb m (r n) ε hε hpar hw' hp'
    (fun a => F (p.prefixWalk m (r n+1) t a)) M hM (fun a => hF _)
  simp_rw [p.prefixWalk_eq m (r n+1) htm'] at hh
  have hcast : (m:ℝ)+((r n:ℝ)+1)=((2*n+1:ℕ):ℝ) := by exact_mod_cast hlen
  rw [hcast] at hh
  rw [hlen] at hh
  simp_rw [← p.iidWalk_endpoint (by omega : 0 < 2*n+1)] at hh
  have hcast' : (r n:ℝ)+1=((r n+1:ℕ):ℝ) := by norm_cast
  rw [hcast'] at hh
  change |_ - _| ≤ 2*M*((2*E (r n)+p.bridgeConstant*
    (1+ε*(p.sigma*Real.sqrt ((2*n+1:ℕ):ℝ)))/
      (p.sigma*Real.sqrt ((r n+1:ℕ):ℝ)))/Real.sqrt ((r n+1:ℕ):ℝ)) /
      (p.iidLaw (2*n+1)).real {d | totalStep d = -1} at hh
  apply hh.trans
  have hnumb := bridge_soft_numeric hM (hE (r n)) p.bridgeConstant_pos p.sigma_pos
    (Real.sqrt_pos.mpr (by positivity : 0 < ((2*n+1:ℕ):ℝ)))
    (Real.sqrt_pos.mpr (by positivity : 0 < ((r n+1:ℕ):ℝ)))
    (by exact_mod_cast (show 0 < k by omega)) hε.le hp hratio
  exact hnumb.trans (by linarith)

theorem CriticalEvenOffspring.stopped_bridge_integral_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν)
    (t : unitInterval) (ht : (t:ℝ)<1) {F : C(unitInterval,ℝ) → ℝ}
    {M : ℝ} {L : ℝ≥0} (hFM : ∀ f, |F f| ≤ M) (hF : LipschitzWith L F) :
    Tendsto (fun n => ∫ d, F (stopPath t (p.iidWalk (2*n+1) d)) ∂p.iidBridgeLaw n)
      atTop (𝓝 (∫ ω, F (stopPath t (bridgePath B ω)) ∂ν)) := by
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hFM 0)
  obtain ⟨C,hC,he⟩ := p.stopped_soft_error t ht hM hFM
  let G : C(unitInterval,ℝ) → ℝ := F ∘ stopPath t
  have hG : LipschitzWith L G := by
    simpa only [mul_one] using hF.comp (stopPath_lipschitz t)
  have hGM : ∀ f, |G f| ≤ M := fun f => hFM _
  have hN : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp;omega) tendsto_id
  have hclt := p.iidWalk_CLT hB
  have hodd : TendstoInDistribution (fun n => p.iidWalk (2*n+1)) atTop
      (brownianPath B) (fun n => p.iidLaw (2*n+1)) ν :=
    ⟨fun n => hclt.forall_aemeasurable (2*n+1),hclt.aemeasurable_limit,hclt.tendsto.comp hN⟩
  have hep : (fun ω => brownianPath B ω 1) =ᵐ[ν] (fun ω => B 1 ω) := by
    filter_upwards [brownianPath_ae_eq hB] with ω hω
    exact hω 1
  have hden (ε : ℝ) : (∫ ω, softCutoff ε (brownianPath B ω 1) ∂ν) =
      ∫ ω, softCutoff ε (B 1 ω) ∂ν :=
    integral_congr_ae (hep.fun_comp (softCutoff ε))
  have hnum (ε : ℝ) : (∫ ω, G (brownianPath B ω)*softCutoff ε (brownianPath B ω 1) ∂ν) =
      ∫ ω, G (brownianPath B ω)*softCutoff ε (B 1 ω) ∂ν := by
    apply integral_congr_ae
    filter_upwards [hep] with ω hω
    rw [hω]
  apply tendsto_of_soft_windows hC L.coe_nonneg he
    (T := fun ε => (∫ ω, G (brownianPath B ω)*softCutoff ε (B 1 ω) ∂ν) /
      (∫ ω, softCutoff ε (B 1 ω) ∂ν))
  · intro ε hε
    have hh := soft_weighted_tendsto hodd hG.continuous
      (show Continuous (fun f : C(unitInterval,ℝ) => f 1) from by fun_prop) hGM hε
      (show 0 < ∫ ω, softCutoff ε (brownianPath B ω 1) ∂ν from by
        rw [hden]; exact brownian_softCutoff_pos hB.toIsPreBrownianReal hε)
    rw [hnum,hden] at hh
    exact hh
  · intro ε hε
    exact brownian_soft_bridge_bound hB hGM hG hε

theorem CriticalEvenOffspring.stopped_bridge_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν)
    (t : unitInterval) (ht : (t:ℝ)<1) :
    TendstoInDistribution (fun n d => stopPath t (p.iidWalk (2*n+1) d)) atTop
      (fun ω => stopPath t (bridgePath B ω)) p.iidBridgeLaw ν := by
  have hX (n : ℕ) : AEMeasurable (fun d => stopPath t (p.iidWalk (2*n+1) d)) (p.iidBridgeLaw n) :=
    ((continuous_stopPath t).measurable.comp (p.iidWalk_measurable _)).aemeasurable
  have hY : AEMeasurable (fun ω => stopPath t (bridgePath B ω)) ν :=
    (continuous_stopPath t).measurable.comp_aemeasurable (bridgePath_aemeasurable hB)
  refine ⟨hX,hY,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨M,hM⟩ ⟨L,hL⟩
  change Tendsto (fun n => ∫ f, F f ∂(p.iidBridgeLaw n).map (fun d => stopPath t (p.iidWalk (2*n+1) d)))
    atTop (𝓝 (∫ f, F f ∂ν.map (fun ω => stopPath t (bridgePath B ω))))
  simp_rw [integral_map (hX _) hL.continuous.aestronglyMeasurable,
    integral_map hY hL.continuous.aestronglyMeasurable]
  apply p.stopped_bridge_integral_limit hB t ht (M := |F 0|+M) (L := L) _ hL
  intro f
  have hh := hM f 0
  rw [Real.dist_eq] at hh
  linarith [abs_sub_abs_le_abs_sub (F f) (F 0)]

lemma hat_reverse (N : ℕ) (i : Fin (N+1)) (t : unitInterval) :
    hat N i.rev.val (unitInterval.symm t) = hat N i.val t := by
  change max 0 (1-|(N:ℝ)*(1-(t:ℝ))-(i.rev.val:ℝ)|) = _
  have hi : i.rev.val=N-i.val := by simp [Fin.val_rev]
  have hile : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  rw [hi,Nat.cast_sub hile]
  have he : (N:ℝ)*(1-(t:ℝ))-((N:ℝ)-i.val) = -((N:ℝ)*(t:ℝ)-i.val) := by ring
  rw [he,abs_neg]
  rfl

lemma interpolation_reverse (N : ℕ) (a : Fin (N+1) → ℝ) (c : ℝ)
    (t : unitInterval) :
    interpolation N (fun i => c-a i.rev) t = c-interpolation N a (unitInterval.symm t) := by
  rw [interpolation_apply,interpolation_apply]
  have hs : (∑ i : Fin (N+1), a i*hat N i.val (unitInterval.symm t)) =
      ∑ i : Fin (N+1), a i.rev*hat N i.val t := by
    rw [← Equiv.sum_comp Fin.revPerm (fun i : Fin (N+1) => a i*hat N i.val (unitInterval.symm t))]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.revPerm_apply,hat_reverse]
  rw [hs]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,hat_sum,mul_one]

lemma reverse_partial_sum (N : ℕ) (x : Fin N → ℝ) (i : Fin (N+1)) :
    (∑ j : Fin N, if j.val < i.val then x j.rev else 0) =
    (∑ j : Fin N, x j)-(∑ j : Fin N, if j.val < i.rev.val then x j else 0) := by
  rw [← Equiv.sum_comp Fin.revPerm (fun j : Fin N => if j.val < i.val then x j.rev else 0),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.revPerm_apply,Fin.rev_rev]
  have hi : i.rev.val=N-i.val := by simp [Fin.val_rev]
  have hj : j.rev.val=N-1-j.val := by simp [Fin.val_rev];omega
  have hb : j.rev.val < i.val ↔ ¬ j.val < i.rev.val := by rw [hi,hj];omega
  by_cases h : j.val < i.rev.val <;> simp only [hb,h,not_true_eq_false,not_false_eq_true,ite_true,ite_false,sub_self,sub_zero]

lemma interpolation_increments_reverse (N : ℕ) (x : Fin N → ℝ) (a : ℝ)
    (t : unitInterval) :
    interpolation N (fun i => (∑ j : Fin N, if j.val < i.val then x j.rev else 0)/a) t =
    (∑ j : Fin N, x j)/a -
      interpolation N (fun i => (∑ j : Fin N, if j.val < i.val then x j else 0)/a)
        (unitInterval.symm t) := by
  simp_rw [reverse_partial_sum,sub_div]
  exact interpolation_reverse N (fun i : Fin (N+1) => (∑ j : Fin N, if j.val < i.val then x j else 0)/a) ((∑ j : Fin N, x j)/a) t

lemma measurePreserving_cond {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {e : Ω → Ω} (he : MeasurePreserving e μ μ) {s : Set Ω}
    (hs : MeasurableSet s) (hes : e ⁻¹' s=s) :
    MeasurePreserving e (cond μ s) (cond μ s) := by
  refine ⟨he.measurable,?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply he.measurable hA,cond_apply hs,cond_apply hs]
  congr 1
  calc
    μ (s ∩ e ⁻¹' A) = μ (e ⁻¹' (s ∩ A)) := by rw [Set.preimage_inter,hes]
    _ = μ (s ∩ A) := he.measure_preimage (hs.inter hA).nullMeasurableSet

lemma reverseArray_apply (N : ℕ) (d : Fin N → ℕ) (i : Fin N) :
    reverseArray N d i = d i.rev := by
  simpa only [Fin.revPerm_apply,Fin.rev_rev,reverseArray] using
    MeasurableEquiv.piCongrLeft_apply_apply Fin.revPerm (β := fun _ : Fin N => ℕ) d i.rev

lemma reverseArray_preserving (μ : Measure ℕ) [SigmaFinite μ] (N : ℕ) :
    MeasurePreserving (reverseArray N) (Measure.pi (fun _ : Fin N => μ))
      (Measure.pi (fun _ : Fin N => μ)) :=
  measurePreserving_piCongrLeft (fun _ : Fin N => μ) Fin.revPerm

lemma reverseArray_sum (N : ℕ) (d : Fin N → ℕ) (f : ℕ → ℤ) :
    (∑ i : Fin N, f (reverseArray N d i)) = ∑ i : Fin N, f (d i) := by
  simpa only [reverseArray_apply,Fin.revPerm_apply] using Equiv.sum_comp Fin.revPerm (fun i : Fin N => f (d i))

lemma reverseArray_cond_preserving (μ : Measure ℕ) [SigmaFinite μ] (N : ℕ)
    (f : ℕ → ℤ) (j : ℤ) :
    MeasurePreserving (reverseArray N)
      (cond (Measure.pi (fun _ : Fin N => μ)) {d | (∑ i : Fin N, f (d i))=j})
      (cond (Measure.pi (fun _ : Fin N => μ)) {d | (∑ i : Fin N, f (d i))=j}) := by
  apply measurePreserving_cond (reverseArray_preserving μ N) (by measurability)
  ext d
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,reverseArray_sum]

lemma stopPath_one (f : C(unitInterval,ℝ)) : stopPath 1 f=f := by
  ext s
  rw [stopPath_apply,min_eq_left (show s ≤ (1:unitInterval) from s.property.2)]

lemma stopPath_zero (f : C(unitInterval,ℝ)) : stopPath 0 f=ContinuousMap.const _ (f 0) := by
  ext s
  simp [stopPath_apply]

lemma continuous_stopPath_time (f : C(unitInterval,ℝ)) : Continuous (fun t => stopPath t f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (continuous_snd.min continuous_fst)

lemma dist_stop_reverse_le (f g : C(unitInterval,ℝ)) (c : ℝ)
    (hfg : ∀ u, g u=c-f (unitInterval.symm u)) (t : unitInterval) :
    dist f (stopPath t f) ≤ 2*‖stopPath (unitInterval.symm t) g‖ := by
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro u
  have hval (v : unitInterval) (hv : v ≤ unitInterval.symm t) :
      |g v| ≤ ‖stopPath (unitInterval.symm t) g‖ := by
    have hh := ContinuousMap.norm_coe_le_norm (stopPath (unitInterval.symm t) g) v
    simpa only [stopPath_apply,min_eq_left hv,Real.norm_eq_abs] using hh
  rw [stopPath_apply,Real.dist_eq]
  by_cases hu : u ≤ t
  · simp only [min_eq_left hu,sub_self,abs_zero]
    positivity
  · have htu : t ≤ u := le_of_not_ge hu
    rw [min_eq_right htu]
    have hv := hval (unitInterval.symm u) ((unitInterval.symm_le_symm).mpr htu)
    have ht' := hval (unitInterval.symm t) le_rfl
    have hdiff : f u-f t = g (unitInterval.symm t)-g (unitInterval.symm u) := by
      rw [hfg,hfg,unitInterval.symm_symm,unitInterval.symm_symm]
      ring
    rw [hdiff]
    exact (abs_sub _ _).trans (by linarith)

lemma earlyTime_pos (j : ℕ) : (0:ℝ)<earlyTime j := by dsimp [earlyTime];positivity

lemma earlyTime_lt_one (j : ℕ) : (earlyTime j:ℝ)<1 := by
  dsimp [earlyTime]
  apply (div_lt_one (by positivity)).mpr
  linarith [Nat.cast_nonneg j (α := ℝ)]

lemma earlyTime_tendsto : Tendsto earlyTime atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  change Tendsto (fun j : ℕ => 1/((j:ℝ)+2)) atTop (𝓝 0)
  exact (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_div_atTop 1

lemma lateTime_tendsto : Tendsto (fun j => unitInterval.symm (earlyTime j)) atTop (𝓝 1) := by
  simpa only [unitInterval.symm_zero,Function.comp_def] using unitInterval.continuous_symm.tendsto 0 |>.comp earlyTime_tendsto

lemma norm_stop_early_tendsto (f : C(unitInterval,ℝ)) (hf : f 0=0) :
    Tendsto (fun j => ‖stopPath (earlyTime j) f‖) atTop (𝓝 0) := by
  have h := ((continuous_stopPath_time f).tendsto 0 |>.comp earlyTime_tendsto).norm
  simpa only [stopPath_zero,hf,ContinuousMap.const_zero,norm_zero,Function.comp_def] using h

lemma stop_late_tendsto (f : C(unitInterval,ℝ)) :
    Tendsto (fun j => stopPath (unitInterval.symm (earlyTime j)) f) atTop (𝓝 f) := by
  simpa only [stopPath_one,Function.comp_def] using (continuous_stopPath_time f).tendsto 1 |>.comp lateTime_tendsto

lemma freezeGauge_continuous (M : ℝ) (L : ℝ≥0) : Continuous (freezeGauge M L) := by
  unfold freezeGauge
  fun_prop

lemma freezeGauge_nonneg {M : ℝ} (hM : 0 ≤ M) (L : ℝ≥0) (f : C(unitInterval,ℝ)) :
    0 ≤ freezeGauge M L f := by unfold freezeGauge;positivity

lemma freezeGauge_abs_le {M : ℝ} (hM : 0 ≤ M) (L : ℝ≥0) (f : C(unitInterval,ℝ)) :
    |freezeGauge M L f| ≤ 2*M := by
  rw [abs_of_nonneg (freezeGauge_nonneg hM L f)]
  exact min_le_left _ _

lemma integral_reverse_freeze_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {e : Ω ≃ᵐ Ω}
    (he : MeasurePreserving e μ μ) {X : Ω → C(unitInterval,ℝ)}
    (hX : AEMeasurable X μ) (c : Ω → ℝ)
    (hrev : ∀ ω u, X (e ω) u=c ω-X ω (unitInterval.symm u))
    {F : C(unitInterval,ℝ) → ℝ} {M : ℝ} {L : ℝ≥0}
    (hFM : ∀ f, |F f| ≤ M) (hF : LipschitzWith L F) (t : unitInterval) :
    |(∫ ω, F (X ω) ∂μ)-(∫ ω, F (stopPath t (X ω)) ∂μ)| ≤
      ∫ ω, freezeGauge M L (stopPath (unitInterval.symm t) (X ω)) ∂μ := by
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hFM 0)
  have hi (Z : Ω → C(unitInterval,ℝ)) (hZ : AEMeasurable Z μ) : Integrable (fun ω => F (Z ω)) μ :=
    Integrable.of_bound (hF.continuous.measurable.comp_aemeasurable hZ).aestronglyMeasurable M
      (ae_of_all μ (fun ω => hFM _))
  have hstop : AEMeasurable (fun ω => stopPath t (X ω)) μ :=
    (continuous_stopPath t).measurable.comp_aemeasurable hX
  have hg : Integrable (fun ω => freezeGauge M L (stopPath (unitInterval.symm t) (X (e ω)))) μ := by
    apply Integrable.of_bound _ (2*M) (ae_of_all μ (fun ω => freezeGauge_abs_le hM L _))
    exact ((freezeGauge_continuous M L).measurable.comp_aemeasurable
      ((continuous_stopPath _).measurable.comp_aemeasurable
        (hX.comp_quasiMeasurePreserving he.quasiMeasurePreserving))).aestronglyMeasurable
  rw [← integral_sub (hi _ hX) (hi _ hstop)]
  apply (show |∫ ω, F (X ω)-F (stopPath t (X ω)) ∂μ| ≤
    ∫ ω, |F (X ω)-F (stopPath t (X ω))| ∂μ by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω => F (X ω)-F (stopPath t (X ω)))).trans
  calc
    _ ≤ ∫ ω, freezeGauge M L (stopPath (unitInterval.symm t) (X (e ω))) ∂μ := by
      apply integral_mono ((hi _ hX).sub (hi _ hstop)).norm hg
      intro ω
      change |F (X ω)-F (stopPath t (X ω))| ≤
        min (2*M) (2*(L:ℝ)*‖stopPath (unitInterval.symm t) (X (e ω))‖)
      apply le_min
      · linarith [abs_sub (F (X ω)) (F (stopPath t (X ω))),hFM (X ω),hFM (stopPath t (X ω))]
      · have hb := dist_stop_reverse_le (X ω) (X (e ω)) (c ω) (hrev ω) t
        have hl := hF.dist_le_mul (X ω) (stopPath t (X ω))
        rw [Real.dist_eq] at hl
        calc
          _ ≤ (L:ℝ)*dist (X ω) (stopPath t (X ω)) := hl
          _ ≤ (L:ℝ)*(2*‖stopPath (unitInterval.symm t) (X (e ω))‖) :=
            mul_le_mul_of_nonneg_left hb L.coe_nonneg
          _ = _ := by ring
    _ = _ := he.integral_comp' (fun ω => freezeGauge M L (stopPath (unitInterval.symm t) (X ω)))

lemma early_gauge_integral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → C(unitInterval,ℝ)}
    (hX : AEMeasurable X μ) (hz : ∀ᵐ ω ∂μ, X ω 0=0) {M : ℝ} (hM : 0 ≤ M) (L : ℝ≥0) :
    Tendsto (fun j => ∫ ω, freezeGauge M L (stopPath (earlyTime j) (X ω)) ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (fun _ : Ω => 2*M)
    (F := fun j ω => freezeGauge M L (stopPath (earlyTime j) (X ω))) (f := fun _ => 0)
    (fun j => ((freezeGauge_continuous M L).measurable.comp_aemeasurable
      ((continuous_stopPath _).measurable.comp_aemeasurable hX)).aestronglyMeasurable)
    (integrable_const _) (fun j => ae_of_all μ (fun ω => freezeGauge_abs_le hM L _)) (by
      filter_upwards [hz] with ω hω
      have h := tendsto_const_nhds.min ((norm_stop_early_tendsto (X ω) hω).const_mul (2*(L:ℝ))) (f := fun _ : ℕ => 2*M)
      simpa only [freezeGauge,mul_zero,min_eq_right (by positivity : 0 ≤ 2*M)] using h)
  simpa only [integral_zero] using hh

lemma late_integral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → C(unitInterval,ℝ)}
    (hX : AEMeasurable X μ) {F : C(unitInterval,ℝ) → ℝ} (hF : Continuous F)
    {M : ℝ} (hFM : ∀ f, |F f| ≤ M) :
    Tendsto (fun j => ∫ ω, F (stopPath (unitInterval.symm (earlyTime j)) (X ω)) ∂μ) atTop
      (𝓝 (∫ ω, F (X ω) ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence (fun _ : Ω => M)
    (fun j => (hF.measurable.comp_aemeasurable
      ((continuous_stopPath _).measurable.comp_aemeasurable hX)).aestronglyMeasurable)
    (integrable_const _) (fun j => ae_of_all μ (fun ω => hFM _))
    (ae_of_all μ (fun ω => (hF.tendsto (X ω)).comp (stop_late_tendsto (X ω))))

lemma CriticalEvenOffspring.iidWalk_reverse (p : CriticalEvenOffspring) (N : ℕ)
    (d : Fin N → ℕ) (t : unitInterval) :
    p.iidWalk N (reverseArray N d) t =
      (∑ j : Fin N, p.standardStep (d j))/Real.sqrt N-
        p.iidWalk N d (unitInterval.symm t) := by
  unfold iidWalk
  simp_rw [reverseArray_apply]
  exact interpolation_increments_reverse N (fun j => p.standardStep (d j)) (Real.sqrt N) t

lemma CriticalEvenOffspring.bridge_reverse_preserving (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (reverseArray (2*n+1)) (p.iidBridgeLaw n) (p.iidBridgeLaw n) :=
  reverseArray_cond_preserving p.law.toMeasure (2*n+1) (fun k => (k:ℤ)-1) (-1)

lemma bridgePath_zero_ae {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν) :
    ∀ᵐ ω ∂ν, bridgePath B ω 0=0 := by
  filter_upwards [bridgePath_ae_eq hB,hB.eval_zero_ae_eq_zero] with ω hω hz
  rw [hω]
  change B 0 ω-(0:ℝ)*B 1 ω=0
  simp [hz]

theorem CriticalEvenOffspring.bridge_integral_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν)
    {F : C(unitInterval,ℝ) → ℝ} {M : ℝ} {L : ℝ≥0}
    (hFM : ∀ f, |F f| ≤ M) (hF : LipschitzWith L F) :
    Tendsto (fun n => ∫ d, F (p.iidWalk (2*n+1) d) ∂p.iidBridgeLaw n) atTop
      (𝓝 (∫ ω, F (bridgePath B ω) ∂ν)) := by
  have hM : 0 ≤ M := (abs_nonneg (F 0)).trans (hFM 0)
  let A : ℕ → ℝ := fun n => ∫ d, F (p.iidWalk (2*n+1) d) ∂p.iidBridgeLaw n
  let S : ℕ → ℕ → ℝ := fun j n => ∫ d,
    F (stopPath (unitInterval.symm (earlyTime j)) (p.iidWalk (2*n+1) d)) ∂p.iidBridgeLaw n
  let b : ℝ := ∫ ω, F (bridgePath B ω) ∂ν
  let a : ℕ → ℝ := fun j => ∫ ω,
    F (stopPath (unitInterval.symm (earlyTime j)) (bridgePath B ω)) ∂ν
  let R : ℕ → ℕ → ℝ := fun j n => ∫ d,
    freezeGauge M L (stopPath (earlyTime j) (p.iidWalk (2*n+1) d)) ∂p.iidBridgeLaw n
  let r : ℕ → ℝ := fun j => ∫ ω,
    freezeGauge M L (stopPath (earlyTime j) (bridgePath B ω)) ∂ν
  have hlate (j : ℕ) : ((unitInterval.symm (earlyTime j):unitInterval):ℝ)<1 := by
    rw [unitInterval.coe_symm_eq]
    linarith [earlyTime_pos j]
  have hS (j : ℕ) : Tendsto (S j) atTop (𝓝 (a j)) :=
    p.stopped_bridge_integral_limit hB _ (hlate j) hFM hF
  have hR (j : ℕ) : Tendsto (R j) atTop (𝓝 (r j)) := by
    exact integral_tendsto_of_tendstoInDistribution (p.stopped_bridge_CLT hB _ (earlyTime_lt_one j))
      (freezeGauge_continuous M L) (freezeGauge_abs_le hM L)
  have hr : Tendsto r atTop (𝓝 0) :=
    early_gauge_integral_tendsto (bridgePath_aemeasurable hB) (bridgePath_zero_ae hB) hM L
  have ha : Tendsto a atTop (𝓝 b) :=
    late_integral_tendsto (bridgePath_aemeasurable hB) hF.continuous hFM
  have he (j n : ℕ) : |A n-S j n| ≤ R j n := by
    have hh := integral_reverse_freeze_bound (p.bridge_reverse_preserving n)
      (p.iidWalk_measurable (2*n+1)).aemeasurable
      (fun d => (∑ i : Fin (2*n+1), p.standardStep (d i))/Real.sqrt ((2*n+1:ℕ):ℝ))
      (p.iidWalk_reverse (2*n+1)) hFM hF (unitInterval.symm (earlyTime j))
    simpa only [unitInterval.symm_symm] using hh
  change Tendsto A atTop (𝓝 b)
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨j,hj,hja⟩ := ((Metric.tendsto_nhds.mp hr (ε/4) (by positivity)).and
    (Metric.tendsto_nhds.mp ha (ε/4) (by positivity))).exists
  rw [Real.dist_eq,sub_zero] at hj
  rw [Real.dist_eq] at hja
  have hSn := Metric.tendsto_nhds.mp (hS j) (ε/4) (by positivity)
  have hRn := (hR j).eventually (eventually_lt_nhds (show r j < r j+ε/4 by linarith))
  filter_upwards [hSn,hRn] with n hn hnr
  rw [Real.dist_eq] at hn ⊢
  have h₁ := abs_sub_le (A n) (S j n) b
  have h₂ := abs_sub_le (S j n) (a j) b
  have h₃ := he j n
  linarith [le_abs_self (r j)]

theorem CriticalEvenOffspring.iidBridge_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B ν) :
    TendstoInDistribution (fun n => p.iidWalk (2*n+1)) atTop
      (bridgePath B) p.iidBridgeLaw ν := by
  have hX (n : ℕ) : AEMeasurable (p.iidWalk (2*n+1)) (p.iidBridgeLaw n) :=
    (p.iidWalk_measurable _).aemeasurable
  have hY := bridgePath_aemeasurable hB
  refine ⟨hX,hY,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨M,hM⟩ ⟨L,hL⟩
  change Tendsto (fun n => ∫ f, F f ∂(p.iidBridgeLaw n).map (p.iidWalk (2*n+1))) atTop
    (𝓝 (∫ f, F f ∂ν.map (bridgePath B)))
  simp_rw [integral_map (hX _) hL.continuous.aestronglyMeasurable,
    integral_map hY hL.continuous.aestronglyMeasurable]
  apply p.bridge_integral_limit hB (M := |F 0|+M) (L := L) _ hL
  intro f
  have hh := hM f 0
  rw [Real.dist_eq] at hh
  linarith [abs_sub_abs_le_abs_sub (F f) (F 0)]

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_Vervaat
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma clipTime_coe (t : unitInterval) : clipTime (t:ℝ)=t :=
  projIcc_val _ t

lemma clipTime_of_nonpos {x : ℝ} (hx : x ≤ 0) : clipTime x=0 :=
  projIcc_of_le_left _ hx

lemma clipTime_of_one_le {x : ℝ} (hx : 1 ≤ x) : clipTime x=1 :=
  projIcc_of_right_le _ hx

lemma cyclePath_zero (c : unitInterval) (f : C(unitInterval,ℝ)) : cyclePath c f 0=0 := by
  change f (clipTime ((c:ℝ)+0))+f (clipTime ((c:ℝ)+0-1))-f 0-f c=0
  rw [add_zero,clipTime_coe,clipTime_of_nonpos (by linarith [c.property.2])]
  ring

lemma cyclePath_apply_left (c t : unitInterval) (f : C(unitInterval,ℝ))
    (h : (c:ℝ)+(t:ℝ) ≤ 1) :
    cyclePath c f t=f ⟨(c:ℝ)+(t:ℝ),add_nonneg c.property.1 t.property.1,h⟩-f c := by
  change f (clipTime ((c:ℝ)+(t:ℝ)))+f (clipTime ((c:ℝ)+(t:ℝ)-1))-f 0-f c=_
  rw [show clipTime ((c:ℝ)+(t:ℝ))=⟨(c:ℝ)+(t:ℝ),add_nonneg c.property.1 t.property.1,h⟩ from
    projIcc_of_mem _ ⟨add_nonneg c.property.1 t.property.1,h⟩,
    clipTime_of_nonpos (by linarith)]
  ring

lemma cyclePath_apply_right (c t : unitInterval) (f : C(unitInterval,ℝ))
    (h : 1 ≤ (c:ℝ)+(t:ℝ)) :
    cyclePath c f t=f 1+f ⟨(c:ℝ)+(t:ℝ)-1,by linarith,by linarith [c.property.2,t.property.2]⟩-f 0-f c := by
  change f (clipTime ((c:ℝ)+(t:ℝ)))+f (clipTime ((c:ℝ)+(t:ℝ)-1))-f 0-f c=_
  rw [clipTime_of_one_le h]
  have hh : clipTime ((c:ℝ)+(t:ℝ)-1)=
      ⟨(c:ℝ)+(t:ℝ)-1,by linarith,by linarith [c.property.2,t.property.2]⟩ :=
    projIcc_of_mem zero_le_one ⟨by linarith,by linarith [c.property.2,t.property.2]⟩
  rw [hh]

lemma continuous_cyclePath : Continuous (fun z : unitInterval × C(unitInterval,ℝ) => cyclePath z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (unitInterval × C(unitInterval,ℝ)) × unitInterval =>
    z.1.2 (clipTime ((z.1.1:ℝ)+(z.2:ℝ)))+
      z.1.2 (clipTime ((z.1.1:ℝ)+(z.2:ℝ)-1))-z.1.2 0-z.1.2 z.1.1)
  have h₁ : Continuous (fun z : (unitInterval × C(unitInterval,ℝ)) × unitInterval =>
    clipTime ((z.1.1:ℝ)+(z.2:ℝ))) := by fun_prop
  have h₂ : Continuous (fun z : (unitInterval × C(unitInterval,ℝ)) × unitInterval =>
    clipTime ((z.1.1:ℝ)+(z.2:ℝ)-1)) := by fun_prop
  apply Continuous.sub _ (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk
    (continuous_fst.comp continuous_fst)))
  apply Continuous.sub _ (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk continuous_const))
  exact (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk h₁)).add
    (continuous_eval.comp ((continuous_snd.comp continuous_fst).prodMk h₂))

lemma minTime_spec (f : C(unitInterval,ℝ)) : ∀ t, f (minTime f) ≤ f t :=
  (exists_firstMinimum f).choose_spec.1

lemma minTime_first (f : C(unitInterval,ℝ)) (d : unitInterval) (hd : ∀ t, f d ≤ f t) :
    minTime f ≤ d := (exists_firstMinimum f).choose_spec.2 d hd

lemma minimum_stable {f : C(unitInterval,ℝ)} {c : unitInterval}
    (hc : UniqueMinimum f c) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ>0, ∀ g : C(unitInterval,ℝ), dist g f<δ →
      ∀ d : unitInterval, (∀ t, g d ≤ g t) → dist d c<ε := by
  let K : Set unitInterval := {d | ε ≤ dist d c}
  have hK : IsCompact K := (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  have hgap : ∀ d ∈ K, f c < f d := by
    intro d hd
    apply lt_of_le_of_ne (hc.1 d)
    intro heq
    have hdc := hc.2 d heq.symm
    subst d
    exact (not_le_of_gt hε) (by simpa [K] using hd)
  obtain ⟨a,ha,hKa⟩ := hK.exists_forall_le' f.continuous.continuousOn hgap
  refine ⟨(a-f c)/3,by linarith,?_⟩
  intro g hg d hd
  by_contra hdc
  have hda : a ≤ f d := hKa d (not_lt.mp hdc)
  have hh (u : unitInterval) : |g u-f u| < (a-f c)/3 :=
    (show |g u-f u| ≤ dist g f from by simpa only [Real.dist_eq] using
      (ContinuousMap.dist_apply_le_dist (f := g) (g := f) u)).trans_lt hg
  have h₁ := hh d
  have h₂ := hh c
  have h₃ := hd c
  have h₄ := abs_lt.mp h₁
  have h₅ := abs_lt.mp h₂
  linarith

lemma continuousAt_minTime {f : C(unitInterval,ℝ)} {c : unitInterval}
    (hc : UniqueMinimum f c) : ContinuousAt minTime f := by
  have heq : minTime f=c := hc.2 _ (le_antisymm (minTime_spec f c) (hc.1 _))
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hδ'⟩ := minimum_stable hc hε
  exact ⟨δ,hδ,fun g hg => heq ▸ hδ' g hg (minTime g) (minTime_spec g)⟩

lemma continuousAt_vervaat {f : C(unitInterval,ℝ)} {c : unitInterval}
    (hc : UniqueMinimum f c) : ContinuousAt vervaat f :=
  continuous_cyclePath.continuousAt.comp ((continuousAt_minTime hc).prodMk continuousAt_id)

lemma restrictedMin_spec (K : Set unitInterval) (hK : IsCompact K) (hne : K.Nonempty)
    (f : C(unitInterval,ℝ)) :
    (∃ c ∈ K, restrictedMin K hK hne f=f c) ∧ ∀ c ∈ K, restrictedMin K hK hne f ≤ f c := by
  have h := (hK.exists_isMinOn hne f.continuous.continuousOn).choose_spec
  exact ⟨⟨_,h.1,rfl⟩,h.2⟩

lemma restrictedMin_lipschitz (K : Set unitInterval) (hK : IsCompact K) (hne : K.Nonempty) :
    LipschitzWith 1 (restrictedMin K hK hne) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul,Real.dist_eq]
  obtain ⟨⟨a,ha,hea⟩,hfa⟩ := restrictedMin_spec K hK hne f
  obtain ⟨⟨b,hb,heb⟩,hgb⟩ := restrictedMin_spec K hK hne g
  have h₁ := hfa b hb
  have h₂ := hgb a ha
  have h₃ := ContinuousMap.dist_apply_le_dist (f := f) (g := g) a
  have h₄ := ContinuousMap.dist_apply_le_dist (f := f) (g := g) b
  rw [Real.dist_eq] at h₃ h₄
  rw [abs_le]
  constructor <;> linarith [le_abs_self (f a-g a),neg_abs_le (f a-g a),
    le_abs_self (f b-g b),neg_abs_le (f b-g b)]

lemma minTime_le_iff (a : unitInterval) (f : C(unitInterval,ℝ)) :
    minTime f ≤ a ↔ restrictedMin (Iic a) isClosed_Iic.isCompact ⟨0,a.property.1⟩ f =
      restrictedMin univ isCompact_univ univ_nonempty f := by
  obtain ⟨⟨b,hb,heb⟩,hgb⟩ := restrictedMin_spec (Iic a) isClosed_Iic.isCompact ⟨0,a.property.1⟩ f
  obtain ⟨⟨c,_,hec⟩,hfc⟩ := restrictedMin_spec univ isCompact_univ univ_nonempty f
  constructor
  · intro ha
    apply le_antisymm
    · exact (hgb (minTime f) ha).trans ((minTime_spec f c).trans_eq hec.symm)
    · exact hfc b (mem_univ b) |>.trans_eq heb.symm
  · intro hh
    apply (minTime_first f b _).trans hb
    intro t
    rw [← heb,hh]
    exact hfc t (mem_univ t)

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_4
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitInterval_solutions_4
lemma measurable_minTime : Measurable minTime := by
  apply measurable_of_Iic
  intro a
  have heq : minTime ⁻¹' Iic a =
    {f | restrictedMin (Iic a) isClosed_Iic.isCompact ⟨0,a.property.1⟩ f =
      restrictedMin univ isCompact_univ univ_nonempty f} := by
    ext f
    exact minTime_le_iff a f
  rw [heq]
  exact measurableSet_eq_fun (restrictedMin_lipschitz _ _ _).continuous.measurable
    (restrictedMin_lipschitz _ _ _).continuous.measurable

lemma measurable_vervaat : Measurable vervaat :=
  continuous_cyclePath.measurable.comp (measurable_minTime.prodMk measurable_id)

lemma reversePath_apply (f : C(unitInterval,ℝ)) (t : unitInterval) :
    reversePath f t=f (unitInterval.symm t) := rfl

lemma reversePath_lipschitz : LipschitzWith 1 reversePath := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  exact ContinuousMap.dist_apply_le_dist (unitInterval.symm t)

lemma lastMinTime_spec (f : C(unitInterval,ℝ)) : ∀ t, f (lastMinTime f) ≤ f t := by
  intro t
  have hh := minTime_spec (reversePath f) (unitInterval.symm t)
  simpa only [reversePath_apply,unitInterval.symm_symm,lastMinTime] using hh

lemma lastMinTime_last (f : C(unitInterval,ℝ)) (d : unitInterval) (hd : ∀ t, f d ≤ f t) :
    d ≤ lastMinTime f := by
  apply unitInterval.symm_le_symm.mp
  simp only [lastMinTime,unitInterval.symm_symm]
  apply minTime_first
  intro t
  simpa only [reversePath_apply,unitInterval.symm_symm] using hd (unitInterval.symm t)

lemma measurable_lastMinTime : Measurable lastMinTime :=
  unitInterval.continuous_symm.measurable.comp (measurable_minTime.comp reversePath_lipschitz.continuous.measurable)

lemma hasUniqueMinimum_iff (f : C(unitInterval,ℝ)) :
    HasUniqueMinimum f ↔ minTime f=lastMinTime f := by
  constructor
  · rintro ⟨c,hc⟩
    have hh (d : unitInterval) (hd : ∀ t, f d ≤ f t) : d=c :=
      hc.2 d (le_antisymm (hd c) (hc.1 d))
    exact (hh _ (minTime_spec f)).trans (hh _ (lastMinTime_spec f)).symm
  · intro heq
    refine ⟨minTime f,minTime_spec f,?_⟩
    intro t ht
    have hh : ∀ s, f t ≤ f s := fun s => ht.trans_le (minTime_spec f s)
    exact le_antisymm ((lastMinTime_last f t hh).trans_eq heq.symm) (minTime_first f t hh)

lemma measurableSet_hasUniqueMinimum : MeasurableSet {f : C(unitInterval,ℝ) | HasUniqueMinimum f} := by
  simp_rw [hasUniqueMinimum_iff]
  exact measurableSet_eq_fun measurable_minTime measurable_lastMinTime

lemma tiltPath_apply (a : ℝ) (f : C(unitInterval,ℝ)) (t : unitInterval) :
    tiltPath a f t=f t+a*(t:ℝ) := rfl

lemma continuous_tiltPath : Continuous (fun z : C(unitInterval,ℝ) × ℝ => tiltPath z.2 z.1) :=
  continuous_fst.add (continuous_snd.smul continuous_const)

lemma tiltMinimum_antitone {f : unitInterval → ℝ} {a b : ℝ} (hab : a<b)
    {s t : unitInterval} (hs : TiltMinimum f a s) (ht : TiltMinimum f b t) : t ≤ s := by
  have h₁ := hs t
  have h₂ := ht s
  change (t:ℝ) ≤ (s:ℝ)
  by_contra hts
  have hp : 0 < (b-a)*((t:ℝ)-(s:ℝ)) := mul_pos (sub_pos.mpr hab) (sub_pos.mpr (lt_of_not_ge hts))
  nlinarith

theorem countable_badTilts (f : unitInterval → ℝ) :
    Set.Countable {a : ℝ | ∃ s t : unitInterval, s<t ∧ TiltMinimum f a s ∧ TiltMinimum f a t} := by
  let D := {a : ℝ // ∃ s t : unitInterval, s<t ∧ TiltMinimum f a s ∧ TiltMinimum f a t}
  have hex (a : D) : ∃ q : ℚ, ∃ s t : unitInterval,
      (s:ℝ)<q ∧ (q:ℝ)<t ∧ TiltMinimum f a s ∧ TiltMinimum f a t := by
    obtain ⟨s,t,hst,hs,ht⟩ := a.property
    obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn (show (s:ℝ)<t from hst)
    exact ⟨q,s,t,hq₁,hq₂,hs,ht⟩
  choose q hq using hex
  have hinj : Function.Injective q := by
    intro a b hab
    by_contra hne
    obtain ⟨s,t,hsq,hqt,hs,ht⟩ := hq a
    obtain ⟨u,v,huq,hqv,hu,hv⟩ := hq b
    have hne' : (a:ℝ) ≠ (b:ℝ) := fun hh => hne (Subtype.ext hh)
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · have hh := tiltMinimum_antitone hlt hs hv
      have : (v:ℝ) ≤ s := hh
      rw [hab] at hsq
      linarith
    · have hh := tiltMinimum_antitone hgt hu ht
      have : (t:ℝ) ≤ u := hh
      rw [hab] at hqt
      linarith
  exact @Set.to_countable ℝ _ (Function.Injective.countable hinj)

lemma not_unique_iff_two_minima (f : C(unitInterval,ℝ)) :
    ¬ HasUniqueMinimum f ↔ ∃ s t, s<t ∧ (∀ u, f s ≤ f u) ∧ (∀ u, f t ≤ f u) := by
  rw [hasUniqueMinimum_iff]
  constructor
  · intro h
    exact ⟨minTime f,lastMinTime f,lt_of_le_of_ne (minTime_first f _ (lastMinTime_spec f)) h,
      minTime_spec f,lastMinTime_spec f⟩
  · rintro ⟨s,t,hst,hs,ht⟩ heq
    have h₁ := minTime_first f s hs
    have h₂ := lastMinTime_last f t ht
    rw [heq] at h₁
    exact (not_le_of_gt hst) (h₂.trans h₁)

theorem ae_unique_minimum_tilt (μ : Measure C(unitInterval,ℝ)) (ν : Measure ℝ)
    [SFinite μ] [SFinite ν] [NullSingletonClass ν] :
    ∀ᵐ z ∂μ.prod ν, HasUniqueMinimum (tiltPath z.2 z.1) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_hasUniqueMinimum.preimage continuous_tiltPath.measurable)).mpr
  apply ae_of_all
  intro f
  rw [ae_iff]
  change ν {a | ¬ HasUniqueMinimum (tiltPath a f)}=0
  have heq : {a | ¬ HasUniqueMinimum (tiltPath a f)}=
      {a : ℝ | ∃ s t : unitInterval, s<t ∧ TiltMinimum f a s ∧ TiltMinimum f a t} := by
    ext a
    simp only [mem_ofPred_eq,not_unique_iff_two_minima,TiltMinimum,tiltPath_apply]
  rw [heq]
  exact (countable_badTilts f).measure_zero ν

theorem IndepFun.ae_unique_minimum_tilt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → C(unitInterval,ℝ)} {A : Ω → ℝ}
    (hX : AEMeasurable X P) (hA : AEMeasurable A P) (h : IndepFun X A P)
    [NullSingletonClass (P.map A)] :
    ∀ᵐ ω ∂P, HasUniqueMinimum (tiltPath (A ω) (X ω)) := by
  have heq := h.map_prod_eq_prod_map_map hX hA
  have hu := FKCRT.TreeCoding.ae_unique_minimum_tilt (P.map X) (P.map A)
  rw [← heq] at hu
  exact (ae_map_iff (hX.prodMk hA)
    (measurableSet_hasUniqueMinimum.preimage continuous_tiltPath.measurable)).mp hu

lemma indepFun_path_of_coords {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → C(unitInterval,ℝ)} {A : Ω → ℝ}
    (h : IndepFun (fun ω t => X ω t) A P) : IndepFun X A P := by
  let D := TopologicalSpace.denseSeq unitInterval
  let f : C(unitInterval,ℝ) → (ℕ → ℝ) := fun g n => g (D n)
  have hf : MeasurableEmbedding f := by
    apply Continuous.measurableEmbedding
    · apply continuous_pi
      intro n
      fun_prop
    · intro a b hab
      apply ContinuousMap.ext
      exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer
        a.continuous b.continuous hab)
  exact indepFun_of_measurableEmbedding_left hf (h.comp
    (φ := fun a : unitInterval → ℝ => fun n : ℕ => a (D n)) (by fun_prop) measurable_id)

lemma prefixTimePath_apply (a t : unitInterval) (f : C(unitInterval,ℝ)) :
    prefixTimePath a f t=f (a*t) := rfl

lemma prefixTimePath_lipschitz (a : unitInterval) : LipschitzWith 1 (prefixTimePath a) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul]
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro t
  exact ContinuousMap.dist_apply_le_dist (a*t)

lemma prefixResidual_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (a : unitInterval) :
    AEMeasurable (prefixResidual B a) P :=
  ((prefixTimePath_lipschitz a).continuous.measurable.comp_aemeasurable
    (brownianPath_aemeasurable hB)).sub ((hB.aemeasurable _).smul aemeasurable_const)

lemma prefixResidual_ae_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (a : unitInterval) :
    ∀ᵐ ω ∂P, ∀ t : unitInterval, prefixResidual B a ω t=
      B ⟨(a:ℝ)*(t:ℝ),mul_nonneg a.property.1 t.property.1⟩ ω-
        (t:ℝ)*B ⟨(a:ℝ),a.property.1⟩ ω := by
  filter_upwards [brownianPath_ae_eq hB] with ω hω
  intro t
  simp only [prefixResidual,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
    prefixTimePath_apply,ContinuousMap.coe_mk,smul_eq_mul,hω,Set.Icc.coe_mul,mul_comm]

lemma prefixResidual_joint_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a : unitInterval) :
    IsGaussianProcess (Sum.elim
      (fun (t : unitInterval) ω =>
        B ⟨(a:ℝ)*(t:ℝ),mul_nonneg a.property.1 t.property.1⟩ ω-
          (t:ℝ)*B ⟨(a:ℝ),a.property.1⟩ ω)
      (fun (_ : Unit) ω => bridgeAt B a ω)) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro s
  cases s with
  | inl t =>
    let u : ℝ≥0 := ⟨(a:ℝ)*(t:ℝ),mul_nonneg a.property.1 t.property.1⟩
    let v : ℝ≥0 := ⟨(a:ℝ),a.property.1⟩
    refine ⟨{u,v},
      { toFun x := x ⟨u,by simp⟩-(t:ℝ)*x ⟨v,by simp⟩
        map_add' x y := by simp only [Pi.add_apply]; ring
        map_smul' c x := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring },?_⟩
    intro ω
    rfl
  | inr t =>
    let v : ℝ≥0 := ⟨(a:ℝ),a.property.1⟩
    refine ⟨{v,1},
      { toFun x := x ⟨v,by simp⟩-(a:ℝ)*x ⟨1,by simp⟩
        map_add' x y := by simp only [Pi.add_apply]; ring
        map_smul' c x := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring },?_⟩
    intro ω
    rfl

lemma prefixResidual_covariance_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a t : unitInterval) :
    cov[fun ω => B ⟨(a:ℝ)*(t:ℝ),mul_nonneg a.property.1 t.property.1⟩ ω-
      (t:ℝ)*B ⟨(a:ℝ),a.property.1⟩ ω,bridgeAt B a; P]=0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (s : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  let u : ℝ≥0 := ⟨(a:ℝ)*(t:ℝ), mul_nonneg (unitInterval.nonneg a) (unitInterval.nonneg t)⟩
  let v : ℝ≥0 := ⟨(a:ℝ), unitInterval.nonneg a⟩
  change cov[fun ω => B u ω - (t:ℝ)*B v ω,
    fun ω => B v ω - (a:ℝ)*B 1 ω; P] = 0
  rw [covariance_fun_sub_fun_sub (hm _) ((hm _).const_mul _) (hm _) ((hm _).const_mul _),
    covariance_const_mul_right,covariance_const_mul_left,covariance_const_mul_left,
    covariance_const_mul_right]
  simp only [hB.covariance_eval]
  have h₁ : (a:ℝ)*(t:ℝ) ≤ a := mul_le_of_le_one_right a.property.1 t.property.2
  have h₂ : (a:ℝ)*(t:ℝ) ≤ 1 := h₁.trans a.property.2
  change min ((a:ℝ)*(t:ℝ)) (a:ℝ)-(a:ℝ)*min ((a:ℝ)*(t:ℝ)) 1-
    (t:ℝ)*min (a:ℝ) (a:ℝ)+(t:ℝ)*((a:ℝ)*min (a:ℝ) 1)=0
  rw [min_eq_left h₁,min_eq_left h₂,min_self,min_eq_left a.property.2]
  ring

lemma prefixResidual_indep_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (a : unitInterval) :
    IndepFun (prefixResidual B a) (bridgeAt B a) P := by
  apply indepFun_path_of_coords
  have hi := (prefixResidual_joint_gaussian hB.toIsPreBrownianReal a).indepFun_of_covariance_eq_zero
    (fun t => (hB.aemeasurable _).sub ((hB.aemeasurable _).const_mul _))
    (fun _ => (hB.aemeasurable _).sub ((hB.aemeasurable _).const_mul _))
    (fun t _ => prefixResidual_covariance_bridgeAt hB.toIsPreBrownianReal a t)
  have he := hi.comp measurable_id (measurable_pi_apply ())
  apply he.congr ?_ (Filter.EventuallyEq.rfl)
  filter_upwards [prefixResidual_ae_eq hB a] with ω hω
  exact funext (fun t => (hω t).symm)

lemma variance_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a : unitInterval) :
    Var[bridgeAt B a; P]=(a:ℝ)*(1-(a:ℝ)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (s : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  let u : ℝ≥0 := ⟨(a:ℝ), unitInterval.nonneg a⟩
  change Var[fun ω => B u ω - (a:ℝ)*B 1 ω; P] = _
  rw [variance_fun_sub (hm _) ((hm _).const_mul _),variance_const_mul,
    covariance_const_mul_right,← covariance_self (hm _).aemeasurable,
    ← covariance_self (hm _).aemeasurable]
  simp only [hB.covariance_eval,min_self,NNReal.coe_one]
  change (a:ℝ)-2*((a:ℝ)*min (a:ℝ) 1)+(a:ℝ)^2*1=_
  rw [min_eq_left a.property.2]
  ring

lemma bridgeAt_nullSingletonClass {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {a : unitInterval}
    (ha₀ : 0 < a) (ha₁ : a < 1) : NullSingletonClass (P.map (bridgeAt B a)) := by
  have hg := (prefixResidual_joint_gaussian hB.toIsPreBrownianReal a).hasGaussianLaw_eval (Sum.inr ())
  change HasGaussianLaw (bridgeAt B a) P at hg
  rw [hg.map_eq_gaussianReal,variance_bridgeAt hB.toIsPreBrownianReal a]
  apply nullSingletonClass_gaussianReal
  exact ne_of_gt (Real.toNNReal_pos.mpr (mul_pos ha₀ (sub_pos.mpr ha₁)))

theorem bridge_prefix_unique_minimum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {a : unitInterval}
    (ha₀ : 0 < a) (ha₁ : a < 1) :
    ∀ᵐ ω ∂P, HasUniqueMinimum (prefixTimePath a (bridgePath B ω)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have := bridgeAt_nullSingletonClass hB ha₀ ha₁
  have hA : AEMeasurable (bridgeAt B a) P :=
    (hB.aemeasurable _).sub ((hB.aemeasurable _).const_mul _)
  have hu := IndepFun.ae_unique_minimum_tilt (prefixResidual_aemeasurable hB a) hA
    (prefixResidual_indep_bridgeAt hB a)
  filter_upwards [hu] with ω hω
  convert hω using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousMap.ext
  intro t
  simp only [prefixTimePath_apply,bridgePath,prefixResidual,tiltPath_apply,bridgeAt,
    ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.coe_mk,smul_eq_mul,Set.Icc.coe_mul]
  ring

theorem gaussianProcess_map_eq {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : T → Ω → ℝ} (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y P)
    (hm : ∀ t, P[X t]=P[Y t])
    (hc : ∀ s t, cov[X s,X t; P]=cov[Y s,Y t; P])
    (hXm : AEMeasurable (fun ω t => X t ω) P)
    (hYm : AEMeasurable (fun ω t => Y t ω) P) :
    P.map (fun ω t => X t ω)=P.map (fun ω t => Y t ω) := by
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  apply (map_eq_iff_forall_finset_map_restrict_eq hXm hYm).mpr
  intro I
  apply (MeasurableEquiv.toLp 2 (I → ℝ)).map_measurableEquiv_injective
  rw [MeasurableEquiv.coe_toLp, ← PiLp.coe_symm_continuousLinearEquiv 2 ℝ]
  have := (hX.hasGaussianLaw I).isGaussian_map
  have := (hY.hasGaussianLaw I).isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map,integral_map,integral_map,integral_map]
    · simp only [id_eq]
      rw [ContinuousLinearEquiv.integral_comp_comm,
        ContinuousLinearEquiv.integral_comp_comm]
      congr 1
      ext i
      rw [eval_integral,eval_integral]
      · exact hm i
      · exact fun j => (hY.hasGaussianLaw_eval j).integrable
      · exact fun j => (hX.hasGaussianLaw_eval j).integrable
    any_goals fun_prop
    · exact AEMeasurable.of_eval fun _ => hY.aemeasurable _
    · exact AEMeasurable.of_eval fun _ => hX.aemeasurable _
  · rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_of_isSymm isPosSemidef_covarianceBilin.isSymm
      isPosSemidef_covarianceBilin.isSymm fun x => ?_
    simp only [ContinuousLinearMap.toBilinForm_apply]
    rw [PiLp.coe_symm_continuousLinearEquiv,covarianceBilin_apply_pi,covarianceBilin_apply_pi]
    · congrm ∑ i, ∑ j, _ * ?_
      rw [covariance_map,covariance_map]
      · exact hc _ _
      any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
      · exact AEMeasurable.of_eval fun _ => hY.aemeasurable _
      · exact AEMeasurable.of_eval fun _ => hX.aemeasurable _
    · exact fun i => ((hY.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two
    · exact fun i => ((hX.hasGaussianLaw I).isGaussian_map.hasGaussianLaw_id.eval i).memLp_two

lemma path_law_eq_of_coords {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X Y : Ω → C(unitInterval,ℝ)} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (heq : P.map (fun ω (n : ℕ) => X ω (TopologicalSpace.denseSeq unitInterval n))=
      P.map (fun ω (n : ℕ) => Y ω (TopologicalSpace.denseSeq unitInterval n))) :
    P.map X=P.map Y := by
  let f : C(unitInterval,ℝ) → (ℕ → ℝ) := fun g n => g (TopologicalSpace.denseSeq unitInterval n)
  have hf : MeasurableEmbedding f := by
    apply Continuous.measurableEmbedding
    · apply continuous_pi
      intro n
      fun_prop
    · intro a b hab
      apply ContinuousMap.ext
      exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer
        a.continuous b.continuous hab)
  apply hf.map_injective
  rw [AEMeasurable.map_map_of_aemeasurable hf.measurable.aemeasurable hX,
    AEMeasurable.map_map_of_aemeasurable hf.measurable.aemeasurable hY]
  exact heq

lemma cyclePath_apply_closed (c t : unitInterval) (f : C(unitInterval,ℝ))
    (hf : f 0=f 1) : cyclePath c f t=f (circleTime c t)-f c := by
  unfold circleTime
  split_ifs with h
  · exact cyclePath_apply_left c t f h
  · rw [cyclePath_apply_right c t f (le_of_not_ge h)]
    rw [hf]
    ring

lemma bbCov_comm (s t : ℝ) : bbCov s t=bbCov t s := by simp [bbCov,min_comm,mul_comm]

lemma circleTime_covariance (c s t : unitInterval) :
    bbCov (circleTime c s) (circleTime c t)-bbCov (circleTime c s) c-
      bbCov c (circleTime c t)+bbCov c c=bbCov s t := by
  wlog hst : s ≤ t generalizing s t
  · rw [bbCov_comm (s:ℝ) (t:ℝ)]
    rw [bbCov_comm (circleTime c s) (circleTime c t),bbCov_comm (circleTime c s) c,
      bbCov_comm c (circleTime c t)]
    convert this t s (le_of_not_ge hst) using 1 <;> first | rfl | ring
  have hc₀ := c.property.1
  have hc₁ := c.property.2
  have hs₀ := s.property.1
  have hs₁ := s.property.2
  have ht₀ := t.property.1
  have ht₁ := t.property.2
  have hst' : (s:ℝ) ≤ t := hst
  by_cases ht : (c:ℝ)+(t:ℝ) ≤ 1
  · have hs : (c:ℝ)+(s:ℝ) ≤ 1 := by linarith
    simp only [circleTime,dite_eq_left hs,dite_eq_left ht,bbCov,min_self]
    rw [min_eq_left (by linarith),min_eq_right (by linarith),min_eq_left (by linarith),
      min_eq_left hst']
    ring
  · by_cases hs : (c:ℝ)+(s:ℝ) ≤ 1
    · simp only [circleTime,dite_eq_left hs,dite_eq_right ht,bbCov,min_self]
      rw [min_eq_right (by linarith),min_eq_right (by linarith),min_eq_right (by linarith),
        min_eq_left hst']
      ring
    · simp only [circleTime,dite_eq_right hs,dite_eq_right ht,bbCov,min_self]
      rw [min_eq_left (by linarith),min_eq_left (by linarith),min_eq_right (by linarith),
        min_eq_left hst']
      ring

lemma circleTime_surj_mod_endpoints (c u : unitInterval) :
    ∃ t, circleTime c t=u ∨ circleTime c t=1 ∧ u=0 := by
  by_cases hcu : c ≤ u
  · let t : unitInterval := ⟨(u:ℝ)-(c:ℝ),sub_nonneg.mpr hcu,by linarith [u.property.2,c.property.1]⟩
    refine ⟨t,Or.inl ?_⟩
    have ht : (c:ℝ)+(t:ℝ) ≤ 1 := by dsimp [t]; linarith [u.property.2]
    simp only [circleTime,dite_eq_left ht]
    apply Subtype.ext
    dsimp [t]
    ring
  · have huc : (u:ℝ) < c := lt_of_not_ge hcu
    let t : unitInterval := ⟨1+(u:ℝ)-(c:ℝ),by linarith [u.property.1,c.property.2],by linarith⟩
    refine ⟨t,?_⟩
    by_cases hu : u=0
    · right
      refine ⟨?_,hu⟩
      have ht : (c:ℝ)+(t:ℝ)=1 := by dsimp [t]; simp [hu]
      simp only [circleTime,ht,le_refl,dite_eq_left]
      rfl
    · left
      have hu₀ : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
      have ht : ¬ (c:ℝ)+(t:ℝ) ≤ 1 := by dsimp [t]; linarith
      simp only [circleTime,dite_eq_right ht]
      apply Subtype.ext
      dsimp [t]
      ring

lemma cycle_min_zero_iff (c : unitInterval) (f : C(unitInterval,ℝ)) (hf : f 0=f 1) :
    (∀ t, cyclePath c f 0 ≤ cyclePath c f t) ↔ ∀ t, f c ≤ f t := by
  rw [cyclePath_zero]
  constructor
  · intro h u
    obtain ⟨t,ht | ⟨ht,hu⟩⟩ := circleTime_surj_mod_endpoints c u
    · have hh := h t
      rw [cyclePath_apply_closed c t f hf,ht] at hh
      linarith
    · have hh := h t
      rw [cyclePath_apply_closed c t f hf,ht,← hf,← hu] at hh
      linarith
  · intro h t
    rw [cyclePath_apply_closed c t f hf]
    exact sub_nonneg.mpr (h _)

lemma bridgeAt_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsGaussianProcess (bridgeAt B) P :=
  (bridge_joint_gaussian hB).comp_right Sum.inl

lemma integral_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a : unitInterval) :
    P[bridgeAt B a]=0 := by
  let u : ℝ≥0 := ⟨(a:ℝ), unitInterval.nonneg a⟩
  change (∫ ω, B u ω - (a:ℝ)*B 1 ω ∂P) = 0
  rw [integral_sub (hB.isGaussianProcess.hasGaussianLaw_eval _).integrable
    ((hB.isGaussianProcess.hasGaussianLaw_eval _).integrable.const_mul _),
    integral_const_mul,hB.integral_eval,hB.integral_eval,mul_zero,sub_zero]

lemma covariance_bridgeAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a b : unitInterval) :
    cov[bridgeAt B a,bridgeAt B b; P]=bbCov a b := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (s : ℝ≥0) := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  let u : ℝ≥0 := ⟨(a:ℝ), unitInterval.nonneg a⟩
  let v : ℝ≥0 := ⟨(b:ℝ), unitInterval.nonneg b⟩
  change cov[fun ω => B u ω - (a:ℝ)*B 1 ω,
    fun ω => B v ω - (b:ℝ)*B 1 ω; P] = _
  rw [covariance_fun_sub_fun_sub (hm _) ((hm _).const_mul _) (hm _) ((hm _).const_mul _),
    covariance_const_mul_right,covariance_const_mul_left,covariance_const_mul_left,
    covariance_const_mul_right]
  simp only [hB.covariance_eval]
  change min (a:ℝ) (b:ℝ)-(b:ℝ)*min (a:ℝ) 1-(a:ℝ)*min 1 (b:ℝ)+
    (a:ℝ)*((b:ℝ)*min 1 1)=_
  rw [min_eq_left a.property.2,min_eq_right b.property.2,min_self]
  dsimp [bbCov]
  ring

lemma cyclicBridge_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (c : unitInterval) :
    IsGaussianProcess (fun t ω => bridgeAt B (circleTime c t) ω-bridgeAt B c ω) P := by
  classical
  apply (bridgeAt_gaussian hB).of_isGaussianProcess
  intro t
  refine ⟨{circleTime c t,c},
    { toFun x := x ⟨circleTime c t,by simp⟩-x ⟨c,by simp⟩
      map_add' x y := by simp only [Pi.add_apply]; ring
      map_smul' a x := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring },?_⟩
  intro ω
  rfl

lemma bridgePath_closed {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, bridgePath B ω 0=0 ∧ bridgePath B ω 1=0 := by
  filter_upwards [bridgePath_ae_eq hB,hB.eval_zero_ae_eq_zero] with ω hω h₀
  constructor
  · have e := hω 0
    change bridgePath B ω 0=B 0 ω-(0:ℝ)*B 1 ω at e
    simpa only [h₀,zero_mul,sub_zero] using e
  · have e := hω 1
    change bridgePath B ω 1=B 1 ω-(1:ℝ)*B 1 ω at e
    simpa only [one_mul,sub_self] using e

theorem bridgePath_cycle_invariant {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (c : unitInterval) :
    P.map (fun ω => cyclePath c (bridgePath B ω))=P.map (bridgePath B) := by
  have hgc := cyclicBridge_gaussian hB.toIsPreBrownianReal c
  have hgb := bridgeAt_gaussian hB.toIsPreBrownianReal
  have hc : Continuous (cyclePath c) := continuous_cyclePath.comp (continuous_const.prodMk continuous_id)
  have hcm := hc.measurable.comp_aemeasurable (bridgePath_aemeasurable hB)
  apply path_law_eq_of_coords hcm (bridgePath_aemeasurable hB)
  let d := TopologicalSpace.denseSeq unitInterval
  have he := gaussianProcess_map_eq (hgc.comp_right d) (hgb.comp_right d)
    (fun n => by
      change P[fun ω => bridgeAt B (circleTime c (d n)) ω-bridgeAt B c ω]=P[bridgeAt B (d n)]
      rw [integral_sub (hgb.hasGaussianLaw_eval _).integrable
        (hgb.hasGaussianLaw_eval _).integrable,integral_bridgeAt hB.toIsPreBrownianReal,
        integral_bridgeAt hB.toIsPreBrownianReal,integral_bridgeAt hB.toIsPreBrownianReal,sub_self])
    (fun n m => by
      have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
      have hm (t : unitInterval) := (hgb.hasGaussianLaw_eval t).memLp_two
      change cov[fun ω => bridgeAt B (circleTime c (d n)) ω-bridgeAt B c ω,
        fun ω => bridgeAt B (circleTime c (d m)) ω-bridgeAt B c ω; P]=
          cov[bridgeAt B (d n),bridgeAt B (d m); P]
      rw [covariance_fun_sub_fun_sub (hm _) (hm _) (hm _) (hm _)]
      simp only [covariance_bridgeAt hB.toIsPreBrownianReal]
      exact circleTime_covariance c (d n) (d m))
    (AEMeasurable.of_eval fun index => hgc.aemeasurable (d index))
    (AEMeasurable.of_eval fun index => hgb.aemeasurable (d index))
  have he₁ : (fun ω n => cyclePath c (bridgePath B ω) (d n)) =ᵐ[P]
      (fun ω n => bridgeAt B (circleTime c (d n)) ω-bridgeAt B c ω) := by
    filter_upwards [bridgePath_ae_eq hB,bridgePath_closed hB] with ω hω hclosed
    funext n
    rw [cyclePath_apply_closed c (d n) _ (hclosed.1.trans hclosed.2.symm),hω _,hω _]
    rfl
  have he₂ : (fun ω n => bridgePath B ω (d n)) =ᵐ[P] (fun ω n => bridgeAt B (d n) ω) := by
    filter_upwards [bridgePath_ae_eq hB] with ω hω
    funext n
    exact hω _
  exact (Measure.map_congr he₁).trans (he.trans (Measure.map_congr he₂).symm)

lemma isClosed_minAtSet (c : unitInterval) : IsClosed (minAtSet c) := by
  simpa only [minAtSet,ofPred_forall] using
    (isClosed_iInter fun t : unitInterval =>
      isClosed_le (by fun_prop : Continuous (fun f : C(unitInterval,ℝ) => f c))
        (by fun_prop : Continuous (fun f : C(unitInterval,ℝ) => f t)))

lemma measurableSet_minAtSet (c : unitInterval) : MeasurableSet (minAtSet c) :=
  (isClosed_minAtSet c).measurableSet

lemma measure_minAt_eq {ν : Measure C(unitInterval,ℝ)}
    (hclosed : ∀ᵐ f ∂ν, f 0=f 1)
    (hc : ∀ c, ν.map (cyclePath c)=ν) (c : unitInterval) :
    ν (minAtSet c)=ν (minAtSet 0) := by
  have hcont : Continuous (cyclePath c) :=
    continuous_cyclePath.comp (continuous_const.prodMk continuous_id)
  calc ν (minAtSet c)=ν ((cyclePath c) ⁻¹' minAtSet 0) := by
         apply measure_congr
         filter_upwards [hclosed] with f hf
         exact propext (cycle_min_zero_iff c f hf).symm
       _=(ν.map (cyclePath c)) (minAtSet 0) :=
         (Measure.map_apply hcont.measurable (measurableSet_minAtSet 0)).symm
       _=ν (minAtSet 0) := by rw [hc]

lemma eq_of_minima_in_unique_prefix {f : C(unitInterval,ℝ)} {a x y : unitInterval}
    (ha : 0 < a) (hu : HasUniqueMinimum (prefixTimePath a f))
    (hx : f ∈ minAtSet x) (hy : f ∈ minAtSet y) (hxa : x ≤ a) (hya : y ≤ a) : x=y := by
  let u : unitInterval := ⟨(x:ℝ)/(a:ℝ),div_nonneg x.property.1 (le_of_lt ha),
    (div_le_one₀ ha).mpr hxa⟩
  let v : unitInterval := ⟨(y:ℝ)/(a:ℝ),div_nonneg y.property.1 (le_of_lt ha),
    (div_le_one₀ ha).mpr hya⟩
  have hau : a*u=x := by apply Subtype.ext; dsimp [u]; field_simp [ne_of_gt ha]
  have hav : a*v=y := by apply Subtype.ext; dsimp [v]; field_simp [ne_of_gt ha]
  obtain ⟨c,hc,huniq⟩ := hu
  have hue := huniq u (le_antisymm (by simpa [prefixTimePath_apply,hau] using hx (a*c)) (hc u))
  have hve := huniq v (le_antisymm (by simpa [prefixTimePath_apply,hav] using hy (a*c)) (hc v))
  rw [← hau,← hav,hue,hve]

lemma reciprocalTime_le_half (n : ℕ) : (reciprocalTime n:ℝ) ≤ 1/2 := by
  apply one_div_le_one_div_of_le (by norm_num)
  linarith [Nat.cast_nonneg n (α := ℝ)]

lemma reciprocalTime_injective : Function.Injective reciprocalTime := by
  intro n m h
  have he := congrArg (fun x : unitInterval => (x:ℝ)) h
  change 1/((n:ℝ)+2)=1/((m:ℝ)+2) at he
  have hnm : (n:ℝ)+2=(m:ℝ)+2 := by simpa only [one_div,inv_inj] using he
  exact_mod_cast (add_right_cancel hnm)

lemma minAt_zero_null_of_cyclic_prefix {ν : Measure C(unitInterval,ℝ)} [IsFiniteMeasure ν]
    (hclosed : ∀ᵐ f ∂ν, f 0=f 1)
    (hcyclic : ∀ c, ν.map (cyclePath c)=ν)
    (hprefix : ∀ᵐ f ∂ν, HasUniqueMinimum (prefixTimePath ⟨1/2,by norm_num,by norm_num⟩ f)) :
    ν (minAtSet 0)=0 := by
  let a : unitInterval := ⟨1/2,by norm_num,by norm_num⟩
  let G : Set C(unitInterval,ℝ) := {f | HasUniqueMinimum (prefixTimePath a f)}
  have hG : MeasurableSet G := measurableSet_hasUniqueMinimum.preimage
    (prefixTimePath_lipschitz a).continuous.measurable
  let E : ℕ → Set C(unitInterval,ℝ) := fun n => minAtSet (reciprocalTime n) ∩ G
  have hE : ∀ n, MeasurableSet (E n) := fun n => (measurableSet_minAtSet _).inter hG
  have hd : Pairwise (fun n m => Disjoint (E n) (E m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro f hfn hfm
    apply hnm
    apply reciprocalTime_injective
    exact eq_of_minima_in_unique_prefix (by change (0:ℝ)<1/2; norm_num) hfn.2 hfn.1 hfm.1
      (reciprocalTime_le_half n) (reciprocalTime_le_half m)
  have hmass (n : ℕ) : ν (E n)=ν (minAtSet 0) := by
    refine (measure_congr ?_).trans (measure_minAt_eq hclosed hcyclic (reciprocalTime n))
    filter_upwards [hprefix] with f hf
    exact propext (and_iff_left hf)
  have hf := measure_ne_top ν (⋃ n, E n)
  rw [measure_iUnion hd hE] at hf
  simp_rw [hmass] at hf
  by_contra hn
  exact hf (ENNReal.tsum_const_eq_top_of_ne_zero hn)

lemma bridgePath_law_cyclic {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (c : unitInterval) :
    (P.map (bridgePath B)).map (cyclePath c)=P.map (bridgePath B) := by
  have hcont : Continuous (cyclePath c) :=
    continuous_cyclePath.comp (continuous_const.prodMk continuous_id)
  rw [AEMeasurable.map_map_of_aemeasurable hcont.measurable.aemeasurable
    (bridgePath_aemeasurable hB)]
  exact bridgePath_cycle_invariant hB c

theorem bridge_not_minimum_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ¬ ∀ t, bridgePath B ω 0 ≤ bridgePath B ω t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let ν := P.map (bridgePath B)
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (bridgePath_aemeasurable hB)
  have hclosed : ∀ᵐ f ∂ν, f 0=f 1 := by
    apply (ae_map_iff (bridgePath_aemeasurable hB)
      (measurableSet_eq_fun
        ((by fun_prop : Continuous (fun f : C(unitInterval,ℝ) => f 0)).measurable)
        ((by fun_prop : Continuous (fun f : C(unitInterval,ℝ) => f 1)).measurable))).mpr
    filter_upwards [bridgePath_closed hB] with ω hω
    exact hω.1.trans hω.2.symm
  have hp : ∀ᵐ f ∂ν, HasUniqueMinimum (prefixTimePath ⟨1/2,by norm_num,by norm_num⟩ f) := by
    apply (ae_map_iff (bridgePath_aemeasurable hB)
      (measurableSet_hasUniqueMinimum.preimage
        (prefixTimePath_lipschitz _).continuous.measurable)).mpr
    exact bridge_prefix_unique_minimum hB
      (by change (0:ℝ)<1/2; norm_num) (by change (1:ℝ)/2<1; norm_num)
  have hz := minAt_zero_null_of_cyclic_prefix hclosed (bridgePath_law_cyclic hB) hp
  have hn : ∀ᵐ f ∂ν, f ∉ minAtSet 0 := (ae_iff.mpr (by simpa using hz))
  exact ae_of_ae_map (bridgePath_aemeasurable hB) hn

lemma innerCut_pos (n : ℕ) : 0 < innerCut n := by
  change (0:ℝ)<1-(reciprocalTime n:ℝ)
  linarith [reciprocalTime_le_half n]

lemma innerCut_lt_one (n : ℕ) : innerCut n < 1 := by
  change 1-1/((n:ℝ)+2)<(1:ℝ)
  have : (0:ℝ)<1/((n:ℝ)+2) := by positivity
  linarith

lemma exists_lt_innerCut {t : unitInterval} (ht : t < 1) : ∃ n, t < innerCut n := by
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (show (t:ℝ)<1 from ht))
  have hh : 1/((n:ℝ)+2)≤1/((n:ℝ)+1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨n,?_⟩
  change (t:ℝ)<1-1/((n:ℝ)+2)
  linarith

theorem bridge_unique_minimum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ c : unitInterval, 0 < c ∧ c<1 ∧ UniqueMinimum (bridgePath B ω) c := by
  have hp : ∀ᵐ ω ∂P, ∀ n : ℕ, HasUniqueMinimum (prefixTimePath (innerCut n) (bridgePath B ω)) :=
    ae_all_iff.mpr fun n => bridge_prefix_unique_minimum hB (innerCut_pos n) (innerCut_lt_one n)
  filter_upwards [hp,bridge_not_minimum_zero hB,bridgePath_closed hB] with ω hprefix hzero hclosed
  let f := bridgePath B ω
  let c := minTime f
  have hc := minTime_spec f
  have hcz : c ≠ 0 := by intro he; exact hzero (by simpa only [← he] using hc)
  have hco : c ≠ 1 := by
    intro he
    apply hzero
    intro t
    calc f 0=f 1 := hclosed.1.trans hclosed.2.symm
         _=f c := by rw [he]
         _≤f t := hc t
  have hc₀ : 0 < c := lt_of_le_of_ne (by exact c.property.1) (Ne.symm hcz)
  have hc₁ : c<1 := lt_of_le_of_ne (by exact c.property.2) hco
  refine ⟨c,hc₀,hc₁,hc,?_⟩
  intro t ht
  have htmin : ∀ s, f t ≤ f s := fun s => ht.trans_le (hc s)
  have hto : t ≠ 1 := by
    intro he
    apply hzero
    intro s
    calc f 0=f 1 := hclosed.1.trans hclosed.2.symm
         _=f t := by rw [he]
         _≤f s := htmin s
  have ht₁ : t<1 := lt_of_le_of_ne t.property.2 hto
  obtain ⟨n,hn⟩ := exists_lt_innerCut (max_lt ht₁ hc₁)
  exact eq_of_minima_in_unique_prefix (innerCut_pos n) (hprefix n) htmin hc
    ((le_max_left t c).trans hn.le) ((le_max_right t c).trans hn.le)

theorem probabilityMeasure_tendsto_map_aeContinuous {E F ι : Type*}
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {l : Filter ι} [l.IsCountablyGenerated] {ν : ι → ProbabilityMeasure E}
    {μ : ProbabilityMeasure E} {g : E → F} (hg : Measurable g)
    (h : Tendsto ν l (𝓝 μ)) (hcont : ∀ᵐ x ∂(μ:Measure E), ContinuousAt g x) :
    Tendsto (fun n => (ν n).map hg.aemeasurable) l (𝓝 (μ.map hg.aemeasurable)) := by
  apply tendsto_of_forall_isClosed_limsup_le'
  intro K hK
  have he : (μ:Measure E) (closure (g ⁻¹' K))=(μ:Measure E) (g ⁻¹' K) := by
    apply measure_congr
    filter_upwards [hcont] with x hx
    apply propext
    constructor
    · intro hmem
      have hh := mem_closure_image hx hmem
      exact hK.closure_eq ▸ (closure_mono (image_preimage_subset g K) hh)
    · intro hx; exact subset_closure hx
  have hle : (fun n => ((ν n).map hg.aemeasurable : Measure F) K) ≤
      (fun n => (ν n:Measure E) (closure (g ⁻¹' K))) := by
    intro n
    change ((ν n:Measure E).map g) K≤_
    rw [Measure.map_apply hg hK.measurableSet]
    exact measure_mono subset_closure
  have hh := (Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)).trans
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h isClosed_closure)
  rw [he] at hh
  change _≤((μ:Measure E).map g) K
  rw [Measure.map_apply hg hK.measurableSet]
  exact hh

theorem TendstoInDistribution.aeContinuous_comp {E F ι Ω' : Type*} {Ω : ι → Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [HasOuterApproxClosed E]
    [TopologicalSpace F] [MeasurableSpace F] [BorelSpace F]
    {l : Filter ι} [l.IsCountablyGenerated] {X : (n : ι) → Ω n → E} {Z : Ω' → E}
    {P : (n : ι) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {Q : Measure Ω'} [IsProbabilityMeasure Q] {g : E → F}
    (hg : Measurable g) (h : TendstoInDistribution X l Z P Q)
    (hcont : ∀ᵐ x ∂Q.map Z, ContinuousAt g x) :
    TendstoInDistribution (fun n => g ∘ X n) l (g ∘ Z) P Q where
  forall_aemeasurable n := hg.comp_aemeasurable (h.forall_aemeasurable n)
  aemeasurable_limit := hg.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    have hh := probabilityMeasure_tendsto_map_aeContinuous hg h.tendsto hcont
    have hn (n : ι) :
        ProbabilityMeasure.map (⟨(P n).map (X n),by first | infer_instance | exact Measure.isProbabilityMeasure_map (h.forall_aemeasurable n)⟩ :
          ProbabilityMeasure E) hg.aemeasurable =
        (⟨(P n).map (g ∘ X n),by first | infer_instance | exact Measure.isProbabilityMeasure_map (hg.comp_aemeasurable (h.forall_aemeasurable n))⟩ : ProbabilityMeasure F) := by
      apply Subtype.ext
      exact AEMeasurable.map_map_of_aemeasurable hg.aemeasurable (h.forall_aemeasurable n)
    have hz :
        ProbabilityMeasure.map (⟨Q.map Z,by first | infer_instance | exact Measure.isProbabilityMeasure_map (h.aemeasurable_limit)⟩ :
          ProbabilityMeasure E) hg.aemeasurable =
        (⟨Q.map (g ∘ Z),by first | infer_instance | exact Measure.isProbabilityMeasure_map (hg.comp_aemeasurable h.aemeasurable_limit)⟩ : ProbabilityMeasure F) := by
      apply Subtype.ext
      exact AEMeasurable.map_map_of_aemeasurable hg.aemeasurable h.aemeasurable_limit
    simpa only [hn,hz] using hh

theorem CriticalEvenOffspring.iidVervaat_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    TendstoInDistribution (fun n d => vervaat (p.iidWalk (2*n+1) d)) atTop
      (fun ω => vervaat (bridgePath B ω)) p.iidBridgeLaw P := by
  apply TendstoInDistribution.aeContinuous_comp measurable_vervaat (p.iidBridge_CLT hB)
  have hp : ∀ᵐ f ∂P.map (bridgePath B), HasUniqueMinimum f := by
    apply (ae_map_iff (bridgePath_aemeasurable hB) measurableSet_hasUniqueMinimum).mpr
    filter_upwards [bridge_unique_minimum hB] with ω hω
    obtain ⟨c,_,_,hc⟩ := hω
    exact ⟨c,hc⟩
  filter_upwards [hp] with f hf
  obtain ⟨c,hc⟩ := hf
  exact continuousAt_vervaat hc

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TreeCode
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSingletonClassCode _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_5
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_5 : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩


lemma codePartition_nonneg (p : CriticalEvenOffspring) (N : ℕ) :
    0 ≤ codePartition p N := Finset.sum_nonneg (fun d _ => codeWeight_nonneg p d)


lemma rotateBridge_add {N : ℕ} [NeZero N] (a b : Fin N) (d : Bridge N) :
    rotateBridge a (rotateBridge b d) = rotateBridge (a+b) d := by
  apply Subtype.ext
  funext i
  simp [rotateBridge, rotateDegrees, add_assoc]


lemma goodRotation_of_code {N : ℕ} [NeZero N] (d : Bridge N)
    (hd : IsTreeCode d.val) : goodRotation d = 0 := by
  apply d.unique_good_rotation.unique (goodRotation_spec d)
  simpa using hd


@[simp] lemma canonicalCode_of_code {N : ℕ} [NeZero N] (d : Code N) :
    canonicalCode (⟨d.val, d.property.1⟩ : Bridge N) = d := by
  apply Subtype.ext
  change (rotateBridge (goodRotation ⟨d.val, d.property.1⟩) _).val = d.val
  rw [goodRotation_of_code _ d.property, rotateBridge_zero]


lemma goodRotation_add {N : ℕ} [NeZero N] (d : Bridge N) (m : Fin N) :
    goodRotation (rotateBridge m d) + m = goodRotation d := by
  apply d.unique_good_rotation.unique _ (goodRotation_spec d)
  rw [← rotateBridge_add]
  exact goodRotation_spec (rotateBridge m d)


@[simp] lemma canonicalCode_rotate {N : ℕ} [NeZero N] (d : Bridge N) (m : Fin N) :
    canonicalCode (rotateBridge m d) = canonicalCode d := by
  apply Subtype.ext
  change (rotateBridge _ (rotateBridge m d)).val = (rotateBridge _ d).val
  rw [rotateBridge_add, goodRotation_add]


theorem canonicalCode_weighted_sum (p : CriticalEvenOffspring)
    {N : ℕ} [NeZero N] (F : Code N → ℝ) :
    ∑ d : Bridge N, bridgeWeight p d * F (canonicalCode d) =
      (N : ℝ) * ∑ d : Code N, codeWeight p d * F d := by
  classical
  have h := weighted_unique_rotation (rotateBridge (N := N))
    (fun d => bridgeWeight p d * F (canonicalCode d))
    (fun d => IsTreeCode d.val)
    (fun m d => by rw [bridgeWeight_rotate, canonicalCode_rotate])
    (fun d => d.unique_good_rotation)
  rw [Fintype.card_fin] at h
  rw [h]
  congr 1
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun d : Bridge N => IsTreeCode d.val) _ (by simp)]
  let e : Code N ≃ {d : Bridge N // IsTreeCode d.val} := {
    toFun := fun d => ⟨⟨d.val, d.property.1⟩, d.property⟩
    invFun := fun d => ⟨d.val.val, d.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro d _
  change bridgeWeight p ⟨d.val, d.property.1⟩ *
    F (canonicalCode ⟨d.val, d.property.1⟩) = codeWeight p d * F d
  rw [canonicalCode_of_code]
  rfl


theorem canonicalCode_expectation (p : CriticalEvenOffspring) (n : ℕ)
    (F : Code (2*n+1) → ℝ) :
    ∑ d : Bridge (2*n+1), (bridgeWeight p d / bridgePartition p (2*n+1)) *
      F (canonicalCode d) =
    ∑ d : Code (2*n+1), (codeWeight p d / codePartition p (2*n+1)) * F d := by
  let : NeZero (2*n+1) := ⟨by omega⟩
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div, canonicalCode_weighted_sum,
    codePartition_cyclic p (by omega)]
  rw [mul_div_mul_left _ _ (by positivity : ((2*n+1 : ℕ) : ℝ) ≠ 0)]


lemma CriticalEvenOffspring.iid_bridge_singleton (p : CriticalEvenOffspring)
    {N : ℕ} (b : Bridge N) :
    (p.iidLaw N).real {bridgeEmbedding N b} = bridgeWeight p b := by
  rw [measureReal_def, iidLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  simp only [p.law_singleton, ENNReal.toReal_ofReal (p.nonneg _)]
  rfl


lemma CriticalEvenOffspring.bridge_integral_eq (p : CriticalEvenOffspring) (N : ℕ)
    (F : (Fin N → ℕ) → ℝ) :
    ∫ d, F d ∂cond (p.iidLaw N) {d | totalStep d = -1} =
      ∑ b : Bridge N, (bridgeWeight p b / bridgePartition p N) * F (bridgeEmbedding N b) := by
  classical
  have hset : {d : Fin N → ℕ | totalStep d = -1} = ⋃ b : Bridge N, {bridgeEmbedding N b} := by
    rw [totalStep_bridge_range]
    ext d
    simp
  have hdis : Pairwise (fun b c : Bridge N => Disjoint ({bridgeEmbedding N b} : Set (Fin N → ℕ))
      {bridgeEmbedding N c}) := by
    intro b c hbc
    exact Set.disjoint_singleton.mpr ((bridgeEmbedding N).injective.ne hbc)
  have hi (b : Bridge N) : IntegrableOn F {bridgeEmbedding N b} (p.iidLaw N) :=
    IntegrableOn.of_finite (Set.finite_singleton _)
  rw [ProbabilityTheory.cond,integral_smul_measure,hset,integral_iUnion_fintype (fun _ => measurableSet_singleton _) hdis hi]
  simp only [integral_singleton,smul_eq_mul,ENNReal.toReal_inv]
  rw [← hset,← measureReal_def,← p.bridgePartition_eq_iid,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [p.iid_bridge_singleton]
  ring


lemma bridgeFromArray_spec {N : ℕ} (d : Fin N → ℕ) (hd : totalStep d = -1) :
    bridgeEmbedding N (bridgeFromArray d hd)=d :=
  ((totalStep_bridge_range N) ▸ hd : d ∈ Set.range (bridgeEmbedding N)).choose_spec


@[simp] lemma bridgeFromArray_embedding {N : ℕ} (b : Bridge N) (hd : totalStep (bridgeEmbedding N b) = -1) :
    bridgeFromArray (bridgeEmbedding N b) hd=b := by
  exact (bridgeEmbedding N).injective (bridgeFromArray_spec _ _)


lemma arrayTree_embedding (n : ℕ) (b : Bridge (2*n+1)) :
    arrayTree n (bridgeEmbedding (2*n+1) b)=canonicalCode b := by
  simp [arrayTree,totalStep_bridge]


theorem CriticalEvenOffspring.arrayTree_expectation (p : CriticalEvenOffspring)
    (n : ℕ) (F : Code (2*n+1) → ℝ) :
    ∫ d, F (arrayTree n d) ∂cond (p.iidLaw (2*n+1)) {d | totalStep d = -1} =
      ∑ b : Code (2*n+1), (codeWeight p b / codePartition p (2*n+1))*F b := by
  rw [p.bridge_integral_eq]
  simp only [arrayTree_embedding]
  exact canonicalCode_expectation p n F


lemma interpolation_interval_formula {N j : ℕ} (hj : j<N)
    (a : Fin (N+1) → ℝ) (t : unitInterval)
    (hl : (j:ℝ) ≤ (N:ℝ)*(t:ℝ)) (hu : (N:ℝ)*(t:ℝ) ≤ j+1) :
    interpolation N a t =
      (1-((N:ℝ)*(t:ℝ)-j))*a ⟨j,by omega⟩ +
        ((N:ℝ)*(t:ℝ)-j)*a ⟨j+1,by omega⟩ := by
  classical
  let i : Fin (N+1) := ⟨j,by omega⟩
  let k : Fin (N+1) := ⟨j+1,by omega⟩
  have hik : i ≠ k := by intro he; have := congrArg Fin.val he; dsimp [i,k] at this; omega
  have hz (r : Fin (N+1)) (hr : r∉({i,k} : Finset (Fin (N+1)))) :
      a r*hat N r.val t=0 := by
    have hir : r.val ≠ j := by
      intro he
      apply hr
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact Or.inl (Fin.ext he)
    have hkr : r.val ≠ j+1 := by
      intro he
      apply hr
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact Or.inr (Fin.ext he)
    suffices hat N r.val t=0 by rw [this,mul_zero]
    change max 0 (1-|(N:ℝ)*(t:ℝ)-(r.val:ℝ)|)=0
    apply max_eq_left
    rcases lt_or_gt_of_ne hir with h | h
    · have hh : (r.val:ℝ)+1 ≤ j := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have h' : j+2 ≤ r.val := by omega
      have hh : (j:ℝ)+2 ≤ r.val := by exact_mod_cast h'
      rw [abs_of_nonpos (by linarith)]
      linarith
  rw [interpolation_apply,← Finset.sum_subset (Finset.subset_univ {i,k}) (fun r _ hr => hz r hr)]
  rw [Finset.sum_pair hik]
  change a i*max 0 (1-|(N:ℝ)*(t:ℝ)-j|)+
    a k*max 0 (1-|(N:ℝ)*(t:ℝ)-(j+1:ℕ)|)=_
  rw [Nat.cast_add,Nat.cast_one,abs_of_nonneg (by linarith),abs_of_nonpos (by linarith),
    max_eq_right (by linarith),max_eq_right (by linarith)]
  dsimp [i,k]
  ring


lemma interpolation_ge {N : ℕ} (a : Fin (N+1) → ℝ) {c : ℝ}
    (h : ∀ i, c ≤ a i) (t : unitInterval) : c ≤ interpolation N a t := by
  rw [interpolation_apply]
  calc
    c = ∑ i : Fin (N+1), c*hat N i.val t := by rw [← Finset.mul_sum,hat_sum,mul_one]
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (hat_nonneg _ _ _)


lemma interpolation_strict_before {N : ℕ} (hN : 0<N) (a : Fin (N+1) → ℝ)
    (m : Fin (N+1)) (hmin : ∀ i, a m≤a i) (hfirst : ∀ i, i < m → a m < a i)
    (t : unitInterval) (ht : t<gridPoint N m) : a m < interpolation N a t := by
  have hNR : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hNt : (N:ℝ)*(t:ℝ) < m.val := by
    have hh : (t:ℝ)<(m.val:ℝ)/(N:ℝ) := ht
    nlinarith [(lt_div_iff₀ hNR).mp hh]
  have hz : 0≤(N:ℝ)*(t:ℝ) := mul_nonneg hNR.le t.property.1
  let j := ⌊(N:ℝ)*(t:ℝ)⌋₊
  have hjx : (j:ℝ)≤(N:ℝ)*(t:ℝ) := Nat.floor_le hz
  have hxj : (N:ℝ)*(t:ℝ)<(j:ℝ)+1 := Nat.lt_floor_add_one _
  have hjm : j < m.val := by exact_mod_cast (hjx.trans_lt hNt)
  have hjN : j<N := hjm.trans_le (Nat.le_of_lt_succ m.isLt)
  rw [interpolation_interval_formula hjN a t hjx hxj.le]
  have ha := hfirst ⟨j,by omega⟩ hjm
  have hb := hmin ⟨j+1,by omega⟩
  have hc : 0<1-((N:ℝ)*(t:ℝ)-j) := by linarith
  have hd : 0≤(N:ℝ)*(t:ℝ)-j := by linarith
  nlinarith [mul_pos hc (sub_pos.mpr ha),mul_nonneg hd (sub_nonneg.mpr hb)]


lemma exists_grid_interval {N : ℕ} (hN : 0<N) (t : unitInterval) :
    ∃ j : ℕ, j<N ∧ (j:ℝ) ≤ (N:ℝ)*(t:ℝ) ∧ (N:ℝ)*(t:ℝ) ≤ j+1 := by
  by_cases ht : t=1
  · have hcast : ((N-1:ℕ):ℝ)=(N:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
    refine ⟨N-1,by omega,?_,?_⟩
    · subst t
      change ((N-1:ℕ):ℝ)≤(N:ℝ)*1
      rw [hcast,mul_one]
      linarith
    · subst t
      change (N:ℝ)*1≤((N-1:ℕ):ℝ)+1
      rw [hcast,mul_one]
      linarith
  · have hlt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (fun he => ht (Subtype.ext he))
    let j := ⌊(N:ℝ)*(t:ℝ)⌋₊
    have hj : (j:ℝ)≤(N:ℝ)*(t:ℝ) := Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) t.property.1)
    have h' : (N:ℝ)*(t:ℝ)<N := by nlinarith [show (0:ℝ)<N from Nat.cast_pos.mpr hN]
    refine ⟨j,?_,hj,(Nat.lt_floor_add_one _).le⟩
    exact_mod_cast (hj.trans_lt h')


lemma cyclePath_interpolation {N m : ℕ} (hN : 0<N) (hm : m≤N)
    (a b : Fin (N+1) → ℝ)
    (hl : ∀ j (hj : j≤N-m), b ⟨j,by omega⟩ = a ⟨m+j,by omega⟩-a ⟨m,by omega⟩)
    (hr : ∀ j (hj : N-m≤j) (hjN : j≤N), b ⟨j,by omega⟩ =
      a ⟨N,by omega⟩+a ⟨j-(N-m),by omega⟩-a ⟨0,by omega⟩-a ⟨m,by omega⟩) :
    cyclePath (gridPoint N ⟨m,by omega⟩) (interpolation N a)=interpolation N b := by
  have hNR : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hNne : (N:ℝ)≠0 := hNR.ne'
  have hgrid : (gridPoint N ⟨m,by omega⟩:ℝ)=(m:ℝ)/N := rfl
  have hmul : (N:ℝ)*((m:ℝ)/N)=m := mul_div_cancel₀ _ hNne
  have hz : (0:unitInterval)=gridPoint N ⟨0,by omega⟩ := by apply Subtype.ext; simp [gridPoint]
  have ho : (1:unitInterval)=gridPoint N ⟨N,by omega⟩ := by apply Subtype.ext; simp [gridPoint,hNne]
  apply ContinuousMap.ext
  intro t
  obtain ⟨j,hj,hjt,htj⟩ := exists_grid_interval hN t
  rw [interpolation_interval_formula hj b t hjt htj]
  by_cases hsum : m+j<N
  · have hjle : j≤N-m := by omega
    have hjle' : j+1≤N-m := by omega
    have hsumR : (m:ℝ)+(j:ℝ)+1≤N := by exact_mod_cast hsum
    have hct : (gridPoint N ⟨m,by omega⟩:ℝ)+(t:ℝ)≤1 := by
      rw [hgrid]
      nlinarith
    rw [cyclePath_apply_left _ _ _ hct,interpolation_gridPoint hN,
      interpolation_interval_formula hsum a _ (by dsimp; rw [hgrid,Nat.cast_add]; nlinarith)
        (by dsimp; rw [hgrid,Nat.cast_add]; nlinarith)]
    rw [hl j hjle,hl (j+1) hjle']
    simp only [Nat.cast_add]
    rw [hgrid]
    have hidx : (⟨m+j+1,by omega⟩ : Fin (N+1))=⟨m+(j+1),by omega⟩ := by congr 1
    simp only [hidx,mul_sub,mul_add,hmul]
    ring
  · have hjge : N-m≤j := by omega
    have hk : j-(N-m)<N := by omega
    have hdiff : (N-m:ℕ) + (j-(N-m))=j := Nat.add_sub_of_le hjge
    have hNm : ((N-m:ℕ):ℝ)=(N:ℝ)-m := Nat.cast_sub hm
    have hkR : ((j-(N-m):ℕ):ℝ)=(j:ℝ)-((N:ℝ)-m) := by rw [Nat.cast_sub hjge,hNm]
    have hct : 1≤(gridPoint N ⟨m,by omega⟩:ℝ)+(t:ℝ) := by
      rw [hgrid]
      have hsumR : (N:ℝ) ≤ m+j := by exact_mod_cast (le_of_not_gt hsum)
      nlinarith
    rw [cyclePath_apply_right _ _ _ hct,hz,ho,
      interpolation_gridPoint hN,interpolation_gridPoint hN,interpolation_gridPoint hN,
      interpolation_interval_formula hk a _ (by dsimp; rw [hgrid,hkR]; nlinarith)
        (by dsimp; rw [hgrid,hkR]; nlinarith)]
    rw [hr j hjge (by omega),hr (j+1) (by omega) (by omega)]
    simp only []
    rw [hgrid,hkR]
    have hidx : (⟨j-(N-m)+1,by omega⟩ : Fin (N+1))=⟨j+1-(N-m),by omega⟩ := by congr 1; omega
    simp only [hidx,mul_sub,mul_add,hmul,mul_one]
    ring


lemma minTime_interpolation {N : ℕ} (hN : 0 < N) (a : Fin (N+1) → ℝ)
    (m : Fin (N+1)) (hmin : ∀ i, a m ≤ a i) (hfirst : ∀ i, i < m → a m < a i) :
    minTime (interpolation N a)=gridPoint N m := by
  apply le_antisymm
  · apply minTime_first
    intro t
    rw [interpolation_gridPoint hN]
    exact interpolation_ge a hmin t
  · by_contra h
    have ht : minTime (interpolation N a)<gridPoint N m := lt_of_not_ge h
    have hs := interpolation_strict_before hN a m hmin hfirst _ ht
    have hu := minTime_spec (interpolation N a) (gridPoint N m)
    rw [interpolation_gridPoint hN] at hu
    exact (not_lt_of_ge hu) hs


@[simp] lemma cyclePath_one_time (f : C(unitInterval,ℝ)) : cyclePath 1 f=f-f 0 • 1 := by
  ext t
  rw [cyclePath_apply_right _ _ _ (by simp only [show ((1:unitInterval):ℝ)=1 from rfl]; linarith [t.property.1])]
  have he : (⟨(1:ℝ)+(t:ℝ)-1,by constructor <;> linarith [t.property.1,t.property.2]⟩ : unitInterval)=t := by
    ext; dsimp; ring
  simp only [show ((1:unitInterval):ℝ)=1 from rfl,he,ContinuousMap.sub_apply,ContinuousMap.smul_apply,ContinuousMap.one_apply,smul_eq_mul,mul_one]
  ring


lemma goodRotation_firstMinimum {N : ℕ} [NeZero N] (d : Bridge N) :
    FirstMinimum (degreeList d.val) (goodRotation d).val := by
  apply firstMinimum_of_isExcursionList_rotate ((degreeList_sum _).trans d.property)
    (by simp)
  rw [← degreeList_rotate,← isTreeCode_iff]
  exact goodRotation_spec d


lemma walkPolygon_cycle {N : ℕ} [NeZero N] (σ : ℝ) (d : Bridge N) (m : Fin N) :
    cyclePath (gridPoint N ⟨m.val,by omega⟩) (walkPolygon σ d.val)=
      walkPolygon σ (rotateBridge m d).val := by
  have hN : 0 < N := NeZero.pos N
  apply cyclePath_interpolation hN m.isLt.le
  · intro j hj
    have he : walk (rotateBridge m d).val j = walk d.val (m.val+j)-walk d.val m.val := by
      change walk (rotateDegrees m d.val) j=_
      rw [← degreeList_prefixSum,degreeList_rotate,
        prefixSum_rotate_left _ (by simp) (by simpa using hj)]
      simp only [degreeList_prefixSum]
    dsimp
    rw [he,Int.cast_sub,sub_div]
  · intro j hj hjN
    have he : walk (rotateBridge m d).val j = walk d.val N-walk d.val m.val+
        walk d.val (j-(N-m.val)) := by
      change walk (rotateDegrees m d.val) j=_
      rw [← degreeList_prefixSum,degreeList_rotate,
        prefixSum_rotate_right _ (by simp) (by simpa using hj) (by simpa using hjN)]
      simp only [degreeList_prefixSum,degreeList_sum,degreeList_length]
    dsimp
    rw [he,Int.cast_add,Int.cast_sub,walk_zero,Int.cast_zero]
    ring


theorem vervaat_walkPolygon {N : ℕ} [NeZero N] {σ : ℝ} (hσ : 0 < σ) (d : Bridge N) :
    vervaat (walkPolygon σ d.val)=walkPolygon σ (canonicalCode d).val := by
  have hN : 0 < N := NeZero.pos N
  have hs : 0 < σ*Real.sqrt N := mul_pos hσ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  have hm := goodRotation_firstMinimum d
  have hmin : ∀ j < N, walk d.val (goodRotation d).val ≤ walk d.val j := by
    simpa only [degreeList_prefixSum,degreeList_length] using hm.2.1
  have hfirst : ∀ j < (goodRotation d).val, walk d.val (goodRotation d).val < walk d.val j := by
    simpa only [degreeList_prefixSum] using hm.2.2
  have hnonpos : walk d.val (goodRotation d).val ≤ 0 := by simpa using hmin 0 hN
  by_cases hz : walk d.val (goodRotation d).val=0
  · have hg : IsTreeCode d.val := ⟨d.property,fun j hj => hz ▸ hmin j hj⟩
    have hc : (canonicalCode d).val=d.val := by
      change (rotateBridge (goodRotation d) d).val=d.val
      rw [goodRotation_of_code d hg,rotateBridge_zero]
    have ht : minTime (walkPolygon σ d.val)=1 := by
      rw [walkPolygon,minTime_interpolation hN _ (⟨N,by omega⟩ : Fin (N+1))]
      · apply Subtype.ext
        simp [gridPoint,(Nat.cast_pos.mpr hN : (0:ℝ)<N).ne']
      · intro i
        apply (div_le_div_iff_of_pos_right hs).mpr
        apply Int.cast_le.mpr
        by_cases hi : i.val=N
        · simp [hi]
        · rw [d.property]
          have hh := hg.2 i.val (by omega)
          omega
      · intro i hi
        apply (div_lt_div_iff_of_pos_right hs).mpr
        apply Int.cast_lt.mpr
        rw [d.property]
        have hh := hg.2 i.val hi
        omega
    rw [vervaat,ht,cyclePath_one_time,hc]
    have hzero : walkPolygon σ d.val 0=0 := by
      have he : (0:unitInterval)=gridPoint N ⟨0,by omega⟩ := by ext; simp [gridPoint]
      rw [walkPolygon,he,interpolation_gridPoint hN]
      simp
    rw [hzero,zero_smul,sub_zero]
  · have hneg : walk d.val (goodRotation d).val ≤ -1 := by omega
    have ht : minTime (walkPolygon σ d.val)=gridPoint N ⟨(goodRotation d).val,by omega⟩ := by
      apply minTime_interpolation hN
      · intro i
        apply (div_le_div_iff_of_pos_right hs).mpr
        apply Int.cast_le.mpr
        by_cases hi : i.val=N
        · simpa only [hi,d.property] using hneg
        · exact hmin i.val (by omega)
      · intro i hi
        apply (div_lt_div_iff_of_pos_right hs).mpr
        exact Int.cast_lt.mpr (hfirst i.val hi)
    rw [vervaat,ht,walkPolygon_cycle]
    rfl


lemma CriticalEvenOffspring.iidWalk_bridgeEmbedding (p : CriticalEvenOffspring)
    {N : ℕ} (d : Bridge N) : p.iidWalk N (bridgeEmbedding N d)=walkPolygon p.sigma d.val := by
  unfold iidWalk walkPolygon
  congr 1
  funext i
  have he : (∑ j : Fin N, if j.val < i.val then p.standardStep (bridgeEmbedding N d j) else 0)=
      (walk d.val i.val:ℝ)/p.sigma := by
    simp only [walk,Int.cast_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · simp only [standardStep,Int.cast_sub,Int.cast_natCast,Int.cast_one]
      rfl
    · simp
  rw [he,div_div]


lemma CriticalEvenOffspring.vervaat_arrayTree (p : CriticalEvenOffspring) (n : ℕ) :
    (fun d => vervaat (p.iidWalk (2*n+1) d)) =ᵐ[p.iidBridgeLaw n]
      (fun d => walkPolygon p.sigma (arrayTree n d).val) := by
  have he : ∀ᵐ d ∂p.iidBridgeLaw n, totalStep d = -1 := by
    exact ae_cond_mem (by measurability)
  filter_upwards [he] with d hd
  let b := bridgeFromArray d hd
  have hb : bridgeEmbedding (2*n+1) b=d := bridgeFromArray_spec _ _
  rw [← hb,p.iidWalk_bridgeEmbedding,arrayTree_embedding,vervaat_walkPolygon p.sigma_pos]


theorem CriticalEvenOffspring.codeWalk_CLT (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (F : BoundedContinuousFunction C(unitInterval,ℝ) ℝ) :
    Tendsto (fun n : ℕ => ∑ d : Code (2*n+1),
      (codeWeight p d/codePartition p (2*n+1))*F (walkPolygon p.sigma d.val)) atTop
      (𝓝 (∫ ω,F (vervaat (bridgePath B ω)) ∂P)) := by
  have hc := p.iidVervaat_CLT hB
  have hh := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hc.tendsto F
  simp only [ProbabilityMeasure.coe_mk] at hh
  have hn (n : ℕ) :
      (∫ f,F f ∂(p.iidBridgeLaw n).map (fun d => vervaat (p.iidWalk (2*n+1) d)))=
        ∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1))*F (walkPolygon p.sigma d.val) := by
    rw [integral_map (hc.forall_aemeasurable n) F.continuous.aestronglyMeasurable]
    calc
      _ = ∫ d,F (walkPolygon p.sigma (arrayTree n d).val) ∂p.iidBridgeLaw n := by
        apply integral_congr_ae
        exact (p.vervaat_arrayTree n).fun_comp F
      _ = _ := p.arrayTree_expectation n (fun d => F (walkPolygon p.sigma d.val))
  have hz : (∫ f,F f ∂P.map (fun ω => vervaat (bridgePath B ω)))=
      ∫ ω,F (vervaat (bridgePath B ω)) ∂P :=
    integral_map hc.aemeasurable_limit F.continuous.aestronglyMeasurable
  simpa only [hn,hz] using hh


theorem CriticalEvenOffspring.stream_hits_negative (p : CriticalEvenOffspring)
    (j : ℕ) (hj : 0 < j) :
    ∀ᵐ ω ∂p.streamLaw, ∃ n, integerSum ω n=-(j:ℤ) := by
  let X : ℕ → (ℕ → ℕ) → ℝ := fun n ω => (ω n:ℝ)-1
  have hm (n : ℕ) : StronglyMeasurable (X n) := by fun_prop
  let ℱ := Filtration.natural X hm
  let S : ℕ → (ℕ → ℕ) → ℤ := fun n ω => (j:ℤ)+integerSum ω (n+1)
  have hM : Martingale (fun n ω => (S n ω:ℝ)) ℱ p.streamLaw := by
    have h := independent_sum_martingale X hm
      (fun n => (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).integrable_comp_of_integrable p.integrable_step)
      (iIndepFun_infinitePi (X := fun _ (k : ℕ) => (k:ℝ)-1) (fun _ => by fun_prop)) (fun n => by
        change (∫ ω, ((fun k : ℕ => (k:ℝ)-1) (ω n)) ∂p.streamLaw)=0
        exact ((measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).hasLaw.integral_comp
          (f := fun k : ℕ => (k:ℝ)-1) (by fun_prop)).trans p.integral_step)
    convert (martingale_const ℱ p.streamLaw (j:ℝ)).add h using 1
    all_goals try with_reducible_and_instances rfl
    ext n ω
    simp [S,integerSum,X]
  have hS : StronglyAdapted ℱ S := by
    intro n
    have h : Measurable[ℱ n] (fun ω => Int.floor (S n ω:ℝ)) :=
      Int.measurable_floor.comp (hM.stronglyMeasurable n).measurable
    simpa only [Int.floor_intCast] using h.stronglyMeasurable
  have h₀ (ω : ℕ → ℕ) : 0 ≤ S 0 ω := by
    dsimp [S]
    simp only [integerSum_succ,integerSum_zero,zero_add]
    omega
  have hstep (n : ℕ) (ω : ℕ → ℕ) : S n ω-1 ≤ S (n+1) ω := by
    dsimp [S]
    rw [integerSum_succ ω (n+1)]
    omega
  have hone : ∀ᵐ k ∂p.law.toMeasure, k≠1 := by
    rw [ae_iff]
    simpa using (show p.law.toMeasure {1}=0 by
      simp [p.even_support 1 (by decide)])
  have hall : ∀ᵐ ω ∂p.streamLaw, ∀ n, ω n≠1 := by
    rw [ae_all_iff]
    intro n
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).quasiMeasurePreserving.tendsto_ae hone
  have hjump : ∀ᵐ ω ∂p.streamLaw, ∃ᶠ n in atTop, S (n+1) ω≠S n ω := by
    filter_upwards [hall] with ω hω
    apply Filter.Frequently.of_forall
    intro n hn
    have h := hω (n+1)
    dsimp [S] at hn
    rw [integerSum_succ ω (n+1)] at hn
    omega
  filter_upwards [integer_martingale_hits_zero hS hM h₀ hstep hjump] with ω hω
  obtain ⟨n,hn⟩ := hω
  exact ⟨n+1,by dsimp [S] at hn; omega⟩


lemma reverseFirst_preserving (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (reverseFirst n) p.streamLaw p.streamLaw := by
  refine ⟨by unfold reverseFirst; fun_prop,?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (reverseIndex_involutive n).injective


lemma integerSum_reverseFirst (x : ℕ → ℕ) (n k : ℕ) (hk : k ≤ n) :
    integerSum (reverseFirst n x) k=integerSum x n-integerSum x (n-k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < n := by omega
    have he : n-k=(n-(k+1))+1 := by omega
    have he' : n-1-k=n-(k+1) := by omega
    rw [integerSum_succ,ih (by omega)]
    simp only [reverseFirst,reverseIndex,ite_eq_left hk',he']
    rw [he,integerSum_succ]
    ring


lemma firstHitBelow_iff_reverse_survival (x : ℕ → ℕ) (j n : ℕ) :
    firstHitBelow x j n ↔ integerSum (reverseFirst n x) n=-(j:ℤ) ∧
      negativeSurvival (reverseFirst n x) n := by
  have he : integerSum (reverseFirst n x) n=integerSum x n := by
    simp [integerSum_reverseFirst x n n le_rfl]
  rw [he]
  constructor
  · rintro ⟨hx,hfirst⟩
    refine ⟨hx,?_⟩
    intro k hk hkn
    rw [integerSum_reverseFirst x n k hkn,hx]
    have h := hfirst (n-k) (by omega)
    omega
  · rintro ⟨hx,hs⟩
    refine ⟨hx,?_⟩
    intro k hkn
    have h := hs (n-k) (by omega) (by omega)
    rw [integerSum_reverseFirst x n (n-k) (by omega)] at h
    have he' : n-(n-k)=k := by omega
    rw [he',hx] at h
    omega


lemma measurable_integerSum (n : ℕ) : Measurable (fun x : ℕ → ℕ => integerSum x n) := by
  unfold integerSum
  fun_prop


lemma measurableSet_firstHitBelow (j n : ℕ) : MeasurableSet {x | firstHitBelow x j n} := by
  unfold firstHitBelow
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_integerSum n) measurable_const).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (measurable_integerSum k))


lemma measurableSet_survival_endpoint (j n : ℕ) :
    MeasurableSet {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} := by
  unfold negativeSurvival
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (measurableSet_eq_fun (measurable_integerSum n) measurable_const).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_integerSum k) measurable_const)


lemma CriticalEvenOffspring.survival_endpoint_eq_firstHit (p : CriticalEvenOffspring)
    (j n : ℕ) :
    p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n}=
      p.streamLaw {x | firstHitBelow x j n} := by
  rw [← (reverseFirst_preserving p n).measure_preimage (measurableSet_survival_endpoint j n).nullMeasurableSet]
  congr 1
  ext x
  exact (firstHitBelow_iff_reverse_survival x j n).symm


lemma exists_firstHitBelow (x : ℕ → ℕ) (j : ℕ) (_hj : 0 < j)
    (hex : ∃ n, integerSum x n=-(j:ℤ)) : ∃ n, firstHitBelow x j n := by
  classical
  refine ⟨Nat.find hex,Nat.find_spec hex,?_⟩
  intro k hk
  have h0 : 0 ≤ (j:ℤ)+integerSum x 0 := by simp
  have hs (r : ℕ) : (j:ℤ)+integerSum x r-1 ≤ (j:ℤ)+integerSum x (r+1) := by
    rw [integerSum_succ]
    omega
  have hn (r : ℕ) (hr : r ≤ k) : (j:ℤ)+integerSum x r≠0 := by
    have h := Nat.find_min hex (by omega : r < Nat.find hex)
    omega
  have hpos := integer_path_nonneg_before_zero (fun r => (j:ℤ)+integerSum x r)
    h0 hs k (fun r hr => hn r hr.le)
  have hne := hn k le_rfl
  omega


lemma firstHitBelow_disjoint (j : ℕ) :
    Pairwise (fun n m => Disjoint {x | firstHitBelow x j n} {x | firstHitBelow x j m}) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro x hn hm
  rcases lt_or_gt_of_ne hnm with h | h
  · have hh := hm.2 n h
    rw [hn.1] at hh
    exact (lt_irrefl _ hh)
  · have hh := hn.2 m h
    rw [hm.1] at hh
    exact (lt_irrefl _ hh)


theorem CriticalEvenOffspring.negative_potential_one (p : CriticalEvenOffspring)
    (j : ℕ) (hj : 0 < j) :
    (∑' n, p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n})=1 := by
  simp_rw [p.survival_endpoint_eq_firstHit]
  rw [← measure_iUnion (firstHitBelow_disjoint j) (measurableSet_firstHitBelow j)]
  apply (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion (measurableSet_firstHitBelow j))).mp
  filter_upwards [p.stream_hits_negative j hj] with x hx
  obtain ⟨n,hn⟩ := exists_firstHitBelow x j hj hx
  exact Set.mem_iUnion.mpr ⟨n,hn⟩


lemma measurable_truncateStream (n : ℕ) : Measurable (truncateStream n) := by
  apply Measurable.of_eval
  intro k
  unfold truncateStream
  split_ifs <;> fun_prop


lemma integerSum_truncateStream (x : ℕ → ℕ) {k n : ℕ} (hkn : k ≤ n) :
    integerSum (truncateStream n x) k=integerSum x k := by
  unfold integerSum
  apply Finset.sum_congr rfl
  intro i hi
  simp [truncateStream,show i<n from lt_of_lt_of_le (Finset.mem_range.mp hi) hkn]


lemma CriticalEvenOffspring.truncate_indep_next (p : CriticalEvenOffspring) (n : ℕ) :
    IndepFun (truncateStream n) (fun x : ℕ → ℕ => x n) p.streamLaw := by
  classical
  have hi : iIndepFun (fun k (x : ℕ → ℕ) => x k) p.streamLaw :=
    iIndepFun_infinitePi (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) {n} := by simp
  have h := hi.indepFun_finset (Finset.range n) {n} hd (fun k => measurable_pi_apply k)
  let f : ((Finset.range n) → ℕ) → (ℕ → ℕ) :=
    fun x k => if hk : k<n then x ⟨k,Finset.mem_range.mpr hk⟩ else 0
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro k
    dsimp [f]
    split_ifs <;> fun_prop
  have hh := h.comp hf (measurable_pi_apply ⟨n,by simp⟩)
  exact hh


lemma CriticalEvenOffspring.prefix_inter_next (p : CriticalEvenOffspring)
    (n r : ℕ) (E : Set (ℕ → ℕ)) (hE : MeasurableSet E)
    (htr : (truncateStream n) ⁻¹' E=E) :
    p.streamLaw (E ∩ {x | x n=r})=p.streamLaw E*p.law r := by
  have h := (p.truncate_indep_next n).measure_inter_preimage_eq_mul E {r} hE
    (measurableSet_singleton _)
  rw [htr] at h
  have he := (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) n).measure_preimage
    (measurableSet_singleton r).nullMeasurableSet
  change p.streamLaw ((fun x => x n) ⁻¹' {r})=p.law.toMeasure {r} at he
  rw [he] at h
  simpa only [Set.preimage,Set.mem_singleton_iff,p.law_singleton,p.law_apply] using h


lemma survival_endpoint_truncate (j n : ℕ) :
    (truncateStream n) ⁻¹' {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n}=
    {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} := by
  ext x
  change (_ ∧ _) ↔ (_ ∧ _)
  simp only [negativeSurvival,integerSum_truncateStream x le_rfl]
  constructor <;> rintro ⟨he,hs⟩ <;> refine ⟨he,?_⟩
  · intro k hk hkn
    simpa only [integerSum_truncateStream x hkn] using hs k hk hkn
  · intro k hk hkn
    simpa only [integerSum_truncateStream x hkn] using hs k hk hkn


lemma CriticalEvenOffspring.negative_potential_zero (p : CriticalEvenOffspring) :
    (∑' n, p.streamLaw {x | integerSum x n=0 ∧ negativeSurvival x n})=1 := by
  rw [tsum_eq_single 0]
  · have he : {x | integerSum x 0=0 ∧ negativeSurvival x 0}=(Set.univ : Set (ℕ → ℕ)) := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true,integerSum_zero,true_and]
      intro k hk hkn
      omega
    rw [he,measure_univ]
  · intro n hn
    have he : {x | integerSum x n=0 ∧ negativeSurvival x n}=(∅ : Set (ℕ → ℕ)) := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_and]
      intro hx hs
      have h := hs n (Nat.pos_of_ne_zero hn) le_rfl
      omega
    rw [he,measure_empty]


lemma CriticalEvenOffspring.negative_potential (p : CriticalEvenOffspring) (j : ℕ) :
    (∑' n, p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n})=1 := by
  cases j with
  | zero => simpa using p.negative_potential_zero
  | succ j => exact p.negative_potential_one _ (by omega)

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_LadderRecords
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma measurableSet_weakLadderHit (n k : ℕ) : MeasurableSet {x | weakLadderHit x n k} := by
  unfold weakLadderHit negativeSurvival
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_lt (measurable_integerSum j) measurable_const).inter
    (measurableSet_eq_fun (measurable_integerSum (n+1)) measurable_const)


lemma weakLadderHit_decomposition (n k : ℕ) :
    {x | weakLadderHit x n k}=⋃ j : ℕ,
      {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} ∩ {x | x n=j+k+1} := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  constructor
  · rintro ⟨hs,he⟩
    have hn : integerSum x n ≤ 0 := by
      cases n with
      | zero => simp
      | succ n => exact (hs _ (by omega) le_rfl).le
    refine ⟨(-integerSum x n).toNat,⟨?_,hs⟩,?_⟩
    · rw [Int.toNat_of_nonneg (by omega)]
      omega
    · rw [integerSum_succ] at he
      have hj := Int.toNat_of_nonneg (show 0 ≤ -integerSum x n by omega)
      omega
  · rintro ⟨j,⟨he,hs⟩,hx⟩
    refine ⟨hs,?_⟩
    rw [integerSum_succ,he,hx]
    push_cast
    ring


lemma weakLadderHit_decomposition_disjoint (n k : ℕ) :
    Pairwise (fun j l : ℕ => Disjoint
      ({x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} ∩ {x | x n=j+k+1})
      ({x | integerSum x n=-(l:ℤ) ∧ negativeSurvival x n} ∩ {x | x n=l+k+1})) := by
  intro j l hjl
  apply Set.disjoint_left.mpr
  intro x hj hl
  exact hjl (by have := hj.1.1; have := hl.1.1; omega)


lemma CriticalEvenOffspring.weakLadderHit_mass (p : CriticalEvenOffspring) (n k : ℕ) :
    p.streamLaw {x | weakLadderHit x n k}=
    ∑' j : ℕ, p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} * p.law (j+k+1) := by
  rw [weakLadderHit_decomposition,measure_iUnion (weakLadderHit_decomposition_disjoint n k)]
  · apply tsum_congr
    intro j
    exact p.prefix_inter_next n (j+k+1) _ (measurableSet_survival_endpoint j n)
      (survival_endpoint_truncate j n)
  · intro j
    exact (measurableSet_survival_endpoint j n).inter
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)


theorem CriticalEvenOffspring.weakLadder_overshoot_mass (p : CriticalEvenOffspring) (k : ℕ) :
    (∑' n, p.streamLaw {x | weakLadderHit x n k})=∑' j : ℕ, p.law (j+k+1) := by
  simp_rw [p.weakLadderHit_mass]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro j
  rw [ENNReal.tsum_mul_right,p.negative_potential,one_mul]


lemma sum_range_cast_nat (r : ℕ) :
    (∑ k ∈ Finset.range r,(k:ℝ))=((r:ℝ)^2-r)/2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring


lemma tail_tsum_first_moment (f : ℕ → ℝ≥0∞) :
    (∑' k : ℕ, (k:ℝ≥0∞)*(∑' j : ℕ, f (j+k+1)))=
    ∑' r : ℕ, ENNReal.ofReal (((r:ℝ)^2-r)/2)*f r := by
  simp_rw [tail_tsum_ite,← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro r
  rw [tsum_eq_sum (s := Finset.range r) (fun k hk => by simp [show ¬ k < r from by simpa using hk])]
  have he : (∑ k ∈ Finset.range r, (k:ℝ≥0∞)*(if k < r then f r else 0))=
      (∑ k ∈ Finset.range r,(k:ℝ≥0∞))*f r := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k hk => by rw [ite_eq_left (Finset.mem_range.mp hk)]
  rw [he]
  congr 1
  rw [← sum_range_cast_nat,ENNReal.ofReal_sum_of_nonneg (fun k _ => Nat.cast_nonneg k)]
  simp


lemma CriticalEvenOffspring.variance_eq_second_sub_one (p : CriticalEvenOffspring) :
    p.variance=(∑' k : ℕ, (k:ℝ)^2*p.mass k)-1 := by
  have he : (fun k : ℕ => ((k:ℝ)-1)^2*p.mass k)=
      (fun k : ℕ => (k:ℝ)^2*p.mass k-2*((k:ℝ)*p.mass k)+p.mass k) := by
    funext k
    ring
  rw [variance,he]
  rw [Summable.tsum_add (p.second.sub (p.mean.summable.mul_left 2)) p.total.summable,
    Summable.tsum_sub p.second (p.mean.summable.mul_left 2),tsum_mul_left,p.mean.tsum_eq,p.total.tsum_eq]
  ring


lemma CriticalEvenOffspring.ladder_first_moment (p : CriticalEvenOffspring) :
    (∑' k : ℕ, (k:ℝ≥0∞)*p.ladderLaw k)=ENNReal.ofReal (p.variance/2) := by
  simp only [p.ladderLaw_apply]
  rw [tail_tsum_first_moment]
  have hs : Summable (fun r : ℕ => (((r:ℝ)^2-r)/2)*p.mass r) := by
    apply Summable.congr ((p.second.sub p.mean.summable).div_const 2)
    intro r
    ring
  have hn (r : ℕ) : 0 ≤ (((r:ℝ)^2-r)/2)*p.mass r := by
    apply mul_nonneg _ (p.nonneg r)
    have hr : r=0 ∨ 1 ≤ r := by omega
    rcases hr with hr | hr
    · simp [hr]
    · have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
  have he : (∑' r : ℕ, (((r:ℝ)^2-r)/2)*p.mass r)=p.variance/2 := by
    have hf : (fun r : ℕ => (((r:ℝ)^2-r)/2)*p.mass r)=
        fun r : ℕ => ((r:ℝ)^2*p.mass r-(r:ℝ)*p.mass r)/2 := by funext r; ring
    rw [hf,tsum_div_const,
      Summable.tsum_sub p.second p.mean.summable,p.mean.tsum_eq,p.variance_eq_second_sub_one]
  rw [← he,ENNReal.ofReal_tsum_of_nonneg hn hs]
  apply tsum_congr
  intro r
  rw [p.law_apply,ENNReal.ofReal_mul (by
    have hr : r=0 ∨ 1 ≤ r := by omega
    rcases hr with hr | hr
    · simp [hr]
    · have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith)]


lemma measurable_streamShift (n : ℕ) : Measurable (streamShift n) := by
  apply Measurable.of_eval
  intro k
  exact measurable_pi_apply _


lemma CriticalEvenOffspring.streamShift_preserving (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (streamShift n) p.streamLaw p.streamLaw := by
  have hi : iIndepFun (fun k (x : ℕ → ℕ) => x k) p.streamLaw :=
    iIndepFun_infinitePi (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)
  have hinj : Function.Injective (fun k : ℕ => n+k) := by intro a b h; dsimp at h; omega
  have h := (hi.precomp hinj).map_fun_eq_infinitePi_map (fun k => measurable_pi_apply (n+k))
  refine ⟨measurable_streamShift n,?_⟩
  change p.streamLaw.map (fun ω i => ω (n+i))=p.streamLaw
  rw [h]
  unfold CriticalEvenOffspring.streamLaw
  congr 1
  funext k
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) (n+k)).map_eq


lemma CriticalEvenOffspring.truncate_indep_shift (p : CriticalEvenOffspring) (n : ℕ) :
    IndepFun (truncateStream n) (streamShift n) p.streamLaw := by
  classical
  apply IndepFun.indepFun_process (measurable_truncateStream n) (fun k => measurable_pi_apply (n+k))
  intro I
  have hi : iIndepFun (fun k (x : ℕ → ℕ) => x k) p.streamLaw :=
    iIndepFun_infinitePi (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) (I.image (fun k => n+k)) := by
    apply Finset.disjoint_left.mpr
    intro k hk hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    have := Finset.mem_range.mp hk
    omega
  have h := hi.indepFun_finset (Finset.range n) (I.image (fun k => n+k)) hd
    (fun k => measurable_pi_apply k)
  let f : ((Finset.range n) → ℕ) → (ℕ → ℕ) :=
    fun x k => if hk : k<n then x ⟨k,Finset.mem_range.mpr hk⟩ else 0
  let g : (I.image (fun k => n+k) → ℕ) → (I → ℕ) :=
    fun x k => x ⟨n+k,Finset.mem_image.mpr ⟨k,k.property,rfl⟩⟩
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro k
    dsimp [f]
    split_ifs <;> fun_prop
  have hg : Measurable g := by fun_prop
  exact h.comp hf hg


lemma CriticalEvenOffspring.prefix_inter_shift (p : CriticalEvenOffspring)
    (n : ℕ) (E F : Set (ℕ → ℕ)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (htr : (truncateStream n) ⁻¹' E=E) :
    p.streamLaw (E ∩ (streamShift n) ⁻¹' F)=p.streamLaw E*p.streamLaw F := by
  have h := (p.truncate_indep_shift n).measure_inter_preimage_eq_mul E F hE hF
  rw [htr,(p.streamShift_preserving n).measure_preimage hF.nullMeasurableSet] at h
  exact h


lemma weakLadderHit_truncate (n k : ℕ) :
    (truncateStream (n+1)) ⁻¹' {x | weakLadderHit x n k}={x | weakLadderHit x n k} := by
  ext x
  change weakLadderHit (truncateStream (n+1) x) n k ↔ weakLadderHit x n k
  simp only [weakLadderHit,negativeSurvival,integerSum_truncateStream x le_rfl]
  constructor <;> rintro ⟨hs,he⟩ <;> refine ⟨?_,he⟩
  · intro j hj hjn
    simpa only [integerSum_truncateStream x (by omega : j ≤ n+1)] using hs j hj hjn
  · intro j hj hjn
    simpa only [integerSum_truncateStream x (by omega : j ≤ n+1)] using hs j hj hjn


lemma weakLadderHit_unique {x : ℕ → ℕ} {n k m l : ℕ}
    (hn : weakLadderHit x n k) (hm : weakLadderHit x m l) : n=m ∧ k=l := by
  have he : n=m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hh := hm.1 (n+1) (by omega) (by omega)
      rw [hn.2] at hh
      omega
    · have hh := hn.1 (m+1) (by omega) (by omega)
      rw [hm.2] at hh
      omega
  refine ⟨he,?_⟩
  subst m
  have := hn.2
  have := hm.2
  omega


lemma weakLadderHit_pairwise : Pairwise (fun a b : ℕ × ℕ =>
    Disjoint {x | weakLadderHit x a.1 a.2} {x | weakLadderHit x b.1 b.2}) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x ha hb
  have h := weakLadderHit_unique ha hb
  exact hab (Prod.ext h.1 h.2)


lemma CriticalEvenOffspring.ae_weakLadderHit (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw, ∃ n k, weakLadderHit x n k := by
  have he : {x | ∃ n k, weakLadderHit x n k}=⋃ a : ℕ×ℕ,{x | weakLadderHit x a.1 a.2} := by
    ext x
    simp
  apply (mem_ae_iff_prob_eq_one (show MeasurableSet {x | ∃ n k, weakLadderHit x n k} from by
    rw [he]; exact MeasurableSet.iUnion fun a => measurableSet_weakLadderHit a.1 a.2)).mpr
  rw [he,measure_iUnion weakLadderHit_pairwise (fun a => measurableSet_weakLadderHit a.1 a.2),
    ENNReal.tsum_prod',ENNReal.tsum_comm]
  simp_rw [p.weakLadder_overshoot_mass]
  exact p.ladder_total


lemma measurableSet_hasWeakLadder : MeasurableSet {x : ℕ → ℕ | ∃ n, 0 ≤ integerSum x (n+1)} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun n => measurableSet_le measurable_const (measurable_integerSum (n+1))


lemma measurable_ladderIndex : Measurable ladderIndex := by
  classical
  apply measurable_find (fun x => ladderPredicate_exists x)
  intro n
  unfold ladderPredicate
  simp only [Set.ofPred_or,Set.ofPred_and,← Set.compl_ofPred]
  exact (measurableSet_le measurable_const (measurable_integerSum (n+1))).union
    (measurableSet_hasWeakLadder.compl.inter (MeasurableSet.const _))


lemma ladderIndex_eq_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderIndex x=n := by
  classical
  apply (Nat.find_eq_iff (ladderPredicate_exists x)).mpr
  refine ⟨Or.inl (by rw [h.2]; positivity),?_⟩
  intro j hj
  rintro (hj' | hj')
  · have hh := h.1 (j+1) (by omega) (by omega)
    omega
  · exact hj'.1 ⟨n,by rw [h.2]; positivity⟩


lemma measurable_ladderOvershoot : Measurable ladderOvershoot := by
  have hs : Measurable (fun x : ℕ → ℕ => (x,ladderIndex x+1)) :=
    measurable_id.prodMk (measurable_ladderIndex.add_const 1)
  have he : Measurable (fun z : (ℕ → ℕ)×ℕ => integerSum z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_integerSum n
  exact (measurable_of_countable (f := Int.toNat)).comp (he.comp hs)


lemma measurable_ladderTail : Measurable ladderTail := by
  apply Measurable.of_eval
  intro k
  have hs : Measurable (fun x : ℕ → ℕ => (x,ladderIndex x+1+k)) :=
    measurable_id.prodMk ((measurable_ladderIndex.add_const 1).add_const k)
  have he : Measurable (fun z : (ℕ → ℕ)×ℕ => z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_pi_apply n
  exact he.comp hs


lemma ladderOvershoot_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderOvershoot x=k := by
  rw [ladderOvershoot,ladderIndex_eq_of_hit h,h.2,Int.toNat_natCast]


lemma ladderTail_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderTail x=streamShift (n+1) x := by
  rw [ladderTail,ladderIndex_eq_of_hit h]


lemma CriticalEvenOffspring.ladder_slice_mass (p : CriticalEvenOffspring)
    (k : ℕ) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw ({x | ladderOvershoot x=k} ∩ ladderTail ⁻¹' F)=
      p.ladderLaw k*p.streamLaw F := by
  have he : ({x | ladderOvershoot x=k} ∩ ladderTail ⁻¹' F : Set (ℕ → ℕ)) =ᵐ[p.streamLaw]
      ⋃ n : ℕ, {x | weakLadderHit x n k} ∩ (streamShift (n+1)) ⁻¹' F := by
    filter_upwards [p.ae_weakLadderHit] with x hx
    apply propext
    obtain ⟨n,l,hh⟩ := hx
    constructor
    · intro hm
      have hl : l=k := (ladderOvershoot_of_hit hh).symm.trans hm.1
      subst l
      exact Set.mem_iUnion.mpr ⟨n,hh,by simpa only [Set.mem_preimage,← ladderTail_of_hit hh] using hm.2⟩
    · intro hm
      obtain ⟨m,hm,hxF⟩ := Set.mem_iUnion.mp hm
      exact ⟨ladderOvershoot_of_hit hm,by simpa only [Set.mem_preimage,ladderTail_of_hit hm] using hxF⟩
  rw [measure_congr he,measure_iUnion]
  · simp_rw [p.prefix_inter_shift (n := _)
      (hE := measurableSet_weakLadderHit _ _) (hF := hF) (htr := weakLadderHit_truncate _ _)]
    rw [ENNReal.tsum_mul_right,p.weakLadder_overshoot_mass]
    rfl
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hn hm
    exact hnm (weakLadderHit_unique hn.1 hm.1).1
  · intro n
    exact (measurableSet_weakLadderHit n k).inter ((measurable_streamShift (n+1)) hF)


lemma countable_slice_rectangle {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (ν : Measure β) (q : PMF ℕ) (Y : Ω → ℕ) (T : Ω → β)
    (hY : Measurable Y) (hT : Measurable T)
    (h : ∀ k E, MeasurableSet E → μ ({x | Y x=k} ∩ T ⁻¹' E)=q k*ν E)
    (A : Set ℕ) (E : Set β) (hA : MeasurableSet A) (hE : MeasurableSet E) :
    μ (Y ⁻¹' A ∩ T ⁻¹' E)=q.toMeasure A*ν E := by
  classical
  have he : Y ⁻¹' A ∩ T ⁻¹' E=⋃ k ∈ A, {x | Y x=k} ∩ T ⁻¹' E := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨Y x,hx.1,rfl,hx.2⟩
    · rintro ⟨k,hk,he,hx⟩
      exact ⟨he.symm ▸ hk,hx⟩
  rw [he,measure_biUnion (Set.to_countable A)]
  · simp_rw [h _ E hE]
    rw [ENNReal.tsum_mul_right]
    congr 1
    rw [tsum_subtype,PMF.toMeasure_apply _ hA]
  · intro k _ l _ hkl
    apply Set.disjoint_left.mpr
    intro x hk hl
    exact hkl (hk.1.symm.trans hl.1)
  · intro k _
    exact (measurableSet_eq_fun hY measurable_const).inter (hT hE)


lemma CriticalEvenOffspring.ladder_rectangle (p : CriticalEvenOffspring)
    (A : Set ℕ) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw (ladderOvershoot ⁻¹' A ∩ ladderTail ⁻¹' F)=
      p.ladderLaw.toMeasure A*p.streamLaw F :=
  countable_slice_rectangle p.streamLaw p.streamLaw p.ladderLaw ladderOvershoot ladderTail
    measurable_ladderOvershoot measurable_ladderTail p.ladder_slice_mass A F ((Set.to_countable A).measurableSet) hF


lemma CriticalEvenOffspring.ladder_hasLaw (p : CriticalEvenOffspring) :
    HasLaw ladderOvershoot p.ladderLaw.toMeasure p.streamLaw := by
  refine ⟨measurable_ladderOvershoot.aemeasurable,?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_ladderOvershoot hA]
  simpa using p.ladder_rectangle A Set.univ MeasurableSet.univ


lemma CriticalEvenOffspring.ladderTail_preserving (p : CriticalEvenOffspring) :
    MeasurePreserving ladderTail p.streamLaw p.streamLaw := by
  refine ⟨measurable_ladderTail,?_⟩
  apply Measure.ext
  intro F hF
  rw [Measure.map_apply measurable_ladderTail hF]
  simpa using p.ladder_rectangle Set.univ F hF


lemma CriticalEvenOffspring.ladder_indep_tail (p : CriticalEvenOffspring) :
    IndepFun ladderOvershoot ladderTail p.streamLaw := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A F hA hF
  rw [(p.ladderTail_preserving).measure_preimage hF.nullMeasurableSet]
  have h := (p.ladder_hasLaw.measurePreserving measurable_ladderOvershoot).measure_preimage hA.nullMeasurableSet
  rw [h]
  exact p.ladder_rectangle A F hF


lemma CriticalEvenOffspring.ladder_integrable (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => (k:ℝ)) p.ladderLaw.toMeasure := by
  rw [← Measure.sum_smul_dirac p.ladderLaw.toMeasure,integrable_sum_dirac_iff]
  · have hs : Summable (fun k : ℕ => ((k:ℝ≥0∞)*p.ladderLaw k).toReal) :=
      ENNReal.summable_toReal (by rw [p.ladder_first_moment]; exact ENNReal.ofReal_ne_top)
    simpa [PMF.toMeasure_apply_singleton,ENNReal.toReal_mul,mul_comm] using hs
  · intro k
    exact measure_ne_top _ _


lemma CriticalEvenOffspring.ladder_integral (p : CriticalEvenOffspring) :
    ∫ k : ℕ,(k:ℝ) ∂p.ladderLaw.toMeasure=p.variance/2 := by
  rw [integral_countable p.ladder_integrable]
  have h := congrArg ENNReal.toReal p.ladder_first_moment
  rw [ENNReal.toReal_ofReal (div_nonneg p.variance_pos.le (by norm_num)),
    ENNReal.tsum_toReal_eq (fun k => ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))] at h
  simpa [measureReal_def,PMF.toMeasure_apply_singleton,ENNReal.toReal_mul,mul_comm] using h


lemma measurable_renewalIncrement (i : ℕ) : Measurable (renewalIncrement i) :=
  measurable_ladderOvershoot.comp (measurable_ladderTail.iterate i)


lemma CriticalEvenOffspring.renewal_iid (p : CriticalEvenOffspring) :
    iIndepFun renewalIncrement p.streamLaw :=
  regenerative_iIndepFun p.streamLaw ladderOvershoot ladderTail
    measurable_ladderOvershoot p.ladderTail_preserving p.ladder_indep_tail


lemma CriticalEvenOffspring.renewal_hasLaw (p : CriticalEvenOffspring) (i : ℕ) :
    HasLaw (renewalIncrement i) p.ladderLaw.toMeasure p.streamLaw :=
  p.ladder_hasLaw.comp (p.ladderTail_preserving.iterate i).hasLaw


lemma CriticalEvenOffspring.renewal_strong_law (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,(renewalIncrement i x : ℝ))/(n:ℝ))
        atTop (𝓝 (p.variance/2)) := by
  let X : ℕ → (ℕ → ℕ) → ℝ := fun i x => (renewalIncrement i x : ℝ)
  have hind : iIndepFun X p.streamLaw := p.renewal_iid.comp (fun _ => Nat.cast)
    (fun _ => measurable_of_countable _)
  have hint : Integrable (X 0) p.streamLaw :=
    ((p.renewal_hasLaw 0).measurePreserving (measurable_renewalIncrement 0)).integrable_comp_of_integrable
      p.ladder_integrable
  have hid : ∀ i, IdentDistrib (X i) (X 0) p.streamLaw p.streamLaw := by
    intro i
    exact ((p.renewal_hasLaw i).identDistrib (p.renewal_hasLaw 0)).comp (measurable_of_countable _)
  have hm : ∫ x, X 0 x ∂p.streamLaw=p.variance/2 := by
    exact ((p.renewal_hasLaw 0).integral_comp
      (measurable_of_countable (fun k : ℕ => (k:ℝ))).aestronglyMeasurable).trans p.ladder_integral
  simpa only [hm] using strong_law_ae_real X hint (fun _ _ hij => hind.indepFun hij) hid


lemma renewalCount_spec {τ : ℕ → ℕ} (h₀ : τ 0=0) (n : ℕ) :
    τ (renewalCount τ n) ≤ n :=
  Nat.findGreatest_spec (P := fun r => τ r ≤ n) (Nat.zero_le n) (by simp [h₀])


lemma le_renewalCount_iff {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0)
    (r n : ℕ) : r ≤ renewalCount τ n ↔ τ r ≤ n := by
  constructor
  · intro h
    exact (hτ.monotone h).trans (renewalCount_spec h₀ n)
  · intro h
    exact Nat.le_findGreatest ((hτ.le_apply (x := r)).trans h) h


lemma renewalCount_succ_gt {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0)
    (n : ℕ) : n < τ (renewalCount τ n+1) := by
  rw [← not_le,← le_renewalCount_iff hτ h₀]
  omega


lemma renewalCount_mono {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0) :
    Monotone (renewalCount τ) := by
  intro m n hmn
  rw [le_renewalCount_iff hτ h₀]
  exact (renewalCount_spec h₀ m).trans hmn


lemma renewalCount_at {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0) (r : ℕ) :
    renewalCount τ (τ r)=r := by
  apply le_antisymm
  · exact hτ.le_iff_le.mp (renewalCount_spec h₀ (τ r))
  · exact (le_renewalCount_iff hτ h₀ r (τ r)).mpr le_rfl


lemma LadderEnumeration.le_level {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (k : ℕ) : S k ≤ S (τ (renewalCount τ k)) := by
  have hk := renewalCount_spec h.zero k
  by_cases he : τ (renewalCount τ k)=k
  · rw [he]
  · exact (h.between _ k (lt_of_le_of_ne hk he) (renewalCount_succ_gt h.strictMono h.zero k)).le


lemma LadderEnumeration.maximum {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) {k n : ℕ} (hkn : k ≤ n) :
    S k ≤ S (τ (renewalCount τ n)) :=
  (h.le_level k).trans (h.level_mono (renewalCount_mono h.strictMono h.zero hkn))


lemma LadderEnumeration.record_at {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (r : ℕ) {k : ℕ} (hk : k ≤ τ r) :
    S k ≤ S (τ r) := by
  simpa only [renewalCount_at h.strictMono h.zero] using h.maximum hk


lemma LadderEnumeration.records {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    weakRecords S n=(Finset.Icc 1 (renewalCount τ n)).image τ := by
  classical
  ext k
  rw [mem_weakRecords,Finset.mem_image]
  constructor
  · rintro ⟨hk1,hkn,hrec⟩
    let r := renewalCount τ k
    have hr : τ r=k := by
      by_contra he
      have hlt := lt_of_le_of_ne (renewalCount_spec h.zero k) he
      exact not_lt_of_ge (hrec (τ r) (renewalCount_spec h.zero k))
        (h.between r k hlt (renewalCount_succ_gt h.strictMono h.zero k))
    refine ⟨r,Finset.mem_Icc.mpr ⟨?_,?_⟩,hr⟩
    · by_contra hn
      have : r=0 := by omega
      rw [this,h.zero] at hr
      omega
    · exact (le_renewalCount_iff h.strictMono h.zero r n).mpr (hr ▸ hkn)
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨hr1,hrn⟩ := Finset.mem_Icc.mp hr
    refine ⟨?_,(le_renewalCount_iff h.strictMono h.zero r n).mp hrn,fun j hj => h.record_at r hj⟩
    exact hr1.trans h.strictMono.le_apply


lemma LadderEnumeration.card_records {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    (weakRecords S n).card=renewalCount τ n := by
  classical
  rw [h.records,Finset.card_image_of_injective _ h.strictMono.injective,Nat.card_Icc]
  omega


lemma LadderEnumeration.first_records_below {α : Type*} [LinearOrder α]
    {S : ℕ → α} {τ : ℕ → ℕ} (h : LadderEnumeration S τ) (n m : ℕ)
    (z : α) (hz : z ≤ S (τ m)) :
    ((weakRecords S n).filter fun k => S k < z).card ≤ m := by
  classical
  have hsub : (weakRecords S n).filter (fun k => S k < z) ⊆
      (Finset.range m).image τ := by
    intro k hk
    obtain ⟨hkr,hkz⟩ := Finset.mem_filter.mp hk
    rw [h.records] at hkr
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hkr
    refine Finset.mem_image.mpr ⟨r,Finset.mem_range.mpr ?_,rfl⟩
    by_contra hn
    exact not_lt_of_ge (hz.trans (h.level_mono (by omega : m ≤ r))) hkz
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans_eq (Finset.card_range m))


lemma ladderTime_strictMono (x : ℕ → ℕ) : StrictMono (ladderTime x) := by
  apply strictMono_nat_of_lt_succ
  intro r
  dsimp [ladderTime]
  omega


lemma streamShift_add (a b : ℕ) (x : ℕ → ℕ) :
    streamShift a (streamShift b x)=streamShift (b+a) x := by
  funext k
  change x (b+(a+k))=x ((b+a)+k)
  rw [Nat.add_assoc]


lemma ladderTail_iterate (x : ℕ → ℕ) (r : ℕ) :
    ladderTail^[r] x=streamShift (ladderTime x r) x := by
  induction r with
  | zero =>
    change x=(fun k => x (0+k))
    funext k
    rw [Nat.zero_add]
  | succ r ih =>
    rw [Function.iterate_succ_apply',ladderTail,ih,streamShift_add,ladderTime,ih]


lemma integerSum_shift (x : ℕ → ℕ) (a k : ℕ) :
    integerSum (streamShift a x) k=integerSum x (a+k)-integerSum x a := by
  unfold integerSum streamShift
  rw [Finset.sum_range_add]
  ring


lemma CriticalEvenOffspring.ae_all_ladders (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw, HasAllLadders x := by
  rw [show HasAllLadders=(fun x => ∀ r, ∃ n k, weakLadderHit (ladderTail^[r] x) n k) from rfl,
    ae_all_iff]
  intro r
  exact (p.ladderTail_preserving.iterate r).quasiMeasurePreserving.ae p.ae_weakLadderHit


lemma ladderTime_step_level {x : ℕ → ℕ} (hx : HasAllLadders x) (r : ℕ) :
    integerSum x (ladderTime x (r+1))-integerSum x (ladderTime x r)=
      (renewalIncrement r x:ℤ) := by
  obtain ⟨n,k,h⟩ := hx r
  have hidx := ladderIndex_eq_of_hit h
  have hval := ladderOvershoot_of_hit h
  change _=(ladderOvershoot (ladderTail^[r] x):ℤ)
  rw [hval,ladderTime,hidx,← integerSum_shift,← ladderTail_iterate]
  exact h.2


lemma ladderTime_between {x : ℕ → ℕ} (hx : HasAllLadders x) (r k : ℕ)
    (hlo : ladderTime x r<k) (hhi : k<ladderTime x (r+1)) :
    integerSum x k < integerSum x (ladderTime x r) := by
  obtain ⟨n,j,h⟩ := hx r
  have hidx := ladderIndex_eq_of_hit h
  have hhi' : k<ladderTime x r+(n+1) := by simpa only [ladderTime,hidx] using hhi
  have hs := h.1 (k-ladderTime x r) (by omega) (by omega)
  rw [ladderTail_iterate,integerSum_shift,Nat.add_sub_of_le hlo.le] at hs
  omega


lemma ladderTime_enumeration {x : ℕ → ℕ} (hx : HasAllLadders x) :
    LadderEnumeration (integerSum x) (ladderTime x) := by
  refine ⟨rfl,ladderTime_strictMono x,?_,ladderTime_between hx⟩
  apply monotone_nat_of_le_succ
  intro r
  have := ladderTime_step_level hx r
  dsimp only [Function.comp_apply]
  omega


lemma ladderTime_level_sum {x : ℕ → ℕ} (hx : HasAllLadders x) (r : ℕ) :
    integerSum x (ladderTime x r)=∑ i ∈ Finset.range r,(renewalIncrement i x:ℤ) := by
  induction r with
  | zero => simp [integerSum]
  | succ r ih =>
    rw [Finset.sum_range_succ,← ih]
    have := ladderTime_step_level hx r
    omega


lemma linear_remainder_of_ratio {L : ℕ → ℝ} {ν ε : ℝ} (hν : 0<ν) (hε : 0<ε)
    (hL : ∀ r, 0 ≤ L r) (ht : Tendsto (fun r : ℕ => L r/(r:ℝ)) atTop (𝓝 ν)) :
    ∃ A : ℕ, ∀ r, |L r-ν*r| ≤ ε*L r+A := by
  let δ := min (ε*ν/2) (ν/2)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp ht) δ hδ)
  have hlarge (r : ℕ) (hr : N+1 ≤ r) : |L r-ν*r| ≤ ε*L r := by
    have hr0 : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have h := hN r (by omega)
    rw [Real.dist_eq,abs_sub_lt_iff] at h
    have hlo : ν/2*(r:ℝ) ≤ L r := by
      have hδν : δ ≤ ν/2 := min_le_right _ _
      have hh : ν/2 ≤ L r/(r:ℝ) := by linarith
      exact (le_div_iff₀ hr0).mp hh
    have he : |L r-ν*r| ≤ δ*r := by
      have hh : |L r/(r:ℝ)-ν| ≤ δ := abs_le.mpr ⟨by linarith,by linarith⟩
      have heq : L r/(r:ℝ)-ν=(L r-ν*r)/(r:ℝ) := by field_simp
      rw [heq,abs_div,abs_of_pos hr0] at hh
      exact (div_le_iff₀ hr0).mp hh
    exact he.trans (by have hh := min_le_left (ε*ν/2) (ν/2); nlinarith)
  obtain ⟨A,hA⟩ := exists_nat_ge (∑ r ∈ Finset.range (N+1),|L r-ν*r|)
  refine ⟨A,fun r => ?_⟩
  by_cases hr : N+1 ≤ r
  · exact (hlarge r hr).trans (le_add_of_nonneg_right (Nat.cast_nonneg A))
  · have hh : |L r-ν*r| ≤ ∑ k ∈ Finset.range (N+1),|L k-ν*k| :=
      Finset.single_le_sum (f := fun k => |L k-ν*k|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (show r<N+1 by omega))
    exact (hh.trans hA).trans (le_add_of_nonneg_left (mul_nonneg hε.le (hL r)))


lemma uniform_remainder_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (L : ℕ → Ω → ℝ) (hL : ∀ r, Measurable (L r))
    (ν ε : ℝ) (hae : ∀ᵐ x ∂μ, ∃ A : ℕ, ∀ r, |L r x-ν*r| ≤ ε*L r x+A) :
    Tendsto (fun A : ℕ => μ {x | ∃ r, ε*L r x+A < |L r x-ν*r|}) atTop (𝓝 0) := by
  let E : ℕ → Set Ω := fun A => {x | ∃ r, ε*L r x+A < |L r x-ν*r|}
  have hm (A : ℕ) : MeasurableSet (E A) := by
    dsimp [E]
    simp only [ofPred_exists]
    exact MeasurableSet.iUnion fun r => measurableSet_lt
      ((hL r).const_mul ε |>.add_const A) (((hL r).sub_const (ν*r)).abs)
  have hanti : Antitone E := by
    intro A B hAB x hx
    obtain ⟨r,hr⟩ := hx
    exact ⟨r,lt_of_le_of_lt (add_le_add le_rfl (Nat.cast_le.mpr hAB)) hr⟩
  have hz : μ (⋂ A, E A)=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hae] with x hx
    obtain ⟨A,hA⟩ := hx
    intro hmem
    obtain ⟨r,hr⟩ := Set.mem_iInter.mp hmem A
    exact not_lt_of_ge (hA r) hr
  simpa only [hz,Function.comp_def,E] using tendsto_measure_iInter_atTop (μ := μ) (fun A => (hm A).nullMeasurableSet)
    hanti ⟨0,measure_ne_top _ _⟩


lemma integrable_neg_exp_nat {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω → ℕ) (hY : Measurable Y) :
    Integrable (fun x => Real.exp (-(Y x:ℝ))) μ := by
  apply Integrable.of_bound ((measurable_of_countable (fun k : ℕ => Real.exp (-(k:ℝ)))).comp hY).aestronglyMeasurable 1
  filter_upwards with x
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))


lemma nat_laplace_lt_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω → ℕ) (hY : Measurable Y)
    (hint : Integrable (fun x => (Y x:ℝ)) μ) (hmean : 0 < ∫ x,(Y x:ℝ) ∂μ) :
    0 < (∫ x,Real.exp (-(Y x:ℝ)) ∂μ) ∧ (∫ x,Real.exp (-(Y x:ℝ)) ∂μ)<1 := by
  have hi := integrable_neg_exp_nat μ Y hY
  have hle : (fun x => Real.exp (-(Y x:ℝ))) ≤ᵐ[μ] fun _ => 1 :=
    ae_of_all _ fun _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  refine ⟨integral_exp_pos hi,lt_of_le_of_ne ?_ ?_⟩
  · simpa using integral_mono_ae hi (integrable_const (1:ℝ)) hle
  · intro he
    have he' : (∫ x,Real.exp (-(Y x:ℝ)) ∂μ)=∫ _ : Ω,(1:ℝ) ∂μ := by simpa using he
    have hae := (integral_eq_iff_of_ae_le hi (integrable_const (1:ℝ)) hle).mp he'
    have hz : (fun x => (Y x:ℝ)) =ᵐ[μ] 0 := by
      filter_upwards [hae] with x hx
      have : -(Y x:ℝ)=0 := (Real.exp_eq_one_iff _).mp hx
      simpa using neg_eq_zero.mp this
    have : (∫ x,(Y x:ℝ) ∂μ)=0 := (integral_eq_zero_iff_of_nonneg (fun _ => Nat.cast_nonneg _) hint).mpr hz
    linarith


lemma iid_nat_laplace_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℕ) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) (n : ℕ) :
    (∫ x,Real.exp (-(∑ i ∈ Finset.range n,(Y i x:ℝ))) ∂μ)=
      (∫ x,Real.exp (-(Y 0 x:ℝ)) ∂μ)^n := by
  let Z : Fin n → Ω → ℝ := fun i x => Real.exp (-(Y i x:ℝ))
  have hZ : iIndepFun Z μ := (hind.precomp Fin.val_injective).comp
    (fun (_ : Fin n) (k : ℕ) => Real.exp (-(k:ℝ))) (fun _ => measurable_of_countable _)
  have he : ∀ x, Real.exp (-(∑ i ∈ Finset.range n,(Y i x:ℝ)))=∏ i : Fin n,Z i x := by
    intro x
    rw [← Finset.sum_neg_distrib,Real.exp_sum]
    exact (Fin.prod_univ_eq_prod_range _ n).symm
  simp_rw [he]
  rw [hZ.integral_fun_prod_eq_prod_integral (fun i =>
    ((measurable_of_countable (fun k : ℕ => Real.exp (-(k:ℝ)))).comp (hY i)).aestronglyMeasurable)]
  have hm (i : Fin n) : (∫ x,Z i x ∂μ)=∫ x,Real.exp (-(Y 0 x:ℝ)) ∂μ :=
    ((hident i).comp (measurable_of_countable (fun k : ℕ => Real.exp (-(k:ℝ))))).integral_eq
  simp_rw [hm]
  simp


lemma iid_nat_lower_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℕ) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hint : Integrable (fun x => (Y 0 x:ℝ)) μ) (hmean : 0 < ∫ x,(Y 0 x:ℝ) ∂μ) :
    ∃ c ρ : ℝ, 0 < c ∧ 0<ρ ∧ ρ<1 ∧ ∀ n : ℕ,
      μ {x | (∑ i ∈ Finset.range n,(Y i x:ℝ)) ≤ c*n} ≤ ENNReal.ofReal (ρ^n) := by
  let q := ∫ x,Real.exp (-(Y 0 x:ℝ)) ∂μ
  obtain ⟨hq0,hq1⟩ := nat_laplace_lt_one μ (Y 0) (hY 0) hint hmean
  change 0<q at hq0
  change q<1 at hq1
  let c := -Real.log q/2
  have hc : 0 < c := by
    dsimp [c]
    have : Real.log q<0 := Real.log_neg hq0 hq1
    linarith
  let ρ := Real.exp (-c)
  have hr0 : 0<ρ := Real.exp_pos _
  have hr1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hprod : Real.exp c*q=ρ := by
    change Real.exp c*q=Real.exp (-c)
    rw [← Real.exp_log hq0,← Real.exp_add]
    congr 1
    dsimp [c]
    ring
  refine ⟨c,ρ,hc,hr0,hr1,fun n => ?_⟩
  let F : Ω → ℝ := fun x => Real.exp (-(∑ i ∈ Finset.range n,(Y i x:ℝ)))
  have hm : Measurable F := by
    dsimp [F]
    fun_prop
  have hi : Integrable F μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _))
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun x => (Real.exp_pos _).le) hi (Real.exp (-c*n))
  have he : {x | Real.exp (-c*n) ≤ F x}=
      {x | (∑ i ∈ Finset.range n,(Y i x:ℝ)) ≤ c*n} := by
    ext x
    simp only [Set.mem_ofPred_eq,F,Real.exp_le_exp,neg_mul,neg_le_neg_iff]
  rw [he,iid_nat_laplace_sum μ Y hY hind hident n] at hmark
  have hp : μ.real {x | (∑ i ∈ Finset.range n,(Y i x:ℝ)) ≤ c*n} ≤ ρ^n := by
    have heq : Real.exp (-c*n)*ρ^n=q^n := by
      rw [← hprod,mul_pow,← Real.exp_nat_mul]
      rw [← mul_assoc,← Real.exp_add]
      have : -c*(n:ℝ)+(n:ℝ)*c=0 := by ring
      rw [this,Real.exp_zero,one_mul]
    rw [← heq] at hmark
    exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp hmark
  have hp' := ENNReal.ofReal_le_ofReal hp
  rwa [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at hp'


lemma measurable_renewalLevel (r : ℕ) : Measurable (renewalLevel r) := by
  unfold renewalLevel
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (measurable_renewalIncrement i)


lemma renewalLevel_nonneg (r : ℕ) (x : ℕ → ℕ) : 0 ≤ renewalLevel r x :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _


lemma CriticalEvenOffspring.renewal_uniform_remainder (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᵐ x ∂p.streamLaw, ∃ A : ℕ, ∀ r,
      |renewalLevel r x-(p.variance/2)*r| ≤ ε*renewalLevel r x+A := by
  filter_upwards [p.renewal_strong_law] with x hx
  exact linear_remainder_of_ratio (half_pos p.variance_pos) hε
    (fun r => renewalLevel_nonneg r x) hx


lemma CriticalEvenOffspring.renewal_remainder_probability (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun A : ℕ => p.streamLaw {x | ∃ r,
      ε*renewalLevel r x+A < |renewalLevel r x-(p.variance/2)*r|}) atTop (𝓝 0) :=
  uniform_remainder_probability p.streamLaw renewalLevel measurable_renewalLevel
    (p.variance/2) ε (p.renewal_uniform_remainder hε)


lemma CriticalEvenOffspring.renewal_lower_tail (p : CriticalEvenOffspring) :
    ∃ c ρ : ℝ, 0 < c ∧ 0<ρ ∧ ρ<1 ∧ ∀ m : ℕ,
      p.streamLaw {x | renewalLevel m x ≤ c*m} ≤ ENNReal.ofReal (ρ^m) := by
  have hint : Integrable (fun x => (renewalIncrement 0 x:ℝ)) p.streamLaw :=
    ((p.renewal_hasLaw 0).measurePreserving (measurable_renewalIncrement 0)).integrable_comp_of_integrable
      p.ladder_integrable
  have hm : (∫ x,(renewalIncrement 0 x:ℝ) ∂p.streamLaw)=p.variance/2 :=
    ((p.renewal_hasLaw 0).integral_comp
      (measurable_of_countable (fun k : ℕ => (k:ℝ))).aestronglyMeasurable).trans p.ladder_integral
  exact iid_nat_lower_tail p.streamLaw renewalIncrement measurable_renewalIncrement p.renewal_iid
    (fun i => (p.renewal_hasLaw i).identDistrib (p.renewal_hasLaw 0)) hint
    (by rw [hm]; exact half_pos p.variance_pos)


lemma ladderTime_level_real {x : ℕ → ℕ} (hx : HasAllLadders x) (r : ℕ) :
    (integerSum x (ladderTime x r):ℝ)=renewalLevel r x := by
  rw [ladderTime_level_sum hx]
  simp only [Int.cast_sum,Int.cast_natCast,renewalLevel]


lemma record_count_remainder {x : ℕ → ℕ} (hx : HasAllLadders x)
    (ν ε A : ℝ) (h : ∀ r, |renewalLevel r x-ν*r| ≤ ε*renewalLevel r x+A) (n : ℕ) :
    |(integerSum x (ladderTime x (renewalCount (ladderTime x) n)):ℝ)-
      ν*(weakRecords (integerSum x) n).card| ≤
      ε*(integerSum x (ladderTime x (renewalCount (ladderTime x) n)):ℝ)+A := by
  rw [(ladderTime_enumeration hx).card_records,ladderTime_level_real hx]
  exact h _


lemma exists_first_path_minimum {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b : ℕ} (hab : a ≤ b) :
    ∃ i, a ≤ i ∧ i ≤ b ∧ (∀ r, a ≤ r → r ≤ b → S i ≤ S r) ∧
      ∀ r, a ≤ r → r < i → S i < S r := by
  classical
  have hex : ∃ i, a ≤ i ∧ i ≤ b ∧ ∀ r, a ≤ r → r ≤ b → S i ≤ S r := by
    obtain ⟨i,hi,hmin⟩ := (Finset.Icc a b).exists_min_image S ⟨a,Finset.mem_Icc.mpr ⟨le_rfl,hab⟩⟩
    exact ⟨i,(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,
      fun r ha hb => hmin r (Finset.mem_Icc.mpr ⟨ha,hb⟩)⟩
  refine ⟨Nat.find hex,(Nat.find_spec hex).1,(Nat.find_spec hex).2.1,
    (Nat.find_spec hex).2.2,?_⟩
  intro r hra hri
  by_contra hn
  have hr : r ≤ b := le_trans (le_of_lt hri) (Nat.find_spec hex).2.1
  exact Nat.find_min hex hri ⟨hra,hr,fun k hka hkb =>
    (le_of_not_gt hn).trans ((Nat.find_spec hex).2.2 k hka hkb)⟩


lemma reverseRecords_at_first_minimum {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b i : ℕ} (hai : a ≤ i) (hib : i ≤ b)
    (hmin : ∀ r, a ≤ r → r ≤ b → S i ≤ S r)
    (hfirst : ∀ r, a ≤ r → r < i → S i < S r) :
    reverseRecords S 0 i = (reverseRecords S 0 b).filter (fun j => j < a) := by
  ext j
  simp only [mem_reverseRecords, Finset.mem_filter]
  constructor
  · rintro ⟨h0,hji,hrec⟩
    have hja : j < a := by
      by_contra hn
      exact (not_le_of_gt (hfirst j (by omega) hji)) (hrec i hji.le le_rfl)
    refine ⟨⟨h0,lt_of_lt_of_le hji hib,?_⟩,hja⟩
    intro r hjr hrb
    by_cases hri : r ≤ i
    · exact hrec r hjr hri
    · exact (hrec i hji.le le_rfl).trans (hmin r (by omega) hrb)
  · rintro ⟨⟨h0,hjb,hrec⟩,hja⟩
    exact ⟨h0,lt_of_lt_of_le hja hai,fun r hjr hri => hrec r hjr (hri.trans hib)⟩


lemma reverseRecords_split {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b : ℕ} (_hab : a ≤ b) :
    reverseRecords S 0 b =
      ((reverseRecords S 0 b).filter (fun j => j < a)) ∪ reverseRecords S a b := by
  ext j
  simp only [Finset.mem_union,Finset.mem_filter,mem_reverseRecords]
  constructor
  · intro hj
    by_cases hja : j < a
    · exact Or.inl ⟨hj,hja⟩
    · exact Or.inr ⟨by omega,hj.2⟩
  · rintro (⟨hj,_⟩ | hj)
    · exact hj
    · exact ⟨Nat.zero_le j,hj.2⟩


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightCoding
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSingletonClassCode _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma reverse_record_iff (S : ℕ → ℤ) {a b j : ℕ} (haj : a ≤ j) (hjb : j < b) :
    j ∈ reverseRecords S a b ↔ b-j ∈ weakRecords (reversedPath S b) (b-a) := by
  rw [mem_reverseRecords,mem_weakRecords]
  constructor
  · rintro ⟨_,_,hrec⟩
    refine ⟨by omega,by omega,?_⟩
    intro k hk
    have hr := hrec (b-k) (by omega) (by omega)
    dsimp [reversedPath]
    have he : b-(b-j)=j := by omega
    rw [he]
    omega
  · rintro ⟨_,_,hrec⟩
    refine ⟨haj,hjb,?_⟩
    intro r hjr hrb
    have hr := hrec (b-r) (by omega)
    dsimp [reversedPath] at hr
    have he : b-(b-r)=r := by omega
    have he' : b-(b-j)=j := by omega
    rw [he,he'] at hr
    omega


lemma reverse_record_filter_card (S : ℕ → ℤ) (a b : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    ((reverseRecords S a b).filter P).card=
      ((weakRecords (reversedPath S b) (b-a)).filter fun k => P (b-k)).card := by
  classical
  apply Finset.card_bij (fun j _ => b-j)
  · intro j hj
    obtain ⟨hrec,hP⟩ := Finset.mem_filter.mp hj
    obtain ⟨haj,hjb,_⟩ := (mem_reverseRecords S a b j).mp hrec
    refine Finset.mem_filter.mpr ⟨(reverse_record_iff S haj hjb).mp hrec,?_⟩
    convert hP using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · intro j hj k hk he
    have hjb := ((mem_reverseRecords S a b j).mp (Finset.mem_filter.mp hj).1).2.1
    have hkb := ((mem_reverseRecords S a b k).mp (Finset.mem_filter.mp hk).1).2.1
    omega
  · intro k hk
    obtain ⟨hrec,hP⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1,hkba,_⟩ := (mem_weakRecords _ _ _).mp hrec
    refine ⟨b-k,?_,by omega⟩
    refine Finset.mem_filter.mpr ⟨?_,hP⟩
    apply (reverse_record_iff S (by omega : a ≤ b-k) (by omega : b-k < b)).mpr
    convert hrec using 1
    all_goals try with_reducible_and_instances rfl
    omega


lemma recordHeight_dual (S : ℕ → ℤ) (a b : ℕ) :
    recordHeight S a b=(weakRecords (reversedPath S b) (b-a)).card := by
  simpa [recordHeight] using reverse_record_filter_card S a b (fun _ => True)


lemma reverseRecords_surviving_at_minimum {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (hmin : ∀ r, a ≤ r → r ≤ b → S c ≤ S r)
    (hfirst : ∀ r, a ≤ r → r < c → S c < S r) :
    reverseRecords S 0 c=(reverseRecords S 0 a).filter fun j => S j ≤ S c := by
  classical
  ext j
  simp only [Finset.mem_filter,mem_reverseRecords]
  constructor
  · rintro ⟨hj0,hjc,hrec⟩
    have hja : j<a := by
      by_contra hn
      exact not_le_of_gt (hfirst j (by omega) hjc) (hrec c hjc.le le_rfl)
    exact ⟨⟨hj0,hja,fun r hjr hra => hrec r hjr (hra.trans hac)⟩,hrec c hjc.le le_rfl⟩
  · rintro ⟨⟨hj0,hja,hrec⟩,hjc⟩
    refine ⟨hj0,lt_of_lt_of_le hja hac,?_⟩
    intro r hjr hrc
    by_cases hra : r ≤ a
    · exact hrec r hjr hra
    · exact hjc.trans (hmin r (by omega) (hrc.trans hcb))


lemma recordHeight_fall_dual (S : ℕ → ℤ) {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (hmin : ∀ r, a ≤ r → r ≤ b → S c ≤ S r)
    (hfirst : ∀ r, a ≤ r → r < c → S c < S r) :
    recordHeight S 0 a-recordHeight S 0 c=
      ((weakRecords (reversedPath S a) a).filter fun k => reversedPath S a k<S a-S c).card := by
  classical
  have he := reverseRecords_surviving_at_minimum S hac hcb hmin hfirst
  have hd := Finset.card_filter_add_card_filter_not (s := reverseRecords S 0 a)
    (p := fun j => S j ≤ S c)
  have hc : ((reverseRecords S 0 a).filter fun j => S c<S j).card=
      recordHeight S 0 a-recordHeight S 0 c := by
    unfold recordHeight
    rw [he]
    simp only [not_le] at hd
    omega
  rw [← hc,reverse_record_filter_card]
  simp only [Nat.sub_zero]
  congr 2
  funext k
  apply propext
  dsimp [reversedPath]
  omega


lemma recordHeight_at_first_minimum_split {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (hmin : ∀ r, a ≤ r → r ≤ b → S c ≤ S r)
    (hfirst : ∀ r, a ≤ r → r < c → S c < S r) :
    recordHeight S 0 c ≤ recordHeight S 0 a ∧
      recordHeight S 0 b=recordHeight S 0 c+recordHeight S a b := by
  classical
  have he := reverseRecords_at_first_minimum S hac hcb hmin hfirst
  constructor
  · unfold recordHeight
    rw [reverseRecords_surviving_at_minimum S hac hcb hmin hfirst]
    exact Finset.card_filter_le _ _
  · unfold recordHeight
    rw [he]
    nth_rw 1 [reverseRecords_split S (hac.trans hcb)]
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have hja := (Finset.mem_filter.mp hj).2
    have haj := ((mem_reverseRecords ..).mp hj').1
    omega


lemma weakRecords_congr_prefix {S T : ℕ → ℤ} {n : ℕ}
    (he : ∀ k, k ≤ n → S k=T k) : weakRecords S n=weakRecords T n := by
  ext k
  simp only [mem_weakRecords]
  constructor <;> rintro ⟨hk,hkn,hr⟩ <;> refine ⟨hk,hkn,?_⟩
  · intro j hj
    rw [← he j (by omega),← he k hkn]
    exact hr j hj
  · intro j hj
    rw [he j (by omega),he k hkn]
    exact hr j hj


lemma height_oscillation_of_reverse_extensions_real (S : ℕ → ℤ) (a b m : ℕ) (hab : a ≤ b)
    (d : ℝ) (Ra Rb : ℕ → ℤ) (τa τb : ℕ → ℕ)
    (hea : ∀ k, k ≤ a → Ra k=reversedPath S a k)
    (heb : ∀ k, k ≤ b → Rb k=reversedPath S b k)
    (ha : LadderEnumeration Ra τa) (hb : LadderEnumeration Rb τb)
    (hla : d ≤ (Ra (τa m):ℝ)) (hlb : d ≤ (Rb (τb m):ℝ))
    (hosc : ∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b → (S u:ℝ)-(S v:ℝ)<d) :
    recordHeight S 0 b ≤ recordHeight S 0 a+m ∧
      recordHeight S 0 a ≤ recordHeight S 0 b+m := by
  classical
  obtain ⟨c,hac,hcb,hmin,hfirst⟩ := exists_first_path_minimum S hab
  obtain ⟨hca,hsplit⟩ := recordHeight_at_first_minimum_split S hac hcb hmin hfirst
  have hfall : recordHeight S 0 a-recordHeight S 0 c ≤ m := by
    rw [recordHeight_fall_dual S hac hcb hmin hfirst,
      ← weakRecords_congr_prefix hea]
    have he : ((weakRecords Ra a).filter fun k => reversedPath S a k<S a-S c)=
        ((weakRecords Ra a).filter fun k => Ra k<S a-S c) := by
      apply Finset.filter_congr
      intro k hk
      rw [hea k ((mem_weakRecords ..).mp hk).2.1]
    rw [he]
    apply ha.first_records_below a m (S a-S c)
    have hh := (hosc a c le_rfl hab hac hcb).le.trans hla
    exact_mod_cast hh
  have hrise : recordHeight S a b ≤ m := by
    rw [recordHeight_dual,← weakRecords_congr_prefix (fun k hk => heb k (by omega)),hb.card_records]
    by_contra hn
    have hl : τb m ≤ b-a :=
      (le_renewalCount_iff hb.strictMono hb.zero m (b-a)).mp (by omega)
    rw [heb (τb m) (by omega)] at hlb
    have hh := hosc b (b-τb m) hab le_rfl (by omega) (by omega)
    simp only [reversedPath,Int.cast_sub] at hlb
    linarith
  omega


lemma CriticalEvenOffspring.ae_reverse_ladders (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw, ∀ b, HasAllLadders (reverseFirst b x) := by
  rw [ae_all_iff]
  intro b
  exact (reverseFirst_preserving p b).quasiMeasurePreserving.ae p.ae_all_ladders


lemma height_modulus_failure_subset {x : ℕ → ℕ} {N m : ℕ} {d : ℝ}
    (hx : ∀ b, HasAllLadders (reverseFirst b x)) (hbad : x ∈ heightModulusFailure N m d) :
    ∃ b ≤ N, renewalLevel m (reverseFirst b x) ≤ d := by
  by_contra hn
  push Not at hn
  obtain ⟨a,b,hab,hb,hosc,hfail⟩ := hbad
  apply hfail
  apply height_oscillation_of_reverse_extensions_real (integerSum x) a b m hab d
    (integerSum (reverseFirst a x)) (integerSum (reverseFirst b x))
    (ladderTime (reverseFirst a x)) (ladderTime (reverseFirst b x))
    (fun k hk => integerSum_reverseFirst x a k hk)
    (fun k hk => integerSum_reverseFirst x b k hk)
    (ladderTime_enumeration (hx a)) (ladderTime_enumeration (hx b))
  · rw [ladderTime_level_real (hx a)]
    exact (hn a (hab.trans hb)).le
  · rw [ladderTime_level_real (hx b)]
    exact (hn b hb).le
  · exact hosc


theorem CriticalEvenOffspring.height_modulus_probability (p : CriticalEvenOffspring) :
    ∃ c ρ : ℝ, 0 < c ∧ 0<ρ ∧ ρ<1 ∧ ∀ N m : ℕ,
      p.streamLaw (heightModulusFailure N m (c*m)) ≤
        (N+1:ℕ)*ENNReal.ofReal (ρ^m) := by
  obtain ⟨c,ρ,hc,hr0,hr1,hbound⟩ := p.renewal_lower_tail
  refine ⟨c,ρ,hc,hr0,hr1,fun N m => ?_⟩
  let B := fun b => {x : ℕ → ℕ | renewalLevel m (reverseFirst b x) ≤ c*m}
  have hsub : heightModulusFailure N m (c*m) ≤ᵐ[p.streamLaw]
      ⋃ b ∈ Finset.range (N+1), B b := by
    filter_upwards [p.ae_reverse_ladders] with x hx
    intro hfail
    obtain ⟨b,hb,hbad⟩ := height_modulus_failure_subset hx hfail
    exact Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hbad⟩⟩
  apply (measure_mono_ae hsub).trans
  apply (measure_biUnion_finset_le (Finset.range (N+1)) B).trans
  calc
    ∑ b ∈ Finset.range (N+1),p.streamLaw (B b) ≤
        ∑ _b ∈ Finset.range (N+1),ENNReal.ofReal (ρ^m) := by
      apply Finset.sum_le_sum
      intro b _
      have he : B b=reverseFirst b ⁻¹' {x | renewalLevel m x ≤ c*m} := rfl
      rw [he,(reverseFirst_preserving p b).measure_preimage
        (measurableSet_le (measurable_renewalLevel m) measurable_const).nullMeasurableSet]
      exact hbound m
    _ = _ := by simp [nsmul_eq_mul]


lemma circularReversePath_prefix (S : ℕ → ℤ) (N v k : ℕ) (hk : k ≤ v) :
    circularReversePath S N v k=reversedPath S v k := by
  simp only [circularReversePath,ite_eq_left hk,reversedPath]


lemma circular_records_of_good {S : ℕ → ℤ} {N v : ℕ} (hv : v<N)
    (hzero : S 0=0) (hpos : ∀ k, k<N → 0 ≤ S k) :
    weakRecords (circularReversePath S N v) N=weakRecords (reversedPath S v) v := by
  ext k
  simp only [mem_weakRecords]
  constructor
  · rintro ⟨hk1,hkN,hrec⟩
    have hkv : k ≤ v := by
      by_contra hn
      have hh := hrec v (by omega)
      simp only [circularReversePath,ite_eq_left le_rfl,Nat.sub_self,hzero,sub_zero,
        ite_eq_right (show ¬k ≤ v from hn)] at hh
      have hh' := hpos (N+v-k) (by omega)
      omega
    refine ⟨hk1,hkv,?_⟩
    intro j hj
    simpa only [circularReversePath_prefix _ _ _ _ (hj.trans hkv),
      circularReversePath_prefix _ _ _ _ hkv] using hrec j hj
  · rintro ⟨hk1,hkv,hrec⟩
    refine ⟨hk1,hkv.trans hv.le,?_⟩
    intro j hj
    simpa only [circularReversePath_prefix _ _ _ _ (hj.trans hkv),
      circularReversePath_prefix _ _ _ _ hkv] using hrec j hj


lemma circular_record_height_of_good {S : ℕ → ℤ} {N v : ℕ} (hv : v<N)
    (hzero : S 0=0) (hpos : ∀ k, k<N → 0 ≤ S k) :
    (weakRecords (circularReversePath S N v) N).card=recordHeight S 0 v := by
  rw [circular_records_of_good hv hzero hpos,recordHeight_dual,Nat.sub_zero]


lemma circular_maximum_of_good {S : ℕ → ℤ} {N v : ℕ} (hv : v<N)
    (hzero : S 0=0) (hpos : ∀ k, k<N → 0 ≤ S k) :
    circularReversePath S N v v=S v ∧
      ∀ k, k ≤ N → circularReversePath S N v k ≤ S v := by
  constructor
  · simp [circularReversePath,hzero]
  · intro k hk
    by_cases hkv : k ≤ v
    · simp only [circularReversePath,ite_eq_left hkv]
      have := hpos (v-k) (by omega)
      omega
    · simp only [circularReversePath,ite_eq_right hkv]
      have := hpos (N+v-k) (by omega)
      omega


lemma height_eq_recordHeight {N : ℕ} (d : Fin N → Fin N) {j : ℕ} (hj : j ≤ N) :
    height d j=recordHeight (walk d) 0 j := by
  classical
  unfold height recordHeight
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    obtain ⟨_,hkj,hrec⟩ := Finset.mem_filter.mp hk
    apply (mem_reverseRecords ..).mpr
    refine ⟨Nat.zero_le _,hkj,?_⟩
    intro r hkr hrj
    exact hrec ⟨r,by omega⟩ hkr hrj
  · intro k _ l _ he
    exact Fin.ext he
  · intro k hk
    obtain ⟨_,hkj,hrec⟩ := (mem_reverseRecords ..).mp hk
    refine ⟨⟨k,by omega⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkj,fun r hr hjr => hrec r.val hr hjr⟩


lemma walk_rotate_left {N : ℕ} [NeZero N] (m : Fin N) (d : Fin N → Fin N)
    {j : ℕ} (hj : j ≤ N-m.val) :
    walk (rotateDegrees m d) j=walk d (m.val+j)-walk d m.val := by
  rw [← degreeList_prefixSum,degreeList_rotate,
    prefixSum_rotate_left _ (by simp) (by simpa using hj),
    degreeList_prefixSum,degreeList_prefixSum]


lemma walk_rotate_right {N : ℕ} [NeZero N] (m : Fin N) (d : Fin N → Fin N)
    {j : ℕ} (hj : N-m.val ≤ j) (hjN : j ≤ N) :
    walk (rotateDegrees m d) j=walk d N-walk d m.val+walk d (j-(N-m.val)) := by
  rw [← degreeList_prefixSum,degreeList_rotate,
    prefixSum_rotate_right _ (by simp) (by simpa using hj) (by simpa using hjN),
    degreeList_sum,degreeList_prefixSum,degreeList_length,degreeList_prefixSum]


lemma circular_reverse_rotate {N : ℕ} [NeZero N] (d : Bridge N) (v : Fin N)
    {k : ℕ} (hk : k ≤ N) :
    reversedPath (walk (rotateBridge v d).val) N k=
      circularReversePath (walk d.val) N v.val k := by
  change walk (rotateDegrees v d.val) N-walk (rotateDegrees v d.val) (N-k)=_
  rw [walk_rotate_terminal]
  by_cases hkv : k ≤ v.val
  · rw [walk_rotate_right v d.val (by omega) (by omega)]
    have he : N-k-(N-v.val)=v.val-k := by omega
    simp only [circularReversePath,ite_eq_left hkv,he]
    omega
  · rw [walk_rotate_left v d.val (by omega)]
    have he : v.val+(N-k)=N+v.val-k := by omega
    simp only [circularReversePath,ite_eq_right hkv,he]
    rw [d.property]
    omega


lemma rotated_code_reverse_records {N : ℕ} [NeZero N] (d : Code N) (v : Fin N) :
    (weakRecords (reversedPath (walk (rotateDegrees v d.val)) N) N).card=height d.val v.val := by
  have he : ∀ k, k ≤ N → reversedPath (walk (rotateDegrees v d.val)) N k=
      circularReversePath (walk d.val) N v.val k :=
    fun k hk => circular_reverse_rotate (⟨d.val,d.property.1⟩ : Bridge N) v hk
  rw [weakRecords_congr_prefix he,
    circular_record_height_of_good v.isLt (walk_zero d.val) d.property.2,
    height_eq_recordHeight d.val v.isLt.le]


lemma prefixMaximum_congr {S T : ℕ → ℤ} {N : ℕ} (h : ∀ k, k ≤ N → S k=T k) :
    prefixMaximum S N=prefixMaximum T N := by
  unfold prefixMaximum
  apply Finset.sup'_congr _ rfl
  intro k hk
  exact h k (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk)


lemma prefixMaximum_eq {S : ℕ → ℤ} {N v : ℕ} (hv : v ≤ N)
    (h : ∀ k, k ≤ N → S k ≤ S v) : prefixMaximum S N=S v := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun k hk => h k (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk))
  · exact Finset.le_sup' S (Finset.mem_range.mpr (by omega))


lemma rotated_code_reverse_maximum {N : ℕ} [NeZero N] (d : Code N) (v : Fin N) :
    prefixMaximum (reversedPath (walk (rotateDegrees v d.val)) N) N=walk d.val v.val := by
  have hp : ∀ k, k ≤ N → reversedPath (walk (rotateDegrees v d.val)) N k=
      circularReversePath (walk d.val) N v.val k :=
    fun k hk => circular_reverse_rotate (⟨d.val,d.property.1⟩ : Bridge N) v hk
  rw [prefixMaximum_congr hp]
  obtain ⟨he,hmax⟩ := circular_maximum_of_good v.isLt (walk_zero d.val) d.property.2
  rw [← he]
  exact prefixMaximum_eq v.isLt.le (by simpa only [he] using hmax)


lemma rotation_sum_invariant {N : ℕ} [NeZero N] (G : Bridge N → ℝ) (d : Bridge N) (m : Fin N) :
    (∑ v : Fin N,G (rotateBridge v (rotateBridge m d)))=
      ∑ v : Fin N,G (rotateBridge v d) := by
  simp_rw [rotateBridge_add]
  exact Equiv.sum_comp (Equiv.addRight m) (fun v => G (rotateBridge v d))


lemma canonical_rotation_sum {N : ℕ} [NeZero N] (G : Bridge N → ℝ) (d : Bridge N) :
    (∑ v : Fin N,G (rotateBridge v ⟨(canonicalCode d).val,(canonicalCode d).property.1⟩))=
      ∑ v : Fin N,G (rotateBridge v d) := by
  exact rotation_sum_invariant G d (goodRotation d)


theorem uniform_vertex_cyclic_identity (p : CriticalEvenOffspring) (n : ℕ)
    (G : Bridge (2*n+1) → ℝ) :
    (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
      ((∑ v : Fin (2*n+1),G (rotateBridge v ⟨d.val,d.property.1⟩))/(2*n+1)))=
    ∑ d : Bridge (2*n+1),(bridgeWeight p d/bridgePartition p (2*n+1))*G d := by
  let N := 2*n+1
  let : NeZero N := ⟨by dsimp [N]; omega⟩
  rw [← canonicalCode_expectation p n]
  simp_rw [canonical_rotation_sum,Finset.sum_div,Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrow (v : Fin N) :
      (∑ d : Bridge N,(bridgeWeight p d/bridgePartition p N)*(G (rotateBridge v d)/(N:ℝ)))=
        (∑ d : Bridge N,(bridgeWeight p d/bridgePartition p N)*G d)/(N:ℝ) := by
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    calc
      _ = ∑ d : Bridge N,(bridgeWeight p (rotateBridge v d)/bridgePartition p N)*G (rotateBridge v d) := by
        simp only [bridgeWeight_rotate]
      _ = _ := Equiv.sum_comp (rotateBridge v) (fun d : Bridge N => (bridgeWeight p d/bridgePartition p N)*G d)
  have hNR : (2*(n:ℝ)+1)=(N:ℝ) := by dsimp [N]; push_cast; rfl
  rw [hNR]
  change (∑ v : Fin N, ∑ d : Bridge N,
    (bridgeWeight p d/bridgePartition p N)*(G (rotateBridge v d)/(N:ℝ)))=_
  simp_rw [hrow]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel₀ _ (by dsimp [N]; positivity : (N:ℝ)≠0)


theorem uniform_vertex_height_error (p : CriticalEvenOffspring) (n : ℕ) (ν a : ℝ) :
    (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
      ((∑ v : Fin (2*n+1), if a < |(walk d.val v.val:ℝ)-ν*height d.val v.val| then (1:ℝ) else 0)/(2*n+1)))=
    ∑ d : Bridge (2*n+1),(bridgeWeight p d/bridgePartition p (2*n+1))*
      (if a < |(prefixMaximum (reversedPath (walk d.val) (2*n+1)) (2*n+1):ℝ)-
        ν*(weakRecords (reversedPath (walk d.val) (2*n+1)) (2*n+1)).card| then (1:ℝ) else 0) := by
  classical
  let G : Bridge (2*n+1) → ℝ := fun d =>
    if a < |(prefixMaximum (reversedPath (walk d.val) (2*n+1)) (2*n+1):ℝ)-
      ν*(weakRecords (reversedPath (walk d.val) (2*n+1)) (2*n+1)).card| then 1 else 0
  have he : ∀ d : Code (2*n+1), ∀ v : Fin (2*n+1),
      G (rotateBridge v ⟨d.val,d.property.1⟩)=
        if a < |(walk d.val v.val:ℝ)-ν*height d.val v.val| then 1 else 0 := by
    intro d v
    change (if a < |(prefixMaximum (reversedPath (walk (rotateDegrees v d.val)) (2*n+1)) (2*n+1):ℝ)-
      ν*(weakRecords (reversedPath (walk (rotateDegrees v d.val)) (2*n+1)) (2*n+1)).card| then 1 else 0)=_
    rw [rotated_code_reverse_records d v,rotated_code_reverse_maximum d v]
  simpa only [he] using uniform_vertex_cyclic_identity p n G


lemma integral_standard_gaussian_complex :
    (∫ t : ℝ, Complex.exp (-(t : ℂ)^2/2)) = (Real.sqrt (2 * Real.pi) : ℂ) := by
  have heq (t : ℝ) : Complex.exp (-(t : ℂ)^2/2) =
      (Real.exp (-(1/2 : ℝ)*t^2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  rw [integral_complex_ofReal, integral_gaussian]
  congr 2
  ring


lemma CriticalEvenOffspring.bridgeFourier_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => ∫ t : ℝ, p.bridgeFourier n t) atTop
      (𝓝 (Real.sqrt (2 * Real.pi) : ℂ)) := by
  obtain ⟨c, hc, hg⟩ := p.charFun_global_gaussian
  have hden : Tendsto (fun n : ℕ => p.sigma * Real.sqrt (n+1)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)).const_mul_atTop
        p.sigma_pos
  have hp (t : ℝ) : Tendsto (fun n => p.bridgeFourier n t) atTop
      (𝓝 (Complex.exp (-(t : ℂ)^2/2))) := by
    have hr : Tendsto (fun n : ℕ => t / (p.sigma * Real.sqrt (n+1))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hden
    have he := ((Complex.continuous_ofReal.tendsto 0).comp hr).mul_const Complex.I
    have hex := Complex.continuous_exp.tendsto 0 |>.comp (by simpa using he)
    simpa [bridgeFourier] using (p.cutoff_pointwise t).mul hex
  have hm (n : ℕ) : AEStronglyMeasurable (p.bridgeFourier n) volume := by
    exact ((p.cutoff_measurable n).mul (by fun_prop)).aestronglyMeasurable
  have hn (n : ℕ) : ∀ᵐ t ∂volume, ‖p.bridgeFourier n t‖ ≤ Real.exp (-c*t^2) := by
    apply ae_of_all
    intro t
    simpa only [bridgeFourier, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] using
      p.cutoff_gaussian_bound hg n t
  have hi := tendsto_integral_of_dominated_convergence (μ := volume)
    (fun t : ℝ => Real.exp (-c*t^2)) hm (integrable_exp_neg_mul_sq hc) hn
      (ae_of_all _ hp)
  simpa only [integral_standard_gaussian_complex] using hi


lemma CriticalEvenOffspring.bridgeFourier_integral (p : CriticalEvenOffspring) (n : ℕ) :
    (∫ t : ℝ, p.bridgeFourier n t) =
      (p.sigma * Real.sqrt (n+1)) •
        ∫ t : ℝ in -(Real.pi/2)..Real.pi/2,
          Complex.exp ((t : ℂ) * Complex.I) *
            (charFun (p.law.toMeasure.map p.standardStep) (p.sigma * t))^(n+1) := by
  let A := (p.sigma * Real.pi / 2) * Real.sqrt (n+1)
  let scale := p.sigma * Real.sqrt (n+1)
  let f : ℝ → ℂ := fun t =>
    (charFun (p.law.toMeasure.map p.standardStep) (t / Real.sqrt (n+1)))^(n+1) *
      Complex.exp ((t / scale : ℝ) * Complex.I)
  have hsqrt : 0 < Real.sqrt (n+1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hscale : 0 < scale := mul_pos p.sigma_pos hsqrt
  have hA : 0 ≤ A := mul_nonneg
    (div_nonneg (mul_nonneg p.sigma_pos.le Real.pi_pos.le) (by norm_num)) hsqrt.le
  have heq : p.bridgeFourier n = (Icc (-A) A).indicator f := by
    ext t
    simp only [bridgeFourier, fourierCutoff, Set.indicator_apply, mem_Icc, ← abs_le]
    split_ifs <;> simp [f, scale]
  rw [heq, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self hA)]
  have hlo : -(Real.pi/2) * scale = -A := by dsimp [scale, A]; ring
  have hhi : (Real.pi/2) * scale = A := by dsimp [scale, A]; ring
  have hsub := intervalIntegral.smul_integral_comp_mul_right
    (a := -(Real.pi/2)) (b := Real.pi/2) f scale
  rw [hlo, hhi] at hsub
  rw [← hsub]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [f]
  rw [mul_div_cancel_right₀ _ hscale.ne']
  have ht : t * scale / Real.sqrt (n+1) = p.sigma * t := by
    dsimp [scale]
    field_simp
  rw [ht, mul_comm]


lemma CriticalEvenOffspring.bridgeFourier_partition (p : CriticalEvenOffspring) (n : ℕ) :
    (∫ t : ℝ, p.bridgeFourier (2*n) t) =
      (p.sigma * Real.sqrt (2*n+1) * Real.pi * bridgePartition p (2*n+1) : ℝ) := by
  have hpar : Even (((2*n+1 : ℕ) : ℤ) + (-1)) := by
    refine ⟨n, ?_⟩
    push_cast
    ring
  have hi := spanTwo_inversion (p.iidLaw (2*n+1)) totalStep
    (totalStep_measurable _) (-1) (p.iid_totalStep_parity _ hpar)
  simp only [Int.cast_neg, Int.cast_one, neg_neg, one_mul, p.iid_charFun] at hi
  rw [p.bridgeFourier_integral, hi, ← p.bridgePartition_eq_iid]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  push_cast
  ring


lemma CriticalEvenOffspring.bridgePartition_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => Real.sqrt (2*n+1) * bridgePartition p (2*n+1)) atTop
      (𝓝 (Real.sqrt (2*Real.pi) / (p.sigma * Real.pi))) := by
  have hsub : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (p.bridgeFourier_limit.comp hsub)
  change Tendsto (fun n : ℕ => (∫ t : ℝ, p.bridgeFourier (2*n) t).re)
    atTop (𝓝 (Real.sqrt (2*Real.pi))) at h
  simp only [p.bridgeFourier_partition, Complex.ofReal_re] at h
  have hdiv := h.div_const (p.sigma * Real.pi)
  convert hdiv using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  have hs := p.sigma_pos.ne'
  have hpi := Real.pi_pos.ne'
  field_simp


theorem CriticalEvenOffspring.codePartition_asymptotic (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => (2*n+1 : ℝ) * Real.sqrt (2*n+1) *
      codePartition p (2*n+1)) atTop (𝓝 (2 / (p.sigma * Real.sqrt (2*Real.pi)))) := by
  have hc : Real.sqrt (2*Real.pi) / (p.sigma * Real.pi) =
      2 / (p.sigma * Real.sqrt (2*Real.pi)) := by
    have hsq := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
    have hsp : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
    field_simp [p.sigma_pos.ne', Real.pi_pos.ne', hsp.ne']
    nlinarith
  rw [← hc]
  convert p.bridgePartition_limit using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [codePartition_cyclic p (by omega)]
  push_cast
  ring


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ConditionedWalk
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.instIsProbabilityMeasureCodeHAddNatHMulOfNatCodeLaw _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding


lemma CriticalEvenOffspring.iid_cond_real (p : CriticalEvenOffspring) (N : ℕ)
    (E : Set (Fin N → ℕ)) :
    (cond (p.iidLaw N) {d | totalStep d = -1}).real E =
      (p.iidLaw N).real {d | d ∈ E ∧ totalStep d = -1} /
        (p.iidLaw N).real {d | totalStep d = -1} := by
  have hs : {d : Fin N → ℕ | totalStep d = -1} ∩ E =
      {d | d ∈ E ∧ totalStep d = -1} := by ext d; exact and_comm
  change ((cond (p.iidLaw N) {d | totalStep d = -1}) E).toReal = _
  rw [cond_apply (by measurability) (p.iidLaw N) E, hs,
    ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
  rfl


end FKCRT.TreeCoding

namespace FKCRT.TreeCoding


lemma iid_prefix_endpoint_bound (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (j : ℤ) (E : Set (Fin m → ℕ)) {C : ℝ} (hC : 0 ≤ C)
    (hsite : ∀ k : ℤ, (Measure.pi (fun _ : Fin r => μ)).real {d | totalStep d = k} ≤ C) :
    (Measure.pi (fun _ : Fin (m+r) => μ)).real
      {d | (iidSplit m r d).1 ∈ E ∧ totalStep d = j} ≤
    C * (Measure.pi (fun _ : Fin m => μ)).real E := by
  let μ₁ := Measure.pi (fun _ : Fin m => μ)
  let μ₂ := Measure.pi (fun _ : Fin r => μ)
  have hset : {d : Fin (m+r) → ℕ | (iidSplit m r d).1 ∈ E ∧ totalStep d = j} =
      iidSplit m r ⁻¹' {x | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1} := by
    ext d
    change (_ ∈ E ∧ totalStep d = j) ↔ (_ ∈ E ∧
      totalStep (iidSplit m r d).2 = j-totalStep (iidSplit m r d).1)
    rw [totalStep_split]
    constructor <;> rintro ⟨hE, h⟩ <;> exact ⟨hE, by omega⟩
  have hb : (μ₁.prod μ₂) {x | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1} ≤
      ENNReal.ofReal C * μ₁ E := by
    rw [Measure.prod_apply (by measurability)]
    have hsect (d : Fin m → ℕ) : μ₂ (Prod.mk d ⁻¹'
        {x | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1}) ≤
        E.indicator (fun _ => ENNReal.ofReal C) d := by
      by_cases hd : d ∈ E
      · rw [Set.indicator_of_mem hd]
        have hs : Prod.mk d ⁻¹' {x : (Fin m → ℕ) × (Fin r → ℕ) | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1} =
            {u | totalStep u = j-totalStep d} := by ext u; simp [hd]
        rw [hs, ← ENNReal.ofReal_toReal (measure_ne_top μ₂ _)]
        exact ENNReal.ofReal_le_ofReal (hsite _)
      · have hs : Prod.mk d ⁻¹' {x : (Fin m → ℕ) × (Fin r → ℕ) | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1} = ∅ := by
          ext u; simp [hd]
        simp [hs, hd]
    apply (lintegral_mono hsect).trans_eq
    rw [lintegral_indicator (by measurability), lintegral_const, Measure.restrict_apply_univ]
  rw [measureReal_def, hset, (iidSplit_preserving μ m r).measure_preimage (by measurability)]
  apply (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ₁ E)) hb).trans_eq
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
  rfl


theorem CriticalEvenOffspring.bridge_prefix_domination_fraction (p : CriticalEvenOffspring)
    (J : ℕ) (hJ : 0<J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, p.PrefixDominatedFraction (2*n+1) J K := by
  obtain ⟨C, hCpos, hC⟩ := p.iid_site_uniform_bound
  let B := Real.sqrt (2*Real.pi) / (p.sigma * Real.pi)
  have hB : 0 < B := div_pos (Real.sqrt_pos.mpr (by positivity))
    (mul_pos p.sigma_pos Real.pi_pos)
  have hden : Tendsto (fun n : ℕ => Real.sqrt ((2*n+1 : ℕ) : ℝ) *
      (p.iidLaw (2*n+1)).real {d | totalStep d = -1}) atTop (𝓝 B) := by
    convert p.bridgePartition_limit using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    rw [p.bridgePartition_eq_iid]
    push_cast
    rfl
  refine ⟨2*J*C/B, by positivity, ?_⟩
  filter_upwards [(tendsto_order.1 hden).1 (B/2) (by linarith)] with n hn
  intro m r hsum hhalf E
  have hr : 0 < r := by
    by_contra hn
    have hrz : r=0 := by omega
    simp only [hrz,mul_zero] at hhalf
    omega
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hr)
  have hsN : 0 < Real.sqrt ((m+r : ℕ) : ℝ) := Real.sqrt_pos.mpr (by norm_cast; omega)
  have hratio : Real.sqrt ((m+r : ℕ) : ℝ) ≤ (J:ℝ) * Real.sqrt (r : ℝ) := by
    have hh : (m+r : ℝ) ≤ J*r := by exact_mod_cast (show m+r ≤ J*r by omega)
    have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast hJ
    have hjr : (J:ℝ)*r ≤ J^2*r := by
      have hr0 : (0:ℝ) ≤ r := by positivity
      nlinarith
    have hpos : 0 ≤ (J:ℝ)*Real.sqrt (r:ℝ) := by positivity
    have h₁ := Real.sq_sqrt (show (0:ℝ) ≤ ((m+r : ℕ) : ℝ) by positivity)
    have h₂ := Real.sq_sqrt (show (0:ℝ) ≤ r by positivity)
    have h₂x := congrArg (fun t : ℝ => (J:ℝ)^2*t) h₂
    push_cast at h₁ ⊢
    nlinarith [Real.sqrt_nonneg (m+r)]
  have hsite (j : ℤ) : (p.iidLaw r).real {d | totalStep d = j} ≤ C / Real.sqrt (r : ℝ) := by
    obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    have hc := hC r' j
    rw [le_div_iff₀ hsr]
    simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hc
  have hpre := iid_prefix_endpoint_bound p.law.toMeasure m r (-1) E
    (show 0 ≤ C / Real.sqrt (r:ℝ) by positivity) hsite
  have hnum : Real.sqrt ((m+r : ℕ) : ℝ) *
      (p.iidLaw (m+r)).real {d | (iidSplit m r d).1 ∈ E ∧ totalStep d = -1} ≤
      J*C*(p.iidLaw m).real E := by
    have hA : Real.sqrt ((m+r : ℕ) : ℝ) * (C / Real.sqrt (r:ℝ)) ≤ J*C := by
      rw [← mul_div_assoc, div_le_iff₀ hsr]
      nlinarith
    calc
      _ ≤ Real.sqrt ((m+r : ℕ) : ℝ) * (C / Real.sqrt (r:ℝ) * (p.iidLaw m).real E) :=
        mul_le_mul_of_nonneg_left hpre hsN.le
      _ = (Real.sqrt ((m+r : ℕ) : ℝ) * (C / Real.sqrt (r:ℝ))) * (p.iidLaw m).real E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA measureReal_nonneg
  have hd : B/2 < Real.sqrt ((m+r : ℕ) : ℝ) *
      (p.iidLaw (m+r)).real {d | totalStep d = -1} := by
    change B/2 < Real.sqrt ((m+r : ℕ) : ℝ) * p.iidSiteProbability (m+r) (-1)
    change B/2 < Real.sqrt ((2*n+1 : ℕ) : ℝ) * p.iidSiteProbability (2*n+1) (-1) at hn
    simpa only [hsum] using hn
  rw [p.iid_cond_real]
  simp only [Set.mem_ofPred_eq]
  calc
    _ = (Real.sqrt ((m+r : ℕ) : ℝ) *
        (p.iidLaw (m+r)).real {d | (iidSplit m r d).1 ∈ E ∧ totalStep d = -1}) /
      (Real.sqrt ((m+r : ℕ) : ℝ) * (p.iidLaw (m+r)).real {d | totalStep d = -1}) := by
      rw [mul_div_mul_left _ _ hsN.ne']
    _ ≤ (J*C*(p.iidLaw m).real E)/(B/2) :=
      div_le_div₀ (by positivity) hnum (by positivity) hd.le
    _ = (2*J*C/B)*(p.iidLaw m).real E := by ring


end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightBounds
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma LadderEnumeration.prefixMaximum {S : ℕ → ℤ} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    prefixMaximum S n = S (τ (renewalCount τ n)) :=
  prefixMaximum_eq (renewalCount_spec h.zero n) (fun _ hk => h.maximum hk)

lemma prefix_record_remainder {x : ℕ → ℕ} (hx : HasAllLadders x)
    (ν ε A : ℝ) (h : ∀ r, |renewalLevel r x-ν*r| ≤ ε*renewalLevel r x+A) (n : ℕ) :
    |(prefixMaximum (integerSum x) n:ℝ)-ν*(weakRecords (integerSum x) n).card| ≤
      ε*(prefixMaximum (integerSum x) n:ℝ)+A := by
  rw [(ladderTime_enumeration hx).prefixMaximum]
  exact record_count_remainder hx ν ε A h n

lemma le_prefixMaximum (S : ℕ → ℤ) {i n : ℕ} (hi : i≤n) :
    S i ≤ prefixMaximum S n :=
  Finset.le_sup' S (Finset.mem_range.mpr (by omega))

lemma prefixMaximum_le {S : ℕ → ℤ} {n : ℕ} {a : ℤ}
    (h : ∀ k, k≤n → S k≤a) : prefixMaximum S n≤a :=
  Finset.sup'_le _ _ (fun k hk => h k (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk))

lemma prefixMaximum_mono (S : ℕ → ℤ) {m n : ℕ} (h : m≤n) :
    prefixMaximum S m≤prefixMaximum S n :=
  prefixMaximum_le fun _ hk => le_prefixMaximum S (hk.trans h)

lemma prefixMaximum_attained (S : ℕ → ℤ) (n : ℕ) :
    ∃ k≤n, prefixMaximum S n = S k := by
  obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (n+1)) Finset.nonempty_range_add_one S
  exact ⟨k,by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk,he⟩

lemma CriticalEvenOffspring.integerSum_scaled (p : CriticalEvenOffspring) (x : ℕ → ℕ) (n : ℕ) :
    (integerSum x n:ℝ)=p.sigma*(∑ j∈Finset.range n,p.streamStep j x) := by
  simp only [integerSum,Int.cast_sum,Int.cast_sub,Int.cast_natCast,Int.cast_one,
    streamStep,standardStep,← Finset.sum_div]
  field_simp [p.sigma_pos.ne']

lemma CriticalEvenOffspring.prefix_maximum_bound (p : CriticalEvenOffspring)
    {N : ℕ} (hN : 0<N) {R : ℝ} (hR : 0<R) :
    p.streamLaw.real {x | p.sigma*R*Real.sqrt N ≤ (prefixMaximum (integerSum x) N:ℝ)} ≤ 1/R^2 := by
  have hb := independent_sum_scaled_maximal_bound p.streamStep
    (fun _ => by unfold streamStep; fun_prop) p.streamStep_memLp
    p.streamStep_indep p.streamStep_integral (fun k => (p.streamStep_integral_sq k).le) hN hR
  apply (measureReal_mono ?_).trans hb
  intro x hx
  obtain ⟨k,hk,he⟩ := prefixMaximum_attained (integerSum x) N
  refine ⟨k,hk,?_⟩
  change p.sigma*R*Real.sqrt N ≤ (prefixMaximum (integerSum x) N:ℝ) at hx
  rw [he,p.integerSum_scaled] at hx
  have hh : R*Real.sqrt N ≤ ∑ j∈Finset.range k,p.streamStep j x := by
    apply (mul_le_mul_iff_right₀ p.sigma_pos).mp
    simpa only [mul_assoc] using hx
  exact hh.trans (le_abs_self _)

lemma CriticalEvenOffspring.prefix_record_error_bound (p : CriticalEvenOffspring)
    {N : ℕ} (hN : 0<N) {R ε : ℝ} (hR : 0<R) (hε : 0≤ε) (A : ℕ) :
    p.streamLaw.real {x | ∃ k≤N,
      ε*(p.sigma*R*Real.sqrt N)+A <
        |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|} ≤
      (p.streamLaw {x | ∃ r, ε*renewalLevel r x+A < |renewalLevel r x-(p.variance/2)*r|}).toReal + 1/R^2 := by
  let E : Set (ℕ → ℕ) := {x | ∃ r, ε*renewalLevel r x+A < |renewalLevel r x-(p.variance/2)*r|}
  let F : Set (ℕ → ℕ) := {x | p.sigma*R*Real.sqrt N ≤ (prefixMaximum (integerSum x) N:ℝ)}
  have hs : ∀ᵐ x ∂p.streamLaw, (∃ k≤N, ε*(p.sigma*R*Real.sqrt N)+A <
      |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|) →
      x∈E∪F := by
    filter_upwards [p.ae_all_ladders] with x hx
    rintro ⟨k,hk,hbad⟩
    by_cases he : x∈E
    · exact Or.inl he
    apply Or.inr
    by_contra hf
    have hrem : ∀ r, |renewalLevel r x-(p.variance/2)*r| ≤ ε*renewalLevel r x+A := by
      simpa only [E,Set.mem_ofPred_eq,not_exists,not_lt] using he
    have hmax : (prefixMaximum (integerSum x) k:ℝ) ≤ p.sigma*R*Real.sqrt N := by
      exact (Int.cast_le.mpr (prefixMaximum_mono _ hk)).trans (le_of_lt (not_le.mp hf))
    exact (not_lt_of_ge ((prefix_record_remainder hx _ _ _ hrem k).trans
      (add_le_add (mul_le_mul_of_nonneg_left hmax hε) le_rfl))) hbad
  calc
    _ ≤ p.streamLaw.real (E∪F) := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
    _ ≤ p.streamLaw.real E+p.streamLaw.real F := measureReal_union_le _ _
    _ ≤ _ := add_le_add le_rfl (p.prefix_maximum_bound hN hR)

/-- Finite variance suffices for the uniform renewal-record approximation on
an unconditioned iid prefix; no upper exponential moment is used. -/
theorem CriticalEvenOffspring.iid_prefix_record_error (p : CriticalEvenOffspring)
    {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun N : ℕ => p.streamLaw.real {x | ∃ k≤N,
      δ*Real.sqrt N <
        |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|})
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  · intro η hη
    let R := Real.sqrt (4/η)
    have hR : 0<R := Real.sqrt_pos.mpr (by positivity)
    have hR2 : R^2=4/η := Real.sq_sqrt (by positivity)
    have htail : 1/R^2=η/4 := by rw [hR2]; field_simp
    have hσ := p.sigma_pos
    let ε := δ/(2*p.sigma*R)
    have hε : 0<ε := div_pos hδ (by positivity)
    have heq : ε*(p.sigma*R)=δ/2 := by dsimp [ε]; field_simp [hR.ne',hσ.ne']
    have hlim : Tendsto (fun A : ℕ => (p.streamLaw {x | ∃ r,
        ε*renewalLevel r x+A < |renewalLevel r x-(p.variance/2)*r|}).toReal)
        atTop (𝓝 0) := by
      simpa only [ENNReal.toReal_zero,Function.comp_def] using
        (ENNReal.tendsto_toReal (by simp : (0:ℝ≥0∞)≠∞)).comp (p.renewal_remainder_probability hε)
    obtain ⟨A,hA⟩ := (hlim.eventually (eventually_lt_nhds (show (0:ℝ)<η/2 from half_pos hη))).exists
    have hscale : Tendsto (fun N : ℕ => δ/2*Real.sqrt N) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (half_pos hδ)
    filter_upwards [hscale.eventually_ge_atTop (A:ℝ),eventually_gt_atTop 0] with N hN hNpos
    have hbound := p.prefix_record_error_bound hNpos hR hε.le A
    have hs : ε*(p.sigma*R*Real.sqrt N)+A ≤ δ*Real.sqrt N := by
      rw [← mul_assoc,heq]
      linarith
    have hmono : p.streamLaw.real {x | ∃ k≤N,
        δ*Real.sqrt N <
          |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|} ≤
        p.streamLaw.real {x | ∃ k≤N, ε*(p.sigma*R*Real.sqrt N)+A <
          |(prefixMaximum (integerSum x) k:ℝ)-(p.variance/2)*(weakRecords (integerSum x) k).card|} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      rintro x ⟨k,hk,hx⟩
      exact ⟨k,hk,hs.trans_lt hx⟩
    apply (hmono.trans hbound).trans_lt
    rw [htail]
    linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma map_cond_preimage {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) {f : Ω → Ξ} (hf : Measurable f) {s : Set Ξ} (hs : MeasurableSet s) :
    (cond μ (f ⁻¹' s)).map f = cond (μ.map f) s := by
  rw [ProbabilityTheory.cond,ProbabilityTheory.cond,Measure.map_smul,
    ← Measure.restrict_map hf hs,Measure.map_apply hf hs]

lemma measurable_streamPrefix (N : ℕ) : Measurable (streamPrefix N) :=
  Measurable.of_eval (fun index => measurable_pi_apply index.val)

lemma totalStep_streamPrefix (N : ℕ) (x : ℕ → ℕ) :
    totalStep (streamPrefix N x)=integerSum x N := by
  exact Fin.sum_univ_eq_sum_range (fun k => ((x k:ℤ)-1)) N

lemma CriticalEvenOffspring.streamPrefix_hasLaw (p : CriticalEvenOffspring) (N : ℕ) :
    HasLaw (streamPrefix N) (p.iidLaw N) p.streamLaw := p.stream_restrict_law N

lemma CriticalEvenOffspring.streamBridge_restrict (p : CriticalEvenOffspring) (n : ℕ) :
    HasLaw (streamPrefix (2*n+1)) (p.iidBridgeLaw n) (p.streamBridgeLaw n) := by
  refine ⟨(measurable_streamPrefix _).aemeasurable,?_⟩
  have hh := map_cond_preimage p.streamLaw (measurable_streamPrefix (2*n+1))
    (show MeasurableSet {d : Fin (2*n+1) → ℕ | totalStep d=-1} from by measurability)
  simpa only [streamBridgeLaw,iidBridgeLaw,Set.preimage_ofPred_eq,totalStep_streamPrefix,
    (p.streamPrefix_hasLaw (2*n+1)).map_eq] using hh

instance instIsProbabilityMeasureForallNatStreamBridgeLaw (p : CriticalEvenOffspring) (n : ℕ) : IsProbabilityMeasure (p.streamBridgeLaw n) := by
  have : IsProbabilityMeasure ((p.streamBridgeLaw n).map (streamPrefix (2*n+1))) := by
    rw [(p.streamBridge_restrict n).map_eq]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map (streamPrefix (2*n+1))

lemma integerSum_arrayStream_prefix (N : ℕ) (x : ℕ → ℕ) {k : ℕ} (hk : k ≤ N) :
    integerSum (arrayStream (streamPrefix N x)) k = integerSum x k := by
  unfold integerSum
  apply Finset.sum_congr rfl
  intro i hi
  simp only [arrayStream,streamPrefix,dite_eq_left ((Finset.mem_range.mp hi).trans_le hk)]

lemma recordError_congr {ν : ℝ} {S T : ℕ → ℤ} {k : ℕ}
    (h : ∀ j, j ≤ k → S j=T j) : recordError ν S k=recordError ν T k := by
  rw [recordError,recordError,prefixMaximum_congr h,weakRecords_congr_prefix h]

lemma recordError_arrayStream_prefix (N : ℕ) (x : ℕ → ℕ) {k : ℕ} (hk : k ≤ N) (ν : ℝ) :
    recordError ν (integerSum (arrayStream (streamPrefix N x))) k = recordError ν (integerSum x) k :=
  recordError_congr fun _ hj => integerSum_arrayStream_prefix N x (hj.trans hk)

lemma CriticalEvenOffspring.prefix_domination_stream (p : CriticalEvenOffspring)
    {n J : ℕ} {K : ℝ} (hdom : p.PrefixDominatedFraction (2*n+1) J K)
    {m r : ℕ} (hs : m+r=2*n+1) (hfrac : 2*n+1 ≤ J*r) (E : Set (Fin m → ℕ)) :
    (p.streamBridgeLaw n).real (streamPrefix m ⁻¹' E)  ≤ 
      K*p.streamLaw.real (streamPrefix m ⁻¹' E) := by
  have hmap := (p.streamPrefix_hasLaw m).measurePreserving (measurable_streamPrefix m)
  rw [hmap.measureReal_preimage (by measurability)]
  have hb := hdom m r hs hfrac E
  have heq : (cond (p.iidLaw (m+r)) {d | totalStep d=-1})=
      (p.streamBridgeLaw n).map (streamPrefix (m+r)) := by
    rw [hs]
    exact (p.streamBridge_restrict n).map_eq.symm
  rw [heq] at hb
  have hm : Measurable (streamPrefix (m+r)) := measurable_streamPrefix _
  rw [map_measureReal_apply hm (by measurability)] at hb
  exact hb

lemma CriticalEvenOffspring.prefix_record_domination (p : CriticalEvenOffspring)
    {n J : ℕ} {K : ℝ} (hdom : p.PrefixDominatedFraction (2*n+1) J K)
    {m r : ℕ} (hs : m+r=2*n+1) (hfrac : 2*n+1 ≤ J*r) (a : ℝ) :
    (p.streamBridgeLaw n).real {x | ∃ k ≤ m, a < recordError (p.variance/2) (integerSum x) k}  ≤ 
      K*p.streamLaw.real {x | ∃ k ≤ m, a < recordError (p.variance/2) (integerSum x) k} := by
  let E : Set (Fin m → ℕ) := {d | ∃ k ≤ m, a < recordError (p.variance/2) (integerSum (arrayStream d)) k}
  have he : streamPrefix m ⁻¹' E={x | ∃ k ≤ m, a < recordError (p.variance/2) (integerSum x) k} := by
    ext x
    change (∃ k ≤ m, a < recordError (p.variance/2) (integerSum (arrayStream (streamPrefix m x))) k) ↔ _
    constructor <;> rintro ⟨k,hk,he⟩ <;> refine ⟨k,hk,?_⟩
    · rwa [recordError_arrayStream_prefix m x hk] at he
    · rwa [recordError_arrayStream_prefix m x hk]
  simpa only [he] using p.prefix_domination_stream hdom hs hfrac E

/-- The uniform record approximation survives conditioning on every fixed
proper prefix. The remaining terminal segment is handled separately. -/
theorem CriticalEvenOffspring.bridge_prefix_record_error (p : CriticalEvenOffspring)
    {J : ℕ} (hJ : 0<J) (m r : ℕ → ℕ)
    (hs : ∀ n, m n+r n=2*n+1) (hfrac : ∀ᶠ n in atTop, 2*n+1 ≤ J*r n)
    {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun n => (p.streamBridgeLaw n).real {x | ∃ k ≤ m n,
      δ*Real.sqrt ((2*n+1:ℕ):ℝ) < recordError (p.variance/2) (integerSum x) k}) atTop (𝓝 0) := by
  obtain ⟨K,hK,hdom⟩ := p.bridge_prefix_domination_fraction J hJ
  have hN : Tendsto (fun n : ℕ => 2*n+1) atTop atTop := by
    exact tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id
  have hi := (p.iid_prefix_record_error hδ).comp hN
  have hlim := hi.const_mul K
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards [hdom,hfrac] with n hn hf
  have hb := p.prefix_record_domination hn (hs n) hf (δ*Real.sqrt ((2*n+1:ℕ):ℝ))
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hK.le
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro x ⟨k,hk,hx⟩
  exact ⟨k,by dsimp; have hh := hs n; omega,hx⟩

lemma CriticalEvenOffspring.streamBridge_reverse (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (reverseFirst (2*n+1)) (p.streamBridgeLaw n) (p.streamBridgeLaw n) := by
  apply measurePreserving_cond (reverseFirst_preserving p (2*n+1))
    (measurableSet_eq_fun (measurable_integerSum _) measurable_const)
  ext x
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,integerSum_reverseFirst x (2*n+1) (2*n+1) le_rfl,
    Nat.sub_self,integerSum_zero,sub_zero]

lemma CriticalEvenOffspring.integer_maximal_bound (p : CriticalEvenOffspring)
    (r : ℕ) {a : ℝ} (ha : 0<a) :
    p.streamLaw.real {x | ∃ k ≤ r, a ≤ |(integerSum x k:ℝ)|}  ≤  (r:ℝ)*p.sigma^2/a^2 := by
  have hb := independent_sum_maximal_bound p.streamStep
    (fun _ => by unfold streamStep; fun_prop) p.streamStep_memLp p.streamStep_indep
    p.streamStep_integral r (div_pos ha p.sigma_pos)
  simp only [p.streamStep_integral_sq,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hb
  have hs : {x | ∃ k ≤ r, a ≤ |(integerSum x k:ℝ)|} ⊆
      {x | ∃ k ≤ r, a/p.sigma ≤ |∑ j∈Finset.range k,p.streamStep j x|} := by
    rintro x ⟨k,hk,hx⟩
    refine ⟨k,hk,?_⟩
    rw [p.integerSum_scaled,abs_mul,abs_of_pos p.sigma_pos] at hx
    exact (div_le_iff₀ p.sigma_pos).mpr (by simpa [mul_comm] using hx)
  apply ((measureReal_mono hs).trans hb).trans_eq
  field_simp

lemma integerSum_prefix_event (r : ℕ) (a : ℝ) :
    streamPrefix r ⁻¹' {d | ∃ k ≤ r, a ≤ |(integerSum (arrayStream d) k:ℝ)|}=
      {x | ∃ k ≤ r, a ≤ |(integerSum x k:ℝ)|} := by
  ext x
  change (∃ k ≤ r, a ≤ |(integerSum (arrayStream (streamPrefix r x)) k:ℝ)|) ↔ _
  constructor <;> rintro ⟨k,hk,he⟩ <;> refine ⟨k,hk,?_⟩
  · rwa [integerSum_arrayStream_prefix r x hk] at he
  · rwa [integerSum_arrayStream_prefix r x hk]

lemma CriticalEvenOffspring.bridge_initial_maximal_bound (p : CriticalEvenOffspring)
    {n : ℕ} {K : ℝ} (hK : 0 ≤ K) (hdom : p.PrefixDominatedFraction (2*n+1) 2 K)
    {r : ℕ} (hr : 2*r ≤ 2*n+1) {a : ℝ} (ha : 0<a) :
    (p.streamBridgeLaw n).real {x | ∃ k ≤ r, a ≤ |(integerSum x k:ℝ)|}  ≤  K*((r:ℝ)*p.sigma^2/a^2) := by
  let E : Set (Fin r → ℕ) := {d | ∃ k ≤ r, a ≤ |(integerSum (arrayStream d) k:ℝ)|}
  have hh := p.prefix_domination_stream hdom (m := r) (r := 2*n+1-r) (by omega) (by omega) E
  rw [integerSum_prefix_event] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (p.integer_maximal_bound r ha) hK)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma weakRecords_mono (S : ℕ → ℤ) {m n : ℕ} (h : m ≤ n) :
    weakRecords S m ⊆ weakRecords S n := by
  intro k hk
  obtain ⟨hk0,hkm,hrec⟩ := (mem_weakRecords S m k).mp hk
  exact (mem_weakRecords S n k).mpr ⟨hk0,hkm.trans h,hrec⟩

/-- New absolute weak records are a subset of records in the translated suffix. -/
lemma weakRecords_suffix_card_le (S : ℕ → ℤ) {m n : ℕ} (h : m ≤ n) :
    (weakRecords S n).card  ≤  (weakRecords S m).card+
      (weakRecords (fun k => S (m+k)-S m) (n-m)).card := by
  classical
  have hs : weakRecords S n ⊆ weakRecords S m ∪
      (weakRecords (fun k => S (m+k)-S m) (n-m)).image (fun k => m+k) := by
    intro k hk
    obtain ⟨hk0,hkn,hrec⟩ := (mem_weakRecords S n k).mp hk
    by_cases hkm : k ≤ m
    · exact Finset.mem_union_left _ ((mem_weakRecords S m k).mpr ⟨hk0,hkm,hrec⟩)
    apply Finset.mem_union_right
    refine Finset.mem_image.mpr ⟨k-m,?_,by omega⟩
    apply (mem_weakRecords ..).mpr
    refine ⟨by omega,by omega,?_⟩
    intro j hj
    have hh := hrec (m+j) (by omega)
    have he : m+(k-m)=k := by omega
    rw [he]
    omega
  exact (Finset.card_le_card hs).trans ((Finset.card_union_le _ _).trans
    (add_le_add le_rfl (Finset.card_image_le)))

lemma weakRecords_suffix_of_ladder_level (x : ℕ → ℕ) {m n h : ℕ} (hmn : m ≤ n)
    (hx : HasAllLadders (streamShift m x)) {a : ℝ}
    (hla : a  ≤  renewalLevel h (streamShift m x))
    (hosc : ∀ k, m ≤ k → k ≤ n → (integerSum x k:ℝ)-(integerSum x m:ℝ)<a) :
    (weakRecords (integerSum x) n).card  ≤  (weakRecords (integerSum x) m).card+h := by
  have hb := weakRecords_suffix_card_le (integerSum x) hmn
  have he : (fun k => integerSum x (m+k)-integerSum x m)=integerSum (streamShift m x) := by
    funext k
    exact (integerSum_shift x m k).symm
  rw [he,(ladderTime_enumeration hx).card_records] at hb
  have hcount : renewalCount (ladderTime (streamShift m x)) (n-m) ≤ h := by
    by_contra hn
    have htime : ladderTime (streamShift m x) h ≤ n-m :=
      (le_renewalCount_iff (ladderTime_enumeration hx).strictMono
        (ladderTime_enumeration hx).zero h (n-m)).mp (by omega)
    have hosc' := hosc (m+ladderTime (streamShift m x) h) (by omega) (by omega)
    rw [← ladderTime_level_real hx] at hla
    rw [integerSum_shift] at hla
    push_cast at hla
    linarith
  omega

lemma prefixMaximum_tail_le {S : ℕ → ℤ} {m n : ℕ} {a : ℝ}
    (ha : 0 ≤ a) (hosc : ∀ k, m ≤ k → k ≤ n → (S k:ℝ)-(S m:ℝ) ≤ a) :
    (prefixMaximum S n:ℝ)  ≤  (prefixMaximum S m:ℝ)+a := by
  obtain ⟨k,hk,he⟩ := prefixMaximum_attained S n
  rw [he]
  by_cases hkm : k ≤ m
  · exact (Int.cast_le.mpr (le_prefixMaximum S hkm)).trans (le_add_of_nonneg_right ha)
  · have hh := hosc k (by omega) hk
    have hsup : (S m:ℝ) ≤ prefixMaximum S m := Int.cast_le.mpr (le_prefixMaximum S le_rfl)
    linarith

/-- Uniform numerical estimate used to pass from a truncated bridge to its
full record count. It needs only attained maxima and a one-sided suffix bound. -/
lemma prefix_record_error_tail {x : ℕ → ℕ} {m n h : ℕ} (hmn : m ≤ n)
    (hx : HasAllLadders (streamShift m x)) {ν a : ℝ} (hν : 0 ≤ ν) (ha : 0 ≤ a)
    (hla : a  ≤  renewalLevel h (streamShift m x))
    (hosc : ∀ k, m ≤ k → k ≤ n → (integerSum x k:ℝ)-(integerSum x m:ℝ)<a) :
    |(prefixMaximum (integerSum x) n:ℝ)-ν*(weakRecords (integerSum x) n).card|  ≤ 
      |(prefixMaximum (integerSum x) m:ℝ)-ν*(weakRecords (integerSum x) m).card|+a+ν*h := by
  have hcount := weakRecords_suffix_of_ladder_level x hmn hx hla hosc
  have hcount' : ((weakRecords (integerSum x) n).card:ℝ)  ≤ 
      ((weakRecords (integerSum x) m).card:ℝ)+h := by exact_mod_cast hcount
  have hcountlo : ((weakRecords (integerSum x) m).card:ℝ)  ≤ 
      ((weakRecords (integerSum x) n).card:ℝ) := by
    exact_mod_cast Finset.card_le_card (weakRecords_mono (integerSum x) hmn)
  have hmax := prefixMaximum_tail_le ha (fun k hk hn => (hosc k hk hn).le)
  have hmaxlo : (prefixMaximum (integerSum x) m:ℝ)  ≤  prefixMaximum (integerSum x) n :=
    Int.cast_le.mpr (prefixMaximum_mono _ hmn)
  apply abs_le.mpr
  have hh := abs_le.mp (le_refl |(prefixMaximum (integerSum x) m:ℝ)-ν*(weakRecords (integerSum x) m).card|)
  constructor <;> nlinarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma cond_real_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {E : Set Ω} (hE : MeasurableSet E) (B : Set Ω) :
    (cond μ E).real B ≤ μ.real B / μ.real E := by
  rw [measureReal_def,cond_apply hE,ENNReal.toReal_mul,ENNReal.toReal_inv]
  change (μ.real E)⁻¹ * μ.real (E ∩ B) ≤ _
  rw [div_eq_mul_inv,mul_comm (μ.real B)]
  exact mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_right) (inv_nonneg.mpr measureReal_nonneg)

lemma CriticalEvenOffspring.stream_endpoint_probability (p : CriticalEvenOffspring) (N : ℕ) :
    p.streamLaw.real {x | integerSum x N = -1} =
      (p.iidLaw N).real {d | totalStep d = -1} := by
  have hh := (p.streamPrefix_hasLaw N).measurePreserving (measurable_streamPrefix N)
  simpa only [Set.preimage_ofPred_eq,totalStep_streamPrefix] using
    hh.measureReal_preimage (show MeasurableSet {d : Fin N → ℕ | totalStep d = -1} from by measurability).nullMeasurableSet

lemma CriticalEvenOffspring.stream_endpoint_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n => Real.sqrt ((2*n+1:ℕ):ℝ)*
      p.streamLaw.real {x | integerSum x (2*n+1) = -1}) atTop (𝓝 p.bridgeConstant) := by
  simpa only [p.stream_endpoint_probability] using p.iid_endpoint_limit

lemma CriticalEvenOffspring.streamBridge_shift_ladders (p : CriticalEvenOffspring) (n m : ℕ) :
    ∀ᵐ x ∂p.streamBridgeLaw n, HasAllLadders (streamShift m x) :=
  cond_absolutelyContinuous.ae_le ((p.streamShift_preserving m).quasiMeasurePreserving.ae p.ae_all_ladders)

lemma CriticalEvenOffspring.bridge_shift_ladder_bound (p : CriticalEvenOffspring)
    {c ρ : ℝ} (hρ : 0 ≤ ρ)
    (hb : ∀ h, p.streamLaw {x | renewalLevel h x ≤ c*h} ≤ ENNReal.ofReal (ρ^h))
    (n m h : ℕ) :
    (p.streamBridgeLaw n).real {x | renewalLevel h (streamShift m x) ≤ c*h} ≤
      ρ^h / p.streamLaw.real {x | integerSum x (2*n+1) = -1} := by
  have hr : MeasurableSet {x | renewalLevel h x ≤ c*h} :=
    measurableSet_le (measurable_renewalLevel h) measurable_const
  have ht := (p.streamShift_preserving m).measureReal_preimage hr.nullMeasurableSet
  have hreal : p.streamLaw.real {x | renewalLevel h x ≤ c*h} ≤ ρ^h := by
    exact (ENNReal.toReal_mono (by finiteness) (hb h)).trans_eq (ENNReal.toReal_ofReal (pow_nonneg hρ _))
  apply (cond_real_le p.streamLaw (measurableSet_eq_fun (measurable_integerSum _) measurable_const) _).trans
  exact div_le_div_of_nonneg_right (ht.le.trans hreal) measureReal_nonneg

lemma CriticalEvenOffspring.bridge_terminal_maximal_bound (p : CriticalEvenOffspring)
    {n : ℕ} {K : ℝ} (hK : 0 ≤ K) (hdom : p.PrefixDominatedFraction (2*n+1) 2 K)
    {r : ℕ} (hr : 2*r ≤ 2*n+1) {a : ℝ} (ha : 0<a) :
    (p.streamBridgeLaw n).real {x | ∃ k, 2*n+1-r ≤ k ∧ k ≤ 2*n+1 ∧
      a ≤ (integerSum x k:ℝ)-(integerSum x (2*n+1-r):ℝ)} ≤ K*((r:ℝ)*p.sigma^2/(a/2)^2) := by
  let E : Set (ℕ → ℕ) := {x | ∃ k ≤ r, a/2 ≤ |(integerSum x k:ℝ)|}
  have hsub : {x | ∃ k, 2*n+1-r ≤ k ∧ k ≤ 2*n+1 ∧
      a ≤ (integerSum x k:ℝ)-(integerSum x (2*n+1-r):ℝ)} ⊆
      reverseFirst (2*n+1) ⁻¹' E := by
    rintro x ⟨k,hkm,hkn,hx⟩
    by_contra hn
    have hn' : ∀ j ≤ r, |(integerSum (reverseFirst (2*n+1) x) j:ℝ)| < a/2 := by
      simpa only [Set.mem_preimage,E,Set.mem_ofPred_eq,not_exists,not_and,not_le] using hn
    have h1 := hn' r le_rfl
    have h2 := hn' (2*n+1-k) (by omega)
    rw [integerSum_reverseFirst x (2*n+1) r (by omega)] at h1
    rw [integerSum_reverseFirst x (2*n+1) (2*n+1-k) (by omega),Nat.sub_sub_self hkn] at h2
    push_cast at h1 h2
    have h1' := (abs_lt.mp h1).2
    have h2' := (abs_lt.mp h2).1
    linarith
  have hE : MeasurableSet E := by
    simp only [E,Set.ofPred_exists]
    exact MeasurableSet.iUnion fun k => (MeasurableSet.const (k ≤ r)).inter
      (measurableSet_le measurable_const ((measurable_of_countable (fun z : ℤ => (z:ℝ))).comp (measurable_integerSum k)).abs)
  have hh := (p.streamBridge_reverse n).measureReal_preimage hE.nullMeasurableSet
  exact (measureReal_mono hsub).trans (hh.le.trans (p.bridge_initial_maximal_bound hK hdom hr (half_pos ha)))

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma tendsto_natCeil_comp_atTop {s : ℕ → ℝ} (hs : Tendsto s atTop atTop) :
    Tendsto (fun n => ⌈s n⌉₊) atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hs.eventually (eventually_ge_atTop (b:ℝ))] with n hn
  exact_mod_cast hn.trans (Nat.le_ceil (s n))

lemma polynomial_geometric_ceil {s : ℕ → ℝ} (hs : Tendsto s atTop atTop)
    (hs0 : ∀ n, 0 ≤ s n) {ε ρ : ℝ} (hε : 0<ε) (hρ : 0 ≤ ρ) (hρ1 : ρ<1) (k : ℕ) :
    Tendsto (fun n => (s n)^k*ρ^⌈ε*s n⌉₊) atTop (𝓝 0) := by
  have hh : Tendsto (fun n => ⌈ε*s n⌉₊) atTop atTop :=
    tendsto_natCeil_comp_atTop (hs.const_mul_atTop hε)
  have ht := ((tendsto_pow_const_mul_const_pow_of_lt_one k hρ hρ1).comp hh).div_const (ε^k)
  simp only [zero_div] at ht
  apply squeeze_zero (fun n => mul_nonneg (pow_nonneg (hs0 n) _) (pow_nonneg hρ _)) ?_ ht
  intro n
  have hr : s n ≤ (⌈ε*s n⌉₊:ℝ)/ε := (le_div_iff₀ hε).mpr (by simpa [mul_comm] using Nat.le_ceil (ε*s n))
  calc
    (s n)^k*ρ^⌈ε*s n⌉₊ ≤ ((⌈ε*s n⌉₊:ℝ)/ε)^k*ρ^⌈ε*s n⌉₊ := by gcongr; exact hs0 n
    _ = _ := by dsimp; rw [div_pow]; ring

lemma odd_size_tendsto : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
  tendsto_atTop_mono (fun n => by dsimp; omega) tendsto_id

lemma odd_sqrt_tendsto : Tendsto (fun n : ℕ => Real.sqrt ((2*n+1:ℕ):ℝ)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp odd_size_tendsto)

lemma CriticalEvenOffspring.bridge_geometric_vanish (p : CriticalEvenOffspring)
    {ε ρ : ℝ} (hε : 0<ε) (hρ : 0 ≤ ρ) (hρ1 : ρ<1) :
    Tendsto (fun n => ρ^⌈ε*Real.sqrt ((2*n+1:ℕ):ℝ)⌉₊ /
      p.streamLaw.real {x | integerSum x (2*n+1) = -1}) atTop (𝓝 0) := by
  have ht := (polynomial_geometric_ceil odd_sqrt_tendsto (fun _ => Real.sqrt_nonneg _) hε hρ hρ1 1).div
    p.stream_endpoint_limit p.bridgeConstant_pos.ne'
  simp only [zero_div,pow_one] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact (mul_div_mul_left _ _ (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<((2*n+1:ℕ):ℝ))).ne').symm

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.bridge_record_tail_bound (p : CriticalEvenOffspring)
    {n m r h : ℕ} (hs : m+r=2*n+1) {t a : ℝ} (ha : 0 ≤ a) :
    (p.streamBridgeLaw n).real {x | t+a+(p.variance/2)*h < recordError (p.variance/2) (integerSum x) (2*n+1)} ≤
      (p.streamBridgeLaw n).real {x | t < recordError (p.variance/2) (integerSum x) m} +
      (p.streamBridgeLaw n).real {x | renewalLevel h (streamShift m x) ≤ a} +
      (p.streamBridgeLaw n).real {x | ∃ k, m ≤ k ∧ k ≤ 2*n+1 ∧
          a ≤ (integerSum x k:ℝ)-(integerSum x m:ℝ)} := by
  let A : Set (ℕ → ℕ) := {x | t < recordError (p.variance/2) (integerSum x) m}
  let B : Set (ℕ → ℕ) := {x | renewalLevel h (streamShift m x) ≤ a}
  let C : Set (ℕ → ℕ) := {x | ∃ k, m ≤ k ∧ k ≤ 2*n+1 ∧ a ≤ (integerSum x k:ℝ)-(integerSum x m:ℝ)}
  have hsub : ∀ᵐ x ∂p.streamBridgeLaw n, t+a+(p.variance/2)*h < recordError (p.variance/2) (integerSum x) (2*n+1) →
      x ∈ (A ∪ B) ∪ C := by
    filter_upwards [p.streamBridge_shift_ladders n m] with x hx
    intro hb
    by_contra hn
    have hn' : ¬x∈A ∧ ¬x∈B ∧ ¬x∈C := by simpa only [Set.mem_union,not_or,and_assoc] using hn
    have hA : recordError (p.variance/2) (integerSum x) m ≤ t := le_of_not_gt hn'.1
    have hB : a < renewalLevel h (streamShift m x) := lt_of_not_ge hn'.2.1
    have hC : ∀ k, m ≤ k → k ≤ 2*n+1 → (integerSum x k:ℝ)-(integerSum x m:ℝ)<a := by
      simpa only [C,Set.mem_ofPred_eq,not_exists,not_and,not_le] using hn'.2.2
    have hh := prefix_record_error_tail (x := x) (h := h) (by omega : m ≤ 2*n+1)
      hx (half_pos p.variance_pos).le ha hB.le hC
    change recordError _ _ _ ≤ recordError _ _ _+a+(p.variance/2)*h at hh
    exact (not_lt_of_ge (hh.trans (by linarith))) hb
  have hb := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact hb.trans ((measureReal_union_le (A ∪ B) C).trans
    (add_le_add (measureReal_union_le A B) le_rfl))

lemma terminal_ratio_bound {N r J : ℕ} (hN : 0<N) (hJ : 0<J) (hr : J*r ≤ N)
    {c ε K σ : ℝ} (hc : 0 < c) (hε : 0<ε) (hK : 0 ≤ K) :
    K*((r:ℝ)*σ^2/(c*⌈ε*Real.sqrt (N:ℝ)⌉₊/2)^2) ≤
      4*K*σ^2/(c^2*ε^2*(J:ℝ)) := by
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have hJ' : (0:ℝ)<J := by exact_mod_cast hJ
  have hceil := Nat.le_ceil (ε*Real.sqrt (N:ℝ))
  have hden : 0 < c*ε*Real.sqrt (N:ℝ)/2 := by positivity
  have hdiv : (r:ℝ)/(N:ℝ) ≤ 1/(J:ℝ) := by
    rw [div_le_div_iff₀ hN' hJ']
    simpa [mul_comm] using (show (J:ℝ)*r ≤ N by exact_mod_cast hr)
  calc
    K*((r:ℝ)*σ^2/(c*⌈ε*Real.sqrt (N:ℝ)⌉₊/2)^2) ≤
        K*((r:ℝ)*σ^2/(c*ε*Real.sqrt (N:ℝ)/2)^2) := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden)
      have hbase : c*ε*Real.sqrt (N:ℝ)/2 ≤ c*⌈ε*Real.sqrt (N:ℝ)⌉₊/2 := by
        nlinarith [mul_le_mul_of_nonneg_left hceil hc.le]
      exact pow_le_pow_left₀ hden.le hbase 2
    _ = (4*K*σ^2/(c^2*ε^2))*((r:ℝ)/(N:ℝ)) := by
      rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hN'.le]
      ring
    _ ≤ (4*K*σ^2/(c^2*ε^2))*(1/(J:ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = _ := by ring

lemma division_prefix_properties {N J : ℕ} (hJ : 2 ≤ J) (hN : J ≤ N) :
    (N-N/J)+N/J=N ∧ 2*(N/J) ≤ N ∧ N ≤ (2*J)*(N/J) := by
  have hJ0 : 0<J := by omega
  have hr : 1 ≤ N/J := (Nat.le_div_iff_mul_le hJ0).mpr (by omega)
  have hm := Nat.div_mul_le_self N J
  have hmod := Nat.mod_lt N hJ0
  have hdecomp := Nat.mod_add_div N J
  have h2 := Nat.mul_le_mul_right (N/J) hJ
  have hjr := Nat.mul_le_mul_left J hr
  have hmul : (2*J)*(N/J)=2*(J*(N/J)) := by ring
  rw [mul_comm (N/J) J] at hm
  constructor
  · exact Nat.sub_add_cancel (Nat.div_le_self N J)
  constructor
  · exact h2.trans hm
  · rw [hmul]
    omega

/-- The weak-record approximation for the **whole** conditioned bridge.
The terminal part is controlled by reversal and a second-moment maximal
inequality, not by independence at the random Vervaat cut. -/
theorem CriticalEvenOffspring.bridge_record_error (p : CriticalEvenOffspring)
    {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun n => (p.streamBridgeLaw n).real {x |
      δ*Real.sqrt ((2*n+1:ℕ):ℝ) < recordError (p.variance/2) (integerSum x) (2*n+1)})
      atTop (𝓝 0) := by
  obtain ⟨K,hK,hdom⟩ := p.bridge_prefix_domination_fraction 2 (by norm_num)
  obtain ⟨c,ρ,hc,hρ,hρ1,hbound⟩ := p.renewal_lower_tail
  let ν := p.variance/2
  have hν : 0<ν := half_pos p.variance_pos
  let ε := δ/(4*(c+ν))
  have hε : 0<ε := div_pos hδ (by positivity)
  have heq : (c+ν)*ε=δ/4 := by dsimp [ε]; field_simp
  let C := 4*K*p.sigma^2/(c^2*ε^2)
  have hC : 0 ≤ C := by positivity
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  intro η hη
  have hjlim : Tendsto (fun J : ℕ => C/(J:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨J,hJ,hCJ⟩ := ((eventually_ge_atTop 2).and
    (hjlim.eventually (eventually_lt_nhds (show (0:ℝ)<η/3 by positivity)))).exists
  have hJ0 : 0<J := by omega
  let r : ℕ → ℕ := fun n => (2*n+1)/J
  let m : ℕ → ℕ := fun n => 2*n+1-r n
  have hs : ∀ n, m n+r n=2*n+1 := fun n => Nat.sub_add_cancel (Nat.div_le_self (2*n+1) J)
  have hfrac : ∀ᶠ n in atTop, 2*n+1 ≤ (2*J)*r n := by
    filter_upwards [odd_size_tendsto.eventually_ge_atTop J] with n hn
    exact (division_prefix_properties hJ hn).2.2
  have hpre := p.bridge_prefix_record_error (by omega : 0<2*J) m r hs hfrac (half_pos hδ)
  have hgeo := p.bridge_geometric_vanish hε hρ.le hρ1
  have hlarge : ∀ᶠ n in atTop, c+ν ≤ δ/4*Real.sqrt ((2*n+1:ℕ):ℝ) :=
    (odd_sqrt_tendsto.const_mul_atTop (by positivity : 0<δ/4)).eventually_ge_atTop (c+ν)
  filter_upwards [hdom,odd_size_tendsto.eventually_ge_atTop J,hlarge,
    hpre.eventually (eventually_lt_nhds (show (0:ℝ)<η/3 by positivity)),
    hgeo.eventually (eventually_lt_nhds (show (0:ℝ)<η/3 by positivity))] with n hn hJn hln hpn hgn
  let s := Real.sqrt ((2*n+1:ℕ):ℝ)
  let h := ⌈ε*s⌉₊
  have hsp : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hhp : (0:ℝ)<h := (mul_pos hε hsp).trans_le (Nat.le_ceil _)
  have hsmall : (c+ν)*h ≤ δ/2*s := by
    have hh : (h:ℝ) ≤ ε*s+1 := (Nat.ceil_lt_add_one (mul_nonneg hε.le hsp.le)).le
    have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ c+ν by positivity)
    have heq' := congrArg (fun t : ℝ => t*s) heq
    dsimp [s] at heq' ⊢
    nlinarith
  have hthresh : δ/2*s+c*h+ν*h ≤ δ*s := by nlinarith
  have hmono : (p.streamBridgeLaw n).real {x | δ*s < recordError ν (integerSum x) (2*n+1)} ≤
      (p.streamBridgeLaw n).real {x | δ/2*s+c*h+ν*h < recordError ν (integerSum x) (2*n+1)} := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    exact hthresh.trans_lt hx
  have hb := p.bridge_record_tail_bound (hs n) (h := h) (t := δ/2*s) (mul_nonneg hc.le hhp.le)
  have hp : (p.streamBridgeLaw n).real {x | δ/2*s < recordError ν (integerSum x) (m n)} < η/3 := by
    apply lt_of_le_of_lt _ hpn
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    exact ⟨m n,le_rfl,hx⟩
  have hg : (p.streamBridgeLaw n).real {x | renewalLevel h (streamShift (m n) x) ≤ c*h} < η/3 :=
    (p.bridge_shift_ladder_bound hρ.le hbound n (m n) h).trans_lt hgn
  have ht : (p.streamBridgeLaw n).real {x | ∃ k, m n ≤ k ∧ k ≤ 2*n+1 ∧
      c*h ≤ (integerSum x k:ℝ)-(integerSum x (m n):ℝ)} ≤ C/(J:ℝ) := by
    have hhalf : 2*r n ≤ 2*n+1 := (division_prefix_properties hJ hJn).2.1
    have hh := p.bridge_terminal_maximal_bound hK.le hn hhalf (mul_pos hc hhp)
    apply hh.trans
    have he := terminal_ratio_bound (by omega : 0<2*n+1) hJ0
      (show J*r n ≤ 2*n+1 by simpa only [r,mul_comm] using Nat.div_mul_le_self (2*n+1) J)
      hc hε hK.le (σ := p.sigma)
    exact he.trans_eq (by dsimp only [C]; ring)
  have hh := (hmono.trans hb).trans (add_le_add (add_le_add hp.le hg.le) ht)
  change (p.streamBridgeLaw n).real {x | δ*s < recordError ν (integerSum x) (2*n+1)} < η
  linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.code_integral (p : CriticalEvenOffspring) (n : ℕ)
    (F : Code (2*n+1) → ℝ) :
    (∫ d,F d ∂p.codeLaw n)=∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1))*F d := by
  rw [codeLaw,integral_map (measurable_of_countable (arrayTree n)).aemeasurable
    (measurable_of_countable F).aestronglyMeasurable]
  exact p.arrayTree_expectation n F

lemma integerSum_arrayStream_bridge {N : ℕ} (d : Bridge N) {k : ℕ} (hk : k ≤ N) :
    integerSum (arrayStream (bridgeEmbedding N d)) k=walk d.val k := by
  unfold integerSum walk
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i hi => (⟨i.val,by
    have hh := Finset.mem_filter.mp hi
    exact hh.2⟩ : Fin k))
  · intro i hi
    exact Finset.mem_univ _
  · intro i hi j hj he
    exact Fin.ext (congrArg (fun z : Fin k => z.val) he)
  · intro i _
    exact ⟨⟨i.val,i.isLt.trans_le hk⟩,by simp [i.isLt],rfl⟩
  · intro i hi
    have hi' : i.val<k := (Finset.mem_filter.mp hi).2
    simp only [arrayStream,dite_eq_left (hi'.trans_le hk),bridgeEmbedding]
    rfl

lemma measurable_recordError_integerSum (ν : ℝ) (N : ℕ) :
    Measurable (fun x => recordError ν (integerSum x) N) := by
  have hh := (measurable_of_countable (fun d : Fin N → ℕ => recordError ν (integerSum (arrayStream d)) N)).comp
    (measurable_streamPrefix N)
  simpa only [Function.comp_def,recordError_arrayStream_prefix N _ le_rfl] using hh

lemma badHeightFraction_nonneg {N : ℕ} (ν a : ℝ) (d : Code N) : 0 ≤ badHeightFraction ν a d := by
  unfold badHeightFraction
  positivity

lemma recordError_reverse_array_bridge {N : ℕ} (ν : ℝ) (b : Bridge N) :
    recordError ν (reversedPath (integerSum (arrayStream (bridgeEmbedding N b))) N) N =
      recordError ν (reversedPath (walk b.val) N) N := by
  apply recordError_congr
  intro k hk
  simp only [reversedPath,integerSum_arrayStream_bridge b le_rfl,
    integerSum_arrayStream_bridge b (Nat.sub_le N k)]

lemma recordError_reverse_streamPrefix (ν : ℝ) (N : ℕ) (x : ℕ → ℕ) :
    recordError ν (reversedPath (integerSum (arrayStream (streamPrefix N x))) N) N =
      recordError ν (integerSum (reverseFirst N x)) N := by
  apply recordError_congr
  intro k hk
  rw [reversedPath,integerSum_arrayStream_prefix N x le_rfl,
    integerSum_arrayStream_prefix N x (Nat.sub_le N k),integerSum_reverseFirst x N k hk]

lemma CriticalEvenOffspring.code_average_height_error (p : CriticalEvenOffspring) (n : ℕ) (ν a : ℝ) :
    (∫ d,badHeightFraction ν a d ∂p.codeLaw n) =
      (p.streamBridgeLaw n).real {x | a < recordError ν (integerSum x) (2*n+1)} := by
  classical
  let N := 2*n+1
  let F : (Fin N → ℕ) → ℝ := fun d =>
    if a < recordError ν (reversedPath (integerSum (arrayStream d)) N) N then 1 else 0
  have hsum : (∫ d,badHeightFraction ν a d ∂p.codeLaw n) = ∫ d,F d ∂p.iidBridgeLaw n := by
    rw [p.code_integral, CriticalEvenOffspring.iidBridgeLaw, p.bridge_integral_eq]
    have hh := uniform_vertex_height_error p n ν a
    unfold badHeightFraction
    convert hh using 1
    · simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    · apply Finset.sum_congr rfl
      intro b _
      dsimp only [F,N]
      rw [recordError_reverse_array_bridge]
      rfl
  rw [hsum]
  have hr := (p.streamBridge_restrict n).integral_comp (measurable_of_countable F).aestronglyMeasurable
  rw [← hr]
  have hF : (fun x => F (streamPrefix N x)) = fun x =>
      if a < recordError ν (integerSum (reverseFirst N x)) N then (1:ℝ) else 0 := by
    funext x
    simp only [F,recordError_reverse_streamPrefix]
  change (∫ x,F (streamPrefix N x) ∂p.streamBridgeLaw n)=_
  rw [hF]
  have hE : MeasurableSet {x | a < recordError ν (integerSum x) N} :=
    measurableSet_lt measurable_const (measurable_recordError_integerSum ν N)
  have hm := (p.streamBridge_reverse n).measureReal_preimage hE.nullMeasurableSet
  rw [← hm]
  exact integral_indicator_one (hE.preimage (reverseFirst_preserving p N).measurable)

/-- The expected proportion of vertices with macroscopic height/walk error
vanishes. This is an exact consequence of cyclic averaging and the full
conditioned-bridge weak-record theorem. -/
theorem CriticalEvenOffspring.average_height_error_limit (p : CriticalEvenOffspring)
    {δ : ℝ} (hδ : 0<δ) :
    Tendsto (fun n => ∫ d,badHeightFraction (p.variance/2)
      (δ*Real.sqrt ((2*n+1:ℕ):ℝ)) d ∂p.codeLaw n) atTop (𝓝 0) := by
  simpa only [p.code_average_height_error] using p.bridge_record_error hδ

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_HeightTightness
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability _root_.OAI.FKCRT.TreeCoding.instMeasurableSpaceBool_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.code_probability_le_stream (p : CriticalEvenOffspring) (n : ℕ)
    (E : Set (Code (2*n+1))) (A : Set (ℕ → ℕ))
    (hEA : ∀ d ∈ E, ∀ x, streamPrefix (2*n+1) x=codeEmbedding (2*n+1) d → x∈A) :
    (p.codeLaw n).real E ≤ p.streamLaw.real A / codePartition p (2*n+1) := by
  classical
  let N := 2*n+1
  let C : Code N → Set (ℕ → ℕ) := fun d => if d∈E then
    streamPrefix N ⁻¹' {codeEmbedding N d} else ∅
  have hm (d) : MeasurableSet (C d) := by
    dsimp [C]
    split_ifs
    · exact (measurableSet_singleton _).preimage (measurable_streamPrefix N)
    · exact MeasurableSet.empty
  have hd : Pairwise (fun d e => Disjoint (C d) (C e)) := by
    intro d e hde
    dsimp [C]
    split_ifs <;> try simp
    exact (Set.disjoint_singleton.mpr ((codeEmbedding N).injective.ne hde)).preimage _
  have he (d : Code N) : p.streamLaw.real (C d) = if d∈E then codeWeight p d else 0 := by
    dsimp [C]
    split_ifs
    · rw [(p.streamPrefix_hasLaw N).measurePreserving (measurable_streamPrefix N) |>.measureReal_preimage
        (measurableSet_singleton _).nullMeasurableSet]
      exact p.iid_bridge_singleton ⟨d.val,d.property.1⟩
    · simp
  have hb : (∑ d : Code N, if d∈E then codeWeight p d else 0) ≤ p.streamLaw.real A := by
    rw [← show p.streamLaw.real (⋃ d, C d)=∑ d : Code N, if d∈E then codeWeight p d else 0 by
      rw [measureReal_iUnion_fintype hd hm]; simp only [he]]
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    rintro x ⟨_,⟨d,rfl⟩,hx⟩
    dsimp [C] at hx
    split_ifs at hx with hE
    · exact hEA d hE x hx
    · exact hx.elim
  rw [← integral_indicator_one (μ := p.codeLaw n) (show MeasurableSet E from trivial),p.code_integral]
  apply (le_div_iff₀ (codePartition_odd_pos p n)).mpr
  have heq : (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
      E.indicator (fun _ => (1:ℝ)) d)*codePartition p (2*n+1)=
      ∑ d : Code (2*n+1), if d∈E then codeWeight p d else 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    dsimp [Set.indicator]
    split_ifs
    · field_simp [(codePartition_odd_pos p n).ne']
    · simp
  change (∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1)) *
    E.indicator (fun _ => (1:ℝ)) d)*codePartition p (2*n+1) ≤ _
  rw [heq]
  exact hb

lemma recordHeight_congr_prefix {S T : ℕ → ℤ} {N j : ℕ} (hj : j ≤ N)
    (hST : ∀ k ≤ N, S k=T k) : recordHeight S 0 j=recordHeight T 0 j := by
  unfold recordHeight
  congr 1
  ext k
  simp only [mem_reverseRecords]
  constructor <;> rintro ⟨hk0,hkj,hk⟩ <;> refine ⟨hk0,hkj,?_⟩ <;> intro r hkr hrj
  · rw [← hST k (by omega),← hST r (by omega)]
    exact hk r hkr hrj
  · rw [hST k (by omega),hST r (by omega)]
    exact hk r hkr hrj

lemma codeHeightModulusFailure_stream {N m : ℕ} {c : ℝ} {d : Code N}
    (hd : d∈codeHeightModulusFailure m c) {x : ℕ → ℕ}
    (hx : streamPrefix N x=codeEmbedding N d) : x∈heightModulusFailure N m c := by
  have hS (k : ℕ) (hk : k ≤ N) : integerSum x k=walk d.val k := by
    rw [← integerSum_arrayStream_prefix N x hk,hx]
    exact integerSum_arrayStream_bridge ⟨d.val,d.property.1⟩ hk
  have hH (k : ℕ) (hk : k ≤ N) : recordHeight (integerSum x) 0 k=height d.val k :=
    (recordHeight_congr_prefix hk hS).trans (height_eq_recordHeight d.val hk).symm
  obtain ⟨a,b,hab,hb,hosc,hbad⟩ := hd
  refine ⟨a,b,hab,hb,?_,?_⟩
  · intro u v hau hub hav hvb
    rw [hS u (by omega),hS v (by omega)]
    exact hosc u v hau hub hav hvb
  · simpa only [hH b hb,hH a (hab.trans hb)] using hbad

lemma CriticalEvenOffspring.code_height_modulus_bound (p : CriticalEvenOffspring) :
    ∃ c ρ : ℝ, 0 < c ∧ 0<ρ ∧ ρ<1 ∧ ∀ n m : ℕ,
      (p.codeLaw n).real (codeHeightModulusFailure m (c*m)) ≤
        ((2*n+1:ℕ)+1:ℝ)*ρ^m/codePartition p (2*n+1) := by
  obtain ⟨c,ρ,hc,hr0,hr1,hb⟩ := p.height_modulus_probability
  refine ⟨c,ρ,hc,hr0,hr1,fun n m => ?_⟩
  apply (p.code_probability_le_stream n _ _ (fun _ hd _ hx => codeHeightModulusFailure_stream hd hx)).trans
  apply div_le_div_of_nonneg_right _ (codePartition_nonneg p _)
  have hnn : 0 ≤ ((2*n+1:ℕ)+1:ℝ)*ρ^m := by positivity
  have hh' : p.streamLaw (heightModulusFailure (2*n+1) m (c*m)) ≤
      ENNReal.ofReal (((2*n+1:ℕ)+1:ℝ)*ρ^m) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((2*n+1:ℕ)+1:ℝ)),
      show ((2*n+1:ℕ):ℝ)+1=((2*n+1+1:ℕ):ℝ) by push_cast; rfl,
      ENNReal.ofReal_natCast]
    exact hb (2*n+1) m
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh'
  simpa only [measureReal_def,ENNReal.toReal_ofReal hnn] using hh

lemma CriticalEvenOffspring.code_geometric_vanish (p : CriticalEvenOffspring)
    {ε ρ : ℝ} (hε : 0<ε) (hρ : 0 ≤ ρ) (hρ1 : ρ<1) :
    Tendsto (fun n => ((2*n+1:ℕ)+1:ℝ)*ρ^⌈ε*Real.sqrt ((2*n+1:ℕ):ℝ)⌉₊ /
      codePartition p (2*n+1)) atTop (𝓝 0) := by
  let s : ℕ → ℝ := fun n => Real.sqrt ((2*n+1:ℕ):ℝ)
  have hs0 (n) : 0 ≤ s n := Real.sqrt_nonneg _
  have h5 := polynomial_geometric_ceil odd_sqrt_tendsto hs0 hε hρ hρ1 5
  have h3 := polynomial_geometric_ceil odd_sqrt_tendsto hs0 hε hρ hρ1 3
  have hpos : 0 < 2/(p.sigma*Real.sqrt (2*Real.pi)) :=
    div_pos (by norm_num) (mul_pos p.sigma_pos (Real.sqrt_pos.mpr (by positivity)))
  have ht := (h5.add h3).div p.codePartition_asymptotic hpos.ne'
  simp only [zero_add,zero_div] at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  have hs : s n^2=((2*n+1:ℕ):ℝ) := Real.sq_sqrt (by positivity)
  have hsne : s n≠0 := (Real.sqrt_pos.mpr (by positivity : (0:ℝ)<((2*n+1:ℕ):ℝ))).ne'
  dsimp only [Pi.div_apply]
  rw [show (2*n+1:ℝ)=((2*n+1:ℕ):ℝ) by push_cast; rfl]
  change (((2*n+1:ℕ):ℝ)+1)*ρ^⌈ε*s n⌉₊/codePartition p (2*n+1)=
    ((s n)^5*ρ^⌈ε*s n⌉₊+(s n)^3*ρ^⌈ε*s n⌉₊)/
      (((2*n+1:ℕ):ℝ)*s n*codePartition p (2*n+1))
  have he : (s n)^5*ρ^⌈ε*s n⌉₊+(s n)^3*ρ^⌈ε*s n⌉₊ =
      (((2*n+1:ℕ):ℝ)+1)*ρ^⌈ε*s n⌉₊ * (((2*n+1:ℕ):ℝ)*s n) := by
    calc
      _ = ((s n)^2+1)*ρ^⌈ε*s n⌉₊*((s n)^2*s n) := by ring
      _ = _ := by rw [hs]
  rw [he]
  push_cast
  rw [mul_comm _ (codePartition p (2*n+1)),mul_div_mul_right]
  exact mul_ne_zero (by positivity) hsne

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma pathOscillation_nonneg (δ : ℝ) (f : C(unitInterval,ℝ)) : 0 ≤ pathOscillation δ f := norm_nonneg _

lemma pathOscillation_le {δ M : ℝ} (hM : 0 ≤ M) (f : C(unitInterval,ℝ))
    (h : ∀ s t, dist s t ≤ δ → |f s-f t| ≤ M) : pathOscillation δ f ≤ M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro st
  exact h st.val.1 st.val.2 st.property

lemma sub_le_pathOscillation {δ : ℝ} (f : C(unitInterval,ℝ)) {s t : unitInterval}
    (hst : dist s t ≤ δ) : |f s-f t| ≤ pathOscillation δ f :=
  (oscillationPath δ f).norm_coe_le_norm ⟨(s,t),hst⟩

lemma pathOscillation_lipschitz (δ : ℝ) : LipschitzWith 2 (pathOscillation δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  apply (dist_norm_norm_le (oscillationPath δ f) (oscillationPath δ g)).trans
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro st
  change |(f st.val.1-f st.val.2)-(g st.val.1-g st.val.2)| ≤ (2:ℝ≥0)*‖f-g‖
  have h1 := (f-g).norm_coe_le_norm st.val.1
  have h2 := (f-g).norm_coe_le_norm st.val.2
  change |f st.val.1-g st.val.1| ≤ ‖f-g‖ at h1
  change |f st.val.2-g st.val.2| ≤ ‖f-g‖ at h2
  have ht := abs_sub ((f-g) st.val.1) ((f-g) st.val.2)
  simp only [ContinuousMap.sub_apply] at ht
  have he : (f st.val.1-f st.val.2)-(g st.val.1-g st.val.2)=
      (f st.val.1-g st.val.1)-(f st.val.2-g st.val.2) := by ring
  rw [he]
  change _ ≤ 2*‖f-g‖
  linarith

lemma pathOscillation_vanish (f : C(unitInterval,ℝ)) :
    Tendsto (fun j : ℕ => pathOscillation (1/(j+1:ℝ)) f) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε/2) (by positivity)
  have ht : Tendsto (fun j : ℕ => 1/(j+1:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with j hj
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (pathOscillation_nonneg _ _)]
  apply lt_of_le_of_lt (pathOscillation_le (by positivity : 0 ≤ ε/2) f ?_) (by linarith)
  intro s t hst
  exact (hd (hst.trans_lt hj)).le


lemma oscillationGauge_continuous (δ ε : ℝ) : Continuous (oscillationGauge δ ε) :=
  continuous_const.min ((pathOscillation_lipschitz δ).continuous.div_const ε)

lemma oscillationGauge_nonneg (δ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (f : C(unitInterval,ℝ)) :
    0 ≤ oscillationGauge δ ε f := le_min (by norm_num) (div_nonneg (pathOscillation_nonneg _ _) hε)

lemma oscillationGauge_abs_le (δ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (f : C(unitInterval,ℝ)) :
    |oscillationGauge δ ε f| ≤ 1 := by
  rw [abs_of_nonneg (oscillationGauge_nonneg δ hε f)]
  exact min_le_left _ _

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_9
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitInterval_solutions_9
lemma oscillationGauge_integral_vanish {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → C(unitInterval,ℝ)}
    (hX : AEMeasurable X μ) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun j : ℕ => ∫ ω, oscillationGauge (1/(j+1:ℝ)) ε (X ω) ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1:ℝ))
    (F := fun j ω => oscillationGauge (1/(j+1:ℝ)) ε (X ω)) (f := fun _=>0)
    (fun j => ((oscillationGauge_continuous _ ε).measurable.comp_aemeasurable hX).aestronglyMeasurable)
    (integrable_const _) (fun _ => ae_of_all μ (fun _ => oscillationGauge_abs_le _ hε.le _)) (by
      apply ae_of_all
      intro ω
      have ht := tendsto_const_nhds.min ((pathOscillation_vanish (X ω)).div_const ε)
        (f := fun _ : ℕ => (1:ℝ))
      simpa only [oscillationGauge,zero_div,min_eq_right (by norm_num : (0:ℝ) ≤ 1)] using ht)
  simpa only [integral_zero] using hh

lemma oscillation_probability_le_gauge {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → C(unitInterval,ℝ)}
    (hX : Measurable X) (δ : ℝ) {ε : ℝ} (hε : 0<ε) :
    μ.real {ω | ε<pathOscillation δ (X ω)} ≤ ∫ ω,oscillationGauge δ ε (X ω) ∂μ := by
  have hg : Integrable (fun ω => oscillationGauge δ ε (X ω)) μ :=
    Integrable.of_bound ((oscillationGauge_continuous _ _).measurable.comp hX).aestronglyMeasurable 1
      (ae_of_all μ (fun _ => oscillationGauge_abs_le _ hε.le _))
  let E := {ω | ε<pathOscillation δ (X ω)}
  have hE : MeasurableSet E := measurableSet_lt measurable_const ((pathOscillation_lipschitz δ).continuous.measurable.comp hX)
  rw [← integral_indicator_one hE]
  apply integral_mono ((integrable_const (1:ℝ)).indicator hE) hg
  intro ω
  by_cases hω : ω∈E
  · rw [Set.indicator_of_mem hω]
    exact le_min le_rfl ((le_div_iff₀ hε).mpr (by simpa using hω.le))
  · rw [Set.indicator_of_notMem hω]
    exact oscillationGauge_nonneg δ hε.le _

lemma continuousPath_modulus_tight {Ω : ℕ → Type*} {Ω' : Type*}
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n, Measure (Ω n)} {ν : Measure Ω'} [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {X : ∀ n, Ω n → C(unitInterval,ℝ)} {Y : Ω' → C(unitInterval,ℝ)}
    (h : TendstoInDistribution X atTop Y μ ν) (hXm : ∀ n, Measurable (X n))
    {ε η : ℝ} (hε : 0<ε) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ ∀ᶠ n in atTop,
      (μ n).real {ω | ε<pathOscillation δ (X n ω)} ≤ η := by
  obtain ⟨j,hj⟩ := ((oscillationGauge_integral_vanish h.aemeasurable_limit hε).eventually
    (gt_mem_nhds (half_pos hη))).exists
  refine ⟨1/(j+1:ℝ),by positivity,?_⟩
  have ht := integral_tendsto_of_tendstoInDistribution h (oscillationGauge_continuous (1/(j+1:ℝ)) ε)
    (oscillationGauge_abs_le _ hε.le)
  filter_upwards [ht.eventually (gt_mem_nhds (hj.trans (half_lt_self hη)))] with n hn
  exact (oscillation_probability_le_gauge (hXm n) _ hε).trans hn.le

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma height_pair_control {N m a b : ℕ} {c : ℝ} {d : Code N}
    (hgood : d∉codeHeightModulusFailure m c) (hb : b ≤ N)
    (hosc : ∀ u v, a ≤ u → u ≤ b → a ≤ v → v ≤ b → (walk d.val u:ℝ)-(walk d.val v:ℝ) < c)
    {u v : ℕ} (hau : a ≤ u) (hub : u ≤ b) (hav : a ≤ v) (hvb : v ≤ b) :
    |(height d.val u:ℝ)-(height d.val v:ℝ)| ≤ m := by
  have hh {j k : ℕ} (hjk : j ≤ k) (haj : a ≤ j) (hkb : k ≤ b) :
      height d.val k ≤ height d.val j+m ∧ height d.val j ≤ height d.val k+m := by
    by_contra hn
    exact hgood ⟨j,k,hjk,hkb.trans hb,fun s t hjs hsk hjt htk =>
      hosc s t (haj.trans hjs) (hsk.trans hkb) (haj.trans hjt) (htk.trans hkb),hn⟩
  obtain h₁|h₁ := le_total u v
  · have hh' := hh h₁ hau hvb
    have h2 : (height d.val v:ℝ) ≤ height d.val u+m := by exact_mod_cast hh'.1
    have h3 : (height d.val u:ℝ) ≤ height d.val v+m := by exact_mod_cast hh'.2
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · have hh' := hh h₁ hav hub
    have h2 : (height d.val u:ℝ) ≤ height d.val v+m := by exact_mod_cast hh'.1
    have h3 : (height d.val v:ℝ) ≤ height d.val u+m := by exact_mod_cast hh'.2
    exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma error_le_error_add {w₁ w₂ h₁ h₂ ν a b : ℝ} (hν : 0 ≤ ν)
    (hw : |w₁-w₂| ≤ a) (hh : |h₁-h₂| ≤ b) :
    |w₁-ν*h₁| ≤ |w₂-ν*h₂|+a+ν*b := by
  have he : w₁-ν*h₁=(w₂-ν*h₂)+(w₁-w₂)-ν*(h₁-h₂) := by ring
  rw [he]
  have ht := (abs_sub ((w₂-ν*h₂)+(w₁-w₂)) (ν*(h₁-h₂))).trans
    (add_le_add (abs_add_le (w₂-ν*h₂) (w₁-w₂)) le_rfl)
  rw [abs_mul,abs_of_nonneg hν] at ht
  nlinarith

lemma badHeightFraction_interval_lower {N r a : ℕ} (har : a+r ≤ N)
    {ν t : ℝ} (d : Code N)
    (hbad : ∀ k < r, t< |(walk d.val (a+k):ℝ)-ν*height d.val (a+k)|) :
    (r:ℝ)/(N:ℝ) ≤ badHeightFraction ν t d := by
  classical
  let f : Fin r → Fin N := fun k => ⟨a+k.val,by omega⟩
  let S := Finset.univ.filter (fun k : Fin N => t< |(walk d.val k.val:ℝ)-ν*height d.val k.val|)
  have hm : ∀ k : Fin r, f k∈S := fun k => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbad k.val k.isLt⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hh := congrArg Fin.val hij
    dsimp [f] at hh
    exact Fin.ext (by omega)
  have hc : r ≤ S.card := by
    have hh := Finset.card_le_card (show Finset.univ.image f ⊆ S by
      intro k hk
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
      exact hm i)
    simpa only [Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_fin] using hh
  unfold badHeightFraction
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  rw [← Finset.sum_filter]
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using (show (r:ℝ) ≤ S.card by exact_mod_cast hc)

lemma uniform_error_of_average {N m r : ℕ} {ν c a t : ℝ} (d : Code N)
    (hν : 0 ≤ ν) (hr : r ≤ N) (hgood : d∉codeHeightModulusFailure m c)
    (hosc : ∀ u v, u ≤ N → v ≤ N → (u:ℤ)-v ≤ r → (v:ℤ)-u ≤ r →
       |(walk d.val u:ℝ)-(walk d.val v:ℝ)| ≤ a)
    (hac : a < c)
    (havg : badHeightFraction ν t d < (r:ℝ)/(N:ℝ)) :
    ∀ j<N, |(walk d.val j:ℝ)-ν*height d.val j| ≤ t+a+ν*m := by
  intro j hj
  by_contra hn
  have hjbad : t+a+ν*m< |(walk d.val j:ℝ)-ν*height d.val j| := lt_of_not_ge hn
  let b := min j (N-r)
  have hbj : b ≤ j := min_le_left _ _
  have hbr : b+r ≤ N := by have := min_le_right j (N-r); dsimp [b]; omega
  have hjbr : j ≤ b+r := by dsimp [b]; omega
  have hw (u v : ℕ) (hbu : b ≤ u) (hub : u ≤ b+r) (hbv : b ≤ v) (hvb : v ≤ b+r) :
      |(walk d.val u:ℝ)-(walk d.val v:ℝ)| ≤ a := hosc u v (by omega) (by omega) (by omega) (by omega)
  have hlocal : ∀ u v, b ≤ u → u ≤ b+r → b ≤ v → v ≤ b+r →
      (walk d.val u:ℝ)-(walk d.val v:ℝ) < c := by
    intro u v hbu hub hbv hvb
    exact (le_abs_self _).trans_lt ((hw u v hbu hub hbv hvb).trans_lt hac)
  have hfrac := badHeightFraction_interval_lower (ν := ν) (t := t) hbr d (fun k hk => ?_)
  · exact (not_lt_of_ge hfrac) havg
  have hH := height_pair_control hgood hbr hlocal hbj hjbr (by omega : b ≤ b+k) (by omega : b+k ≤ b+r)
  have hW := hw j (b+k) hbj hjbr (by omega) (by omega)
  have he := error_le_error_add hν hW hH
  linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_10
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitInterval_solutions_10
lemma CriticalEvenOffspring.codeWalk_converges (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    TendstoInDistribution (fun n (d : Code (2*n+1)) => walkPolygon p.sigma d.val) atTop
      (fun ω => vervaat (bridgePath B ω)) p.codeLaw P := by
  have hX (n : ℕ) : AEMeasurable (fun d : Code (2*n+1) => walkPolygon p.sigma d.val) (p.codeLaw n) :=
    (measurable_of_countable _).aemeasurable
  have hY := (p.iidVervaat_CLT hB).aemeasurable_limit
  refine ⟨hX,hY,?_⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  change Tendsto (fun n => ∫ f,F f ∂(p.codeLaw n).map (fun d => walkPolygon p.sigma d.val)) atTop
    (𝓝 (∫ f,F f ∂P.map (fun ω => vervaat (bridgePath B ω))))
  simp_rw [integral_map (hX _) F.continuous.aestronglyMeasurable,
    integral_map hY F.continuous.aestronglyMeasurable,p.code_integral]
  exact p.codeWalk_CLT hB F

lemma gridPoint_dist_le {N r u v : ℕ} (_hN : 0<N) (hu : u ≤ N) (hv : v ≤ N)
    (huv : (u:ℤ)-v ≤ r) (hvu : (v:ℤ)-u ≤ r) :
    dist (gridPoint N ⟨u,by omega⟩) (gridPoint N ⟨v,by omega⟩) ≤ (r:ℝ)/(N:ℝ) := by
  change |(u:ℝ)/(N:ℝ)-(v:ℝ)/(N:ℝ)| ≤ (r:ℝ)/(N:ℝ)
  rw [← sub_div,abs_div,abs_of_nonneg (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply abs_le.mpr
  constructor
  · have hh : (v:ℝ)-(u:ℝ) ≤ r := by exact_mod_cast hvu
    linarith
  · exact_mod_cast huv

lemma walk_grid_oscillation {N r : ℕ} (hN : 0<N) {σ δ θ : ℝ} (hσ : 0<σ)
    (d : Code N) (hr : (r:ℝ)/(N:ℝ) ≤ δ)
    (hosc : pathOscillation δ (walkPolygon σ d.val) ≤ θ) :
    ∀ u v, u ≤ N → v ≤ N → (u:ℤ)-v ≤ r → (v:ℤ)-u ≤ r →
      |(walk d.val u:ℝ)-(walk d.val v:ℝ)| ≤ θ*(σ*Real.sqrt N) := by
  intro u v hu hv huv hvu
  have hp := (sub_le_pathOscillation (walkPolygon σ d.val) ((gridPoint_dist_le hN hu hv huv hvu).trans hr)).trans hosc
  simp only [walkPolygon,interpolation_gridPoint hN] at hp
  rw [← sub_div,abs_div,abs_of_pos (mul_pos hσ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)))] at hp
  exact (div_le_iff₀ (mul_pos hσ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)))).mp hp

lemma floor_fraction_bounds {δ : ℝ} (hδ : 0<δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : 0<N)
    (hlarge : 2 ≤ δ*N) :
    ⌊δ*N⌋₊ ≤ N ∧ (⌊δ*N⌋₊:ℝ)/(N:ℝ) ≤ δ ∧ δ/2 ≤ (⌊δ*N⌋₊:ℝ)/(N:ℝ) := by
  have hN0 : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hfloor := Nat.floor_le (mul_nonneg hδ.le hN0.le)
  have hfloor' := Nat.lt_floor_add_one (δ*N)
  constructor
  · exact_mod_cast hfloor.trans (mul_le_of_le_one_left hN0.le hδ1)
  constructor
  · exact (div_le_iff₀ hN0).mpr hfloor
  · apply (le_div_iff₀ hN0).mpr
    linarith

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma CriticalEvenOffspring.bad_fraction_markov (p : CriticalEvenOffspring) (n : ℕ) (ν a : ℝ)
    {t : ℝ} (ht : 0<t) :
    (p.codeLaw n).real {d | t ≤ badHeightFraction ν a d} ≤
      (∫ d,badHeightFraction ν a d ∂p.codeLaw n)/t := by
  apply (le_div_iff₀ ht).mpr
  have hh := mul_meas_ge_le_integral_of_nonneg
    (μ := p.codeLaw n) (f := badHeightFraction ν a)
    (ae_of_all _ (fun d => badHeightFraction_nonneg ν a d)) (Integrable.of_finite) t
  simpa only [mul_comm] using hh

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_11_r574da1_1 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩
/-- Exact conditioned critical finite-variance height/walk coupling, uniformly
at every depth-first vertex. Only the stated second moment is used. -/
theorem CriticalEvenOffspring.uniform_height_error_limit (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real {d | ∃ j<2*n+1,
      ε*Real.sqrt ((2*n+1:ℕ):ℝ)< |(walk d.val j:ℝ)-(p.variance/2)*height d.val j|})
      atTop (𝓝 0) := by
  obtain ⟨c,ρ,hc,hρ,hρ1,hmod⟩ := p.code_height_modulus_bound
  let ν := p.variance/2
  have hν : 0<ν := half_pos p.variance_pos
  let κ := ε/(8*ν)
  have hκ : 0<κ := div_pos hε (by positivity)
  have hκeq : ν*κ=ε/8 := by dsimp [κ]; field_simp
  let θ := min (ε/(4*p.sigma)) (c*κ/(2*p.sigma))
  have hσ := p.sigma_pos
  have hθ : 0<θ := lt_min (div_pos hε (by positivity)) (div_pos (mul_pos hc hκ) (by positivity))
  have hθε : θ*p.sigma ≤ ε/4 := by
    calc
      _ ≤ (ε/(4*p.sigma))*p.sigma := mul_le_mul_of_nonneg_right (min_le_left _ _) hσ.le
      _ = _ := by field_simp
  have hθc : θ*p.sigma ≤ c*κ/2 := by
    calc
      _ ≤ (c*κ/(2*p.sigma))*p.sigma := mul_le_mul_of_nonneg_right (min_le_right _ _) hσ.le
      _ = _ := by field_simp
  have hgeo := p.code_geometric_vanish hκ hρ.le hρ1
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  intro η hη
  obtain ⟨δ₀,hδ₀,hwalk⟩ := continuousPath_modulus_tight (p.codeWalk_converges hB)
    (fun _ => measurable_of_countable _) hθ (by positivity : 0<η/3)
  let δ := min δ₀ 1
  have hδ : 0<δ := lt_min hδ₀ (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hmean := (p.average_height_error_limit (by positivity : 0<ε/4)).div_const (δ/2)
  simp only [zero_div] at hmean
  have hlargeν : ∀ᶠ n in atTop, ν ≤ ε/8*Real.sqrt ((2*n+1:ℕ):ℝ) :=
    (odd_sqrt_tendsto.const_mul_atTop (by positivity : 0<ε/8)).eventually_ge_atTop ν
  have hlarger : ∀ᶠ n in atTop, 2 ≤ δ*((2*n+1:ℕ):ℝ) :=
    ((tendsto_natCast_atTop_atTop.comp odd_size_tendsto).const_mul_atTop hδ).eventually_ge_atTop 2
  filter_upwards [hwalk,hlargeν,hlarger,
    hgeo.eventually (gt_mem_nhds (by positivity : (0:ℝ)<η/3)),
    hmean.eventually (gt_mem_nhds (by positivity : (0:ℝ)<η/3))] with n hwn hνn hrn hgn han
  let N := 2*n+1
  let s := Real.sqrt (N:ℝ)
  let m := ⌈κ*s⌉₊
  let r := ⌊δ*N⌋₊
  have hN : 0<N := by dsimp [N]; omega
  have hs : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hmν : ν*m ≤ ε/4*s := by
    have hm := (Nat.ceil_lt_add_one (mul_nonneg hκ.le hs.le)).le
    have hh := mul_le_mul_of_nonneg_left hm hν.le
    have he := congrArg (fun t : ℝ => t*s) hκeq
    change ν ≤ ε/8*s at hνn
    dsimp [m]
    nlinarith
  have hcm : θ*(p.sigma*s) < c*m := by
    have hm : κ*s ≤ (m:ℝ) := Nat.le_ceil _
    have hh := mul_le_mul_of_nonneg_left hm hc.le
    have hth := mul_le_mul_of_nonneg_right hθc hs.le
    have hcs : 0 < c*κ*s := by positivity
    nlinarith
  have hθεs : θ*(p.sigma*s) ≤ ε/4*s := by nlinarith [mul_le_mul_of_nonneg_right hθε hs.le]
  have hr := floor_fraction_bounds hδ hδ1 hN hrn
  let A := {d : Code N | θ<pathOscillation δ₀ (walkPolygon p.sigma d.val)}
  let C := codeHeightModulusFailure m (c*m) (N := N)
  let D := {d : Code N | δ/2 ≤ badHeightFraction ν (ε/4*s) d}
  have hsub : {d : Code N | ∃ j<N, ε*s< |(walk d.val j:ℝ)-ν*height d.val j|} ⊆ (A ∪ C) ∪ D := by
    intro d hd
    by_contra hn
    have hh : ¬d∈A ∧ ¬d∈C ∧ ¬d∈D := by simpa only [Set.mem_union,not_or,and_assoc] using hn
    have hw : pathOscillation δ₀ (walkPolygon p.sigma d.val) ≤ θ := not_lt.mp hh.1
    have havg : badHeightFraction ν (ε/4*s) d < (r:ℝ)/(N:ℝ) :=
      (lt_of_not_ge hh.2.2).trans_le hr.2.2
    have hu := uniform_error_of_average d hν.le hr.1 hh.2.1
      (walk_grid_oscillation hN p.sigma_pos d (hr.2.1.trans hδδ₀) hw) hcm havg
    obtain ⟨j,hj,hjbad⟩ := hd
    have hjle := hu j hj
    linarith
  have hb := (measureReal_mono (μ := p.codeLaw n) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le (A ∪ C) D).trans (add_le_add (measureReal_union_le A C) le_rfl))
  have hA : (p.codeLaw n).real A ≤ η/3 := hwn
  have hC : (p.codeLaw n).real C < η/3 := (hmod n m).trans_lt hgn
  have hD : (p.codeLaw n).real D < η/3 :=
    (p.bad_fraction_markov n ν (ε/4*s) (half_pos hδ)).trans_lt han
  exact hb.trans_lt (by linarith)

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

/-- Converging together with varying sample spaces and actual probability laws. -/
theorem tendstoInDistribution_of_close {E Ω' : Type*} {Ω : ℕ → Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n, Measure (Ω n)} {ν : Measure Ω'} [∀ n, IsProbabilityMeasure (μ n)]
    [IsProbabilityMeasure ν] {X Y : ∀ n, Ω n → E} {Z : Ω' → E}
    (hXZ : TendstoInDistribution X atTop Z μ ν)
    (hY : ∀ n, AEMeasurable (Y n) (μ n))
    (hclose : ∀ ε>0, Tendsto (fun n => (μ n).real {ω | ε < dist (X n ω) (Y n ω)}) atTop (𝓝 0)) :
    TendstoInDistribution Y atTop Z μ ν := by
  refine ⟨hY,hXZ.aemeasurable_limit,?_⟩
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F ⟨M,hM⟩ ⟨L,hL⟩
  have hZ := hXZ.aemeasurable_limit
  have hmid := tendsto_iff_forall_lipschitz_integral_tendsto.mp hXZ.tendsto F ⟨M,hM⟩ ⟨L,hL⟩
  change Tendsto (fun n => ∫ x,F x ∂(μ n).map (Y n)) atTop (𝓝 (∫ x,F x ∂ν.map Z))
  change Tendsto (fun n => ∫ x,F x ∂(μ n).map (X n)) atTop (𝓝 (∫ x,F x ∂ν.map Z)) at hmid
  simp_rw [integral_map (hY _) hL.continuous.aestronglyMeasurable,
    integral_map hZ hL.continuous.aestronglyMeasurable]
  simp_rw [integral_map (hXZ.forall_aemeasurable _) hL.continuous.aestronglyMeasurable,
    integral_map hZ hL.continuous.aestronglyMeasurable] at hmid
  have hM0 : 0≤M := by
    obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure ν
    simpa using hM (Z ω) (Z ω)
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/(4*((L:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hLd : (L:ℝ)*δ ≤ ε/4 := by
    dsimp [δ]; rw [← mul_div_assoc,div_le_iff₀ (by positivity : 0<4*((L:ℝ)+1))]
    nlinarith [L.coe_nonneg]
  have htail := (hclose (δ/2) (half_pos hδ)).const_mul M
  simp only [mul_zero] at htail
  filter_upwards [htail.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/4)),
    (Metric.tendsto_nhds.mp hmid) (ε/4) (by positivity)] with n hn hnmid
  have he := integral_lipschitz_approx_bound (hY n) (hXZ.forall_aemeasurable n) hM hL hδ.le
  have hs : (μ n).real {ω | δ ≤ dist (Y n ω) (X n ω)} ≤
      (μ n).real {ω | δ/2 < dist (X n ω) (Y n ω)} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω
    change δ ≤ dist (Y n ω) (X n ω) at hω
    change δ/2 < dist (X n ω) (Y n ω)
    rw [dist_comm] at hω
    exact lt_of_lt_of_le (by linarith) hω
  have hh := mul_le_mul_of_nonneg_left hs hM0
  have ht := abs_sub_le (∫ ω,F (Y n ω) ∂μ n) (∫ ω,F (X n ω) ∂μ n) (∫ ω,F (Z ω) ∂ν)
  rw [Real.dist_eq] at hnmid ⊢
  linarith

lemma diagonalPath_lipschitz : LipschitzWith 1 diagonalPath := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one,one_mul]
  apply (ContinuousMap.dist_le (dist_nonneg)).mpr
  intro t
  change max (dist (f t) (g t)) (dist (f t) (g t)) ≤ dist f g
  simpa only [max_self] using ContinuousMap.dist_apply_le_dist (f := f) (g := g) t

lemma jointCode_close {N : ℕ} (hN : 0<N) (p : CriticalEvenOffspring) (d : Code N)
    {ε : ℝ} (hε : 0≤ε)
    (h : ∀ j≤N, |(walk d.val j:ℝ)-(p.variance/2)*height d.val j| ≤ ε*p.sigma*Real.sqrt N) :
    dist (diagonalPath (walkPolygon p.sigma d.val)) (jointCode p.sigma d) ≤ ε := by
  have hs := p.sigma_pos
  have hsqrt : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hsq : p.sigma^2=p.variance := Real.sq_sqrt p.variance_pos.le
  have hb := interpolation_diff_bound N
    (fun i => (walk d.val i.val:ℝ)/(p.sigma*Real.sqrt N))
    (fun i => p.sigma*height d.val i.val/(2*Real.sqrt N)) hε (fun i => ?_)
  · apply (ContinuousMap.dist_le hε).mpr
    intro t
    change max (dist (walkPolygon p.sigma d.val t) (walkPolygon p.sigma d.val t))
      (dist (walkPolygon p.sigma d.val t)
        (interpolation N (fun i => p.sigma*height d.val i.val/(2*Real.sqrt N)) t)) ≤ ε
    rw [dist_self,max_eq_right (dist_nonneg)]
    exact (ContinuousMap.dist_apply_le_dist t).trans (by simpa only [walkPolygon,dist_eq_norm] using hb)
  have he : (walk d.val i.val:ℝ)/(p.sigma*Real.sqrt N)-
      p.sigma*height d.val i.val/(2*Real.sqrt N) =
      ((walk d.val i.val:ℝ)-(p.variance/2)*height d.val i.val)/(p.sigma*Real.sqrt N) := by
    field_simp
    nlinarith [congrArg (fun x : ℝ => x*(height d.val i.val:ℝ)) hsq]
  rw [he,abs_div,abs_of_pos (mul_pos hs hsqrt)]
  apply (div_le_iff₀ (mul_pos hs hsqrt)).mpr
  simpa only [mul_assoc] using h i.val (Nat.le_of_lt_succ i.isLt)

lemma CriticalEvenOffspring.joint_diagonal_close (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun n => (p.codeLaw n).real {d | ε <
      dist (diagonalPath (walkPolygon p.sigma d.val)) (jointCode p.sigma d)}) atTop (𝓝 0) := by
  have hsmall := p.uniform_height_error_limit hB (mul_pos hε p.sigma_pos)
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hsmall
  have hlarge : ∀ᶠ n in atTop, 1 ≤ (ε*p.sigma)*Real.sqrt ((2*n+1:ℕ):ℝ) :=
    (odd_sqrt_tendsto.const_mul_atTop (mul_pos hε p.sigma_pos)).eventually_ge_atTop 1
  filter_upwards [hlarge] with n hn
  apply measureReal_mono _ (measure_ne_top _ _)
  intro d hd
  by_contra hh
  have he : ∀ j<2*n+1, |(walk d.val j:ℝ)-(p.variance/2)*height d.val j| ≤
      (ε*p.sigma)*Real.sqrt ((2*n+1:ℕ):ℝ) := by simpa only [Set.mem_ofPred_eq,not_exists,not_and,not_lt] using hh
  apply not_lt_of_ge (jointCode_close (by omega) p d hε.le (fun j hj => ?_)) hd
  by_cases hj' : j<2*n+1
  · exact he j hj'
  · have hjj : j=2*n+1 := by omega
    subst j
    simpa only [d.property.1,height_terminal,Nat.cast_zero,mul_zero,sub_zero,Int.cast_neg,
      Int.cast_one,abs_neg,abs_one] using hn

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_12_r574da1_1 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩
attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitIntervalProd_solutions
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitIntervalProd_solutions
/-- Full joint walk/height convergence to the same Vervaat bridge excursion.
Identification with the standard Bessel3 excursion uses its finite-dimensional laws. -/
theorem CriticalEvenOffspring.jointCode_vervaat_CLT_oai (p : CriticalEvenOffspring)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    TendstoInDistribution (fun n (d : Code (2*n+1)) => jointCode p.sigma d) atTop
      (fun ω => diagonalPath (vervaat (bridgePath B ω))) p.codeLaw P := by
  have hc := (p.codeWalk_converges hB).continuous_comp diagonalPath_lipschitz.continuous
  exact tendstoInDistribution_of_close hc (fun _ => (measurable_of_countable _).aemeasurable)
    (fun _ hε => p.joint_diagonal_close hB hε)

end FKCRT.TreeCoding
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.FKCRT.TreeCoding.CriticalEvenOffspring.jointCode_vervaat_CLT_oai.{u_1} := @OAI.FKCRT.TreeCoding.CriticalEvenOffspring.jointCode_vervaat_CLT_oai.{u_1}
