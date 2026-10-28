-- Prove2me | solution 1 for OAI.FKCRT.Inventory.actualHeight_CLT
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T18:38:01.735902+00:00
-- url     : https://prove2.me/submissions/e7e01329-11ed-489f-83db-56240e11569f

import Mathlib
import Definitions.Def_FKCRT
import Definitions.Def_OAIQ021F004
import Theorems.Thm_OAI_FKCRT_TreeCoding_CriticalEvenOffspring_jointCode_vervaat_CLT

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

lemma CriticalEvenOffspring.code_integral (p : CriticalEvenOffspring) (n : ℕ)
    (F : Code (2*n+1) → ℝ) :
    (∫ d,F d ∂p.codeLaw n)=∑ d : Code (2*n+1), (codeWeight p d/codePartition p (2*n+1))*F d := by
  rw [codeLaw,integral_map (measurable_of_countable (arrayTree n)).aemeasurable
    (measurable_of_countable F).aestronglyMeasurable]
  exact p.arrayTree_expectation n F

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

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SimpleWalk
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma arrayWalk_codeEmbedding {N : ℕ} (d : Code N) (k : ℕ) :
    arrayWalk (codeEmbedding N d) k=walk d.val k := rfl

lemma arrayGood_range (N : ℕ) : {d : Fin N → ℕ | ArrayGood d}=Set.range (codeEmbedding N) := by
  ext d
  constructor
  · rintro ⟨hd,hpos⟩
    obtain ⟨b,hb⟩ := Set.mem_range.mp (show d∈Set.range (bridgeEmbedding N) from by
      rw [← totalStep_bridge_range]; exact hd)
    have hcode : IsTreeCode b.val := ⟨b.property,by
      intro k hk
      change 0≤arrayWalk (bridgeEmbedding N b) k
      rw [hb]
      exact hpos k hk⟩
    exact ⟨⟨b.val,hcode⟩,hb⟩
  · rintro ⟨d,rfl⟩
    exact ⟨totalStep_bridge ⟨d.val,d.property.1⟩,d.property.2⟩

/-- The actual good-array restriction is the weighted finite code sum. -/
lemma CriticalEvenOffspring.iid_good_integral (p : CriticalEvenOffspring) (N : ℕ)
    (F : (Fin N → ℕ) → ℝ) :
    (∫ d,if ArrayGood d then F d else 0 ∂p.iidLaw N)=
      ∑ d : Code N,codeWeight p d*F (codeEmbedding N d) := by
  let G : Code N → (Fin N → ℕ) → ℝ := fun c =>
    ({codeEmbedding N c} : Set (Fin N → ℕ)).indicator (fun _ => F (codeEmbedding N c))
  have hi (c : Code N) : Integrable (G c) (p.iidLaw N) :=
    (integrable_const _).indicator (measurableSet_singleton _)
  have he : (fun d => if ArrayGood d then F d else 0)=fun d => ∑ c : Code N,G c d := by
    funext d
    by_cases hd : ArrayGood d
    · obtain ⟨c,rfl⟩ := Set.mem_range.mp (show d∈Set.range (codeEmbedding N) from by
        rw [← arrayGood_range]; exact hd)
      rw [ite_eq_left hd,Finset.sum_eq_single c]
      · simp [G]
      · intro b _ hbc
        have hnot : codeEmbedding N c≠codeEmbedding N b := fun h => hbc ((codeEmbedding N).injective h.symm)
        simp [G,hnot]
      · simp
    · rw [ite_eq_right hd]
      symm
      apply Finset.sum_eq_zero
      intro c _
      have hn : d≠codeEmbedding N c := by
        intro he
        apply hd
        rw [← Set.mem_ofPred_eq (p := ArrayGood),arrayGood_range]
        exact ⟨c,he.symm⟩
      simp [G,hn]
  rw [he,integral_finsetSum _ (fun c _ => hi c)]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [G]
  rw [integral_indicator (measurableSet_singleton _),setIntegral_const,smul_eq_mul]
  rw [show (p.iidLaw N).real {codeEmbedding N c}=codeWeight p c from
    p.iid_bridge_singleton ⟨c.val,c.property.1⟩]

/-- No informal conditioning is used: finite code expectations are exactly
normalized restriction of the iid offspring law to the good event. -/
theorem CriticalEvenOffspring.code_iid_integral (p : CriticalEvenOffspring) (n : ℕ)
    (F : (Fin (2*n+1) → ℕ) → ℝ) :
    (∫ c,F (codeEmbedding (2*n+1) c) ∂p.codeLaw n)=
      (∫ d,if ArrayGood d then F d else 0 ∂p.iidLaw (2*n+1))/codePartition p (2*n+1) := by
  rw [p.code_integral,p.iid_good_integral,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma arrayWalk_binaryArray {N : ℕ} (d : SimpleWalk.Path N) (k : ℕ) :
    arrayWalk (binaryArray d) k=SimpleWalk.pathSum d k := by
  simp [arrayWalk,binaryArray,binaryStep,SimpleWalk.pathSum]

lemma binaryArray_good {N : ℕ} (d : SimpleWalk.Path N) : ArrayGood (binaryArray d)↔SimpleExcursion d := by
  simp only [ArrayGood,SimpleExcursion,binaryArray_totalStep,arrayWalk_binaryArray]

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

/-- Cutting a first-hitting path at a specified nonnegative intermediate level. -/
lemma firstHit_append_middle {n m : ℕ} (a b : ℕ) (d : Path n) (e : Path m) :
    (firstHit a (Fin.append d e) ∧ (a:ℤ)+pathSum d n=b)↔
      (nonnegativePath a d ∧ (a:ℤ)+pathSum d n=b) ∧ firstHit b e := by
  constructor
  · rintro ⟨⟨hend,hpos⟩,hb⟩
    have hd : nonnegativePath a d := by
      intro k hk
      by_cases he : k=n
      · subst k; omega
      · have hh := hpos k (by omega)
        rwa [pathSum_append_left d e hk] at hh
    refine ⟨⟨hd,hb⟩,?_,?_⟩
    · rw [pathSum_append_right] at hend
      linarith
    · intro k hk
      have hh := hpos (n+k) (by omega)
      rw [pathSum_append_right] at hh
      linarith
  · rintro ⟨⟨hd,hb⟩,hend,hpos⟩
    refine ⟨⟨?_,?_⟩,hb⟩
    · rw [pathSum_append_right]; linarith
    · intro k hk
      by_cases hkn : k≤n
      · rw [pathSum_append_left d e hkn]; exact hd k hkn
      · have hke : k=n+(k-n) := by omega
        rw [hke,pathSum_append_right]
        have hh := hpos (k-n) (by omega)
        linarith

lemma traceExcursion_iff (a R : ℕ) (xs : List (ℕ×ℕ)) (d : Path (traceSize R xs)) :
    traceExcursion a R xs d↔firstHit a d ∧ tracePoints a R xs d := by
  induction xs generalizing a with
  | nil => simp only [traceExcursion,tracePoints,and_true]
  | cons x xs ih =>
    obtain ⟨⟨d,e⟩,rfl⟩ := (splitPathAt x.1 (traceSize R xs)).symm.surjective d
    simp only [traceExcursion,tracePoints,Equiv.apply_symm_apply,ih]
    change ((nonnegativePath a d ∧ (a:ℤ)+pathSum d x.1=x.2) ∧ firstHit x.2 e ∧
        tracePoints x.2 R xs e)↔
      firstHit a (Fin.append d e) ∧ ((a:ℤ)+pathSum d x.1=x.2) ∧ tracePoints x.2 R xs e
    have hh := firstHit_append_middle a x.2 d e
    tauto

/-- Actual nonnegative first-hitting finite-dimensional probabilities have the
reflected-kernel product, with the exact terminal first-hitting factor. -/
theorem pathMass_traceExcursion (a R : ℕ) (xs : List (ℕ×ℕ)) :
    pathMass (traceSize R xs) (traceExcursion a R xs)=traceKilledWeight a R xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    change pathMass (x.1+traceSize R xs) (fun d =>
      (nonnegativePath a (splitPathAt x.1 (traceSize R xs) d).1 ∧
      (a:ℤ)+pathSum (splitPathAt x.1 (traceSize R xs) d).1 x.1=x.2) ∧
      traceExcursion x.2 R xs (splitPathAt x.1 (traceSize R xs) d).2)=_
    rw [pathMass_append x.1 (traceSize R xs)
      (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d x.1=x.2)
      (traceExcursion x.2 R xs),pathMass_killed,ih]
    rfl

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding
attribute [local instance] Classical.propDecidable

lemma firstHit_zero_iff {N : ℕ} (d : Path N) : firstHit 0 d↔SimpleExcursion d := by
  simp [firstHit,SimpleExcursion]

lemma excursionLaw_real (n : ℕ) (A : Set (Path (2*n+1))) :
    (excursionLaw n).real A=
      pathMass (2*n+1) (fun d => firstHit 0 d ∧ d∈A)/pathMass (2*n+1) (firstHit 0) := by
  rw [measureReal_def,excursionLaw,cond_apply ((Set.to_countable _).measurableSet),
    ENNReal.toReal_mul,ENNReal.toReal_inv]
  change ((uniformLaw (2*n+1)).real {d | firstHit 0 d})⁻¹ *
    (uniformLaw (2*n+1)).real ({d | firstHit 0 d}∩A)=_
  rw [uniformLaw_real,uniformLaw_real]
  simp only [mem_inter_iff,mem_ofPred_eq,div_eq_mul_inv,mul_comm]

lemma excursionLaw_ae (n : ℕ) : ∀ᵐ d ∂excursionLaw n,firstHit 0 d :=
  ae_cond_mem₀ ((Set.to_countable _).measurableSet.nullMeasurableSet)

lemma excursionLaw_integral (n : ℕ) (F : Path (2*n+1) → ℝ) :
    (∫ d,F d ∂excursionLaw n)=
      (∫ d,if firstHit 0 d then F d else 0 ∂uniformLaw (2*n+1))/
        pathMass (2*n+1) (firstHit 0) := by
  rw [excursionLaw,TreeCoding.integral_cond_eq_div _ _ ((Set.to_countable _).measurableSet),uniformLaw_real]
  rfl

lemma binary_code_integral (n : ℕ) (F : (Fin (2*n+1) → ℕ) → ℝ) :
    (∫ c,F (codeEmbedding (2*n+1) c) ∂binaryOffspring.codeLaw n)=
      ∫ d,F (binaryArray d) ∂excursionLaw n := by
  rw [binaryOffspring.code_iid_integral,excursionLaw_integral]
  have hn : codePartition binaryOffspring (2*n+1)=pathMass (2*n+1) (firstHit 0) := by
    rw [binary_partition,firstHit_formula]
    norm_num only [Nat.cast_zero,Int.natCast_zero,zero_add,one_mul]
    rw [← kernel_symm (2*n+1) 1]
    push_cast
    ring
  rw [hn,← (binaryArray_preserving (2*n+1)).map_eq,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with d
  simp only [binaryArray_good,← firstHit_zero_iff]

lemma pathSum_parity {N : ℕ} (d : Path N) {k : ℕ} (hk : k≤N) :
    Even (pathSum d k-(k:ℤ)) := by
  induction N generalizing k with
  | zero =>
    have : k=0 := by omega
    subst k
    simp
  | succ N ih =>
    cases k with
    | zero => simp
    | succ k =>
      have he : d=Fin.cons (d 0) (Fin.tail d) := (Fin.cons_self_tail d).symm
      rw [he,pathSum_cons]
      have hh := ih (Fin.tail d) (by omega : k≤N)
      have hs : Even (sign (d 0)-1) := by cases d 0 <;> norm_num [sign]
      have heq : sign (d 0)+pathSum (Fin.tail d) k-((k+1:ℕ):ℤ)=
          (sign (d 0)-1)+(pathSum (Fin.tail d) k-(k:ℤ)) := by push_cast; ring
      rw [heq]
      exact hs.add hh

end FKCRT.SimpleWalk
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Histogram
variable {ι : Type*} [Fintype ι]

lemma mem_cube_dist {δ : ℝ} {a x : ι → ℝ} (hδ : 0≤δ) (hx : x∈cube δ a) : dist x a≤δ := by
  apply (dist_pi_le_iff hδ).mpr
  intro i
  have hi := hx i (mem_univ i)
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩

lemma boxLaw_dist {δ : ℝ} (hδ : 0≤δ) (a : ι → ℝ) :
    ∀ᵐ x ∂boxLaw δ a, dist x a≤δ := by
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem (measurableSet_cube δ a)] with x hx
  exact mem_cube_dist hδ hx

end FKCRT.Histogram
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Histogram
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

omit [MeasurableSingletonClass Ω] in
lemma measurable_density (μ : Measure Ω) (φ : Ω → ι → ℝ) (δ : ℝ) :
    Measurable (density μ φ δ) := by
  apply Finset.measurable_sum
  intro ω hω
  exact measurable_const.mul (measurable_const.indicator (measurableSet_cube δ (φ ω)))

omit [MeasurableSingletonClass Ω] in
lemma integral_mixture (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : Ω → ι → ℝ) {δ : ℝ} (hδ : 0<δ) (F : BoundedContinuousFunction (ι → ℝ) ℝ) :
    (∫ x,F x ∂mixture μ φ δ)=∑ ω,(μ {ω}).toReal * ∫ x,F x ∂boxLaw δ (φ ω) := by
  have (ω : Ω) : IsProbabilityMeasure (boxLaw δ (φ ω)) := boxLaw_probability hδ (φ ω)
  have hi (ω : Ω) : Integrable F (μ {ω} • boxLaw δ (φ ω)) := by
    exact (F.integrable (boxLaw δ (φ ω))).smul_measure (measure_ne_top _ _)
  rw [mixture,integral_finsetSum_measure (fun ω _ => hi ω)]
  simp only [integral_smul_measure,smul_eq_mul]

lemma box_integral_lipschitz {δ : ℝ} (hδ : 0<δ) (a : ι → ℝ)
    (F : BoundedContinuousFunction (ι → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    |(∫ x,F x ∂boxLaw δ a)-F a|≤L*δ := by
  have := boxLaw_probability hδ a
  have hconst : (∫ x,F a ∂boxLaw δ a)=F a := by simp
  rw [← hconst,← integral_sub (F.integrable _) (integrable_const _)]
  apply abs_integral_le_integral_abs.trans
  calc
    (∫ x,|F x-F a| ∂boxLaw δ a) ≤ ∫ x,(L:ℝ)*δ ∂boxLaw δ a := by
      apply integral_mono_ae ((F.integrable _).sub (integrable_const _)).abs (integrable_const _)
      filter_upwards [boxLaw_dist hδ.le a] with x hx
      exact (hF.dist_le_mul x a).trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
    _ = _ := by simp

lemma integral_mixture_close (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : Ω → ι → ℝ) {δ : ℝ} (hδ : 0<δ)
    (F : BoundedContinuousFunction (ι → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    |(∫ x,F x ∂mixture μ φ δ)-(∫ ω,F (φ ω) ∂μ)|≤L*δ := by
  have hi : Integrable (fun ω => F (φ ω)) μ := Integrable.of_finite
  rw [integral_mixture μ φ hδ F,integral_fintype hi,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ ω,|(μ {ω}).toReal * (∫ x,F x ∂boxLaw δ (φ ω)) - μ.real {ω} • F (φ ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω,(μ {ω}).toReal*((L:ℝ)*δ) := by
      apply Finset.sum_le_sum
      intro ω _
      rw [smul_eq_mul,measureReal_def,← mul_sub,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left (box_integral_lipschitz hδ (φ ω) F hF) ENNReal.toReal_nonneg
    _ = _ := by
      rw [← Finset.sum_mul,← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _),
        sum_measure_singleton,Finset.coe_univ,measure_univ,ENNReal.toReal_one,one_mul]

end FKCRT.Histogram
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Histogram
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [MeasurableSpace Ω]
  [MeasurableSingletonClass Ω]

omit [Fintype ι] in
lemma mem_lattice_cube {δ : ℝ} (hδ : 0<δ) (a : ι → ℕ) {x : ι → ℝ}
    (hx : ∀ i,0≤x i) : x∈cube δ (fun i => δ*(a i:ℝ))↔a=fun i => ⌊x i/δ⌋₊ := by
  constructor
  · intro h
    apply funext
    intro i
    have hi := h i (mem_univ i)
    symm
    apply (Nat.floor_eq_iff (div_nonneg (hx i) hδ.le)).mpr
    constructor
    · exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hi.1)
    · apply (div_lt_iff₀ hδ).mpr
      simpa only [add_mul,mul_add,one_mul,mul_one,mul_comm] using hi.2
  · rintro rfl
    intro i _
    have hfloor := (Nat.floor_eq_iff (div_nonneg (hx i) hδ.le)).mp (rfl : ⌊x i/δ⌋₊=⌊x i/δ⌋₊)
    constructor
    · simpa only [mul_comm] using (le_div_iff₀ hδ).mp hfloor.1
    · simpa only [add_mul,mul_add,one_mul,mul_one,mul_comm] using (div_lt_iff₀ hδ).mp hfloor.2

lemma density_lattice (μ : Measure Ω) (a : Ω → ι → ℕ) {δ : ℝ} (hδ : 0<δ)
    {x : ι → ℝ} (hx : ∀ i,0≤x i) :
    density μ (fun ω i => δ*(a ω i:ℝ)) δ x=
      μ {ω | a ω=fun i => ⌊x i/δ⌋₊}*(ENNReal.ofReal δ ^ Fintype.card ι)⁻¹ := by
  classical
  let s : Finset Ω := Finset.univ.filter (fun ω => a ω=fun i => ⌊x i/δ⌋₊)
  have hset : (s : Set Ω)={ω | a ω=fun i => ⌊x i/δ⌋₊} := by ext ω; simp [s]
  rw [density,← hset,← sum_measure_singleton,Finset.sum_mul]
  simp only [s,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : a ω=fun i => ⌊x i/δ⌋₊
  · rw [ite_eq_left h,indicator_of_mem ((mem_lattice_cube hδ _ hx).mpr h)]
  · rw [ite_eq_right h,indicator_of_notMem (mt (mem_lattice_cube hδ _ hx).mp h),mul_zero]

omit [MeasurableSingletonClass Ω] in
lemma density_lattice_negative (μ : Measure Ω) (a : Ω → ι → ℕ) {δ : ℝ}
    (hδ : 0≤δ) {x : ι → ℝ} (hx : ∃ i,x i<0) :
    density μ (fun ω i => δ*(a ω i:ℝ)) δ x=0 := by
  obtain ⟨i,hi⟩ := hx
  apply Finset.sum_eq_zero
  intro ω _
  have hn : x∉cube δ (fun i => δ*(a ω i:ℝ)) := by
    intro h
    have hh := (h i (mem_univ i)).1
    have hz : 0≤δ*(a ω i:ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
    linarith
  rw [indicator_of_notMem hn,mul_zero]

lemma floor_mesh_tendsto {δ : ℕ → ℝ} (hδ : ∀ n,0<δ n)
    (hlim : Tendsto δ atTop (𝓝 0)) {x : ℝ} (hx : 0≤x) :
    Tendsto (fun n => δ n*(⌊x/δ n⌋₊:ℝ)) atTop (𝓝 x) := by
  have hl (n : ℕ) := Nat.floor_le (div_nonneg hx (hδ n).le)
  have hu (n : ℕ) := Nat.lt_floor_add_one (x/δ n)
  have hlow : Tendsto (fun n => x-δ n) atTop (𝓝 x) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro n
    have h := (div_lt_iff₀ (hδ n)).mp (hu n)
    nlinarith
  · intro n
    simpa only [mul_comm] using (le_div_iff₀ (hδ n)).mp (hl n)

end FKCRT.Histogram
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

lemma tracePoints_observed (a R : ℕ) (xs : List (ℕ×ℕ)) (d : Path (traceSize R xs)) :
    tracePoints a R xs d↔observed a xs d := by
  induction xs generalizing a with
  | nil => simp [tracePoints,observed,located]
  | cons x xs ih =>
    obtain ⟨⟨d,e⟩,rfl⟩ := (splitPathAt x.1 (traceSize R xs)).symm.surjective d
    simp only [tracePoints,Equiv.apply_symm_apply,ih,observed,located,List.mem_cons,
      List.mem_map,forall_eq_or_imp,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]
    change ((a:ℤ)+pathSum d x.1=x.2 ∧
      ∀ y∈located xs,(x.2:ℤ)+pathSum e y.1=y.2)↔
      ((a:ℤ)+pathSum (Fin.append d e) x.1=x.2 ∧
      ∀ y∈located xs,(a:ℤ)+pathSum (Fin.append d e) (x.1+y.1)=y.2)
    simp only [pathSum_append_left d e le_rfl,pathSum_append_right]
    constructor <;> rintro ⟨hx,hxs⟩ <;> refine ⟨hx,?_⟩ <;> intro y hy
    · have h := hxs y hy; linarith
    · have h := hxs y hy; linarith

lemma pathMass_firstHit_observed (a R : ℕ) (xs : List (ℕ×ℕ)) :
    pathMass (traceSize R xs) (fun d => firstHit a d ∧ observed a xs d)=
      traceKilledWeight a R xs := by
  rw [← pathMass_traceExcursion]
  apply pathMass_congr
  intro d
  rw [traceExcursion_iff,tracePoints_observed]

lemma traceSize_eq_sum (R : ℕ) (xs : List (ℕ×ℕ)) :
    traceSize R xs=(xs.map Prod.fst).sum+R := by
  induction xs with
  | nil => simp [traceSize]
  | cons x xs ih => simp [traceSize,ih,Nat.add_assoc]

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma even_evenGrid (n : ℕ) (t : ℝ) : Even (evenGrid n t) := even_two_mul _

lemma evenGrid_mono (n : ℕ) {s t : ℝ} (h : s≤t) : evenGrid n s≤evenGrid n t := by
  unfold evenGrid
  exact Nat.mul_le_mul_left _ (Nat.floor_mono (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)) (by norm_num)))

lemma evenGrid_le (n : ℕ) {t : ℝ} (ht : t≤1) : evenGrid n t≤2*n := by
  have h : ((2*n+1:ℕ):ℝ)*t/2<(n:ℝ)+1 := by
    have he := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (2*n+1) : (0:ℝ)≤(2*n+1:ℕ))
    push_cast at he ⊢
    linarith
  have hh : ⌊((2*n+1:ℕ):ℝ)*t/2⌋₊≤n := (Nat.floor_lt' (by omega : n+1≠0)).mpr
    (by exact_mod_cast h) |> Nat.le_of_lt_succ
  exact Nat.mul_le_mul_left 2 hh

lemma evenGrid_error (n : ℕ) {t : ℝ} (ht : 0≤t) :
    0≤((2*n+1:ℕ):ℝ)*t-(evenGrid n t:ℝ) ∧
    ((2*n+1:ℕ):ℝ)*t-(evenGrid n t:ℝ)<2 := by
  have hnonneg : 0≤((2*n+1:ℕ):ℝ)*t/2 := by positivity
  have hl := Nat.floor_le hnonneg
  have hu := Nat.lt_floor_add_one (((2*n+1:ℕ):ℝ)*t/2)
  unfold evenGrid
  push_cast at hl hu ⊢
  constructor <;> linarith

lemma evenGrid_ratio (t : ℝ) (ht : 0≤t) :
    Tendsto (fun n => (evenGrid n t:ℝ)/((2*n+1:ℕ):ℝ)) atTop (𝓝 t) := by
  have hN : Tendsto (fun n : ℕ => ((2*n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun n => by show n≤2*n+1; omega) tendsto_id)
  have hzero : Tendsto (fun n => (2:ℝ)/((2*n+1:ℕ):ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have hl : Tendsto (fun n => t-2/((2*n+1:ℕ):ℝ)) atTop (𝓝 t) := by
    simpa using tendsto_const_nhds.sub hzero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro n
    have hpos : 0<((2*n+1:ℕ):ℝ) := by positivity
    have he := (evenGrid_error n ht).2
    apply (le_div_iff₀ hpos).mpr
    rw [sub_mul,div_mul_cancel₀ _ hpos.ne']
    linarith
  · intro n
    exact (div_le_iff₀ (by positivity : 0<((2*n+1:ℕ):ℝ))).mpr
      (by have h := (evenGrid_error n ht).1; linarith)

lemma gridDurations_even {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (n : ℕ) (i : Fin m) : Even (gridDurations u n i) := by
  exact (Nat.even_sub (evenGrid_mono n (hu i.castSucc_lt_succ.le))).mpr
    (iff_of_true (even_evenGrid n _) (even_evenGrid n _))

lemma gridRemainder_even {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ) :
    Even (gridRemainder u n) :=
  (Nat.even_sub (evenGrid_le n (u (Fin.last m)).property.2)).mpr
    (iff_of_true (even_two_mul n) (even_evenGrid n _))

lemma gridDurations_ratio {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (i : Fin m) :
    Tendsto (fun n => (gridDurations u n i:ℝ)/((2*n+1:ℕ):ℝ)) atTop
      (𝓝 ((u i.succ:ℝ)-(u i.castSucc:ℝ))) := by
  have h := (evenGrid_ratio (u i.succ) (u i.succ).property.1).sub
    (evenGrid_ratio (u i.castSucc) (u i.castSucc).property.1)
  apply h.congr'
  exact Filter.Eventually.of_forall (fun n => by
    dsimp only [gridDurations]
    rw [Nat.cast_sub (evenGrid_mono n (hu i.castSucc_lt_succ.le)),sub_div])

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

lemma kernel_local_limit {N : ℕ → ℕ} {z : ℕ → ℤ} {x : ℝ}
    (hN : Tendsto N atTop atTop)
    (hz : ∀ᶠ n in atTop,Even ((N n:ℤ)+z n))
    (hx : Tendsto (fun n => (z n:ℝ)/Real.sqrt (N n:ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n => Real.sqrt (N n:ℝ)*kernel (N n) (z n)) atTop
      (𝓝 ((Real.sqrt (2*Real.pi)/Real.pi)*Real.exp (-x^2/2))) := by
  obtain ⟨E,_hE,hEt,hE⟩ := kernel_uniform_local_limit
  have hmodel := ((Real.continuous_exp.tendsto (-x^2/2)).comp ((hx.pow 2).neg.div_const 2)).const_mul
      (Real.sqrt (2*Real.pi)/Real.pi)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun n => (Real.sqrt (2*Real.pi)/Real.pi)*
      Real.exp (-((z n:ℝ)/Real.sqrt (N n:ℝ))^2/2)-E (N n)) atTop _ by
      simpa using hmodel.sub (hEt.comp hN))
    (show Tendsto (fun n => (Real.sqrt (2*Real.pi)/Real.pi)*
      Real.exp (-((z n:ℝ)/Real.sqrt (N n:ℝ))^2/2)+E (N n)) atTop _ by
      simpa using hmodel.add (hEt.comp hN))
  · filter_upwards [hz,hN.eventually (eventually_gt_atTop 0)] with n hn hnn
    have hh := (abs_le.mp (hE (N n) hnn (z n) hn)).1
    linarith
  · filter_upwards [hz,hN.eventually (eventually_gt_atTop 0)] with n hn hnn
    have hh := (abs_le.mp (hE (N n) hnn (z n) hn)).2
    linarith

lemma sqrt_ratio_tendsto {N T : ℕ → ℕ} {t : ℝ}
    (hr : Tendsto (fun n => (N n:ℝ)/(T n:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun n => Real.sqrt (N n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (Real.sqrt t)) := by
  simpa only [Function.comp_def,Real.sqrt_div (Nat.cast_nonneg _)] using Real.continuous_sqrt.tendsto t |>.comp hr

/-- Kernel limit at arbitrary macroscopic times and spatial lattice sites. -/
theorem kernel_scaled_limit {N T : ℕ → ℕ} {z : ℕ → ℤ} {t x : ℝ}
    (ht : 0<t) (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => (N n:ℝ)/(T n:ℝ)) atTop (𝓝 t))
    (hz : ∀ᶠ n in atTop,Even ((N n:ℤ)+z n))
    (hx : Tendsto (fun n => (z n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)*kernel (N n) (z n)) atTop (𝓝 (2*heat t x)) := by
  have hs := sqrt_ratio_tendsto hr
  have ht' : 0<Real.sqrt t := Real.sqrt_pos.mpr ht
  have hz' : Tendsto (fun n => (z n:ℝ)/Real.sqrt (N n:ℝ)) atTop (𝓝 (x/Real.sqrt t)) := by
    apply (hx.div hs (ne_of_gt ht')).congr'
    filter_upwards [hT.eventually (eventually_gt_atTop 0),hN.eventually (eventually_gt_atTop 0)] with n hn hnn
    have htp : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
    have hnp : Real.sqrt (N n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hnn))
    dsimp only [Pi.div_apply]
    field_simp
  have hc := (kernel_local_limit hN hz hz').div hs (ne_of_gt ht')
  have hm : ((Real.sqrt (2*Real.pi)/Real.pi)*Real.exp (-(x/Real.sqrt t)^2/2))/Real.sqrt t=2*heat t x := by
    rw [heat,div_pow,Real.sq_sqrt ht.le,Real.sqrt_mul (by positivity : 0≤2*Real.pi)]
    have hpi : Real.sqrt (2*Real.pi)^2=2*Real.pi := Real.sq_sqrt (by positivity)
    have hpis : Real.sqrt (2*Real.pi)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have harg : -(x^2/t)/2= -x^2/(2*t) := by ring
    rw [harg]
    field_simp
    nlinarith
  rw [hm] at hc
  apply hc.congr'
  filter_upwards [hN.eventually (eventually_gt_atTop 0),hT.eventually (eventually_gt_atTop 0)] with n hn hnt
  have hnp : Real.sqrt (N n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have htp : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hnt))
  dsimp only [Pi.div_apply]
  field_simp

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma cast_div_sqrt_tendsto_zero {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) (c : ℝ) :
  Tendsto (fun n => c/Real.sqrt (T n:ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp hT))

lemma killed_scaled_limit {N T a b : ℕ → ℕ} {t x y : ℝ}
    (ht : 0<t) (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => (N n:ℝ)/(T n:ℝ)) atTop (𝓝 t))
    (hz : ∀ᶠ n in atTop,Even ((N n:ℤ)+(b n:ℤ)-a n))
    (hx : Tendsto (fun n => (a n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 x))
    (hy : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)*killed (N n) (a n) (b n)) atTop
      (𝓝 (2*killedHeat t x y)) := by
  have hm : Tendsto (fun n => (((b n:ℤ)-a n:ℤ):ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (y-x)) := by
    simpa only [Int.cast_sub,Int.cast_natCast,sub_div] using hy.sub hx
  have hp : Tendsto (fun n => (((b n:ℤ)+a n+2:ℤ):ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (y+x)) := by
    simpa only [Int.cast_add,Int.cast_ofNat,Int.cast_natCast,add_div,add_zero] using
      (hy.add hx).add (cast_div_sqrt_tendsto_zero hT 2)
  have hz1 : ∀ᶠ n in atTop, Even ((N n:ℤ)+((b n:ℤ)-a n)) := by
    filter_upwards [hz] with n hn; convert hn using 1; ring
  have hz2 : ∀ᶠ n in atTop, Even ((N n:ℤ)+((b n:ℤ)+a n+2)) := by
    filter_upwards [hz] with n hn
    have he : (N n:ℤ)+((b n:ℤ)+a n+2)=((N n:ℤ)+b n-a n)+2*((a n:ℤ)+1) := by ring
    rw [he]
    exact hn.add (even_two_mul ((a n:ℤ)+1))
  have h := (kernel_scaled_limit ht hN hT hr hz1 hm).sub (kernel_scaled_limit ht hN hT hr hz2 hp)
  simpa only [killed_reflection,mul_sub,killedHeat] using h

lemma sqrt_div_nat_tendsto_zero {T : ℕ → ℕ} (hT : Tendsto T atTop atTop) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)/(T n:ℝ)) atTop (𝓝 0) := by
  apply (cast_div_sqrt_tendsto_zero hT 1).congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have htp : 0<(T n:ℝ) := by exact_mod_cast hn
  have hsp : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr htp)
  have hs := Real.sq_sqrt htp.le
  field_simp
  nlinarith

lemma entrance_scaled_limit {N T b : ℕ → ℕ} {t y : ℝ}
    (ht : 0<t) (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => (N n:ℝ)/(T n:ℝ)) atTop (𝓝 t))
    (hz : ∀ᶠ n in atTop,Even ((N n:ℤ)+b n))
    (hy : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => (T n:ℝ)*killed (N n) 0 (b n)) atTop (𝓝 (4*y/t*heat t y)) := by
  have hsmall : Tendsto (fun n => (b n:ℝ)/(T n:ℝ)) atTop (𝓝 0) := by
    have h := hy.mul (sqrt_div_nat_tendsto_zero hT)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
    have hs : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
    field_simp
  have hnum : Tendsto (fun n => 2*((b n:ℝ)+1)/Real.sqrt (T n:ℝ)) atTop (𝓝 (2*y)) := by
    simpa only [add_zero,mul_div_assoc,add_div] using (hy.add (cast_div_sqrt_tendsto_zero hT 1)).const_mul 2
  have hden : Tendsto (fun n => ((N n:ℝ)+b n+2)/(T n:ℝ)) atTop (𝓝 t) := by
    simpa only [add_div,add_zero] using (hr.add hsmall).add
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hT) :
        Tendsto (fun n => (2:ℝ)/(T n:ℝ)) atTop (𝓝 0))
  have hk := kernel_scaled_limit ht hN hT hr hz (by simpa only [Int.cast_natCast] using hy)
  have h := (hnum.div hden (ne_of_gt ht)).mul hk
  have hi : 2*y/t*(2*heat t y)=4*y/t*heat t y := by ring
  rw [hi] at h
  apply h.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have htp : (T n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hd : (N n:ℝ)+b n+2≠0 := by positivity
  rw [killed_entrance]
  dsimp only [Pi.mul_apply,Pi.div_apply]
  field_simp

/-- Terminal first-hitting density at macroscopic time. -/
lemma firstHit_scaled_limit {N T b : ℕ → ℕ} {t y : ℝ}
    (ht : 0<t) (hN : Tendsto N atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => ((N n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t))
    (hz : ∀ᶠ n in atTop,Even (((N n+1:ℕ):ℤ)+((b n:ℤ)+1)))
    (hy : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => (T n:ℝ)*pathMass (N n+1) (firstHit (b n))) atTop
      (𝓝 (2*y/t*heat t y)) := by
  have hN' : Tendsto (fun n => N n+1) atTop atTop := tendsto_atTop_mono (fun n => by omega) hN
  have hy' : Tendsto (fun n => (((b n:ℤ)+1:ℤ):ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y) := by
    simpa only [Int.cast_add,Int.cast_one,Int.cast_natCast,add_div,add_zero] using
      hy.add (cast_div_sqrt_tendsto_zero hT 1)
  have hk := kernel_scaled_limit ht hN' hT (by simpa only [Nat.cast_add,Nat.cast_one] using hr) hz hy'
  have hnum : Tendsto (fun n => ((b n:ℝ)+1)/Real.sqrt (T n:ℝ)) atTop (𝓝 y) := by
    simpa only [Int.cast_add,Int.cast_one,Int.cast_natCast] using hy'
  have h := (hnum.div hr (ne_of_gt ht)).mul hk
  have hi : y/t*(2*heat t y)=2*y/t*heat t y := by ring
  rw [hi] at h
  apply h.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have htp : (T n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hd : (N n:ℝ)+1≠0 := by positivity
  rw [firstHit_formula]
  dsimp only [Pi.mul_apply,Pi.div_apply]
  field_simp

end FKCRT.SimpleWalk
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_RadialBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma heat_neg (t r : ℝ) : heat t (-r)=heat t r := by simp [heat]

/-- The elementary Gaussian bridge identity with its exact normalizing constants. -/
lemma heat_bridge {A B : ℝ} (hB : 0<B) (hBA : B<A) (r s : ℝ) :
    heat ((A-B)*B/A) (s-(B/A)*r)*heat A r=heat (A-B) (s-r)*heat B s := by
  have hA : 0<A := hB.trans hBA
  have hd : 0<A-B := sub_pos.mpr hBA
  have hv : 0<(A-B)*B/A := by positivity
  have hden : Real.sqrt (2*Real.pi*((A-B)*B/A))*Real.sqrt (2*Real.pi*A)=
      Real.sqrt (2*Real.pi*(A-B))*Real.sqrt (2*Real.pi*B) := by
    rw [← Real.sqrt_mul (by positivity),← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hexp : -(s-(B/A)*r)^2/(2*((A-B)*B/A))-r^2/(2*A)=
      -(s-r)^2/(2*(A-B))-s^2/(2*B) := by
    field_simp
    ring
  unfold heat
  rw [div_mul_div_comm,div_mul_div_comm,← Real.exp_add,← Real.exp_add,hden]
  congr 1
  congr 1
  simpa only [sub_eq_add_neg,neg_div] using hexp

/-- Gaussian regression and the radial heat transform agree, including radius zero. -/
theorem radialHeat_bridge {A B : ℝ} (hB : 0<B) (hBA : B<A) (r s : ℝ) :
    radialHeat ((A-B)*B/A) ((B/A)*r) s=
      radialHeat (A-B) r s*((A/B)*heat B s/heat A r) := by
  have hA : 0<A := hB.trans hBA
  have hd : 0<A-B := sub_pos.mpr hBA
  have hc : B/A≠0 := div_ne_zero hB.ne' hA.ne'
  have hh : heat A r≠0 := (heat_pos hA r).ne'
  have hminus := heat_bridge hB hBA r s
  have hplus := heat_bridge hB hBA (-r) s
  simp only [heat_neg,mul_neg,sub_neg_eq_add] at hplus
  by_cases hr : r=0
  · subst r
    simp only [mul_zero,radialHeat]
    -- Keep the normalizing Gaussian product rather than squaring any density.
    have he : heat ((A-B)*B/A) s=heat (A-B) s*heat B s/heat A 0 := by
      apply (eq_div_iff (heat_pos hA 0).ne').mpr
      simpa only [mul_zero,sub_zero] using heat_bridge hB hBA 0 s
    change 2*s^2/((A-B)*B/A)*heat ((A-B)*B/A) s=
      (2*s^2/(A-B)*heat (A-B) s)*((A/B)*heat B s/heat A 0)
    rw [he]
    field_simp
  · have hcr : (B/A)*r≠0 := mul_ne_zero hc hr
    simp only [radialHeat,ite_eq_right hcr,ite_eq_right hr,killedHeat]
    apply (mul_right_cancel₀ hh)
    calc
      (s/(B/A*r)*(heat ((A-B)*B/A) (s-(B/A)*r)-heat ((A-B)*B/A) (s+(B/A)*r)))*heat A r
          =s/(B/A*r)*(heat (A-B) (s-r)-heat (A-B) (s+r))*heat B s := by
            calc
              _=s/(B/A*r)*(heat ((A-B)*B/A) (s-(B/A)*r)*heat A r-
                heat ((A-B)*B/A) (s+(B/A)*r)*heat A r) := by ring
              _=_ := by rw [hminus,hplus]; ring
      _=(s/r*(heat (A-B) (s-r)-heat (A-B) (s+r))*((A/B)*heat B s/heat A r))*heat A r := by
        field_simp

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma hitHeat_pos {t x : ℝ} (ht : 0<t) (hx : 0<x) : 0<hitHeat t x :=
  mul_pos (div_pos (mul_pos (by norm_num) hx) ht) (heat_pos ht x)

/-- Positive-radius bridge transition, directly from the reflected kernels and
the terminal ballot factor. -/
lemma conditioned_kernel_limit {J R T a b : ℕ → ℕ} {s t x y : ℝ}
    (hs : 0 < s) (ht : 0<t) (hx : 0<x)
    (hJ : Tendsto J atTop atTop) (hR : Tendsto R atTop atTop)
    (hT : Tendsto T atTop atTop)
    (hrJ : Tendsto (fun n => (J n:ℝ)/(T n:ℝ)) atTop (𝓝 s))
    (hrR : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t))
    (hzJ : ∀ᶠ n in atTop,Even ((J n:ℤ)+(b n:ℤ)-a n))
    (hzR : ∀ᶠ n in atTop,Even (((R n+1:ℕ):ℤ)+((b n:ℤ)+1)))
    (hzA : ∀ᶠ n in atTop,Even (((J n+R n+1:ℕ):ℤ)+((a n:ℤ)+1)))
    (ha : Tendsto (fun n => (a n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 x))
    (hb : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)/2*
      (killed (J n) (a n) (b n)*pathMass (R n+1) (firstHit (b n)) /
        pathMass (J n+R n+1) (firstHit (a n)))) atTop
      (𝓝 (radialHeat (s*t/(s+t)) (t/(s+t)*x) y)) := by
  have hJR : Tendsto (fun n => J n+R n) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) hJ
  have hrJR : Tendsto (fun n => (((J n+R n:ℕ):ℝ)+1)/(T n:ℝ)) atTop (𝓝 (s+t)) := by
    convert hrJ.add hrR using 1; simp [add_div,add_assoc]
  have hk := killed_scaled_limit hs hJ hT hrJ hzJ ha hb
  have hr := firstHit_scaled_limit ht hR hT hrR hzR hb
  have hd := firstHit_scaled_limit (add_pos hs ht) hJR hT hrJR hzA ha
  have hd0 := hitHeat_pos (add_pos hs ht) hx
  have hlimit := ((hk.mul hr).div hd hd0.ne').div_const 2
  have he : ((2*killedHeat s x y)*(2*y/t*heat t y)/(2*x/(s+t)*heat (s+t) x))/2=
      radialHeat (s*t/(s+t)) (t/(s+t)*x) y := by
    have hh := radialHeat_bridge ht (by linarith : t < s+t) x y
    rw [show s+t-t=s by ring] at hh
    rw [hh,radialHeat,ite_eq_right hx.ne']
    field_simp
  rw [he] at hlimit
  apply hlimit.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have hn0 : (T n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  dsimp only [Pi.div_apply,Pi.mul_apply]
  field_simp

lemma firstHit_zero_scaled_limit {D T : ℕ → ℕ} {u : ℝ}
    (hu : 0<u) (hD : Tendsto D atTop atTop) (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => ((D n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 u))
    (hz : ∀ᶠ n in atTop,Even (((D n+1:ℕ):ℤ)+1)) :
    Tendsto (fun n => (T n:ℝ)*Real.sqrt (T n:ℝ)*pathMass (D n+1) (firstHit 0))
      atTop (𝓝 (2/u*heat u 0)) := by
  have hD' : Tendsto (fun n => D n+1) atTop atTop := tendsto_atTop_mono (fun n => by omega) hD
  have hk := kernel_scaled_limit hu hD' hT
    (by simpa only [Nat.cast_add,Nat.cast_one] using hr) hz
    (by simpa only [Int.cast_one] using cast_div_sqrt_tendsto_zero hT 1)
  have hh := hk.div hr hu.ne'
  have he : (2*heat u 0)/u=2/u*heat u 0 := by ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have ht0 : (T n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [firstHit_formula]
  dsimp only [Pi.div_apply]
  norm_num only [Nat.cast_zero,Int.natCast_zero,zero_add]
  field_simp

lemma entrance_conditioned_limit {J R T b : ℕ → ℕ} {s t y : ℝ}
    (hs : 0 < s) (ht : 0<t)
    (hJ : Tendsto J atTop atTop) (hR : Tendsto R atTop atTop)
    (hT : Tendsto T atTop atTop)
    (hrJ : Tendsto (fun n => (J n:ℝ)/(T n:ℝ)) atTop (𝓝 s))
    (hrR : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t))
    (hzJ : ∀ᶠ n in atTop,Even ((J n:ℤ)+(b n:ℤ)))
    (hzR : ∀ᶠ n in atTop,Even (((R n+1:ℕ):ℤ)+((b n:ℤ)+1)))
    (hzA : ∀ᶠ n in atTop,Even (((J n+R n+1:ℕ):ℤ)+1))
    (hb : Tendsto (fun n => (b n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 y)) :
    Tendsto (fun n => Real.sqrt (T n:ℝ)/2*
      (killed (J n) 0 (b n)*pathMass (R n+1) (firstHit (b n)) /
        pathMass (J n+R n+1) (firstHit 0))) atTop
      (𝓝 (radialHeat (s*t/(s+t)) 0 y)) := by
  have hJR : Tendsto (fun n => J n+R n) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) hJ
  have hrJR : Tendsto (fun n => (((J n+R n:ℕ):ℝ)+1)/(T n:ℝ)) atTop (𝓝 (s+t)) := by
    convert hrJ.add hrR using 1; simp [add_div,add_assoc]
  have hk := entrance_scaled_limit hs hJ hT hrJ hzJ hb
  have hr := firstHit_scaled_limit ht hR hT hrR hzR hb
  have hd := firstHit_zero_scaled_limit (add_pos hs ht) hJR hT hrJR hzA
  have hd0 : 0<2/(s+t)*heat (s+t) 0 := mul_pos (div_pos (by norm_num) (add_pos hs ht)) (heat_pos (add_pos hs ht) 0)
  have hlimit := ((hk.mul hr).div hd hd0.ne').div_const 2
  have he : ((4*y/s*heat s y)*(2*y/t*heat t y)/(2/(s+t)*heat (s+t) 0))/2=
      radialHeat (s*t/(s+t)) 0 y := by
    have hh := radialHeat_bridge ht (by linarith : t < s+t) 0 y
    rw [mul_zero,show s+t-t=s by ring] at hh
    rw [hh]
    rw [show radialHeat s 0 y=2*y^2/s*heat s y by simp [radialHeat]]
    field_simp
    ring
  rw [he] at hlimit
  apply hlimit.congr'
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with n hn
  have hn0 : (T n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs0 : Real.sqrt (T n:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hn))
  have hsq := Real.sq_sqrt (show 0≤(T n:ℝ) from Nat.cast_nonneg _)
  dsimp only [Pi.div_apply,Pi.mul_apply]
  field_simp
  rw [hsq]
  ring

end FKCRT.SimpleWalk
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_TraceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

lemma segments_cons {m : ℕ} (d b : Fin (m+1) → ℕ) :
    segments d b=(d 0,b 0)::segments (Fin.tail d) (Fin.tail b) := by
  simp [segments,List.ofFn_succ,Fin.tail_def]

lemma traceSize_segments {m : ℕ} (R : ℕ) (d b : Fin m → ℕ) :
    traceSize R (segments d b)=(∑ i,d i)+R := by
  rw [traceSize_eq_sum]
  simp [segments,List.sum_ofFn]

lemma normalizedTrace_cons {m : ℕ} (a R : ℕ) (d b : Fin (m+1) → ℕ)
    (h : pathMass ((∑ i,Fin.tail d i)+R+1) (firstHit (b 0))≠0) :
    normalizedTrace a R d b=
      (killed (d 0) a (b 0)*pathMass ((∑ i,Fin.tail d i)+R+1) (firstHit (b 0)) /
        pathMass (d 0+((∑ i,Fin.tail d i)+R)+1) (firstHit a))*
      normalizedTrace (b 0) R (Fin.tail d) (Fin.tail b) := by
  simp only [normalizedTrace,segments_cons,traceKilledWeight]
  rw [Fin.sum_univ_succ d]
  change killed (d 0) a (b 0)*traceKilledWeight (b 0) (R+1)
    (segments (Fin.tail d) (Fin.tail b)) /
    pathMass (d 0+(∑ i,Fin.tail d i)+R+1) (firstHit a)=_
  rw [show d 0+(∑ i,Fin.tail d i)+R+1=d 0+((∑ i,Fin.tail d i)+R)+1 by omega]
  field_simp

lemma remaining_zero {m : ℕ} (s : Fin (m+1) → ℝ) (r : ℝ) :
    remaining s r 0=(∑ i,Fin.tail s i)+r := by
  simp only [remaining,Finset.sum_filter,Fin.sum_univ_succ,lt_self_iff_false,ite_false,
    Fin.succ_pos,ite_true,zero_add]
  rw [add_comm]
  rfl

lemma remaining_succ {m : ℕ} (s : Fin (m+1) → ℝ) (r : ℝ) (i : Fin m) :
    remaining s r i.succ=remaining (Fin.tail s) r i := by
  simp only [remaining,Finset.sum_filter,Fin.sum_univ_succ,Fin.not_lt_zero,ite_false,
    Fin.succ_lt_succ_iff,zero_add]
  rfl

lemma sum_ratio_tendsto {m : ℕ} {d : ℕ → Fin m → ℕ} {T : ℕ → ℕ}
    {s : Fin m → ℝ} (hd : ∀ i,Tendsto (fun n => (d n i:ℝ)/(T n:ℝ)) atTop (𝓝 (s i))) :
    Tendsto (fun n => ((∑ i,d n i:ℕ):ℝ)/(T n:ℝ)) atTop (𝓝 (∑ i,s i)) := by
  have hh := tendsto_finsetSum Finset.univ (fun i _ => hd i)
  simpa only [Nat.cast_sum,Finset.sum_div] using hh

lemma even_int_cast {n : ℕ} (h : Even n) : Even (n:ℤ) := by exact_mod_cast h

lemma even_int_terminal {n b : ℕ} (hn : Even n) (hb : Even b) :
    Even (((n+1:ℕ):ℤ)+((b:ℤ)+1)) := by
  have h := (even_int_cast hn).add (even_int_cast hb)
  have he : (((n+1:ℕ):ℤ)+((b:ℤ)+1))=((n:ℤ)+(b:ℤ))+2 := by push_cast; ring
  rw [he]
  exact h.add (by norm_num : Even (2:ℤ))


lemma firstHit_eventually_ne_zero {R T a : ℕ → ℕ} {t x : ℝ}
    (ht : 0<t) (hx : 0<x) (hR : Tendsto R atTop atTop)
    (hT : Tendsto T atTop atTop)
    (hr : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t))
    (hRe : ∀ n,Even (R n)) (hae : ∀ n,Even (a n))
    (ha : Tendsto (fun n => (a n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 x)) :
    ∀ᶠ n in atTop,pathMass (R n+1) (firstHit (a n))≠0 := by
  have hh := firstHit_scaled_limit ht hR hT hr
    (Filter.Eventually.of_forall (fun n => even_int_terminal (hRe n) (hae n))) ha
  have hp := hh.eventually (eventually_ne_nhds (hitHeat_pos ht hx).ne')
  filter_upwards [hp] with n hn
  exact fun h => hn (by simp only [h,mul_zero])


lemma pathMass_nonneg (N : ℕ) (P : Path N → Prop) : 0≤pathMass N P := by
  unfold pathMass
  positivity

lemma chainDensity_ne_top (m : ℕ) (z : ℝ) (a t x : Fin m → ℝ) :
    Radial.chainDensity z a t x≠∞ := by
  induction m generalizing z with
  | zero => exact ENNReal.one_ne_top
  | succ m ih =>
    apply ENNReal.mul_ne_top _ (ih _ _ _ _)
    unfold Radial.transition Set.indicator
    split_ifs <;> simp

/-- Interior-start conditioned trace densities from the exact killed kernels. -/
lemma scaledTrace_limit_positive (m : ℕ) {d b : ℕ → Fin m → ℕ} {R T a : ℕ → ℕ}
    {s x : Fin m → ℝ} {r z : ℝ}
    (hr : 0 < r) (hz : 0<z) (hs : ∀ i,0 < s i) (hx : ∀ i,0<x i)
    (hR : Tendsto R atTop atTop) (hT : Tendsto T atTop atTop)
    (hd : ∀ i,Tendsto (fun n => d n i) atTop atTop)
    (hrR : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 r))
    (hrd : ∀ i,Tendsto (fun n => (d n i:ℝ)/(T n:ℝ)) atTop (𝓝 (s i)))
    (hRe : ∀ n,Even (R n)) (hde : ∀ n i,Even (d n i))
    (hae : ∀ n,Even (a n)) (hbe : ∀ n i,Even (b n i))
    (ha : Tendsto (fun n => (a n:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 z))
    (hb : ∀ i,Tendsto (fun n => (b n i:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (x i))) :
    Tendsto (fun n => ENNReal.ofReal ((Real.sqrt (T n:ℝ)/2)^m*
      normalizedTrace (a n) (R n) (d n) (b n))) atTop
      (𝓝 (Radial.chainDensity z (durationRatio s r) (durationVariance s r) x)) := by
  induction m generalizing R T a r z with
  | zero =>
    have hne := firstHit_eventually_ne_zero hr hz hR hT hrR hRe hae ha
    apply tendsto_const_nhds.congr'
    filter_upwards [hne] with n hn
    have he : (∑ i : Fin 0,d n i)=0 := Fin.sum_univ_zero _
    simp only [normalizedTrace]
    rw [he,Nat.zero_add]
    simp only [segments,List.ofFn_zero,traceKilledWeight,pow_zero,one_mul,div_self hn,ENNReal.ofReal_one,Radial.chainDensity]
  | succ m ih =>
    let R' : ℕ → ℕ := fun n => (∑ i,Fin.tail (d n) i)+R n
    let t : ℝ := (∑ i,Fin.tail s i)+r
    have ht : 0<t := add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => (hs i.succ).le)) hr
    have hR' : Tendsto R' atTop atTop := tendsto_atTop_mono (fun n => Nat.le_add_left _ _) hR
    have hrR' : Tendsto (fun n => ((R' n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t) := by
      convert (sum_ratio_tendsto (fun i => hrd i.succ)).add hrR using 1 <;>
      simp [R',t,Nat.cast_add,add_div,add_assoc,Fin.tail_def]
    have hRe' (n : ℕ) : Even (R' n) :=
      (Finset.even_sum (fun i : Fin m => Fin.tail (d n) i) (fun i _ => hde n i.succ)).add (hRe n)
    have hk := conditioned_kernel_limit (hs 0) ht hz (hd 0) hR' hT (hrd 0) hrR'
      (Filter.Eventually.of_forall (fun n => ((even_int_cast (hde n 0)).add
        (even_int_cast (hbe n 0))).sub (even_int_cast (hae n))))
      (Filter.Eventually.of_forall (fun n => even_int_terminal (hRe' n) (hbe n 0)))
      (Filter.Eventually.of_forall (fun n => even_int_terminal ((hde n 0).add (hRe' n)) (hae n)))
      ha (hb 0)
    have hh := ih hr (hx 0) (fun i => hs i.succ) (fun i => hx i.succ) hR hT
      (fun i => hd i.succ) hrR (fun i => hrd i.succ) hRe (fun n i => hde n i.succ)
      (fun n => hbe n 0) (fun n i => hbe n i.succ) (hb 0) (fun i => hb i.succ)
    have hne := firstHit_eventually_ne_zero ht (hx 0) hR' hT hrR' hRe' (fun n => hbe n 0) (hb 0)
    have hlim := ENNReal.Tendsto.mul (ENNReal.continuous_ofReal.tendsto _ |>.comp hk)
      (Or.inr (chainDensity_ne_top _ _ _ _ _)) hh (Or.inr ENNReal.ofReal_ne_top)
    have hcoef : |t/(s 0+t)|=t/(s 0+t) := abs_of_pos (div_pos ht (add_pos (hs 0) ht))
    have htarget : Radial.transition (durationVariance s r 0)
        (|durationRatio s r 0| *z) (x 0)=
        ENNReal.ofReal (radialHeat (s 0*t/(s 0+t)) (t/(s 0+t)*z) (x 0)) := by
      rw [Radial.transition,indicator_of_mem (show x 0∈Ioi (0:ℝ) from hx 0)]
      simp only [durationVariance,durationRatio,remaining_zero]
      rw [hcoef]
    have heta : Fin.tail (durationRatio s r)=durationRatio (Fin.tail s) r := by
      funext i
      simp only [Fin.tail_def,durationRatio,remaining_succ]
    have hetv : Fin.tail (durationVariance s r)=durationVariance (Fin.tail s) r := by
      funext i
      simp only [Fin.tail_def,durationVariance,remaining_succ]
    change Tendsto _ atTop (𝓝 (Radial.transition (durationVariance s r 0)
      (|durationRatio s r 0| *z) (x 0)*
      Radial.chainDensity (x 0) (Fin.tail (durationRatio s r)) (Fin.tail (durationVariance s r)) (Fin.tail x)))
    rw [htarget,heta,hetv]
    apply hlim.congr'
    filter_upwards [hne] with n hn
    rw [normalizedTrace_cons _ _ _ _ hn,pow_succ]
    simp only [Function.comp_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity)
      (div_nonneg (mul_nonneg (killed_nonneg _ _ _) (pathMass_nonneg _ _)) (pathMass_nonneg _ _)))]
    congr 1
    simp only [R']
    simp +unfoldPartialApp only [Fin.tail_def]
    ring

/-- Entrance-start trace densities, including the singular zero-radius initial law. -/
lemma scaledTrace_limit_zero (m : ℕ) {d b : ℕ → Fin m → ℕ} {R T : ℕ → ℕ}
    {s x : Fin m → ℝ} {r : ℝ}
    (hr : 0 < r) (hs : ∀ i,0 < s i) (hx : ∀ i,0<x i)
    (hR : Tendsto R atTop atTop) (hT : Tendsto T atTop atTop)
    (hd : ∀ i,Tendsto (fun n => d n i) atTop atTop)
    (hrR : Tendsto (fun n => ((R n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 r))
    (hrd : ∀ i,Tendsto (fun n => (d n i:ℝ)/(T n:ℝ)) atTop (𝓝 (s i)))
    (hRe : ∀ n,Even (R n)) (hde : ∀ n i,Even (d n i))
    (hbe : ∀ n i,Even (b n i))
    (hb : ∀ i,Tendsto (fun n => (b n i:ℝ)/Real.sqrt (T n:ℝ)) atTop (𝓝 (x i))) :
    Tendsto (fun n => ENNReal.ofReal ((Real.sqrt (T n:ℝ)/2)^m*
      normalizedTrace 0 (R n) (d n) (b n))) atTop
      (𝓝 (Radial.chainDensity 0 (durationRatio s r) (durationVariance s r) x)) := by
  cases m with
  | zero =>
    have hl := firstHit_zero_scaled_limit hr hR hT hrR
      (Filter.Eventually.of_forall (fun n => by
        simpa using even_int_terminal (hRe n) (by norm_num : Even 0)))
    have hp : 0<2/r*heat r 0 := mul_pos (div_pos (by norm_num) hr) (heat_pos hr 0)
    have hne : ∀ᶠ n in atTop,pathMass (R n+1) (firstHit 0)≠0 := by
      filter_upwards [hl.eventually (eventually_ne_nhds hp.ne')] with n hn
      exact fun h => hn (by simp only [h,mul_zero])
    apply tendsto_const_nhds.congr'
    filter_upwards [hne] with n hn
    have he : (∑ i : Fin 0,d n i)=0 := Fin.sum_univ_zero _
    simp only [normalizedTrace]
    rw [he,Nat.zero_add]
    simp only [segments,List.ofFn_zero,traceKilledWeight,pow_zero,one_mul,div_self hn,ENNReal.ofReal_one,Radial.chainDensity]
  | succ m =>
    let R' : ℕ → ℕ := fun n => (∑ i,Fin.tail (d n) i)+R n
    let t : ℝ := (∑ i,Fin.tail s i)+r
    have ht : 0<t := add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun i _ => (hs i.succ).le)) hr
    have hR' : Tendsto R' atTop atTop := tendsto_atTop_mono (fun n => Nat.le_add_left _ _) hR
    have hrR' : Tendsto (fun n => ((R' n:ℝ)+1)/(T n:ℝ)) atTop (𝓝 t) := by
      convert (sum_ratio_tendsto (fun i => hrd i.succ)).add hrR using 1 <;>
      simp [R',t,Nat.cast_add,add_div,add_assoc,Fin.tail_def]
    have hRe' (n : ℕ) : Even (R' n) :=
      (Finset.even_sum (fun i : Fin m => Fin.tail (d n) i) (fun i _ => hde n i.succ)).add (hRe n)
    have hk := entrance_conditioned_limit (hs 0) ht (hd 0) hR' hT (hrd 0) hrR'
      (Filter.Eventually.of_forall (fun n => (even_int_cast (hde n 0)).add
        (even_int_cast (hbe n 0))))
      (Filter.Eventually.of_forall (fun n => even_int_terminal (hRe' n) (hbe n 0)))
      (Filter.Eventually.of_forall (fun n => by
        simpa using even_int_terminal ((hde n 0).add (hRe' n)) (by norm_num : Even 0)))
      (hb 0)
    have hh := scaledTrace_limit_positive m hr (hx 0) (fun i => hs i.succ) (fun i => hx i.succ) hR hT
      (fun i => hd i.succ) hrR (fun i => hrd i.succ) hRe (fun n i => hde n i.succ)
      (fun n => hbe n 0) (fun n i => hbe n i.succ) (hb 0) (fun i => hb i.succ)
    have hne := firstHit_eventually_ne_zero ht (hx 0) hR' hT hrR' hRe' (fun n => hbe n 0) (hb 0)
    have hlim := ENNReal.Tendsto.mul (ENNReal.continuous_ofReal.tendsto _ |>.comp hk)
      (Or.inr (chainDensity_ne_top _ _ _ _ _)) hh (Or.inr ENNReal.ofReal_ne_top)
    have htarget : Radial.transition (durationVariance s r 0)
        (|durationRatio s r 0| *0) (x 0)=
        ENNReal.ofReal (radialHeat (s 0*t/(s 0+t)) 0 (x 0)) := by
      rw [Radial.transition,indicator_of_mem (show x 0∈Ioi (0:ℝ) from hx 0)]
      simp only [durationVariance,durationRatio,remaining_zero]
      simp only [mul_zero]
      rfl
    have heta : Fin.tail (durationRatio s r)=durationRatio (Fin.tail s) r := by
      funext i
      simp only [Fin.tail_def,durationRatio,remaining_succ]
    have hetv : Fin.tail (durationVariance s r)=durationVariance (Fin.tail s) r := by
      funext i
      simp only [Fin.tail_def,durationVariance,remaining_succ]
    change Tendsto _ atTop (𝓝 (Radial.transition (durationVariance s r 0)
      (|durationRatio s r 0| *0) (x 0)*
      Radial.chainDensity (x 0) (Fin.tail (durationRatio s r)) (Fin.tail (durationVariance s r)) (Fin.tail x)))
    rw [htarget,heta,hetv]
    apply hlim.congr'
    filter_upwards [hne] with n hn
    rw [normalizedTrace_cons _ _ _ _ hn,pow_succ]
    simp only [Function.comp_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity)
      (div_nonneg (mul_nonneg (killed_nonneg _ _ _) (pathMass_nonneg _ _)) (pathMass_nonneg _ _)))]
    congr 1
    simp only [R']
    simp +unfoldPartialApp only [Fin.tail_def]
    ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma sum_differences_nat {m : ℕ} (g : Fin (m+1) → ℕ) (hg : Monotone g) :
    (∑ i : Fin m,(g i.succ-g i.castSucc))=g (Fin.last m)-g 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hh := ih (Fin.tail g) (hg.comp (fun _ _ h => Fin.succ_le_succ_iff.mpr h))
    simp only [Fin.tail_def,Fin.succ_castSucc] at hh
    rw [hh]
    have h0 := hg (show (0:Fin (m+2))≤(0:Fin (m+1)).succ by exact Fin.zero_le _)
    have h1 := hg (Fin.le_last ((0:Fin (m+1)).succ))
    change (g (Fin.succ 0)-g 0)+(g (Fin.last (m+1))-g (Fin.succ 0))=
      g (Fin.last (m+1))-g 0
    change g 0≤g (Fin.succ 0) at h0
    change g (Fin.succ 0)≤g (Fin.last (m+1)) at h1
    omega

lemma located_differences {m : ℕ} (g : Fin (m+1) → ℕ) (hg : Monotone g)
    (b : Fin m → ℕ) :
    located (segments (fun i => g i.succ-g i.castSucc) b)=
      List.ofFn (fun i => (g i.succ-g 0,b i)) := by
  induction m with
  | zero => simp [segments,located]
  | succ m ih =>
    rw [segments_cons,located]
    have hh := ih (Fin.tail g) (hg.comp (fun _ _ h => Fin.succ_le_succ_iff.mpr h)) (Fin.tail b)
    simp +unfoldPartialApp only [Fin.tail_def,Fin.succ_castSucc] at hh ⊢
    rw [hh,List.ofFn_succ,List.map_ofFn]
    congr 1
    congr 1
    funext i
    have h0 := hg (show (0:Fin (m+2))≤(0:Fin (m+1)).succ by exact Fin.zero_le _)
    have h1 := hg (show (0 : Fin (m+1)).succ ≤ i.succ.succ from Fin.succ_le_succ_iff.mpr (Fin.zero_le _))
    simp only [Function.comp_apply,Fin.castSucc_zero]
    congr 1
    omega

lemma sum_gridDurations {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) :
    (∑ i,gridDurations u n i)=evenGrid n (u (Fin.last m)) := by
  have hh := sum_differences_nat (fun i => evenGrid n (u i))
    (fun _ _ h => evenGrid_mono n (hu h))
  simpa only [gridDurations,h0,(show ((0:unitInterval):ℝ)=0 from rfl),evenGrid_zero,Nat.sub_zero] using hh

lemma grid_total {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) :
    (∑ i,gridDurations u n i)+gridRemainder u n+1=2*n+1 := by
  rw [sum_gridDurations u hu h0,gridRemainder]
  have h := evenGrid_le n (u (Fin.last m)).property.2
  omega

lemma grid_observed {N m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) (b : Fin m → ℕ) (d : Path N) :
    observed 0 (segments (gridDurations u n) b) d↔
      ∀ i,pathSum d (evenGrid n (u i.succ))=(b i:ℤ) := by
  have hh := located_differences (fun i => evenGrid n (u i))
    (fun _ _ h => evenGrid_mono n (hu h)) b
  unfold observed
  rw [show located (segments (gridDurations u n) b)=_ from hh]
  simp only [h0,(show ((0:unitInterval):ℝ)=0 from rfl),evenGrid_zero,Nat.sub_zero,List.mem_ofFn,
    forall_exists_index,forall_apply_eq_imp_iff,Int.natCast_zero,zero_add]

lemma gridRemainder_ratio {m : ℕ} (u : Fin (m+1) → unitInterval) :
    Tendsto (fun n => ((gridRemainder u n:ℝ)+1)/((2*n+1:ℕ):ℝ)) atTop
      (𝓝 (1-(u (Fin.last m):ℝ))) := by
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub (evenGrid_ratio (u (Fin.last m)) (u (Fin.last m)).property.1)
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only [gridRemainder]
  rw [Nat.cast_sub (evenGrid_le n (u (Fin.last m)).property.2)]
  have hp : ((2*n+1:ℕ):ℝ)≠0 := by positivity
  field_simp
  push_cast
  ring

lemma nat_atTop_of_ratio {A B : ℕ → ℕ} {r : ℝ} (hr : 0 < r)
    (hB : Tendsto B atTop atTop)
    (h : Tendsto (fun n => (A n:ℝ)/(B n:ℝ)) atTop (𝓝 r)) :
    Tendsto A atTop atTop := by
  have hB' : Tendsto (fun n => (B n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hB
  have hm := Filter.Tendsto.pos_mul_atTop hr h hB'
  have hB0 : ∀ᶠ n in atTop,(B n:ℝ)≠0 := (hB'.eventually_gt_atTop 0).mono (fun _ h => h.ne')
  have hh : Tendsto (fun n => (A n:ℝ)) atTop atTop := hm.congr' (by
    filter_upwards [hB0] with n hn
    exact div_mul_cancel₀ _ hn)
  exact tendsto_natCast_atTop_iff.mp hh

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding

lemma bridgeResidual_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IsGaussianProcess (fun p : unitInterval×unitInterval => bridgeResidual B p.1 p.2) P := by
  classical
  apply (bridgeAt_gaussian hB).of_isGaussianProcess
  intro p
  refine ⟨{p.1,p.2},
    { toFun x := x ⟨p.2,by simp⟩-bridgeRatio p.1 p.2*x ⟨p.1,by simp⟩
      map_add' x y := by simp only [Pi.add_apply]; ring
      map_smul' c x := by simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring},?_⟩
  intro ω
  rfl

lemma integral_bridgeResidual {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (a b : unitInterval) :
    P[bridgeResidual B a b]=0 := by
  have hg := bridgeAt_gaussian hB
  unfold bridgeResidual
  rw [integral_sub (hg.hasGaussianLaw_eval _).integrable
    ((hg.hasGaussianLaw_eval _).integrable.const_mul _),integral_const_mul]
  simp only [integral_bridgeAt hB,mul_zero,sub_zero]

lemma covariance_bridgeResidual_earlier {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {s a b : unitInterval} (hsa : s≤a) (hab : a≤b) (ha : (a:ℝ)<1) :
    cov[bridgeResidual B a b,bridgeAt B s;P]=0 := by
  have hg := bridgeAt_gaussian hB
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  unfold bridgeResidual
  rw [covariance_fun_sub_left (hg.hasGaussianLaw_eval _).memLp_two
    ((hg.hasGaussianLaw_eval _).memLp_two.const_mul _) (hg.hasGaussianLaw_eval _).memLp_two,
    covariance_const_mul_left,covariance_bridgeAt hB,covariance_bridgeAt hB]
  change bbCov (b:ℝ) (s:ℝ)-bridgeRatio a b*bbCov (a:ℝ) (s:ℝ)=0
  rw [bbCov,bbCov,min_eq_right (show (s:ℝ)≤b from hsa.trans hab),min_eq_right (show (s:ℝ)≤a from hsa)]
  unfold bridgeRatio
  have ha0 : 1-(a:ℝ)≠0 := ne_of_gt (sub_pos.mpr ha)
  field_simp
  ring

lemma variance_bridgeResidual {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {a b : unitInterval} (hab : a≤b) (ha : (a:ℝ)<1) :
    Var[bridgeResidual B a b;P]=bridgeVariance a b := by
  have hg := bridgeAt_gaussian hB
  have hr := (bridgeResidual_gaussian hB).hasGaussianLaw_eval (a,b)
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [← covariance_self hr.aemeasurable]
  change cov[bridgeResidual B a b,fun ω => bridgeAt B b ω-bridgeRatio a b*bridgeAt B a ω;P]=_
  rw [covariance_fun_sub_right hr.memLp_two (hg.hasGaussianLaw_eval _).memLp_two
    ((hg.hasGaussianLaw_eval _).memLp_two.const_mul _),covariance_const_mul_right,
    covariance_bridgeResidual_earlier hB le_rfl hab ha,mul_zero,sub_zero]
  unfold bridgeResidual
  rw [covariance_fun_sub_left (hg.hasGaussianLaw_eval _).memLp_two
    ((hg.hasGaussianLaw_eval _).memLp_two.const_mul _) (hg.hasGaussianLaw_eval _).memLp_two,
    covariance_const_mul_left,covariance_bridgeAt hB,covariance_bridgeAt hB]
  change bbCov (b:ℝ) (b:ℝ)-bridgeRatio a b*bbCov (a:ℝ) (b:ℝ)=_
  rw [bbCov,bbCov,min_self,min_eq_left (show (a:ℝ)≤b from hab)]
  unfold bridgeRatio bridgeVariance
  have ha0 : 1-(a:ℝ)≠0 := ne_of_gt (sub_pos.mpr ha)
  field_simp
  ring

lemma bridgeResidual_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {a b : unitInterval} (hab : a<b) (hb : (b:ℝ)<1) :
    HasLaw (bridgeResidual B a b) (gaussianReal 0 (bridgeVariance a b).toNNReal) P := by
  have hr := (bridgeResidual_gaussian hB).hasGaussianLaw_eval (a,b)
  refine ⟨hr.aemeasurable,?_⟩
  rw [hr.map_eq_gaussianReal,integral_bridgeResidual hB,
    variance_bridgeResidual hB hab.le (lt_trans hab hb)]

lemma innovation_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u)
    (h1 : ∀ i,(u i:ℝ)<1) (i : Fin m) :
    HasLaw (innovation B u i) (gaussianReal 0 1) P := by
  have hij := hu i.castSucc_lt_succ
  have hv := bridgeVariance_pos hij (h1 _)
  have hh := gaussianReal_const_mul (bridgeResidual_hasLaw hB hij (h1 _))
    ((Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹)
  have hvar : NNReal.mk ((Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹^2)
      (sq_nonneg _)*(bridgeVariance (u i.castSucc) (u i.succ)).toNNReal=1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_one,NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal _ hv.le,
      inv_pow,Real.sq_sqrt hv.le]
    exact inv_mul_cancel₀ hv.ne'
  change HasLaw (fun ω => (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹*
    bridgeResidual B (u i.castSucc) (u i.succ) ω) (gaussianReal 0 1) P
  simpa only [mul_zero,hvar] using hh

lemma innovations_independent {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u) (h1 : ∀ i,(u i:ℝ)<1) :
    iIndepFun (innovation B u) P := by
  classical
  have hg := bridgeAt_gaussian hB
  let L : ({x // x∈(Finset.univ : Finset (Fin (m+1)))} → ℝ) →L[ℝ] (Fin m → ℝ) :=
    { toFun x i := (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹*
        (x ⟨i.succ,by simp⟩-bridgeRatio (u i.castSucc) (u i.succ)*x ⟨i.castSucc,by simp⟩)
      map_add' x y := by ext i; simp only [Pi.add_apply]; ring
      map_smul' c x := by ext i; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
  have hjoint : HasGaussianLaw (fun ω i => innovation B u i ω) P :=
    ((hg.comp_right u).hasGaussianLaw Finset.univ).map L
  apply hjoint.iIndepFun_of_covariance_eq_zero
  intro i j hij
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hh (i j : Fin m) (hij : i<j) :
      cov[innovation B u j,innovation B u i;P]=0 := by
    have hr := (bridgeResidual_gaussian hB).hasGaussianLaw_eval (u j.castSucc,u j.succ)
    unfold innovation
    rw [covariance_const_mul_left,covariance_const_mul_right]
    have he : cov[bridgeResidual B (u j.castSucc) (u j.succ),
        bridgeResidual B (u i.castSucc) (u i.succ);P]=0 := by
      change cov[bridgeResidual B (u j.castSucc) (u j.succ),
        fun ω => bridgeAt B (u i.succ) ω-bridgeRatio (u i.castSucc) (u i.succ)*bridgeAt B (u i.castSucc) ω;P]=0
      rw [covariance_fun_sub_right hr.memLp_two (hg.hasGaussianLaw_eval _).memLp_two
        ((hg.hasGaussianLaw_eval _).memLp_two.const_mul _),covariance_const_mul_right,
        covariance_bridgeResidual_earlier hB (hu.monotone (by exact_mod_cast hij))
          (hu.monotone j.castSucc_lt_succ.le) (h1 _),
        covariance_bridgeResidual_earlier hB (hu.monotone (by exact_mod_cast hij.le))
          (hu.monotone j.castSucc_lt_succ.le) (h1 _)]
      ring
    rw [he,mul_zero,mul_zero]
  rcases lt_or_gt_of_ne hij with h|h
  · rw [covariance_comm]; exact hh i j h
  · exact hh j i h

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding

lemma innovations_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u) (h1 : ∀ i,(u i:ℝ)<1) :
    HasGaussianLaw (fun ω i => innovation B u i ω) P :=
  (innovations_independent hB u hu h1).hasGaussianLaw
    (fun i => (innovation_hasLaw hB u hu h1 i).hasGaussianLaw)

lemma independent_innovations {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hB : iIndepFun (fun i ω t => B i t ω) P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) :
    iIndepFun (fun k ω i => innovation (B k) u i ω) P := by
  let f : (ℝ≥0 → ℝ) → (Fin m → ℝ) := fun x i =>
    (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹*
      (x ⟨(u i.succ:ℝ),(u i.succ).property.1⟩-(u i.succ:ℝ)*x 1-
       bridgeRatio (u i.castSucc) (u i.succ)*
       (x ⟨(u i.castSucc:ℝ),(u i.castSucc).property.1⟩-(u i.castSucc:ℝ)*x 1))
  have hf : Measurable f := by fun_prop
  exact hB.comp (fun _ => f) (fun _ => hf)

/-- Regression innovations are independent not only in time but across the three
source Brownian coordinates; no radial-process theorem is taken as an assumption. -/
theorem vector_innovations_law {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ k,IsPreBrownianReal (B k) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u) (h1 : ∀ i,(u i:ℝ)<1) :
    HasLaw (fun ω i => (toLp 2 (fun k => innovation (B k) u i ω) : Space))
      (Measure.pi (fun _ : Fin m => stdGaussian Space)) P := by
  have hrows := independent_innovations hI u
  have hrowg := hrows.hasGaussianLaw (fun k => innovations_gaussian (hB k) u hu h1)
  let L : (Fin 3 → Fin m → ℝ) →L[ℝ] (Fin m → Fin 3 → ℝ) :=
    { toFun x i k := x k i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hg : HasGaussianLaw (fun ω i k => innovation (B k) u i ω) P := hrowg.map L
  have hin (k : Fin 3) := innovations_independent (hB k) u hu h1
  have hl (k : Fin 3) (i : Fin m) := innovation_hasLaw (hB k) u hu h1 i
  have hcol : iIndepFun (fun i ω k => innovation (B k) u i ω) P := by
    apply hg.iIndepFun_of_covariance_eval
    intro i j hij k l
    apply IndepFun.covariance_eq_zero _ (hl k i).hasGaussianLaw.memLp_two
      (hl l j).hasGaussianLaw.memLp_two
    by_cases hkl : k=l
    · subst l
      exact (hin k).indepFun hij
    · exact (hrows.indepFun hkl).comp (measurable_pi_apply i) (measurable_pi_apply j)
  have hlcol (i : Fin m) :
      HasLaw (fun ω => (toLp 2 (fun k => innovation (B k) u i ω) : Space)) (stdGaussian Space) P := by
    have hi := hrows.comp (fun _ x => x i) (fun _ => measurable_pi_apply i)
    have hr := hi.hasLaw_pi (fun k => hl k i)
    have hs : HasLaw (toLp 2 : (Fin 3 → ℝ) → Space) (stdGaussian Space)
        (Measure.pi (fun _ => gaussianReal 0 1)) :=
      ⟨(by fun_prop),map_pi_eq_stdGaussian⟩
    exact hs.comp hr
  exact (hcol.comp (fun _ => (toLp 2 : (Fin 3 → ℝ) → Space)) (by fun_prop)).hasLaw_pi hlcol

/-- Reconstruction of a chronological chain from its standardized innovations. -/
lemma chain_reconstruct (m : ℕ) (x : Fin (m+1) → Space) (a t : Fin m → ℝ)
    (ht : ∀ i,0<t i) :
    chain (x 0) a t (fun i => (Real.sqrt (t i))⁻¹ • (x i.succ-a i • x i.castSucc)) =
      Fin.tail x := by
  induction m with
  | zero => exact Subsingleton.elim _ _
  | succ m ih =>
    have ht0 : Real.sqrt (t 0)≠0 := ne_of_gt (Real.sqrt_pos.mpr (ht 0))
    have hw : a 0 • x 0+Real.sqrt (t 0) •
        ((Real.sqrt (t 0))⁻¹ • (x (Fin.succ 0)-a 0 • x 0))=x (Fin.succ 0) := by
      rw [smul_smul,mul_inv_cancel₀ ht0,one_smul,add_sub_cancel]
    have hh := ih (Fin.tail x) (Fin.tail a) (Fin.tail t) (fun i => ht i.succ)
    apply funext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hw
    · change chain (a 0 • x 0+Real.sqrt (t 0) •
          ((Real.sqrt (t 0))⁻¹ • (x (Fin.succ 0)-a 0 • x 0)))
        (Fin.tail a) (Fin.tail t) _ j=(Fin.tail (Fin.tail x)) j
      rw [hw]
      exact congrFun hh j

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory WithLp
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding SimpleWalk

lemma vector_residual {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (i : Fin m) (ω : Ω) :
    (Real.sqrt (bridgeVariance (u i.castSucc) (u i.succ)))⁻¹ •
      (bridgeVector B (u i.succ) ω-bridgeRatio (u i.castSucc) (u i.succ) •
        bridgeVector B (u i.castSucc) ω)=
      toLp 2 (fun k => innovation (B k) u i ω) := by
  ext k
  rfl

lemma norm_bridgeVector {Ω : Type} (B : Fin 3 → ℝ≥0 → Ω → ℝ)
    (u : unitInterval) (ω : Ω) : ‖bridgeVector B u ω‖=standardExcursion B ω u := by
  have h := EuclideanSpace.real_norm_sq_eq (bridgeVector B u ω)
  change ‖bridgeVector B u ω‖ ^ 2 = ∑ k : Fin 3, (bridgeAt (B k) u ω)^2 at h
  have hs : 0≤∑ k : Fin 3,(bridgeAt (B k) u ω)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [standardExcursion]
  change ‖bridgeVector B u ω‖=Real.sqrt (∑ k : Fin 3,(bridgeAt (B k) u ω)^2)
  have he := Real.sq_sqrt hs
  nlinarith [norm_nonneg (bridgeVector B u ω),Real.sqrt_nonneg (∑ k : Fin 3,(bridgeAt (B k) u ω)^2)]

/-- Exact finite-dimensional density of the source standard excursion (the norm
of three independent bridges), at every increasing collection of interior times. -/
theorem lintegral_standardExcursion {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ k,IsPreBrownianReal (B k) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u)
    (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1)
    (F : (Fin m → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω,F (fun i => standardExcursion B ω (u i.succ)) ∂P)=
      ∫⁻ x,F x*bridgeDensity u x := by
  let a : Fin m → ℝ := fun i => bridgeRatio (u i.castSucc) (u i.succ)
  let t : Fin m → ℝ := fun i => bridgeVariance (u i.castSucc) (u i.succ)
  have ht (i : Fin m) : 0<t i := bridgeVariance_pos (hu i.castSucc_lt_succ) (h1 _)
  have hl := vector_innovations_law hB hI u hu h1
  have he : ∀ᵐ ω ∂P,chain 0 a t (fun i => toLp 2 (fun k => innovation (B k) u i ω))=
      fun i => bridgeVector B (u i.succ) ω := by
    have hz : ∀ᵐ ω ∂P,∀ k,B k 0 ω=0 := ae_all_iff.mpr (fun k => (hB k).eval_zero_ae_eq_zero)
    filter_upwards [hz] with ω hω
    have hx : bridgeVector B (u 0) ω=0 := by
      rw [h0]
      ext k
      change B k (0:ℝ≥0) ω - (0:ℝ) * B k 1 ω = 0
      rw [hω k]
      ring
    have hh := chain_reconstruct m (fun i => bridgeVector B (u i) ω) a t ht
    rw [hx] at hh
    apply funext
    intro i
    simpa only [a,t,vector_residual,Fin.tail_def] using congrFun hh i
  have hFn : Measurable (fun z : Fin m → Space => F (fun i => ‖chain 0 a t z i‖)) := by
    have hc : Measurable (chain 0 a t) := ((continuous_chain m a t).comp
      (show Continuous (fun z : Fin m → Space => ((0:Space),z)) from by fun_prop)).measurable
    exact hF.comp (by fun_prop)
  calc
    _=(∫⁻ ω,F (fun i => ‖chain 0 a t (fun j => toLp 2 (fun k => innovation (B k) u j ω)) i‖) ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [he] with ω hω
      rw [hω]
      simp only [norm_bridgeVector]
    _=∫⁻ z,F (fun i => ‖chain 0 a t z i‖) ∂Measure.pi (fun _ => stdGaussian Space) :=
      hl.lintegral_comp hFn.aemeasurable
    _=_ := by simpa only [norm_zero,bridgeDensity,a,t] using lintegral_chain m 0 a t ht F hF

lemma measurable_bridgeDensity {m : ℕ} (u : Fin (m+1) → unitInterval) :
    Measurable (bridgeDensity u) :=
  (measurable_chainDensity m _ _).comp
    (show Measurable (fun x : Fin m → ℝ => ((0:ℝ),x)) from by fun_prop)

end FKCRT.Radial
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_ExcursionLaw
attribute [-instance] _root_.OAI.FKCRT.TreeCoding.CriticalEvenOffspring.markedCodeLaw_probability _root_.OAI.FKCRT.TreeCoding.codeMarkKernel_markov _root_.OAI.FKCRT.TreeCoding.codeMarkLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma sum_differences_real {m : ℕ} (g : Fin (m+1) → ℝ) :
    (∑ i : Fin m,(g i.succ-g i.castSucc))=g (Fin.last m)-g 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    have hh := ih (Fin.tail g)
    simp only [Fin.tail_def,Fin.succ_castSucc] at hh
    rw [hh]
    simp only [Fin.succ_last,Fin.castSucc_zero]
    ring

lemma remaining_differences {m : ℕ} (g : Fin (m+1) → ℝ) (i : Fin m) :
    remaining (fun j => g j.succ-g j.castSucc) (1-g (Fin.last m)) i=1-g i.succ := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    induction i using Fin.cases with
    | zero =>
      rw [remaining_zero]
      have hh := sum_differences_real (Fin.tail g)
      simp only [Fin.tail_def,Fin.succ_castSucc] at hh
      simp +unfoldPartialApp only [Fin.tail_def]
      rw [hh]
      simp only [Fin.succ_last]
      ring
    | succ i =>
      rw [remaining_succ]
      have hh := ih (Fin.tail g) i
      simpa only [Fin.tail_def,Fin.succ_castSucc,Fin.succ_last] using hh

lemma durationRatio_bridge {m : ℕ} (u : Fin (m+1) → unitInterval) :
    durationRatio (fun i => (u i.succ:ℝ)-(u i.castSucc:ℝ)) (1-(u (Fin.last m):ℝ))=
      fun i => Radial.bridgeRatio (u i.castSucc) (u i.succ) := by
  funext i
  rw [durationRatio,remaining_differences (fun j => (u j:ℝ)),Radial.bridgeRatio]
  congr 1
  ring

lemma durationVariance_bridge {m : ℕ} (u : Fin (m+1) → unitInterval) :
    durationVariance (fun i => (u i.succ:ℝ)-(u i.castSucc:ℝ)) (1-(u (Fin.last m):ℝ))=
      fun i => Radial.bridgeVariance (u i.castSucc) (u i.succ) := by
  funext i
  rw [durationVariance,remaining_differences (fun j => (u j:ℝ)),Radial.bridgeVariance]
  congr 1
  ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Histogram

lemma tendsto_withDensity {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] {μ : Measure α} {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (_hg : Measurable g)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hp : ∀ n, IsProbabilityMeasure (μ.withDensity (f n)))
    (hpg : IsProbabilityMeasure (μ.withDensity g)) :
    Tendsto (fun n => (⟨μ.withDensity (f n),hp n⟩ : ProbabilityMeasure α)) atTop
      (@nhds (ProbabilityMeasure α) inferInstance ⟨μ.withDensity g,hpg⟩) := by
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro s hs
  simp only [ProbabilityMeasure.coe_mk,withDensity_apply _ hs.measurableSet]
  have he : ∀ᵐ x ∂μ.restrict s,g x=liminf (fun n => f n x) atTop := by
    filter_upwards [ae_restrict_of_ae hlim] with x hx
    exact hx.liminf_eq.symm
  rw [lintegral_congr_ae he]
  exact lintegral_liminf_le (fun n => hf n)

end FKCRT.Histogram
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

lemma pathMass_trace_at_size {N : ℕ} (a R : ℕ) (xs : List (ℕ×ℕ))
    (h : traceSize R xs=N) :
    pathMass N (fun d => firstHit a d ∧ observed a xs d)=traceKilledWeight a R xs := by
  subst N
  exact pathMass_firstHit_observed a R xs

lemma excursion_probability {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) (b : Fin m → ℕ) :
    (excursionLaw n).real {d | ∀ i,pathSum d (evenGrid n (u i.succ))=(b i:ℤ)}=
      normalizedTrace 0 (gridRemainder u n) (gridDurations u n) b := by
  have ht : traceSize (gridRemainder u n+1) (segments (gridDurations u n) b)=2*n+1 := by
    rw [traceSize_segments,← Nat.add_assoc,grid_total u hu h0]
  have hh := pathMass_trace_at_size 0 (gridRemainder u n+1) (segments (gridDurations u n) b) ht
  simp_rw [grid_observed u hu h0] at hh
  rw [excursionLaw_real,normalizedTrace,grid_total u hu h0]
  simp only [mem_ofPred_eq]
  rw [hh]

lemma odd_size_atTop : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
  tendsto_atTop_mono (fun n => by show n≤2*n+1; omega) tendsto_id

lemma mesh_tendsto_zero : Tendsto mesh atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp odd_size_atTop))

lemma index_eq_iff {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    {d : Path (2*n+1)} (hd : firstHit 0 d) (i : Fin m) (b : ℕ) :
    gridIndex u n d i=b↔pathSum d (evenGrid n (u i.succ))=(2*b:ℕ) := by
  have hk := evenGrid_le n (u i.succ).property.2
  have hpos : 0≤pathSum d (evenGrid n (u i.succ)) := by
    have h := hd.2 _ (by omega : evenGrid n (u i.succ)<2*n+1)
    simpa only [Int.natCast_zero,zero_add] using h
  have hp := pathSum_parity d (hk.trans (Nat.le_succ _))
  have he : Even (evenGrid n (u i.succ):ℤ) := by exact_mod_cast even_evenGrid n (u i.succ)
  have hb := hp.add he
  rw [sub_add_cancel] at hb
  obtain ⟨k,hk⟩ := hb
  have hnat := Int.toNat_of_nonneg hpos
  unfold gridIndex
  push_cast
  omega

lemma gridSample_eq {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    {d : Path (2*n+1)} (hd : firstHit 0 d) (i : Fin m) :
    gridSample u n d i=(pathSum d (evenGrid n (u i.succ)):ℝ)/Real.sqrt ((2*n+1:ℕ):ℝ) := by
  have he := (index_eq_iff u n hd i (gridIndex u n d i)).mp rfl
  rw [gridSample,mesh,he]
  push_cast
  ring

lemma gridIndex_probability {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) (b : Fin m → ℕ) :
    (excursionLaw n).real {d | gridIndex u n d=b}=
      normalizedTrace 0 (gridRemainder u n) (gridDurations u n) (fun i => 2*b i) := by
  rw [← excursion_probability u hu h0]
  apply measureReal_congr
  filter_upwards [excursionLaw_ae n] with d hd
  apply propext
  change gridIndex u n d = b ↔ ∀ i, pathSum d (evenGrid n ↑(u i.succ)) = ↑(2 * b i)
  rw [funext_iff]
  exact forall_congr' (fun i => index_eq_iff u n hd i (b i))

lemma histogramDensity_positive {m : ℕ} (u : Fin (m+1) → unitInterval) (hu : Monotone u)
    (h0 : u 0=0) (n : ℕ) {x : Fin m → ℝ} (hx : ∀ i,0≤x i) :
    histogramDensity u n x=ENNReal.ofReal ((Real.sqrt ((2*n+1:ℕ):ℝ)/2)^m*
      normalizedTrace 0 (gridRemainder u n) (gridDurations u n)
        (fun i => 2*⌊x i/mesh n⌋₊)) := by
  simp +unfoldPartialApp only [histogramDensity,gridSample]
  rw [Histogram.density_lattice _ _ (mesh_pos n) hx]
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change ENNReal.ofReal ((excursionLaw n).real {d | gridIndex u n d=fun i => ⌊x i/mesh n⌋₊}) * _=_
  rw [gridIndex_probability u hu h0]
  simp only [Fintype.card_fin]
  have hp : 0≤normalizedTrace 0 (gridRemainder u n) (gridDurations u n) (fun i => 2*⌊x i/mesh n⌋₊) := by
    rw [← gridIndex_probability u hu h0 n (fun i => ⌊x i/mesh n⌋₊)]
    exact measureReal_nonneg
  rw [← ENNReal.ofReal_pow (mesh_pos n).le,← ENNReal.ofReal_inv_of_pos (pow_pos (mesh_pos n) _),
    ← ENNReal.ofReal_mul hp]
  congr 1
  rw [← inv_pow,mesh,inv_div]
  ring

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

lemma gridRemainder_atTop {m : ℕ} (u : Fin (m+1) → unitInterval)
    (h1 : (u (Fin.last m):ℝ)<1) : Tendsto (gridRemainder u) atTop atTop := by
  have h : Tendsto (fun n => gridRemainder u n+1) atTop atTop := nat_atTop_of_ratio (sub_pos.mpr h1) odd_size_atTop (by
    simpa only [Nat.cast_add,Nat.cast_one] using gridRemainder_ratio u)
  apply tendsto_atTop.2
  intro b
  filter_upwards [tendsto_atTop.1 h (b+1)] with n hn
  omega

lemma histogramDensity_limit_pos {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1)
    {x : Fin m → ℝ} (hx : ∀ i,0<x i) :
    Tendsto (fun n => histogramDensity u n x) atTop (𝓝 (Radial.bridgeDensity u x)) := by
  let s : Fin m → ℝ := fun i => (u i.succ:ℝ)-(u i.castSucc:ℝ)
  let r : ℝ := 1-(u (Fin.last m):ℝ)
  have hs (i : Fin m) : 0 < s i := sub_pos.mpr (hu i.castSucc_lt_succ)
  have hr : 0 < r := sub_pos.mpr (h1 _)
  have hd (i : Fin m) : Tendsto (fun n => gridDurations u n i) atTop atTop :=
    nat_atTop_of_ratio (hs i) odd_size_atTop (gridDurations_ratio u hu.monotone i)
  have hb (i : Fin m) : Tendsto (fun n => ((2*⌊x i/mesh n⌋₊:ℕ):ℝ)/
      Real.sqrt ((2*n+1:ℕ):ℝ)) atTop (𝓝 (x i)) := by
    have hh := Histogram.floor_mesh_tendsto mesh_pos mesh_tendsto_zero (hx i).le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    simp only [mesh,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hl := scaledTrace_limit_zero m hr hs hx (gridRemainder_atTop u (h1 _))
    odd_size_atTop hd (gridRemainder_ratio u) (gridDurations_ratio u hu.monotone)
    (gridRemainder_even u) (gridDurations_even u hu.monotone)
    (fun _ _ => even_two_mul _) hb
  simp only [s,r,durationRatio_bridge,durationVariance_bridge] at hl
  change Tendsto _ atTop (𝓝 (Radial.bridgeDensity u x)) at hl
  apply hl.congr'
  exact Filter.Eventually.of_forall (fun n => (histogramDensity_positive u hu.monotone h0 n (fun i => (hx i).le)).symm)

lemma chainDensity_zero {m : ℕ} (v : ℝ) (a t x : Fin m → ℝ)
    (hx : ∃ i,x i≤0) : Radial.chainDensity v a t x=0 := by
  induction m generalizing v with
  | zero => obtain ⟨i,_⟩ := hx; exact Fin.elim0 i
  | succ m ih =>
    obtain ⟨i,hi⟩ := hx
    induction i using Fin.cases with
    | zero =>
      rw [Radial.chainDensity,Radial.transition,indicator_of_notMem (show x 0 ∉ Ioi (0:ℝ) from not_lt.mpr hi),zero_mul]
    | succ i =>
      rw [Radial.chainDensity,ih _ (Fin.tail a) (Fin.tail t) (Fin.tail x) ⟨i,hi⟩,mul_zero]

lemma histogramDensity_limit_ae {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1) :
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      Tendsto (fun n => histogramDensity u n x) atTop (𝓝 (Radial.bridgeDensity u x)) := by
  have hwall : ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),∀ i,x i≠0 := by
    rw [volume_pi]
    exact ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ => volume) i 0)
  filter_upwards [hwall] with x hx
  by_cases hp : ∀ i,0<x i
  · exact histogramDensity_limit_pos u hu h0 h1 hp
  · obtain ⟨i,hi⟩ := not_forall.mp hp
    have hn : x i<0 := lt_of_le_of_ne (le_of_not_gt hi) (hx i)
    have hg : Radial.bridgeDensity u x=0 := chainDensity_zero _ _ _ _ ⟨i,hn.le⟩
    rw [hg]
    apply tendsto_const_nhds.congr'
    apply Filter.Eventually.of_forall
    intro n
    exact (Histogram.density_lattice_negative (excursionLaw n) (gridIndex u n)
      (mesh_pos n).le ⟨i,hn⟩).symm

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.Radial
open TreeCoding

lemma aemeasurable_standardExcursion {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ k,IsPreBrownianReal (B k) P)
    (u : unitInterval) : AEMeasurable (fun ω => standardExcursion B ω u) P := by
  apply Real.continuous_sqrt.measurable.comp_aemeasurable
  apply Finset.aemeasurable_fun_sum
  intro i _
  exact (((hB i).aemeasurable _).sub ((hB i).aemeasurable 1 |>.const_mul (u:ℝ))).pow_const 2

lemma standardExcursion_hasLaw {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ k,IsPreBrownianReal (B k) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u)
    (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1) :
    HasLaw (fun ω i => standardExcursion B ω (u i.succ)) (volume.withDensity (bridgeDensity u)) P := by
  have ha := AEMeasurable.of_eval (fun index : Fin m => aemeasurable_standardExcursion hB (u index.succ))
  refine ⟨ha,?_⟩
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map' hF.aemeasurable ha,lintegral_withDensity_eq_lintegral_mul _ (measurable_bridgeDensity u) hF]
  rw [lintegral_standardExcursion hB hI u hu h0 h1 F hF]
  apply lintegral_congr
  intro x
  exact mul_comm _ _

end FKCRT.Radial
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

lemma pathSum_step {N k : ℕ} (d : Path N) (hk : k<N) :
    pathSum d (k+1)=pathSum d k+sign (d ⟨k,hk⟩) := by
  have he (i : Fin N) : (if i.val<k+1 then sign (d i) else 0)=
      (if i.val<k then sign (d i) else 0)+(if i=⟨k,hk⟩ then sign (d ⟨k,hk⟩) else 0) := by
    by_cases hi : i=⟨k,hk⟩
    · subst i; simp
    · have hne : i.val≠k := fun h => hi (Fin.ext h)
      by_cases hh : i.val<k <;> simp [hi,hh,show (i.val<k+1)↔(i.val<k) by omega]
  simp only [pathSum,he,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

lemma abs_sign (s : Bool) : |(sign s:ℝ)|=1 := by cases s <;> norm_num [sign]

lemma pathSum_diff_le {N k j : ℕ} (d : Path N) (hj : j≤k) (hk : k≤N) :
    |(pathSum d k:ℝ)-(pathSum d j:ℝ)|≤(k:ℝ)-(j:ℝ) := by
  induction k generalizing j with
  | zero =>
    have : j=0 := by omega
    subst j
    simp
  | succ k ih =>
    by_cases he : j=k+1
    · subst j; simp
    · have hjk : j≤k := by omega
      have hh := ih hjk (by omega)
      rw [pathSum_step d (by omega)]
      push_cast
      calc
        |(pathSum d k:ℝ)+(sign (d ⟨k,by omega⟩):ℝ)-(pathSum d j:ℝ)| =
          |((pathSum d k:ℝ)-(pathSum d j:ℝ))+(sign (d ⟨k,by omega⟩):ℝ)| := by ring_nf
        _ ≤ |(pathSum d k:ℝ)-(pathSum d j:ℝ)|+|(sign (d ⟨k,by omega⟩):ℝ)| := abs_add_le _ _
        _ ≤ (k:ℝ)+1-j := by rw [abs_sign]; linarith

lemma pathSum_dist_le {N k j : ℕ} (d : Path N) (hk : k≤N) (hj : j≤N) :
    |(pathSum d k:ℝ)-(pathSum d j:ℝ)|≤|(k:ℝ)-(j:ℝ)| := by
  rcases le_total j k with h|h
  · simpa only [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))] using pathSum_diff_le d h hk
  · rw [abs_sub_comm,abs_sub_comm (k:ℝ)]
    simpa only [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))] using pathSum_diff_le d h hj

lemma arrayPolygon_binaryArray {N : ℕ} (d : Path N) :
    arrayPolygon (binaryArray d)=simplePolygon d := by
  simp only [arrayPolygon,simplePolygon,arrayWalk_binaryArray]

lemma arrayPolygon_code {N : ℕ} (d : Code N) :
    arrayPolygon (codeEmbedding N d)=walkPolygon binaryOffspring.sigma d.val := by
  simp only [arrayPolygon,walkPolygon,arrayWalk_codeEmbedding,binaryOffspring_sigma,one_mul]

lemma simplePolygon_grid_bound {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    {d : Path (2*n+1)} (hd : firstHit 0 d) (i : Fin m) :
    |simplePolygon d (u i.succ)-gridSample u n d i|≤3/Real.sqrt ((2*n+1:ℕ):ℝ) := by
  rw [gridSample_eq u n hd,simplePolygon]
  apply interpolation_sub_const_bound
  intro j hj
  have hs := hat_support hj
  have he := evenGrid_error n (u i.succ).property.1
  have hpos : 0<Real.sqrt ((2*n+1:ℕ):ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [← sub_div,abs_div,abs_of_pos hpos]
  apply (div_le_div_iff_of_pos_right hpos).mpr
  have hh := pathSum_dist_le d (Nat.le_of_lt_succ j.isLt)
    ((evenGrid_le n (u i.succ).property.2).trans (Nat.le_succ _))
  apply hh.trans
  rw [abs_lt] at hs
  rw [abs_le]
  constructor <;> linarith

lemma code_simple_integral (n : ℕ) (F : C(unitInterval,ℝ) → ℝ) :
    (∫ c,F (walkPolygon binaryOffspring.sigma c.val) ∂binaryOffspring.codeLaw n)=
      ∫ d,F (simplePolygon d) ∂excursionLaw n := by
  have h := binary_code_integral n (fun a => F (arrayPolygon a))
  simpa only [arrayPolygon_code,arrayPolygon_binaryArray] using h

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding

lemma histogram_converges {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1) :
    Tendsto (fun n => (⟨volume.withDensity (histogramDensity u n),histogram_probability u n⟩ :
      ProbabilityMeasure (Fin m → ℝ))) atTop
      (@nhds (ProbabilityMeasure (Fin m → ℝ)) inferInstance ⟨volume.withDensity (Radial.bridgeDensity u),Radial.bridgeDensity_probability u hu h1⟩) :=
  Histogram.tendsto_withDensity (fun _ => Histogram.measurable_density _ _ _)
    (Radial.measurable_bridgeDensity u) (histogramDensity_limit_ae u hu h0 h1)
    (histogram_probability u) (Radial.bridgeDensity_probability u hu h1)

lemma grid_integral_limit {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1)
    (F : BoundedContinuousFunction (Fin m → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    Tendsto (fun n => ∫ d,F (gridSample u n d) ∂excursionLaw n) atTop
      (𝓝 (∫ x,F x ∂volume.withDensity (Radial.bridgeDensity u))) := by
  have hm := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (histogram_converges u hu h0 h1) F
  change Tendsto (fun n => ∫ x,F x ∂volume.withDensity (histogramDensity u n)) atTop
    (𝓝 (∫ x,F x ∂volume.withDensity (Radial.bridgeDensity u))) at hm
  apply hm.congr_dist
  have he (n : ℕ) := Histogram.integral_mixture_close (excursionLaw n) (gridSample u n) (mesh_pos n) F hF
  simp_rw [Histogram.mixture_withDensity] at he
  exact squeeze_zero (fun _ => dist_nonneg) (fun n => by
    simpa only [Real.dist_eq,histogramDensity] using he n)
    (by simpa only [mul_zero] using mesh_tendsto_zero.const_mul (L:ℝ))

lemma pathEvaluation_continuous {m : ℕ} (u : Fin (m+1) → unitInterval) :
    Continuous (pathEvaluation u) := continuous_pi (fun i => continuous_eval_const (u i.succ))

lemma polygon_integral_close {m : ℕ} (u : Fin (m+1) → unitInterval) (n : ℕ)
    (F : BoundedContinuousFunction (Fin m → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    |(∫ d,F (simplePolygon d |> pathEvaluation u) ∂excursionLaw n)-
      (∫ d,F (gridSample u n d) ∂excursionLaw n)|≤(L:ℝ)*(3/Real.sqrt ((2*n+1:ℕ):ℝ)) := by
  rw [← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ _ : Path (2*n+1),(L:ℝ)*(3/Real.sqrt ((2*n+1:ℕ):ℝ)) ∂excursionLaw n := by
      apply integral_mono_ae (Integrable.of_finite) (integrable_const _)
      filter_upwards [excursionLaw_ae n] with d hd
      apply (hF.dist_le_mul _ _).trans
      apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
      apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      exact simplePolygon_grid_bound u n hd i
    _ = _ := by simp

lemma polygon_integral_limit {m : ℕ} (u : Fin (m+1) → unitInterval)
    (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1)
    (F : BoundedContinuousFunction (Fin m → ℝ) ℝ) {L : ℝ≥0} (hF : LipschitzWith L F) :
    Tendsto (fun n => ∫ d,F (pathEvaluation u (simplePolygon d)) ∂excursionLaw n) atTop
      (𝓝 (∫ x,F x ∂volume.withDensity (Radial.bridgeDensity u))) := by
  apply (grid_integral_limit u hu h0 h1 F hF).congr_dist
  have hz : Tendsto (fun n => (L:ℝ)*(3/Real.sqrt ((2*n+1:ℕ):ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (3:ℝ))).div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp odd_size_atTop))
    simpa only [mul_zero,Function.comp_def] using h.const_mul (L:ℝ)
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hz
  rw [dist_comm,Real.dist_eq]
  exact polygon_integral_close u n F hF

local instance instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_r140a2c_1 : MeasurableSpace C(unitInterval,ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩
lemma vervaat_fdd {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {m : ℕ}
    (u : Fin (m+1) → unitInterval) (hu : StrictMono u) (h0 : u 0=0) (h1 : ∀ i,(u i:ℝ)<1) :
    HasLaw (fun ω => pathEvaluation u (vervaat (bridgePath B ω)))
      (volume.withDensity (Radial.bridgeDensity u)) P := by
  have hV := (binaryOffspring.codeWalk_converges hB).continuous_comp (pathEvaluation_continuous u)
  refine ⟨hV.aemeasurable_limit,?_⟩
  have ht : Tendsto (fun n => (⟨(binaryOffspring.codeLaw n).map
      (fun d : Code (2*n+1) => pathEvaluation u (walkPolygon binaryOffspring.sigma d.val)),
      by first | infer_instance | exact Measure.isProbabilityMeasure_map ((measurable_of_countable _).aemeasurable)⟩ : ProbabilityMeasure (Fin m → ℝ)))
      atTop (@nhds (ProbabilityMeasure (Fin m → ℝ)) inferInstance ⟨volume.withDensity (Radial.bridgeDensity u),Radial.bridgeDensity_probability u hu h1⟩) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    rintro F ⟨M,hM⟩ ⟨L,hL⟩
    let F' : BoundedContinuousFunction (Fin m → ℝ) ℝ := ⟨⟨F,hL.continuous⟩,⟨M,hM⟩⟩
    change Tendsto (fun n => ∫ x,F x ∂(binaryOffspring.codeLaw n).map
      (fun d : Code (2*n+1) => pathEvaluation u (walkPolygon binaryOffspring.sigma d.val))) atTop (𝓝 (∫ x,F x ∂volume.withDensity (Radial.bridgeDensity u)))
    have he (n : ℕ) : (∫ x,F x ∂(binaryOffspring.codeLaw n).map
        (fun d : Code (2*n+1) => pathEvaluation u (walkPolygon binaryOffspring.sigma d.val)))=
        ∫ d,F (pathEvaluation u (simplePolygon d)) ∂excursionLaw n := by
      rw [integral_map (measurable_of_countable _).aemeasurable hL.continuous.aestronglyMeasurable]
      exact code_simple_integral n (fun f => F (pathEvaluation u f))
    simp_rw [he]
    exact polygon_integral_limit u hu h0 h1 F' hL
  exact congrArg (fun μ : ProbabilityMeasure (Fin m → ℝ) => (μ : Measure (Fin m → ℝ)))
    (tendsto_nhds_unique hV.tendsto ht)

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_13
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_13 : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

lemma interiorTimes_strictMono (m : ℕ) : StrictMono (interiorTimes m) := by
  intro i j hij
  change (i.val:ℝ)/(m+2:ℕ)<(j.val:ℝ)/(m+2:ℕ)
  exact (div_lt_div_iff_of_pos_right (by positivity)).mpr (Nat.cast_lt.mpr hij)

lemma interiorTimes_zero (m : ℕ) : interiorTimes m 0=0 := by
  apply Subtype.ext
  simp [interiorTimes,gridPoint]

lemma interiorTimes_lt_one (m : ℕ) (i : Fin (m+2)) : (interiorTimes m i:ℝ)<1 := by
  change (i.val:ℝ)/(m+2:ℕ)<1
  exact (div_lt_one (by positivity)).mpr (Nat.cast_lt.mpr i.isLt)

lemma continuous_interiorReconstruct (m : ℕ) : Continuous (interiorReconstruct m) :=
  (continuous_interpolation _).comp (continuous_pi (fun _ => continuous_apply _))

lemma interiorIndex_bounds (m : ℕ) (j : Fin (m+3)) :
    (interiorIndex m j).val+1≤j.val+1 ∧ j.val≤(interiorIndex m j).val+2 := by
  simp only [interiorIndex]
  have hj := j.isLt
  omega

lemma interiorTime_dist (m : ℕ) (j : Fin (m+3)) :
    dist (interiorTimes m (interiorIndex m j).succ) (gridPoint (m+2) j)≤1/(m+2:ℕ) := by
  have h := interiorIndex_bounds m j
  change |(((interiorIndex m j).val+1:ℕ):ℝ)/(m+2:ℕ)-(j.val:ℝ)/(m+2:ℕ)|≤_
  rw [← sub_div,abs_div,abs_of_pos (by positivity : (0:ℝ)<(m+2:ℕ)),
    div_le_div_iff_of_pos_right (by positivity)]
  rw [abs_le]
  have h₁ : ((interiorIndex m j).val:ℝ)+1≤(j.val:ℝ)+1 := by exact_mod_cast h.1
  have h₂ : (j.val:ℝ)≤((interiorIndex m j).val:ℝ)+2 := by exact_mod_cast h.2
  push_cast
  constructor <;> linarith

lemma interiorReconstruct_tendsto (f : C(unitInterval,ℝ)) :
    Tendsto (fun m => interiorReconstruct m (fun i => f (interiorTimes m i.succ))) atTop (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε/2) (half_pos hε)
  have hz : Tendsto (fun m : ℕ => (2:ℝ)/(m+2:ℕ)) atTop (𝓝 (0:ℝ)) := by
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  filter_upwards [hz.eventually (gt_mem_nhds hδ)] with m hm
  apply lt_of_le_of_lt _ (half_lt_self hε)
  rw [dist_eq_norm]
  apply (ContinuousMap.norm_le _ (by positivity : 0≤ε/2)).mpr
  intro t
  change |interiorReconstruct m _ t-f t|≤ε/2
  apply interpolation_sub_const_bound
  intro j hj
  have ht := hat_gridPoint_dist (by omega : 0 < m+2) j t hj
  have hh := interiorTime_dist m j
  have htriangle := dist_triangle (interiorTimes m (interiorIndex m j).succ) (gridPoint (m+2) j) t
  have he : (1:ℝ)/(m+2:ℕ)+1/(m+2:ℕ)=2/(m+2:ℕ) := by ring
  apply (hd (lt_of_le_of_lt htriangle ?_)).le
  have hsum := add_lt_add_of_le_of_lt hh ht
  rw [he] at hsum
  exact hsum.trans hm

lemma interior_integral_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → C(unitInterval,ℝ)} (hX : AEMeasurable X P)
    (F : BoundedContinuousFunction C(unitInterval,ℝ) ℝ) :
    Tendsto (fun m => ∫ ω,F (interiorReconstruct m (fun i => X ω (interiorTimes m i.succ))) ∂P)
      atTop (𝓝 (∫ ω,F (X ω) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro m
    exact F.continuous.measurable.comp_aemeasurable
      ((continuous_interiorReconstruct m).measurable.comp_aemeasurable
        (AEMeasurable.of_eval (fun index =>
          (continuous_eval_const (interiorTimes m index.succ)).measurable.comp_aemeasurable hX)))
      |>.aestronglyMeasurable
  · exact integrable_const _
  · intro m
    exact ae_of_all _ (fun ω => F.norm_coe_le_norm _)
  · exact ae_of_all _ (fun ω => F.continuous.continuousAt.tendsto.comp (interiorReconstruct_tendsto (X ω)))

lemma identDistrib_of_interior {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → C(unitInterval,ℝ)} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (h : ∀ m : ℕ,IdentDistrib (fun ω (i : Fin (m+1)) => X ω (interiorTimes m i.succ))
      (fun ω (i : Fin (m+1)) => Y ω (interiorTimes m i.succ)) P P) : IdentDistrib X Y P P := by
  refine ⟨hX,hY,?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map hX F.continuous.aestronglyMeasurable,integral_map hY F.continuous.aestronglyMeasurable]
  apply tendsto_nhds_unique (interior_integral_limit hX F)
  apply (interior_integral_limit hY F).congr
  intro m
  exact ((h m).comp ((F.continuous.comp (continuous_interiorReconstruct m)).measurable)).integral_eq.symm

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_14
local instance instBorelSpaceContinuousMapElemRealUnitInterval_solutions_14 : BorelSpace C(unitInterval,ℝ) := ⟨rfl⟩

lemma continuous_standardExcursion {Ω : Type} {B : Fin 3 → ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hB : ∀ i,Continuous (B i · ω)) : Continuous (standardExcursion B ω) := by
  unfold standardExcursion
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro i _
  apply Continuous.pow
  apply Continuous.sub
  · exact (hB i).comp (continuous_subtype_val.subtype_mk _)
  · exact continuous_subtype_val.mul continuous_const

lemma standardExcursion_ae_continuous {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P,Continuous (standardExcursion B ω) := by
  filter_upwards [ae_all_iff.mpr (fun i => (hB i).cont)] with ω hω
  exact continuous_standardExcursion hω

lemma excursionPath_ae_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P,(excursionPath B ω : unitInterval → ℝ)=standardExcursion B ω := by
  filter_upwards [standardExcursion_ae_continuous hB] with ω hω
  funext t
  exact ContinuousMap.mkD_apply_of_continuous hω

local instance instMeasurableSpaceContinuousMapElemRealUnitIntervalProd_solutions_1_r140a2c_1 : MeasurableSpace C(unitInterval,ℝ×ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ×ℝ) := ⟨rfl⟩
lemma dense_eval_measurableEmbedding : MeasurableEmbedding (fun f : C(unitInterval,ℝ) =>
    fun n : ℕ => f (TopologicalSpace.denseSeq unitInterval n)) := by
  apply Continuous.measurableEmbedding
  · exact continuous_pi (fun n => continuous_eval_const _)
  · intro f g he
    apply ContinuousMap.ext
    exact congrFun ((TopologicalSpace.denseRange_denseSeq unitInterval).equalizer f.continuous g.continuous he)

lemma excursionPath_aemeasurable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P) :
    AEMeasurable (excursionPath B) P := by
  apply dense_eval_measurableEmbedding.aemeasurable_comp_iff.mp
  apply AEMeasurable.of_eval
  intro n
  apply (Radial.aemeasurable_standardExcursion (fun i => (hB i).toIsPreBrownianReal) _).congr
  filter_upwards [excursionPath_ae_eq hB] with ω hω
  exact (congrFun hω _).symm

/-- The law identification is proved from exact binary first-passage counts and
radial Gaussian densities, not assumed as Vervaat's theorem. -/
theorem vervaat_identDistrib_excursion {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) :
    IdentDistrib (fun ω => vervaat (bridgePath W ω)) (excursionPath B) P P := by
  apply identDistrib_of_interior
    ((measurable_vervaat).comp_aemeasurable (bridgePath_aemeasurable hW)) (excursionPath_aemeasurable hB)
  intro m
  have hV := SimpleWalk.vervaat_fdd hW (interiorTimes m) (interiorTimes_strictMono m)
    (interiorTimes_zero m) (interiorTimes_lt_one m)
  have hE := Radial.standardExcursion_hasLaw (fun i => (hB i).toIsPreBrownianReal) hI
    (interiorTimes m) (interiorTimes_strictMono m) (interiorTimes_zero m) (interiorTimes_lt_one m)
  apply hV.identDistrib
  apply hE.congr
  filter_upwards [excursionPath_ae_eq hB] with ω hω
  exact funext (fun i => congrFun hω _)

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_SpineBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma distribution_norm_tight {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {Ω : ℕ → Type*} {Ω' : Type*} [∀ n,MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n,Measure (Ω n)} {ν : Measure Ω'} [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {X : ∀ n,Ω n → E} {Y : Ω' → E} (h : TendstoInDistribution X atTop Y μ ν)
    (hm : ∀ n,Measurable (X n)) {η : ℝ} (hη : 0<η) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n in atTop,(μ n).real {x | C<‖X n x‖}≤η := by
  let G : ℕ → E → ℝ := fun j z => min 1 (‖z‖/(j+1:ℝ))
  have hG (j) : Continuous (G j) := continuous_const.min (continuous_norm.div_const _)
  have hG0 (j z) : 0≤G j z := le_min (by norm_num) (by positivity)
  have hG1 (j z) : |G j z|≤1 := by rw [abs_of_nonneg (hG0 j z)]; exact min_le_left _ _
  have ht : Tendsto (fun j : ℕ => ∫ x,G j (Y x) ∂ν) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (fun _ : Ω' => (1:ℝ))
      (F := fun j x => G j (Y x)) (f := fun _ =>0)
      (fun j => ((hG j).measurable.comp_aemeasurable h.aemeasurable_limit).aestronglyMeasurable)
      (integrable_const _) (fun j => ae_of_all ν (fun z => hG1 j (Y z))) (by
        apply ae_of_all
        intro z
        have hh : Tendsto (fun j : ℕ => ‖Y z‖/(j+1:ℝ)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa only [G,min_eq_right (by norm_num : (0:ℝ)≤1)] using
          (tendsto_const_nhds.min hh (f := fun _ : ℕ => (1:ℝ))))
    simpa only [integral_zero] using hh
  obtain ⟨j,hj⟩ := (ht.eventually (gt_mem_nhds (half_pos hη))).exists
  have hx := integral_tendsto_of_tendstoInDistribution h (hG j) (hG1 j)
  refine ⟨j+1,by positivity,?_⟩
  filter_upwards [hx.eventually (gt_mem_nhds (hj.trans (half_lt_self hη)))] with n hn
  apply le_of_lt (lt_of_le_of_lt ?_ hn)
  let A := {x : Ω n | (j+1:ℝ)<‖X n x‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (hm n).norm
  rw [← integral_indicator_one hA]
  have hi : Integrable (fun x => G j (X n x)) (μ n) :=
    Integrable.of_bound ((hG j).measurable.comp (hm n)).aestronglyMeasurable 1
      (ae_of_all _ (fun x => hG1 j (X n x)))
  apply integral_mono ((integrable_const (1:ℝ)).indicator hA) hi
  intro x
  by_cases hx : x∈A
  · rw [Set.indicator_of_mem hx]
    exact le_min le_rfl ((le_div_iff₀ (by positivity : (0:ℝ)<j+1)).mpr (by simpa using hx.le))
  · rw [Set.indicator_of_notMem hx]
    exact hG0 j _

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MarkedSpines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

variable {A : Type*} [MeasurableSpace A]

lemma CriticalEvenOffspring.markedCodeLaw_fst (p : CriticalEvenOffspring)
    (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (n : ℕ) (E : Set (Code (2*n+1))) :
    (p.markedCodeLaw κ n).real (Prod.fst ⁻¹' E)=(p.codeLaw n).real E := by
  have hh : Prod.fst ⁻¹' E=E×ˢ(Set.univ : Set (Fin (2*n+1) → A)) := by ext x; simp
  unfold Measure.real
  rw [hh,CriticalEvenOffspring.markedCodeLaw,Measure.compProd_apply_prod (Set.to_countable E).measurableSet MeasurableSet.univ]
  simp

end FKCRT.TreeCoding
end

end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_GHPBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma heightProjection_continuous : Continuous heightProjection :=
  ContinuousMap.continuous_postcomp ⟨Prod.snd,continuous_snd⟩

lemma heightProjection_diagonal (f : C(unitInterval,ℝ)) : heightProjection (diagonalPath f)=f := by
  ext t
  rfl

lemma heightCode_eq {N : ℕ} (p : CriticalEvenOffspring) (d : Code N) :
    heightCode p d=heightProjection (jointCode p.sigma d) := by ext t;rfl

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_15
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitInterval_solutions_15
local instance instMeasurableSpaceContinuousMapElemRealUnitIntervalProd_solutions_3_r140a2c_1 : MeasurableSpace C(unitInterval,ℝ×ℝ) := borel _
local instance : BorelSpace C(unitInterval,ℝ×ℝ) := ⟨rfl⟩
/-- The unconditional, full height-path limit with the exact excursion
law; this only reuses the already proved joint invariance theorem. -/
theorem CriticalEvenOffspring.heightCode_CLT (p : CriticalEvenOffspring)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) :
    TendstoInDistribution (fun n (d : Code (2*n+1)) => heightCode p d) atTop
      (excursionPath B) p.codeLaw P := by
  have hh := (p.jointCode_vervaat_CLT (hB 0)).continuous_comp heightProjection_continuous
  simp only [Function.comp_def,← heightCode_eq,heightProjection_diagonal] at hh
  have hi := vervaat_identDistrib_excursion (hB 0) hB hI
  refine ⟨hh.forall_aemeasurable,hi.aemeasurable_snd,?_⟩
  convert hh.tendsto using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  exact hi.map_eq.symm

end FKCRT.TreeCoding
end


end OAI
end

section
-- module Solutions.OAIQ021_FK.FKMaps_MetricLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open List Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology
namespace FKCRT.Inventory
open FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma heightFactor_tendsto : Tendsto heightFactor atTop (𝓝 1) := by
  have hh : Tendsto (fun n : ℕ => 1/(2*((n:ℝ)+1))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop (by norm_num))
  have hs := ((tendsto_const_nhds.add hh (a := (1:ℝ))).sqrt)
  change Tendsto (fun n : ℕ => Real.sqrt (1+1/(2*((n:ℝ)+1)))) atTop (𝓝 1)
  simpa only [add_zero,Real.sqrt_one] using hs

end FKCRT.Inventory
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

lemma distribution_smul_one {E Ω' : Type*} {Ω : ℕ → Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [∀ n,MeasurableSpace (Ω n)] [MeasurableSpace Ω']
    {μ : ∀ n,Measure (Ω n)} {ν : Measure Ω'} [∀ n,IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {X : ∀ n,Ω n → E} {Z : Ω' → E} (h : TendstoInDistribution X atTop Z μ ν)
    (hm : ∀ n,Measurable (X n)) {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 1)) :
    TendstoInDistribution (fun n x => a n • X n x) atTop Z μ ν := by
  apply tendstoInDistribution_of_close h (fun n => ((hm n).const_smul (a n)).aemeasurable)
  intro ε hε
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨C,hC,hbound⟩ := distribution_norm_tight h hm (half_pos hη)
  have ha' : Tendsto (fun n => |1-a n|) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero] using (tendsto_const_nhds.sub ha (a := (1:ℝ))).abs
  filter_upwards [hbound,ha'.eventually (gt_mem_nhds (div_pos hε hC))] with n hn hn'
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  apply lt_of_le_of_lt _ (half_lt_self hη)
  apply le_trans _ hn
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx
  change C<‖X n x‖
  change ε<dist (X n x) (a n • X n x) at hx
  rw [dist_eq_norm,show X n x-a n • X n x=(1-a n) • X n x by rw [sub_smul,one_smul],
    norm_smul,Real.norm_eq_abs] at hx
  by_contra hbad
  have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hbad) (abs_nonneg (1-a n))
  have hh' := (lt_div_iff₀ hC).mp hn'
  linarith

lemma CriticalEvenOffspring.markedCodeLaw_map_fst (p : CriticalEvenOffspring)
    {A : Type*} [MeasurableSpace A] (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)] (n : ℕ) :
    (p.markedCodeLaw κ n).map Prod.fst=p.codeLaw n := by
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply measurable_fst hE,← ofReal_measureReal,← ofReal_measureReal]
  exact congrArg ENNReal.ofReal (p.markedCodeLaw_fst κ n E)

attribute [local instance] OAI.FKCRT.TreeCoding.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions_16
attribute [local instance] OAI.FKCRT.TreeCoding.instBorelSpaceContinuousMapElemRealUnitInterval_solutions_16
lemma CriticalEvenOffspring.marked_height_CLT (p : CriticalEvenOffspring)
    {A : Type*} [MeasurableSpace A] (κ : ℕ → Measure A) [∀ k,IsProbabilityMeasure (κ k)]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) P)
    (hI : iIndepFun (fun i ω t => B i t ω) P) :
    TendstoInDistribution (fun n (x : Code (2*n+1) × (Fin (2*n+1) → A)) => heightCode p x.1)
      atTop (excursionPath B) (p.markedCodeLaw κ) P := by
  have hh := p.heightCode_CLT hB hI
  refine ⟨fun n => ((measurable_of_countable (heightCode p)).comp measurable_fst).aemeasurable,
    hh.aemeasurable_limit,?_⟩
  have hmap (n : ℕ) : (p.markedCodeLaw κ n).map (fun x => heightCode p x.1)=
      (p.codeLaw n).map (heightCode p) := by
    change (p.markedCodeLaw κ n).map (heightCode p ∘ Prod.fst)=_
    rw [← Measure.map_map (measurable_of_countable _) measurable_fst,p.markedCodeLaw_map_fst]
  simpa only [hmap] using hh.tendsto

end FKCRT.TreeCoding
namespace FKCRT.Inventory
open FKCRT.TreeCoding

attribute [local instance] OAI.FKCRT.Inventory.instMeasurableSpaceContinuousMapElemRealUnitInterval_solutions
attribute [local instance] OAI.FKCRT.Inventory.instBorelSpaceContinuousMapElemRealUnitInterval_solutions
/-- The exact original-edge normalization of the same sampled marked tree
has the standard (not rescaled) three-bridge excursion limit. -/
theorem actualHeight_CLT_oai (P : Parameters)
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : Fin 3 → ℝ≥0 → Ω → ℝ} (hB : ∀ i,IsBrownianReal (B i) μ)
    (hI : iIndepFun (fun i ω t => B i t ω) μ) :
    TendstoInDistribution (actualHeight P) atTop (excursionPath B) (actualDrawLaw P) μ := by
  have hh := (actualOffspring P).marked_height_CLT
    (fun k => (CoreLabel.markLaw P k).toMeasure) hB hI
  have hr : TendstoInDistribution
      (fun n (x : ActualDraw n) => heightCode (actualOffspring P) x.1) atTop
      (excursionPath B) (actualDrawLaw P) μ :=
    ⟨fun n => hh.forall_aemeasurable (n+1),hh.aemeasurable_limit,
      hh.tendsto.comp (tendsto_add_atTop_nat 1)⟩
  exact distribution_smul_one hr (fun _ => measurable_of_countable _) heightFactor_tendsto

end FKCRT.Inventory
end


end OAI
end

theorem solution : type_of% @OAI.FKCRT.Inventory.actualHeight_CLT_oai := @OAI.FKCRT.Inventory.actualHeight_CLT_oai
