-- Prove2me | solution 1 for OAI.SKRatio.Planted.residual_norm_rare
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:34:43.67774+00:00
-- url     : https://prove2.me/submissions/c2bf4ea4-0c9b-4f24-8380-cb1fa6b8f8d7

import Mathlib
import Definitions.Def_SKRatio
import Definitions.Def_OAIQ024S008
import Theorems.Thm_OAI_SKRatio_Planted_augmented_norm_rare

section
-- module Solutions.OAIQ024_SK.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_GOERegression
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise

namespace SKRatioClock.Regression

lemma coordinate_hasLaw {ι : Type*} [Fintype ι] (i : ι) :
    HasLaw (fun g : ι → ℝ => g i) (gaussianReal 0 1) (standardArrayLaw ι) :=
  (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).hasLaw

lemma coordinates_independent {ι : Type*} [Fintype ι] :
    iIndepFun (fun i (g : ι → ℝ) => g i) (standardArrayLaw ι) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

lemma coordinates_gaussian {ι : Type*} [Fintype ι] :
    HasGaussianLaw (fun g : ι → ℝ => g) (standardArrayLaw ι) :=
  coordinates_independent.hasGaussianLaw (fun i => (coordinate_hasLaw i).hasGaussianLaw)

lemma coordinate_covariance {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    cov[fun g : ι → ℝ => g i, fun g => g j; standardArrayLaw ι] = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    rw [covariance_self (coordinate_hasLaw i).aemeasurable,
      (coordinate_hasLaw i).variance_eq, variance_id_gaussianReal]
    simp
  · rw [ite_eq_right h]
    exact (coordinates_independent.indepFun h).covariance_eq_zero
      ((coordinate_hasLaw i).hasGaussianLaw.memLp_two)
      ((coordinate_hasLaw j).hasGaussianLaw.memLp_two)

attribute [local instance] OAI.SKRatioClock.Regression.matrixMeasurable
local instance matrixBorel_rc1ce18_1 {n m : ℕ} : BorelSpace (Matrix (Fin n) (Fin m) ℝ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin m → ℝ))
lemma goe_gaussian (n : ℕ) :
    HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ => goe g)
      (standardArrayLaw (Fin n × Fin n)) := by
  have h := coordinates_gaussian.map_fun
    (show ((Fin n × Fin n) → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) from goeCLM n)
  exact h.congr (Filter.Eventually.of_forall (goeCLM_apply n))

lemma goe_entry_covariance {n : ℕ} (hn : 0 < n) (i j k l : Fin n) :
    cov[fun g : (Fin n × Fin n) → ℝ => goe g i j, fun g => goe g k l;
        standardArrayLaw (Fin n × Fin n)] =
      ((if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) / n := by
  have hLp (a : Fin n × Fin n) := (coordinate_hasLaw a).hasGaussianLaw.memLp_two
  simp only [goe, covariance_fun_div_left, covariance_fun_div_right]
  change cov[(fun g => g (i,j)) + (fun g => g (j,i)),
    (fun g => g (k,l)) + (fun g => g (l,k)); standardArrayLaw (Fin n × Fin n)] /
      Real.sqrt (2*n) / Real.sqrt (2*n) = _
  rw [covariance_add_left (hLp _) (hLp _) ((hLp _).add (hLp _)),
    covariance_add_right (hLp _) (hLp _) (hLp _),
    covariance_add_right (hLp _) (hLp _) (hLp _)]
  simp only [coordinate_covariance, Prod.mk.injEq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (2*n) ^ 2 = 2*n := Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2*(n : ℝ)) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  rw [div_div, ← pow_two]
  rw [hs]
  have ha : (j = k ∧ i = l) ↔ (i = l ∧ j = k) := and_comm
  have hb : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
  simp only [ha, hb]
  ring

lemma coordinate_mean {ι : Type*} [Fintype ι] (i : ι) :
    (∫ g : ι → ℝ, g i ∂standardArrayLaw ι) = 0 := by
  rw [(coordinate_hasLaw i).integral_eq, integral_id_gaussianReal]

lemma goe_entry_mean {n : ℕ} (i j : Fin n) :
    (∫ g : (Fin n × Fin n) → ℝ, goe g i j ∂standardArrayLaw (Fin n × Fin n)) = 0 := by
  simp only [goe, integral_div]
  rw [integral_add (coordinate_hasLaw (i,j)).hasGaussianLaw.integrable
    (coordinate_hasLaw (j,i)).hasGaussianLaw.integrable]
  simp only [coordinate_mean, add_zero, zero_div]

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Nonempty ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma centered_sq (p : ι → ℝ) : (∑ i, centered p i^2)=(∑ i, p i^2)-
    (Fintype.card ι:ℝ)*average p^2 := by
  have hn : (Fintype.card ι:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (∑ i, p i)=(Fintype.card ι:ℝ)*average p := by
    dsimp [average]
    field_simp
  simp only [centered,sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ←Finset.sum_mul,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [hsum]
  ring
lemma centered_sq_le (p : ι → ℝ) : (∑ i, centered p i^2)≤∑ i, p i^2 := by
  rw [centered_sq]
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_RandomMatrixNet
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
namespace SKRatio.MatrixNet

lemma matrix_opNorm_le_schur {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i, ∑ j, |A i j| ≤ R) (hc : ∀ j, ∑ i, |A i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hR
  intro x y hx hy
  change inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x) y ≤ R
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, y i * ∑ j, A i j*x j) ≤ R
  simp only [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, |A i j| * ((y i)^2 + (x j)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hab : 2*|y i| *|x j| ≤ (y i)^2+(x j)^2 := by
        nlinarith [sq_nonneg (|y i|-|x j|), sq_abs (y i), sq_abs (x j)]
      have hp := mul_le_mul_of_nonneg_left hab (abs_nonneg (A i j))
      have hh : y i*(A i j*x j) ≤ |y i| *|A i j| *|x j| := by
        simpa only [abs_mul, mul_assoc] using le_abs_self (y i*(A i j*x j))
      nlinarith
    _ = ((∑ i, (y i)^2 * ∑ j, |A i j|) + ∑ j, (x j)^2 * ∑ i, |A i j|)/2 := by
      simp only [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [Finset.sum_comm (f := fun i j => |A i j| * (x j)^2)]
      simp only [← Finset.sum_mul]
      congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ ≤ ((∑ i, (y i)^2 * R) + ∑ j, (x j)^2*R)/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i) (sq_nonneg _)))
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i) (sq_nonneg _)))
    _ = R := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq,
        ← EuclideanSpace.real_norm_sq_eq, hx, hy]
      ring

lemma matrix_diagonal_opNorm_le {n : ℕ} (d : Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hd : ∀ i, |d i| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal d)‖ ≤ R := by
  apply matrix_opNorm_le_schur _ R hR
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i

end SKRatio.MatrixNet

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_ExponentialEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKRatioClock.Regression

lemma ExponentiallyRare.mono {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A B : ∀ n, Set (H n)}
    (hB : ExponentiallyRare ρ B) (hAB : ∀ᶠ n in atTop, A n ⊆ B n) :
    ExponentiallyRare ρ A := by
  obtain ⟨C,c,hC,hc,he⟩ := hB
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [he,hAB] with n hn hABn
  exact (measure_mono hABn).trans hn

lemma ExponentiallyRare.union {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    {ρ : ∀ n, Measure (H n)} {A B : ∀ n, Set (H n)}
    (hA : ExponentiallyRare ρ A) (hB : ExponentiallyRare ρ B) :
    ExponentiallyRare ρ (fun n => A n ∪ B n) := by
  obtain ⟨C,c,hC,hc,he⟩ := hA
  obtain ⟨D,d,hD,hd,hf⟩ := hB
  refine ⟨C+D,min c d,add_pos hC hD,lt_min hc hd,?_⟩
  filter_upwards [he,hf] with n hn hm
  refine (measure_union_le _ _).trans ((add_le_add hn hm).trans ?_)
  have hc' : Real.exp (-c*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by
      have := min_le_left c d
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hd' : Real.exp (-d*(n:ℝ)) ≤ Real.exp (-min c d*(n:ℝ)) :=
    Real.exp_le_exp.mpr (by
      have := min_le_right c d
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  rw [add_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc' hC.le))
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hd' hD.le))

lemma exponentiallyRare_empty {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) : ExponentiallyRare ρ (fun _ => ∅) := by
  refine ⟨1,1,by norm_num,by norm_num,Filter.Eventually.of_forall ?_⟩
  intro n
  simp only [measure_empty, zero_le]

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_ExponentialBounds
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatioClock.Regression

lemma eventually_polynomial_exp_le {a : ℝ} (ha : 0<a) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (n:ℝ)^k*exp (-a*n) ≤ exp (-(a/2)*n) := by
  have ht : Tendsto (fun n : ℕ => (a/2)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp ht).div_const ((a/2)^k)
  simp only [zero_div] at h
  have hlim : Tendsto (fun n : ℕ => (n:ℝ)^k*exp (-(a/2)*n)) atTop (𝓝 0) := by
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    simp only [Function.comp_apply,mul_pow,neg_mul]
    field_simp
  filter_upwards [hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with n hn
  calc
    _ = ((n:ℝ)^k*exp (-(a/2)*n))*exp (-(a/2)*n) := by
      rw [mul_assoc,←exp_add]
      congr 2
      ring
    _ ≤ 1*exp (-(a/2)*n) := mul_le_mul_of_nonneg_right hn.le (by positivity)
    _ = _ := one_mul _

lemma exponentiallyRare_of_polynomial {H : ℕ → Type*} [∀ n, MeasurableSpace (H n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, Set (H n))
    {C c : ℝ} (hC : 0<C) (hc : 0 < c) (k : ℕ)
    (hbound : ∀ᶠ n in atTop, ρ n (A n) ≤ ENNReal.ofReal (C*(n:ℝ)^k*exp (-c*n))) :
    ExponentiallyRare ρ A := by
  refine ⟨C,c/2,hC,by positivity,?_⟩
  filter_upwards [hbound,eventually_polynomial_exp_le hc k] with n hn hp
  refine hn.trans (ENNReal.ofReal_le_ofReal ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le

lemma exponentiallyRare_iUnion_polynomial {H I : ℕ → Type*}
    [∀ n, MeasurableSpace (H n)] [∀ n, Fintype (I n)]
    (ρ : ∀ n, Measure (H n)) (A : ∀ n, I n → Set (H n))
    {c C D : ℝ} (hc : 0 < c) (hC : 0<C) (hD : 0<D) (k : ℕ)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (I n) : ℝ) ≤ D*(n:ℝ)^k)
    (hbound : ∀ᶠ n in atTop, ∀ i, ρ n (A n i) ≤ ENNReal.ofReal (C*exp (-c*n))) :
    ExponentiallyRare ρ (fun n => ⋃ i, A n i) := by
  apply exponentiallyRare_of_polynomial ρ _ (mul_pos hD hC) hc k
  filter_upwards [hcard,hbound] with n hcard hb
  calc
    _ ≤ ∑ i, ρ n (A n i) := measure_iUnion_fintype_le (ρ n) _
    _ ≤ ∑ _i : I n, ENNReal.ofReal (C*exp (-c*n)) := Finset.sum_le_sum (fun i _ => hb i)
    _ = ENNReal.ofReal ((Fintype.card (I n):ℝ)*(C*exp (-c*n))) := by
      simp [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((D*C)*(n:ℝ)^k*exp (-c*n)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (D*(n:ℝ)^k)*(C*exp (-c*n)) := mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Gaussian_GaussianEmpirical
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
namespace SKRatioClock.Regression

lemma subgaussian_abs_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ {ω | ε ≤ |X ω|} ≤ 2 * ENNReal.ofReal (Real.exp (-ε^2/(2*(c:ℝ)))) := by
  have hu := ENNReal.ofReal_le_ofReal (hX.measure_ge_le hε)
  have hl := ENNReal.ofReal_le_ofReal (hX.neg.measure_ge_le hε)
  simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hu hl
  have hs : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    intro ω h
    simpa only [Set.mem_union, Set.mem_ofPred_eq, le_abs] using h
  calc
    _ ≤ _ := measure_mono hs
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := add_le_add hu hl
    _ = _ := (two_mul _).symm

lemma gaussian_hasSubgaussianMGF {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) : HasSubgaussianMGF X v μ where
  integrable_exp_mul t := by
    rw [← mgf_pos_iff, mgf_gaussianReal hX.map_eq]
    exact Real.exp_pos _
  mgf_le t := by
    rw [mgf_gaussianReal hX.map_eq]
    simp

end SKRatioClock.Regression

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_PlantedGOE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Matrix Matrix.Norms.Elementwise Topology
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma coupling_augmentedDisorder (β : ℝ) (g : (Fin n × Fin n) → ℝ) :
    Matrix.of (coupling (augmentedDisorder β g)) = augmented β g - Matrix.diagonal (fun i => augmented β g i i) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [coupling]
  · rcases lt_or_gt_of_ne h with hij | hij
    · simp [coupling,hij,h,augmentedDisorder]
    · simp [coupling,hij,not_lt_of_gt hij,h,augmentedDisorder,augmented,goe,add_comm]

end SKRatio.Planted

end
end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Matrices_AugmentedBounds
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyBorel _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historySecondCountable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma centered_augmentedDiagonal_hasLaw (hn : 0<n) (β : ℝ) (i : Fin n) :
    HasLaw (fun g : (Fin n × Fin n) → ℝ => β*goe g i i)
      (gaussianReal 0 (Real.toNNReal (2*β^2/(n:ℝ)))) (standardArrayLaw (Fin n × Fin n)) := by
  have hg : HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ => β*goe g i i)
      (standardArrayLaw (Fin n × Fin n)) := by
    simpa only [ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,
      smul_eq_mul,mul_comm] using (((goe_gaussian n).eval i |>.eval i).map_fun
        ((ContinuousLinearMap.id ℝ ℝ).smulRight β))
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal,integral_const_mul,goe_entry_mean,mul_zero,
    ←covariance_self hg.aemeasurable,covariance_const_mul_left,covariance_const_mul_right,
    goe_entry_covariance hn]
  congr 2
  simp only [and_self,ite_true, if_true]
  ring

lemma augmented_diagonal_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ i : Fin n, u< |augmentedDiagonal β g i|}) := by
  by_cases hb : β=0
  · apply (exponentiallyRare_empty (fun n => standardArrayLaw (Fin n × Fin n))).mono
    refine Eventually.of_forall ?_
    intro n g hg
    obtain ⟨i,hi⟩ := hg
    simp [augmentedDiagonal,augmented,hb,hu.not_gt] at hi
  have hb2 : 0<β^2 := sq_pos_of_ne_zero hb
  have hc : 0<u^2/(16*β^2) := by positivity
  have ht := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (β^2)
  have hbound : ∀ᶠ n in atTop, ∀ i : Fin n,
      standardArrayLaw (Fin n × Fin n) {g | u< |augmentedDiagonal β g i|} ≤
        ENNReal.ofReal (2*exp (-(u^2/(16*β^2))*n)) := by
    filter_upwards [eventually_gt_atTop 0,ht.eventually (gt_mem_nhds (by positivity : (0:ℝ)<u/2))]
      with n hn hm i
    have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hs := subgaussian_abs_tail (gaussian_hasSubgaussianMGF (centered_augmentedDiagonal_hasLaw hn β i))
      (u/2) (by positivity)
    have hv : (Real.toNNReal (2*β^2/(n:ℝ)) : ℝ)=2*β^2/(n:ℝ) := Real.coe_toNNReal _ (by positivity)
    have he : -(u/2)^2/(2*(2*β^2/(n:ℝ)))=-(u^2/(16*β^2))*(n:ℝ) := by field_simp; ring
    rw [hv,he,←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num)] at hs
    refine (measure_mono ?_).trans hs
    intro g hg
    change u/2 ≤ |β*goe g i i|
    have ha := abs_add_le (β*goe g i i) (β^2/(n:ℝ))
    rw [abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ))] at ha
    change u< |β*goe g i i+β^2/(n:ℝ)| at hg
    linarith
  have hh := exponentiallyRare_iUnion_polynomial (fun n => standardArrayLaw (Fin n × Fin n))
    (fun n i => {g | u< |augmentedDiagonal β g i|}) hc (by norm_num : (0:ℝ)<2)
    (D := 1) (by norm_num) 1 (Eventually.of_forall (fun n => by simp)) hbound
  apply hh.mono
  exact Eventually.of_forall (fun n g hg => mem_iUnion.mpr hg)

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinProjected
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open SKRatioClock.Regression Scalar
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma fieldProjection_apply (i j : Fin n) :
    fieldProjection n i j = (if i=j then 1 else 0)-(n:ℝ)⁻¹ := by
  simp only [fieldProjection,residualProjection,Matrix.sub_apply,Matrix.one_apply,
    Matrix.mul_apply,Matrix.transpose_apply,queryColumn,constantDirection,Fin.sum_univ_one]
  congr 1
  rw [←mul_inv_rev,←pow_two,sq_sqrt (Nat.cast_nonneg n)]

lemma fieldProjection_mulVec (p : Fin n → ℝ) :
    fieldProjection n *ᵥ p = Bins.centered p := by
  ext i
  simp only [Matrix.mulVec,dotProduct,fieldProjection_apply,sub_mul,Finset.sum_sub_distrib,
    ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true,
    ←Finset.mul_sum,Bins.centered,Bins.average,Fintype.card_fin,div_eq_mul_inv]
  ring

end SKRatio.Planted

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_Quantization_BinStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression MatrixNet Calculus
variable {n : ℕ}
attribute [local instance] Classical.propDecidable

lemma mean_constant_rows (hn : 0<n) (β : ℝ) (_ : Fin n) :
    (∑ _j : Fin n, |β^2/(n:ℝ)|)=β^2 := by
  simp only [abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ)),Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne')

end SKRatio.Bins

end

end OAI
end

section
-- module Solutions.OAIQ024_SK.SKRatio_FiniteChain_ResidualBounds
attribute [-instance] _root_.OAI.SKRatio.Observation.History.historyMeasurable _root_.OAI.SKRatio.Observation.History.historyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Planted
open Bins Scalar SKRatioClock.Regression MatrixNet Calculus
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma fieldProjection_opNorm_le_one (hn : 0<n) : euclideanOpNorm (fieldProjection n) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ)≤1)
  intro x
  change ‖WithLp.toLp 2 (fieldProjection n *ᵥ x.ofLp)‖ ≤ 1*‖x‖
  rw [fieldProjection_mulVec,one_mul]
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hs := centered_sq_le x.ofLp
  rw [←EuclideanSpace.real_norm_sq_eq x] at hs
  have ht := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (centered x.ofLp))
  nlinarith only [hs,ht,norm_nonneg x,norm_nonneg (WithLp.toLp 2 (centered x.ofLp))]

lemma projected_opNorm_le (hn : 0<n) (M : Matrix (Fin n) (Fin n) ℝ) :
    euclideanOpNorm (fieldProjection n*M*fieldProjection n) ≤ euclideanOpNorm M := by
  unfold euclideanOpNorm
  rw [map_mul,map_mul]
  apply (norm_mul_le _ _).trans
  apply (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans
  have hp := fieldProjection_opNorm_le_one hn
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (fieldProjection n)‖ ≤ 1 at hp
  calc
    _ ≤ 1*‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖*1 := by gcongr
    _ = _ := by ring

lemma fullMean_opNorm_le (β : ℝ) :
    euclideanOpNorm (fun _ _ : Fin n => β^2/(n:ℝ)) ≤ β^2 := by
  apply matrix_opNorm_le_schur _ _ (sq_nonneg β)
  all_goals
    intro i
    have hn : 0<n := Nat.zero_lt_of_lt i.isLt
    rw [mean_constant_rows hn β i]

lemma centered_augmented_opNorm_le (β : ℝ) (g : (Fin n × Fin n) → ℝ)
    {D : ℝ} (hD : 0≤D) (hd : ∀ i, |augmentedDiagonal β g i|≤D) :
    euclideanOpNorm (β • goe g) ≤
      euclideanOpNorm (coupling (augmentedDisorder β g))+D+β^2 := by
  have he : β • goe g = Matrix.of (coupling (augmentedDisorder β g))+
      Matrix.diagonal (augmentedDiagonal β g) - Matrix.of (fun _ _ : Fin n => β^2/(n:ℝ)) := by
    ext i j
    have hc := congrFun (congrFun (coupling_augmentedDisorder β g) i) j
    change coupling (augmentedDisorder β g) i j = augmented β g i j-
      Matrix.diagonal (augmentedDiagonal β g) i j at hc
    change β*goe g i j = coupling (augmentedDisorder β g) i j+
      Matrix.diagonal (augmentedDiagonal β g) i j-β^2/(n:ℝ)
    rw [hc]
    change β*goe g i j = (β*goe g i j+β^2/(n:ℝ)-_)+_-β^2/(n:ℝ)
    ring
  unfold euclideanOpNorm
  rw [he,map_sub,map_add]
  apply (norm_sub_le _ _).trans
  exact (add_le_add (norm_add_le _ _) le_rfl).trans
    (add_le_add (add_le_add le_rfl (matrix_diagonal_opNorm_le _ D hD hd)) (fullMean_opNorm_le β))

theorem residual_norm_rare_oai {β : ℝ} (hβ : 0<β) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | 2*β+2*β^2+2 <
        euclideanOpNorm (fieldProjection n*(β • goe g)*fieldProjection n)}) := by
  apply ((augmented_norm_rare hβ (by norm_num : (0:ℝ)<1)).union
    (augmented_diagonal_rare β (by norm_num : (0:ℝ)<1))).mono
  filter_upwards [eventually_gt_atTop 0] with n hn
  intro g hg
  by_contra h
  have hnot := not_or.mp h
  have hnorm : euclideanOpNorm (coupling (augmentedDisorder β g)) ≤ 2*β+β^2+1 := not_lt.mp hnot.1
  have hdiag : ∀ i : Fin n, |augmentedDiagonal β g i| ≤ 1 := by
    intro i
    exact not_lt.mp (fun hi => hnot.2 ⟨i,hi⟩)
  have hr := (projected_opNorm_le hn (β • goe g)).trans
    (centered_augmented_opNorm_le β g (by norm_num) hdiag)
  change 2*β+2*β^2+2 < _ at hg
  linarith only [hg,hr,hnorm]

end SKRatio.Planted

end

end OAI
end

theorem solution : type_of% @OAI.SKRatio.Planted.residual_norm_rare_oai := @OAI.SKRatio.Planted.residual_norm_rare_oai
