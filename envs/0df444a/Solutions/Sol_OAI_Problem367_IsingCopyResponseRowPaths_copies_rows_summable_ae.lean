-- Prove2me | solution 1 for OAI.Problem367.IsingCopyResponseRowPaths.copies_rows_summable_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:43:06.100301+00:00
-- url     : https://prove2.me/submissions/4ab880b2-9e40-4cfb-b1f4-f0f4667c2cbe

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Pair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped NNReal

namespace Problem367
namespace CavityPair

variable {ψ : ℝ → ℝ} {θ : ℝ≥0}

theorem solve_swap (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (z : ℝ × ℝ) :
    solve hψ hθ z.swap = (solve hψ hθ z).swap := by
  apply solve_eq hψ hθ
  exact ⟨(solve_spec hψ hθ z).2, (solve_spec hψ hθ z).1⟩

end CavityPair
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

lemma responseAttenuation_le_one_sub {theta : ℝ} (hθ : theta ^ 2 ≤ 1) (z : ℝ) :
    responseAttenuation theta z ≤ 1 - (1 - theta ^ 2) * Real.tanh z ^ 2 := by
  rw [responseAttenuation, div_le_iff₀ (attenuation_denominator_pos hθ z)]
  have hp : 0 ≤ theta ^ 2 * (1 - theta ^ 2) * (Real.tanh z ^ 2) ^ 2 := by
    exact mul_nonneg (mul_nonneg (sq_nonneg theta) (sub_nonneg.mpr hθ)) (sq_nonneg _)
  nlinarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Homeomorph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem cavityFromSites_eq {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    {z p : ℝ × ℝ}
    (hp : p.1 + cavityMessage theta p.2 = z.1 ∧
      p.2 + cavityMessage theta p.1 = z.2) : cavityFromSites h0 h1 z = p :=
  CavityPair.solve_eq (lipschitzWith_cavityMessage h0 h1.le) h1 hp

theorem cavityFromSites_swap {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta < 1)
    (z : ℝ × ℝ) : cavityFromSites h0 h1 z.swap = (cavityFromSites h0 h1 z).swap :=
  CavityPair.solve_swap (lipschitzWith_cavityMessage h0 h1.le) h1 z

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_Array
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.CavityArray

variable {d : ℕ} {theta : ℝ}

theorem field_reverse (h0 : 0 ≤ theta) (h1 : theta < 1)
    (H : TreeVertex d → ℝ) (v w : TreeVertex d) :
    field h0 h1 H w v = (cavityFromSites h0 h1 (H v, H w)).2 := by
  exact congrArg Prod.fst (cavityFromSites_swap h0 h1 (H v, H w))

end Problem367.CavityArray

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_LogOdds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem cavityMessage_eq_half_log_cosh_ratio (beta z : ℝ) :
    cavityMessage (Real.tanh beta) z =
      (1 / 2 : ℝ) * Real.log (Real.cosh (z + beta) / Real.cosh (z - beta)) := by
  have htheta_sq : Real.tanh beta ^ 2 ≤ 1 := (Real.tanh_sq_lt_one beta).le
  have hmem := cavityMessage_argument_mem htheta_sq z
  have hratio : (1 + Real.tanh beta * Real.tanh z) /
      (1 - Real.tanh beta * Real.tanh z) =
      Real.cosh (z + beta) / Real.cosh (z - beta) := by
    apply (div_eq_div_iff (by linarith [hmem.2]) (Real.cosh_pos (z - beta)).ne').2
    rw [Real.cosh_add, Real.cosh_sub]
    simp only [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [cavityMessage, Real.artanh_eq_half_log ⟨hmem.1.le, hmem.2.le⟩, hratio]

theorem cavityMessage_eq_log_cosh_sub (beta z : ℝ) :
    cavityMessage (Real.tanh beta) z =
      (Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2 := by
  rw [cavityMessage_eq_half_log_cosh_ratio beta,
    Real.log_div (Real.cosh_pos (z + beta)).ne' (Real.cosh_pos (z - beta)).ne']
  ring

theorem tanh_field_difference_eq (beta z : ℝ) :
    (Real.tanh (z + beta) - Real.tanh (z - beta)) / 2 =
      Real.tanh beta * (1 - Real.tanh z ^ 2) /
        (1 - Real.tanh beta ^ 2 * Real.tanh z ^ 2) := by
  have hp := ((Real.hasDerivAt_cosh (z + beta)).comp z
    ((hasDerivAt_id z).add_const beta)).log (Real.cosh_pos (z + beta)).ne'
  have hm := ((Real.hasDerivAt_cosh (z - beta)).comp z
    ((hasDerivAt_id z).sub_const beta)).log (Real.cosh_pos (z - beta)).ne'
  simp only [id_eq, mul_one, Function.comp_apply, ← Real.tanh_eq_sinh_div_cosh] at hp hm
  have h : HasDerivAt (cavityMessage (Real.tanh beta))
      ((Real.tanh (z + beta) - Real.tanh (z - beta)) / 2) z := by
    apply ((hp.sub hm).div_const 2).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun x => cavityMessage_eq_log_cosh_sub beta x
  simpa only [responseAttenuation, mul_div_assoc] using
    h.unique (hasDerivAt_cavityMessage (Real.tanh_sq_lt_one beta).le z)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FiniteChain
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367.FiniteChain

variable {A : Type*}

theorem endpoint_eq_last (n : ℕ) (a : A) (x : Fin n → A) :
    endpoint n a x = (Fin.cons a x : Fin (n+1) → A) (Fin.last n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [endpoint, ih]
    simp

variable [Fintype A]

theorem sum_cons (n : ℕ) (f : (Fin (n+1) → A) → ℝ) :
    ∑ x, f x = ∑ a, ∑ x : Fin n → A, f (Fin.cons a x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

end Problem367.FiniteChain

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InhomogeneousSpinChain
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*}

theorem weight_eq_prod (K : ℕ → A → A → ℝ) (n : ℕ)
    (a : A) (x : Fin n → A) :
    weight K n a x = ∏ i : Fin n,
      K i ((Fin.cons a x : Fin (n + 1) → A) i.castSucc) (x i) := by
  induction n generalizing K a with
  | zero => simp
  | succ n ih =>
    rw [weight, Fin.prod_univ_succ, ih]
    simp [Fin.tail]

@[simp] theorem jointWeight_cons (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (n : ℕ) (a : A) (x : Fin n → A) :
    jointWeight K w n (Fin.cons a x) = w a * weight K n a x := by
  rw [weight_eq_prod]
  simp [jointWeight]

variable [Fintype A]

theorem expectation_succ (K : ℕ → A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) :
    expectation K (n + 1) f a =
      ∑ b, K 0 a b * expectation (fun i => K (i + 1)) n f b := by
  unfold expectation
  rw [FiniteChain.sum_cons]
  simp only [weight_cons, FiniteChain.endpoint_cons, mul_assoc, Finset.mul_sum]

theorem sum_weight (K : ℕ → A → A → ℝ)
    (hK : ∀ i a, ∑ b, K i a b = 1) (n : ℕ) (a : A) :
    ∑ x : Fin n → A, weight K n a x = 1 := by
  induction n generalizing K a with
  | zero => simp
  | succ n ih =>
    rw [FiniteChain.sum_cons]
    simp only [weight_cons, ← Finset.mul_sum]
    simp only [ih (fun i => K (i + 1)) (fun i => hK (i + 1)), mul_one]
    exact hK 0 a

theorem sum_jointWeight (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (hK : ∀ i a, ∑ b, K i a b = 1) (hw : ∑ a, w a = 1) (n : ℕ) :
    ∑ x : Fin (n + 1) → A, jointWeight K w n x = 1 := by
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, ← Finset.mul_sum, sum_weight K hK, mul_one]
  exact hw

theorem sum_jointWeight_endpoints (K : ℕ → A → A → ℝ) (w f g : A → ℝ) (n : ℕ) :
    (∑ x : Fin (n + 1) → A,
      jointWeight K w n x * f (x 0) * g (x (Fin.last n))) =
    ∑ a, w a * f a * expectation K n g a := by
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, Fin.cons_zero, ← FiniteChain.endpoint_eq_last]
  apply Finset.sum_congr rfl
  intro a _
  rw [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem expectation_affine (K : ℕ → A → A → ℝ) (f : A → ℝ)
    (p q : ℕ → ℝ) (hK : ∀ i a, ∑ b, K i a b = 1)
    (hmean : ∀ i a, ∑ b, K i a b * f b = p i + q i * f a) (n : ℕ) :
    ∃ c : ℝ, ∀ a, expectation K n f a =
      c + (∏ i ∈ Finset.range n, q i) * f a := by
  induction n generalizing K p q with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih (fun i => K (i + 1))
      (fun i => p (i + 1)) (fun i => q (i + 1))
      (fun i => hK (i + 1)) (fun i => hmean (i + 1))
    let Q := ∏ i ∈ Finset.range n, q (i + 1)
    refine ⟨c + Q * p 0, ?_⟩
    intro a
    rw [expectation_succ]
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib]
    have hconst : (∑ b, K 0 a b * c) = c := by
      rw [← Finset.sum_mul, hK, one_mul]
    have hlinear : (∑ b, K 0 a b * (Q * f b)) =
        Q * (p 0 + q 0 * f a) := by
      calc
        _ = Q * ∑ b, K 0 a b * f b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by rw [hmean]
    change (∑ b, K 0 a b * c) + (∑ b, K 0 a b * (Q * f b)) = _
    rw [hconst, hlinear, Finset.prod_range_succ']
    dsimp [Q]
    ring

theorem covariance_eq_variance_mul_prod
    (K : ℕ → A → A → ℝ) (f : A → ℝ) (p q : ℕ → ℝ)
    (w : A → ℝ) (hw : ∑ a, w a = 1)
    (hK : ∀ i a, ∑ b, K i a b = 1)
    (hmean : ∀ i a, ∑ b, K i a b * f b = p i + q i * f a) (n : ℕ) :
    (∑ a, w a * f a * expectation K n f a) -
      (∑ a, w a * f a) * (∑ a, w a * expectation K n f a) =
    ((∑ a, w a * (f a) ^ 2) - (∑ a, w a * f a) ^ 2) *
      (∏ i ∈ Finset.range n, q i) := by
  obtain ⟨c, hc⟩ := expectation_affine K f p q hK hmean n
  let Q := ∏ i ∈ Finset.range n, q i
  have hfirst : (∑ a, w a * expectation K n f a) =
      c + Q * (∑ a, w a * f a) := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib]
    calc
      _ = (∑ a, w a) * c + Q * (∑ a, w a * f a) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [hw, one_mul]
  have hsecond : (∑ a, w a * f a * expectation K n f a) =
      c * (∑ a, w a * f a) + Q * (∑ a, w a * (f a) ^ 2) := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
  rw [hfirst, hsecond]
  dsimp [Q]
  ring

end Problem367.InhomogeneousChain

namespace Problem367.PosteriorChain

theorem transition_spinMean_affine (beta z : ℝ) (a : IsingSpin) :
    ∑ b, transition beta z a b * spinSign b =
      intercept beta z + slope beta z * spinSign a := by
  rw [transition_spinMean]
  cases a <;> simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one,
    ← sub_eq_add_neg, intercept, slope] <;> ring

theorem slope_eq_responseAttenuation (beta z : ℝ) :
    slope beta z = Real.tanh beta * responseAttenuation (Real.tanh beta) z := by
  simpa only [slope, responseAttenuation, mul_div_assoc] using
    tanh_field_difference_eq beta z

theorem covariance_eq_response_product (beta : ℝ) (z : ℕ → ℝ)
    (w : IsingSpin → ℝ) (hw : ∑ a, w a = 1) (n : ℕ) :
    (∑ a, w a * spinSign a *
      InhomogeneousChain.expectation (fun i => transition beta (z i)) n spinSign a) -
      (∑ a, w a * spinSign a) *
        (∑ a, w a * InhomogeneousChain.expectation
          (fun i => transition beta (z i)) n spinSign a) =
    (1 - (∑ a, w a * spinSign a) ^ 2) * Real.tanh beta ^ n *
      (∏ i ∈ Finset.range n, responseAttenuation (Real.tanh beta) (z i)) := by
  have h := InhomogeneousChain.covariance_eq_variance_mul_prod
    (fun i => transition beta (z i)) spinSign
    (fun i => intercept beta (z i)) (fun i => slope beta (z i)) w hw
    (fun i => transition_sum beta (z i))
    (fun i => transition_spinMean_affine beta (z i)) n
  simp only [spinSign_sq, mul_one, hw] at h
  rw [h]
  simp_rw [slope_eq_responseAttenuation]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range]
  ring

end Problem367.PosteriorChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_BinaryMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PosteriorChain

private theorem tanh_add_ratio (x y : ℝ) :
    Real.tanh (x + y) =
      (Real.tanh x + Real.tanh y) / (1 + Real.tanh x * Real.tanh y) := by
  have hm := cavityMessage_argument_mem (Real.tanh_sq_lt_one x).le y
  have hd : 1 + Real.tanh x * Real.tanh y ≠ 0 := by linarith [hm.1]
  apply (eq_div_iff hd).2
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp
  rw [Real.sinh_add, Real.cosh_add]
  ring

private theorem tanh_sub_ratio (x y : ℝ) :
    Real.tanh (x - y) =
      (Real.tanh x - Real.tanh y) / (1 - Real.tanh x * Real.tanh y) := by
  simpa only [sub_eq_add_neg, Real.tanh_neg, mul_neg] using tanh_add_ratio x (-y)

theorem affine_mean_eq_cavity_mean (beta z H : ℝ) :
    intercept beta z + slope beta z * Real.tanh H =
      Real.tanh (z + cavityMessage (Real.tanh beta)
        (H - cavityMessage (Real.tanh beta) z)) := by
  have htheta : Real.tanh beta ^ 2 ≤ 1 := (Real.tanh_sq_lt_one beta).le
  have hinner : Real.tanh (cavityMessage (Real.tanh beta) z) =
      Real.tanh beta * Real.tanh z :=
    Real.tanh_artanh (cavityMessage_argument_mem htheta z)
  have houter : Real.tanh (cavityMessage (Real.tanh beta)
      (H - cavityMessage (Real.tanh beta) z)) =
      Real.tanh beta * Real.tanh (H - cavityMessage (Real.tanh beta) z) :=
    Real.tanh_artanh (cavityMessage_argument_mem htheta _)
  rw [tanh_add_ratio, houter, tanh_sub_ratio H, hinner]
  unfold intercept slope
  rw [tanh_add_ratio, tanh_sub_ratio]
  have hz := cavityMessage_argument_mem (Real.tanh_sq_lt_one z).le beta
  have hh := cavityMessage_argument_mem (Real.tanh_sq_lt_one H).le
    (cavityMessage (Real.tanh beta) z)
  rw [hinner] at hh
  have hdplus : 1 + Real.tanh z * Real.tanh beta ≠ 0 := by linarith [hz.1]
  have hdminus : 1 - Real.tanh z * Real.tanh beta ≠ 0 := by linarith [hz.2]
  have hdinner : 1 - Real.tanh H * (Real.tanh beta * Real.tanh z) ≠ 0 := by
    linarith [hh.2]
  have hout := cavityMessage_argument_mem (Real.tanh_sq_lt_one z).le
    (cavityMessage (Real.tanh beta) (H - cavityMessage (Real.tanh beta) z))
  rw [houter, tanh_sub_ratio H, hinner] at hout
  have hdouter : 1 + Real.tanh z * (Real.tanh beta *
      ((Real.tanh H - Real.tanh beta * Real.tanh z) /
        (1 - Real.tanh H * (Real.tanh beta * Real.tanh z)))) ≠ 0 := by
    linarith [hout.1]
  apply (eq_div_iff hdouter).2
  have hdinner' : 1 - Real.tanh z * Real.tanh beta * Real.tanh H ≠ 0 := by
    convert hdinner using 1
    all_goals try with_reducible_and_instances rfl
    ring
  field_simp [hdplus, hdminus, hdinner, hdinner']
  ring

theorem cavityFromSites_affine_mean {beta : ℝ} (hbeta : 0 ≤ beta) (z H : ℝ) :
    cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (H, Real.artanh (intercept beta z + slope beta z * Real.tanh H)) =
        (H - cavityMessage (Real.tanh beta) z, z) := by
  apply cavityFromSites_eq
  constructor
  · ring
  · simp only [affine_mean_eq_cavity_mean, Real.artanh_tanh]

theorem cavityFromSites_affine_mean_snd {beta : ℝ} (hbeta : 0 ≤ beta) (z H : ℝ) :
    (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
      (H, Real.artanh (intercept beta z + slope beta z * Real.tanh H))).2 = z := by
  rw [cavityFromSites_affine_mean hbeta]

end Problem367.PosteriorChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

theorem tendsto_conditional_covariance_ae
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ m) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => (μ[fun x => f x * g x | ℱ n]) ω -
        (μ[f | ℱ n]) ω * (μ[g | ℱ n]) ω)
      atTop (𝓝 ((μ[fun x => f x * g x | ⨆ n, ℱ n]) ω -
        (μ[f | ⨆ n, ℱ n]) ω * (μ[g | ⨆ n, ℱ n]) ω)) := by
  filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) (fun x => f x * g x),
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f,
    tendsto_ae_condExp (μ := μ) (ℱ := ℱ) g] with ω hfg hf hg
  exact hfg.sub (hf.mul hg)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_CovarianceLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma stronglyMeasurable_posteriorCovariance (μ : Measure Ω)
    (m : MeasurableSpace Ω) (f g : Ω → ℝ) :
    StronglyMeasurable[m] (posteriorCovariance (mΩ := mΩ) μ m f g) :=
  stronglyMeasurable_condExp.sub
    (stronglyMeasurable_condExp.mul stronglyMeasurable_condExp)

theorem tendsto_ae_posteriorCovariance (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℕ mΩ) (f g : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorCovariance μ (F n) f g ω) atTop
      (𝓝 (posteriorCovariance μ (⨆ n, F n) f g ω)) := by
  exact tendsto_conditional_covariance_ae μ F f g

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LeafDeletion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem inducedEdges_eq_insert_erase_of_unique_lower_neighbor
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hleaf : ∀ x ∈ D, treeAdj v x → x = p) :
    inducedEdges D = insert (p, v) (inducedEdges (D.erase v)) := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  simp only [inducedEdges, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_insert, Prod.mk.injEq, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hx, hy⟩, hxy, hlen⟩
    have hxv : x ≠ v := by
      intro h
      subst x
      have hyp := hleaf y hy hxy
      subst y
      omega
    by_cases hyv : y = v
    · exact Or.inl ⟨hleaf x hx ((hyv ▸ hxy).elim Or.inr Or.inl), hyv⟩
    · exact Or.inr ⟨⟨⟨hxv, hx⟩, ⟨hyv, hy⟩⟩, hxy, hlen⟩
  · rintro (⟨rfl, rfl⟩ | ⟨⟨⟨_, hx⟩, ⟨_, hy⟩⟩, hxy, hlen⟩)
    · exact ⟨⟨hp, hv⟩, hpv, hplen⟩
    · exact ⟨⟨hx, hy⟩, hxy, hlen⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_FieldL2Limit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

open PlantedSymmetry

open CavityFieldLimit

theorem HasFreeIsingLaw.exhaustionSiteField_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n))
    (hex : ∀ u, ∃ n, u ∈ D n) (v : TreeVertex d) (hv : ∀ n, v ∈ D n)
    (t : ℝ≥0) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => finiteSiteField beta (D n) ⟨v, hv n⟩ (observation t p))
        atTop (𝓝 (Real.artanh (infiniteGibbsSpinMean beta v (observation t p)))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hb (n : ℕ) := hμ.finiteObservation_spin_tanh_bounds hbeta (D n) (hconn n) t ⟨v, hv n⟩
  have hlim := tendsto_posterior_fields_ae
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => observation t p v) ((d : ℝ) * beta) hb
  rw [finiteObservationFiltration_iSup D hD hex t] at hlim
  have hce (n : ℕ) := hμ.finiteObservation_condExp (D n) (hconn n) t
    (fun eta => spinSign (eta ⟨v, hv n⟩))
  filter_upwards [hlim, ae_all_iff.mpr hce,
    hμ.infiniteGibbsSpinMean_eq_posterior t v] with p hp hce hinf
  convert hp.2.2 using 1
  · ext n
    exact congrArg Real.artanh (hce n).symm
  · exact congrArg (fun x : ℝ => 𝓝 (Real.artanh x)) hinf

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_DiscrepancyRowEnergy
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Problem367.DiscrepancyEnergy

theorem sq_row_integrable_of_summable_integrals
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {μ : Measure Ω}
    {c : ι → Ω → ℝ}
    (hc : ∀ i, Integrable (fun ω => (c i ω) ^ 2) μ)
    (hs : Summable (fun i => ∫ ω, (c i ω) ^ 2 ∂μ)) :
    (∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2)) ∧
      Integrable (fun ω => ∑' i, (c i ω) ^ 2) μ := by
  have hm (i : ι) : AEMeasurable (fun ω => ENNReal.ofReal ((c i ω) ^ 2)) μ :=
    (hc i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ ω, ∑' i, ENNReal.ofReal ((c i ω) ^ 2) ∂μ) < ∞ := by
    rw [lintegral_tsum hm]
    calc
      (∑' i, ∫⁻ ω, ENNReal.ofReal ((c i ω) ^ 2) ∂μ) =
          ∑' i, ENNReal.ofReal (∫ ω, (c i ω) ^ 2 ∂μ) := by
        apply tsum_congr
        intro i
        exact (ofReal_integral_eq_lintegral_ofReal (hc i)
          (Eventually.of_forall (fun ω => sq_nonneg (c i ω)))).symm
      _ < ∞ := hs.tsum_ofReal_lt_top
  have hAe : ∀ᵐ ω ∂μ, Summable (fun i => (c i ω) ^ 2) := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin.ne] with ω hω
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using
      ENNReal.summable_toReal hω.ne
  refine ⟨hAe, ?_⟩
  have hI := integrable_toReal_of_lintegral_ne_top (AEMeasurable.tsum hm) hfin.ne
  simpa only [ENNReal.tsum_toReal_eq (fun i => ENNReal.ofReal_ne_top),
    ENNReal.toReal_ofReal (sq_nonneg _)] using hI

end Problem367.DiscrepancyEnergy

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_FiniteLeafCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.LeafGibbs

theorem expectation_eq_mean_zero {A : Type*} [Fintype A] (E f : A → ℝ) :
    expectation E f = FinitePosterior.mean E (fun _ => 0) f 0 := by
  simp only [expectation, FinitePosterior.mean, FinitePosterior.partition,
    FinitePosterior.weight, zero_mul, add_zero]

lemma expectation_add {A : Type*} [Fintype A] (E f g : A → ℝ) :
    expectation E (fun a => f a + g a) = expectation E f + expectation E g := by
  simp only [expectation, add_mul, Finset.sum_add_distrib, add_div]

lemma expectation_const_mul {A : Type*} [Fintype A] (E f : A → ℝ) (c : ℝ) :
    expectation E (fun a => c * f a) = c * expectation E f := by
  simp only [expectation, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

lemma expectation_const {A : Type*} [Fintype A] [Nonempty A] (E : A → ℝ) (c : ℝ) :
    expectation E (fun _ => c) = c := by
  have hpos : 0 < ∑ a, Real.exp (E a) :=
    Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [expectation, ← Finset.mul_sum]
  exact mul_div_cancel_right₀ c hpos.ne'

lemma spin_exponential_mean (z : ℝ) :
    (∑ l : IsingSpin, spinSign l * Real.exp (z * spinSign l)) =
      Real.tanh z * ∑ l : IsingSpin, Real.exp (z * spinSign l) := by
  simp only [sum_isingSpin, spinSign_neg, spinSign_pos, mul_neg_one,
    mul_one, neg_one_mul, one_mul]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hpos : Real.exp z + Real.exp (-z) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  field_simp
  ring

lemma tanh_leaf_affine (beta y : ℝ) (s : IsingSpin) :
    Real.tanh (y + beta * spinSign s) =
      (Real.tanh (y + beta) + Real.tanh (y - beta)) / 2 +
        (Real.tanh beta * responseAttenuation (Real.tanh beta) y) * spinSign s := by
  have hs : Real.tanh beta * responseAttenuation (Real.tanh beta) y =
      (Real.tanh (y + beta) - Real.tanh (y - beta)) / 2 := by
    simpa only [responseAttenuation, mul_div_assoc] using (tanh_field_difference_eq beta y).symm
  rw [hs]
  cases s <;> simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one, ← sub_eq_add_neg] <;> ring

theorem expectation_mul_leaf_eq {A : Type*} [Fintype A]
    (E f : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    expectation (energy E parent beta y) (fun s => f s.1 * spinSign s.2) =
    expectation (energy E parent beta y)
      (fun s => f s.1 * Real.tanh (y + beta * spinSign (parent s.1))) := by
  unfold expectation
  congr 1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  have he (l : IsingSpin) : energy E parent beta y (a, l) =
      E a + (y + beta * spinSign (parent a)) * spinSign l := by
    unfold energy
    ring
  simp_rw [he]
  simp only [Real.exp_add]
  calc
    _ = (f a * Real.exp (E a)) *
        ∑ l : IsingSpin, spinSign l *
          Real.exp ((y + beta * spinSign (parent a)) * spinSign l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = _ := by
      rw [spin_exponential_mean, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      ring

theorem expectation_mul_leaf_affine {A : Type*} [Fintype A]
    (E f : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    expectation (energy E parent beta y) (fun s => f s.1 * spinSign s.2) =
      ((Real.tanh (y + beta) + Real.tanh (y - beta)) / 2) *
        expectation (energy E parent beta y) (fun s => f s.1) +
      (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
        expectation (energy E parent beta y) (fun s => f s.1 * spinSign (parent s.1)) := by
  rw [expectation_mul_leaf_eq]
  simp_rw [tanh_leaf_affine]
  have he : (fun s : A × IsingSpin => f s.1 *
      ((Real.tanh (y + beta) + Real.tanh (y - beta)) / 2 +
        (Real.tanh beta * responseAttenuation (Real.tanh beta) y) * spinSign (parent s.1))) =
      (fun s => ((Real.tanh (y + beta) + Real.tanh (y - beta)) / 2) * f s.1 +
        (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
          (f s.1 * spinSign (parent s.1))) := by
    funext s
    ring
  rw [he, expectation_add, expectation_const_mul, expectation_const_mul]

theorem covariance_leaf_eq_mul_parent {A : Type*} [Fintype A] [Nonempty A]
    (E f : A → ℝ) (parent : A → IsingSpin) (beta y : ℝ) :
    covariance (energy E parent beta y) (fun s => f s.1) (fun s => spinSign s.2) =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) y) *
        covariance (energy E parent beta y) (fun s => f s.1)
          (fun s => spinSign (parent s.1)) := by
  let : Nonempty IsingSpin := ⟨.neg⟩
  have hmean := expectation_mul_leaf_affine E (fun _ => 1) parent beta y
  simp only [one_mul, expectation_const, mul_one] at hmean
  unfold covariance
  rw [expectation_mul_leaf_affine, hmean]
  ring

end Problem367.LeafGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_NormalizedResponseLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma stronglyMeasurable_posteriorResponse (μ : Measure Ω)
    (m : MeasurableSpace Ω) (f g : Ω → ℝ) :
    StronglyMeasurable[m] (posteriorResponse (mΩ := mΩ) μ m f g) :=
  (stronglyMeasurable_posteriorCovariance (mΩ := mΩ) μ m f g).div
    (stronglyMeasurable_const.sub (stronglyMeasurable_condExp.pow 2))

theorem tendsto_ae_posteriorResponse
    (μ : Measure Ω) [IsFiniteMeasure μ] (F : Filtration ℕ mΩ)
    (f g : Ω → ℝ)
    (hinterior : ∀ᵐ ω ∂μ, μ[f | ⨆ n, F n] ω ∈ Set.Ioo (-1 : ℝ) 1) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => posteriorResponse μ (F n) f g ω) atTop
      (𝓝 (posteriorResponse μ (⨆ n, F n) f g ω)) := by
  filter_upwards [tendsto_ae_posteriorCovariance μ F f g,
    tendsto_ae_condExp (μ := μ) (ℱ := F) f, hinterior] with ω hc hm hi
  have hden : 1 - (μ[f | ⨆ n, F n] ω) ^ 2 ≠ 0 := by
    have hsq : (μ[f | ⨆ n, F n] ω) ^ 2 < 1 := by
      nlinarith [mul_pos (show 0 < 1 - μ[f | ⨆ n, F n] ω by linarith [hi.2])
        (show 0 < 1 + μ[f | ⨆ n, F n] ω by linarith [hi.1])]
    exact ne_of_gt (sub_pos.mpr hsq)
  exact hc.div (tendsto_const_nhds.sub (hm.pow 2)) hden

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ProgressiveIsingCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry

local instance progressiveIsingCovarianceNonemptySpin : Nonempty IsingSpin := ⟨.neg⟩

lemma pairExhaustion_monotone {d : ℕ} (v w : TreeVertex d) :
    Monotone (pairExhaustion v w) := by
  intro n m hnm
  exact connectedExhaustion_monotone v (Nat.add_le_add_right hnm _)

lemma pairExhaustion_connected {d : ℕ} (v w : TreeVertex d) (n : ℕ) :
    ConnectedFinset (pairExhaustion v w n) := connectedExhaustion_connected v _

lemma exists_mem_pairExhaustion {d : ℕ} (v w u : TreeVertex d) :
    ∃ n, u ∈ pairExhaustion v w n := by
  obtain ⟨n, hn⟩ := (eventually_mem_connectedExhaustion v u).exists
  exact ⟨n, connectedExhaustion_monotone v (Nat.le_add_right n _) hn⟩

lemma continuous_finiteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) (n : ℕ) :
    Continuous (finiteGibbsPairMean beta v w n) := by
  apply (FinitePosterior.continuous_fieldMean _ _ _).comp
  exact continuous_pi (fun u => continuous_apply u.1)

lemma measurable_infiniteGibbsPairMean {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsPairMean beta v w) := by
  have hm : StronglyMeasurable (fun y =>
      limUnder atTop (fun n => finiteGibbsPairMean beta v w n y)) :=
    StronglyMeasurable.limUnder
      (fun n => (continuous_finiteGibbsPairMean beta v w n).measurable.stronglyMeasurable)
  exact measurable_const.max (measurable_const.min hm.measurable)

lemma spinSign_pair_norm_le_one {d : ℕ} (v w : TreeVertex d)
    (sigma : TreeVertex d → IsingSpin) : ‖spinSign (sigma v) * spinSign (sigma w)‖ ≤ 1 := by
  cases hv : sigma v <;> cases hw : sigma w <;> norm_num [spinSign, hv, hw]

theorem HasFreeIsingLaw.infiniteGibbsPairMean_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsPairMean beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hce (n : ℕ) := hμ.finiteObservation_condExp (pairExhaustion v w n)
    (pairExhaustion_connected v w n) t
    (fun eta => spinSign (eta ⟨v, mem_pairExhaustion_left v w n⟩) *
      spinSign (eta ⟨w, mem_pairExhaustion_right v w n⟩))
  have hlim := tendsto_ae_condExp (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (ℱ := finiteObservationFiltration (pairExhaustion v w)
      (pairExhaustion_monotone v w) t)
    (fun p => spinSign (p.1 v) * spinSign (p.1 w))
  rw [finiteObservationFiltration_iSup (pairExhaustion v w)
    (pairExhaustion_monotone v w) (exists_mem_pairExhaustion v w) t] at hlim
  have hb := ae_bdd_norm_condExp_of_ae_bdd_norm
    (μ := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (m := observationSigma (TreeVertex d) t)
    (Eventually.of_forall (fun p => spinSign_pair_norm_le_one v w p.1))
  filter_upwards [ae_all_iff.mpr hce, hlim, hb] with p hp hlim hb
  have hseq : Tendsto (fun n => finiteGibbsPairMean beta v w n (observation t p)) atTop
      (𝓝 ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) * spinSign (p.1 w) |
        observationSigma (TreeVertex d) t] p)) := by
    convert hlim using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    exact (hp n).symm
  change max (-1) (min 1 (limUnder atTop _)) = _
  rw [hseq.limUnder_eq, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]

lemma measurable_infiniteGibbsCovariance {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsCovariance beta v w) :=
  (measurable_infiniteGibbsPairMean beta v w).sub
    ((measurable_infiniteGibbsSpinMean beta v).mul
      (measurable_infiniteGibbsSpinMean beta w))

theorem HasFreeIsingLaw.infiniteGibbsCovariance_eq_posterior {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (t : ℝ≥0) (v w : TreeVertex d) :
    (fun p => infiniteGibbsCovariance beta v w (observation t p)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      posteriorCovariance (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (observationSigma (TreeVertex d) t)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) := by
  filter_upwards [hμ.infiniteGibbsPairMean_eq_posterior t v w,
    hμ.infiniteGibbsSpinMean_eq_posterior t v,
    hμ.infiniteGibbsSpinMean_eq_posterior t w] with p hp hv hw
  exact congrArg₂ (fun a b : ℝ => a - b) hp (congrArg₂ (· * ·) hv hw)

lemma measurable_infiniteGibbsResponse {d : ℕ} (beta : ℝ) (v w : TreeVertex d) :
    Measurable (infiniteGibbsResponse beta v w) :=
  (measurable_infiniteGibbsCovariance beta v w).div
    (measurable_const.sub ((measurable_infiniteGibbsSpinMean beta v).pow_const 2))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ShiftedFieldVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {G : Ω → ℝ} {beta : ℝ}

lemma continuous_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Continuous (responseAttenuation theta) := by
  have ht := lipschitzWith_tanh_response.continuous
  exact (continuous_const.sub (ht.pow 2)).div
    (continuous_const.sub (continuous_const.mul (ht.pow 2)))
    (fun z => ne_of_gt (attenuation_denominator_pos hθ z))

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_ChainMarginals
attribute [-instance] _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*} [Fintype A]

theorem sum_advance (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (hK : ∀ a, ∑ b, K 0 a b = 1) (hw : ∑ a, w a = 1) :
    ∑ b, advance K w b = 1 := by
  unfold advance
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK, mul_one]
  exact hw

theorem sum_jointWeight_tail (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (n : ℕ) (F : (Fin (n + 1) → A) → ℝ) :
    (∑ x : Fin (n + 2) → A, jointWeight K w (n + 1) x * F (Fin.tail x)) =
      ∑ x : Fin (n + 1) → A,
        jointWeight (fun i => K (i + 1)) (advance K w) n x * F x := by
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, weight, Fin.tail_cons]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [jointWeight, advance, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [weight_eq_prod]
  simp only [Fin.cons_self_tail, Fin.tail]
  ring

theorem coordinateMean_succ (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (n : ℕ) (i : Fin (n + 1)) :
    coordinateMean K w f (n + 1) i.succ =
      coordinateMean (fun j => K (j + 1)) (advance K w) f n i := by
  exact sum_jointWeight_tail K w n (fun x => f (x i))

theorem coordinateMean_zero (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (hK : ∀ i a, ∑ b, K i a b = 1) (n : ℕ) :
    coordinateMean K w f n 0 = ∑ a, w a * f a := by
  unfold coordinateMean
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, Fin.cons_zero]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ x, w a * weight K n a x * f a) =
        w a * f a * ∑ x, weight K n a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [sum_weight K hK, mul_one]

theorem coordinateMean_affine (K : ℕ → A → A → ℝ) (w f : A → ℝ)
    (p q : ℕ → ℝ) (hw : ∑ a, w a = 1)
    (hK : ∀ i a, ∑ b, K i a b = 1)
    (hmean : ∀ i a, ∑ b, K i a b * f b = p i + q i * f a)
    (n : ℕ) (i : Fin n) :
    coordinateMean K w f n i.succ =
      p i + q i * coordinateMean K w f n i.castSucc := by
  induction n generalizing K w p q with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [coordinateMean_succ, coordinateMean_zero _ _ _ (fun i => hK (i + 1)),
        show (Fin.castSucc (0 : Fin (n + 1))) = 0 by rfl,
        coordinateMean_zero K w f hK]
      simp only [Fin.val_zero]
      unfold advance
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      calc
        (∑ a, ∑ b, w a * K 0 a b * f b) =
            ∑ a, w a * (p 0 + q 0 * f a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [← hmean 0 a, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw, one_mul]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring
    · rw [coordinateMean_succ, show j.succ.castSucc = j.castSucc.succ by rfl,
        coordinateMean_succ]
      exact ih (fun k => K (k + 1)) (advance K w)
        (fun k => p (k + 1)) (fun k => q (k + 1))
        (sum_advance K w (hK 0) hw) (fun k => hK (k + 1))
        (fun k => hmean (k + 1)) j

end Problem367.InhomogeneousChain

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathCylinders
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
namespace Problem367
namespace ConnectedHull

theorem connected_vertices {d : ℕ} (v : TreeVertex d) :
    ConnectedFinset (vertices v) := by
  have hmem : ∀ n ≤ v.1.length, takeVertex v n ∈ vertices v :=
    fun _ hn => prefix_mem_vertices v hn
  refine ⟨⟨root d, by simpa using hmem 0 (Nat.zero_le _)⟩, ?_⟩
  intro u hu w hw
  obtain ⟨i, hi, rfl⟩ := mem_vertices.mp hu
  obtain ⟨j, hj, rfl⟩ := mem_vertices.mp hw
  exact (prefix_paths (vertices v) v hmem hi).2.trans
    (prefix_paths (vertices v) v hmem hj).1

theorem pathEdge_injective {d : ℕ} (v : TreeVertex d) :
    Function.Injective (pathEdge v) := by
  intro i j h
  have hi := path_injective v (congrArg Prod.fst h)
  exact Fin.ext (congrArg (fun x : Fin (v.1.length+1) => x.val) hi)

theorem vertices_eq_image_path {d : ℕ} (v : TreeVertex d) :
    vertices v = Finset.univ.image (path v) := by
  classical
  ext u
  simp only [mem_vertices, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, hn, heq⟩
    exact ⟨⟨n, by omega⟩, heq⟩
  · rintro ⟨i, heq⟩
    exact ⟨i, by omega, heq⟩

theorem inducedEdges_vertices {d : ℕ} (v : TreeVertex d) :
    inducedEdges (vertices v) = Finset.univ.image (pathEdge v) := by
  classical
  ext e
  rcases e with ⟨u,w⟩
  constructor
  · intro he
    obtain ⟨hmem, hadj, hlt⟩ := Finset.mem_filter.mp he
    obtain ⟨hu,hw⟩ := Finset.mem_product.mp hmem
    obtain ⟨i,hi,rfl⟩ := mem_vertices.mp hu
    obtain ⟨j,hj,rfl⟩ := mem_vertices.mp hw
    have hij : j = i+1 := by
      rcases hadj with ⟨c,hc⟩ | ⟨c,hc⟩
      · have hl := congrArg List.length hc
        simpa only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] using hl
      · have hl := congrArg List.length hc
        simp only [List.length_append, List.length_singleton,
          prefix_length_eq v hi, prefix_length_eq v hj] at hl
        simp only [prefix_length_eq v hi, prefix_length_eq v hj] at hlt
        omega
    subst j
    exact Finset.mem_image.mpr ⟨⟨i, by omega⟩, Finset.mem_univ _, rfl⟩
  · intro he
    obtain ⟨i,-,hei⟩ := Finset.mem_image.mp he
    rw [←hei]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩, ?_, ?_⟩
    · exact prefix_mem_vertices v (Nat.le_of_lt i.isLt)
    · exact prefix_mem_vertices v (Nat.succ_le_of_lt i.isLt)
    · exact prefix_adj v i.isLt
    · change (takeVertex v i.val).1.length < (takeVertex v (i.val+1)).1.length
      rw [prefix_length_eq v (Nat.le_of_lt i.isLt),
        prefix_length_eq v (Nat.succ_le_of_lt i.isLt)]
      omega

end ConnectedHull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_PairCorrelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem reducedWordDistance_cons_ne {α : Type*} [DecidableEq α]
    {a b : α} (hab : a ≠ b) (u v : List α) :
    reducedWordDistance (a::u) (b::v) = u.length + v.length + 2 := by
  simp only [reducedWordDistance, ite_eq_right hab]

theorem reducedWordDistance_move_head {α : Type*} [DecidableEq α]
    (a b : α) (u v : List α) (hab : a ≠ b)
    (hu : List.IsChain (fun x y : α => x ≠ y) (a::u)) :
    reducedWordDistance u (a::b::v) = reducedWordDistance (a::u) (b::v) := by
  rw [reducedWordDistance_cons_ne hab]
  cases u with
  | nil => simp
  | cons c u =>
    have hac : a ≠ c := (List.isChain_cons_cons.mp hu).1
    rw [reducedWordDistance_cons_ne hac.symm]
    simp only [List.length_cons]
    omega

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_RadialSummability
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem summable_radial_iff (d : ℕ) (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    Summable (fun v : TreeVertex d => f v.1.length) ↔
      Summable (fun n : ℕ => (Fintype.card (TreeShell d n) : ℝ) * f n) := by
  rw [← (treeShellSigmaEquiv d).summable_iff]
  change Summable (fun s : Σ n : ℕ, TreeShell d n => f s.2.1.1.length) ↔ _
  rw [summable_sigma_of_nonneg
    (f := fun s : Σ n : ℕ, TreeShell d n => f s.2.1.1.length)
    (fun s => hf s.2.1.1.length)]
  simp only [tsum_treeShell_radial]
  exact and_iff_right (fun _ => (hasSum_fintype _).summable)

theorem tsum_radial (d : ℕ) (f : ℕ → ℝ)
    (hf : Summable (fun v : TreeVertex d => f v.1.length)) :
    (∑' v : TreeVertex d, f v.1.length) =
      ∑' n : ℕ, (Fintype.card (TreeShell d n) : ℝ) * f n := by
  have hs := (treeShellSigmaEquiv d).summable_iff.mpr hf
  calc
    (∑' v : TreeVertex d, f v.1.length) =
        ∑' s : Σ n : ℕ, TreeShell d n, f s.2.1.1.length :=
      ((treeShellSigmaEquiv d).tsum_eq (fun v : TreeVertex d => f v.1.length)).symm
    _ = ∑' n : ℕ, ∑' v : TreeShell d n, f v.1.1.length := hs.tsum_sigma
    _ = _ := by simp only [tsum_treeShell_radial]

theorem summable_geometric_radial (d : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hbranch : (d - 1 : ℕ) * q < 1) :
    Summable (fun v : TreeVertex d => q ^ v.1.length) := by
  apply (summable_radial_iff d (fun n => q ^ n) (fun _ => pow_nonneg hq _)).mpr
  apply (summable_nat_add_iff 1).mp
  have hgeom : Summable (fun n : ℕ => ((d - 1 : ℕ) * q) ^ n) :=
    summable_geometric_of_lt_one (mul_nonneg (Nat.cast_nonneg _) hq) hbranch
  have h := hgeom.mul_left ((d : ℝ) * q)
  refine h.congr fun n => ?_
  simp only [card_treeShell_succ, Nat.cast_mul, Nat.cast_pow, pow_succ, mul_pow]
  ring

theorem tsum_geometric_radial (d : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hbranch : (d - 1 : ℕ) * q < 1) :
    (∑' v : TreeVertex d, q ^ v.1.length) =
      1 + (d : ℝ) * q / (1 - (d - 1 : ℕ) * q) := by
  have hrad := summable_geometric_radial d hq hbranch
  rw [tsum_radial d (fun n => q ^ n) hrad]
  have hs := (summable_radial_iff d (fun n => q ^ n) (fun _ => pow_nonneg hq _)).mp hrad
  rw [hs.tsum_eq_zero_add]
  simp only [card_treeShell_zero, Nat.cast_one, pow_zero, one_mul]
  have hterm (n : ℕ) :
      (Fintype.card (TreeShell d (n + 1)) : ℝ) * q ^ (n + 1) =
        ((d : ℝ) * q) * (((d - 1 : ℕ) : ℝ) * q) ^ n := by
    simp only [card_treeShell_succ, Nat.cast_mul, Nat.cast_pow, pow_succ, mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (mul_nonneg (Nat.cast_nonneg _) hq) hbranch]
  rw [div_eq_mul_inv]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SmallBall
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

namespace Problem367

theorem gaussianPDFReal_le_peak (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ := by
  unfold gaussianPDFReal
  have hexp : Real.exp (-(x - m) ^ 2 / (2 * v)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
  calc
    _ ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := mul_one _

theorem gaussianReal_le_peak_mul_volume
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal m v s ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) * volume s := by
  rw [gaussianReal_apply m hv s]
  calc
    _ ≤ ∫⁻ _ in s, ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_peak m v x)
    _ = _ := by simp

theorem gaussianReal_Icc_le
    (m a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal m v (Set.Icc a b) ≤
      ENNReal.ofReal ((b - a) / Real.sqrt (2 * Real.pi * v)) := by
  have h := gaussianReal_le_peak_mul_volume m hv (Set.Icc a b)
  rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)] at h
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem gaussianReal_abs_le
    (m ε : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal m v {x | |x| ≤ ε} ≤
      ENNReal.ofReal (2 * ε / Real.sqrt (2 * Real.pi * v)) := by
  have hset : {x : ℝ | |x| ≤ ε} = Set.Icc (-ε) ε := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  rw [hset]
  convert gaussianReal_Icc_le m (-ε) ε hv using 2
  all_goals try with_reducible_and_instances rfl
  ring

theorem gaussianReal_abs_le_of_variance_ge
    (m : ℝ) {ε : ℝ} (hε : 0 ≤ ε) {δ v : ℝ≥0}
    (hδ : 0 < δ) (hδv : δ ≤ v) :
    gaussianReal m v {x | |x| ≤ ε} ≤
      ENNReal.ofReal (2 * ε / Real.sqrt (2 * Real.pi * δ)) := by
  have hv : v ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hδv)
  apply (gaussianReal_abs_le m ε hv).trans
  apply ENNReal.ofReal_le_ofReal
  have hsqrt : Real.sqrt (2 * Real.pi * (δ : ℝ)) ≤
      Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hδv) (by positivity)
  apply div_le_div_of_nonneg_left (by positivity) _ hsqrt
  apply Real.sqrt_pos.mpr
  exact mul_pos (by positivity) (by exact_mod_cast hδ)

lemma gaussianSmallRadius_pos {δ : ℝ≥0} (hδ : 0 < δ) :
    0 < gaussianSmallRadius δ := by
  unfold gaussianSmallRadius
  positivity

lemma gaussianReal_smallBall_le_half
    (m : ℝ) {δ v : ℝ≥0} (hδ : 0 < δ) (hδv : δ ≤ v) :
    gaussianReal m v {x | |x| ≤ gaussianSmallRadius δ} ≤ (1 / 2 : ℝ≥0∞) := by
  have h := gaussianReal_abs_le_of_variance_ge m
    (gaussianSmallRadius_pos hδ).le hδ hδv
  have hs : Real.sqrt (2 * Real.pi * (δ : ℝ)) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    exact mul_pos (by positivity) (by exact_mod_cast hδ)
  have hc : 2 * gaussianSmallRadius δ / Real.sqrt (2 * Real.pi * δ) = (1 / 2 : ℝ) := by
    unfold gaussianSmallRadius
    field_simp
    ring
  rw [hc] at h
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  simpa only [hhalf] using h

theorem integral_le_one_sub_half_gap
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} {s : Set Ω} {c : ℝ}
    (hf : Integrable f P) (hs : MeasurableSet s) (hc : 0 ≤ c)
    (hupper : ∀ᵐ x ∂P, f x ≤ 1)
    (houtside : ∀ᵐ x ∂P, x ∉ s → f x ≤ 1 - c)
    (hmass : P s ≤ (1 / 2 : ℝ≥0∞)) :
    ∫ x, f x ∂P ≤ 1 - c / 2 := by
  have hsreal : P.real s ≤ 1 / 2 := by
    change (P s).toReal ≤ 1 / 2
    have h := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ∞) hmass
    simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using h
  have hi : Integrable (fun x => (1 - c) + s.indicator (fun _ => c) x) P :=
    (integrable_const _).add ((integrable_const _).indicator hs)
  have hvalue : (∫ x, (1 - c) + s.indicator (fun _ => c) x ∂P) =
      1 - c + P.real s * c := by
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hs),
      integral_const, integral_indicator_const _ hs]
    simp
  have hle : ∫ x, f x ∂P ≤ ∫ x, (1 - c) + s.indicator (fun _ => c) x ∂P := by
    apply integral_mono_ae hf hi
    filter_upwards [hupper, houtside] with x hx ho
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]
      linarith
    · simpa only [Set.indicator_of_notMem hxs, add_zero] using ho hxs
  rw [hvalue] at hle
  nlinarith

theorem integral_gaussian_le_one_sub_half_gap
    (m : ℝ) {δ v : ℝ≥0} (hδ : 0 < δ) (hδv : δ ≤ v)
    {f : ℝ → ℝ} {c : ℝ} (hf : Integrable f (gaussianReal m v)) (hc : 0 ≤ c)
    (hupper : ∀ x, f x ≤ 1)
    (houtside : ∀ x, gaussianSmallRadius δ < |x| → f x ≤ 1 - c) :
    ∫ x, f x ∂gaussianReal m v ≤ 1 - c / 2 := by
  apply integral_le_one_sub_half_gap (gaussianReal m v) hf
    (measurableSet_le measurable_id.abs measurable_const) hc
    (Filter.Eventually.of_forall hupper)
  · exact Filter.Eventually.of_forall fun x hx => houtside x (lt_of_not_ge hx)
  · exact gaussianReal_smallBall_le_half m hδ hδv

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_Attenuation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
namespace GaussianAttenuation

private lemma tanh_strictMono : StrictMono Real.tanh := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_tanh_response x).deriv]
  exact sub_pos.mpr (Real.tanh_sq_lt_one x)

private lemma tanh_abs (x : ℝ) : Real.tanh |x| = |Real.tanh x| := by
  rcases le_total 0 x with hx | hx
  · have ht : 0 ≤ Real.tanh x := by
      simpa only [Real.tanh_zero] using tanh_strictMono.monotone hx
    rw [abs_of_nonneg hx, abs_of_nonneg ht]
  · have ht : Real.tanh x ≤ 0 := by
      simpa only [Real.tanh_zero] using tanh_strictMono.monotone hx
    rw [abs_of_nonpos hx, Real.tanh_neg, abs_of_nonpos ht]

lemma attenuation_sq_le_one {θ : ℝ} (hθ : θ ^ 2 ≤ 1) (x : ℝ) :
    responseAttenuation θ x ^ 2 ≤ 1 := by
  have hpos := responseAttenuation_pos hθ x
  have hle := responseAttenuation_le_one hθ x
  nlinarith

lemma integrable_attenuation_sq (m : ℝ) (v : ℝ≥0) {θ : ℝ} (hθ : θ ^ 2 ≤ 1) :
    Integrable (fun x => responseAttenuation θ x ^ 2) (gaussianReal m v) := by
  have hm : Measurable (fun x => responseAttenuation θ x ^ 2) := by
    simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
    fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact attenuation_sq_le_one hθ x

theorem integral_attenuation_sq_le
    {θ : ℝ} (hθ : θ ^ 2 < 1) (m : ℝ) {δ v : ℝ≥0}
    (hδ : 0 < δ) (hδv : δ ≤ v) :
    ∫ x, responseAttenuation θ x ^ 2 ∂gaussianReal m v ≤
      1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2 := by
  apply integral_gaussian_le_one_sub_half_gap m hδ hδv
    (integrable_attenuation_sq m v hθ.le)
  · exact mul_nonneg (sub_nonneg.mpr hθ.le) (sq_nonneg _)
  · exact attenuation_sq_le_one hθ.le
  · intro x hx
    have ht0 : 0 ≤ Real.tanh (gaussianSmallRadius δ) := by
      simpa only [Real.tanh_zero] using
        tanh_strictMono.monotone (gaussianSmallRadius_pos hδ).le
    have ht : Real.tanh (gaussianSmallRadius δ) ≤ |Real.tanh x| := by
      rw [← tanh_abs]
      exact tanh_strictMono.monotone hx.le
    have hsq : Real.tanh (gaussianSmallRadius δ) ^ 2 ≤ Real.tanh x ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ ht0 (abs_nonneg (Real.tanh x))).mpr ht
    have hmul := mul_le_mul_of_nonneg_left hsq (sub_nonneg.mpr hθ.le)
    have hpos := responseAttenuation_pos hθ.le x
    have hone := responseAttenuation_le_one hθ.le x
    have hbound := responseAttenuation_le_one_sub hθ.le x
    nlinarith

theorem integral_attenuation_sq_le_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {θ m : ℝ} {δ v : ℝ≥0} (hX : HasLaw X (gaussianReal m v) P)
    (hθ : θ ^ 2 < 1) (hδ : 0 < δ) (hδv : δ ≤ v) :
    ∫ ω, responseAttenuation θ (X ω) ^ 2 ∂P ≤
      1 - ((1 - θ ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2) / 2 := by
  have heq := hX.integral_comp (integrable_attenuation_sq m v hθ.le).aestronglyMeasurable
  change (∫ ω, ((fun x => responseAttenuation θ x ^ 2) ∘ X) ω ∂P) ≤ _
  rw [heq]
  exact integral_attenuation_sq_le hθ m hδ hδv

end GaussianAttenuation
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_Leaf
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

theorem energy_congr_on {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) {eta xi : TreeVertex d → IsingSpin}
    (heq : ∀ x ∈ D, eta x = xi x) : energy beta h D eta = energy beta h D xi := by
  classical
  unfold energy
  congr 1
  · exact Finset.sum_congr rfl (fun x hx => by rw [heq x hx])
  · congr 1
    apply Finset.sum_congr rfl
    intro e he
    have hm := (Finset.mem_filter.mp he).1
    rw [Finset.product_eq_sprod] at hm
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hm
    rw [heq e.1 hu, heq e.2 hv]

theorem energy_update_eq_erase_add
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) (s : IsingSpin) :
    energy beta h D (Function.update eta v s) = energy beta h (D.erase v) eta +
      (h v + beta * spinSign (eta p)) * spinSign s := by
  classical
  have hnot : (p, v) ∉ inducedEdges (D.erase v) := by
    simp [inducedEdges, Finset.product_eq_sprod]
  have hfield : (∑ x ∈ D, h x * spinSign (Function.update eta v s x)) =
      (∑ x ∈ D.erase v, h x * spinSign (eta x)) + h v * spinSign s := by
    rw [← Finset.sum_erase_add D _ hv]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  have hedge : (∑ e ∈ inducedEdges (D.erase v),
      spinSign (Function.update eta v s e.1) * spinSign (Function.update eta v s e.2)) =
      ∑ e ∈ inducedEdges (D.erase v), spinSign (eta e.1) * spinSign (eta e.2) := by
    apply Finset.sum_congr rfl
    intro e he
    have hm := (Finset.mem_filter.mp he).1
    rw [Finset.product_eq_sprod] at hm
    obtain ⟨hu, hw⟩ := Finset.mem_product.mp hm
    rw [Function.update_of_ne (Finset.mem_erase.mp hu).1,
      Function.update_of_ne (Finset.mem_erase.mp hw).1]
  unfold energy
  rw [hfield, hedges, Finset.sum_insert hnot, hedge]
  simp only [Function.update_of_ne hpne, Function.update_self]
  ring

theorem sum_weight_update_of_edges
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, weight beta h D (Function.update eta v s)) =
      2 * Real.cosh (h v + beta * spinSign (eta p)) * weight beta h (D.erase v) eta := by
  simp only [weight, energy_update_eq_erase_add beta h hv hpne hedges, Real.exp_add]
  rw [← Finset.mul_sum, sum_isingSpin]
  simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one]
  rw [Real.cosh_eq]
  ring

theorem sum_weight_eq_erase_sum
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)) =
      ∑ eta : D.erase v → IsingSpin,
        2 * Real.cosh (h v + beta * spinSign (extendFiniteSpin (D.erase v) eta p)) *
          weight beta h (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        weight beta h D (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) :=
      ((finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta => weight beta h D (extendFiniteSpin D eta))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro eta _
      simp only [extendFiniteSpin_eraseEquiv_symm]
      exact sum_weight_update_of_edges beta h hv hpne hedges _

end Problem367.GibbsLeaf

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gibbs_LeafMessage
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

theorem eliminationConstant_pos (beta z : ℝ) : 0 < eliminationConstant beta z := by
  unfold eliminationConstant
  positivity

theorem cosh_eq_eliminationConstant_mul_message (beta z : ℝ) (s : IsingSpin) :
    2 * Real.cosh (z + beta * spinSign s) =
      eliminationConstant beta z * Real.exp
        (cavityMessage (Real.tanh beta) z * spinSign s) := by
  unfold eliminationConstant
  rw [mul_assoc, ← Real.exp_add, cavityMessage_eq_log_cosh_sub]
  cases s
  · simp only [spinSign_neg, mul_neg_one]
    rw [show (Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2 +
        -((Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2) =
        Real.log (Real.cosh (z - beta)) by ring]
    rw [Real.exp_log (Real.cosh_pos _)]
    congr 2
  · simp only [spinSign_pos, mul_one]
    rw [show (Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2 +
        (Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2 =
        Real.log (Real.cosh (z + beta)) by ring]
    rw [Real.exp_log (Real.cosh_pos _)]

theorem energy_update_field {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) {p : TreeVertex d} (hp : p ∈ D)
    (z : ℝ) (eta : TreeVertex d → IsingSpin) :
    energy beta (Function.update h p (h p + z)) D eta =
      energy beta h D eta + z * spinSign (eta p) := by
  classical
  have hsum : (∑ x ∈ D.erase p, Function.update h p (h p + z) x * spinSign (eta x)) =
      ∑ x ∈ D.erase p, h x * spinSign (eta x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  unfold energy
  rw [← Finset.sum_erase_add D
    (fun x => Function.update h p (h p + z) x * spinSign (eta x)) hp,
    ← Finset.sum_erase_add D (fun x => h x * spinSign (eta x)) hp, hsum]
  simp only [Function.update_self]
  ring

theorem sum_weight_update_eq_cavity
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, weight beta h D (Function.update eta v s)) =
      eliminationConstant beta (h v) *
        weight beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
          (D.erase v) eta := by
  rw [sum_weight_update_of_edges beta h hv (Finset.mem_erase.mp hp).1 hedges,
    cosh_eq_eliminationConstant_mul_message]
  simp only [weight, energy_update_field beta h (D.erase v) hp, Real.exp_add]
  ring

theorem partition_eq_cavity_partition
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)) =
      eliminationConstant beta (h v) *
        ∑ eta : D.erase v → IsingSpin,
          weight beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
            (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  rw [sum_weight_eq_erase_sum beta h hv (Finset.mem_erase.mp hp).1 hedges, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  rw [← sum_weight_update_of_edges beta h hv (Finset.mem_erase.mp hp).1 hedges]
  exact sum_weight_update_eq_cavity beta h hv hp hedges _

theorem sum_mass_update_eq_cavity
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, mass beta h D (Function.update eta v s)) =
      mass beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) eta := by
  classical
  simp only [mass, ← Finset.sum_div]
  rw [sum_weight_update_eq_cavity beta h hv hp hedges]
  unfold partition
  rw [partition_eq_cavity_partition beta h hv hp hedges]
  exact mul_div_mul_left _ _ (ne_of_gt (eliminationConstant_pos beta (h v)))

end Problem367.GibbsLeaf

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LeafMarginal
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_expectation_eq_sum_mass
    {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ) (D : Finset (TreeVertex d))
    (f : (D → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) f =
      ∑ eta : D → IsingSpin, GibbsLeaf.mass beta h D (extendFiniteSpin D eta) * f eta := by
  classical
  simp only [LeafGibbs.expectation, GibbsLeaf.mass, GibbsLeaf.weight,
    GibbsLeaf.partition, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro eta heta
  ring

theorem tree_gibbs_expectation_erase
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1)) =
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta
        (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) (extendFiniteSpin (D.erase v) eta)) f := by
  classical
  rw [tree_gibbs_expectation_eq_sum_mass, tree_gibbs_expectation_eq_sum_mass]
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        GibbsLeaf.mass beta h D
          (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) * f z.1 := by
      rw [← (finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta : D → IsingSpin => GibbsLeaf.mass beta h D (extendFiniteSpin D eta) *
          f ((finiteSpinEraseEquiv hv eta).1))]
      simp only [Equiv.apply_symm_apply]
    _ = ∑ eta : D.erase v → IsingSpin,
        (∑ s : IsingSpin, GibbsLeaf.mass beta h D
          (Function.update (extendFiniteSpin (D.erase v) eta) v s)) * f eta := by
      rw [Fintype.sum_prod_type]
      simp only [extendFiniteSpin_eraseEquiv_symm, Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro eta heta
      rw [GibbsLeaf.sum_mass_update_eq_cavity beta h hv hp hedges]

theorem tree_gibbs_covariance_erase
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f g : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
      (fun eta => g ((finiteSpinEraseEquiv hv eta).1)) =
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta
        (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) (extendFiniteSpin (D.erase v) eta)) f g := by
  unfold LeafGibbs.covariance
  rw [tree_gibbs_expectation_erase beta h hv hp hedges (fun eta => f eta * g eta),
    tree_gibbs_expectation_erase beta h hv hp hedges f,
    tree_gibbs_expectation_erase beta h hv hp hedges g]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

theorem ConnectedFinset.prefix_mem_of_min_length_le {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ w ∈ D, r.1.length ≤ w.1.length)
    {u v : TreeVertex d} (hv : v ∈ D) (huv : u.1 <+: v.1)
    (hru : r.1.length ≤ u.1.length) : u ∈ D := by
  have aux : ∀ n : ℕ, ∀ v : TreeVertex d, v.1.length = n → v ∈ D →
      u.1 <+: v.1 → u ∈ D := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hn hv huv
      by_cases huv_eq : u = v
      · exact huv_eq.symm ▸ hv
      · have hvne : v ≠ r := by
          intro heq
          subst v
          exact huv_eq (Subtype.ext (huv.eq_of_length_le hru))
        have hp := hD.parent_mem_of_ne_min hr hmin hv hvne
        have hvnil := ConnectedFinset.ne_nil_of_ne_min hmin hv hvne
        have hpos : 0 < v.1.length := List.length_pos_iff.mpr hvnil
        have hplen : (parentVertex v).1.length < n := by
          rw [parentVertex_length]
          omega
        have hup : u.1 <+: (parentVertex v).1 := by
          apply List.prefix_of_prefix_length_le huv (List.dropLast_prefix v.1)
          have hle := huv.length_le
          have hneq : u.1.length ≠ v.1.length := by
            intro heq
            exact huv_eq (Subtype.ext (huv.eq_of_length heq))
          change u.1.length ≤ (parentVertex v).1.length
          rw [parentVertex_length]
          omega
        exact ih _ hplen _ rfl hp hup
  exact aux _ v rfl hv huv

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedProjectivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem ConnectedFinset.exists_prunable_vertex_of_shared_min
    {d : ℕ} {D E : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hE : ConnectedFinset E) (hDE : D ⊆ E) {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length) (hne : D ≠ E) :
    ∃ v p : TreeVertex d, v ∈ E ∧ v ∉ D ∧ p ∈ E ∧ p ≠ v ∧
      ConnectedFinset (E.erase v) ∧ D ⊆ E.erase v ∧
      inducedEdges E = insert (p, v) (inducedEdges (E.erase v)) := by
  classical
  have hdiff : (E \ D).Nonempty := Finset.sdiff_nonempty.mpr (by
    intro hED
    exact hne (Finset.Subset.antisymm hDE hED))
  obtain ⟨v, hvdiff, hmax⟩ := Finset.exists_max_image (E \ D) (fun x => x.1.length) hdiff
  obtain ⟨hvE, hvD⟩ := Finset.mem_sdiff.mp hvdiff
  have hvr : v ≠ r := by
    intro h
    exact hvD (h ▸ hr)
  have hpE : parentVertex v ∈ E :=
    hE.parent_mem_of_ne_min (hDE hr) hmin hvE hvr
  have hvnil : v.1 ≠ [] := ConnectedFinset.ne_nil_of_ne_min hmin hvE hvr
  have hpv : treeAdj (parentVertex v) v := treeAdj_parentVertex hvnil
  have hplen : (parentVertex v).1.length < v.1.length := by
    rw [parentVertex_length]
    have : 0 < v.1.length := List.length_pos_iff.mpr hvnil
    omega
  have hleaf : ∀ x ∈ E, treeAdj v x → x = parentVertex v := by
    intro x hx hadj
    rcases treeAdj_length hadj with hlen | hlen
    · have hxD : x ∈ D := by
        by_contra hxD
        have hbound := hmax x (Finset.mem_sdiff.mpr ⟨hx, hxD⟩)
        omega
      have hxr : x ≠ r := by
        intro h
        subst x
        have := hmin v hvE
        omega
      have hpD := hD.parent_mem_of_ne_min hr (fun y hy => hmin y (hDE hy)) hxD hxr
      have hparent : parentVertex x = v := treeAdj_parent_of_length_lt hadj (by omega)
      exact False.elim (hvD (hparent ▸ hpD))
    · exact (treeAdj_parent_of_length_lt (hadj.elim Or.inr Or.inl) (by omega)).symm
  have hDEerase : D ⊆ E.erase v := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by intro h; exact hvD (h ▸ hx), hDE hx⟩
  have hconn : ConnectedFinset (E.erase v) :=
    connectedFinset_erase_of_leaf hE hvE ⟨r, hDEerase hr⟩
      (fun x hx y hy hvx hvy => (hleaf x hx hvx).trans (hleaf y hy hvy).symm)
  refine ⟨v, parentVertex v, hvE, hvD, hpE, ?_, hconn, hDEerase, ?_⟩
  · intro h
    have := congrArg (fun x : TreeVertex d => x.1.length) h
    omega
  · exact inducedEdges_eq_insert_erase_of_unique_lower_neighbor hvE hpE hpv hplen hleaf

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_GibbsMarginal
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tree_gibbs_marginal_of_shared_min
    {d : ℕ} (beta : ℝ) {D E : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hE : ConnectedFinset E) (hDE : D ⊆ E)
    {r : TreeVertex d} (hr : r ∈ D)
    (hmin : ∀ x ∈ E, r.1.length ≤ x.1.length) (h : TreeVertex d → ℝ) :
    ∃ h' : TreeVertex d → ℝ, ∀ f : (D → IsingSpin) → ℝ,
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta))
        (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDE eta)) =
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h' D (extendFiniteSpin D eta)) f := by
  classical
  revert hE hDE hmin h
  refine Finset.strongInductionOn E ?_
  intro E ih hE hDE hmin h
  by_cases heq : D = E
  · subst E
    exact ⟨h, fun _ => rfl⟩
  · obtain ⟨v, p, hvE, _, hpE, hpne, hEr, hDEr, hedges⟩ :=
      hD.exists_prunable_vertex_of_shared_min hE hDE hr hmin heq
    have hpEr : p ∈ E.erase v := Finset.mem_erase.mpr ⟨hpne, hpE⟩
    have hErE : E.erase v ⊆ E := Finset.erase_subset _ _
    obtain ⟨h', hh'⟩ := ih (E.erase v) (Finset.erase_ssubset hvE) hEr hDEr
      (fun x hx => hmin x (hErE hx))
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
    refine ⟨h', fun f => ?_⟩
    calc
      _ = LeafGibbs.expectation
          (fun eta => GibbsLeaf.energy beta
            (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
            (E.erase v) (extendFiniteSpin (E.erase v) eta))
          (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDEr eta)) := by
        exact tree_gibbs_expectation_erase beta h hvE hpEr hedges
          (fun eta => f (Finset.restrict₂ (π := fun _ => IsingSpin) hDEr eta))
      _ = _ := hh' f

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_LeafCovariance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

private theorem leaf_expectation_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (E f : B → ℝ) :
    LeafGibbs.expectation (E ∘ e) (f ∘ e) = LeafGibbs.expectation E f := by
  unfold LeafGibbs.expectation
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun b => f b * Real.exp (E b)), e.sum_comp (fun b => Real.exp (E b))]

private theorem leaf_covariance_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (E f g : B → ℝ) :
    LeafGibbs.covariance (E ∘ e) (f ∘ e) (g ∘ e) = LeafGibbs.covariance E f g := by
  unfold LeafGibbs.covariance
  rw [leaf_expectation_equiv, leaf_expectation_equiv]
  congr 1
  exact leaf_expectation_equiv e E (fun b => f b * g b)

theorem tree_gibbs_leaf_energy_split
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) ∘
      (finiteSpinEraseEquiv hv).symm =
    LeafGibbs.energy
      (fun eta => GibbsLeaf.energy beta h (D.erase v) (extendFiniteSpin (D.erase v) eta))
      (fun eta => extendFiniteSpin (D.erase v) eta p) beta (h v) := by
  funext z
  rcases z with ⟨eta, s⟩
  simp only [Function.comp_apply, extendFiniteSpin_eraseEquiv_symm,
    GibbsLeaf.energy_update_eq_erase_add beta h hv hpne hedges, LeafGibbs.energy]
  ring

theorem tree_gibbs_covariance_leaf
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (f : (D.erase v → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
      (fun eta => spinSign (eta ⟨v, hv⟩)) =
    (Real.tanh beta * responseAttenuation (Real.tanh beta) (h v)) *
      LeafGibbs.covariance
        (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
        (fun eta => f ((finiteSpinEraseEquiv hv eta).1))
        (fun eta => spinSign (eta ⟨p, (Finset.mem_erase.mp hp).2⟩)) := by
  classical
  let : Nonempty (D.erase v → IsingSpin) := ⟨fun _ => .neg⟩
  let e := (finiteSpinEraseEquiv hv).symm
  let E : (D → IsingSpin) → ℝ :=
    fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)
  let F : (D → IsingSpin) → ℝ := fun eta => f ((finiteSpinEraseEquiv hv eta).1)
  let L : (D → IsingSpin) → ℝ := fun eta => spinSign (eta ⟨v, hv⟩)
  let P : (D → IsingSpin) → ℝ :=
    fun eta => spinSign (eta ⟨p, (Finset.mem_erase.mp hp).2⟩)
  change LeafGibbs.covariance E F L = _ * LeafGibbs.covariance E F P
  rw [← leaf_covariance_equiv e E F L, ← leaf_covariance_equiv e E F P]
  have he : E ∘ e = LeafGibbs.energy
      (fun eta => GibbsLeaf.energy beta h (D.erase v) (extendFiniteSpin (D.erase v) eta))
      (fun eta => extendFiniteSpin (D.erase v) eta p) beta (h v) :=
    tree_gibbs_leaf_energy_split beta h hv (Finset.mem_erase.mp hp).1 hedges
  have hf : F ∘ e = fun z => f z.1 := by
    funext z
    simp [F, e]
  have hl : L ∘ e = fun z => spinSign z.2 := by
    funext z
    simp [L, e, finiteSpinEraseEquiv]
  have hp' : P ∘ e = fun z => spinSign (extendFiniteSpin (D.erase v) z.1 p) := by
    funext z
    simp [P, e, finiteSpinEraseEquiv, extendFiniteSpin,
      (Finset.mem_erase.mp hp).1, hp]
  rw [he, hf, hl, hp']
  exact LeafGibbs.covariance_leaf_eq_mul_parent _ f _ beta (h v)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeCovariance
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.GaussianTreeCovariance

lemma gaussianContraction_pos (beta : ℝ) (δ : ℝ≥0) :
    0 < gaussianContraction beta δ := by
  have ht := Real.tanh_sq_lt_one (gaussianSmallRadius δ)
  have hp := mul_nonneg (sq_nonneg (Real.tanh beta))
    (sq_nonneg (Real.tanh (gaussianSmallRadius δ)))
  unfold gaussianContraction
  nlinarith

lemma gaussianContraction_lt_one (beta : ℝ) {δ : ℝ≥0} (hδ : 0 < δ) :
    gaussianContraction beta δ < 1 := by
  have ht : 0 < Real.tanh (gaussianSmallRadius δ) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (gaussianSmallRadius_pos hδ)) (Real.cosh_pos _)
  have hg : 0 < (1 - Real.tanh beta ^ 2) * Real.tanh (gaussianSmallRadius δ) ^ 2 :=
    mul_pos (sub_pos.mpr (Real.tanh_sq_lt_one beta)) (sq_pos_of_pos ht)
  unfold gaussianContraction
  linarith

lemma lintegral_gaussian_attenuation_le (beta m a : ℝ) {δ t : ℝ≥0}
    (hδ : 0 < δ) (ht : δ ≤ t) :
    (∫⁻ z, ENNReal.ofReal (responseAttenuation (Real.tanh beta) (a + z) ^ 2)
      ∂gaussianReal m t) ≤ ENNReal.ofReal (gaussianContraction beta δ) := by
  have hm : Measurable (fun z : ℝ => responseAttenuation (Real.tanh beta) (a + z) ^ 2) := by
    simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
    fun_prop
  have hint : Integrable (fun z : ℝ => responseAttenuation (Real.tanh beta) (a + z) ^ 2)
      (gaussianReal m t) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact GaussianAttenuation.attenuation_sq_le_one (Real.tanh_sq_lt_one beta).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hlaw : HasLaw (fun z : ℝ => a + z) (gaussianReal (m + a) t) (gaussianReal m t) := by
    refine ⟨(measurable_const.add measurable_id).aemeasurable, ?_⟩
    simpa only [add_comm a] using (gaussianReal_map_add_const (μ := m) (v := t) a)
  exact GaussianAttenuation.integral_attenuation_sq_le_of_hasLaw hlaw
    (Real.tanh_sq_lt_one beta) hδ ht

end Problem367.GaussianTreeCovariance

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RadialEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem367

theorem summable_of_tree_radial_le {d : ℕ} {f : TreeVertex d → ℝ} {C r : ℝ}
    (hf : ∀ v, 0 ≤ f v) (hbound : ∀ v, f v ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) : Summable f :=
  ((summable_geometric_radial d hr hsmall).mul_left C).of_nonneg_of_le hf hbound

theorem tsum_le_of_tree_radial_le {d : ℕ} {f : TreeVertex d → ℝ} {C r : ℝ}
    (hf : ∀ v, 0 ≤ f v) (hbound : ∀ v, f v ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    (∑' v, f v) ≤ C * (1 + (d : ℝ) * r / (1 - ((d - 1 : ℕ) : ℝ) * r)) := by
  have hfS := summable_of_tree_radial_le hf hbound hr hsmall
  calc
    (∑' v, f v) ≤ ∑' v : TreeVertex d, C * r ^ v.1.length :=
      hfS.tsum_le_tsum hbound ((summable_geometric_radial d hr hsmall).mul_left C)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_radial d hr hsmall]

theorem integral_tsum_sq_eq_of_tree_radial_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : TreeVertex d → Ω → ℝ} {C r : ℝ}
    (hInt : ∀ v, Integrable (fun ω => A v ω ^ 2) P)
    (hbound : ∀ v, (∫ ω, A v ω ^ 2 ∂P) ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    (∫ ω, ∑' v, A v ω ^ 2 ∂P) = ∑' v, ∫ ω, A v ω ^ 2 ∂P := by
  apply (integral_tsum_of_summable_integral_norm hInt _).symm
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  exact summable_of_tree_radial_le (fun v => integral_nonneg (fun ω => sq_nonneg _))
    hbound hr hsmall

theorem integral_tsum_sq_le_of_tree_radial_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : TreeVertex d → Ω → ℝ} {C r : ℝ}
    (hInt : ∀ v, Integrable (fun ω => A v ω ^ 2) P)
    (hbound : ∀ v, (∫ ω, A v ω ^ 2 ∂P) ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    (∫ ω, ∑' v, A v ω ^ 2 ∂P) ≤
      C * (1 + (d : ℝ) * r / (1 - ((d - 1 : ℕ) : ℝ) * r)) := by
  rw [integral_tsum_sq_eq_of_tree_radial_bound hInt hbound hr hsmall]
  exact tsum_le_of_tree_radial_le (fun v => integral_nonneg (fun ω => sq_nonneg _))
    hbound hr hsmall

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeCovariance

lemma gaussian_radial_ratio_lt_one {d : ℕ} {beta : ℝ} {δ : ℝ≥0}
    (hδ : 0 < δ) (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta δ) < 1 := by
  calc
    _ = (((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2) * gaussianContraction beta δ := by ring
    _ ≤ 1 * gaussianContraction beta δ :=
      mul_le_mul_of_nonneg_right hcrit (gaussianContraction_pos beta δ).le
    _ < 1 := by simpa only [one_mul] using gaussianContraction_lt_one beta hδ

end Problem367.GaussianTreeCovariance

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_AutDistance
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem reducedWordDistance_prefixFlipWord {α : Type*} [DecidableEq α]
    (a : α) (u v : List α) (hu : List.IsChain (fun x y : α => x ≠ y) (a :: u)) :
    reducedWordDistance u (prefixFlipWord a v) = reducedWordDistance (a :: u) v := by
  cases v with
  | nil =>
      cases u with
      | nil => rfl
      | cons b u =>
          have hab : a ≠ b := (List.isChain_cons_cons.mp hu).1
          simp only [prefixFlipWord, reducedWordDistance_cons_ne hab.symm,
            List.length_nil, reducedWordDistance_nil_right, List.length_cons]
  | cons b v =>
      by_cases hab : a = b
      · subst b
        simp [prefixFlipWord]
      · simp only [prefixFlipWord, ite_eq_right hab]
        exact reducedWordDistance_move_head a b u v hab hu

theorem exists_treeAut_to_root_distance {d : ℕ} (u : TreeVertex d) :
    ∃ g : TreeAut d,
      g.toEquiv u = ⟨[], List.IsChain.nil⟩ ∧
      ∀ v : TreeVertex d, (g.toEquiv v).1.length = reducedWordDistance u.1 v.1 := by
  rcases u with ⟨w, hw⟩
  induction w with
  | nil =>
      exact ⟨TreeAut.refl d, rfl, fun v => rfl⟩
  | cons a w ih =>
      obtain ⟨g, hg, hdist⟩ := ih hw.tail
      refine ⟨(prefixTreeAut a).trans g, ?_, ?_⟩
      · change g.toEquiv (prefixFlip a ⟨a :: w, hw⟩) = _
        have hflip : prefixFlip a (⟨a :: w, hw⟩ : TreeVertex d) = ⟨w, hw.tail⟩ := by
          apply Subtype.ext
          simp [prefixFlip, prefixFlipWord]
        rw [hflip]
        exact hg
      · intro v
        change (g.toEquiv (prefixFlip a v)).1.length = reducedWordDistance (a :: w) v.1
        rw [hdist (prefixFlip a v)]
        exact reducedWordDistance_prefixFlipWord a w v.1 hw

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FinitePathGibbs
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.FinitePathGibbs

theorem rawKernel_pos (beta : ℝ) (h : ℕ → ℝ) (i : ℕ) (a b : IsingSpin) :
    0 < rawKernel beta h i a b := Real.exp_pos _

theorem tailPartition_pos (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) :
    0 < tailPartition beta h n a := by
  let : Nonempty (Fin n → IsingSpin) := ⟨fun _ => .pos⟩
  apply Finset.sum_pos _ Finset.univ_nonempty
  intro x _
  rw [InhomogeneousChain.weight_eq_prod]
  exact Finset.prod_pos fun i _ => rawKernel_pos beta h i _ _

theorem tailPartition_succ (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a : IsingSpin) :
    tailPartition beta h (n + 1) a =
      ∑ b, rawKernel beta h 0 a b *
        tailPartition beta (fun i => h (i + 1)) n b := by
  unfold tailPartition
  rw [FiniteChain.sum_cons]
  simp only [InhomogeneousChain.weight_cons, ← Finset.mul_sum]
  rfl

theorem normalize_binary (w : IsingSpin → ℝ) (hw : ∀ a, 0 < w a) (b : IsingSpin) :
    w b / (∑ a, w a) =
      (1 + spinSign b * Real.tanh
        ((Real.log (w .pos) - Real.log (w .neg)) / 2)) / 2 := by
  rw [← binary_mean_eq_tanh_half_log (hw .pos) (hw .neg), sum_isingSpin]
  have hsum : w .pos + w .neg ≠ 0 := (add_pos (hw .pos) (hw .neg)).ne'
  have hsum' : w .neg + w .pos ≠ 0 := (add_pos (hw .neg) (hw .pos)).ne'
  cases b <;> simp only [spinSign_neg, spinSign_pos] <;>
    field_simp [hsum, hsum'] <;> ring

theorem normalized_head (beta : ℝ) (h : ℕ → ℝ) (n : ℕ) (a b : IsingSpin) :
    rawKernel beta h 0 a b * tailPartition beta (fun i => h (i + 1)) n b /
      tailPartition beta h (n + 1) a =
    PosteriorChain.transition beta (backwardField beta h (n + 1) 0) a b := by
  let w : IsingSpin → ℝ := fun b =>
    rawKernel beta h 0 a b * tailPartition beta (fun i => h (i + 1)) n b
  have hw : ∀ b, 0 < w b := fun b =>
    mul_pos (rawKernel_pos beta h 0 a b)
      (tailPartition_pos beta (fun i => h (i + 1)) n b)
  rw [tailPartition_succ]
  change w b / (∑ s, w s) = _
  rw [normalize_binary w hw]
  have hlog : (Real.log (w .pos) - Real.log (w .neg)) / 2 =
      backwardField beta h (n + 1) 0 + beta * spinSign a := by
    dsimp [w, rawKernel, backwardField]
    rw [Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
      Real.log_mul (Real.exp_pos _).ne' (tailPartition_pos _ _ _ _).ne',
      Real.log_exp, Real.log_exp]
    ring
  rw [hlog]
  rfl

theorem normalized_path (beta : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (a : IsingSpin) (x : Fin n → IsingSpin) :
    InhomogeneousChain.weight
      (fun i => PosteriorChain.transition beta (backwardField beta h n i)) n a x =
    InhomogeneousChain.weight (rawKernel beta h) n a x / tailPartition beta h n a := by
  induction n generalizing h a with
  | zero => simp
  | succ n ih =>
    rw [InhomogeneousChain.weight, InhomogeneousChain.weight]
    change PosteriorChain.transition beta (backwardField beta h (n + 1) 0) a (x 0) *
      InhomogeneousChain.weight
        (fun i => PosteriorChain.transition beta
          (backwardField beta (fun j => h (j + 1)) n i)) n (x 0) (Fin.tail x) = _
    rw [ih, ← normalized_head]
    have ht := (tailPartition_pos beta (fun i => h (i + 1)) n (x 0)).ne'
    have ht' := (tailPartition_pos beta h (n + 1) a).ne'
    change (rawKernel beta h 0 a (x 0) *
        tailPartition beta (fun i => h (i + 1)) n (x 0) /
        tailPartition beta h (n + 1) a) *
      (InhomogeneousChain.weight (rawKernel beta (fun i => h (i + 1))) n
        (x 0) (Fin.tail x) / tailPartition beta (fun i => h (i + 1)) n (x 0)) = _
    field_simp [ht, ht']
    rfl

theorem partition_pos (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    0 < partition beta root h n := by
  rw [partition, sum_isingSpin]
  exact add_pos (mul_pos (Real.exp_pos _) (tailPartition_pos _ _ _ _))
    (mul_pos (Real.exp_pos _) (tailPartition_pos _ _ _ _))

@[simp] theorem sum_rootLaw (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    ∑ a, rootLaw beta root h n a = 1 := by
  simp only [rootLaw, ← Finset.sum_div]
  exact div_self (partition_pos beta root h n).ne'

theorem mass_eq_jointWeight (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) :
    mass beta root h n x =
    InhomogeneousChain.jointWeight
      (fun i => PosteriorChain.transition beta (backwardField beta h n i))
      (rootLaw beta root h n) n x := by
  obtain ⟨a, x, rfl⟩ := Fin.exists_cons x
  rw [mass, InhomogeneousChain.jointWeight_cons,
    InhomogeneousChain.jointWeight_cons, normalized_path]
  unfold rootLaw
  field_simp [(partition_pos beta root h n).ne', (tailPartition_pos beta h n a).ne']

theorem mass_eq_exp_energy (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (x : Fin (n + 1) → IsingSpin) :
    mass beta root h n x = Real.exp (energy beta root h n x) /
      partition beta root h n := by
  simp only [mass, InhomogeneousChain.jointWeight, rawKernel,
    energy, Real.exp_add, Real.exp_sum]

@[simp] theorem sum_mass (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    ∑ x, mass beta root h n x = 1 := by
  simp_rw [mass_eq_jointWeight]
  exact InhomogeneousChain.sum_jointWeight _ _
    (fun i => PosteriorChain.transition_sum beta (backwardField beta h n i))
    (sum_rootLaw beta root h n) n

theorem partition_eq_sum_exp (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    partition beta root h n =
      ∑ x : Fin (n + 1) → IsingSpin, Real.exp (energy beta root h n x) := by
  have hm := sum_mass beta root h n
  simp_rw [mass_eq_exp_energy] at hm
  rw [← Finset.sum_div, div_eq_one_iff_eq (partition_pos beta root h n).ne'] at hm
  exact hm.symm

theorem mean_endpoints (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (f g : IsingSpin → ℝ) :
    mean beta root h n (fun x => f (x 0) * g (x (Fin.last n))) =
      ∑ a, rootLaw beta root h n a * f a *
        InhomogeneousChain.expectation
          (fun i => PosteriorChain.transition beta (backwardField beta h n i)) n g a := by
  unfold mean
  simp_rw [mass_eq_jointWeight, ← mul_assoc]
  exact InhomogeneousChain.sum_jointWeight_endpoints _ _ _ _ _

theorem mean_first (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    mean beta root h n (fun x => spinSign (x 0)) =
      ∑ a, rootLaw beta root h n a * spinSign a := by
  have hm := mean_endpoints beta root h n spinSign (fun _ => 1)
  simp only [mul_one, InhomogeneousChain.expectation] at hm
  simp only [InhomogeneousChain.sum_weight _
    (fun i => PosteriorChain.transition_sum beta (backwardField beta h n i)), mul_one] at hm
  exact hm

theorem mean_last (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    mean beta root h n (fun x => spinSign (x (Fin.last n))) =
      ∑ a, rootLaw beta root h n a *
        InhomogeneousChain.expectation
          (fun i => PosteriorChain.transition beta (backwardField beta h n i)) n spinSign a := by
  simpa only [one_mul, mul_one] using
    mean_endpoints beta root h n (fun _ => 1) spinSign

theorem endpointCovariance_eq (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ) :
    endpointCovariance beta root h n =
      (1 - mean beta root h n (fun x => spinSign (x 0)) ^ 2) * Real.tanh beta ^ n *
        (∏ i ∈ Finset.range n,
          responseAttenuation (Real.tanh beta) (backwardField beta h n i)) := by
  unfold endpointCovariance
  rw [mean_endpoints, mean_first, mean_last]
  exact PosteriorChain.covariance_eq_response_product beta (backwardField beta h n)
    (rootLaw beta root h n) (sum_rootLaw beta root h n) n

end Problem367.FinitePathGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_PathPosteriorResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.PathPosterior

theorem energy_eq_fieldEnergy (beta : ℝ) (n : ℕ)
    (y : Fin (n + 1) → ℝ) (s : Fin (n + 1) → IsingSpin) :
    FinitePathGibbs.energy beta (y 0) (childFields y) n s =
      FinitePosterior.fieldEnergy (interaction beta n) (spin n) y s := by
  unfold FinitePathGibbs.energy FinitePosterior.fieldEnergy interaction spin
  rw [Fin.sum_univ_succ]
  simp only [childFields_fin, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  ring

theorem mean_eq_fieldMean (beta : ℝ) (n : ℕ) (y : Fin (n + 1) → ℝ)
    (f : (Fin (n + 1) → IsingSpin) → ℝ) :
    FinitePathGibbs.mean beta (y 0) (childFields y) n f =
      FinitePosterior.fieldMean (interaction beta n) (spin n) f y := by
  unfold FinitePathGibbs.mean FinitePosterior.fieldMean
  simp_rw [FinitePathGibbs.mass_eq_exp_energy]
  rw [FinitePathGibbs.partition_eq_sum_exp]
  simp_rw [energy_eq_fieldEnergy]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  apply congrArg (fun a => a / ∑ s, Real.exp
    (FinitePosterior.fieldEnergy (interaction beta n) (spin n) y s))
  apply Finset.sum_congr rfl
  intro s _
  ring

end Problem367.PathPosterior

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathGibbs
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.TreePathGibbs

theorem extend_assignment_path {d : ℕ} (v : TreeVertex d)
    (eta : ConnectedHull.vertices v → IsingSpin) (i : Fin (v.1.length + 1)) :
    extendFiniteSpin (ConnectedHull.vertices v) eta (ConnectedHull.path v i) =
      assignmentEquiv v eta i := by
  exact extendFiniteSpin_apply (ConnectedHull.vertices v) eta (vertexEquiv v i)

theorem extend_assignment_symm_path {d : ℕ} (v : TreeVertex d)
    (s : Fin (v.1.length + 1) → IsingSpin) (i : Fin (v.1.length + 1)) :
    extendFiniteSpin (ConnectedHull.vertices v) ((assignmentEquiv v).symm s)
      (ConnectedHull.path v i) = s i := by
  rw [extend_assignment_path, Equiv.apply_symm_apply]

theorem energy_eq_path {d : ℕ} (v : TreeVertex d) (beta : ℝ)
    (h : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    GibbsLeaf.energy beta h (ConnectedHull.vertices v) eta =
      FinitePosterior.fieldEnergy (PathPosterior.interaction beta v.1.length)
        (PathPosterior.spin v.1.length) (fun i => h (ConnectedHull.path v i))
        (fun i => eta (ConnectedHull.path v i)) := by
  classical
  unfold GibbsLeaf.energy
  rw [ConnectedHull.inducedEdges_vertices, ConnectedHull.vertices_eq_image_path]
  rw [Finset.sum_image]
  · rw [Finset.sum_image]
    · unfold FinitePosterior.fieldEnergy PathPosterior.interaction PathPosterior.spin
      simp only [ConnectedHull.pathEdge]
      ring
    · exact fun _ _ _ _ he => ConnectedHull.pathEdge_injective v he
  · exact fun _ _ _ _ he => ConnectedHull.path_injective v he

theorem expectation_eq_path {d : ℕ} (v : TreeVertex d) (beta : ℝ)
    (h : TreeVertex d → ℝ) (f : (Fin (v.1.length + 1) → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h (ConnectedHull.vertices v)
        (extendFiniteSpin (ConnectedHull.vertices v) eta))
      (fun eta => f (assignmentEquiv v eta)) =
    FinitePathGibbs.mean beta (h (ConnectedHull.path v 0))
      (PathPosterior.childFields (fun i => h (ConnectedHull.path v i))) v.1.length f := by
  rw [PathPosterior.mean_eq_fieldMean beta v.1.length
    (fun i => h (ConnectedHull.path v i)) f]
  unfold LeafGibbs.expectation FinitePosterior.fieldMean
  rw [← (assignmentEquiv v).symm.sum_comp
    (fun eta => f (assignmentEquiv v eta) *
      Real.exp (GibbsLeaf.energy beta h (ConnectedHull.vertices v)
        (extendFiniteSpin (ConnectedHull.vertices v) eta)))]
  rw [← (assignmentEquiv v).symm.sum_comp
    (fun eta => Real.exp (GibbsLeaf.energy beta h (ConnectedHull.vertices v)
      (extendFiniteSpin (ConnectedHull.vertices v) eta)))]
  simp only [Equiv.apply_symm_apply, energy_eq_path, extend_assignment_symm_path]

end Problem367.TreePathGibbs

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.TreePathResponse

theorem path_subset {d : ℕ} {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (hr : ConnectedHull.root d ∈ D)
    {v : TreeVertex d} (hv : v ∈ D) : ConnectedHull.vertices v ⊆ D := by
  intro u hu
  obtain ⟨n, hn, rfl⟩ := ConnectedHull.mem_vertices.mp hu
  apply hD.prefix_mem_of_min_length_le hr (fun x _ => Nat.zero_le _) hv
  · exact List.take_prefix n v.1
  · exact Nat.zero_le _

theorem exists_path_fields {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    ∃ y : Fin (v.1.length + 1) → ℝ, ∀ f : (Fin (v.1.length + 1) → IsingSpin) → ℝ,
      LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
        (fun eta => f (fun i => extendFiniteSpin D eta (ConnectedHull.path v i))) =
      FinitePathGibbs.mean beta (y 0) (PathPosterior.childFields y) v.1.length f := by
  classical
  have hsub := path_subset hD hr hv
  have hrpath : ConnectedHull.root d ∈ ConnectedHull.vertices v := by
    simpa using ConnectedHull.prefix_mem_vertices v (Nat.zero_le v.1.length)
  obtain ⟨h', hh'⟩ := tree_gibbs_marginal_of_shared_min beta
    (ConnectedHull.connected_vertices v) hD hsub hrpath
    (fun x _ => Nat.zero_le _) h
  refine ⟨fun i => h' (ConnectedHull.path v i), fun f => ?_⟩
  have hrest (eta : D → IsingSpin) :
      TreePathGibbs.assignmentEquiv v (Finset.restrict₂ (π := fun _ => IsingSpin) hsub eta) =
        (fun i => extendFiniteSpin D eta (ConnectedHull.path v i)) := by
    funext i
    exact (extendFiniteSpin_apply D eta
      ⟨ConnectedHull.path v i, hsub (TreePathGibbs.vertexEquiv v i).property⟩).symm
  calc
    _ = LeafGibbs.expectation
        (fun eta => GibbsLeaf.energy beta h' (ConnectedHull.vertices v)
          (extendFiniteSpin (ConnectedHull.vertices v) eta))
        (fun eta => f (TreePathGibbs.assignmentEquiv v eta)) := by
      simpa only [hrest] using hh' (fun eta => f (TreePathGibbs.assignmentEquiv v eta))
    _ = _ := TreePathGibbs.expectation_eq_path v beta h' f

theorem exists_root_covariance_product {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    ∃ z : ℕ → ℝ,
      covariance beta h D (ConnectedHull.root d) v =
        (1 - mean beta h D (ConnectedHull.root d) ^ 2) * Real.tanh beta ^ v.1.length *
          ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta) (z i) := by
  obtain ⟨y, hy⟩ := exists_path_fields beta h hD hr hv
  refine ⟨FinitePathGibbs.backwardField beta (PathPosterior.childFields y) v.1.length, ?_⟩
  have hm := hy (fun s => spinSign (s 0))
  have hn := hy (fun s => spinSign (s (Fin.last v.1.length)))
  have hp := hy (fun s => spinSign (s 0) * spinSign (s (Fin.last v.1.length)))
  simp only [ConnectedHull.path_zero, ConnectedHull.path_last] at hm hn hp
  unfold covariance LeafGibbs.covariance mean
  rw [hp, hm, hn]
  exact FinitePathGibbs.endpointCovariance_eq beta (y 0) (PathPosterior.childFields y) v.1.length

theorem mean_mem_Ioo {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {v : TreeVertex d} (hv : v ∈ D) :
    mean beta h D v ∈ Set.Ioo (-1 : ℝ) 1 := by
  classical
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .pos⟩
  rw [mean, LeafGibbs.expectation_eq_mean_zero]
  apply FinitePosterior.spin_mean_mem_Ioo
  · intro eta
    cases extendFiniteSpin D eta v <;> simp [spinSign]
  · refine ⟨fun _ => .neg, ?_⟩
    rw [extendFiniteSpin_apply D (fun _ => .neg) ⟨v, hv⟩]
    rfl
  · refine ⟨fun _ => .pos, ?_⟩
    rw [extendFiniteSpin_apply D (fun _ => .pos) ⟨v, hv⟩]
    rfl

theorem variance_pos {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {v : TreeVertex d} (hv : v ∈ D) :
    0 < 1 - mean beta h D v ^ 2 := by
  have hm := mean_mem_Ioo beta h hv
  have hp : 0 < (1 - mean beta h D v) * (1 + mean beta h D v) :=
    mul_pos (by linarith [hm.2]) (by linarith [hm.1])
  nlinarith

theorem exists_root_response_product {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    ∃ z : ℕ → ℝ, response beta h D (ConnectedHull.root d) v =
      Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta) (z i) := by
  obtain ⟨z, hz⟩ := exists_root_covariance_product beta h hD hr hv
  refine ⟨z, ?_⟩
  rw [response, hz]
  have hp := (variance_pos beta h hr).ne'
  field_simp

theorem root_response_mem_Icc {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    response beta h D (ConnectedHull.root d) v ∈ Set.Icc 0 (Real.tanh beta ^ v.1.length) := by
  obtain ⟨z, hz⟩ := exists_root_response_product beta h hD hr hv
  rw [hz]
  have ht := pow_nonneg (tanh_nonneg_of_beta_nonneg hbeta) v.1.length
  have ha0 : 0 ≤ ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta) (z i) :=
    Finset.prod_nonneg fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le
  have ha1 : (∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta) (z i)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (responseAttenuation_pos (Real.tanh_sq_lt_one beta).le _).le)
      (fun i _ => responseAttenuation_le_one (Real.tanh_sq_lt_one beta).le _)
  exact ⟨mul_nonneg ht ha0, mul_le_of_le_one_right ht ha1⟩

end Problem367.TreePathResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_GibbsAutomorphism
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.sum_mass _root_.OAI.Problem367.FinitePathGibbs.sum_rootLaw _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace Problem367.TreeGibbsAut

variable {d : ℕ}

theorem sum_inducedEdges_image {M : Type*} [AddCommMonoid M]
    (g : TreeAut d) (D : Finset (TreeVertex d))
    (f : TreeVertex d → TreeVertex d → M) (hf : ∀ u v, f u v = f v u) :
    (∑ e ∈ inducedEdges (D.image g.toEquiv),
      f (g.toEquiv.symm e.1) (g.toEquiv.symm e.2)) =
        ∑ e ∈ inducedEdges D, f e.1 e.2 := by
  have h := CylinderAut.prod_inducedEdges_image g D
    (fun u v => Multiplicative.ofAdd (f u v))
    (fun u v => congrArg Multiplicative.ofAdd (hf u v))
  simpa using congrArg Multiplicative.toAdd h

theorem energy_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (eta : TreeVertex d → IsingSpin) :
    GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv) (relabel g eta) =
      GibbsLeaf.energy beta h D eta := by
  unfold GibbsLeaf.energy relabel
  rw [Finset.sum_image g.toEquiv.injective.injOn]
  simp only [Equiv.symm_apply_apply]
  rw [sum_inducedEdges_image g D
    (fun u v => spinSign (eta u) * spinSign (eta v))
    (fun u v => mul_comm _ _)]

theorem energy_spinEquiv (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (eta : D → IsingSpin) :
    GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
      (extendFiniteSpin (D.image g.toEquiv) (spinEquiv g D eta)) =
        GibbsLeaf.energy beta h D (extendFiniteSpin D eta) := by
  calc
    _ = GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (relabel g (extendFiniteSpin D eta)) := by
      apply GibbsLeaf.energy_congr_on
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      change extendFiniteSpin (D.image g.toEquiv) (spinEquiv g D eta)
          ((vertexEquiv g D ⟨u, hu⟩).val) = _
      rw [extendFiniteSpin_apply, spinEquiv_apply_image]
      simp [relabel, extendFiniteSpin, hu]
    _ = _ := energy_relabel g D beta h _

theorem expectation_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (E f : B → ℝ) :
    LeafGibbs.expectation (E ∘ e) (f ∘ e) = LeafGibbs.expectation E f := by
  unfold LeafGibbs.expectation
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun b => f b * Real.exp (E b)), e.sum_comp (fun b => Real.exp (E b))]

theorem expectation_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (f : (D.image g.toEquiv → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta)) f =
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f (spinEquiv g D eta)) := by
  rw [← expectation_equiv (spinEquiv g D)]
  congr 1
  funext eta
  exact energy_spinEquiv g D beta h eta

theorem covariance_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (f k : (D.image g.toEquiv → IsingSpin) → ℝ) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta)) f k =
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => f (spinEquiv g D eta)) (fun eta => k (spinEquiv g D eta)) := by
  unfold LeafGibbs.covariance
  rw [expectation_relabel, expectation_relabel, expectation_relabel]

theorem spin_covariance_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u v : D) :
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta))
      (fun eta => spinSign (eta (vertexEquiv g D u)))
      (fun eta => spinSign (eta (vertexEquiv g D v))) =
    LeafGibbs.covariance
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta u)) (fun eta => spinSign (eta v)) := by
  rw [covariance_relabel]
  simp only [spinEquiv_apply_image]

theorem spin_expectation_relabel (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u : D) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta (relabel g h) (D.image g.toEquiv)
        (extendFiniteSpin (D.image g.toEquiv) eta))
      (fun eta => spinSign (eta (vertexEquiv g D u))) =
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta))
      (fun eta => spinSign (eta u)) := by
  rw [expectation_relabel]
  simp only [spinEquiv_apply_image]

end Problem367.TreeGibbsAut

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ResponseAutomorphism
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.TreePathResponse

theorem mean_relabel {d : ℕ} (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u : D) :
    mean beta (relabel g h) (D.image g.toEquiv) (g.toEquiv u) = mean beta h D u := by
  change mean beta (relabel g h) (D.image g.toEquiv)
    (TreeGibbsAut.vertexEquiv g D u).val = mean beta h D u
  simpa only [mean, extendFiniteSpin_apply] using
    TreeGibbsAut.spin_expectation_relabel g D beta h u

theorem covariance_relabel {d : ℕ} (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u v : D) :
    covariance beta (relabel g h) (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v) =
      covariance beta h D u v := by
  change covariance beta (relabel g h) (D.image g.toEquiv)
    (TreeGibbsAut.vertexEquiv g D u).val (TreeGibbsAut.vertexEquiv g D v).val = _
  simpa only [covariance, extendFiniteSpin_apply] using
    TreeGibbsAut.spin_covariance_relabel g D beta h u v

theorem response_relabel {d : ℕ} (g : TreeAut d) (D : Finset (TreeVertex d))
    (beta : ℝ) (h : TreeVertex d → ℝ) (u v : D) :
    response beta (relabel g h) (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v) =
      response beta h D u v := by
  rw [response, response, covariance_relabel, mean_relabel]

theorem response_mem_Icc_of_reroot {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (u v : D) (g : TreeAut d) (hg : g.toEquiv u = ConnectedHull.root d) :
    response beta h D u v ∈ Set.Icc 0 (Real.tanh beta ^ (g.toEquiv v).1.length) := by
  have hr : ConnectedHull.root d ∈ D.image g.toEquiv := by
    rw [← hg]
    exact (TreeGibbsAut.vertexEquiv g D u).property
  have hb := root_response_mem_Icc hbeta (relabel g h) (hD.image g) hr
    (TreeGibbsAut.vertexEquiv g D v).property
  rw [← hg] at hb
  change response beta (relabel g h) (D.image g.toEquiv) (g.toEquiv u) (g.toEquiv v) ∈ Set.Icc 0 _ at hb
  rw [response_relabel g D beta h u v] at hb
  exact hb

theorem response_mem_Icc {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (h : TreeVertex d → ℝ) {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (u v : D) :
    response beta h D u v ∈ Set.Icc 0 (Real.tanh beta ^ reducedWordDistance u.1.1 v.1.1) := by
  obtain ⟨g, hg, hd⟩ := exists_treeAut_to_root_distance u.1
  simpa only [hd v] using response_mem_Icc_of_reroot hbeta h hD u v g hg

end Problem367.TreePathResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ResponseLeaf
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.TreePathResponse

theorem mean_erase {d : ℕ} {D : Finset (TreeVertex d)} {v p u : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (hu : u ∈ D.erase v) :
    mean beta h D u = mean beta
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v))) (D.erase v) u := by
  have hm := tree_gibbs_expectation_erase beta h hv hp hedges
    (fun eta => spinSign (eta ⟨u, hu⟩))
  change LeafGibbs.expectation _ (fun eta : D → IsingSpin =>
    spinSign (eta ⟨u, (Finset.mem_erase.mp hu).2⟩)) = _ at hm
  simpa only [mean, extendFiniteSpin, dite_eq_left hu,
    dite_eq_left (Finset.mem_erase.mp hu).2] using hm

theorem covariance_erase {d : ℕ} {D : Finset (TreeVertex d)} {v p u w : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (hu : u ∈ D.erase v) (hw : w ∈ D.erase v) :
    covariance beta h D u w = covariance beta
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v))) (D.erase v) u w := by
  have hm := tree_gibbs_covariance_erase beta h hv hp hedges
    (fun eta => spinSign (eta ⟨u, hu⟩)) (fun eta => spinSign (eta ⟨w, hw⟩))
  change LeafGibbs.covariance _ (fun eta : D → IsingSpin =>
    spinSign (eta ⟨u, (Finset.mem_erase.mp hu).2⟩))
    (fun eta => spinSign (eta ⟨w, (Finset.mem_erase.mp hw).2⟩)) = _ at hm
  simpa only [covariance, extendFiniteSpin, dite_eq_left hu,
    dite_eq_left (Finset.mem_erase.mp hu).2, dite_eq_left hw,
    dite_eq_left (Finset.mem_erase.mp hw).2] using hm

theorem response_erase {d : ℕ} {D : Finset (TreeVertex d)} {v p u w : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (hu : u ∈ D.erase v) (hw : w ∈ D.erase v) :
    response beta h D u w = response beta
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v))) (D.erase v) u w := by
  rw [response, response, covariance_erase beta h hv hp hedges hu hw,
    mean_erase beta h hv hp hedges hu]

theorem response_leaf {d : ℕ} {D : Finset (TreeVertex d)} {v p u : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (hu : u ∈ D.erase v) :
    response beta h D u v =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) (h v)) *
        response beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
          (D.erase v) u p := by
  have hc := tree_gibbs_covariance_leaf beta h hv hp hedges
    (fun eta => spinSign (eta ⟨u, hu⟩))
  change LeafGibbs.covariance _ (fun eta : D → IsingSpin =>
    spinSign (eta ⟨u, (Finset.mem_erase.mp hu).2⟩))
    (fun eta => spinSign (eta ⟨v, hv⟩)) = _ *
    LeafGibbs.covariance _ (fun eta : D → IsingSpin =>
      spinSign (eta ⟨u, (Finset.mem_erase.mp hu).2⟩))
      (fun eta => spinSign (eta ⟨p, (Finset.mem_erase.mp hp).2⟩)) at hc
  have hc' : covariance beta h D u v =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) (h v)) *
        covariance beta h D u p := by
    simpa only [covariance, extendFiniteSpin, dite_eq_left hv,
      dite_eq_left (Finset.mem_erase.mp hu).2,
      dite_eq_left (Finset.mem_erase.mp hp).2] using hc
  rw [response, hc', covariance_erase beta h hv hp hedges hu hp,
    mean_erase beta h hv hp hedges hu, response, mul_div_assoc]

theorem response_self {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} {u : TreeVertex d} (hu : u ∈ D) :
    response beta h D u u = 1 := by
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .pos⟩
  have hc : covariance beta h D u u = 1 - mean beta h D u ^ 2 := by
    simp only [covariance, LeafGibbs.covariance, spinSign_mul_self,
      LeafGibbs.expectation_const, mean, pow_two]
  rw [response, hc, div_self (variance_pos beta h hu).ne']

end Problem367.TreePathResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance (gaussianContraction gaussianContraction_pos
  lintegral_gaussian_attenuation_le)

lemma measurable_response {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r v : TreeVertex d) : Measurable (response beta E r v) := by
  classical
  unfold response TreePathResponse.response TreePathResponse.covariance
    TreePathResponse.mean LeafGibbs.covariance LeafGibbs.expectation GibbsLeaf.energy
  fun_prop

lemma response_congr {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r v : TreeVertex d) {h k : TreeVertex d → ℝ}
    (heq : ∀ x ∈ E, h x = k x) : response beta E r v h = response beta E r v k := by
  have he : (fun eta => GibbsLeaf.energy beta h E (extendFiniteSpin E eta)) =
      (fun eta => GibbsLeaf.energy beta k E (extendFiniteSpin E eta)) := by
    funext eta
    unfold GibbsLeaf.energy
    congr 1
    exact Finset.sum_congr rfl (fun x hx => by rw [heq x hx])
  unfold response TreePathResponse.response TreePathResponse.covariance TreePathResponse.mean
  rw [he]

lemma response_erase {d : ℕ} {E : Finset (TreeVertex d)}
    {w p r v : TreeVertex d} (beta : ℝ) (h : TreeVertex d → ℝ)
    (hw : w ∈ E) (hp : p ∈ E.erase w) (hr : r ∈ E.erase w) (hv : v ∈ E.erase w)
    (hedges : inducedEdges E = insert (p, w) (inducedEdges (E.erase w))) :
    response beta E r v h = response beta (E.erase w) r v
      (Function.update h p (h p + cavityMessage (Real.tanh beta) (h w))) :=
  TreePathResponse.response_erase beta h hw hp hedges hr hv

lemma response_leaf {d : ℕ} {E : Finset (TreeVertex d)}
    {w p r : TreeVertex d} (beta : ℝ) (h : TreeVertex d → ℝ)
    (hw : w ∈ E) (hp : p ∈ E.erase w) (hr : r ∈ E.erase w)
    (hedges : inducedEdges E = insert (p, w) (inducedEdges (E.erase w))) :
    response beta E r w h =
      (Real.tanh beta * responseAttenuation (Real.tanh beta) (h w)) *
        response beta (E.erase w) r p
          (Function.update h p (h p + cavityMessage (Real.tanh beta) (h w))) :=
  TreePathResponse.response_leaf beta h hw hp hedges hr

lemma measurable_response_sq {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r v : TreeVertex d) (h : TreeVertex d → ℝ) :
    Measurable (fun x : TreeVertex d → ℝ => ENNReal.ofReal
      (response beta E r v (fun u => h u + x u) ^ 2)) := by
  exact (((measurable_response beta E r v).comp
    (Measurable.of_eval (fun u => measurable_const.add (measurable_pi_apply u)))).pow_const 2).ennreal_ofReal

lemma response_updated_fields {d : ℕ} {E : Finset (TreeVertex d)}
    {w p : TreeVertex d} (beta : ℝ) (r v : TreeVertex d)
    (hp : p ∈ E.erase w) (h x : TreeVertex d → ℝ) (z : ℝ)
    (y : E.erase w → ℝ) :
    response beta (E.erase w) r v
      (Function.update (fun u => h u + Function.updateFinset (Function.update x w z) (E.erase w) y u)
        p (h p + Function.updateFinset (Function.update x w z) (E.erase w) y p +
          cavityMessage (Real.tanh beta)
            (h w + Function.updateFinset (Function.update x w z) (E.erase w) y w))) =
    response beta (E.erase w) r v
      (fun u => Function.update h p (h p + cavityMessage (Real.tanh beta) (h w + z)) u +
        Function.updateFinset x (E.erase w) y u) := by
  classical
  apply response_congr
  intro u hu
  by_cases hup : u = p
  · subst u
    simp only [Function.update_self, Function.updateFinset, dite_eq_left hp,
      Finset.notMem_erase, dite_false, Function.update_self]
    ring
  · simp only [Function.update_of_ne hup, Function.updateFinset, dite_eq_left hu]

lemma lmarginal_leaf {d : ℕ} {E : Finset (TreeVertex d)}
    {w p r : TreeVertex d} (beta : ℝ) (h x : TreeVertex d → ℝ) (z : ℝ)
    (hw : w ∈ E) (hp : p ∈ E.erase w) (hr : r ∈ E.erase w)
    (hedges : inducedEdges E = insert (p, w) (inducedEdges (E.erase w)))
    (μ : TreeVertex d → Measure ℝ) :
    lmarginal μ (E.erase w)
      (fun y => ENNReal.ofReal (response beta E r w (fun u => h u + y u) ^ 2))
      (Function.update x w z) =
    ENNReal.ofReal (Real.tanh beta ^ 2 * responseAttenuation (Real.tanh beta) (h w + z) ^ 2) *
      lmarginal μ (E.erase w)
        (fun y => ENNReal.ofReal (response beta (E.erase w) r p
          (fun u => Function.update h p (h p + cavityMessage (Real.tanh beta) (h w + z)) u + y u) ^ 2)) x := by
  classical
  unfold lmarginal
  rw [← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro y
  dsimp only
  rw [response_leaf beta _ hw hp hr hedges, response_updated_fields beta r p hp h x z y]
  simp only [Function.updateFinset, Finset.notMem_erase, dite_false, Function.update_self,
    mul_pow, ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _))]

lemma lmarginal_nonleaf {d : ℕ} {E : Finset (TreeVertex d)}
    {w p r v : TreeVertex d} (beta : ℝ) (h x : TreeVertex d → ℝ) (z : ℝ)
    (hw : w ∈ E) (hp : p ∈ E.erase w) (hr : r ∈ E.erase w) (hv : v ∈ E.erase w)
    (hedges : inducedEdges E = insert (p, w) (inducedEdges (E.erase w)))
    (μ : TreeVertex d → Measure ℝ) :
    lmarginal μ (E.erase w)
      (fun y => ENNReal.ofReal (response beta E r v (fun u => h u + y u) ^ 2))
      (Function.update x w z) =
      lmarginal μ (E.erase w)
        (fun y => ENNReal.ofReal (response beta (E.erase w) r v
          (fun u => Function.update h p (h p + cavityMessage (Real.tanh beta) (h w + z)) u + y u) ^ 2)) x := by
  classical
  unfold lmarginal
  apply lintegral_congr
  intro y
  dsimp only
  rw [response_erase beta _ hw hp hr hv hedges, response_updated_fields beta r v hp h x z y]

theorem lmarginal_response_sq_le
    {d : ℕ} {beta : ℝ} (_hb : 0 ≤ beta)
    (μ : TreeVertex d → Measure ℝ) [∀ u, IsProbabilityMeasure (μ u)]
    (q : ℝ≥0∞)
    (hq : ∀ (u : TreeVertex d) (a : ℝ),
      (∫⁻ z, ENNReal.ofReal (responseAttenuation (Real.tanh beta) (a + z) ^ 2) ∂μ u) ≤ q)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (hmin : ∀ u ∈ E, r.1.length ≤ u.1.length)
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    lmarginal μ E (fun y => ENNReal.ofReal
      (response beta E r v (fun u => h u + y u) ^ 2)) x ≤
      (ENNReal.ofReal (Real.tanh beta ^ 2) * q) ^ (v.1.length - r.1.length) := by
  classical
  revert hE hr hmin h x v
  refine Finset.strongInductionOn E ?_
  intro E ih hE hr hmin h x v hv
  by_cases hvr : v = r
  · subst v
    simp only [Nat.sub_self, pow_zero]
    unfold lmarginal
    calc
      _ ≤ ∫⁻ _ : E → ℝ, (1 : ℝ≥0∞) ∂Measure.pi (fun u : E => μ u) := by
        apply lintegral_mono
        intro y
        apply ENNReal.ofReal_le_one.mpr
        change TreePathResponse.response beta
          (fun u => h u + Function.updateFinset x E y u) E r r ^ 2 ≤ 1
        rw [TreePathResponse.response_self beta _ hr]
        norm_num
      _ = 1 := by simp
  have hsub : ({r} : Finset (TreeVertex d)) ⊆ E := Finset.singleton_subset_iff.mpr hr
  have hne : ({r} : Finset (TreeVertex d)) ≠ E := by
    intro heq
    exact hvr (Finset.mem_singleton.mp (heq.symm ▸ hv))
  obtain ⟨w, p, hwE, _, hpE, hpw, hEr, hsubr, hedges⟩ :=
    (connectedFinset_singleton r).exists_prunable_vertex_of_shared_min
      hE hsub (Finset.mem_singleton_self r) hmin hne
  have hrEr : r ∈ E.erase w := hsubr (Finset.mem_singleton_self r)
  have hpEr : p ∈ E.erase w := Finset.mem_erase.mpr ⟨hpw, hpE⟩
  have hErE : E.erase w ⊆ E := Finset.erase_subset _ _
  have hmin' : ∀ u ∈ E.erase w, r.1.length ≤ u.1.length :=
    fun u hu => hmin u (hErE hu)
  rw [lmarginal_erase _ (measurable_response_sq beta E r v h) hwE x]
  by_cases hvw : v = w
  · subst v
    have hedge : (p, w) ∈ inducedEdges E := by
      rw [hedges]
      exact Finset.mem_insert_self _ _
    have hdata := Finset.mem_filter.mp hedge
    have hadj : treeAdj p w := hdata.2.1
    have hlower : p.1.length < w.1.length := hdata.2.2
    have hlen := treeAdj_length hadj
    have hdist : w.1.length - r.1.length = (p.1.length - r.1.length) + 1 := by
      have := hmin p hpE
      omega
    let B := ENNReal.ofReal (Real.tanh beta ^ 2) * q
    have hm : Measurable (fun z : ℝ => ENNReal.ofReal
        (responseAttenuation (Real.tanh beta) (h w + z) ^ 2)) := by
      simp only [responseAttenuation, Real.tanh_eq_sinh_div_cosh]
      fun_prop
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal (Real.tanh beta ^ 2 *
          responseAttenuation (Real.tanh beta) (h w + z) ^ 2) *
          B ^ (p.1.length - r.1.length) ∂μ w := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [lmarginal_leaf beta h x z hwE hpEr hrEr hedges]
        exact mul_le_mul_right (ih (E.erase w) (Finset.erase_ssubset hwE)
          hEr hrEr hmin' _ x p hpEr) _
      _ = ENNReal.ofReal (Real.tanh beta ^ 2) *
          (∫⁻ z, ENNReal.ofReal (responseAttenuation (Real.tanh beta) (h w + z) ^ 2) ∂μ w) *
          B ^ (p.1.length - r.1.length) := by
        simp_rw [ENNReal.ofReal_mul (sq_nonneg (Real.tanh beta))]
        have hcm : Measurable (fun z : ℝ => ENNReal.ofReal (Real.tanh beta ^ 2) *
            ENNReal.ofReal (responseAttenuation (Real.tanh beta) (h w + z) ^ 2)) :=
          measurable_const.mul hm
        rw [lintegral_mul_const _ hcm, lintegral_const_mul _ hm]
      _ ≤ ENNReal.ofReal (Real.tanh beta ^ 2) * q * B ^ (p.1.length - r.1.length) := by
        gcongr
        exact hq w (h w)
      _ = _ := by
        rw [hdist]
        change B * B ^ (p.1.length - r.1.length) = B ^ ((p.1.length - r.1.length) + 1)
        exact (pow_succ' B _).symm
  · have hvEr : v ∈ E.erase w := Finset.mem_erase.mpr ⟨hvw, hv⟩
    calc
      _ ≤ ∫⁻ _ : ℝ, (ENNReal.ofReal (Real.tanh beta ^ 2) * q) ^
          (v.1.length - r.1.length) ∂μ w := by
        apply lintegral_mono
        intro z
        dsimp only
        rw [lmarginal_nonleaf beta h x z hwE hpEr hrEr hvEr hedges]
        exact ih (E.erase w) (Finset.erase_ssubset hwE) hEr hrEr hmin' _ x v hvEr
      _ = _ := by simp

theorem lintegral_gaussian_response_sq_le
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (hmin : ∀ u ∈ E, r.1.length ≤ u.1.length)
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    (∫⁻ y : E → ℝ, ENNReal.ofReal (response beta E r v
      (fun u => h u + Function.updateFinset x E y u) ^ 2)
      ∂Measure.pi (fun u : E => gaussianReal (m u) (t u))) ≤
    ENNReal.ofReal ((Real.tanh beta ^ 2 * gaussianContraction beta δ) ^
      (v.1.length - r.1.length)) := by
  have he := lmarginal_response_sq_le hb (fun u => gaussianReal (m u) (t u))
    (ENNReal.ofReal (gaussianContraction beta δ))
    (fun u a => lintegral_gaussian_attenuation_le beta (m u) a hδ (ht u))
    hE hr hmin h x v hv
  simpa only [lmarginal, ← ENNReal.ofReal_mul (sq_nonneg (Real.tanh beta)),
    ← ENNReal.ofReal_pow (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le)] using he

lemma integrable_response_sq {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → TreeVertex d → ℝ} (hX : Measurable X)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (_hmin : ∀ u ∈ E, r.1.length ≤ u.1.length)
    (h : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    Integrable (fun ω => response beta E r v (fun u => h u + X ω u) ^ 2) P := by
  have hm : Measurable (fun ω => response beta E r v (fun u => h u + X ω u) ^ 2) :=
    ((measurable_response beta E r v).comp
      (Measurable.of_eval (fun u => measurable_const.add
        ((measurable_pi_apply u).comp hX)))).pow_const 2
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hc := TreePathResponse.response_mem_Icc hb
    (fun u => h u + X ω u) hE ⟨r, hr⟩ ⟨v, hv⟩
  have ht := tanh_nonneg_of_beta_nonneg hb
  have hp : Real.tanh beta ^ reducedWordDistance r.1 v.1 ≤ 1 :=
    pow_le_one₀ ht (Real.tanh_lt_one beta).le
  change 0 ≤ response beta E r v (fun u => h u + X ω u) ∧
    response beta E r v (fun u => h u + X ω u) ≤
      Real.tanh beta ^ reducedWordDistance r.1 v.1 at hc
  nlinarith

theorem integral_gaussian_response_sq_le
    {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E)
    (hmin : ∀ u ∈ E, r.1.length ≤ u.1.length)
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) (hv : v ∈ E) :
    (∫ y : E → ℝ, response beta E r v
      (fun u => h u + Function.updateFinset x E y u) ^ 2
      ∂Measure.pi (fun u : E => gaussianReal (m u) (t u))) ≤
    (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^
      (v.1.length - r.1.length) := by
  apply (ENNReal.ofReal_le_ofReal_iff
    (pow_nonneg (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le) _)).mp
  have hint := integrable_response_sq hb
    (P := Measure.pi (fun u : E => gaussianReal (m u) (t u)))
    (X := fun y => Function.updateFinset x E y) (by fun_prop)
    hE hr hmin h v hv
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
  exact lintegral_gaussian_response_sq_le hb m t hδ ht hE hr hmin h x v hv

end Problem367.GaussianTreeResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponseEnergy
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance

lemma integral_finiteRow_sq_le {d : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (h x : TreeVertex d → ℝ) (v : TreeVertex d) :
    (∫ y, finiteRow beta E r h x v y ^ 2
      ∂Measure.pi (fun u : E => gaussianReal (m u) (t u))) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length := by
  classical
  by_cases hv : v ∈ E
  · simpa only [finiteRow, ite_eq_left hv, hrnil, List.length_nil, Nat.sub_zero] using
      integral_gaussian_response_sq_le hb m t hδ ht hE hr
        (fun u _ => by simp [hrnil]) h x v hv
  · simp only [finiteRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0), integral_zero]
    exact pow_nonneg (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta δ).le) _

end Problem367.GaussianTreeResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponseMixture
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance

lemma integrable_shiftedRow_sq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (H : Ω → TreeVertex d → ℝ) (hH : Measurable H)
    (x : TreeVertex d → ℝ) (v : TreeVertex d) :
    Integrable (fun p => shiftedRow beta E r H x v p ^ 2)
      (μ.prod (Measure.pi (fun u : E => gaussianReal (m u) (t u)))) := by
  classical
  by_cases hv : v ∈ E
  · simpa only [shiftedRow, finiteRow, ite_eq_left hv, zero_add] using
      integrable_response_sq hb
        (P := μ.prod (Measure.pi (fun u : E => gaussianReal (m u) (t u))))
        (X := fun p : Ω × (E → ℝ) =>
          fun u => H p.1 u + Function.updateFinset x E p.2 u)
        (by fun_prop) hE hr (fun u _ => by simp [hrnil]) (fun _ => 0) v hv
  · simp only [shiftedRow, finiteRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
    exact integrable_zero _ _ _

theorem integral_shiftedRow_sq_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {beta : ℝ} (hb : 0 ≤ beta)
    (m : TreeVertex d → ℝ) (t : TreeVertex d → ℝ≥0)
    {δ : ℝ≥0} (hδ : 0 < δ) (ht : ∀ u, δ ≤ t u)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = [])
    (H : Ω → TreeVertex d → ℝ) (hH : Measurable H)
    (x : TreeVertex d → ℝ) (v : TreeVertex d) :
    (∫ p, shiftedRow beta E r H x v p ^ 2
      ∂μ.prod (Measure.pi (fun u : E => gaussianReal (m u) (t u)))) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length := by
  have hint := integrable_shiftedRow_sq μ hb m t hE hr hrnil H hH x v
  rw [integral_prod _ hint]
  calc
    _ ≤ ∫ _ω, (Real.tanh beta ^ 2 * gaussianContraction beta δ) ^ v.1.length ∂μ := by
      apply integral_mono hint.integral_prod_left (integrable_const _)
      intro ω
      exact integral_finiteRow_sq_le hb m t hδ ht hE hr hrnil (H ω) x v
    _ = _ := by simp

end Problem367.GaussianTreeResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponsePlanted
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.GaussianTreeResponse

open GaussianTreeCovariance PlantedSymmetry

lemma measurable_spinDrift (d : ℕ) (t : ℝ) : Measurable (spinDrift (d := d) t) := by
  exact Measurable.of_eval (fun u =>
    ((measurable_of_finite spinSign).comp (measurable_pi_apply u)).const_mul t)

lemma observedRow_eq_shiftedRow {d : ℕ} (beta : ℝ) (E : Finset (TreeVertex d))
    (r : TreeVertex d) (t : ℝ) (v : TreeVertex d)
    (p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :
    observedRow beta E r t v p =
      shiftedRow beta E r (spinDrift t) (fun _ => 0) v (p.1, E.restrict p.2) := by
  classical
  unfold observedRow shiftedRow finiteRow
  split_ifs with hv
  · apply response_congr
    intro u hu
    simp only [observation, spinDrift, Function.updateFinset, dite_eq_left hu,
      Finset.restrict]
  · rfl

lemma hasLaw_restrict_noise {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    (E : Finset (TreeVertex d)) (t : ℝ≥0) :
    HasLaw
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (p.1, E.restrict p.2))
      (μ.prod (Measure.pi (fun _ : E => gaussianReal 0 t)))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  refine ⟨(measurable_fst.prodMk (E.measurable_restrict.comp measurable_snd)).aemeasurable, ?_⟩
  have hmap := (Measure.map_prod_map μ (gaussianNoiseLaw (TreeVertex d) t)
    measurable_id E.measurable_restrict).symm
  have hfun : Prod.map (id : (TreeVertex d → IsingSpin) → (TreeVertex d → IsingSpin))
      (E.restrict : (TreeVertex d → ℝ) → (E → ℝ)) =
        fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
          (p.1, E.restrict p.2) := by
    funext p
    cases p
    rfl
  rw [hfun] at hmap
  simpa only [gaussianNoiseLaw, Measure.map_id, Measure.infinitePi_map_restrict] using hmap

lemma integrable_observedRow_sq {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) (t : ℝ≥0)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = []) (v : TreeVertex d) :
    Integrable (fun p => observedRow beta E r t v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  classical
  by_cases hv : v ∈ E
  · simpa only [observedRow, ite_eq_left hv, zero_add] using
      integrable_response_sq hb (P := μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (X := observation (t : ℝ)) (measurable_observation t) hE hr
        (fun u _ => by simp [hrnil]) (fun _ => 0) v hv
  · simp only [observedRow, ite_eq_right hv, zero_pow (by decide : 2 ≠ 0)]
    exact integrable_zero _ _ _

theorem integral_observedRow_sq_le {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) [IsProbabilityMeasure μ]
    {beta : ℝ} (hb : 0 ≤ beta) {t : ℝ≥0} (ht : 0 < t)
    {E : Finset (TreeVertex d)} {r : TreeVertex d}
    (hE : ConnectedFinset E) (hr : r ∈ E) (hrnil : r.1 = []) (v : TreeVertex d) :
    (∫ p, observedRow beta E r t v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.length := by
  simp_rw [observedRow_eq_shiftedRow]
  have hi := integrable_shiftedRow_sq μ hb (fun _ => 0) (fun _ => t)
    hE hr hrnil (spinDrift t) (measurable_spinDrift d t) (fun _ => 0) v
  have he := (hasLaw_restrict_noise μ E t).integral_comp hi.aestronglyMeasurable
  simp only [Function.comp_apply] at he
  rw [he]
  exact integral_shiftedRow_sq_le μ hb (fun _ => 0) (fun _ => t) ht (fun _ => le_rfl)
    hE hr hrnil (spinDrift t) (measurable_spinDrift d t) (fun _ => 0) v

end Problem367.GaussianTreeResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponsePosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem GibbsLeaf.energy_eq_fieldEnergy {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (h : TreeVertex d → ℝ) (eta : D → IsingSpin) :
    GibbsLeaf.energy beta h D (extendFiniteSpin D eta) =
      FinitePosterior.fieldEnergy (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) (D.restrict h) eta := by
  classical
  have hsum : (∑ x ∈ D, h x * spinSign (extendFiniteSpin D eta x)) =
      ∑ x : D, h x * spinSign (eta x) := by
    rw [← Finset.sum_coe_sort D (fun x => h x * spinSign (extendFiniteSpin D eta x))]
    apply Finset.sum_congr rfl
    intro x _
    rw [extendFiniteSpin_apply D eta x]
  unfold GibbsLeaf.energy FinitePosterior.fieldEnergy finiteIsingEnergy
  rw [hsum]
  exact add_comm _ _

theorem GibbsLeaf.expectation_eq_fieldMean {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (h : TreeVertex d → ℝ)
    (q : (D → IsingSpin) → ℝ) :
    LeafGibbs.expectation
      (fun eta => GibbsLeaf.energy beta h D (extendFiniteSpin D eta)) q =
      FinitePosterior.fieldMean (finiteIsingEnergy beta D)
        (fun (eta : D → IsingSpin) v => spinSign (eta v)) q (D.restrict h) := by
  simp only [LeafGibbs.expectation, FinitePosterior.fieldMean,
    GibbsLeaf.energy_eq_fieldEnergy]

theorem HasFreeIsingLaw.finiteObservation_condExp_treeMean {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (v : D) :
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
      fun p => spinSign (p.1 v.1) |
      MeasurableSpace.comap (finiteObservation D t) inferInstance] =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => TreePathResponse.mean beta (PlantedSymmetry.observation t p) D v.1 := by
  have heq := hμ.finiteObservation_condExp D hD t (fun eta => spinSign (eta v))
  filter_upwards [heq] with p hp
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun p => spinSign (p.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp]
  simp only [TreePathResponse.mean, extendFiniteSpin_apply D _ v,
    GibbsLeaf.expectation_eq_fieldMean]
  rfl

theorem HasFreeIsingLaw.finiteObservation_normalizedResponse {d : ℕ} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (u v : D) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let m := MeasurableSpace.comap (finiteObservation D t) inferInstance
    (fun p => ((P[fun q => spinSign (q.1 u.1) * spinSign (q.1 v.1) | m]) p -
      (P[fun q => spinSign (q.1 u.1) | m]) p *
      (P[fun q => spinSign (q.1 v.1) | m]) p) /
      (1 - (P[fun q => spinSign (q.1 u.1) | m]) p ^ 2)) =ᵐ[P]
      fun p => GaussianTreeResponse.response beta D u.1 v.1
        (PlantedSymmetry.observation t p) := by
  dsimp only
  have hpair := hμ.finiteObservation_condExp D hD t
    (fun eta => spinSign (eta u) * spinSign (eta v))
  filter_upwards [hpair, hμ.finiteObservation_condExp_treeMean D hD t u,
    hμ.finiteObservation_condExp_treeMean D hD t v] with p hp hu hv
  change (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
    fun q => spinSign (q.1 u.1) * spinSign (q.1 v.1) |
    MeasurableSpace.comap (finiteObservation D t) inferInstance] p = _ at hp
  rw [hp, hu, hv]
  unfold GaussianTreeResponse.response TreePathResponse.response TreePathResponse.covariance
    LeafGibbs.covariance
  simp only [extendFiniteSpin_apply D _ u, extendFiniteSpin_apply D _ v,
    GibbsLeaf.expectation_eq_fieldMean, TreePathResponse.mean]
  rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_NormalizedPosteriorLimit
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem367

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem integrable_sq_and_integral_le_of_tendsto_ae
    (μ : Measure Ω) {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {K : ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    (hY : AEStronglyMeasurable Y μ) (hK : 0 ≤ K)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)))
    (hbound : ∀ᶠ n in atTop, Integrable (fun ω => (X n ω) ^ 2) μ ∧
      (∫ ω, (X n ω) ^ 2 ∂μ) ≤ K) :
    Integrable (fun ω => (Y ω) ^ 2) μ ∧ (∫ ω, (Y ω) ^ 2 ∂μ) ≤ K := by
  have hfatou : (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ) ≤ ENNReal.ofReal K := by
    calc
      (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ) =
          ∫⁻ ω, liminf (fun n => ENNReal.ofReal ((X n ω) ^ 2)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (hω.pow 2)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((X n ω) ^ 2) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => ((hX n).pow 2).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal K := by
        apply liminf_le_of_frequently_le'
        apply Filter.Eventually.frequently
        filter_upwards [hbound] with n hn
        rw [← ofReal_integral_eq_lintegral_ofReal hn.1
          (Filter.Eventually.of_forall (fun ω => sq_nonneg (X n ω)))]
        exact ENNReal.ofReal_le_ofReal hn.2
  refine ⟨⟨hY.pow 2, ?_⟩, ?_⟩
  · apply (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω)))).mpr
    exact hfatou.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω))) (hY.pow 2)]
    exact ENNReal.toReal_le_of_le_ofReal hK hfatou

section Gaussian

open PlantedSymmetry

theorem HasFreeIsingLaw.gaussian_posteriorResponse_tendsto_ae
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) (v w : TreeVertex d) :
    ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p) atTop
        (𝓝 (gaussianPosteriorResponse μ t v w p)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hi := (hμ.gaussian_posterior_field_bound hbeta t v).mono (fun _ h => h.1)
  have hi' : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t))[
        fun p => spinSign (p.1 v) | ⨆ n, finiteObservationFiltration D hD t n] p ∈
        Set.Ioo (-1 : ℝ) 1 := by
    rw [finiteObservationFiltration_iSup D hD hex t]
    exact hi
  have h := tendsto_ae_posteriorResponse
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) (finiteObservationFiltration D hD t)
    (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) hi'
  rw [finiteObservationFiltration_iSup D hD hex t] at h
  exact h

theorem HasFreeIsingLaw.gaussian_posteriorResponse_integrable_sq
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hex : ∀ w, ∃ n, w ∈ D n) (t : ℝ≥0) (v w : TreeVertex d)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᶠ n in atTop,
      Integrable (fun p => (posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p) ^ 2)
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
      (∫ p, (posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
        (MeasurableSpace.comap (finiteObservation (D n) t) inferInstance)
        (fun p => spinSign (p.1 v)) (fun p => spinSign (p.1 w)) p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤ K) :
    Integrable (fun p => (gaussianPosteriorResponse μ t v w p) ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
      (∫ p, (gaussianPosteriorResponse μ t v w p) ^ 2
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤ K := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply integrable_sq_and_integral_le_of_tendsto_ae
    (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
    (fun n => ((stronglyMeasurable_posteriorResponse _ _ _ _).mono
      (measurable_finiteObservation (D n) t).comap_le).aestronglyMeasurable)
    (((stronglyMeasurable_posteriorResponse _ _ _ _).mono
      (observationSigma_le (TreeVertex d) t)).aestronglyMeasurable)
    hK (hμ.gaussian_posteriorResponse_tendsto_ae hbeta D hD hex t v w) hbound

end Gaussian

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_TreeResponseObservedPosterior
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367

open PlantedSymmetry GaussianTreeResponse GaussianTreeCovariance

theorem HasFreeIsingLaw.finiteObservation_posteriorResponse_eq_observedRow
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (t : ℝ≥0) (u v : D) :
    posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun p => spinSign (p.1 u.1)) (fun p => spinSign (p.1 v.1)) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      observedRow beta D u.1 t v.1 := by
  unfold posteriorResponse posteriorCovariance observedRow
  simp only [ite_eq_left v.property]
  exact hμ.finiteObservation_normalizedResponse D hD t u v

theorem HasFreeIsingLaw.finiteObservation_posteriorResponse_sq_bound
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D)
    {t : ℝ≥0} (ht : 0 < t) (u v : D) (hu : u.1.1 = []) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    Integrable (fun p => (posteriorResponse P (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p) ^ 2) P ∧
    (∫ p, (posteriorResponse P (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p) ^ 2 ∂P) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.1.length := by
  dsimp only
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have he := hμ.finiteObservation_posteriorResponse_eq_observedRow D hD t u v
  have he2 : (fun p => (posteriorResponse (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
      (MeasurableSpace.comap (finiteObservation D t) inferInstance)
      (fun q => spinSign (q.1 u.1)) (fun q => spinSign (q.1 v.1)) p) ^ 2) =ᵐ[
        μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => observedRow beta D u.1 t v.1 p ^ 2 := by
    filter_upwards [he] with p hp
    exact congrArg (fun x : ℝ => x ^ 2) hp
  refine ⟨(integrable_observedRow_sq μ hbeta t hD u.property hu v.1).congr he2.symm, ?_⟩
  rw [integral_congr_ae he2]
  exact integral_observedRow_sq_le μ hbeta ht hD u.property hu v.1

theorem HasFreeIsingLaw.gaussian_posteriorResponse_sq_decay_of_exhaustion
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (D : ℕ → Finset (TreeVertex d)) (hD : Monotone D)
    (hconn : ∀ n, ConnectedFinset (D n)) (hex : ∀ w, ∃ n, w ∈ D n)
    {t : ℝ≥0} (ht : 0 < t) (r v : TreeVertex d) (hr : r.1 = []) :
    Integrable (fun p => gaussianPosteriorResponse μ t r v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, gaussianPosteriorResponse μ t r v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.length := by
  apply hμ.gaussian_posteriorResponse_integrable_sq hbeta D hD hex t r v
    (pow_nonneg (mul_nonneg (sq_nonneg _) (gaussianContraction_pos beta t).le) _)
  obtain ⟨nr, hnr⟩ := hex r
  obtain ⟨nv, hnv⟩ := hex v
  filter_upwards [eventually_ge_atTop (max nr nv)] with n hn
  have hrn : r ∈ D n := hD (le_trans (le_max_left nr nv) hn) hnr
  have hvn : v ∈ D n := hD (le_trans (le_max_right nr nv) hn) hnv
  exact hμ.finiteObservation_posteriorResponse_sq_bound hbeta (D n) (hconn n) ht
    ⟨r, hrn⟩ ⟨v, hvn⟩ hr

theorem HasFreeIsingLaw.gaussian_posteriorResponse_sq_decay
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t) (r v : TreeVertex d) (hr : r.1 = []) :
    Integrable (fun p => gaussianPosteriorResponse μ t r v p ^ 2)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ∧
    (∫ p, gaussianPosteriorResponse μ t r v p ^ 2
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.length := by
  obtain ⟨D, hD, hc, hex⟩ := exists_connected_exhaustion r
  exact hμ.gaussian_posteriorResponse_sq_decay_of_exhaustion hbeta D hD
    (fun n => (hc n).1) hex ht r v hr

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_CanonicalPathResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem367.FinitePathGibbs

theorem mean_eq_posterior_mean (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (f : (Fin (n + 1) → IsingSpin) → ℝ) :
    mean beta root h n f =
      FinitePosterior.mean (energy beta root h n) (fun _ => 0) f 0 := by
  unfold mean FinitePosterior.mean FinitePosterior.partition
  simp only [FinitePosterior.weight, zero_mul, add_zero]
  simp_rw [mass_eq_exp_energy, partition_eq_sum_exp, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem coordinate_mean_mem_Ioo (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (i : Fin (n + 1)) :
    mean beta root h n (fun x => spinSign (x i)) ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [mean_eq_posterior_mean]
  let : Nonempty (Fin (n + 1) → IsingSpin) := ⟨fun _ => .pos⟩
  apply FinitePosterior.spin_mean_mem_Ioo
  · intro x
    cases x i <;> simp [spinSign]
  · exact ⟨fun _ => .neg, rfl⟩
  · exact ⟨fun _ => .pos, rfl⟩

theorem coordinate_mean_affine (beta root : ℝ) (h : ℕ → ℝ) (n : ℕ)
    (i : Fin n) :
    mean beta root h n (fun x => spinSign (x i.succ)) =
      PosteriorChain.intercept beta (backwardField beta h n i) +
        PosteriorChain.slope beta (backwardField beta h n i) *
          mean beta root h n (fun x => spinSign (x i.castSucc)) := by
  have hh := InhomogeneousChain.coordinateMean_affine
    (fun j => PosteriorChain.transition beta (backwardField beta h n j))
    (rootLaw beta root h n) spinSign
    (fun j => PosteriorChain.intercept beta (backwardField beta h n j))
    (fun j => PosteriorChain.slope beta (backwardField beta h n j))
    (sum_rootLaw beta root h n)
    (fun j => PosteriorChain.transition_sum beta (backwardField beta h n j))
    (fun j => PosteriorChain.transition_spinMean_affine beta (backwardField beta h n j)) n i
  simpa only [InhomogeneousChain.coordinateMean, ← mass_eq_jointWeight, mean] using hh

theorem backwardField_eq_cavityFromSites {beta : ℝ} (hbeta : 0 ≤ beta)
    (root : ℝ) (h : ℕ → ℝ) (n : ℕ) (i : Fin n) :
    backwardField beta h n i =
      (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
        (Real.artanh (mean beta root h n (fun x => spinSign (x i.castSucc))),
          Real.artanh (mean beta root h n (fun x => spinSign (x i.succ))))).2 := by
  have hh := PosteriorChain.cavityFromSites_affine_mean_snd hbeta
    (backwardField beta h n i)
    (Real.artanh (mean beta root h n (fun x => spinSign (x i.castSucc))))
  rw [Real.tanh_artanh (coordinate_mean_mem_Ioo beta root h n i.castSucc),
    ← coordinate_mean_affine beta root h n i] at hh
  exact hh.symm

end Problem367.FinitePathGibbs

namespace Problem367.TreePathResponse

theorem root_response_eq_canonical_product {d : ℕ} {beta : ℝ}
    (hbeta : 0 ≤ beta) (h : TreeVertex d → ℝ)
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hr : ConnectedHull.root d ∈ D) {v : TreeVertex d} (hv : v ∈ D) :
    response beta h D (ConnectedHull.root d) v =
      Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
          (orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
            (ConnectedHull.takeVertex v (i + 1))) := by
  obtain ⟨y, hy⟩ := exists_path_fields beta h hD hr hv
  have hmean (i : Fin (v.1.length + 1)) :
      mean beta h D (ConnectedHull.path v i) =
        FinitePathGibbs.mean beta (y 0) (PathPosterior.childFields y) v.1.length
          (fun x => spinSign (x i)) :=
    hy (fun x => spinSign (x i))
  have hback (i : ℕ) (hi : i < v.1.length) :
      FinitePathGibbs.backwardField beta (PathPosterior.childFields y) v.1.length i =
        orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
          (ConnectedHull.takeVertex v (i + 1)) := by
    have hh := FinitePathGibbs.backwardField_eq_cavityFromSites hbeta
      (y 0) (PathPosterior.childFields y) v.1.length ⟨i, hi⟩
    rw [← hmean (Fin.castSucc ⟨i, hi⟩), ← hmean (Fin.succ ⟨i, hi⟩)] at hh
    exact hh
  have hprod :
      (∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
        (FinitePathGibbs.backwardField beta (PathPosterior.childFields y) v.1.length i)) =
      ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
        (orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
          (ConnectedHull.takeVertex v (i + 1))) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hback i (Finset.mem_range.mp hi)]
  have hcov : covariance beta h D (ConnectedHull.root d) v =
      (1 - mean beta h D (ConnectedHull.root d) ^ 2) * Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
          (orientedCavity hbeta h D (ConnectedHull.takeVertex v i)
            (ConnectedHull.takeVertex v (i + 1))) := by
    rw [← hprod]
    have hm := hy (fun x => spinSign (x 0))
    have hn := hy (fun x => spinSign (x (Fin.last v.1.length)))
    have hp := hy (fun x => spinSign (x 0) * spinSign (x (Fin.last v.1.length)))
    simp only [ConnectedHull.path_zero, ConnectedHull.path_last] at hm hn hp
    unfold covariance LeafGibbs.covariance mean
    rw [hp, hm, hn]
    exact FinitePathGibbs.endpointCovariance_eq beta (y 0)
      (PathPosterior.childFields y) v.1.length
  rw [response, hcov]
  have hp := (variance_pos beta h hr).ne'
  field_simp

end Problem367.TreePathResponse

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_InfiniteCanonicalPathResponse
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators

namespace Problem367

open PlantedSymmetry

namespace CavityFieldLimit

theorem finiteSiteField_eq_treeField {d : ℕ} (beta : ℝ)
    (D : Finset (TreeVertex d)) (v : D) (y : TreeVertex d → ℝ) :
    finiteSiteField beta D v y = TreePathResponse.field beta y D v.1 := by
  unfold finiteSiteField TreePathResponse.field TreePathResponse.mean
  rw [GibbsLeaf.expectation_eq_fieldMean]
  simp only [extendFiniteSpin_apply D _ v]

theorem infiniteCavityField_eq_snd {d : ℕ} {beta : ℝ} (hbeta : 0 ≤ beta)
    (u v : TreeVertex d) (y : TreeVertex d → ℝ) :
    infiniteCavityField hbeta v u y =
      (cavityFromSites (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta)
        (Real.artanh (infiniteGibbsSpinMean beta u y),
          Real.artanh (infiniteGibbsSpinMean beta v y))).2 :=
  CavityArray.field_reverse _ _ _ u v

end CavityFieldLimit

open CavityFieldLimit

theorem HasFreeIsingLaw.gaussian_rootResponse_eq_canonical_product
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    gaussianPosteriorResponse μ t (ConnectedHull.root d) v =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => rootResponseProduct hbeta v (observation t p) := by
  classical
  let D := connectedExhaustion v
  have hpath (i : ℕ) (hi : i ≤ v.1.length) (n : ℕ) :
      ConnectedHull.takeVertex v i ∈ D n := by
    exact ConnectedHull.prefix_mem_hull (Finset.mem_insert_self v (treeBallFinset d n)) hi
  have hr (n : ℕ) : ConnectedHull.root d ∈ D n := by
    simpa only [ConnectedHull.prefix_zero] using hpath 0 (Nat.zero_le _) n
  have hv (n : ℕ) : v ∈ D n := mem_connectedExhaustion v n
  have hconn (n : ℕ) : ConnectedFinset (D n) := connectedExhaustion_connected v n
  have hex (u : TreeVertex d) : ∃ n, u ∈ D n :=
    (eventually_mem_connectedExhaustion v u).exists
  have hfield (i : Fin (v.1.length + 1)) :
      ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
        Tendsto (fun n => TreePathResponse.field beta (observation t p) (D n)
          (ConnectedHull.takeVertex v i)) atTop
          (𝓝 (Real.artanh (infiniteGibbsSpinMean beta
            (ConnectedHull.takeVertex v i) (observation t p)))) := by
    have hh := hμ.exhaustionSiteField_tendsto_ae hbeta D
      (connectedExhaustion_monotone v) hconn hex (ConnectedHull.takeVertex v i)
      (hpath i (by omega)) t
    simpa only [finiteSiteField_eq_treeField] using hh
  have hprod : ∀ᵐ p ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t),
      Tendsto (fun n => Real.tanh beta ^ v.1.length *
        ∏ i ∈ Finset.range v.1.length, responseAttenuation (Real.tanh beta)
          (TreePathResponse.orientedCavity hbeta (observation t p) (D n)
            (ConnectedHull.takeVertex v i) (ConnectedHull.takeVertex v (i + 1))))
        atTop (𝓝 (rootResponseProduct hbeta v (observation t p))) := by
    filter_upwards [ae_all_iff.mpr hfield] with p hp
    apply Tendsto.const_mul
    apply tendsto_finsetProd
    intro i hi
    have hi' : i < v.1.length := Finset.mem_range.mp hi
    have hleft := hp ⟨i, by omega⟩
    have hright := hp ⟨i + 1, by omega⟩
    have hc := (continuous_snd.comp (continuous_cavityFromSites
      (tanh_nonneg_of_beta_nonneg hbeta) (Real.tanh_lt_one beta))).continuousAt.tendsto.comp
      (hleft.prodMk_nhds hright)
    simp only [Function.comp_apply] at hc
    rw [← infiniteCavityField_eq_snd hbeta] at hc
    exact (continuous_responseAttenuation (Real.tanh_sq_lt_one beta).le).continuousAt.tendsto.comp hc
  have hresponse := hμ.gaussian_posteriorResponse_tendsto_ae hbeta D
    (connectedExhaustion_monotone v) hex t (ConnectedHull.root d) v
  have hfinite (n : ℕ) := hμ.finiteObservation_normalizedResponse
    (D n) (hconn n) t ⟨ConnectedHull.root d, hr n⟩ ⟨v, hv n⟩
  filter_upwards [hresponse, hprod, ae_all_iff.mpr hfinite] with p hp hprod hfinite
  apply tendsto_nhds_unique hp
  apply hprod.congr'
  apply Eventually.of_forall
  intro n
  exact (hfinite n).trans
    (TreePathResponse.root_response_eq_canonical_product hbeta (observation t p)
      (hconn n) (hr n) (hv n)) |>.symm

theorem HasFreeIsingLaw.infiniteGibbsRootResponse_eq_canonical_product
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    (fun p => infiniteGibbsResponse beta (ConnectedHull.root d) v (observation t p)) =ᵐ[
      μ.prod (gaussianNoiseLaw (TreeVertex d) t)]
      fun p => rootResponseProduct hbeta v (observation t p) := by
  filter_upwards [hμ.gaussian_rootResponse_eq_canonical_product hbeta t v,
    hμ.infiniteGibbsCovariance_eq_posterior t (ConnectedHull.root d) v,
    hμ.infiniteGibbsSpinMean_eq_posterior t (ConnectedHull.root d)] with p hp hc hm
  rw [infiniteGibbsResponse, hc, hm]
  exact hp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Ising_CopyResponseRowSummability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopyStationarity
open PlantedSymmetry GaussianTreeResponse GaussianTreeCovariance

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem row_identDistrib_gaussian
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : TreeVertex d) :
    IdentDistrib (row beta t v)
      (gaussianPosteriorResponse μ t (ConnectedHull.root d) v)
      (observationLaw μ) (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have hobs := (IsingConditionalCopyBounds.hasLaw_observationLaw_eval μ t).identDistrib
    (show HasLaw (observation t)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t)).map (observation t))
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) from
      ⟨(measurable_observation t).aemeasurable, rfl⟩)
  have hr := hobs.comp (measurable_infiniteGibbsResponse beta (ConnectedHull.root d) v)
  have heq := (hμ.infiniteGibbsRootResponse_eq_canonical_product hb t v).trans
    (hμ.gaussian_rootResponse_eq_canonical_product hb t v).symm
  exact hr.trans (IdentDistrib.of_ae_eq hr.aemeasurable_snd heq)

theorem integrable_row_sq_and_integral_le
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d) :
    Integrable (fun x => row beta t v x ^ 2) (observationLaw μ) ∧
      (∫ x, row beta t v x ^ 2 ∂observationLaw μ) ≤
        (Real.tanh beta ^ 2 * gaussianContraction beta t) ^ v.1.length := by
  have hi := (row_identDistrib_gaussian hμ hb t v).sq
  have hg := hμ.gaussian_posteriorResponse_sq_decay hb ht (ConnectedHull.root d) v rfl
  exact ⟨hi.integrable_iff.mpr hg.1, hi.integral_eq.trans_le hg.2⟩

theorem observation_row_energy
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    (∀ᵐ x ∂observationLaw μ, Summable (fun v => row beta t v x ^ 2)) ∧
      Integrable (fun x => ∑' v, row beta t v x ^ 2) (observationLaw μ) ∧
      (∫ x, ∑' v, row beta t v x ^ 2 ∂observationLaw μ) ≤
        1 + (d : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t) /
          (1 - ((d - 1 : ℕ) : ℝ) * (Real.tanh beta ^ 2 * gaussianContraction beta t)) := by
  have hc := integrable_row_sq_and_integral_le hμ hb ht
  have hnonneg := mul_nonneg (sq_nonneg (Real.tanh beta)) (gaussianContraction_pos beta t).le
  have hsmall := gaussian_radial_ratio_lt_one ht hcrit
  have hs : Summable (fun v => ∫ x, row beta t v x ^ 2 ∂observationLaw μ) :=
    summable_of_tree_radial_le (C := 1)
      (fun v => integral_nonneg (fun x => sq_nonneg _))
      (fun v => by simpa only [one_mul] using (hc v).2) hnonneg hsmall
  obtain ⟨hae, hint⟩ := DiscrepancyEnergy.sq_row_integrable_of_summable_integrals
    (fun v => (hc v).1) hs
  refine ⟨hae, hint, ?_⟩
  simpa only [one_mul] using integral_tsum_sq_le_of_tree_radial_bound (C := 1)
    (fun v => (hc v).1) (fun v => by simpa only [one_mul] using (hc v).2) hnonneg hsmall

theorem copies_rows_summable_ae_oai
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    {t : ℝ≥0} (ht : 0 < t)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∀ᵐ q ∂copies beta μ,
      Summable (fun v => row beta t v q.2.1 ^ 2) ∧
        Summable (fun v => row beta t v q.2.2 ^ 2) := by
  obtain ⟨hl, hr⟩ := measurePreserving_observations (beta := beta) (μ := μ)
  have hrow := (observation_row_energy hμ hb ht hcrit).1
  filter_upwards [hl.quasiMeasurePreserving.ae hrow,
    hr.quasiMeasurePreserving.ae hrow] with q hqL hqR
  exact ⟨hqL, hqR⟩

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.IsingCopyResponseRowPaths.copies_rows_summable_ae_oai := @OAI.Problem367.IsingCopyResponseRowPaths.copies_rows_summable_ae_oai
