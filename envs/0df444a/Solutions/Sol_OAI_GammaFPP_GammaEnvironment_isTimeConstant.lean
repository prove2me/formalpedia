-- Prove2me | solution 1 for OAI.GammaFPP.GammaEnvironment.isTimeConstant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T04:00:03.010836+00:00
-- url     : https://prove2.me/submissions/27441f50-38d0-4299-a9ec-c3e5e4a624cf

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage
import Definitions.Def_OAIW2GF000

section
-- module Solutions.OAIW2_GammaFPP.Compat
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_CoordinateTails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

theorem straightEdge_injective (p : Vertex) (d : Step) :
    Function.Injective (straightEdge p d) := by
  intro i j h
  cases d <;> simp [straightEdge, Step.edge, Step.delta, Prod.ext_iff] at h <;> omega

theorem pathCost_replicate (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ i ∈ range n, w (straightEdge p d i) := by
  induction n generalizing p with
  | zero => simp [pathCost]
  | succ n ih =>
    rw [List.replicate_succ, pathCost, ih, sum_range_succ']
    simp [straightEdge, Nat.cast_add, add_smul, add_assoc, add_comm]

theorem pathCost_replicate_edgeSet (w : Edge → ℝ) (p : Vertex) (d : Step) (n : ℕ) :
    pathCost w p (List.replicate n d) =
      ∑ e ∈ (range n).image (straightEdge p d), w e := by
  rw [sum_image (fun i _ j _ hij => straightEdge_injective p d hij)]
  exact pathCost_replicate w p d n

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.FirstPassage_SpatialModulus
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Finset Filter Set
open scoped ENNReal Topology

theorem latticeBox_card (n : ℕ) : (latticeBox n).card = (2*n+1)^2 := by
  have hi : (Finset.Icc (-(n : ℤ)) n).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  simp [latticeBox, hi, pow_two]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem summable_box_connection_bound {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => (2*(n : ℝ)+1)^4 * (2 * Real.exp (-ε*n/4))) := by
  have hs (k : ℕ) := Real.summable_pow_mul_exp_neg_nat_mul k
    (show 0 < ε/4 by linarith)
  have ht := (((((hs 4).mul_left 32).add ((hs 3).mul_left 64)).add
    ((hs 2).mul_left 48)).add ((hs 1).mul_left 16)).add ((hs 0).mul_left 2)
  apply ht.congr
  intro n
  simp only [pow_one, pow_zero]
  have he : -(ε/4)*(n : ℝ) = -ε*n/4 := by ring
  rw [he]
  ring

end PlanarFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_Environment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

/-- The joint law on a finite set of edges, including the empty set. -/
theorem IidEnvironment.finiteJointLaw (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) :
    P.map (fun ω (e : S) => τ e ω) = Measure.pi (fun _ : S => ν) := by
  have hi := h.independent.precomp
    (Subtype.val_injective : Function.Injective (fun e : S => (e : PlanarFPP.Edge)))
  rw [iIndepFun.map_fun_eq_pi_map (fun e : S => (h.measurable e).aemeasurable) hi]
  simp only [h.marginal]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ASMeanBridge
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory Filter Topology PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Summable deviations at the countable tolerances `1 / (k + 1)` imply
almost-sure convergence to zero. The events need not be measurable. -/
theorem ae_tendsto_zero_of_summable_deviations (X : ℕ → Ω → ℝ)
    (hsum : ∀ k : ℕ,
      (∑' n, P {ω | 1 / ((k : ℝ) + 1) ≤ |X n ω|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n in atTop,
      ω ∉ {ω | 1 / ((k : ℝ) + 1) ≤ |X n ω|} :=
    ae_all_iff.mpr (fun k => ae_eventually_notMem (hsum k))
  filter_upwards [hall] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k] with n hn
  have hn' : |X n ω| < 1 / ((k : ℝ) + 1) := lt_of_not_ge hn
  simpa only [Real.dist_eq, sub_zero] using hn'.trans hk

/-- Add a convergent deterministic center after Borel--Cantelli. -/
theorem ae_tendsto_of_summable_centered_deviations
    (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (L : ℝ)
    (ha : Tendsto a atTop (𝓝 L))
    (hsum : ∀ k : ℕ,
      (∑' n, P {ω | 1 / ((k : ℝ) + 1) ≤ |X n ω - a n|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 L) := by
  filter_upwards [ae_tendsto_zero_of_summable_deviations
    (fun n ω => X n ω - a n) hsum] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add ha

/-- Summable centered lattice-passage deviations identify the almost-sure
limit with the Fekete limit of the means. -/
theorem GammaEnvironment.ae_lattice_limit_of_summable_deviations
    {τ : Edge → Ω → ℝ} {shape rate : ℝ}
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex)
    (hsum : ∀ k : ℕ, (∑' n : ℕ, P {ω |
      1 / ((k : ℝ) + 1) ≤
        |passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ) -
          meanPassageSequence P τ z n / (n : ℝ)|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ))
      atTop (𝓝 (directionalMeanConstant h hs hr z)) :=
  ae_tendsto_of_summable_centered_deviations _ _ _
    (h.meanPassageSequence_tendsto hs hr z) hsum

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RealMeanExtension
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open Topology
open scoped NNReal

/-- Agreement with the original lattice mean once its rational L1 bound is supplied.
No seminorm or continuity premise on that lattice function is needed. -/
theorem realMeanExtension_integerPair (m : PlanarFPP.Vertex → ℝ)
    (hm : ∀ (k : ℕ) (x : PlanarFPP.Vertex), m (k • x) = (k : ℝ) * m x)
    (C : ℝ≥0)
    (hlip : ∀ q r, |rationalMean m q-rationalMean m r| ≤ (C : ℝ) *
      (|(q.1 : ℝ)-(r.1 : ℝ)| + |(q.2 : ℝ)-(r.2 : ℝ)|))
    (x : PlanarFPP.Vertex) :
    realMeanExtension (rationalMean m) ((x.1 : ℝ), (x.2 : ℝ)) = m x := by
  have he := realMeanExtension_on_rat
    (rational_l1_lipschitz (rationalMean m) C hlip).uniformContinuous
    ((x.1 : ℚ), (x.2 : ℚ))
  simpa only [rationalPairCast, Rat.cast_intCast, rationalMean_integerPair m hm] using he

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanPairSeminorm
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The extended mean seminorm agrees on lattice points with the normalized
expectation limit of passage times. -/
theorem gammaMeanPairSeminorm_integerPair
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (x : Vertex) : gammaMeanPairSeminorm h hs hr ((x.1 : ℝ), (x.2 : ℝ)) =
      directionalMeanConstant h hs hr x := by
  change realMeanExtension (rationalMean (directionalMeanConstant h hs hr))
    ((x.1 : ℝ), (x.2 : ℝ)) = _
  apply realMeanExtension_integerPair (directionalMeanConstant h hs hr)
    (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    ⟨shape/rate, (div_pos hs hr).le⟩
  exact rationalMean_l1 _ (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MGF
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

/-- Exponential weighting changes the Gamma rate from `rate` to `rate - theta`. -/
lemma gamma_weighted_density {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) (x : ℝ) :
    gammaPDF shape rate x * ENNReal.ofReal (exp (theta * x)) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) *
        gammaPDF shape (rate - theta) x := by
  have hs : 0 < rate - theta := sub_pos.mpr htheta
  have hc : 0 ≤ (rate / (rate - theta)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hrate hs) shape).le
  by_cases hx : 0 ≤ x
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc]
    congr 1
    have hexp : exp (-(rate * x)) * exp (theta * x) =
        exp (-((rate - theta) * x)) := by
      rw [← exp_add]
      congr 1
      ring
    calc
      rate ^ shape / Gamma shape * x ^ (shape - 1) * exp (-(rate * x)) *
          exp (theta * x) =
          rate ^ shape / Gamma shape * x ^ (shape - 1) *
            (exp (-(rate * x)) * exp (theta * x)) := by ring
      _ = rate ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x)) := by rw [hexp]
      _ = (rate / (rate - theta)) ^ shape *
          ((rate - theta) ^ shape / Gamma shape * x ^ (shape - 1) *
            exp (-((rate - theta) * x))) := by
        rw [Real.div_rpow hrate.le hs.le]
        have hpow : (rate - theta) ^ shape ≠ 0 :=
          (Real.rpow_pos_of_pos hs shape).ne'
        have hgamma : Gamma shape ≠ 0 := (Real.Gamma_pos_of_pos hshape).ne'
        field_simp [hpow, hgamma]
  · rw [gammaPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

/-- The nonnegative exponential moment from the normalized density with shifted rate. -/
theorem gamma_lintegral_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x)) ∂gammaMeasure shape rate) =
      ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
  change (∫⁻ x : ℝ, ENNReal.ofReal (exp (theta * x))
    ∂volume.withDensity (gammaPDF shape rate)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (by unfold gammaPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, gamma_weighted_density hshape hrate htheta]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one hshape (sub_pos.mpr htheta), mul_one]

/-- Exponential functions are integrable under the Gamma law for `theta < rate`. -/
theorem gamma_integrable_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    Integrable (fun x : ℝ => exp (theta * x)) (gammaMeasure shape rate) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Filter.Eventually.of_forall fun x => (exp_pos (theta * x)).le)).mp
  rw [gamma_lintegral_exp hshape hrate htheta]
  exact ENNReal.ofReal_ne_top

/-- Gamma exponential moments, as in paper 210, Lemma `df:ga:moment`. -/
theorem gamma_integral_exp {shape rate theta : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (htheta : theta < rate) :
    (∫ x : ℝ, exp (theta * x) ∂gammaMeasure shape rate) =
      (rate / (rate - theta)) ^ shape := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => (exp_pos (theta * x)).le) (by fun_prop),
    gamma_lintegral_exp hshape hrate htheta]
  exact ENNReal.toReal_ofReal
    (Real.rpow_pos_of_pos (div_pos hrate (sub_pos.mpr htheta)) shape).le

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

lemma IidEnvironment.measurable_edgeSum (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) : Measurable (edgeSum S τ) :=
  Finset.measurable_sum S (fun e _ => h.measurable e)

/-- Integral transport along the joint law of a finite edge set. -/
lemma IidEnvironment.integral_finiteJoint (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) (f : (S → ℝ) → ℝ) (hf : Measurable f) :
    (∫ ω, f (fun e : S => τ e ω) ∂P) =
      ∫ x : S → ℝ, f x ∂Measure.pi (fun _ : S => ν) := by
  rw [← h.finiteJointLaw S]
  exact (integral_map
    (Measurable.of_eval (fun e : S => h.measurable e)).aemeasurable
    hf.aestronglyMeasurable).symm

variable {shape rate theta : ℝ}

/-- The nonnegative exponential moment of a finite iid Gamma edge sum. -/
theorem GammaEnvironment.lintegral_exp_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) =
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card := by
  classical
  let X : PlanarFPP.Edge → Ω → ℝ≥0∞ :=
    fun e ω => ENNReal.ofReal (Real.exp (theta * τ e ω))
  have hX : ∀ e, Measurable (X e) := by
    intro e
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable e)))
  have hXi : iIndepFun X P := h.independent.comp
    (fun _ (x : ℝ) => ENNReal.ofReal (Real.exp (theta * x))) (fun _ => by fun_prop)
  have hpoint (ω : Ω) : ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) =
      ∏ e ∈ S, X e ω := by
    rw [edgeSum, Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg (fun e _ => (Real.exp_pos _).le)
  have hm (e : PlanarFPP.Edge) :
      (∫⁻ ω, X e ω ∂P) = ENNReal.ofReal ((rate / (rate - theta)) ^ shape) := by
    change (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * τ e ω)) ∂P) = _
    rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (Real.exp (theta * x)))
      (by fun_prop) (h.measurable e), h.marginal e]
    exact gamma_lintegral_exp hshape hrate htheta
  simp_rw [hpoint]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun S X hXi hX]
  simp only [hm, Finset.prod_const]

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate theta : ℝ}

/-- Exponential Markov bound for a real parameter `theta` and an arbitrary real threshold. -/
theorem GammaEnvironment.exponential_markov_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta : theta < rate) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  have hm : Measurable (fun ω => ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (h.measurable_edgeSum S)))
  calc
    P {ω | theta * a ≤ theta * edgeSum S τ ω} ≤
        P {ω | ENNReal.ofReal (Real.exp (theta * a)) ≤
          ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω))} := by
      apply measure_mono
      intro ω hω
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Real.exp (theta * edgeSum S τ ω)) ∂P) /
        ENNReal.ofReal (Real.exp (theta * a)) :=
      meas_ge_le_lintegral_div hm.aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
    _ = _ := by rw [h.lintegral_exp_edgeSum hshape hrate htheta S]

/-- Gamma Chernoff upper-tail estimate for `0 < theta < rate`. -/
theorem GammaEnvironment.upper_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_pos : 0 < theta) (htheta : theta < rate)
    (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | a ≤ edgeSum S τ ω} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate htheta S a)
  intro ω hω
  exact mul_le_mul_of_nonneg_left hω htheta_pos.le

/-- Gamma Chernoff lower-tail estimate for `theta < 0`. -/
theorem GammaEnvironment.lower_tail_edgeSum
    (h : GammaEnvironment shape rate P τ) (hshape : 0 < shape) (hrate : 0 < rate)
    (htheta_neg : theta < 0) (S : Finset PlanarFPP.Edge) (a : ℝ) :
    P {ω | edgeSum S τ ω ≤ a} ≤
      (ENNReal.ofReal ((rate / (rate - theta)) ^ shape)) ^ S.card /
        ENNReal.ofReal (Real.exp (theta * a)) := by
  apply le_trans (measure_mono ?_)
    (h.exponential_markov_edgeSum hshape hrate (htheta_neg.trans hrate) S a)
  intro ω hω
  exact mul_le_mul_of_nonpos_left hω htheta_neg.le

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPath
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

lemma trace_edge_length (p : Vertex) (ds : List Step) :
    ((trace p ds).map traversalEdge).length = ds.length := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih =>
    simpa only [trace, List.map_cons, List.length_cons] using
      (congrArg Nat.succ (ih (p + d.delta)))

lemma pathCost_trace_edge_sum (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p ds = (((trace p ds).map traversalEdge).map w).sum := by
  induction ds generalizing p with
  | nil => rfl
  | cons d ds ih => simp only [pathCost, trace, List.map_cons, List.sum_cons,
      traversalEdge, ih]

/-- Only a trail's traversal sum can be replaced by its distinct-edge set sum. -/
lemma pathCost_eq_distinct_edgeSum (w : Edge → ℝ) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) :
    pathCost w p ds = ∑ e ∈ ((trace p ds).map traversalEdge).toFinset, w e := by
  classical
  rw [pathCost_trace_edge_sum]
  exact (List.sum_toFinset w hn).symm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Genuine Gamma lower tail for any fixed trail, with arbitrary real threshold.
The positive parameter s uses the native MGF at theta=-s. -/
theorem GammaEnvironment.cheap_path_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) (t : ℝ) :
    P {ω | pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ ds.length /
        ENNReal.ofReal (Real.exp (-s * t)) := by
  classical
  have hc : ((trace p ds).map traversalEdge).toFinset.card = ds.length := by
    rw [List.toFinset_card_of_nodup hn, trace_edge_length]
  have he (ω : Ω) : edgeSum ((trace p ds).map traversalEdge).toFinset τ ω =
      pathCost (fun e => τ e ω) p ds := by
    exact (pathCost_eq_distinct_edgeSum (fun e => τ e ω) p ds hn).symm
  have hb := h.lower_tail_edgeSum hs hr (neg_neg_of_pos hsp)
    ((trace p ds).map traversalEdge).toFinset t
  simpa only [he, hc, sub_neg_eq_add] using hb

/-- The probability that a finite family contains a cheap trail is bounded by
its cardinality times the single-trail estimate. -/
theorem GammaEnvironment.cheap_path_family_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (F : Finset (List Step)) (n : ℕ)
    (hF : ∀ ds ∈ F, ((trace p ds).map traversalEdge).Nodup ∧ ds.length = n)
    (t : ℝ) :
    P {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} ≤
      (F.card : ℝ≥0∞) * ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
  classical
  have he : {ω | ∃ ds ∈ F, pathCost (fun e => τ e ω) p ds ≤ t} =
      ⋃ ds ∈ F, {ω | pathCost (fun e => τ e ω) p ds ≤ t} := by
    ext ω
    simp
  rw [he]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _ds ∈ F, ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp (-s * t))) := by
      apply Finset.sum_le_sum
      intro ds hds
      simpa only [(hF ds hds).2] using
        h.cheap_path_probability hs hr s hsp p ds (hF ds hds).1 t
    _ = _ := by simp

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathCounting
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

attribute [local instance] OAI.GammaFPP.cheapStepFintype
private lemma cheapStep_card : Fintype.card Step = 4 := by decide

lemma card_fixedStepLists_le (n : ℕ) : (fixedStepLists n).card ≤ 4 ^ n := by
  classical
  calc
    (fixedStepLists n).card ≤ (Finset.univ : Finset (Fin n → Step)).card :=
      Finset.card_image_le
    _ = 4 ^ n := by rw [Finset.card_univ, Fintype.card_fun, cheapStep_card, Fintype.card_fin]

lemma card_fixedTrailLists_le (p : Vertex) (n : ℕ) :
    (fixedTrailLists p n).card ≤ 4 ^ n := by
  classical
  exact (Finset.card_filter_le _ _).trans (card_fixedStepLists_le n)

/-- Exact event equality; there is no hidden restriction to a selected optimizer. -/
lemma fixedTrail_event_eq {Ω : Type*} (τ : Edge → Ω → ℝ)
    (p : Vertex) (n : ℕ) (t : ℝ) :
    {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} =
    {ω | ∃ ds ∈ fixedTrailLists p n, pathCost (fun e => τ e ω) p ds ≤ t} := by
  ext ω
  simp only [Set.mem_ofPred_eq, mem_fixedTrailLists]
  constructor
  · rintro ⟨ds, hl, hn, hc⟩
    exact ⟨ds, ⟨hl, hn⟩, hc⟩
  · rintro ⟨ds, ⟨hl, hn⟩, hc⟩
    exact ⟨ds, hl, hn, hc⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual fixed-length trails, with a proved four-way exponential count. -/
theorem GammaEnvironment.cheap_fixed_length_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (s : ℝ) (hsp : 0 < s) (p : Vertex) (n : ℕ) (t : ℝ) :
    P {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ t} ≤
      ((4 ^ n : ℕ) : ℝ≥0∞) *
        ((ENNReal.ofReal ((rate / (rate + s)) ^ shape)) ^ n /
          ENNReal.ofReal (Real.exp (-s * t))) := by
  rw [fixedTrail_event_eq]
  have hb := h.cheap_path_family_probability hs hr s hsp p (fixedTrailLists p n) n
    (fun ds hds => ((mem_fixedTrailLists p n ds).mp hds).symm) t
  refine hb.trans (mul_le_mul_left ?_ _)
  exact_mod_cast card_fixedTrailLists_le p n

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapPathDecay
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP
open scoped ENNReal

lemma cheapChernoff_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapChernoff shape rate := by
  have hl : 0 < Real.log (16 : ℝ) := Real.log_pos (by norm_num)
  exact mul_pos hr (sub_pos.mpr (Real.one_lt_exp_iff.mpr (div_pos hl hs)))

lemma cheapSlope_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < cheapSlope shape rate :=
  div_pos (Real.log_pos (by norm_num)) (cheapChernoff_pos hs hr)

/-- The exact native Gamma Laplace factor is 1/16 at the chosen parameter. -/
lemma cheapChernoff_factor {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    (rate / (rate + cheapChernoff shape rate)) ^ shape = (1 / 16 : ℝ) := by
  have hd : rate + cheapChernoff shape rate =
      rate * Real.exp (Real.log 16 / shape) := by
    unfold cheapChernoff
    ring
  have hratio : rate / (rate + cheapChernoff shape rate) =
      Real.exp (-(Real.log 16 / shape)) := by
    rw [hd, Real.exp_neg]
    field_simp [hr.ne', Real.exp_ne_zero]
  rw [hratio, ← Real.exp_mul]
  have he : -(Real.log 16 / shape) * shape = -Real.log 16 := by
    field_simp [hs.ne']
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
  norm_num

lemma cheapChernoff_mul_slope {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    cheapChernoff shape rate * cheapSlope shape rate = Real.log 2 := by
  unfold cheapSlope
  field_simp [(cheapChernoff_pos hs hr).ne']

/-- Exact cancellation of counting, Laplace factor and linear threshold. -/
lemma cheap_count_bound_eq {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) (n : ℕ) :
    (4 : ℝ)^n * (((rate / (rate + cheapChernoff shape rate)) ^ shape)^n /
      Real.exp (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) =
        (1 / 2 : ℝ)^n := by
  rw [cheapChernoff_factor hs hr]
  have he : -cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)) =
      (n : ℝ) * (-Real.log 2) := by
    have hc := cheapChernoff_mul_slope hs hr
    calc
      _ = -(cheapChernoff shape rate * cheapSlope shape rate) * (n : ℝ) := by ring
      _ = _ := by rw [hc]; ring
  rw [he, Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← div_pow, ← mul_pow]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- All actual trails of n steps from p are exponentially unlikely to cost at
most c*n. This includes n=0, where the empty path has probability one. -/
theorem GammaEnvironment.cheap_fixed_length_decay_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (n : ℕ) :
    P.real {ω | ∃ ds : List Step, ds.length = n ∧
      ((trace p ds).map traversalEdge).Nodup ∧
        pathCost (fun e => τ e ω) p ds ≤ cheapSlope shape rate * (n : ℝ)} ≤
      (1 / 2 : ℝ)^n := by
  have hsp := cheapChernoff_pos hs hr
  have hbase : 0 ≤ (rate / (rate + cheapChernoff shape rate)) ^ shape :=
    (Real.rpow_pos_of_pos (div_pos hr (add_pos hr hsp)) shape).le
  have hden : ENNReal.ofReal (Real.exp
      (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ)))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hfin : ((4 ^ n : ℕ) : ℝ≥0∞) *
      ((ENNReal.ofReal ((rate / (rate + cheapChernoff shape rate)) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp
          (-cheapChernoff shape rate * (cheapSlope shape rate * (n : ℝ))))) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp)
      (ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden)
  have hb := ENNReal.toReal_mono hfin
    (h.cheap_fixed_length_probability hs hr (cheapChernoff shape rate) hsp p n
      (cheapSlope shape rate * (n : ℝ)))
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_div,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hbase,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Nat.cast_pow, Nat.cast_ofNat] at hb
  change P.real _ ≤ _ at hb
  rw [cheap_count_bound_eq hs hr n] at hb
  exact hb

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CheapLongTrails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Exponential decay is summable, including the nonempty bad event at n=0. -/
theorem GammaEnvironment.summable_cheapTrailEvent_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) : Summable (fun n => P.real (cheapTrailEvent shape rate τ p n)) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  exact hg.of_nonneg_of_le (fun _ => measureReal_nonneg)
    (fun n => h.cheap_fixed_length_decay_real hs hr p n)

/-- At each fixed start, almost surely all sufficiently long trails have
strictly positive linear cost. No independence across lengths is used. -/
theorem GammaEnvironment.ae_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  let := h.probability
  have hsum : (∑' n, P (cheapTrailEvent shape rate τ p n)) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      (h.summable_cheapTrailEvent_real hs hr p).tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨N, ?_⟩
  intro ds hlen htrail
  by_contra hc
  exact hN ds.length hlen ⟨ds, rfl, htrail, le_of_not_gt hc⟩

/-- Countably many lattice starts may share one event; the length cutoff can
depend on both the environment and the start. -/
theorem GammaEnvironment.ae_all_starts_long_trails_cost
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ ds : List Step, N ≤ ds.length →
      ((trace p ds).map traversalEdge).Nodup →
        cheapSlope shape rate * (ds.length : ℝ) < pathCost (fun e => τ e ω) p ds := by
  rw [ae_all_iff]
  intro p
  exact h.ae_long_trails_cost hs hr p

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LoopErasure
attribute [-instance] _root_.OAI.PlanarFPP.instCountableStep _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.LoopErase
open PlanarFPP

/-- Near-optimal paths with simple physical-edge traces, at every pair of
lattice endpoints and every positive approximation error. -/
theorem exists_near_optimal_simple_path (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (ε : ℝ) (hε : 0 < ε) :
    ∃ ds : List Step, p+displacement ds=q ∧
      ((trace p ds).map traversalEdge).Nodup ∧
      passageTime w p q ≤ pathCost w p ds ∧ pathCost w p ds < passageTime w p q+ε := by
  obtain ⟨ds,hend,hcost⟩ := exists_near_optimal_path w p q ε hε
  obtain ⟨es,he,hs,hc⟩ := erase_path_loops w hw p ds
  have he' : p+displacement es=q := by rw [he,hend]
  exact ⟨es,he',hs,passageTime_le_cost w hw p q es he',hc.trans_lt hcost⟩

end GammaFPP.LoopErase

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PassageLowerBound
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Filter

/-- Each original nearest-neighbor step contributes at most one L1 unit. -/
lemma displacement_natAbs_sum_le_length (ds : List Step) :
    (displacement ds).1.natAbs + (displacement ds).2.natAbs ≤ ds.length := by
  induction ds with
  | nil => simp [displacement]
  | cons d ds ih =>
      have h₁ := Int.natAbs_add_le d.delta.1 (displacement ds).1
      have h₂ := Int.natAbs_add_le d.delta.2 (displacement ds).2
      have hd : d.delta.1.natAbs + d.delta.2.natAbs = 1 := by
        cases d <;> norm_num [Step.delta]
      simp only [displacement_cons, List.length_cons]
      change (d.delta.1 + (displacement ds).1).natAbs +
        (d.delta.2 + (displacement ds).2).natAbs ≤ ds.length + 1
      omega

/-- Literal latticeDistance, not the product max norm. -/
lemma latticeDistance_endpoint_le_length (p : Vertex) (ds : List Step) :
    latticeDistance p (p + displacement ds) ≤ ds.length := by
  simpa only [latticeDistance, Prod.fst_add, Prod.snd_add, add_sub_cancel_left] using
    displacement_natAbs_sum_le_length ds

/-- Erasure preserves the endpoint, so every sufficiently distant arbitrary
path inherits the long-trail lower bound, even if it repeats edges. -/
lemma pathCost_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) (ds : List Step)
    (hend : p + displacement ds = q) :
    c * (latticeDistance p q : ℝ) < pathCost w p ds := by
  obtain ⟨es, he, hn, hcost⟩ := LoopErase.erase_path_loops w hw p ds
  have hend' : p + displacement es = q := by rw [he, hend]
  have hdist : latticeDistance p q ≤ es.length := by
    simpa only [hend'] using latticeDistance_endpoint_le_length p es
  have hdistR : (latticeDistance p q : ℝ) ≤ (es.length : ℝ) := by
    exact_mod_cast hdist
  exact (mul_le_mul_of_nonneg_left hdistR hc).trans_lt
    ((hN es (hq.trans hdist) hn).trans_le hcost)

/-- Taking the infimum of path costs preserves the non-strict lower bound,
without requiring the existence of a minimizing path. -/
lemma passageTime_lower_of_long_trails (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (p : Vertex) (N : ℕ)
    (hN : ∀ es : List Step, N ≤ es.length →
      ((trace p es).map traversalEdge).Nodup → c * (es.length : ℝ) < pathCost w p es)
    (q : Vertex) (hq : N ≤ latticeDistance p q) :
    c * (latticeDistance p q : ℝ) ≤ passageTime w p q := by
  apply le_csInf (path_costs_nonempty w p q)
  rintro t ⟨ds, hend, rfl⟩
  exact (pathCost_lower_of_long_trails w hw c hc p N hN q hq ds hend).le

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- On one probability-one event, every lattice start has an eventual metric
lower bound for all distant endpoints. The cutoff may depend on start/sample. -/
theorem GammaEnvironment.ae_all_starts_passageTime_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, ∀ p : Vertex, ∃ N : ℕ, ∀ q : Vertex,
      N ≤ latticeDistance p q →
        cheapSlope shape rate * (latticeDistance p q : ℝ) ≤
          passageTime (fun e => τ e ω) p q := by
  filter_upwards [h.ae_positive, h.ae_all_starts_long_trails_cost hs hr] with ω hpos hlong
  intro p
  obtain ⟨N, hN⟩ := hlong p
  refine ⟨N, ?_⟩
  intro q hq
  exact passageTime_lower_of_long_trails (fun e => τ e ω) (fun e => (hpos e).le)
    (cheapSlope shape rate) (cheapSlope_pos hs hr).le p N hN q hq

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanPositive
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Filter
open scoped Topology ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Fatou needs only eventual lower bounds, not samplewise convergence. -/
lemma lower_le_limit_integral_of_ae_eventually [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (a m : ℝ)
    (hX : ∀ n, Measurable (X n)) (hI : ∀ n, Integrable (X n) P)
    (hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω)
    (hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, a ≤ X n ω)
    (hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop (𝓝 m)) (hm : 0 ≤ m) :
    a ≤ m := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (X n ω)
  have hmeas : ∀ n, Measurable (F n) := fun n => (hX n).ennreal_ofReal
  have hpoint : ∀ᵐ ω ∂P, ENNReal.ofReal a ≤ liminf (fun n => F n ω) atTop := by
    filter_upwards [hlower] with ω hω
    exact le_liminf_of_le (h := hω.mono fun n hn => ENNReal.ofReal_le_ofReal hn)
  have hlow : ENNReal.ofReal a ≤ ∫⁻ ω, liminf (fun n => F n ω) atTop ∂P := by
    simpa only [lintegral_const, measure_univ, mul_one] using lintegral_mono_ae hpoint
  have hfatou := lintegral_liminf_le (μ := P) (u := atTop) hmeas
  have hint (n : ℕ) : (∫⁻ ω, F n ω ∂P) = ENNReal.ofReal (∫ ω, X n ω ∂P) :=
    (ofReal_integral_eq_lintegral_ofReal (hI n) (hpos n)).symm
  have ht : Tendsto (fun n => ∫⁻ ω, F n ω ∂P) atTop (𝓝 (ENNReal.ofReal m)) := by
    simpa only [hint] using ENNReal.tendsto_ofReal hlimit
  have hb : ENNReal.ofReal a ≤ ENNReal.ofReal m := by
    simpa only [ht.liminf_eq] using hlow.trans hfatou
  exact (ENNReal.ofReal_le_ofReal_iff hm).mp hb

/-- Literal lattice L1 distance scales under natural multiplication. -/
lemma latticeDistance_zero_nsmul (z : Vertex) (n : ℕ) :
    latticeDistance 0 (n • z) = n * latticeDistance 0 z := by
  simp [latticeDistance, nsmul_eq_mul, Int.natAbs_mul, Nat.mul_add]

variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The actual Fekete mean limit has the same positive linear lower bound as
the eventual path metric. The zero direction is treated before division. -/
theorem GammaEnvironment.directionalMeanConstant_linear_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) :
    cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ directionalMeanConstant h hs hr z := by
  by_cases hz : z = 0
  · subst z
    simp [latticeDistance, h.directionalMeanConstant_zero hs hr]
  let : IsProbabilityMeasure P := h.probability
  have hd : 0 < latticeDistance 0 z := by
    by_contra hn
    have hd0 : latticeDistance 0 z = 0 := Nat.eq_zero_of_not_pos hn
    have hxy : z.1 = 0 ∧ z.2 = 0 := by simpa [latticeDistance] using hd0
    exact hz (Prod.ext hxy.1 hxy.2)
  let X : ℕ → Ω → ℝ := fun n ω => passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
  have hX : ∀ n, Measurable (X n) := fun n =>
    (h.measurable_passageTime 0 (n • z)).div_const (n : ℝ)
  have hI : ∀ n, Integrable (X n) P := fun n =>
    (h.integrable_passageTime hs hr 0 (n • z)).div_const (n : ℝ)
  have hpos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ X n ω := by
    intro n
    filter_upwards [h.ae_positive] with ω hω
    exact div_nonneg (passageTime_nonneg _ (fun e => (hω e).le) 0 (n • z))
      (Nat.cast_nonneg n)
  have hlower : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤ X n ω := by
    filter_upwards [h.ae_all_starts_passageTime_lower hs hr] with ω hω
    obtain ⟨N, hN⟩ := hω 0
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    have hnN : N ≤ n := (le_max_left N 1).trans hn
    have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
    have hnd : N ≤ latticeDistance 0 (n • z) := by
      rw [latticeDistance_zero_nsmul]
      nlinarith
    have hb := hN (n • z) hnd
    rw [latticeDistance_zero_nsmul, Nat.cast_mul] at hb
    change cheapSlope shape rate * (latticeDistance 0 z : ℝ) ≤
      passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ)
    apply (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast (show 0 < n by omega))).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  have hlimit : Tendsto (fun n => ∫ ω, X n ω ∂P) atTop
      (𝓝 (directionalMeanConstant h hs hr z)) := by
    simpa only [X, integral_div, meanPassageSequence] using h.meanPassageSequence_tendsto hs hr z
  exact lower_le_limit_integral_of_ae_eventually X _ _ hX hI hpos hlower hlimit
    (h.directionalMeanConstant_nonneg hs hr z)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MeanNorm
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP Topology

/-- Positive denominators transport a lattice coercivity bound to rationals. -/
lemma rationalMean_lower (m : Vertex → ℝ) (c : ℝ)
    (hm : ∀ x, c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|) ≤ m x)
    (q : ℚ × ℚ) :
    c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ rationalMean m q := by
  let x := rationalNumerator q
  let n := rationalDenominator q
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (rationalDenominator_pos q)
  have he := rationalLatticePoint_numerator_denominator q
  have h₁ : (x.1 : ℝ) / (n : ℝ) = (q.1 : ℝ) := by
    have hq : (x.1 : ℚ) / (n : ℚ) = q.1 := by
      simpa only [rationalLatticePoint] using congrArg Prod.fst he
    exact_mod_cast hq
  have h₂ : (x.2 : ℝ) / (n : ℝ) = (q.2 : ℝ) := by
    have hq : (x.2 : ℚ) / (n : ℚ) = q.2 := by
      simpa only [rationalLatticePoint] using congrArg Prod.snd he
    exact_mod_cast hq
  change _ ≤ m x / (n : ℝ)
  rw [← h₁, ← h₂, abs_div, abs_div, abs_of_pos hn]
  simpa only [← add_div, ← mul_div_assoc] using
    div_le_div_of_nonneg_right (hm x) hn.le

/-- A closed inequality on the rational image holds on its real closure. -/
lemma realMeanExtension_lower {f : ℚ × ℚ → ℝ} (hf : UniformContinuous f)
    (c : ℝ) (hl : ∀ q, c * (|(q.1 : ℝ)| + |(q.2 : ℝ)|) ≤ f q)
    (v : ℝ × ℝ) : c * (|v.1| + |v.2|) ≤ realMeanExtension f v := by
  apply isClosed_property rationalPairCast_dense
    (p := fun v => c * (|v.1| + |v.2|) ≤ realMeanExtension f v) ?_ ?_ v
  · exact isClosed_le
      (continuous_const.mul (continuous_fst.abs.add continuous_snd.abs))
      (realMeanExtension_uniformContinuous hf).continuous
  · intro q
    rw [realMeanExtension_on_rat hf]
    exact hl q

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma gammaMeanPairSeminorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : ℝ × ℝ) :
    cheapSlope shape rate * (|v.1| + |v.2|) ≤ gammaMeanPairSeminorm h hs hr v := by
  change _ ≤ realMeanExtension (rationalMean (directionalMeanConstant h hs hr)) v
  have hlip := rationalMean_l1 (directionalMeanConstant h hs hr)
    (fun k z => h.directionalMeanConstant_nsmul hs hr z k)
    (shape/rate) (h.directionalMeanConstant_l1_lipschitz hs hr)
  apply realMeanExtension_lower
    (rational_l1_lipschitz _ ⟨shape/rate, (div_pos hs hr).le⟩ hlip).uniformContinuous
  intro q
  apply rationalMean_lower
  intro z
  simpa [latticeDistance] using h.directionalMeanConstant_linear_lower hs hr z

lemma gammaMeanNorm_lower
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (v : Plane) : cheapSlope shape rate * (|v 0| + |v 1|) ≤ gammaMeanNorm h hs hr v :=
  gammaMeanPairSeminorm_lower h hs hr (v 0, v 1)

/-- The real extension of the Gamma directional mean constants is a norm. -/
theorem gammaMeanNorm_laws
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    TimeConstantNorm (gammaMeanNorm h hs hr) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    exact apply_nonneg (gammaMeanPairSeminorm h hs hr) (v 0, v 1)
  · intro v
    constructor
    · intro hv
      have hb := gammaMeanNorm_lower h hs hr v
      have hc := cheapSlope_pos hs hr
      rw [hv] at hb
      have h₀ : v 0 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      have h₁ : v 1 = 0 := abs_eq_zero.mp (by nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)])
      ext i
      fin_cases i
      · exact h₀
      · exact h₁
    · rintro rfl
      change gammaMeanPairSeminorm h hs hr 0 = 0
      exact map_zero _
  · intro v w
    change gammaMeanPairSeminorm h hs hr ((v 0, v 1) + (w 0, w 1)) ≤ _
    exact map_add_le_add (gammaMeanPairSeminorm h hs hr) _ _
  · intro a v
    change gammaMeanPairSeminorm h hs hr (a • (v 0, v 1)) = _
    simpa only [Real.norm_eq_abs, gammaMeanNorm] using map_smul_eq_mul (gammaMeanPairSeminorm h hs hr) a (v 0, v 1)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RealDirectionGeometry
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
open scoped Topology

theorem plane_coordinate_le_norm (v : Plane) (i : Fin 2) : |v i| ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

theorem plane_norm_le_coordinates (v : Plane) : ‖v‖ ≤ |v 0| + |v 1| := by
  let x : Plane := PiLp.single 2 0 (v 0)
  let y : Plane := PiLp.single 2 1 (v 1)
  have hv : v = x+y := by
    ext i
    fin_cases i <;> simp [x,y]
  have hx : ‖x‖ = |v 0| := by simp [x]
  have hy : ‖y‖ = |v 1| := by simp [y]
  calc
    ‖v‖ = ‖x+y‖ := congrArg norm hv
    _ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    _ = _ := by rw [hx,hy]

theorem latticeDistance_le_norm (p q : Vertex) :
    (latticeDistance p q : ℝ) ≤ 2 * ‖latticeEmbed q - latticeEmbed p‖ := by
  have h0 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 0
  have h1 := plane_coordinate_le_norm (latticeEmbed q - latticeEmbed p) 1
  have hc (a : ℤ) : (a.natAbs : ℝ) = |(a : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  simp only [latticeDistance, Nat.cast_add, hc, Int.cast_sub]
  simpa only [latticeEmbed, PiLp.sub_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, two_mul] using add_le_add h0 h1

theorem latticeFloor_error (v : Plane) : ‖latticeEmbed (latticeFloor v) - v‖ ≤ 2 := by
  have hi (i : Fin 2) : |(latticeEmbed (latticeFloor v) - v) i| ≤ 1 := by
    have hle := Int.floor_le (v i)
    have hlt := Int.lt_floor_add_one (v i)
    have he : (latticeEmbed (latticeFloor v) - v) i = (⌊v i⌋ : ℝ) - v i := by
      fin_cases i <;> rfl
    rw [he, abs_of_nonpos (by linarith)]
    linarith
  exact (plane_norm_le_coordinates _).trans (by linarith [hi 0, hi 1])

theorem timeConstantNorm_lipschitz_bound (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    ∃ B : ℝ, 0 < B ∧ ∀ v w, |μ v - μ w| ≤ B * ‖v-w‖ := by
  let e0 : Plane := PiLp.single 2 0 1
  let e1 : Plane := PiLp.single 2 1 1
  let B := μ e0 + μ e1 + 1
  have hB : 0 < B := by dsimp [B]; linarith [hμ.nonneg e0, hμ.nonneg e1]
  have hu (v : Plane) : μ v ≤ B * ‖v‖ := by
    have he : v = v 0 • e0 + v 1 • e1 := by
      ext i; fin_cases i <;> simp [e0, e1]
    have ht := hμ.triangle (v 0 • e0) (v 1 • e1)
    rw [← he, hμ.homogeneous, hμ.homogeneous] at ht
    have h0 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 0) (hμ.nonneg e0)
    have h1 := mul_le_mul_of_nonneg_right (plane_coordinate_le_norm v 1) (hμ.nonneg e1)
    dsimp [B]
    nlinarith [norm_nonneg v]
  refine ⟨B, hB, ?_⟩
  intro v w
  apply abs_le.mpr
  have h1 := hμ.triangle (v-w) w
  have h2 := hμ.triangle (w-v) v
  simp only [sub_add_cancel] at h1 h2
  have hu1 := hu (v-w)
  have hu2 := hu (w-v)
  rw [norm_sub_rev] at hu2
  constructor <;> linarith

theorem passageTime_origin_difference_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) : |passageTime w 0 p-passageTime w 0 q| ≤ passageTime w p q := by
  have h1 := passageTime_triangle w hw 0 q p
  have h2 := passageTime_triangle w hw 0 p q
  rw [passageTime_symm w hw q p] at h1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma lattice_mem_box_of_norm (p : Vertex) (n : ℕ) (hp : ‖latticeEmbed p‖ ≤ n) :
    p ∈ latticeBox n := by
  have hi (i : Fin 2) := (plane_coordinate_le_norm (latticeEmbed p) i).trans hp
  have h₁ : |p.1| ≤ (n : ℤ) := by exact_mod_cast (show |(p.1 : ℝ)| ≤ n from hi 0)
  have h₂ : |p.2| ≤ (n : ℤ) := by exact_mod_cast (show |(p.2 : ℝ)| ≤ n from hi 1)
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (abs_le.mp h₁),Finset.mem_Icc.mpr (abs_le.mp h₂)⟩

lemma floor_real_ratio_tendsto (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => (⌊t/M⌋₊ : ℝ)/t) atTop (𝓝 (1/M)) := by
  simpa [div_eq_mul_inv,mul_comm] using
    (tendsto_nat_floor_mul_div_atTop (inv_nonneg.mpr hM.le))

lemma scaledLatticePoint_norm (t : ℝ) (ht : 0 < t) (p : Vertex) :
    ‖scaledLatticePoint t p‖ = ‖latticeEmbed p‖/t := by
  rw [scaledLatticePoint,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht)]
  ring

lemma scaledLatticePoint_sub_norm (t : ℝ) (ht : 0 < t) (p q : Vertex) :
    ‖scaledLatticePoint t p-scaledLatticePoint t q‖ = ‖latticeEmbed p-latticeEmbed q‖/t := by
  rw [scaledLatticePoint,scaledLatticePoint,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr ht)]
  ring

lemma scaled_floor_error (t : ℝ) (ht : 0 < t) (v : Plane) :
    ‖scaledLatticePoint t (latticeFloor (t • v))-v‖ ≤ 2/t := by
  have he : scaledLatticePoint t (latticeFloor (t • v))-v =
      (1/t) • (latticeEmbed (latticeFloor (t • v))-t • v) := by
    rw [smul_sub,smul_smul,one_div_mul_cancel ht.ne',one_smul]
    rfl
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ht)]
  simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using
    mul_le_mul_of_nonneg_left (latticeFloor_error (t • v)) (le_of_lt (one_div_pos.mpr ht))

lemma scaled_floor_tendsto (v : Plane) :
    Tendsto (fun t : ℝ => scaledLatticePoint t (latticeFloor (t • v))) atTop (𝓝 v) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (max 0 (2/ε))] with t ht
  have ht0 : 0 < t := (le_max_left _ _).trans_lt ht
  rw [dist_eq_norm]
  exact (scaled_floor_error t ht0 v).trans_lt ((div_lt_iff₀ ht0).mpr
    (by have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt ht); nlinarith))

lemma latticeEmbed_nsmul (n : ℕ) (z : Vertex) :
    latticeEmbed (n • z) = (n : ℝ) • latticeEmbed z := by
  ext i
  fin_cases i <;> simp [latticeEmbed,nsmul_eq_mul]

lemma scaled_lattice_ray_tendsto (z : Vertex) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => scaledLatticePoint t (⌊t/M⌋₊ • z)) atTop
      (𝓝 ((1/M) • latticeEmbed z)) := by
  have h := (floor_real_ratio_tendsto M hM).smul_const (latticeEmbed z)
  simpa only [scaledLatticePoint,latticeEmbed_nsmul,smul_smul,one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h

lemma passageTime_real_lattice_ray_tendsto (w : Edge → ℝ) (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ)
    (hray : ∀ z : Vertex, Tendsto (fun n : ℕ => passageTime w 0 (n • z)/n)
      atTop (𝓝 (μ (latticeEmbed z)))) (z : Vertex) (M : ℝ) (hM : 0 < M) :
    Tendsto (fun t : ℝ => passageTime w 0 (⌊t/M⌋₊ • z)/t) atTop
      (𝓝 (μ ((1/M) • latticeEmbed z))) := by
  have hn : Tendsto (fun t : ℝ => ⌊t/M⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hM)
  have hh := ((hray z).comp hn).mul (floor_real_ratio_tendsto M hM)
  have he : (fun t : ℝ => passageTime w 0 (⌊t/M⌋₊ • z)/t) =ᶠ[atTop]
      (fun t : ℝ => (passageTime w 0 (⌊t/M⌋₊ • z)/(⌊t/M⌋₊ : ℝ))*((⌊t/M⌋₊ : ℝ)/t)) := by
    filter_upwards [hn.eventually (eventually_ge_atTop 1)] with t ht
    have hn0 : (⌊t/M⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (show ⌊t/M⌋₊ ≠ 0 by omega)
    field_simp
  rw [hμ.homogeneous,abs_of_pos (one_div_pos.mpr hM),mul_comm]
  exact hh.congr' he.symm

end GammaFPP.RealDirectionBridge

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_CoordinateTails
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma coordinateAllowance_pos (hs : 0 < shape) (hr : 0 < rate) :
    0 < coordinateAllowance shape rate := by
  unfold coordinateAllowance
  positivity

/-- Exponential upper tail for the cost of a straight lattice path. -/
theorem GammaEnvironment.costly_straight_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ n /
        ENNReal.ofReal (Real.exp ((rate / 2) * t)) := by
  have hp : 0 < rate / 2 := by positivity
  have hl : rate / 2 < rate := by linarith
  have he : rate / (rate - rate / 2) = 2 := by
    have hd : rate - rate / 2 ≠ 0 := (sub_pos.mpr hl).ne'
    field_simp [hd]; ring
  have hb := h.upper_tail_edgeSum hs hr hp hl
    ((range n).image (straightEdge p d)) t
  simpa only [edgeSum, pathCost_replicate_edgeSet, he,
    card_image_of_injective _ (straightEdge_injective p d), card_range] using hb

/-- The real-valued upper tail for the cost of a straight lattice path. -/
theorem GammaEnvironment.costly_straight_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | t ≤ pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      ((2 : ℝ) ^ shape) ^ n * Real.exp (-(rate / 2) * t) := by
  have hbase : 0 ≤ (2 : ℝ) ^ shape := (Real.rpow_pos_of_pos (by norm_num) shape).le
  have hden : ENNReal.ofReal (Real.exp ((rate / 2) * t)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hn : (ENNReal.ofReal ((2 : ℝ) ^ shape)) ^ n /
      ENNReal.ofReal (Real.exp ((rate / 2) * t)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hden
  have hb := ENNReal.toReal_mono hn (h.costly_straight_probability hs hr p d n t)
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hbase, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hb
  change P.real _ ≤ _ at hb
  rw [show -(rate / 2) * t = -((rate / 2) * t) by ring, Real.exp_neg]
  simpa only [div_eq_mul_inv] using hb

lemma gamma_half_rate_mgf_bound (hs : 0 < shape) :
    (2 : ℝ) ^ shape ≤ Real.exp (shape + 1) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hl : Real.log (2 : ℝ) ≤ 1 := by
    have hb := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hb ⊢
    exact hb
  nlinarith

/-- Exponential tail above the linear allowance, for every real excess `t`. -/
theorem GammaEnvironment.costly_straight_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (d : Step) (n : ℕ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (n : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (List.replicate n d)} ≤
      Real.exp (-(rate / 2) * t) := by
  refine (h.costly_straight_probability_real hs hr p d n
    (coordinateAllowance shape rate * n + t)).trans ?_
  have hp : ((2 : ℝ) ^ shape) ^ n ≤ Real.exp ((n : ℝ) * (shape + 1)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.rpow_pos_of_pos (by norm_num) shape).le
      (gamma_half_rate_mgf_bound hs) n
  calc
    ((2 : ℝ) ^ shape) ^ n *
        Real.exp (-(rate / 2) * (coordinateAllowance shape rate * n + t)) ≤
        Real.exp ((n : ℝ) * (shape + 1)) *
          Real.exp (-(rate / 2) * (coordinateAllowance shape rate * n + t)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-(rate / 2) * t) := by
      rw [← Real.exp_add]
      congr 1
      unfold coordinateAllowance
      field_simp [hr.ne']; ring

theorem GammaEnvironment.costly_horizontal_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (horizontal a)} ≤ Real.exp (-(rate / 2) * t) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_left ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.east a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [horizontal, ite_eq_right ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.west (-a).toNat t

theorem GammaEnvironment.costly_vertical_excess_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (a : ℤ) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (a.natAbs : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (vertical a)} ≤ Real.exp (-(rate / 2) * t) := by
  by_cases ha : 0 ≤ a
  · have he : a.toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_left ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.north a.toNat t
  · have he : (-a).toNat = a.natAbs := by omega
    simpa only [vertical, ite_eq_right ha, he] using
      h.costly_straight_excess_probability_real hs hr p Step.south (-a).toNat t

/-- A union bound for the two coordinate legs, counting every edge traversal. -/
theorem GammaEnvironment.costly_coordinatePath_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (t : ℝ) :
    P.real {ω | coordinateAllowance shape rate * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ≤
      2 * Real.exp (-(rate / 4) * t) := by
  let := h.probability
  let A := {ω | coordinateAllowance shape rate * ((q.1-p.1).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) p (horizontal (q.1-p.1))}
  let B := {ω | coordinateAllowance shape rate * ((q.2-p.2).natAbs : ℝ) + t/2 ≤
    pathCost (fun e => τ e ω) (p + displacement (horizontal (q.1-p.1)))
      (vertical (q.2-p.2))}
  have hsub : {ω | coordinateAllowance shape rate * (latticeDistance p q : ℝ) + t ≤
      pathCost (fun e => τ e ω) p (coordinatePath p q)} ⊆ A ∪ B := by
    intro ω hω
    change _ ∨ _
    by_contra hn
    push Not at hn
    simp only [Set.mem_ofPred_eq, coordinatePath, pathCost_append, latticeDistance,
      Nat.cast_add] at hω
    simp only [A, B, Set.mem_ofPred_eq, not_le] at hn
    linarith
  refine (measureReal_mono hsub).trans ((measureReal_union_le A B).trans ?_)
  have ha := h.costly_horizontal_excess_probability_real hs hr p (q.1-p.1) (t/2)
  have hb := h.costly_vertical_excess_probability_real hs hr
    (p + displacement (horizontal (q.1-p.1))) (q.2-p.2) (t/2)
  change P.real A + P.real B ≤ _
  change P.real A ≤ _ at ha
  change P.real B ≤ _ at hb
  have he : -(rate / 2) * (t / 2) = -(rate / 4) * t := by ring
  rw [he] at ha hb
  linarith

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_EnvironmentScaling
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}
variable {shape rate a : ℝ}

theorem GammaEnvironment.ae_positive_edges
    (h : GammaEnvironment shape rate P τ) :
    ∀ᵐ ω ∂P, ∀ e, 0 < τ e ω := by
  rw [ae_all_iff]
  intro e
  have hp : ∀ᵐ x ∂Measure.map (τ e) P, 0 < x := by
    rw [h.marginal e]
    exact gamma_ae_pos shape rate
  exact (ae_map_iff (h.measurable e).aemeasurable measurableSet_Ioi).mp hp

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SpatialModulus
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory PlanarFPP Finset Filter Set
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Finite union bound over all ordered pairs, without independence of path events. -/
theorem GammaEnvironment.gammaBadConnections_probability
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (ε : ℝ) (n : ℕ) :
    P.real (gammaBadConnections shape rate τ ε n) ≤
      (2 * (n : ℝ) + 1) ^ 4 * (2 * Real.exp (-(rate / 4) * (ε * n))) := by
  let := h.probability
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _pq ∈ (latticeBox n) ×ˢ (latticeBox n),
        2 * Real.exp (-(rate / 4) * (ε * n)) :=
      sum_le_sum (fun pq _ => h.costly_coordinatePath_probability_real hs hr pq.1 pq.2 (ε * n))
    _ = _ := by simp [latticeBox_card]; ring

/-- The only summability requirement is positive rate times positive epsilon. -/
theorem summable_gamma_box_connection_bound {rate ε : ℝ}
    (hr : 0 < rate) (hε : 0 < ε) :
    Summable (fun n : ℕ =>
      (2 * (n : ℝ) + 1) ^ 4 * (2 * Real.exp (-(rate / 4) * (ε * n)))) := by
  apply (PlanarFPP.summable_box_connection_bound (mul_pos hr hε)).congr
  intro n
  have he : -(rate * ε) * (n : ℝ) / 4 = -(rate / 4) * (ε * n) := by ring
  rw [he]

/-- For each fixed positive epsilon, almost surely all sufficiently large boxes
have the connection estimate for every pair, even pairs selected from the environment. -/
theorem GammaEnvironment.ae_eventually_coordinate_connections
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      pathCost (fun e => τ e ω) p (coordinatePath p q) <
        coordinateAllowance shape rate * (latticeDistance p q : ℝ) + ε * n := by
  let := h.probability
  have hsumm : Summable (fun n => P.real (gammaBadConnections shape rate τ ε n)) :=
    (summable_gamma_box_connection_bound hr hε).of_nonneg_of_le
      (fun _ => measureReal_nonneg) (h.gammaBadConnections_probability hs hr ε)
  have hfinite : (∑' n, P (gammaBadConnections shape rate τ ε n)) ≠ ⊤ := by
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
      hsumm.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with n hn
  intro p hp q hq
  by_contra hc
  apply hn
  exact mem_iUnion₂.mpr ⟨(p, q), mem_product.mpr ⟨hp, hq⟩, le_of_not_gt hc⟩

/-- The same modulus for the actual infimum passage time. Fixed epsilon precedes
AE; simultaneous control concerns finite-box pairs, not an uncountable family of epsilons. -/
theorem GammaEnvironment.ae_eventually_passageTime_connections
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q <
        coordinateAllowance shape rate * (latticeDistance p q : ℝ) + ε * n := by
  filter_upwards [h.ae_positive_edges, h.ae_eventually_coordinate_connections hs hr hε]
    with ω hp hc
  filter_upwards [hc] with n hn
  intro p hp' q hq'
  exact (passageTime_le_cost _ (fun e => (hp e).le) p q
    (coordinatePath p q) (coordinatePath_endpoint p q)).trans_lt (hn p hp' q hq')

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_RealDirectionBridge
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
open scoped Topology

theorem real_scale_connections (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (A : ℝ) (_hA : 0 < A)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < A*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ p q : Vertex,
      ‖latticeEmbed p‖ ≤ C*t → ‖latticeEmbed q‖ ≤ C*t →
      |passageTime w 0 p/t-passageTime w 0 q/t| ≤
        A*(latticeDistance p q : ℝ)/t+ε := by
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (div_pos hε (show 0 < C+1 by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hc k)
  filter_upwards [eventually_ge_atTop (max 1 ((N : ℝ)/C))] with t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith
  let n : ℕ := ⌈C*t⌉₊
  have htn : C*t ≤ (n : ℝ) := Nat.le_ceil _
  have hnu : (n : ℝ) ≤ (C+1)*t := by
    have he := Nat.ceil_lt_add_one (show 0 ≤ C*t by positivity)
    dsimp [n]
    nlinarith
  have hnN : N ≤ n := by
    have hh := (div_le_iff₀ hC).mp ((le_max_right _ _).trans ht)
    have hh' : (N : ℝ) ≤ (n : ℝ) := by nlinarith
    exact_mod_cast hh'
  intro p q hp hq
  have hp' := lattice_mem_box_of_norm p n (hp.trans htn)
  have hq' := lattice_mem_box_of_norm q n (hq.trans htn)
  have hdiff := passageTime_origin_difference_le w hw p q
  have hconn := hN n hnN p hp' q hq'
  have he : (1/(k+1 : ℝ))*(n : ℝ) ≤ ε*t := by
    have ha := mul_le_mul_of_nonneg_left hnu (show 0 ≤ 1/(k+1 : ℝ) by positivity)
    have hb := (lt_div_iff₀ (show 0 < C+1 by linarith)).mp hk
    nlinarith
  rw [← sub_div,abs_div,abs_of_pos ht0]
  apply (div_le_iff₀ ht0).mpr
  rw [add_mul,div_mul_cancel₀ _ ht0.ne']
  linarith

theorem real_scale_connections_normalized (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (A : ℝ) (hA : 0 < A)
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < A*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n)
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ p q : Vertex,
      ‖scaledLatticePoint t p‖ ≤ C → ‖scaledLatticePoint t q‖ ≤ C →
      |passageTime w 0 p/t-passageTime w 0 q/t| ≤
        (2*A)*‖scaledLatticePoint t p-scaledLatticePoint t q‖+ε := by
  filter_upwards [real_scale_connections w hw A hA hc C hC ε hε,
    eventually_gt_atTop (0 : ℝ)] with t ht ht0
  intro p q hp hq
  rw [scaledLatticePoint_norm t ht0] at hp hq
  have he := ht p q ((div_le_iff₀ ht0).mp hp) ((div_le_iff₀ ht0).mp hq)
  have hd := latticeDistance_le_norm p q
  rw [norm_sub_rev] at hd
  rw [scaledLatticePoint_sub_norm t ht0]
  apply he.trans
  have hh := (div_le_div_of_nonneg_right hd ht0.le)
  simp only [mul_div_assoc] at hh ⊢
  nlinarith [mul_le_mul_of_nonneg_left hh hA.le]

theorem real_direction_limits_of_lattice_limits (w : Edge → ℝ)
    (hw : ∀ e, 0 ≤ w e) (A : ℝ) (hA : 0 < A) (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hray : ∀ z : Vertex, Tendsto (fun n : ℕ => passageTime w 0 (n • z)/n)
      atTop (𝓝 (μ (latticeEmbed z))))
    (hc : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime w p q < A*(latticeDistance p q : ℝ)+(1/(k+1 : ℝ))*n) :
    ∀ v : Plane, Tendsto (fun t : ℝ => passageTime w 0 (latticeFloor (t • v))/t)
      atTop (𝓝 (μ v)) := by
  obtain ⟨B,hB,hLip⟩ := timeConstantNorm_lipschitz_bound μ hμ
  intro v
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min (1/2 : ℝ) (ε/(8*(B+4*A)))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by linarith))
  have hδ1 : δ ≤ 1/2 := min_le_left _ _
  have hδe : (B+4*A)*δ ≤ ε/8 := by
    have hh := (le_div_iff₀ (show 0 < 8*(B+4*A) by linarith)).mp (min_le_right (1/2 : ℝ) (ε/(8*(B+4*A))))
    dsimp [δ]
    nlinarith
  obtain ⟨M,hM⟩ := exists_nat_gt (max 1 (2/δ))
  have hM0 : (0 : ℝ) < M := (lt_of_lt_of_le (by norm_num) (le_max_left _ _)).trans hM
  let z := latticeFloor ((M : ℝ) • v)
  let u := (1/(M : ℝ)) • latticeEmbed z
  have huv : ‖u-v‖ < δ := by
    apply (scaled_floor_error M hM0 v).trans_lt
    apply (div_lt_iff₀ hM0).mpr
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hM)
    nlinarith
  have hμuv := hLip u v
  let C := ‖v‖+2
  have hC : 0 < C := by dsimp [C]; positivity
  have huC : ‖u‖ < C := by
    have hh := norm_add_le (u-v) v
    rw [sub_add_cancel] at hh
    dsimp [C]
    linarith
  have hp := scaled_floor_tendsto v
  have hq := scaled_lattice_ray_tendsto z M hM0
  have hpC : ∀ᶠ t : ℝ in atTop, ‖scaledLatticePoint t (latticeFloor (t • v))‖ ≤ C :=
    (hp.norm.eventually (gt_mem_nhds (show ‖v‖ < C by dsimp [C]; linarith))).mono (fun _ h => h.le)
  have hqC : ∀ᶠ t : ℝ in atTop, ‖scaledLatticePoint t (⌊t/(M : ℝ)⌋₊ • z)‖ ≤ C :=
    (hq.norm.eventually (gt_mem_nhds huC)).mono (fun _ h => h.le)
  have hpq : ∀ᶠ t : ℝ in atTop,
      ‖scaledLatticePoint t (latticeFloor (t • v))-
        scaledLatticePoint t (⌊t/(M : ℝ)⌋₊ • z)‖ < 2*δ := by
    have hh : ‖v-u‖ < 2*δ := by rw [norm_sub_rev]; linarith
    exact (hp.sub hq).norm.eventually (gt_mem_nhds hh)
  have hcost : ∀ᶠ t : ℝ in atTop,
      |passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t-μ u| < ε/4 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp
      (passageTime_real_lattice_ray_tendsto w μ hμ hray z M hM0) (ε/4) (by linarith)
  filter_upwards [hpC,hqC,hpq,hcost,
    real_scale_connections_normalized w hw A hA hc C hC (ε/4) (by linarith)] with t hpC hqC hpq hcost ht
  have he := ht _ _ hpC hqC
  have htri : |passageTime w 0 (latticeFloor (t • v))/t-μ v| ≤
      |passageTime w 0 (latticeFloor (t • v))/t-passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t|+
      |passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t-μ u|+|μ u-μ v| := by
    calc
      _ = |(passageTime w 0 (latticeFloor (t • v))/t-passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t)+
        (passageTime w 0 (⌊t/(M : ℝ)⌋₊ • z)/t-μ u)+(μ u-μ v)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  rw [Real.dist_eq]
  have hmul := mul_lt_mul_of_pos_left huv hB
  nlinarith

end GammaFPP.RealDirectionBridge

namespace GammaFPP
open RealDirectionBridge
open PlanarFPP MeasureTheory Filter Set
open scoped Topology

/-- Almost-sure lattice-ray limits and the Gamma spatial modulus extend the
constructed mean norm to a time constant in every fixed real direction. -/
theorem GammaEnvironment.isTimeConstant_of_ae_lattice_limits
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}
    {shape rate : ℝ} (h : GammaEnvironment shape rate P τ)
    (hs : 0 < shape) (hr : 0 < rate)
    (hray : ∀ z : Vertex, ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => passageTime (fun e => τ e ω) 0 (n • z) / n)
        atTop (𝓝 (directionalMeanConstant h hs hr z))) :
    IsTimeConstant P τ (gammaMeanNorm h hs hr) := by
  have hall := ae_all_iff.mpr hray
  have hc : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ p ∈ latticeBox n, ∀ q ∈ latticeBox n,
      passageTime (fun e => τ e ω) p q <
        coordinateAllowance shape rate * (latticeDistance p q : ℝ) +
          (1 / (k + 1 : ℝ)) * n := by
    apply ae_all_iff.mpr
    intro k
    exact h.ae_eventually_passageTime_connections hs hr (by positivity)
  intro v
  filter_upwards [h.ae_positive_edges, hall, hc] with ω hp hω hcω
  apply RealDirectionBridge.real_direction_limits_of_lattice_limits
    (fun e => τ e ω) (fun e => (hp e).le)
    (coordinateAllowance shape rate) (coordinateAllowance_pos hs hr)
    (gammaMeanNorm h hs hr) (gammaMeanNorm_laws h hs hr) ?_ hcω v
  intro z
  have he : gammaMeanNorm h hs hr (latticeEmbed z) =
      directionalMeanConstant h hs hr z := by
    change gammaMeanPairSeminorm h hs hr ((z.1 : ℝ), (z.2 : ℝ)) = _
    exact gammaMeanPairSeminorm_integerPair h hs hr z
  rw [he]
  exact hω z

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ConcentrationScale
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal

lemma concentrationKappa_bounds {shape rate : ℝ} (hr : 0 < rate) :
    0 < concentrationKappa shape rate ∧
      concentrationKappa shape rate ≤ rate/4 ∧
      concentrationKappa shape rate ≤ 1/4 ∧
      (16*(2 : ℝ)^shape/rate^2)*(concentrationKappa shape rate)^2 ≤ 1/16 := by
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  let k := concentrationKappa shape rate
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hk : 0 < k := by dsimp [k, concentrationKappa]; positivity
  have hkr : k ≤ rate/4 := min_le_left _ _
  have hkd : k ≤ 1/(4*(B+1)) := min_le_right _ _
  have hd : 0 < 4*(B+1) := by linarith
  have hm : k*(4*(B+1)) ≤ 1 := (le_div_iff₀ hd).mp hkd
  have hBk : 0 ≤ B*k := mul_nonneg hB hk.le
  have hkquarter : k ≤ 1/4 := by nlinarith
  have hBkquarter : B*k ≤ 1/4 := by nlinarith
  have hprod := mul_le_mul hBkquarter hkquarter hk.le (by norm_num : (0 : ℝ) ≤ 1/4)
  refine ⟨hk, hkr, hkquarter, ?_⟩
  change B*k^2 ≤ 1/16
  nlinarith

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_DyadicDerivativeBound
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open Filter Topology

theorem dyadic_derivative_bound (G : ℝ → ℝ) (a m K : ℝ) (hK : 0 ≤ K)
    (hzero : G 0 = 0) (hd : HasDerivAt G m 0)
    (hrec : ∀ n : ℕ, G (a*(1/2 : ℝ)^n) ≤
      2*G (a*(1/2 : ℝ)^(n+1)) + K*((1/2 : ℝ)^n)^2) :
    G a ≤ a*m+2*K := by
  have hi : ∀ n : ℕ, G a ≤ G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n +
      2*K*(1-(1/2 : ℝ)^n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hn : 0 < (1/2 : ℝ)^n := pow_pos (by norm_num) n
      have hdiv := div_le_div_of_nonneg_right (hrec n) hn.le
      calc
        _ ≤ G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n + 2*K*(1-(1/2 : ℝ)^n) := ih
        _ ≤ (2*G (a*(1/2 : ℝ)^(n+1))+K*((1/2 : ℝ)^n)^2)/(1/2 : ℝ)^n +
            2*K*(1-(1/2 : ℝ)^n) := add_le_add hdiv le_rfl
        _ = _ := by
          rw [pow_succ]
          field_simp
          ring
  by_cases ha : a = 0
  · subst a
    simp only [hzero, zero_mul, zero_add]
    positivity
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hb : Tendsto (fun n : ℕ => a*(1/2 : ℝ)^n) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using hp.const_mul a
    · exact .of_forall (fun n => by simp [ha])
  have hsl := (hd.tendsto_slope.comp hb).const_mul a
  have hmain : Tendsto (fun n : ℕ => G (a*(1/2 : ℝ)^n)/(1/2 : ℝ)^n)
      atTop (𝓝 (a*m)) := by
    convert hsl using 1
    funext n
    simp only [Function.comp_def, slope, sub_zero, hzero, smul_eq_mul, vsub_eq_sub, sub_zero]
    field_simp [ha]
  have hc : Tendsto (fun n : ℕ => 2*K*(1-(1/2 : ℝ)^n)) atTop (𝓝 (2*K)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hp).const_mul (2*K)
  exact ge_of_tendsto (hmain.add hc) (.of_forall hi)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalTrailPassage
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP

lemma costs_finite (w : Edge → ℝ) (p q : Vertex) (R : ℕ) :
    (costs w p q R).Finite := by
  classical
  apply ((candidates p q R).image (fun ds => pathCost w p ds)).finite_toSet.subset
  rintro c ⟨ds, hds, rfl⟩
  exact Finset.mem_image.mpr ⟨ds, hds, rfl⟩

lemma costs_nonempty (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) : (costs w p q R).Nonempty := by
  obtain ⟨ds, hds⟩ := candidates_nonempty p q R hR
  exact ⟨pathCost w p ds, ds, hds, rfl⟩

/-- A nonempty finite candidate family attains its minimum for every real
edge-weight assignment. -/
theorem minimizing_candidate (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    ∃ ds ∈ candidates p q R, pathCost w p ds = passageTime w p q R := by
  let C := costs w p q R
  have hC : C.Finite := costs_finite w p q R
  have hne : C.Nonempty := costs_nonempty w p q R hR
  obtain ⟨c, hc, hm⟩ := Set.exists_min_image C id hC hne
  obtain ⟨ds, hds, rfl⟩ := hc
  refine ⟨ds, hds, le_antisymm ?_ ?_⟩
  · exact le_csInf hne (fun c hc => hm c hc)
  · exact csInf_le hC.bddBelow ⟨ds, hds, rfl⟩

lemma passageTime_le_candidate (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (ds : List Step) (hds : ds ∈ candidates p q R) :
    passageTime w p q R ≤ pathCost w p ds :=
  csInf_le (costs_finite w p q R).bddBelow ⟨ds, hds, rfl⟩

/-- A minimizing candidate is a trail connecting the endpoints in fewer than
`R` steps. -/
theorem exists_minimizing_trail (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    ∃ ds : List Step, p + displacement ds = q ∧
      ((trace p ds).map traversalEdge).Nodup ∧ ds.length < R ∧
      pathCost w p ds = passageTime w p q R := by
  obtain ⟨ds, hds, hc⟩ := minimizing_candidate w p q R hR
  obtain ⟨hend, hn, hl⟩ := (mem_candidates p q R ds).mp hds
  exact ⟨ds, hend, hn, hl, hc⟩

/-- Unrestricted passage time is at most the finite local minimum. -/
theorem unrestricted_passageTime_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    PlanarFPP.passageTime w p q ≤ passageTime w p q R := by
  obtain ⟨ds, hend, _, _, hc⟩ := exists_minimizing_trail w p q R hR
  rw [← hc]
  exact PlanarFPP.passageTime_le_cost w hw p q ds hend

lemma passageTime_nonneg (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    0 ≤ passageTime w p q R :=
  (PlanarFPP.passageTime_nonneg w hw p q).trans
    (unrestricted_passageTime_le w hw p q R hR)

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalResamplingModel
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP Finset

lemma candidate_edges_subset (p q : Vertex) (R : ℕ) (ds : List Step)
    (hds : ds ∈ candidates p q R) :
    ((trace p ds).map traversalEdge).toFinset ⊆ localEdges p q R := by
  classical
  intro e he
  exact Finset.mem_biUnion.mpr ⟨ds, hds, he⟩

lemma extend_nonneg (p q : Vertex) (R : ℕ) (v : Coordinates p q R)
    (hv : ∀ e, 0 ≤ v e) : ∀ e, 0 ≤ extend p q R v e := by
  intro e
  unfold extend
  split_ifs with he
  · exact hv ⟨e, he⟩
  · exact le_rfl

lemma extend_update (p q : Vertex) (R : ℕ) (v : Coordinates p q R)
    (e : ↥(localEdges p q R)) (u : ℝ) :
    extend p q R (Function.update v e u) = Function.update (extend p q R v) e.val u := by
  classical
  funext f
  by_cases hf : f = e.val
  · subst f
    simp [extend, e.property]
  · by_cases hm : f ∈ localEdges p q R
    · have hne : (⟨f, hm⟩ : ↥(localEdges p q R)) ≠ e := by
        intro h
        exact hf (congrArg Subtype.val h)
      simp [extend, hm, Function.update_of_ne hf, Function.update_of_ne hne]
    · simp [extend, hm, Function.update_of_ne hf]

/-- Changing one edge weight changes a trail cost by that weight difference
when the edge belongs to the trail, and by zero otherwise. -/
lemma trailCost_one_edge_change (w w' : Edge → ℝ) (e : Edge)
    (h : ∀ f, f ≠ e → w' f = w f) (p : Vertex) (ds : List Step)
    (hn : ((trace p ds).map traversalEdge).Nodup) :
    pathCost w' p ds - pathCost w p ds =
      if e ∈ (trace p ds).map traversalEdge then w' e - w e else 0 := by
  classical
  rw [pathCost_eq_distinct_edgeSum w' p ds hn, pathCost_eq_distinct_edgeSum w p ds hn,
    ← Finset.sum_sub_distrib]
  by_cases he : e ∈ (trace p ds).map traversalEdge
  · rw [ite_eq_left he]
    apply Finset.sum_eq_single_of_mem e (List.mem_toFinset.mpr he)
    intro f _ hfe
    rw [h f hfe, sub_self]
  · rw [ite_eq_right he]
    apply Finset.sum_eq_zero
    intro f hf
    have hfe : f ≠ e := by
      intro hfe
      exact he (hfe ▸ List.mem_toFinset.mp hf)
    rw [h f hfe, sub_self]

lemma upward_nonneg (w : Edge → ℝ) (p q : Vertex) (R : ℕ) (e : Edge) (u : ℝ) :
    0 ≤ upward w p q R e u := le_max_right _ _

/-- One minimizing trail in the initial environment controls every upward
coordinate-resampling increment. -/
lemma upward_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R : ℕ) (ds : List Step) (hds : ds ∈ candidates p q R)
    (hm : pathCost w p ds = passageTime w p q R) (e : Edge) (u : ℝ) (hu : 0 ≤ u) :
    upward w p q R e u ≤ if e ∈ (trace p ds).map traversalEdge then u else 0 := by
  classical
  have hn := ((mem_candidates p q R ds).mp hds).2.1
  have hb := passageTime_le_candidate (Function.update w e u) p q R ds hds
  have he := trailCost_one_edge_change w (Function.update w e u) e
    (fun f hf => Function.update_of_ne hf _ _) p ds hn
  simp only [Function.update_self] at he
  unfold upward
  apply max_le
  · split_ifs at he ⊢ with hmem
    · linarith [hw e]
    · linarith
  · split_ifs <;> positivity

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalRegularity
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP MeasureTheory

lemma pathCost_eq_of_agree (w w' : Edge → ℝ) (p : Vertex) (ds : List Step)
    (h : ∀ e ∈ (trace p ds).map traversalEdge, w e = w' e) :
    pathCost w p ds = pathCost w' p ds := by
  rw [pathCost_trace_edge_sum, pathCost_trace_edge_sum]
  congr 1
  exact List.map_congr_left h

lemma candidate_pathCost_eq (w w' : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (h : ∀ e ∈ localEdges p q R, w e = w' e)
    (ds : List Step) (hds : ds ∈ candidates p q R) :
    pathCost w p ds = pathCost w' p ds := by
  apply pathCost_eq_of_agree
  intro e he
  exact h e (candidate_edges_subset p q R ds hds (List.mem_toFinset.mpr he))

/-- Agreement on the finite local edge set implies equality of local passage times. -/
theorem passageTime_eq_of_agree (w w' : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (h : ∀ e ∈ localEdges p q R, w e = w' e) :
    passageTime w p q R = passageTime w' p q R := by
  unfold passageTime
  congr 1
  ext c
  constructor
  · rintro ⟨ds, hds, rfl⟩
    exact ⟨ds, hds, candidate_pathCost_eq w w' p q R h ds hds⟩
  · rintro ⟨ds, hds, rfl⟩
    exact ⟨ds, hds, (candidate_pathCost_eq w w' p q R h ds hds).symm⟩

/-- Restricting weights to the local edge set and extending by zero preserves
the local passage time. -/
theorem finitePassageTime_restrict (p q : Vertex) (R : ℕ) (w : Edge → ℝ) :
    finitePassageTime p q R (fun e : ↥(localEdges p q R) => w e) =
      passageTime w p q R := by
  apply passageTime_eq_of_agree
  intro e he
  exact extend_apply p q R _ ⟨e, he⟩

/-- The cost of a finite path is continuous in the edge weights. -/
lemma continuous_pathCost (p : Vertex) (ds : List Step) :
    Continuous (fun w : Edge → ℝ => pathCost w p ds) := by
  induction ds generalizing p with
  | nil => exact continuous_const
  | cons d ds ih =>
      exact (continuous_apply (d.edge p)).add (ih (p + d.delta))

/-- Identify the real sInf with the nonempty finite lattice infimum. -/
lemma passageTime_eq_inf' (w : Edge → ℝ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    passageTime w p q R =
      (candidates p q R).inf' (candidates_nonempty p q R hR)
        (fun ds => pathCost w p ds) := by
  apply le_antisymm
  · exact Finset.le_inf' (candidates_nonempty p q R hR) _
      (fun ds hds => passageTime_le_candidate w p q R ds hds)
  · obtain ⟨ds, hds, hm⟩ := minimizing_candidate w p q R hR
    rw [← hm]
    exact Finset.inf'_le _ hds

/-- Local passage time is continuous when the candidate family is nonempty. -/
theorem continuous_passageTime (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    Continuous (fun w : Edge → ℝ => passageTime w p q R) := by
  have he : (fun w : Edge → ℝ => passageTime w p q R) =
      (fun w => (candidates p q R).inf' (candidates_nonempty p q R hR)
        (fun ds => pathCost w p ds)) := by
    funext w
    exact passageTime_eq_inf' w p q R hR
  rw [he]
  exact Continuous.finset_inf'_apply (candidates_nonempty p q R hR)
    (fun ds _ => continuous_pathCost p ds)

lemma continuous_extend (p q : Vertex) (R : ℕ) : Continuous (extend p q R) := by
  classical
  apply continuous_pi
  intro e
  by_cases he : e ∈ localEdges p q R
  · simpa only [extend, dite_eq_left he] using
      (continuous_apply (⟨e, he⟩ : ↥(localEdges p q R)))
  · simpa only [extend, dite_eq_right he] using
      (continuous_const : Continuous (fun _ : Coordinates p q R => (0 : ℝ)))

@[fun_prop] theorem continuous_finitePassageTime (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) : Continuous (finitePassageTime p q R) :=
  (continuous_passageTime p q R hR).comp (continuous_extend p q R)

@[fun_prop] theorem measurable_finitePassageTime (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) : Measurable (finitePassageTime p q R) :=
  (continuous_finitePassageTime p q R hR).measurable

/-- Local passage time is measurable as a function of the edge weights. -/
@[fun_prop] theorem measurable_passageTime (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    Measurable (fun w : Edge → ℝ => passageTime w p q R) :=
  (continuous_passageTime p q R hR).measurable

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ExponentialIncrement
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Real

/-- Global, signed version of the elementary exponential increment estimate. -/
lemma abs_exp_sub_one_le_abs_mul_exp_abs (x : ℝ) :
    |exp x - 1| ≤ |x| * exp |x| := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hx))]
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (exp_pos x).le
    rw [← Real.exp_add] at h
    simp only [neg_add_cancel, Real.exp_zero] at h
    nlinarith
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hx'))]
    have h₁ := Real.add_one_le_exp x
    have h₂ := mul_le_mul_of_nonneg_left (Real.one_le_exp (neg_nonneg.mpr hx'))
      (neg_nonneg.mpr hx')
    nlinarith

/-- Pointwise domination on the support; it also covers u=0 and a=0. -/
lemma half_exp_increment_square_domination {rate a u : ℝ}
    (hrate : 0 < rate) (ha : |a| ≤ rate / 4) (hu : 0 ≤ u) :
    (exp (a*u/2)-1)^2 ≤ (8 / rate^2 * a^2) * exp ((rate/2)*u) := by
  have hab := abs_exp_sub_one_le_abs_mul_exp_abs (a*u/2)
  have hsq : (exp (a*u/2)-1)^2 ≤
      (a^2*u^2/4) * exp (|a| * u) := by
    have h := mul_self_le_mul_self (abs_nonneg (exp (a*u/2)-1)) hab
    rw [← sq, sq_abs] at h
    have he : (|a * u / 2| * exp |a * u / 2|)^2 =
        (a^2*u^2/4) * exp (|a| * u) := by
      rw [mul_pow, sq_abs]
      have he' : (exp |a * u / 2|)^2 = exp (|a| * u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        rw [abs_div, abs_mul, abs_of_nonneg hu]
        norm_num
      rw [he']
      ring
    exact h.trans_eq (by simpa only [pow_two] using he)
  have hmono : exp (|a| * u) ≤ exp ((rate/4)*u) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hu)
  have ht := Real.pow_div_factorial_le_exp ((rate/4)*u) (show 0 ≤ (rate/4)*u by positivity) 2
  norm_num at ht
  have hpoly : u^2 ≤ (32 / rate^2) * exp ((rate/4)*u) := by
    have haux : u^2 ≤ (32 * exp ((rate/4)*u)) / rate^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hrate)).mpr
      nlinarith
    convert haux using 1; ring
  calc
    (exp (a*u/2)-1)^2 ≤ (a^2*u^2/4)*exp ((rate/4)*u) :=
      hsq.trans (mul_le_mul_of_nonneg_left hmono (by positivity))
    _ ≤ (a^2*((32/rate^2)*exp ((rate/4)*u))/4)*exp ((rate/4)*u) := by
      gcongr
    _ = (8/rate^2*a^2)*exp ((rate/2)*u) := by
      have he : exp ((rate/4)*u)*exp ((rate/4)*u) = exp ((rate/2)*u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (8/rate^2*a^2)*(exp ((rate/4)*u)*exp ((rate/4)*u)) := by ring
        _ = _ := by rw [he]

/-- Integrability follows from a positive Gamma moment at rate/2. -/
theorem gamma_integrable_half_exp_increment_square {shape rate a : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (ha : |a| ≤ rate/4) :
    Integrable (fun u : ℝ => (exp (a*u/2)-1)^2) (gammaMeasure shape rate) := by
  have hi := (gamma_integrable_exp hshape hrate (show rate/2 < rate by linarith)).const_mul
    (8/rate^2*a^2)
  apply hi.mono' (by fun_prop)
  filter_upwards [gamma_ae_pos shape rate] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact half_exp_increment_square_domination hrate ha hu.le

/-- Signed quadratic increment estimate for all positive shape and rate. -/
theorem gamma_integral_half_exp_increment_square_le {shape rate a : ℝ}
    (hshape : 0 < shape) (hrate : 0 < rate) (ha : |a| ≤ rate/4) :
    (∫ u : ℝ, (exp (a*u/2)-1)^2 ∂gammaMeasure shape rate) ≤
      (8*(2 : ℝ)^shape/rate^2)*a^2 := by
  have hi := (gamma_integrable_exp hshape hrate (show rate/2 < rate by linarith)).const_mul
    (8/rate^2*a^2)
  have h := integral_mono_ae (gamma_integrable_half_exp_increment_square hshape hrate ha) hi
    ((gamma_ae_pos shape rate).mono fun u hu => half_exp_increment_square_domination hrate ha hu.le)
  calc
    _ ≤ ∫ u : ℝ, (8/rate^2*a^2)*exp ((rate/2)*u) ∂gammaMeasure shape rate := h
    _ = (8/rate^2*a^2)*(rate/(rate-rate/2))^shape := by
      rw [integral_const_mul, gamma_integral_exp hshape hrate (show rate/2 < rate by linarith)]
    _ = (8*(2 : ℝ)^shape/rate^2)*a^2 := by
      have he : rate/(rate-rate/2) = (2 : ℝ) := by
        apply (div_eq_iff (show rate-rate/2 ≠ 0 by linarith)).mpr
        ring
      rw [he]
      ring
end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalResamplingExponential
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real Finset
open scoped ENNReal

/-- A single minimizing trail bounds the summed upward resampling increments
for every replacement law supported on nonnegative weights. -/
theorem sum_upward_transform (μ : Measure ℝ) (hμ : ∀ᵐ u ∂μ, 0 ≤ u)
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (φ : ℝ → ℝ≥0∞)
    (hφ : MonotoneOn φ (Set.Ici 0)) (hzero : φ 0 = 0) :
    (∑ e ∈ localEdges p q R, ∫⁻ u, φ (upward w p q R e u) ∂μ) ≤
      (∫⁻ u, φ u ∂μ) * R := by
  classical
  obtain ⟨ds, hds, hm⟩ := minimizing_candidate w p q R hR
  obtain ⟨hend, hn, hl⟩ := (mem_candidates p q R ds).mp hds
  have hsub := candidate_edges_subset p q R ds hds
  have he : ∀ e, (∫⁻ u, φ (upward w p q R e u) ∂μ) ≤
      if e ∈ (trace p ds).map traversalEdge then ∫⁻ u, φ u ∂μ else 0 := by
    intro e
    by_cases he : e ∈ (trace p ds).map traversalEdge
    · rw [ite_eq_left he]
      apply lintegral_mono_ae
      filter_upwards [hμ] with u hu
      apply hφ (upward_nonneg w p q R e u) hu
      simpa only [ite_eq_left he] using upward_le w hw p q R ds hds hm e u hu
    · rw [ite_eq_right he, ← lintegral_zero (μ := μ)]
      apply lintegral_mono_ae
      filter_upwards [hμ] with u hu
      have hb := upward_le w hw p q R ds hds hm e u hu
      simp only [ite_eq_right he] at hb
      rw [le_antisymm hb (upward_nonneg w p q R e u), hzero]
  calc
    _ ≤ ∑ e ∈ localEdges p q R,
        if e ∈ (trace p ds).map traversalEdge then ∫⁻ u, φ u ∂μ else 0 :=
      Finset.sum_le_sum (fun e _ => he e)
    _ = ∑ e ∈ ((trace p ds).map traversalEdge).toFinset, ∫⁻ u, φ u ∂μ := by
      rw [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter, List.mem_toFinset]
      exact and_iff_right_of_imp (fun he => hsub (List.mem_toFinset.mpr he))
    _ = (ds.length : ℝ≥0∞) * ∫⁻ u, φ u ∂μ := by
      rw [Finset.sum_const, nsmul_eq_mul, List.toFinset_card_of_nodup hn,
        trace_edge_length]
    _ ≤ (∫⁻ u, φ u ∂μ) * R := by
      rw [mul_comm]
      gcongr

/-- Scalar monotonicity holds for negative as well as positive a. -/
lemma exponential_increment_monotone (a : ℝ) :
    MonotoneOn (fun u => ENNReal.ofReal ((exp (a*u/2)-1)^2)) (Set.Ici 0) := by
  intro u hu v hv huv
  change 0 ≤ u at hu
  change 0 ≤ v at hv
  apply ENNReal.ofReal_le_ofReal
  rcases le_total 0 a with ha | ha
  · have he : exp (a*u/2) ≤ exp (a*v/2) := exp_le_exp.mpr (by nlinarith)
    have h1 : 1 ≤ exp (a*u/2) := one_le_exp_iff.mpr (by nlinarith)
    nlinarith
  · have he : exp (a*v/2) ≤ exp (a*u/2) := exp_le_exp.mpr (by nlinarith)
    have h1 : exp (a*u/2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith)
    nlinarith

lemma gamma_lintegral_half_exp_increment_square_le {shape rate a : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ha : |a| ≤ rate/4) :
    (∫⁻ u : ℝ, ENNReal.ofReal ((exp (a*u/2)-1)^2) ∂gammaMeasure shape rate) ≤
      ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (gamma_integrable_half_exp_increment_square hs hr ha)
    (Filter.Eventually.of_forall (fun u => sq_nonneg (exp (a*u/2)-1)))]
  exact ENNReal.ofReal_le_ofReal (gamma_integral_half_exp_increment_square_le hs hr ha)

/-- Quadratic Gamma proxy, uniform in ambient edge-set cardinality. -/
theorem sum_upward_exponential {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (a : ℝ) (ha : |a| ≤ rate/4) :
    (∑ e ∈ localEdges p q R, ∫⁻ u, ENNReal.ofReal
      ((exp (a * upward w p q R e u / 2)-1)^2) ∂gammaMeasure shape rate) ≤
      ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2) * R := by
  apply (sum_upward_transform (gammaMeasure shape rate)
    ((gamma_ae_pos shape rate).mono (fun _ hu => hu.le))
    w hw p q R hR _ (exponential_increment_monotone a) (by simp)).trans
  exact _root_.mul_le_mul_left (gamma_lintegral_half_exp_increment_square_le hs hr ha) _

/-- The summed exponential upward increments are bounded uniformly over every
nonnegative finite coordinate assignment. -/
theorem finite_upward_exponential_sum {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (v : Coordinates p q R) (hv : ∀ e, 0 ≤ v e) (a : ℝ) (ha : |a| ≤ rate/4) :
    (∑ e : ↥(localEdges p q R), ∫⁻ u, ENNReal.ofReal
      ((exp (a * max (finitePassageTime p q R (Function.update v e u) -
        finitePassageTime p q R v) 0 / 2)-1)^2) ∂gammaMeasure shape rate) ≤
      ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2) * R := by
  classical
  have hb := sum_upward_exponential hs hr (extend p q R v) (extend_nonneg p q R v hv)
    p q R hR a ha
  rw [← Finset.sum_attach (localEdges p q R)] at hb
  simpa only [Finset.attach_eq_univ, finitePassageTime, extend_update, upward] using hb

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.LatticePassage_ProductVariance
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

lemma square_integral_le_integral_square {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ ∫ x, (f x)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  simp only [Pi.pow_apply] at h
  linarith

lemma bounded_memLp_two {f : α → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (.of_forall (by simpa only [Real.norm_eq_abs] using hC))

lemma abs_integral_le_bound {f : α → ℝ} (C : ℝ) (hC : ∀ x, |f x| ≤ C) (_h0 : 0 ≤ C) :
    |∫ x, f x ∂μ| ≤ C := by
  simpa using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (.of_forall (by simpa only [Real.norm_eq_abs] using hC))

theorem product_variance_decomposition {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y => f (x,y)) ν ∂μ) +
        variance (fun x => ∫ y, f (x,y) ∂ν) μ := by
  let g := fun x => ∫ y, f (x,y) ∂ν
  have hfm := bounded_memLp_two (μ := μ.prod ν) hf C hC
  have hsm : ∀ x, MemLp (fun y => f (x,y)) 2 ν := fun x =>
    bounded_memLp_two (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hC (x,y))
  have hgm : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hgb : ∀ x, |g x| ≤ C := fun x => abs_integral_le_bound C (fun y => hC (x,y)) hC0
  have hg := bounded_memLp_two (μ := μ) hgm C hgb
  have hv : (fun x => variance (fun y => f (x,y)) ν) =
      fun x => (∫ y, (f (x,y))^2 ∂ν) - (g x)^2 := by
    funext x
    exact variance_eq_sub (hsm x)
  rw [hv, integral_sub hfm.integrable_sq.integral_prod_left hg.integrable_sq,
    variance_eq_sub hfm, variance_eq_sub hg]
  have hi := integral_prod f (hfm.integrable (by norm_num))
  have hi2 := integral_prod (fun z => (f z)^2) hfm.integrable_sq
  change _ = _ - _ + (_ - _)
  simp only [Pi.pow_apply]
  rw [hi, hi2]
  dsimp [g]
  ring

theorem variance_integral_le_integral_variance {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    variance (fun x => ∫ y, f (x,y) ∂ν) μ ≤
      ∫ y, variance (fun x => f (x,y)) μ ∂ν := by
  let g := fun x => ∫ y, f (x,y) ∂ν
  let h := fun y => ∫ x, f (x,y) ∂μ
  have hfm := bounded_memLp_two (μ := μ.prod ν) hf C hC
  have hgm : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hhm : Measurable h := hf.stronglyMeasurable.integral_prod_left'.measurable
  have hgb : ∀ x, |g x| ≤ C := fun x => abs_integral_le_bound C (fun y => hC (x,y)) hC0
  have hhb : ∀ y, |h y| ≤ C := fun y => abs_integral_le_bound C (fun x => hC (x,y)) hC0
  have hg := bounded_memLp_two (μ := μ) hgm C hgb
  have hh := bounded_memLp_two (μ := ν) hhm C hhb
  let D := fun z : α × β => f z - h z.2
  have hDm : Measurable D := hf.sub (hhm.comp measurable_snd)
  have hDb : ∀ z, |D z| ≤ 2*C := by
    intro z
    exact (abs_sub _ _).trans (by linarith [hC z, hhb z.2])
  have hD := bounded_memLp_two (μ := μ.prod ν) hDm (2*C) hDb
  have hmean : (∫ y, h y ∂ν) = ∫ x, g x ∂μ :=
    (integral_integral_swap (f := fun x y => f (x,y)) (hfm.integrable (by norm_num))).symm
  have he : ∀ x, (∫ y, D (x,y) ∂ν) = g x - ∫ z, g z ∂μ := by
    intro x
    dsimp [D]
    rw [integral_sub (f := fun y => f (x,y)) (g := h) ((bounded_memLp_two (hf.comp (measurable_const.prodMk measurable_id))
      C (fun y => hC (x,y))).integrable (by norm_num)) (hh.integrable (by norm_num)), hmean]
  have hp : ∀ x, (g x - ∫ z, g z ∂μ)^2 ≤ ∫ y, (D (x,y))^2 ∂ν := by
    intro x
    rw [← he x]
    exact square_integral_le_integral_square
      (bounded_memLp_two (hDm.comp (measurable_const.prodMk measurable_id)) (2*C)
        (fun y => hDb (x,y)))
  rw [variance_eq_integral hgm.aemeasurable]
  apply (integral_mono (hg.sub (memLp_const _)).integrable_sq
    hD.integrable_sq.integral_prod_left hp).trans_eq
  rw [integral_integral_swap (f := fun x y => (D (x,y))^2) hD.integrable_sq]
  apply integral_congr_ae
  exact .of_forall (fun y => (variance_eq_integral
    (hf.comp (measurable_id.prodMk measurable_const)).aemeasurable).symm)

theorem product_variance_le {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    variance f (μ.prod ν) ≤
      (∫ x, variance (fun y => f (x,y)) ν ∂μ) +
      (∫ y, variance (fun x => f (x,y)) μ ∂ν) := by
  rw [product_variance_decomposition (μ := μ) (ν := ν) hf hC0 hC]
  exact add_le_add le_rfl (variance_integral_le_integral_variance (μ := μ) (ν := ν) hf hC0 hC)

lemma measurable_section_variance {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ z, |f z| ≤ C) :
    Measurable (fun x => variance (fun y => f (x,y)) ν) := by
  have he : (fun x => variance (fun y => f (x,y)) ν) =
      fun x => (∫ y, (f (x,y))^2 ∂ν) - (∫ y, f (x,y) ∂ν)^2 := by
    funext x
    exact variance_eq_sub (bounded_memLp_two
      (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hC (x,y)))
  rw [he]
  exact (hf.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.sub
    (hf.stronglyMeasurable.integral_prod_right'.measurable.pow_const 2)

lemma variance_le_bound_square {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (_hC0 : 0 ≤ C) (hC : ∀ x, |f x| ≤ C) : variance f μ ≤ C^2 := by
  have hm := bounded_memLp_two (μ := μ) hf C hC
  apply (variance_le_expectation_sq hf.aestronglyMeasurable).trans
  have h := integral_mono hm.integrable_sq (integrable_const (C^2))
    (fun x => show (f x)^2 ≤ C^2 by nlinarith [hC x, abs_le.mp (hC x)])
  simpa using h

lemma integrable_section_variance {f : α × β → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, |f z| ≤ C) :
    Integrable (fun x => variance (fun y => f (x,y)) ν) μ := by
  apply (bounded_memLp_two (measurable_section_variance hf hC) (C^2) ?_).integrable
    (by norm_num)
  intro x
  rw [abs_of_nonneg (variance_nonneg _ _)]
  exact variance_le_bound_square (hf.comp (measurable_const.prodMk measurable_id))
    hC0 (fun y => hC (x,y))

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.LatticePassage_FiniteVariance
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

lemma measurable_finCons (n : ℕ) :
    Measurable (fun z : α × (Fin n → α) => (Fin.cons z.1 z.2 : Fin (n+1) → α)) := by
  apply Measurable.of_eval
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa only [Function.comp_def, Fin.cons_succ] using (measurable_pi_apply j).comp (measurable_snd :
      Measurable (Prod.snd : α × (Fin n → α) → (Fin n → α)))

lemma finCons_preserving (n : ℕ) :
    MeasurePreserving (fun z : α × (Fin n → α) => Fin.cons z.1 z.2)
      (μ.prod (Measure.pi (fun _ : Fin n => μ)))
      (Measure.pi (fun _ : Fin (n+1) => μ)) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm

lemma integral_finCons {n : ℕ} {f : (Fin (n+1) → α) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ v, |f v| ≤ C) :
    (∫ v, f v ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ a, ∫ w, f (Fin.cons a w) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  have he := integral_map (finCons_preserving μ n).aemeasurable hf.aestronglyMeasurable
  rw [(finCons_preserving μ n).map_eq] at he
  rw [he]
  exact integral_prod _ ((bounded_memLp_two (hf.comp (measurable_finCons n))
    C (fun z => hC (Fin.cons z.1 z.2))).integrable (by norm_num))

lemma measurable_coordinateVariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ v, |f v| ≤ C) (i : ι) :
    Measurable (coordinateVariance μ f i) := by
  apply measurable_section_variance (C := C) (f := fun z => f (Function.update z.1 i z.2))
  · exact hf.comp (by fun_prop)
  · exact fun z => hC _

lemma coordinateVariance_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, |f v| ≤ C) (i : ι) (v : ι → α) :
    |coordinateVariance μ f i v| ≤ C^2 := by
  rw [coordinateVariance, abs_of_nonneg (variance_nonneg _ _)]
  exact variance_le_bound_square (hf.comp (by fun_prop)) hC0 (fun _ => hC _)

lemma integrable_coordinateVariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ v, |f v| ≤ C) (i : ι) :
    Integrable (coordinateVariance μ f i) (Measure.pi (fun _ : ι => μ)) :=
  (bounded_memLp_two (measurable_coordinateVariance μ hf hC i) (C^2)
    (coordinateVariance_bound μ hf hC0 hC i)).integrable (by norm_num)

omit [IsProbabilityMeasure μ] in
lemma coordinateVariance_cons_zero {n : ℕ} (f : (Fin (n+1) → α) → ℝ)
    (a : α) (w : Fin n → α) :
    coordinateVariance μ f 0 (Fin.cons a w) = variance (fun u => f (Fin.cons u w)) μ := by
  simp only [coordinateVariance, Fin.update_cons_zero]

omit [IsProbabilityMeasure μ] in
lemma coordinateVariance_cons_succ {n : ℕ} (f : (Fin (n+1) → α) → ℝ)
    (i : Fin n) (a : α) (w : Fin n → α) :
    coordinateVariance μ f i.succ (Fin.cons a w) =
      coordinateVariance μ (fun v => f (Fin.cons a v)) i w := by
  simp only [coordinateVariance, ← Fin.cons_update]

lemma integral_coordinateVariance_zero {n : ℕ} {f : (Fin (n+1) → α) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    (∫ v, coordinateVariance μ f 0 v ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ w, variance (fun u => f (Fin.cons u w)) μ ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [integral_finCons μ (measurable_coordinateVariance μ hf hC 0)
    (coordinateVariance_bound μ hf hC0 hC 0)]
  simp [coordinateVariance_cons_zero]

lemma integral_coordinateVariance_succ {n : ℕ} {f : (Fin (n+1) → α) → ℝ}
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) (i : Fin n) :
    (∫ v, coordinateVariance μ f i.succ v ∂Measure.pi (fun _ : Fin (n+1) => μ)) =
      ∫ a, ∫ w, coordinateVariance μ (fun v => f (Fin.cons a v)) i w
        ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  rw [integral_finCons μ (measurable_coordinateVariance μ hf hC i.succ)
    (coordinateVariance_bound μ hf hC0 hC i.succ)]
  simp only [coordinateVariance_cons_succ]

theorem variance_fin_le_sum_coordinateVariance (n : ℕ)
    {f : (Fin n → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    variance f (Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ i : Fin n, ∫ v, coordinateVariance μ f i v ∂Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero =>
    have he : f = fun _ => f (fun i => Fin.elim0 i) := by
      funext v
      congr 1
      funext i
      exact Fin.elim0 i
    rw [he]
    simp [variance_eq_integral measurable_const.aemeasurable]
  | succ n ih =>
    let F := fun z : α × (Fin n → α) => f (Fin.cons z.1 z.2)
    have hFm : Measurable F := hf.comp (measurable_finCons n)
    have hFb : ∀ z, |F z| ≤ C := fun z => hC _
    have he : variance f (Measure.pi (fun _ : Fin (n+1) => μ)) =
        variance F (μ.prod (Measure.pi (fun _ : Fin n => μ))) := by
      rw [← (finCons_preserving μ n).map_eq,
        variance_map hf.aemeasurable (finCons_preserving μ n).aemeasurable]
      rfl
    rw [he]
    have hv := product_variance_le (μ := μ) (ν := Measure.pi (fun _ : Fin n => μ))
      hFm hC0 hFb
    apply hv.trans
    have hI : ∀ i : Fin n, Integrable (fun a => ∫ w,
        coordinateVariance μ (fun v => f (Fin.cons a v)) i w
        ∂Measure.pi (fun _ : Fin n => μ)) μ := by
      intro i
      have hm := (measurable_coordinateVariance μ hf hC i.succ).comp (measurable_finCons n)
      have hb := fun z : α × (Fin n → α) =>
        coordinateVariance_bound μ hf hC0 hC i.succ (Fin.cons z.1 z.2)
      have hi := (bounded_memLp_two (μ := μ.prod (Measure.pi (fun _ : Fin n => μ)))
        hm (C^2) hb).integrable (by norm_num)
      simpa only [Function.comp_def, coordinateVariance_cons_succ] using hi.integral_prod_left
    have hstep := integral_mono (integrable_section_variance hFm hC0 hFb)
      (integrable_finsetSum Finset.univ (fun i _ => hI i)) (fun a =>
        ih (hf.comp ((measurable_finCons n).comp (measurable_const.prodMk measurable_id)))
          (fun v => hC (Fin.cons a v)))
    rw [integral_finsetSum _ (fun i _ => hI i)] at hstep
    rw [Fin.sum_univ_succ, integral_coordinateVariance_zero μ hf hC0 hC]
    simp_rw [integral_coordinateVariance_succ μ hf hC0 hC]
    dsimp [F] at hstep ⊢
    linarith

lemma reindex_preserving {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ ≃ ι) :
    MeasurePreserving (fun v : κ → α => fun i => v (e.symm i))
      (Measure.pi (fun _ : κ => μ)) (Measure.pi (fun _ : ι => μ)) := by
  convert measurePreserving_piCongrLeft (fun _ : ι => μ) e using 1
  funext v i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

omit [IsProbabilityMeasure μ] in
lemma coordinateVariance_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : κ ≃ ι) (f : (ι → α) → ℝ) (j : κ) (v : κ → α) :
    coordinateVariance μ (fun w => f (fun i => w (e.symm i))) j v =
      coordinateVariance μ f (e j) (fun i => v (e.symm i)) := by
  unfold coordinateVariance
  congr 1
  funext u
  dsimp only
  congr 1
  funext i
  by_cases hi : i = e j
  · subst i
    simp
  · have hj : e.symm i ≠ j := by
      intro h
      apply hi
      simpa using congrArg e h
    simp [Function.update_of_ne hi, Function.update_of_ne hj]

theorem variance_pi_le_sum_coordinateVariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    variance f (Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫ v, coordinateVariance μ f i v ∂Measure.pi (fun _ : ι => μ) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hmp := reindex_preserving μ e
  have hg := hf.comp hmp.measurable
  have ht := variance_fin_le_sum_coordinateVariance μ (Fintype.card ι) hg hC0
    (fun w => hC (fun i => w (e.symm i)))
  simp only [Function.comp_def] at ht
  rw [hmp.variance_fun_comp hf.aemeasurable] at ht
  simp only [coordinateVariance_reindex] at ht
  have he : ∀ j : Fin (Fintype.card ι),
      (∫ w, coordinateVariance μ f (e j) (fun i => w (e.symm i))
        ∂Measure.pi (fun _ : Fin (Fintype.card ι) => μ)) =
      ∫ v, coordinateVariance μ f (e j) v ∂Measure.pi (fun _ : ι => μ) := by
    intro j
    have h := integral_map hmp.aemeasurable
      (measurable_coordinateVariance μ hf hC (e j)).aestronglyMeasurable
    rw [hmp.map_eq] at h
    exact h.symm
  simp_rw [he] at ht
  rwa [e.sum_comp (fun i => ∫ v, coordinateVariance μ f i v ∂Measure.pi (fun _ : ι => μ))] at ht

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.LatticePassage_ResamplingSymmetry
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

lemma exchangeCoordinate_preserving (i : ι) :
    MeasurePreserving (exchangeCoordinate i)
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)))
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  have hA := measurePreserving_arrowProdEquivProdArrow α α ι (fun _ : ι => μ) (fun _ : ι => μ)
  let s := fun j : ι => if j = i then (Prod.swap : α × α → α × α) else id
  have hs : ∀ j, MeasurePreserving (s j) (μ.prod μ) (μ.prod μ) := by
    intro j
    by_cases hj : j = i
    · simpa [s, hj] using (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    · simpa [s, hj] using (MeasurePreserving.id (μ.prod μ))
  have hp := measurePreserving_pi (fun _ : ι => μ.prod μ) (fun _ : ι => μ.prod μ) hs
  have h := hA.comp (hp.comp hA.symm)
  convert h using 1
  funext z
  apply Prod.ext <;> funext j <;>
    by_cases hj : j = i <;>
    simp [exchangeCoordinate, Function.comp_def, s, hj,
      MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]

omit [Fintype ι] [MeasurableSpace α] in
lemma exchangeCoordinate_first (i : ι) (z : (ι → α) × (ι → α)) :
    (exchangeCoordinate i z).1 = Function.update z.1 i (z.2 i) := rfl

omit [Fintype ι] [MeasurableSpace α] in
lemma exchangeCoordinate_resample (i : ι) (z : (ι → α) × (ι → α)) :
    Function.update (exchangeCoordinate i z).1 i ((exchangeCoordinate i z).2 i) = z.1 := by
  simp [exchangeCoordinate]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ResamplingEnergyIdentity
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.EnergyIdentity
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma exponential_square_difference (a b t : ℝ) :
    (exp (t*b/2)-exp (t*a/2))^2 = exp (t*a)*(exp (t*(b-a)/2)-1)^2 := by
  have h₁ : exp (t*b/2) = exp (t*a/2)*exp (t*(b-a)/2) := by
    rw [← exp_add]
    congr 1
    ring
  have h₂ : exp (t*a) = exp (t*a/2)^2 := by
    rw [pow_two, ← exp_add]
    congr 1
    ring
  rw [h₁, h₂]
  ring

lemma exponential_square_difference_split (a b t : ℝ) :
    (exp (t*b/2)-exp (t*a/2))^2 =
      exp (t*a)*(exp (t*max (b-a) 0/2)-1)^2 +
      exp (t*b)*(exp (t*max (a-b) 0/2)-1)^2 := by
  rcases le_total a b with h | h
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    simp only [mul_zero, zero_div, exp_zero, sub_self, zero_pow (by omega : 2 ≠ 0),
      mul_zero, add_zero]
    exact exponential_square_difference a b t
  · rw [max_eq_left (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    simp only [mul_zero, zero_div, exp_zero, sub_self, zero_pow (by omega : 2 ≠ 0),
      mul_zero, zero_add]
    rw [sub_sq_comm]
    exact exponential_square_difference b a t

/-- Exchanging a coordinate identifies the backward exponential energy with
the forward one. The weighting belongs to the old environment in each term. -/
theorem exponential_resampling_energy_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (ι → ℝ) → ℝ) (hf : Measurable f)
    (i : ι) (a : ℝ) :
    (∫⁻ z : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      ((exp (a*f (Function.update z.1 i (z.2 i))/2)-exp (a*f z.1/2))^2)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) =
    2 * (∫⁻ z : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal
      (exp (a*f z.1)*(exp (a*max (f (Function.update z.1 i (z.2 i))-f z.1) 0/2)-1)^2)
      ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
  let P := (Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))
  let H := fun z : (ι → ℝ) × (ι → ℝ) => ENNReal.ofReal
    (exp (a*f z.1)*(exp (a*max (f (Function.update z.1 i (z.2 i))-f z.1) 0/2)-1)^2)
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hswap := lintegral_map (μ := P) hH (CompanionFPP.exchangeCoordinate_preserving μ i).measurable
  rw [(CompanionFPP.exchangeCoordinate_preserving μ i).map_eq] at hswap
  have he (x y : ℝ) : ENNReal.ofReal ((exp (a*y/2)-exp (a*x/2))^2) =
      ENNReal.ofReal (exp (a*x)*(exp (a*max (y-x) 0/2)-1)^2) +
      ENNReal.ofReal (exp (a*y)*(exp (a*max (x-y) 0/2)-1)^2) := by
    rw [exponential_square_difference_split, ENNReal.ofReal_add (by positivity) (by positivity)]
  simp_rw [he]
  rw [lintegral_add_left (by fun_prop)]
  have hb : (∫⁻ z, ENNReal.ofReal
      (exp (a*f (Function.update z.1 i (z.2 i)))*
        (exp (a*max (f z.1-f (Function.update z.1 i (z.2 i))) 0/2)-1)^2) ∂P) =
      ∫⁻ z, H z ∂P := by
    rw [hswap]
    apply lintegral_congr
    intro z
    dsimp [H]
    rw [CompanionFPP.exchangeCoordinate_resample, CompanionFPP.exchangeCoordinate_first]
  change (∫⁻ z, H z ∂P) + _ = 2*(∫⁻ z, H z ∂P)
  rw [hb, two_mul]

end GammaFPP.EnergyIdentity

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalExponentialEnergy
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real Finset
open scoped ENNReal

lemma finite_coordinates_nonnegative {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) :
    ∀ᵐ v ∂finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate, ∀ e, 0 ≤ v e := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  rw [ae_all_iff]
  intro e
  exact ((measurePreserving_eval
    (fun _ : ↥(localEdges p q R) => gammaMeasure shape rate) e).quasiMeasurePreserving.ae
      (gamma_ae_pos shape rate)).mono (fun _ hu => hu.le)

/-- The forward resampling energy is bounded after weighting by the exponential
of the passage time in the initial environment. -/
theorem finite_exponential_forward_energy {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (a : ℝ) (ha : |a| ≤ rate/4) :
    (∑ e : ↥(localEdges p q R), ∫⁻ z : Coordinates p q R × Coordinates p q R,
      ENNReal.ofReal (exp (a*finitePassageTime p q R z.1) *
        (exp (a*max (finitePassageTime p q R (Function.update z.1 e (z.2 e))-
          finitePassageTime p q R z.1) 0/2)-1)^2)
      ∂(finiteGammaMeasure shape rate).prod (finiteGammaMeasure shape rate)) ≤
      (ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2)*R) *
        ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime p q R v))
          ∂finiteGammaMeasure shape rate := by
  classical
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by
    dsimp only [P, finiteGammaMeasure]
    infer_instance
  let F := finitePassageTime p q R
  have hF : Measurable F := measurable_finitePassageTime p q R hR
  let K := fun v e u => ENNReal.ofReal ((exp (a*max (F (Function.update v e u)-F v) 0/2)-1)^2)
  have he : ∀ e : ↥(localEdges p q R),
      (∫⁻ z : Coordinates p q R × Coordinates p q R,
        ENNReal.ofReal (exp (a*F z.1))*K z.1 e (z.2 e) ∂P.prod P) =
      ∫⁻ v, ENNReal.ofReal (exp (a*F v))*(∫⁻ u, K v e u ∂gammaMeasure shape rate) ∂P := by
    intro e
    rw [lintegral_prod _ (by dsimp [K]; fun_prop)]
    apply lintegral_congr
    intro v
    dsimp only
    rw [lintegral_const_mul _ (show Measurable (fun w : Coordinates p q R => K v e (w e))
      from by dsimp [K]; fun_prop)]
    congr 1
    have hm := lintegral_map (μ := P) (show Measurable (K v e) from by dsimp [K]; fun_prop)
      (measurable_pi_apply e)
    dsimp only [P, finiteGammaMeasure] at hm
    rw [(measurePreserving_eval
      (fun _ : ↥(localEdges p q R) => gammaMeasure shape rate) e).map_eq] at hm
    exact hm.symm
  simp_rw [ENNReal.ofReal_mul (exp_pos _).le]
  change (∑ e, ∫⁻ z : Coordinates p q R × Coordinates p q R,
    ENNReal.ofReal (exp (a*F z.1))*K z.1 e (z.2 e) ∂P.prod P) ≤ _
  simp_rw [he]
  rw [← lintegral_finsetSum _ (fun e _ => by dsimp [K]; fun_prop)]
  simp_rw [← mul_sum]
  calc
    _ ≤ ∫⁻ v, ENNReal.ofReal (exp (a*F v))*
        (ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2)*R) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [finite_coordinates_nonnegative hs hr p q R] with v hv
      gcongr
      exact finite_upward_exponential_sum hs hr p q R hR v hv a ha
    _ = _ := by
      simp_rw [mul_comm _ (ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2)*R)]
      exact lintegral_const_mul _ (by fun_prop)

/-- Exchanging the initial and resampled coordinates bounds the total exponential
resampling energy by twice the forward energy, for either sign of `a`. -/
theorem finite_exponential_resampling_energy {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (a : ℝ) (ha : |a| ≤ rate/4) :
    (∑ e : ↥(localEdges p q R), ∫⁻ z : Coordinates p q R × Coordinates p q R,
      ENNReal.ofReal ((exp (a*finitePassageTime p q R (Function.update z.1 e (z.2 e))/2) -
        exp (a*finitePassageTime p q R z.1/2))^2)
      ∂(finiteGammaMeasure shape rate).prod (finiteGammaMeasure shape rate)) ≤
      (ENNReal.ofReal ((16*(2 : ℝ)^shape/rate^2)*a^2)*R) *
        ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime p q R v))
          ∂finiteGammaMeasure shape rate := by
  classical
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  simp only [finiteGammaMeasure]
  simp_rw [EnergyIdentity.exponential_resampling_energy_split (gammaMeasure shape rate)
    (finitePassageTime p q R) (measurable_finitePassageTime p q R hR), ← mul_sum]
  have hb := finite_exponential_forward_energy hs hr p q R hR a ha
  simp only [finiteGammaMeasure] at hb
  calc
    _ ≤ 2*((ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2)*R)*
        ∫⁻ v, ENNReal.ofReal (exp (a*finitePassageTime p q R v))
          ∂Measure.pi (fun _ : ↥(localEdges p q R) => gammaMeasure shape rate)) := by
      exact _root_.mul_le_mul_right hb 2
    _ = _ := by
      have he : (2 : ℝ≥0∞)*ENNReal.ofReal ((8*(2 : ℝ)^shape/rate^2)*a^2) =
          ENNReal.ofReal ((16*(2 : ℝ)^shape/rate^2)*a^2) := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
      simp only [← mul_assoc, he]

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_FiniteSumIntegrability
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {ι : Type*} [Fintype ι]

lemma finiteGammaMeasure_ae_nonneg {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ v ∂finiteGammaMeasure (ι := ι) shape rate, ∀ i, 0 ≤ v i := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  unfold finiteGammaMeasure
  rw [ae_all_iff]
  intro i
  exact ((measurePreserving_eval (fun _ : ι => gammaMeasure shape rate) i).quasiMeasurePreserving.ae (gamma_ae_pos shape rate)).mono (fun _ hu => hu.le)

/-- Nonnegative integrals factor over a finite product of probability measures. -/
private lemma finite_probability_lintegral_prod (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ v, ∏ i, f i (v i) ∂Measure.pi μ) = ∏ i, ∫⁻ u, f i u ∂μ i := by
  have hi : iIndepFun (fun i (v : ι → ℝ) => f i (v i)) (Measure.pi μ) :=
    iIndepFun_pi (fun i => (hf i).aemeasurable)
  have hh := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
    (fun i => (hf i).comp (measurable_pi_apply i))
  rw [hh]
  apply Finset.prod_congr rfl
  intro i _
  rw [← lintegral_map (hf i) (measurable_pi_apply i),
    (measurePreserving_eval μ i).map_eq]

/-- Exact nonnegative exponential moment for the sum of all finite coordinates. -/
theorem finite_gamma_lintegral_exp_sum {shape rate t : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ht : t < rate) :
    (∫⁻ v : ι → ℝ, ENNReal.ofReal (Real.exp (t * ∑ i, v i))
      ∂finiteGammaMeasure shape rate) =
      (ENNReal.ofReal ((rate / (rate-t)) ^ shape)) ^ Fintype.card ι := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hs hr
  have he (v : ι → ℝ) : ENNReal.ofReal (Real.exp (t * ∑ i, v i)) =
      ∏ i, ENNReal.ofReal (Real.exp (t * v i)) := by
    rw [Finset.mul_sum, Real.exp_sum]
    exact ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)
  simp_rw [he]
  unfold finiteGammaMeasure
  rw [finite_probability_lintegral_prod _
    (fun _ u => ENNReal.ofReal (Real.exp (t*u))) (fun _ => by fun_prop)]
  simp only [gamma_lintegral_exp hs hr ht, Finset.prod_const, Finset.card_univ]

/-- The exponential moment of the coordinate sum is finite for every `t < rate`. -/
theorem finite_gamma_integrable_exp_sum {shape rate t : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (ht : t < rate) :
    Integrable (fun v : ι → ℝ => Real.exp (t * ∑ i, v i))
      (finiteGammaMeasure shape rate) := by
  have hm : Measurable (fun v : ι → ℝ => Real.exp (t * ∑ i, v i)) := by fun_prop
  apply (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun v => (Real.exp_pos _).le))).mp
  rw [finite_gamma_lintegral_exp_sum hs hr ht]
  exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalIntegrability
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP

/-- Nonnegative candidate cost is bounded by the sum on its containing edge set.
Nodup is essential: the finite coordinates are physical edges, not traversals. -/
lemma finitePassageTime_le_sum (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (v : Coordinates p q R)
    (hv : ∀ e, 0 ≤ v e) : finitePassageTime p q R v ≤ ∑ e, v e := by
  classical
  obtain ⟨ds, hds⟩ := candidates_nonempty p q R hR
  have hn := ((mem_candidates p q R ds).mp hds).2.1
  have hsub := candidate_edges_subset p q R ds hds
  have hw := extend_nonneg p q R v hv
  change passageTime (extend p q R v) p q R ≤ _
  apply (passageTime_le_candidate (extend p q R v) p q R ds hds).trans
  rw [pathCost_eq_distinct_edgeSum (extend p q R v) p ds hn]
  calc
    _ ≤ ∑ e ∈ localEdges p q R, extend p q R v e :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hw e)
    _ = ∑ e : ↥(localEdges p q R), v e := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro e _
      exact extend_apply p q R v e

lemma finitePassageTime_nonneg (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (v : Coordinates p q R)
    (hv : ∀ e, 0 ≤ v e) : 0 ≤ finitePassageTime p q R v :=
  passageTime_nonneg (extend p q R v) (extend_nonneg p q R v hv) p q R hR

/-- All real t<=rate/2 are allowed, including arbitrarily negative t. -/
theorem integrable_finitePassageTime_exp {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (t : ℝ) (ht : t ≤ rate/2) :
    Integrable (fun v => Real.exp (t * finitePassageTime p q R v))
      (finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate) := by
  have hi := finite_gamma_integrable_exp_sum (ι := ↥(localEdges p q R)) hs hr
    (show rate/2 < rate by linarith)
  have hm : Measurable (fun v => Real.exp (t * finitePassageTime p q R v)) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_finitePassageTime p q R hR))
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [finiteGammaMeasure_ae_nonneg (ι := ↥(localEdges p q R)) hs hr] with v hv
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_right ht (finitePassageTime_nonneg p q R hR v hv)).trans
    (mul_le_mul_of_nonneg_left (finitePassageTime_le_sum p q R hR v hv) (by positivity))

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.LatticePassage_BoundedEfronStein
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

lemma variance_le_integral_square_sub {f : α → ℝ} (hf : Measurable f) (c : ℝ) :
    variance f μ ≤ ∫ u, (f u-c)^2 ∂μ := by
  have h := variance_le_expectation_sq (μ := μ) (hf.sub_const c).aestronglyMeasurable
  rw [variance_sub_const hf.aestronglyMeasurable c] at h
  exact h

theorem bounded_efron_stein {f : (ι → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    variance f (Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫ z : (ι → α) × (ι → α),
        (f (Function.update z.1 i (z.2 i)) - f z.1)^2
        ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)) := by
  apply (variance_pi_le_sum_coordinateVariance μ hf hC0 hC).trans
  apply sum_le_sum
  intro i _
  let G := fun z : (ι → α) × (ι → α) => (f (Function.update z.1 i (z.2 i))-f z.1)^2
  have hGm : Measurable G := by dsimp [G]; fun_prop
  have hGb : ∀ z, |G z| ≤ (2*C)^2 := by
    intro z
    have hb : |f (Function.update z.1 i (z.2 i))-f z.1| ≤ 2*C :=
      (abs_sub _ _).trans (by linarith [hC (Function.update z.1 i (z.2 i)), hC z.1])
    dsimp [G]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp hb]
  have hGi := (bounded_memLp_two (μ := (Measure.pi (fun _ : ι => μ)).prod
      (Measure.pi (fun _ : ι => μ))) hGm ((2*C)^2) hGb).integrable (by norm_num)
  rw [integral_prod _ hGi]
  apply integral_mono (integrable_coordinateVariance μ hf hC0 hC i) hGi.integral_prod_left
  intro v
  have he : (∫ w : ι → α, G (v,w) ∂Measure.pi (fun _ : ι => μ)) =
      ∫ u, (f (Function.update v i u)-f v)^2 ∂μ := by
    exact integral_comp_eval (μ := fun _ : ι => μ) (i := i)
      (f := fun u => (f (Function.update v i u)-f v)^2)
      (show Measurable (fun u => (f (Function.update v i u)-f v)^2) from by fun_prop).aestronglyMeasurable
  change coordinateVariance μ f i v ≤ ∫ w, G (v,w) ∂Measure.pi (fun _ : ι => μ)
  rw [he]
  exact variance_le_integral_square_sub μ (hf.comp (by fun_prop)) (f v)

theorem bounded_centered_square_lintegral {f : (ι → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ v, |f v| ≤ C) :
    (∫⁻ v : ι → α, ENNReal.ofReal ((f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2)
      ∂Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
        ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2)
        ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)) := by
  have hv := ENNReal.ofReal_le_ofReal (bounded_efron_stein μ hf hC0 hC)
  rw [variance_eq_integral hf.aemeasurable] at hv
  have hm := bounded_memLp_two (μ := Measure.pi (fun _ : ι => μ)) hf C hC
  rw [ofReal_integral_eq_lintegral_ofReal (f := fun v => (f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2) (hm.sub (memLp_const _)).integrable_sq
    (by filter_upwards [] with v; positivity)] at hv
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg (fun z => sq_nonneg _))] at hv
  apply hv.trans
  apply sum_le_sum
  intro i _
  have hm : MemLp (fun z : (ι → α) × (ι → α) =>
      f (Function.update z.1 i (z.2 i))-f z.1) 2
      ((Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ))) := by
    apply bounded_memLp_two (by fun_prop) (2*C)
    intro z
    exact (abs_sub _ _).trans (by linarith [hC (Function.update z.1 i (z.2 i)), hC z.1])
  rw [ofReal_integral_eq_lintegral_ofReal hm.integrable_sq
    (by filter_upwards [] with z; positivity)]

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.LatticePassage_EfronStein
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

lemma clipReal_bound (n : ℕ) (a : ℝ) : |clipReal n a| ≤ n := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (min_le_right _ _)

lemma clipReal_lipschitz (n : ℕ) (a b : ℝ) : |clipReal n a-clipReal n b| ≤ |a-b| := by
  have h₁ := abs_max_sub_max_le_max (-(n : ℝ)) (min a n) (-(n : ℝ)) (min b n)
  have h₂ := abs_min_sub_min_le_max a (n : ℝ) b n
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (min a (n : ℝ)-min b n))] at h₁
  simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (a-b))] at h₂
  exact h₁.trans h₂

lemma clipReal_abs_le (n : ℕ) (a : ℝ) : |clipReal n a| ≤ |a| := by
  have h := clipReal_lipschitz n a 0
  have he : clipReal n 0 = 0 := by simp [clipReal]
  simpa only [he, sub_zero] using h

lemma clipReal_tendsto (a : ℝ) : Tendsto (fun n => clipReal n a) atTop (𝓝 a) := by
  obtain ⟨N,hN⟩ := exists_nat_ge |a|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hna : |a| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have ha := abs_le.mp hna
  simp [clipReal, min_eq_left ha.2, max_eq_right ha.1]

theorem centered_square_lintegral_le_resampling {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : (ι → α) → ℝ} (hf : Measurable f)
    (hfi : Integrable f (Measure.pi (fun _ : ι => μ))) :
    (∫⁻ v : ι → α, ENNReal.ofReal ((f v - ∫ w, f w ∂Measure.pi (fun _ : ι => μ))^2)
      ∂Measure.pi (fun _ : ι => μ)) ≤
      ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
        ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2)
        ∂(Measure.pi (fun _ : ι => μ)).prod (Measure.pi (fun _ : ι => μ)) := by
  let P := Measure.pi (fun _ : ι => μ)
  let F := fun n v => clipReal n (f v)
  have hFm : ∀ n, Measurable (F n) := fun n => (measurable_clipReal n).comp hf
  have hmean : Tendsto (fun n => ∫ v, F n v ∂P) atTop (𝓝 (∫ v, f v ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun v => |f v|)
      (fun n => (hFm n).aestronglyMeasurable) hfi.abs
    · intro n
      exact .of_forall (fun v => by simpa only [Real.norm_eq_abs] using clipReal_abs_le n (f v))
    · exact .of_forall (fun v => clipReal_tendsto (f v))
  let H := fun n v => ENNReal.ofReal ((F n v - ∫ w, F n w ∂P)^2)
  have hHm : ∀ n, Measurable (H n) := by intro n; dsimp [H]; fun_prop
  have hlim : ∀ v, Tendsto (fun n => H n v) atTop
      (𝓝 (ENNReal.ofReal ((f v - ∫ w, f w ∂P)^2))) := by
    intro v
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((clipReal_tendsto (f v)).sub hmean).pow 2)
  let E := ∑ i : ι, ∫⁻ z : (ι → α) × (ι → α),
    ENNReal.ofReal ((f (Function.update z.1 i (z.2 i))-f z.1)^2) ∂P.prod P
  have hbound : ∀ n, (∫⁻ v, H n v ∂P) ≤ E := by
    intro n
    apply (bounded_centered_square_lintegral μ (hFm n) (Nat.cast_nonneg n)
      (fun v => clipReal_bound n (f v))).trans
    apply sum_le_sum
    intro i _
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    have h := clipReal_lipschitz n (f (Function.update z.1 i (z.2 i))) (f z.1)
    have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa only [sq_abs] using hs
  change (∫⁻ v, ENNReal.ofReal ((f v - ∫ w, f w ∂P)^2) ∂P) ≤ E
  calc
    _ = ∫⁻ v, liminf (fun n => H n v) atTop ∂P :=
      lintegral_congr (fun v => (hlim v).liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ v, H n v ∂P) atTop := lintegral_liminf_le hHm
    _ ≤ E := by
      apply (liminf_le_liminf (.of_forall hbound)).trans_eq
      simp

end CompanionFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalPassageMGF
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real
open scoped ENNReal

/-- Efron–Stein applied to `exp (a * F / 2)` gives a recursion for the local
passage-time moment-generating function. -/
theorem finitePassageTime_mgf_recursion {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (a : ℝ) (ha : |a| ≤ rate/4) :
    mgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) a ≤
      (mgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) (a/2))^2 +
      ((16*(2 : ℝ)^shape/rate^2)*a^2*R) *
        mgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) a := by
  classical
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by dsimp [P, finiteGammaMeasure]; infer_instance
  let F := finitePassageTime p q R
  let H := fun v => exp (a*F v/2)
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : Measurable F := measurable_finitePassageTime p q R hR
  have hHmeas : Measurable H := by dsimp [H]; fun_prop
  have hExp : Integrable (fun v => exp (a*F v)) P :=
    integrable_finitePassageTime_exp hs hr p q R hR a
      (by have hab := (le_abs_self a).trans ha; linarith)
  have hsq : (fun v => (H v)^2) = fun v => exp (a*F v) := by
    funext v
    dsimp [H]
    rw [pow_two, ← exp_add]
    congr 1
    ring
  have hH : MemLp H 2 P := by
    apply (memLp_two_iff_integrable_sq hHmeas.aestronglyMeasurable).mpr
    rw [hsq]
    exact hExp
  have henergy := finite_exponential_resampling_energy hs hr p q R hR a ha
  have hv : ENNReal.ofReal (variance H P) ≤
      ENNReal.ofReal ((B*a^2*R)*(∫ v, exp (a*F v) ∂P)) := by
    rw [variance_eq_integral hHmeas.aemeasurable,
      ofReal_integral_eq_lintegral_ofReal
        (f := fun v => (H v - ∫ w, H w ∂P)^2)
        (hH.sub (memLp_const _)).integrable_sq
        (by filter_upwards [] with v; positivity)]
    apply (CompanionFPP.centered_square_lintegral_le_resampling
      (gammaMeasure shape rate) hHmeas (hH.integrable (by norm_num))).trans
    apply henergy.trans_eq
    rw [← ofReal_integral_eq_lintegral_ofReal hExp
      (by filter_upwards [] with v; positivity)]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ B*a^2*R),
      ENNReal.ofReal_mul (by positivity : 0 ≤ B*a^2), ENNReal.ofReal_natCast]
  have hM : 0 ≤ ∫ v, exp (a*F v) ∂P := integral_nonneg (fun _ => (exp_pos _).le)
  have hv' := (ENNReal.ofReal_le_ofReal_iff
    (by positivity : 0 ≤ (B*a^2*R)*(∫ v, exp (a*F v) ∂P))).mp hv
  rw [variance_eq_sub hH] at hv'
  simp only [Pi.pow_apply] at hv'
  rw [hsq] at hv'
  have he : (∫ v, H v ∂P) = mgf F P (a/2) := by
    unfold mgf
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro v
    dsimp [H]
    congr 1
    ring
  rw [he] at hv'
  change mgf F P a ≤ (mgf F P (a/2))^2 + (B*a^2*R)*mgf F P a
  change mgf F P a - (mgf F P (a/2))^2 ≤ (B*a^2*R)*mgf F P a at hv'
  linarith

/-- The negative logarithm of `1 - x` is at most `2 * x` for `0 ≤ x ≤ 1 / 2`. -/
private lemma neg_log_one_sub_le (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    -log (1-x) ≤ 2*x := by
  have hp : 0 < 1-x := by linarith
  have h := log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [log_inv] at h
  have hb : (1-x)⁻¹ - 1 ≤ 2*x := by
    rw [inv_eq_one_div]
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hp).mpr
    nlinarith
  exact h.trans hb

/-- Signed log-MGF recursion; the smallness condition is explicit. -/
theorem finitePassageTime_cgf_recursion {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (a : ℝ) (ha : |a| ≤ rate/4)
    (hq : (16*(2 : ℝ)^shape/rate^2)*a^2*R ≤ 1/2) :
    cgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) a ≤
      2*cgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) (a/2) +
      2*((16*(2 : ℝ)^shape/rate^2)*a^2*R) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by dsimp [P, finiteGammaMeasure]; infer_instance
  let F := finitePassageTime p q R
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hab := (le_abs_self a).trans ha
  have hM : 0 < mgf F P a := mgf_pos
    (integrable_finitePassageTime_exp hs hr p q R hR a (by linarith))
  have hM2 : 0 < mgf F P (a/2) := mgf_pos
    (integrable_finitePassageTime_exp hs hr p q R hR (a/2) (by linarith))
  have hrec := finitePassageTime_mgf_recursion hs hr p q R hR a ha
  have hden : 0 < 1-B*a^2*R := by change B*a^2*R ≤ 1/2 at hq; linarith
  have hbound : mgf F P a ≤ (mgf F P (a/2))^2/(1-B*a^2*R) := by
    apply (le_div_iff₀ hden).mpr
    change mgf F P a ≤ (mgf F P (a/2))^2 + (B*a^2*R)*mgf F P a at hrec
    nlinarith
  have hl := log_le_log hM hbound
  rw [log_div (pow_ne_zero _ hM2.ne') hden.ne', log_pow] at hl
  have hlog := neg_log_one_sub_le (B*a^2*R) (by positivity) hq
  change log (mgf F P a) ≤ 2*log (mgf F P (a/2)) + 2*(B*a^2*R)
  norm_num only [Nat.cast_ofNat] at hl
  linarith

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_MGFDerivative
attribute [-instance] _root_.OAI.PlanarFPP.rateOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory Real Filter Topology

lemma exp_derivative_domination {c x t : ℝ} (hc : 0 < c) (hx : 0 ≤ x)
    (ht : t < c/2) : |exp (t*x)*x| ≤ (2/c)*exp (c*x) := by
  have hxbound : x ≤ (2/c)*exp ((c/2)*x) := by
    have hh := Real.add_one_le_exp ((c/2)*x)
    calc
      x ≤ (2*exp ((c/2)*x))/c := (le_div_iff₀ hc).mpr (by nlinarith)
      _ = (2/c)*exp ((c/2)*x) := by ring
  rw [abs_of_nonneg (mul_nonneg (exp_pos _).le hx), mul_comm (exp (t*x)) x]
  calc
    x*exp (t*x) ≤ ((2/c)*exp ((c/2)*x))*exp (t*x) :=
      mul_le_mul_of_nonneg_right hxbound (exp_pos _).le
    _ = (2/c)*exp ((c/2+t)*x) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (2/c)*exp (c*x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (by linarith : c/2+t ≤ c) hx

/-- A nonnegative measurable function with a positive exponential moment is
integrable, and its moment-generating function has derivative equal to its mean
at zero. Finiteness of the measure follows by domination. -/
theorem hasDerivAt_integral_exp_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Ω → ℝ} (hF : Measurable F)
    (hpos : ∀ᵐ ω ∂P, 0 ≤ F ω) {c : ℝ} (hc : 0 < c)
    (hexp : Integrable (fun ω => exp (c*F ω)) P) :
    Integrable F P ∧
      HasDerivAt (fun t : ℝ => ∫ ω, exp (t*F ω) ∂P) (∫ ω, F ω ∂P) 0 := by
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := by
    apply hexp.mono' (by fun_prop)
    filter_upwards [hpos] with ω hω
    simpa only [norm_one] using Real.one_le_exp (mul_nonneg hc.le hω)
  have hmeas : ∀ᶠ t : ℝ in 𝓝 0,
      AEStronglyMeasurable (fun ω => exp (t*F ω)) P :=
    Eventually.of_forall fun t => (by fun_prop : Measurable (fun ω => exp (t*F ω))).aestronglyMeasurable
  have hint : Integrable (fun ω => exp ((0 : ℝ)*F ω)) P := by simpa using hone
  have hdmeas : AEStronglyMeasurable (fun ω => exp ((0 : ℝ)*F ω)*F ω) P := by
    fun_prop
  have hbound : ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioo (-c/2) (c/2),
      ‖exp (t*F ω)*F ω‖ ≤ (2/c)*exp (c*F ω) := by
    filter_upwards [hpos] with ω hω
    intro t ht
    rw [Real.norm_eq_abs]
    exact exp_derivative_domination hc hω ht.2
  have hdiff : ∀ᵐ ω ∂P, ∀ t ∈ Set.Ioo (-c/2) (c/2),
      HasDerivAt (fun s : ℝ => exp (s*F ω)) (exp (t*F ω)*F ω) t := by
    filter_upwards [] with ω
    intro t _
    simpa using ((hasDerivAt_id t).mul_const (F ω)).exp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : -c/2 < (0 : ℝ)) (by linarith : (0 : ℝ) < c/2))
    hmeas hint hdmeas hbound (hexp.const_mul (2/c)) hdiff
  simpa only [zero_mul, Real.exp_zero, one_mul] using h

/-- The probability cgf has derivative EF at zero, by the real log chain rule. -/
theorem hasDerivAt_cgf_zero_of_nonneg_exp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Ω → ℝ}
    (hF : Measurable F) (hpos : ∀ᵐ ω ∂P, 0 ≤ F ω) {c : ℝ} (hc : 0 < c)
    (hexp : Integrable (fun ω => exp (c*F ω)) P) :
    HasDerivAt (cgf F P) (∫ ω, F ω ∂P) 0 := by
  have hd := (hasDerivAt_integral_exp_zero hF hpos hc hexp).2
  have hzero : (∫ ω, exp ((0 : ℝ)*F ω) ∂P) = 1 := by simp
  have hl := hd.log (by rw [hzero]; exact one_ne_zero)
  change HasDerivAt (fun t : ℝ => log (∫ ω, exp (t*F ω) ∂P)) (∫ ω, F ω ∂P) 0
  simpa only [hzero, div_one] using hl

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalCenteredCGF
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real Filter Topology

/-- Derivative at zero from the actual positive moment at rate/2. -/
theorem finitePassageTime_hasDerivAt_cgf_zero {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    HasDerivAt (cgf (finitePassageTime p q R) (finiteGammaMeasure shape rate))
      (∫ v, finitePassageTime p q R v ∂finiteGammaMeasure shape rate) 0 := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let : IsProbabilityMeasure (finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate) := by
    unfold finiteGammaMeasure
    infer_instance
  apply hasDerivAt_cgf_zero_of_nonneg_exp (measurable_finitePassageTime p q R hR)
    (c := rate/2) ?_ (by linarith)
    (integrable_finitePassageTime_exp hs hr p q R hR (rate/2) le_rfl)
  filter_upwards [finiteGammaMeasure_ae_nonneg (ι := ↥(localEdges p q R)) hs hr] with v hv
  exact finitePassageTime_nonneg p q R hR v hv

/-- Signed centered cgf estimate, with all smallness conditions explicit. -/
theorem finitePassageTime_cgf_centered {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (a : ℝ) (ha : |a| ≤ rate/4)
    (hq : (16*(2 : ℝ)^shape/rate^2)*a^2*R ≤ 1/2) :
    cgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) a ≤
      a*(∫ v, finitePassageTime p q R v ∂finiteGammaMeasure shape rate) +
      4*((16*(2 : ℝ)^shape/rate^2)*a^2*R) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by dsimp [P, finiteGammaMeasure]; infer_instance
  let F := finitePassageTime p q R
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd : HasDerivAt (cgf F P) (∫ v, F v ∂P) 0 :=
    finitePassageTime_hasDerivAt_cgf_zero hs hr p q R hR
  have hb := dyadic_derivative_bound (cgf F P) a (∫ v, F v ∂P) (2*(B*a^2*R))
    (by positivity) (cgf_zero (X := F) (μ := P)) hd (fun n => ?_)
  · convert hb using 1; ring
  have hn0 : 0 ≤ (1/2 : ℝ)^n := by positivity
  have hn1 : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have han : |a*(1/2 : ℝ)^n| ≤ rate/4 := by
    rw [abs_mul, abs_of_nonneg hn0]
    calc
      _ ≤ |a| *1 := mul_le_mul_of_nonneg_left hn1 (abs_nonneg a)
      _ ≤ _ := by simpa using ha
  have hqn : B*(a*(1/2 : ℝ)^n)^2*R ≤ 1/2 := by
    have hsquare : ((1/2 : ℝ)^n)^2 ≤ 1 := by nlinarith
    calc
      _ = (B*a^2*R)*((1/2 : ℝ)^n)^2 := by ring
      _ ≤ (B*a^2*R)*1 := mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ ≤ _ := by simpa only [mul_one] using hq
  have hrec := finitePassageTime_cgf_recursion hs hr p q R hR
    (a*(1/2 : ℝ)^n) han hqn
  have he : a*(1/2 : ℝ)^n/2 = a*(1/2 : ℝ)^(n+1) := by rw [pow_succ]; ring
  rw [he] at hrec
  convert hrec using 1; ring

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalCenteredConcentration
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real
open scoped ENNReal

/-- For every real threshold t, finite local fluctuations have a centered
sqrt(R)-scale exponential tail. The scale is positive for every rate>0. -/
theorem finitePassageTime_centered_exponential {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (t : ℝ) :
    (finiteGammaMeasure shape rate)
      {v | t*sqrt R ≤ |finitePassageTime p q R v -
        ∫ w, finitePassageTime p q R w ∂finiteGammaMeasure shape rate|} ≤
      2*ENNReal.ofReal (exp (1-concentrationKappa shape rate*t)) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by dsimp [P, finiteGammaMeasure]; infer_instance
  let F := finitePassageTime p q R
  let M := ∫ v, F v ∂P
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  let k := concentrationKappa shape rate
  let a : ℝ := k/sqrt R
  obtain ⟨hk, hkr, hkquarter, hkB⟩ := concentrationKappa_bounds (shape := shape) hr
  have hkB' : B*k^2 ≤ 1/16 := hkB
  have hpos : 0 < R := lt_of_le_of_lt (Nat.zero_le _) hR
  have hsqrt : 0 < sqrt R := sqrt_pos.mpr (by exact_mod_cast hpos)
  have hsqrt1 : 1 ≤ sqrt R := by
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hpos
    nlinarith [sq_sqrt (Nat.cast_nonneg R), sqrt_nonneg (R : ℝ)]
  have ha : 0 < a := div_pos hk hsqrt
  have hak : a ≤ k := by
    apply (div_le_iff₀ hsqrt).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsqrt1 hk.le
  have har : a ≤ rate/4 := hak.trans hkr
  have has : a*sqrt R = k := by dsimp [a]; field_simp [hsqrt.ne']
  have hscale : B*a^2*R = B*k^2 := by
    calc
      _ = B*(a*sqrt R)^2 := by rw [mul_pow, sq_sqrt (Nat.cast_nonneg R)]; ring
      _ = _ := by rw [has]
  have hsmall : B*a^2*R ≤ 1/2 := by
    rw [hscale]
    linarith
  have hc := finitePassageTime_cgf_centered hs hr p q R hR a
    (by rwa [abs_of_pos ha]) hsmall
  have hcn := finitePassageTime_cgf_centered hs hr p q R hR (-a)
    (by simpa only [abs_neg, abs_of_pos ha] using har)
    (by simpa only [neg_sq] using hsmall)
  have hu : P.real {v | M+t*sqrt R ≤ F v} ≤ exp (1-k*t) := by
    apply (measure_ge_le_exp_cgf (μ := P) (X := F) (M+t*sqrt R) ha.le
      (integrable_finitePassageTime_exp hs hr p q R hR a (by linarith))).trans
    apply exp_le_exp.mpr
    change cgf F P a ≤ a*M+4*(B*a^2*R) at hc
    calc
      _ ≤ -a*(M+t*sqrt R)+(a*M+4*(B*a^2*R)) := add_le_add le_rfl hc
      _ = 4*(B*a^2*R)-t*(a*sqrt R) := by ring
      _ ≤ 1-k*t := by rw [hscale, has]; nlinarith
  have hl : P.real {v | F v ≤ M-t*sqrt R} ≤ exp (1-k*t) := by
    apply (measure_le_le_exp_cgf (μ := P) (X := F) (M-t*sqrt R)
      (neg_nonpos.mpr ha.le)
      (integrable_finitePassageTime_exp hs hr p q R hR (-a) (by linarith))).trans
    apply exp_le_exp.mpr
    change cgf F P (-a) ≤ (-a)*M+4*(B*(-a)^2*R) at hcn
    calc
      _ ≤ -(-a)*(M-t*sqrt R)+((-a)*M+4*(B*(-a)^2*R)) := add_le_add le_rfl hcn
      _ = 4*(B*a^2*R)-t*(a*sqrt R) := by ring
      _ ≤ 1-k*t := by rw [hscale, has]; nlinarith
  have hu' : P {v | M+t*sqrt R ≤ F v} ≤ ENNReal.ofReal (exp (1-k*t)) := by
    have hb := ENNReal.ofReal_le_ofReal hu
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hb
  have hl' : P {v | F v ≤ M-t*sqrt R} ≤ ENNReal.ofReal (exp (1-k*t)) := by
    have hb := ENNReal.ofReal_le_ofReal hl
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hb
  have hsub : {v | t*sqrt R ≤ |F v-M|} ⊆
      {v | M+t*sqrt R ≤ F v} ∪ {v | F v ≤ M-t*sqrt R} := by
    intro v hv
    change t*sqrt R ≤ |F v-M| at hv
    rcases le_total M (F v) with h | h
    · left
      change M+t*sqrt R ≤ F v
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hv
      linarith
    · right
      change F v ≤ M-t*sqrt R
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hv
      linarith
  change P {v | t*sqrt R ≤ |F v-M|} ≤ 2*ENNReal.ofReal (exp (1-k*t))
  apply (measure_mono hsub).trans
  apply (measure_union_le _ _).trans
  simpa only [two_mul] using add_le_add hu' hl'

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalLawTransfer
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Real
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma GammaEnvironment.local_restriction_law
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ) :
    P.map (fun ω (e : ↥(FiniteLocal.localEdges p q R)) => τ e ω) =
      finiteGammaMeasure (ι := ↥(FiniteLocal.localEdges p q R)) shape rate :=
  h.finiteJointLaw (FiniteLocal.localEdges p q R)

/-- The finite-coordinate passage time has the same expectation as its realization
in a Gamma environment. -/
theorem GammaEnvironment.integral_localPassageTime
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    (∫ ω, FiniteLocal.passageTime (fun e => τ e ω) p q R ∂P) =
      ∫ v, FiniteLocal.finitePassageTime p q R v ∂finiteGammaMeasure shape rate := by
  have hi := h.integral_finiteJoint (FiniteLocal.localEdges p q R)
    (FiniteLocal.finitePassageTime p q R)
    (FiniteLocal.measurable_finitePassageTime p q R hR)
  have hF : (fun ω => FiniteLocal.finitePassageTime p q R
      (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω)) =
      (fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R) := by
    funext ω
    exact FiniteLocal.finitePassageTime_restrict p q R (fun e => τ e ω)
  change (∫ ω, FiniteLocal.finitePassageTime p q R
    (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω) ∂P) = _ at hi
  rw [hF] at hi
  exact hi

/-- Local passage times in a Gamma environment are integrable. -/
theorem GammaEnvironment.integrable_localPassageTime
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    Integrable (fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R) P := by
  have hpos : ∀ᵐ v ∂finiteGammaMeasure (ι := ↥(FiniteLocal.localEdges p q R)) shape rate,
      0 ≤ FiniteLocal.finitePassageTime p q R v :=
    (finiteGammaMeasure_ae_nonneg hs hr).mono fun v hv =>
      FiniteLocal.finitePassageTime_nonneg p q R hR v hv
  have hi := (hasDerivAt_integral_exp_zero
    (FiniteLocal.measurable_finitePassageTime p q R hR) hpos
    (show 0 < rate/2 by positivity)
    (FiniteLocal.integrable_finitePassageTime_exp hs hr p q R hR (rate/2) le_rfl)).1
  rw [← h.local_restriction_law p q R] at hi
  have hc := hi.comp_measurable (Measurable.of_eval (fun e => h.measurable e))
  have hF : (fun ω => FiniteLocal.finitePassageTime p q R
      (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω)) =
      (fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R) := by
    funext ω
    exact FiniteLocal.finitePassageTime_restrict p q R (fun e => τ e ω)
  change Integrable (fun ω => FiniteLocal.finitePassageTime p q R
    (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω)) P at hc
  rw [hF] at hc
  exact hc

/-- Centered local passage times have exponential tails at scale `sqrt R`,
for every real threshold. -/
theorem GammaEnvironment.localPassageTime_centered_exponential
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) (t : ℝ) :
    P {ω | t*sqrt R ≤ |FiniteLocal.passageTime (fun e => τ e ω) p q R -
      ∫ η, FiniteLocal.passageTime (fun e => τ e η) p q R ∂P|} ≤
      2*ENNReal.ofReal (exp (1-FiniteLocal.concentrationKappa shape rate*t)) := by
  rw [h.integral_localPassageTime p q R hR]
  let A : Set (FiniteLocal.Coordinates p q R) :=
    {v | t*sqrt R ≤ |FiniteLocal.finitePassageTime p q R v -
      ∫ w, FiniteLocal.finitePassageTime p q R w ∂finiteGammaMeasure shape rate|}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    (continuous_abs.measurable.comp
      ((FiniteLocal.measurable_finitePassageTime p q R hR).sub measurable_const))
  have hm := Measure.map_apply (μ := P)
    (Measurable.of_eval (fun e : ↥(FiniteLocal.localEdges p q R) => h.measurable e)) hA
  rw [h.local_restriction_law p q R] at hm
  have he : P {ω | t*sqrt R ≤ |FiniteLocal.passageTime (fun e => τ e ω) p q R -
      ∫ w, FiniteLocal.finitePassageTime p q R w ∂finiteGammaMeasure shape rate|} =
      (finiteGammaMeasure shape rate) A := by
    rw [hm]
    congr 1
    ext ω
    change (t*sqrt R ≤ |FiniteLocal.passageTime (fun e => τ e ω) p q R -
      ∫ w, FiniteLocal.finitePassageTime p q R w ∂finiteGammaMeasure shape rate|) ↔
      (t*sqrt R ≤ |FiniteLocal.finitePassageTime p q R
        (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω) -
      ∫ w, FiniteLocal.finitePassageTime p q R w ∂finiteGammaMeasure shape rate|)
    rw [show FiniteLocal.finitePassageTime p q R
      (fun e : ↥(FiniteLocal.localEdges p q R) => τ e ω) =
        FiniteLocal.passageTime (fun e => τ e ω) p q R from
      FiniteLocal.finitePassageTime_restrict p q R (fun e => τ e ω)]
  rw [he]
  exact FiniteLocal.finitePassageTime_centered_exponential hs hr p q R hR t

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalGlobalEquality
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP.FiniteLocal
open PlanarFPP

lemma localization_trace_take (p : Vertex) (ds : List Step) (n : ℕ) :
    trace p (ds.take n) = (trace p ds).take n := by
  induction n generalizing p ds with
  | zero => simp [trace]
  | succ n ih =>
      cases ds with
      | nil => simp [trace]
      | cons d ds => simp [trace, ih]

lemma localization_prefix_cost_le (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) (n : ℕ) :
    pathCost w p (ds.take n) ≤ pathCost w p ds := by
  calc
    _ ≤ pathCost w p (ds.take n) +
        pathCost w (p + displacement (ds.take n)) (ds.drop n) :=
      le_add_of_nonneg_right (pathCost_nonneg hw _ _)
    _ = pathCost w p ds := by
      rw [← pathCost_append, List.take_append_drop]

/-- If no trail of length `R` has cost at most `B`, every trail with cost at most
`B` has fewer than `R` steps. -/
lemma trail_short_of_no_cheap_prefix (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (R : ℕ) (B : ℝ)
    (hno : ¬ ∃ es : List Step, es.length = R ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ B)
    (ds : List Step) (hn : ((trace p ds).map traversalEdge).Nodup)
    (hc : pathCost w p ds ≤ B) : ds.length < R := by
  by_contra hshort
  have hR : R ≤ ds.length := Nat.le_of_not_gt hshort
  apply hno
  refine ⟨ds.take R, ?_, ?_, (localization_prefix_cost_le w hw p ds R).trans hc⟩
  · rw [List.length_take, Nat.min_eq_left hR]
  · rw [localization_trace_take]
    exact hn.sublist ((List.take_sublist R (trace p ds)).map traversalEdge)

/-- Near-optimal paths belong to the finite local family when some endpoint path
has cost below `B` and no trail of length `R` has cost at most `B`. -/
theorem exists_local_near_optimal_of_no_cheap_trail
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p q : Vertex) (R : ℕ) (B : ℝ)
    (hpath : ∃ ds : List Step, p + displacement ds = q ∧ pathCost w p ds < B)
    (hno : ¬ ∃ es : List Step, es.length = R ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ds ∈ candidates p q R,
      pathCost w p ds < PlanarFPP.passageTime w p q + ε := by
  obtain ⟨qs, hq, hqcost⟩ := hpath
  have hgap : PlanarFPP.passageTime w p q < B :=
    (PlanarFPP.passageTime_le_cost w hw p q qs hq).trans_lt hqcost
  let δ := min ε ((B - PlanarFPP.passageTime w p q) / 2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  obtain ⟨ds, hend, hn, _hmin, hc⟩ :=
    GammaFPP.LoopErase.exists_near_optimal_simple_path w hw p q δ hδ
  have hδε : δ ≤ ε := min_le_left _ _
  have hδgap : δ ≤ (B - PlanarFPP.passageTime w p q) / 2 := min_le_right _ _
  have hcB : pathCost w p ds ≤ B := by linarith
  have hlen := trail_short_of_no_cheap_prefix w hw p R B hno ds hn hcB
  exact ⟨ds, (mem_candidates p q R ds).mpr ⟨hend, hn, hlen⟩, by linarith⟩

/-- The finite local minimum equals the unrestricted passage time when no trail
of length `R` has cost at most the comparison threshold. -/
theorem passageTime_eq_unrestricted_of_no_cheap_trail
    (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e) (p q : Vertex) (R : ℕ) (B : ℝ)
    (hR : latticeDistance p q < R)
    (hpath : ∃ ds : List Step, p + displacement ds = q ∧ pathCost w p ds < B)
    (hno : ¬ ∃ es : List Step, es.length = R ∧
      ((trace p es).map traversalEdge).Nodup ∧ pathCost w p es ≤ B) :
    passageTime w p q R = PlanarFPP.passageTime w p q := by
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨ds, hds, hc⟩ :=
      exists_local_near_optimal_of_no_cheap_trail w hw p q R B hpath hno ε hε
    exact (passageTime_le_candidate w p q R ds hds).trans_lt hc
  · exact unrestricted_passageTime_le w hw p q R hR

end GammaFPP.FiniteLocal

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalizationProbability
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma GammaEnvironment.measurableSet_localization_error
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    MeasurableSet {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
      PlanarFPP.passageTime (fun e => τ e ω) p q} := by
  have hl : Measurable (fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R) :=
    (FiniteLocal.measurable_passageTime p q R hR).comp
      (Measurable.of_eval h.measurable)
  exact (measurableSet_eq_fun hl (h.measurable_passageTime p q)).compl

theorem GammaEnvironment.localization_error_probability_real
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    P.real {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
      PlanarFPP.passageTime (fun e => τ e ω) p q} ≤
      (1 / 2 : ℝ)^R + 2 * Real.exp (-(rate / 4) *
        (cheapSlope shape rate * (R : ℝ) -
          coordinateAllowance shape rate * (latticeDistance p q : ℝ))) := by
  let := h.probability
  let B := cheapSlope shape rate * (R : ℝ)
  let A : Set Ω := {ω | ∃ ds : List Step, ds.length = R ∧
    ((trace p ds).map traversalEdge).Nodup ∧ pathCost (fun e => τ e ω) p ds ≤ B}
  let C : Set Ω := {ω | B ≤ pathCost (fun e => τ e ω) p (coordinatePath p q)}
  have hsub : {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
      PlanarFPP.passageTime (fun e => τ e ω) p q} ≤ᵐ[P] (A ∪ C : Set Ω) := by
    filter_upwards [h.ae_positive_edges] with ω hpos herror
    by_cases hA : ω ∈ A
    · exact Or.inl hA
    · by_cases hC : ω ∈ C
      · exact Or.inr hC
      · exfalso
        have hcoord : pathCost (fun e => τ e ω) p (coordinatePath p q) < B :=
          lt_of_not_ge hC
        apply herror
        exact FiniteLocal.passageTime_eq_unrestricted_of_no_cheap_trail
          (fun e => τ e ω) (fun e => (hpos e).le) p q R B hR
          ⟨coordinatePath p q, coordinatePath_endpoint p q, hcoord⟩ hA
  have hA : P.real A ≤ (1 / 2 : ℝ)^R :=
    h.cheap_fixed_length_decay_real hs hr p R
  have hC : P.real C ≤ 2 * Real.exp (-(rate / 4) *
      (B - coordinateAllowance shape rate * (latticeDistance p q : ℝ))) := by
    have hc := h.costly_coordinatePath_probability_real hs hr p q
      (B - coordinateAllowance shape rate * (latticeDistance p q : ℝ))
    have he : coordinateAllowance shape rate * (latticeDistance p q : ℝ) +
        (B - coordinateAllowance shape rate * (latticeDistance p q : ℝ)) = B := by ring
    rw [he] at hc
    exact hc
  calc
    _ ≤ P.real (A ∪ C) :=
      ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
    _ ≤ P.real A + P.real C := measureReal_union_le A C
    _ ≤ _ := add_le_add hA hC

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GlobalCenteredConcentration
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Real
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Comparing two observables and their centers bounds the probability of a
centered deviation. The estimate holds for arbitrary measures. -/
lemma centered_event_comparison (P : Measure Ω) (X Y : Ω → ℝ)
    (a b s d : ℝ) (hd : |b-a| ≤ d) :
    P {ω | s+d ≤ |X ω-a|} ≤
      P {ω | s ≤ |Y ω-b|} + P {ω | Y ω ≠ X ω} := by
  have hsub : {ω | s+d ≤ |X ω-a|} ⊆
      {ω | s ≤ |Y ω-b|} ∪ {ω | Y ω ≠ X ω} := by
    intro ω hω
    by_cases he : Y ω = X ω
    · left
      change s ≤ |Y ω-b|
      have htri : |X ω-a| ≤ |Y ω-b| + |b-a| := by
        rw [← he]
        simpa only [sub_add_sub_cancel] using abs_add_le (Y ω-b) (b-a)
      change s+d ≤ |X ω-a| at hω
      linarith
    · exact Or.inr he
  exact (measure_mono hsub).trans (measure_union_le _ _)

variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The localization error and a bound on the deterministic mean shift control
unrestricted centered deviations. The case `p = q` is included when `0 < R`. -/
theorem GammaEnvironment.passageTime_centered_exponential_of_mean_gap
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R)
    (b : ℝ)
    (hb : |(∫ ω, FiniteLocal.passageTime (fun e => τ e ω) p q R ∂P) -
      ∫ ω, PlanarFPP.passageTime (fun e => τ e ω) p q ∂P| ≤ b)
    (t : ℝ) :
    P.real {ω | t*sqrt R+b ≤ |PlanarFPP.passageTime (fun e => τ e ω) p q -
      ∫ η, PlanarFPP.passageTime (fun e => τ e η) p q ∂P|} ≤
      2*exp (1-FiniteLocal.concentrationKappa shape rate*t) +
      ((1/2 : ℝ)^R + 2*exp (-(rate/4) *
        (cheapSlope shape rate*(R : ℝ) -
          coordinateAllowance shape rate*(latticeDistance p q : ℝ)))) := by
  let : IsProbabilityMeasure P := h.probability
  let X : Ω → ℝ := fun ω => PlanarFPP.passageTime (fun e => τ e ω) p q
  let Y : Ω → ℝ := fun ω => FiniteLocal.passageTime (fun e => τ e ω) p q R
  have hc := centered_event_comparison P X Y (∫ ω, X ω ∂P) (∫ ω, Y ω ∂P)
    (t*sqrt R) b hb
  have hlocal := h.localPassageTime_centered_exponential hs hr p q R hR t
  have hlocalReal : P.real {ω | t*sqrt R ≤ |Y ω-∫ η, Y η ∂P|} ≤
      2*exp (1-FiniteLocal.concentrationKappa shape rate*t) := by
    have hfin : (2 : ℝ≥0∞)*ENNReal.ofReal
        (exp (1-FiniteLocal.concentrationKappa shape rate*t)) ≠ ∞ := by
      exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
    have hh := ENNReal.toReal_mono hfin hlocal
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (exp_pos _).le] using hh
  have hsumfin : P {ω | t*sqrt R ≤ |Y ω-∫ η, Y η ∂P|} +
      P {ω | Y ω ≠ X ω} ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  have hreal := ENNReal.toReal_mono hsumfin hc
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hreal
  exact hreal.trans (add_le_add hlocalReal
    (h.localization_error_probability_real hs hr p q R hR))

/-- A quantitative separation of the distance and localization scales bounds
the difference between localized and unrestricted means. -/
lemma localization_exponential_scale_separation
    {shape rate d r : ℝ} (hr : 0 < rate)
    (hscale : 2 * coordinateAllowance shape rate * d ≤ cheapSlope shape rate * r) :
    exp (-(rate/4) * (cheapSlope shape rate*r-coordinateAllowance shape rate*d)) ≤
      exp (-(rate*cheapSlope shape rate/8)*r) := by
  apply exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hscale hr.le
  nlinarith

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalCoordinateDomination
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open PlanarFPP

lemma coordinatePath_length_eq_distance (p q : Vertex) :
    (coordinatePath p q).length = latticeDistance p q := by
  have hh (a : ℤ) : (horizontal a).length = a.natAbs := by
    unfold horizontal
    split_ifs <;> simp only [List.length_replicate] <;> omega
  have hv (a : ℤ) : (vertical a).length = a.natAbs := by
    unfold vertical
    split_ifs <;> simp only [List.length_replicate] <;> omega
  simp [coordinatePath, latticeDistance, hh, hv]

namespace LoopErase
lemma steps_companion_walk_length (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    ∃ walk : LoopGraph.lattice.Walk p (p + displacement ds),
      LoopGraph.pathCost (companionWeights w) walk = pathCost w p ds ∧
      walk.length = ds.length := by
  induction ds generalizing p with
  | nil =>
      refine ⟨(SimpleGraph.Walk.nil : LoopGraph.lattice.Walk p p).copy rfl (by simp), ?_, ?_⟩
      · rw [companion_pathCost_copy]; rfl
      · rw [SimpleGraph.Walk.length_copy]
        rfl
  | cons d ds ih =>
      obtain ⟨walk, hw, hl⟩ := ih (p + d.delta)
      have he : (p + d.delta) + displacement ds = p + displacement (d :: ds) := by
        simp [add_assoc]
      refine ⟨(SimpleGraph.Walk.cons (companion_adj_step p d) walk).copy rfl he, ?_, ?_⟩
      · simp only [companion_pathCost_copy, LoopGraph.pathCost_cons, LoopGraph.edgeCost,
          pathCost, hw]
        rw [← companionEdge_step, companionWeights_edge]
      · simp [hl]

lemma erase_path_loops_length (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) :
    ∃ es : List Step, p + displacement es = p + displacement ds ∧
      ((trace p es).map traversalEdge).Nodup ∧ es.length ≤ ds.length ∧
      pathCost w p es ≤ pathCost w p ds := by
  obtain ⟨walk, hc, hl⟩ := steps_companion_walk_length w p ds
  obtain ⟨es, he, hcost, hedges⟩ := companion_walk_steps_edges w walk.bypass
  have hn := walk.bypass_isPath.isTrail.edges_nodup
  rw [← hedges] at hn
  have hn' : (((trace p es).map traversalEdge).map (fun e => (companionEdge e).val)).Nodup := by
    simpa only [List.map_map, Function.comp_def] using hn
  have hlen : es.length = walk.bypass.length := by
    have hh := congrArg List.length hedges
    have htrace : (trace p es).length = es.length := by
      simpa only [List.length_map] using trace_edge_length p es
    simpa only [List.length_map, SimpleGraph.Walk.length_edges, htrace] using hh
  refine ⟨es, he, List.Nodup.of_map _ hn', ?_, ?_⟩
  · rw [hlen, ← hl]
    exact walk.length_bypass_le_length
  · rw [hcost, ← hc]
    exact LoopGraph.bypass_cost_le (companionWeights w) (fun e => hw _) walk
end LoopErase

lemma FiniteLocal.passageTime_le_coordinatePath (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    FiniteLocal.passageTime w p q R ≤ pathCost w p (coordinatePath p q) := by
  obtain ⟨es, he, hn, hl, hc⟩ := LoopErase.erase_path_loops_length w hw p (coordinatePath p q)
  have hend : p + displacement es = q := he.trans (coordinatePath_endpoint p q)
  have hlen : es.length < R := hl.trans_lt (by rwa [coordinatePath_length_eq_distance])
  exact (FiniteLocal.passageTime_le_candidate w p q R es
    ((FiniteLocal.mem_candidates p q R es).mpr ⟨hend, hn, hlen⟩)).trans hc
end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_PathSecondMoment
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Finset
open scoped BigOperators

lemma square_le_gamma_exp (rate x : ℝ) (hr : 0 < rate) (hx : 0 ≤ x) :
    x^2 ≤ (8 / rate^2) * Real.exp ((rate/2)*x) := by
  have ht := Real.pow_div_factorial_le_exp ((rate/2)*x) (by positivity) 2
  norm_num at ht
  have ha : x^2 ≤ (8 * Real.exp ((rate/2)*x)) / rate^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith
  convert ha using 1
  ring

lemma gamma_integrable_square_bound (shape rate : ℝ) (hs : 0 < shape) (hr : 0 < rate) :
    Integrable (fun x : ℝ => x^2) (gammaMeasure shape rate) := by
  apply ((gamma_integrable_exp hs hr (show rate/2 < rate by linarith)).const_mul
    (8 / rate^2)).mono' (by fun_prop)
  filter_upwards [gamma_ae_pos shape rate] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  exact square_le_gamma_exp rate x hr hx.le

lemma gamma_integral_square_le (shape rate : ℝ) (hs : 0 < shape) (hr : 0 < rate) :
    (∫ x : ℝ, x^2 ∂gammaMeasure shape rate) ≤ pathSecondMomentConstant shape rate := by
  have hi := gamma_integrable_exp hs hr (show rate/2 < rate by linarith)
  have hb := integral_mono_ae (gamma_integrable_square_bound shape rate hs hr)
    (hi.const_mul (8 / rate^2)) (by
      filter_upwards [gamma_ae_pos shape rate] with x hx
      exact square_le_gamma_exp rate x hr hx.le)
  rw [integral_const_mul, gamma_integral_exp hs hr (show rate/2 < rate by linarith)] at hb
  have he : rate / (rate - rate/2) = 2 := by
    have hd : rate - rate/2 ≠ 0 := by linarith
    field_simp [hd]
    ring
  rw [he] at hb
  calc
    _ ≤ (8 / rate^2) * (2 : ℝ)^shape := hb
    _ = pathSecondMomentConstant shape rate := by
      unfold pathSecondMomentConstant
      ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

lemma GammaEnvironment.integrable_edge_square
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) (e : Edge) :
    Integrable (fun ω => (τ e ω)^2) P := by
  have hi : Integrable (fun x : ℝ => x^2) (Measure.map (τ e) P) := by
    rw [h.marginal e]
    exact gamma_integrable_square_bound shape rate hs hr
  simpa only [Function.comp_def] using hi.comp_aemeasurable (h.measurable e).aemeasurable

lemma GammaEnvironment.integral_edge_square_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) (e : Edge) :
    (∫ ω, (τ e ω)^2 ∂P) ≤ pathSecondMomentConstant shape rate := by
  have he := integral_map (μ := P) (h.measurable e).aemeasurable
    (f := fun x : ℝ => x^2) (by fun_prop)
  rw [h.marginal e] at he
  rw [← he]
  exact gamma_integral_square_le shape rate hs hr

lemma GammaEnvironment.pathCost_memLp_two
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (ds : List Step) :
    MemLp (fun ω => pathCost (fun e => τ e ω) p ds) 2 P := by
  let := h.probability
  induction ds generalizing p with
  | nil => exact memLp_const 0
  | cons d ds ih =>
      have he : MemLp (τ (d.edge p)) 2 P :=
        (memLp_two_iff_integrable_sq (h.measurable _).aestronglyMeasurable).mpr
          (h.integrable_edge_square hs hr _)
      exact he.add (ih (p + d.delta))

/-- The path cost is a sum over ordered traversal positions, including repeated edges. -/
lemma pathCost_eq_indexed_trace (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    pathCost w p ds =
      ∑ i : Fin ((trace p ds).map traversalEdge).length,
        w (((trace p ds).map traversalEdge).get i) := by
  rw [pathCost_trace_edge_sum]
  generalize ((trace p ds).map traversalEdge) = es
  conv_lhs => rw [← List.ofFn_get es]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]

/-- Finite Cauchy–Schwarz bounds the square of a sum for every real assignment. -/
lemma pathCost_square_le_indexed (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    (pathCost w p ds)^2 ≤ (ds.length : ℝ) *
      ∑ i : Fin ((trace p ds).map traversalEdge).length,
        (w (((trace p ds).map traversalEdge).get i))^2 := by
  rw [pathCost_eq_indexed_trace]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Fin ((trace p ds).map traversalEdge).length))
    (fun _ => (1 : ℝ)) (fun i => w (((trace p ds).map traversalEdge).get i))
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, trace_edge_length] using hc

/-- A polynomial second-moment bound for every deterministic finite step list. -/
theorem GammaEnvironment.pathCost_second_moment_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p : Vertex) (ds : List Step) :
    (∫ ω, (pathCost (fun e => τ e ω) p ds)^2 ∂P) ≤
      pathSecondMomentConstant shape rate * (ds.length : ℝ)^2 := by
  let es := (trace p ds).map traversalEdge
  have hi (i : Fin es.length) : Integrable (fun ω => (τ (es.get i) ω)^2) P :=
    h.integrable_edge_square hs hr _
  have hsum : Integrable (fun ω => ∑ i : Fin es.length, (τ (es.get i) ω)^2) P :=
    integrable_finsetSum _ (fun i _ => hi i)
  have hb := integral_mono_ae (h.pathCost_memLp_two hs hr p ds).integrable_sq
    (hsum.const_mul (ds.length : ℝ))
    (Filter.Eventually.of_forall (fun ω => pathCost_square_le_indexed (fun e => τ e ω) p ds))
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)] at hb
  have he : (∑ i : Fin es.length, ∫ ω, (τ (es.get i) ω)^2 ∂P) ≤
      (ds.length : ℝ) * pathSecondMomentConstant shape rate := by
    calc
      _ ≤ ∑ _i : Fin es.length, pathSecondMomentConstant shape rate :=
        Finset.sum_le_sum (fun i _ => h.integral_edge_square_le hs hr _)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show es.length = ds.length from trace_edge_length p ds]
  calc
    _ ≤ (ds.length : ℝ) * (∑ i : Fin es.length, ∫ ω, (τ (es.get i) ω)^2 ∂P) := hb
    _ ≤ (ds.length : ℝ) * ((ds.length : ℝ) * pathSecondMomentConstant shape rate) :=
      mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
    _ = _ := by ring

/-- A polynomial second-moment bound for the deterministic coordinate path. -/
theorem GammaEnvironment.coordinatePath_second_moment_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) :
    (∫ ω, (pathCost (fun e => τ e ω) p (coordinatePath p q))^2 ∂P) ≤
      pathSecondMomentConstant shape rate * ((coordinatePath p q).length : ℝ)^2 :=
  h.pathCost_second_moment_le hs hr p (coordinatePath p q)

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_LocalMeanGap
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear _root_.OAI.PlanarFPP.instFintypeStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP

/-- Cauchy–Schwarz bounds an integral restricted to a measurable event. -/
lemma integral_indicator_le_sqrt_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Ω → ℝ} {E : Set Ω} (hE : MeasurableSet E)
    (hS : MemLp S 2 P) (hpos : 0 ≤ᵐ[P] S) :
    (∫ ω, E.indicator S ω ∂P) ≤
      Real.sqrt (∫ ω, (S ω)^2 ∂P) * Real.sqrt (P.real E) := by
  have hI : MemLp (E.indicator (fun _ : Ω => (1 : ℝ))) 2 P :=
    (memLp_const (1 : ℝ)).indicator hE
  have hIpos : 0 ≤ᵐ[P] (E.indicator (fun _ : Ω => (1 : ℝ))) := by
    filter_upwards [] with ω
    by_cases he : ω ∈ E <;> simp [he]
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    hpos hIpos (by simpa using hS) (by simpa using hI)
  have hi : (∫ ω, (E.indicator (fun _ : Ω => (1 : ℝ)) ω)^(2 : ℝ) ∂P) = P.real E := by
    have heq : (fun ω => (E.indicator (fun _ : Ω => (1 : ℝ)) ω)^(2 : ℝ)) =
        E.indicator (fun _ : Ω => (1 : ℝ)) := by
      funext ω
      by_cases he : ω ∈ E <;> simp [he]
    rw [heq, integral_indicator_const (1 : ℝ) hE]
    simp
  have hprod : (fun ω => S ω * E.indicator (fun _ : Ω => (1 : ℝ)) ω) =
      E.indicator S := by
    funext ω
    by_cases he : ω ∈ E <;> simp [he]
  rw [hi, hprod] at hc
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using hc

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- The gap between local and unrestricted passage times is nonnegative and
bounded by the coordinate-path cost on the event where they differ. -/
theorem GammaEnvironment.ae_localPassageTime_gap_indicator
    (h : GammaEnvironment shape rate P τ) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    ∀ᵐ ω ∂P,
      0 ≤ FiniteLocal.passageTime (fun e => τ e ω) p q R -
        PlanarFPP.passageTime (fun e => τ e ω) p q ∧
      FiniteLocal.passageTime (fun e => τ e ω) p q R -
        PlanarFPP.passageTime (fun e => τ e ω) p q ≤
      {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
        PlanarFPP.passageTime (fun e => τ e ω) p q}.indicator
          (fun ω => pathCost (fun e => τ e ω) p (coordinatePath p q)) ω := by
  filter_upwards [h.ae_positive_edges] with ω hpos
  have hw : ∀ e, 0 ≤ τ e ω := fun e => (hpos e).le
  have hlo := FiniteLocal.unrestricted_passageTime_le (fun e => τ e ω) hw p q R hR
  have hup := FiniteLocal.passageTime_le_coordinatePath (fun e => τ e ω) hw p q R hR
  have ht := PlanarFPP.passageTime_nonneg (fun e => τ e ω) hw p q
  refine ⟨sub_nonneg.mpr hlo, ?_⟩
  by_cases he : FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
      PlanarFPP.passageTime (fun e => τ e ω) p q
  · have hmem : ω ∈ {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
        PlanarFPP.passageTime (fun e => τ e ω) p q} := he
    rw [Set.indicator_of_mem hmem]
    linarith
  · have heq := not_ne_iff.mp he
    simp [heq]

/-- The difference of the local and unrestricted mean passage times is controlled
by the coordinate-path second moment and the localization probability. -/
theorem GammaEnvironment.localPassageTime_mean_gap_le
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) :
    0 ≤ (∫ ω, FiniteLocal.passageTime (fun e => τ e ω) p q R ∂P) -
      (∫ ω, PlanarFPP.passageTime (fun e => τ e ω) p q ∂P) ∧
    (∫ ω, FiniteLocal.passageTime (fun e => τ e ω) p q R ∂P) -
      (∫ ω, PlanarFPP.passageTime (fun e => τ e ω) p q ∂P) ≤
      Real.sqrt (pathSecondMomentConstant shape rate * (latticeDistance p q : ℝ)^2) *
      Real.sqrt ((1 / 2 : ℝ)^R + 2 * Real.exp (-(rate / 4) *
        (cheapSlope shape rate * (R : ℝ) -
          coordinateAllowance shape rate * (latticeDistance p q : ℝ)))) := by
  let := h.probability
  let E : Set Ω := {ω | FiniteLocal.passageTime (fun e => τ e ω) p q R ≠
    PlanarFPP.passageTime (fun e => τ e ω) p q}
  let S : Ω → ℝ := fun ω => pathCost (fun e => τ e ω) p (coordinatePath p q)
  have hE : MeasurableSet E := h.measurableSet_localization_error p q R hR
  have hSlp : MemLp S 2 P := h.pathCost_memLp_two hs hr p (coordinatePath p q)
  have hSi : Integrable S P := h.integrable_pathCost hs hr p (coordinatePath p q)
  have hSpos : 0 ≤ᵐ[P] S := by
    filter_upwards [h.ae_positive_edges] with ω hpos
    exact pathCost_nonneg (fun e => (hpos e).le) _ _
  have hLi := h.integrable_localPassageTime hs hr p q R hR
  have hTi := h.integrable_passageTime hs hr p q
  have hgap := h.ae_localPassageTime_gap_indicator p q R hR
  simp only [← integral_sub hLi hTi]
  refine ⟨integral_nonneg_of_ae (hgap.mono fun _ hω => hω.1), ?_⟩
  calc
    _ ≤ ∫ ω, E.indicator S ω ∂P :=
      integral_mono_ae (hLi.sub hTi) (hSi.indicator hE) (hgap.mono fun _ hω => hω.2)
    _ ≤ Real.sqrt (∫ ω, (S ω)^2 ∂P) * Real.sqrt (P.real E) :=
      integral_indicator_le_sqrt_second_moment hE hSlp hSpos
    _ ≤ _ := by
      apply mul_le_mul
      · apply Real.sqrt_le_sqrt
        simpa only [coordinatePath_length_eq_distance] using
          h.coordinatePath_second_moment_le hs hr p q
      · exact Real.sqrt_le_sqrt (h.localization_error_probability_real hs hr p q R hR)
      · exact Real.sqrt_nonneg _
      · exact Real.sqrt_nonneg _
end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_GlobalConcentration
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Real

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Unrestricted centered Gamma passage-time concentration with an explicit
localization allowance and constants depending only on the shape and rate. -/
theorem GammaEnvironment.passageTime_centered_exponential
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (p q : Vertex) (R : ℕ) (hR : latticeDistance p q < R) (t : ℝ) :
    P.real {ω | t*sqrt R + meanLocalizationAllowance shape rate (latticeDistance p q) R ≤
      |PlanarFPP.passageTime (fun e => τ e ω) p q -
        ∫ η, PlanarFPP.passageTime (fun e => τ e η) p q ∂P|} ≤
      2*exp (1-FiniteLocal.concentrationKappa shape rate*t) +
        localizationErrorBound shape rate (latticeDistance p q) R := by
  obtain ⟨hzero, hgap⟩ := h.localPassageTime_mean_gap_le hs hr p q R hR
  have habs : |(∫ η, FiniteLocal.passageTime (fun e => τ e η) p q R ∂P) -
      ∫ η, PlanarFPP.passageTime (fun e => τ e η) p q ∂P| ≤
      meanLocalizationAllowance shape rate (latticeDistance p q) R := by
    rw [abs_of_nonneg hzero]
    exact hgap
  exact h.passageTime_centered_exponential_of_mean_gap hs hr p q R hR _ habs t

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_SequenceSummability
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory Real Filter Topology PlanarFPP

lemma exp_neg_sqrt_le (a m : ℝ) (ha : 0 < a) (hm : 0 < m) :
    exp (-(a*sqrt m)) ≤ (24/a^4)/m^2 := by
  have h := Real.pow_div_factorial_le_exp (a*sqrt m) (by positivity) 4
  have hs := sq_sqrt hm.le
  have he : (a*sqrt m)^4 = a^4*m^2 := by
    rw [mul_pow, show sqrt m^4 = (sqrt m^2)^2 by ring, hs]
  rw [he] at h
  norm_num at h
  rw [exp_neg, ← one_div, div_div]
  apply (div_le_div_iff₀ (exp_pos _) (by positivity)).mpr
  nlinarith

lemma summable_exp_neg_sqrt (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => exp (-(a*sqrt (n+1)))) := by
  have h := ((summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
    (show Function.Injective (fun n : ℕ => n+1) from fun _ _ h => Nat.add_right_cancel h)).mul_left (24/a^4)
  apply h.of_nonneg_of_le (fun n => (exp_pos _).le)
  intro n
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_one_div] using
    exp_neg_sqrt_le a (n+1) ha (by positivity)

lemma localizationDecay_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < localizationDecay shape rate := by
  exact lt_min (log_pos (by norm_num)) (by have := cheapSlope_pos hs hr; positivity)

lemma localizationErrorBound_exp {shape rate : ℝ} (hr : 0 < rate) (d R : ℕ)
    (hscale : 2*coordinateAllowance shape rate*(d : ℝ) ≤ cheapSlope shape rate*(R : ℝ)) :
    localizationErrorBound shape rate d R ≤ 3*exp (-localizationDecay shape rate*R) := by
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hlog : localizationDecay shape rate ≤ log 2 := min_le_left _ _
  have hc : localizationDecay shape rate ≤ rate*cheapSlope shape rate/8 := min_le_right _ _
  have hp : (1/2 : ℝ)^R = exp (-(log 2)*(R : ℝ)) := by
    rw [show -(log 2)*(R : ℝ) = (R : ℝ)*(-log 2) by ring, exp_nat_mul, exp_neg,
      exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  have h₁ : (1/2 : ℝ)^R ≤ exp (-localizationDecay shape rate*R) := by
    rw [hp]
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hlog hR]
  have h₂ := localization_exponential_scale_separation hr hscale
  have h₃ : exp (-(rate*cheapSlope shape rate/8)*(R : ℝ)) ≤
      exp (-localizationDecay shape rate*R) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hR]
  unfold localizationErrorBound
  linarith [h₂.trans h₃]

/-- Choose a natural length multiplier; it may depend on direction and law,
never on sample, time n, or deviation threshold. -/
lemma exists_ray_cutoff {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) (d : ℕ) :
    ∃ L : ℕ, d < L ∧ 2*coordinateAllowance shape rate*(d : ℝ) ≤ cheapSlope shape rate*L := by
  obtain ⟨L,hL⟩ := exists_nat_gt (max (d : ℝ)
    (2*coordinateAllowance shape rate*d/cheapSlope shape rate))
  refine ⟨L, ?_, ?_⟩
  · exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hL)
  · have hc := cheapSlope_pos hs hr
    have hh := lt_of_le_of_lt (le_max_right _ _) hL
    exact ((div_lt_iff₀ hc).mp hh).le.trans_eq (mul_comm _ _)

lemma meanLocalizationAllowance_mul (shape rate : ℝ) (m d R : ℕ) :
    meanLocalizationAllowance shape rate (m*d) R =
      (m : ℝ)*sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2)*
        sqrt (localizationErrorBound shape rate (m*d) R) := by
  unfold meanLocalizationAllowance
  rw [Nat.cast_mul, show pathSecondMomentConstant shape rate*((m : ℝ)*(d : ℝ))^2 =
    (m : ℝ)^2*(pathSecondMomentConstant shape rate*(d : ℝ)^2) by ring,
    sqrt_mul (sq_nonneg _), sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Absolute centered deviations at every positive lattice-ray index are
summable. Zero direction needs no special denominator or positive distance. -/
theorem GammaEnvironment.summable_ray_centered_deviations
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (ε : ℝ) (hε : 0 < ε) :
    Summable (fun n : ℕ => P.real {ω | ε*(n+1 : ℝ) ≤
      |passageTime (fun e => τ e ω) 0 ((n+1) • z) -
        meanPassageSequence P τ z (n+1)|}) := by
  let : IsProbabilityMeasure P := h.probability
  let d := latticeDistance 0 z
  obtain ⟨L,hLd,hLs⟩ := exists_ray_cutoff hs hr d
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le d) hLd
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  let k := localizationDecay shape rate
  have hk : 0 < k := localizationDecay_pos hs hr
  let E : ℕ → ℝ := fun n => localizationErrorBound shape rate ((n+1)*d) (L*(n+1))
  have hEbound (n : ℕ) : E n ≤ 3*exp (-(k*L)*(n+1 : ℝ)) := by
    have hb := localizationErrorBound_exp hr ((n+1)*d) (L*(n+1)) (by
      push_cast
      have hh := mul_le_mul_of_nonneg_right hLs (show (0 : ℝ) ≤ n+1 by positivity)
      nlinarith)
    change localizationErrorBound shape rate ((n+1)*d) (L*(n+1)) ≤ _
    calc
      _ ≤ 3*exp (-localizationDecay shape rate*(L*(n+1) : ℕ)) := hb
      _ = _ := by
        dsimp [k]
        push_cast
        exact congrArg (fun x : ℝ => 3*exp x) (by ring)
  have hgeo : Summable (fun n : ℕ => exp (-(k*L)*(n+1 : ℝ))) := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_exp_nat_mul_iff.mpr (show -(k*(L : ℝ)) < 0 from neg_neg_of_pos (mul_pos hk hLR)))
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hh
  have hEsum : Summable E := (hgeo.mul_left 3).of_nonneg_of_le
    (fun n => by dsimp [E, localizationErrorBound]; positivity) hEbound
  have hEzero : Tendsto E atTop (𝓝 0) := hEsum.tendsto_atTop_zero
  have hsmall : ∀ᶠ n : ℕ in atTop,
      sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2)*sqrt (E n) < ε/2 := by
    have ht := (hEzero.sqrt).const_mul (sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2))
    have ht' : Tendsto (fun n => sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2)*sqrt (E n))
        atTop (𝓝 0) := by simpa using ht
    exact ht'.eventually (gt_mem_nhds (by positivity))
  let a := FiniteLocal.concentrationKappa shape rate*ε/(2*sqrt (L : ℝ))
  have ha : 0 < a := by
    have := (FiniteLocal.concentrationKappa_bounds (shape := shape) hr).1
    dsimp [a]; positivity
  have hsum := ((summable_exp_neg_sqrt a ha).mul_left (2*exp 1)).add hEsum
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [hsmall] with n hn
  have hm : (0 : ℝ) < n+1 := by positivity
  have hrad : latticeDistance 0 ((n+1) • z) < L*(n+1) := by
    rw [latticeDistance_zero_nsmul]
    dsimp [d] at hLd
    nlinarith
  have hal : meanLocalizationAllowance shape rate ((n+1)*d) (L*(n+1)) ≤ ε*(n+1 : ℝ)/2 := by
    rw [meanLocalizationAllowance_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    have hh := mul_le_mul_of_nonneg_left hn.le hm.le
    dsimp [E] at hh
    nlinarith
  let t : ℝ := ε*sqrt (n+1)/(2*sqrt (L : ℝ))
  have ht : t*sqrt (L*(n+1) : ℕ) = ε*(n+1 : ℝ)/2 := by
    dsimp [t]
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, sqrt_mul hLR.le]
    have hne : sqrt (L : ℝ) ≠ 0 := (sqrt_pos.mpr hLR).ne'
    calc
      ε*sqrt (n+1)/(2*sqrt (L : ℝ))*(sqrt (L : ℝ)*sqrt (n+1)) =
          ε*(sqrt (n+1))^2/2 := by field_simp [hne]
      _ = ε*(n+1 : ℝ)/2 := by rw [sq_sqrt hm.le]
  have hb := h.passageTime_centered_exponential hs hr 0 ((n+1) • z)
    (L*(n+1)) hrad t
  rw [latticeDistance_zero_nsmul] at hb
  have hsub : {ω | ε*(n+1 : ℝ) ≤ |passageTime (fun e => τ e ω) 0 ((n+1) • z) -
      meanPassageSequence P τ z (n+1)|} ⊆
      {ω | t*sqrt (L*(n+1) : ℕ)+meanLocalizationAllowance shape rate ((n+1)*d) (L*(n+1)) ≤
      |passageTime (fun e => τ e ω) 0 ((n+1) • z)-
        ∫ η, passageTime (fun e => τ e η) 0 ((n+1) • z) ∂P|} := by
    intro ω hω
    change ε*(n+1 : ℝ) ≤ _ at hω
    change t*sqrt (L*(n+1) : ℕ)+_ ≤ _
    rw [ht]
    change ε*(n+1 : ℝ) ≤ |passageTime (fun e => τ e ω) 0 ((n+1) • z)-
      ∫ η, passageTime (fun e => τ e η) 0 ((n+1) • z) ∂P| at hω
    linarith
  have hprob := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  apply hprob.trans (hb.trans_eq ?_)
  dsimp [E, t, a]
  congr 1
  rw [show 1-FiniteLocal.concentrationKappa shape rate*
      (ε*sqrt (n+1)/(2*sqrt (L : ℝ))) =
      1 + -(FiniteLocal.concentrationKappa shape rate*ε/(2*sqrt (L : ℝ))*sqrt (n+1)) by ring,
    exp_add]
  ring

/-- Normalized centered deviations along a lattice ray have summable
probabilities at every positive tolerance. The event at `n = 0` is empty. -/
theorem GammaEnvironment.normalized_ray_deviations_tsum_ne_top
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (k : ℕ) :
    (∑' n : ℕ, P {ω | 1/((k : ℝ)+1) ≤
      |passageTime (fun e => τ e ω) 0 (n • z)/(n : ℝ) -
        meanPassageSequence P τ z n/(n : ℝ)|}) ≠ ⊤ := by
  let : IsProbabilityMeasure P := h.probability
  let ε : ℝ := 1/((k : ℝ)+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hh := h.summable_ray_centered_deviations hs hr z ε hε
  have he (n : ℕ) : {ω | ε ≤ |passageTime (fun e => τ e ω) 0 ((n+1) • z)/((n+1 : ℕ) : ℝ) -
      meanPassageSequence P τ z (n+1)/((n+1 : ℕ) : ℝ)|} =
      {ω | ε*(n+1 : ℝ) ≤ |passageTime (fun e => τ e ω) 0 ((n+1) • z)-
        meanPassageSequence P τ z (n+1)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ← sub_div, abs_div, Nat.cast_add, Nat.cast_one,
      abs_of_pos (show (0 : ℝ) < n+1 by positivity), le_div_iff₀ (show (0 : ℝ) < n+1 by positivity)]
  have hn : Summable (fun n : ℕ => P.real {ω | ε ≤
      |passageTime (fun e => τ e ω) 0 (n • z)/(n : ℝ)-meanPassageSequence P τ z n/(n : ℝ)|}) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [he] using hh
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hn.tsum_ofReal_ne_top

end GammaFPP

end OAI
end

section
-- module Solutions.OAIW2_GammaFPP.GammaPassage_ActualTimeConstant
attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem GammaEnvironment.isTimeConstant_oai
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    IsTimeConstant P τ (gammaMeanNorm h hs hr) := by
  apply h.isTimeConstant_of_ae_lattice_limits hs hr
  intro z
  exact h.ae_lattice_limit_of_summable_deviations hs hr z
    (fun k => h.normalized_ray_deviations_tsum_ne_top hs hr z k)

end GammaFPP

end OAI
end

theorem solution.{u_1} : type_of% @OAI.GammaFPP.GammaEnvironment.isTimeConstant_oai.{u_1} := @OAI.GammaFPP.GammaEnvironment.isTimeConstant_oai.{u_1}
