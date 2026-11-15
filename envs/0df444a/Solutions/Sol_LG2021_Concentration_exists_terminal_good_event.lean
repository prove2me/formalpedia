-- Prove2me | solution 1 for LG2021.Concentration.exists_terminal_good_event
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T17:05:10.234099+00:00
-- url     : https://prove2.me/submissions/26c81403-89be-4917-9311-64f880149584

import Definitions.Def_LG2021_Policy
import Theorems.Thm_LG2021_Algorithm_candidateTerminalEvent_failure_le
import Theorems.Thm_LG2021_Concentration_estimatorGood_failure_le
import Theorems.Thm_LG2021_Concentration_estimatorGood_full_gradient
import Theorems.Thm_LG2021_Concentration_estimatorGood_full_scalar
import Theorems.Thm_LG2021_Concentration_terminal_trace_regret_good_event
import Mathlib
import Definitions.Def_LG2021_RegretRate
import Definitions.Def_BilateralProfitMHR_ConvexBandit
import Definitions.Def_LG2021_CanonicalBandit
import Definitions.Def_LG2021_GaussianEstimators
import Definitions.Def_LG2021_GaussianSeparation
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
import Theorems.Thm_LG2021_nearby_simplex_volume
import Theorems.Thm_LG2021_paper_strong_separation
import Theorems.Thm_LG2021_shallow_ellipsoid_cover
import Theorems.Thm_ModernConvex_Ellipsoids_lowner_fritz_john
import Theorems.Thm_OAI_IndependentProducts_gaussian_integral_fourth
import Theorems.Thm_RandomGradFree_Nonsmooth_smoothing_hasGradient

set_option autoImplicit false

/- LG2021AlgorithmOracle -/
section

/-!
The concrete estimators and stopping rule of Algorithm 1 in Tor Lattimore and
Andras Gyorgy, "Improved regret for zeroth-order stochastic convex bandits",
Proceedings of the 34th Conference on Learning Theory, PMLR 134, 2021.

The positivity test in `eligible` makes the stopping rule total: a zero
lower confidence bound cannot trigger stopping. The moment constants remain
explicit parameters for the formal concentration estimates.
-/

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory Concentration
open scoped Classical























private theorem measurable_likelihoodRatio {d : ℕ} (lambda : ℝ) :
    Measurable (fun w : Space d × Space d => likelihoodRatio lambda w.1 w.2) := by
  unfold likelihoodRatio
  fun_prop

private theorem measurable_truncation {d : ℕ} (lambda r : ℝ) :
    Measurable (fun w : Space d × Space d => truncation lambda r w.1 w.2) := by
  unfold truncation
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_le (measurable_likelihoodRatio lambda) measurable_const).inter
    (measurableSet_le measurable_snd.norm measurable_const)

private theorem measurable_scalarCoefficient {d : ℕ} (lambda r : ℝ) :
    Measurable (fun w : Space d × Space d => scalarCoefficient lambda r w.1 w.2) := by
  exact ((measurable_const.sub measurable_const).add
    ((measurable_likelihoodRatio lambda).div_const lambda)).mul (measurable_truncation lambda r)

private theorem measurable_gradientCoefficient {d : ℕ} (lambda r : ℝ) :
    Measurable (fun w : Space d × Space d => gradientCoefficient lambda r w.1 w.2) := by
  exact (((measurable_likelihoodRatio lambda).mul (measurable_truncation lambda r)).div_const
    ((1 - lambda) ^ 2)).smul (by fun_prop)



private theorem measurable_scalarEstimate {u : ℕ} (s : Fin u) :
    Measurable (fun w : ℕ × (Fin u → ℝ) => scalarEstimate w.1 w.2 s) := by
  unfold scalarEstimate
  fun_prop

private theorem measurable_confidenceRadius (p : OracleConfig) (u : ℕ) :
    Measurable (fun m : ℕ => confidenceRadius p u m) := measurable_of_countable _

private theorem measurable_lowerBound (p : OracleConfig) {u : ℕ} (s : Fin u) :
    Measurable (fun w : ℕ × (Fin u → ℝ) => lowerBound p w.1 w.2 s) := by
  exact measurable_const.max ((measurable_scalarEstimate s).sub
    ((measurable_confidenceRadius p u).comp measurable_fst))

private theorem measurableSet_eligible (p : OracleConfig) {u : ℕ} (s : Fin u) :
    MeasurableSet {w : ℕ × (Fin u → ℝ) | eligible p w.1 w.2 s} := by
  have hleft : Measurable (fun w : ℕ × (Fin u → ℝ) =>
      (4 * p.momentConstant * p.radius / lowerBound p w.1 w.2 s) ^ 2 *
        confidenceLog p u / p.concentrationConstant) :=
    ((((measurable_const.div (measurable_lowerBound p s)).pow_const 2).mul_const
      (confidenceLog p u)).div_const p.concentrationConstant)
  have hright : Measurable (fun w : ℕ × (Fin u → ℝ) => (w.1 : ℝ)) := by fun_prop
  exact (measurableSet_lt measurable_const (measurable_lowerBound p s)).inter
    (measurableSet_le hleft hright)

private theorem measurable_firstEligible (p : OracleConfig) {u : ℕ} (indices : List (Fin u)) :
    Measurable (fun w : ℕ × (Fin u → ℝ) => firstEligible p indices w.1 w.2) := by
  induction indices with
  | nil => exact measurable_const
  | cons i rest ih => exact Measurable.ite (measurableSet_eligible p i) measurable_const ih

private theorem measurable_winner (p : OracleConfig) {u : ℕ} :
    Measurable (fun w : ℕ × (Fin u → ℝ) => winner p w.1 w.2) :=
  measurable_firstEligible p (List.finRange u)











end LG2021.Algorithm

end
end

/- LG2021AlgorithmGeometry -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory Matrix
open scoped Classical




















@[fun_prop] private theorem continuous_matrixAction {d : ℕ} :
    Continuous (fun w : Matrix (Fin d) (Fin d) ℝ × Space d => matrixAction w.1 w.2) := by
  unfold matrixAction
  fun_prop

@[fun_prop] private theorem measurable_matrixInverse {d : ℕ} :
    Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => M⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact (continuous_id.matrix_det.measurable.inv).smul continuous_id.matrix_adjugate.measurable

@[fun_prop] private theorem continuous_frameApply {d : ℕ} :
    Continuous (fun w : Frame d × Space d => frameApply w.1 w.2) := by
  unfold frameApply
  exact (continuous_matrixAction.comp (continuous_fst.fst.prodMk continuous_snd)).add
    continuous_fst.snd

@[fun_prop] private theorem measurable_frameUnapply {d : ℕ} :
    Measurable (fun w : Frame d × Space d => frameUnapply w.1 w.2) := by
  unfold frameUnapply
  exact continuous_matrixAction.measurable.comp
    ((measurable_matrixInverse.comp measurable_fst.fst).prodMk
      (measurable_snd.sub measurable_fst.snd))

@[fun_prop] private theorem measurable_cutFromEstimate {d : ℕ} :
    Measurable (fun w : Frame d × Space d × Space d => cutFromEstimate w.1 w.2.1 w.2.2) := by
  unfold cutFromEstimate
  have hi : Measurable (fun w : Frame d × Space d × Space d => w.1.1⁻¹) :=
    (measurable_matrixInverse (d := d)).comp measurable_fst.fst
  have ht : Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => M.transpose) :=
    continuous_id.matrix_transpose.measurable
  have ha : Measurable (fun w : Frame d × Space d × Space d =>
      matrixAction w.1.1⁻¹.transpose w.2.2) := by
    exact (continuous_matrixAction (d := d)).measurable.comp
      ((ht.comp hi).prodMk measurable_snd.snd)
  apply ha.prodMk
  exact continuous_inner.measurable.comp (ha.prodMk
    (continuous_frameApply.measurable.comp (measurable_fst.prodMk measurable_snd.fst)))





















end LG2021.Algorithm

end
end

/- LG2021AlgorithmQuantization -/
section

/-!
An explicit countable approximation of halfspace coefficients. This is an
additional algorithm completion, not a statement asserted in Lattimore–Gyorgy.
It permits measurable canonical ellipsoid choices on countable cut histories.
-/

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory
open scoped Classical





private theorem continuous_decodeCut {d : ℕ} : Continuous (decodeCut (d := d)) := by
  unfold decodeCut
  fun_prop

private theorem denseRange_decodeCut {d : ℕ} : DenseRange (decodeCut (d := d)) := by
  have hv : DenseRange (fun v : Fin d → ℚ =>
      (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => (v i : ℝ))) := by
    exact (EuclideanSpace.equiv (Fin d) ℝ).symm.surjective.denseRange.comp
      (DenseRange.piMap (fun _ : Fin d => (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ))))
      (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous
  exact hv.prodMap Rat.denseRange_cast



private theorem enumerateCuts_surjective (d : ℕ) : Function.Surjective (enumerateCuts d) :=
  Classical.choose_spec (exists_surjective_nat (CutCode d))

private theorem denseRange_enumerateCuts (d : ℕ) : DenseRange (fun n => decodeCut (enumerateCuts d n)) :=
  denseRange_decodeCut.comp (enumerateCuts_surjective d).denseRange continuous_decodeCut



private theorem positiveRadius_pos (ε : ℝ) : 0 < positiveRadius ε := by
  unfold positiveRadius
  split_ifs with h
  · exact h
  · norm_num

private theorem measurable_positiveRadius : Measurable positiveRadius := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_id measurable_const

private theorem exists_close_cut {d : ℕ} (w : Cut d × ℝ) :
    ∃ k : ℕ, dist w.1 (decodeCut (enumerateCuts d k)) < positiveRadius w.2 :=
  (denseRange_enumerateCuts d).exists_dist_lt w.1 (positiveRadius_pos w.2)



private theorem measurable_quantizeCut {d : ℕ} :
    Measurable (fun w : Cut d × ℝ => quantizeCut w.1 w.2) := by
  apply (measurable_of_countable (enumerateCuts d)).comp
  apply measurable_find (exists_close_cut (d := d))
  intro k
  exact measurableSet_lt (measurable_fst.dist measurable_const)
    (measurable_positiveRadius.comp measurable_snd)











private theorem measurable_roundedInwardCut {d : ℕ} (R : ℝ) :
    Measurable (fun w : Cut d × ℝ => roundedInwardCut w.1 w.2 R) := by
  have htarget : Measurable (fun w : Cut d × ℝ => inwardCut w.1 w.2) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.sub (measurable_snd.div_const 8))
  exact measurable_quantizeCut.comp (htarget.prodMk
    (measurable_snd.div_const (32 * (R + 1))))







end LG2021.Algorithm

end
end

/- LG2021JohnHelpers -/
section

/-! Small internal adapters reused verbatim from the accepted John-ellipsoid
solution. Their explicit inclusion avoids relying on unexposed helper names in
an external canonical theorem module. The John theorem itself is imported and
reused by its canonical statement. -/

noncomputable section
namespace LG2021.JohnHelpers
open Matrix Finset MeasureTheory ModernConvex.Ellipsoids
open scoped ENNReal



































end LG2021.JohnHelpers

end
end

/- LG2021Geometry -/
section

namespace LG2021

open Set ModernConvex.Ellipsoids



open Matrix











end LG2021

end

/- LG2021AlgorithmSelector -/
section

/-!
A canonical minimum enclosing ellipsoid is chosen for each finite rational cut
history. The history space is countable, so this choice is measurable without
an additional measurable-selection principle.

The geometric existence and rounding facts reuse the proved Loewner–Fritz John
theorem. The countable-history adapter is an additional algorithm completion.
-/

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory Matrix ModernConvex.Ellipsoids
open scoped Classical



















private theorem measurable_canonicalOuterFrame {d p : ℕ} (K : Set (Space d)) (r : ℝ) :
    Measurable (canonicalOuterFrame (p := p) K r) := measurable_of_countable _





















end LG2021.Algorithm

end
end

/- LG2021AlgorithmState -/
section

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace LG2021.Algorithm

open MeasureTheory Concentration
open scoped Classical













private theorem measurable_finSnoc {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {p : ℕ} {f : α → Fin p → β} {g : α → β} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => (Fin.snoc (f a) (g a) : Fin (p + 1) → β)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
  · exact hg
  · exact (measurable_pi_apply j).comp hf

private theorem measurable_optionCases {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {u : ℕ} {choice : α → Option (Fin u)} {no : α → β} {yes : Fin u → α → β}
    (hc : Measurable choice) (hn : Measurable no) (hy : ∀ s, Measurable (yes s)) :
    Measurable (fun a => match choice a with | none => no a | some s => yes s a) := by
  have hm : Measurable (fun w : Option (Fin u) × α =>
      match w.1 with | none => no w.2 | some s => yes s w.2) := by
    apply measurable_from_prod_countable_right
    intro o
    cases o with
    | none => exact hn
    | some s => exact hy s
  exact hm.comp (hc.prodMk measurable_id)

private theorem measurable_updatedScalars {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    (cfg : OracleConfig) {st : α → State d u p} {x : α → Space d} {y y' : α → ℝ}
    (hst : Measurable st) (hx : Measurable x) (hy : Measurable y) (hy' : Measurable y') :
    Measurable (fun a => updatedScalars cfg (st a) (x a) (y a) (y' a)) := by
  apply measurable_pi_lambda
  intro s
  exact (((measurable_pi_apply s).comp hst.snd.snd.snd.snd.fst).add
    (hy.mul ((measurable_scalarCoefficient cfg.lambda cfg.radius).comp
      (((measurable_pi_apply s).comp hst.snd.snd.fst).prodMk hx)))).sub hy'

private theorem measurable_updatedGradients {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    (cfg : OracleConfig) {st : α → State d u p} {x : α → Space d} {y : α → ℝ}
    (hst : Measurable st) (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun a => updatedGradients cfg (st a) (x a) (y a)) := by
  apply measurable_pi_lambda
  intro s
  have hz : Measurable (fun a => (st a).2.2.1 s) :=
    (measurable_pi_apply s).comp hst.snd.snd.fst
  have hc : Measurable (fun a => gradientCoefficient cfg.lambda cfg.radius
      ((st a).2.2.1 s) (x a)) := by
    simpa only [Function.comp_def] using
      (measurable_gradientCoefficient (d := d) cfg.lambda cfg.radius).comp (hz.prodMk hx)
  have hp : Measurable (fun a => (st a).2.2.2.2.2 s) :=
    (measurable_pi_apply s).comp hst.snd.snd.snd.snd.snd
  exact hp.add (hy.smul hc)

private theorem measurable_continueState {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    {st : α → State d u p} {sums : α → Fin u → ℝ} {grads : α → Fin u → Space d}
    (hst : Measurable st) (hs : Measurable sums) (hg : Measurable grads) :
    Measurable (fun a => continueState (st a) (sums a) (grads a)) := by
  exact (measurable_finSnoc hst.fst measurable_const).prodMk
    (hst.snd.fst.prodMk (hst.snd.snd.fst.prodMk
      ((hst.snd.snd.snd.fst.add_const 1).prodMk (hs.prodMk hg))))

private theorem measurable_restartState {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d) (hr : Measurable rounding)
    {st : α → State d u p} {next : α → Fin u → Space d}
    {sums : α → Fin u → ℝ} {grads : α → Fin u → Space d}
    (hst : Measurable st) (hn : Measurable next) (hs : Measurable sums)
    (hg : Measurable grads) (s : Fin u) :
    Measurable (fun a => restartState cfg R rounding (st a) (next a) (sums a) (grads a) s) := by
  have hv : Measurable (fun a => gradientEstimate ((st a).2.2.2.1 + 1) (grads a) s) := by
    unfold gradientEstimate
    have hm : Measurable (fun a => (((st a).2.2.2.1 + 1 : ℕ) : ℝ)) :=
      (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (hst.snd.snd.snd.fst.add_const 1)
    exact hm.inv.smul
      ((measurable_pi_apply s).comp hg)
  have hc : Measurable (fun a => (Fin.snoc (st a).1
      (roundedInwardCut (cutFromEstimate (st a).2.1 ((st a).2.2.1 s)
        (gradientEstimate ((st a).2.2.2.1 + 1) (grads a) s))
          (lowerBound cfg ((st a).2.2.2.1 + 1) (sums a) s) R) : Fin (p + 1) → CutCode d)) := by
    have hz : Measurable (fun a => (st a).2.2.1 s) :=
      (measurable_pi_apply s).comp hst.snd.snd.fst
    have hw : Measurable (fun a => ((st a).2.1, (st a).2.2.1 s,
        gradientEstimate ((st a).2.2.2.1 + 1) (grads a) s)) :=
      hst.snd.fst.prodMk (hz.prodMk hv)
    have hcut := (measurable_cutFromEstimate (d := d)).comp hw
    have hlo := (measurable_lowerBound cfg s).comp ((hst.snd.snd.snd.fst.add_const 1).prodMk hs)
    have hrounded := (measurable_roundedInwardCut (d := d) R).comp (hcut.prodMk hlo)
    exact measurable_finSnoc hst.fst hrounded
  exact hc.prodMk ((hr.comp hc).prodMk (hn.prodMk
    (measurable_const.prodMk (measurable_const.prodMk measurable_const))))

private theorem measurable_step {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d) (hr : Measurable rounding)
    {st : α → State d u p} {next : α → Fin u → Space d}
    {x : α → Space d} {y y' : α → ℝ}
    (hst : Measurable st) (hn : Measurable next) (hx : Measurable x)
    (hy : Measurable y) (hy' : Measurable y') :
    Measurable (fun a => step cfg R rounding (st a) (next a) (x a) (y a) (y' a)) := by
  have hs := measurable_updatedScalars cfg hst hx hy hy'
  have hg := measurable_updatedGradients cfg hst hx hy
  exact measurable_optionCases
    ((measurable_winner cfg).comp ((hst.snd.snd.snd.fst.add_const 1).prodMk hs))
    (measurable_continueState hst hs hg)
    (fun s => measurable_restartState cfg R rounding hr hst hn hs hg s)





private theorem step_continues {d u p : ℕ} (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d)
    (st : State d u p) (next : Fin u → Space d) (x : Space d) (y y' : ℝ)
    (h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') = none) :
    step cfg R rounding st next x y y' =
      continueState st (updatedScalars cfg st x y y') (updatedGradients cfg st x y) := by
  simp only [step, h]

private theorem step_restarts {d u p : ℕ} (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d)
    (st : State d u p) (next : Fin u → Space d) (x : Space d) (y y' : ℝ) (s : Fin u)
    (h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') = some s) :
    step cfg R rounding st next x y y' =
      restartState cfg R rounding st next (updatedScalars cfg st x y y')
        (updatedGradients cfg st x y) s := by
  simp only [step, h]

end LG2021.Algorithm

end
end

/- CorollaryTransport -/
section
noncomputable section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal







end BilateralProfitMHR.CorollaryTransport

end
end

/- LG2021GaussianGeometrySphere -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory













end LG2021

end
end

/- Normalized Gaussian norm support -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory





end LG2021

end
end

/- LG2021AlgorithmPolicy -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory BilateralProfitMHR
open scoped Classical







private theorem measurable_seedCandidates {d u n : ℕ} (p : ℕ) :
    Measurable (fun seed : Seed d u n => seedCandidates seed p) := by
  unfold seedCandidates
  split_ifs <;> fun_prop

private theorem measurable_seedGaussian {d u n : ℕ} (p : ℕ) :
    Measurable (fun seed : Seed d u n => seedGaussian seed p) := by
  unfold seedGaussian
  split_ifs <;> fun_prop





private theorem measurable_initialState {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) :
    Measurable (initialState (u := u) cfg K) := by
  exact measurable_const.prodMk (measurable_const.prodMk
    ((measurable_seedCandidates 0).prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_const))))

private theorem measurable_runState {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (p : ℕ) : Measurable (fun w : Seed d u cfg.horizon × (Fin p → ℝ × ℝ) =>
      runState cfg K R w.1 p w.2) := by
  induction p with
  | zero => exact (measurable_initialState cfg K).comp measurable_fst
  | succ p ih =>
      have hs : Measurable (fun w : Seed d u cfg.horizon × (Fin (p + 1) → ℝ × ℝ) =>
          runState cfg K R w.1 p (fun i => w.2 i.castSucc)) := by
        exact ih.comp (measurable_fst.prodMk (by fun_prop))
      exact measurable_step cfg R (canonicalOuterFrame K cfg.radius)
        (measurable_canonicalOuterFrame K cfg.radius) hs
        ((measurable_seedCandidates (p + 1)).comp measurable_fst)
        ((measurable_seedGaussian p).comp measurable_fst)
        ((measurable_pi_apply (Fin.last p)).comp measurable_snd).fst
        ((measurable_pi_apply (Fin.last p)).comp measurable_snd).snd











private theorem policy_isOn {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (hK : MeasurableSet K) (R : ℝ) {anchor : Space d} (ha : anchor ∈ K) :
    (policy (u := u) cfg K hK R anchor).IsOn K := by
  intro τ seed ys
  change (if proposedQuery cfg K R τ seed ys ∈ K then proposedQuery cfg K R τ seed ys
    else anchor) ∈ K
  split_ifs with h
  · exact h
  · exact ha











end LG2021.Algorithm

end
end

/- CorollaryNormalization -/
section
noncomputable section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
private theorem unitNoiseCond_noiseCond {X : Type} (K : Set X) (L : X → ℝ)
    (ν : ObsKernel X) (hν : UnitNoiseCond K L ν) : NoiseCond K L 1 ν := by
  intro τ xs ys x hxs hx
  obtain ⟨hp, hi, hm, hei, hem⟩ := hν τ xs ys x hxs hx
  refine ⟨hp, hi, hm, ?_⟩
  unfold HighDimProb.Concentration.subgaussianNorm
  refine iInf_le_of_le 1 (iInf_le_of_le (by norm_num) ?_)
  refine iInf_le_of_le (by simpa using hei) (iInf_le_of_le (by simpa using hem) ?_)
  rfl



end BilateralProfitMHR.CorollaryTransport

end
end

/- LG2021Process -/
section

namespace LG2021

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal





private theorem observationKernel_isMarkov {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν) (τ : ℕ) :
    IsMarkovKernel (observationKernel A ν hνm τ) := by
  constructor
  intro z
  exact (hν τ (A.pastQueries z.1 z.2) z.2 (A.query τ z.1 z.2)
    (fun i => hA i z.1 _) (hA τ z.1 z.2)).1

private theorem measurable_history_snoc {Ω : Type} [MeasurableSpace Ω] (τ : ℕ) :
    Measurable (fun z : (Ω × (Fin τ → ℝ)) × ℝ =>
      (z.1.1, (Fin.snoc z.1.2 z.2 : Fin (τ + 1) → ℝ))) := by
  apply Measurable.prodMk (by fun_prop)
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
  · fun_prop
  · fun_prop













end LG2021

end

/- LG2021Concentration -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal






















end LG2021.Concentration

end

/- LG2021ConcentrationProducts -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory















end LG2021.Concentration

end

/- LG2021ConcentrationCentering -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory











end LG2021.Concentration

end

/- LG2021ConcentrationEstimators -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
















end LG2021.Concentration

end

/- LG2021ConcentrationObservation -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
















end LG2021.Concentration

end

/- LG2021ConcentrationKernelMoments -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory











end LG2021.Concentration

end

/- LG2021GaussianMoments -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal

































end LG2021

end
end

/- LG2021ConcentrationEstimatorMoments -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace









end LG2021.Concentration

end

/- LG2021ConcentrationParameters -/
section

set_option autoImplicit false

namespace LG2021.Concentration

/-- Elementary bounds on the explicit confidence base. -/
private theorem parameterBase_bounds (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    (10 ^ 6 : ℝ) ≤ parameterBase d D n ∧
      (d : ℝ) + 1 ≤ parameterBase d D n ∧
      D + 1 ≤ parameterBase d D n ∧
      (n : ℝ) + 1 ≤ parameterBase d D n ∧
      3 * (D + 1) * ((d : ℝ) + 1) ≤ parameterBase d D n := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hdn : (1 : ℝ) ≤ ((d : ℝ) + 1) * ((n : ℝ) + 1) := by nlinarith
  have hDn : (1 : ℝ) ≤ (D + 1) * ((n : ℝ) + 1) := by nlinarith
  have hdD : (1 : ℝ) ≤ ((d : ℝ) + 1) * (D + 1) := by nlinarith
  unfold parameterBase
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n : ℝ) + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hDn (show 0 ≤ (d : ℝ) + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdn (show 0 ≤ D + 1 by positivity)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hdD (show 0 ≤ (n : ℝ) + 1 by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith)
      (show 0 ≤ ((d : ℝ) + 1) * (D + 1) by positivity)]

/-- The explicit confidence logarithm is bounded below and above. -/
private theorem parameterLog_bounds (d n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ parameterLog d D n ∧ parameterLog d D n ≤ 32 * parameterBase d D n := by
  have hb := (parameterBase_bounds d n hD).1
  have hA : 0 < parameterBase d D n := by nlinarith
  have hlower : 1 ≤ Real.log (parameterBase d D n) := by
    apply (Real.le_log_iff_exp_le hA).2
    have h := Real.exp_one_lt_three
    nlinarith
  have hupper := Real.log_le_sub_one_of_pos hA
  unfold parameterLog
  constructor <;> linarith




/-- Basic size bounds for the Gaussian scale in the logarithmic regime. -/
private theorem paperRadius_bounds {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 ≤ paperRadius d L ∧
      0 < paperRadius d L ∧ paperRadius d L ≤ 2 * 10 ^ 5 * (d : ℝ) ^ 2 * L := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : 1 ≤ Real.sqrt (2 * L) := Real.one_le_sqrt.2 (by linarith)
  have hhi : Real.sqrt (2 * L) ≤ 2 * L := (Real.sqrt_le_left (by linarith)).2 (by nlinarith)
  unfold paperRadius
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo (show 0 ≤ (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 by positivity)]
  constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hhi (show 0 ≤ (10 ^ 5 : ℝ) * (d : ℝ) ^ 2 by positivity)]

/-- The contraction parameter is positive and uniformly small. -/
private theorem paperLambda_bounds {d : ℕ} (hd : 0 < d) {L : ℝ} (hL : 1 ≤ L) :
    0 < paperLambda d L ∧ paperLambda d L ≤ 1 / 2 ∧
      (d : ℝ) * paperLambda d L ≤ 1 / 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hLpos : 0 < L := by linarith
  have hden : 0 < (4 * 10 ^ 5 : ℝ) * (d : ℝ) * L := by positivity
  unfold paperLambda
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ hden).2
    have h := mul_le_mul hdR hL (by norm_num) (by positivity)
    nlinarith
  · rw [mul_one_div]
    apply (div_le_iff₀ hden).2
    have h := mul_le_mul_of_nonneg_left hL hdpos.le
    nlinarith











end LG2021.Concentration

end

/- LG2021ConcentrationFinite -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped NNReal






end LG2021.Concentration

end

/- LG2021ConcentrationTruncation -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory












end LG2021.Concentration

end

/- LG2021ConcentrationGaussianTails -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal


















end LG2021.Concentration

end

/- LG2021ConcentrationParameterTails -/
section

set_option autoImplicit false

namespace LG2021.Concentration






end LG2021.Concentration

end

/- LG2021GaussianGeometrySurrogate -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace













end LG2021

end
end

/- LG2021ConcentrationEnvelopes -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace











end LG2021.Concentration

end

/- LG2021ConcentrationBias -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory









end LG2021.Concentration

end

/- LG2021GaussianGeometryTranslation -/
section


noncomputable section
namespace LG2021.GaussianTranslation
universe uX uY uι
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

















end LG2021.GaussianTranslation

namespace LG2021
open MeasureTheory ProbabilityTheory



end LG2021

end
end

/- LG2021GaussianGeometryDensity -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace









end LG2021

end
end

/- LG2021GaussianGeometryAffine -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory











end LG2021

end
end

/- LG2021GaussianGeometryChangeOfMeasure -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory









end LG2021

end
end

/- LG2021GaussianGeometryMollification -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace











end LG2021

end
end

/- LG2021GaussianGeometrySmoothingReuse -/
section
noncomputable section
namespace LG2021.ReusedSmoothing.RGF6
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]





end LG2021.ReusedSmoothing.RGF6
namespace LG2021
open MeasureTheory ProbabilityTheory



end LG2021

end
end

/- LG2021GaussianGeometryIntegrability -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory









end LG2021

end
end

/- LG2021GaussianGeometryGradient -/
section

noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory









end LG2021

end
end

/- LG2021ConcentrationSurrogateBias -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory







end LG2021.Concentration

end

/- LG2021ConcentrationLemma4 -/
section

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory








end LG2021.Concentration

end

/- LG2021ConcentrationConditional -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory




end LG2021.Concentration

end

/- LG2021ConcentrationOracleMoments -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory












end LG2021.Concentration

end

/- LG2021ConcentrationOracleGradient -/
section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory










end LG2021.Concentration

end

/- LG2021ConcentrationPathLaw -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal



private theorem historyMeasure_probability {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (τ : ℕ) :
    IsProbabilityMeasure (historyMeasure A P ν hνm τ) := by
  induction τ with
  | zero =>
      unfold historyMeasure
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  | succ τ ih =>
      letI := ih
      letI := observationKernel_isMarkov A ν hνm hA L γ hν τ
      unfold historyMeasure
      exact Measure.isProbabilityMeasure_map (measurable_history_snoc τ).aemeasurable



/-- Integration against the history law exactly reproduces one observation-kernel step. -/
private theorem lintegral_historyMeasure_succ {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (τ : ℕ)
    (F : Ω × (Fin (τ + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂historyMeasure A P ν hνm (τ + 1)) =
      ∫⁻ w, ∫⁻ y, F (w.1, Fin.snoc w.2 y)
        ∂ν τ (A.pastQueries w.1 w.2) w.2 (A.query τ w.1 w.2)
          ∂historyMeasure A P ν hνm τ := by
  letI := historyMeasure_probability A P ν hνm hA L γ hν τ
  letI := observationKernel_isMarkov A ν hνm hA L γ hν τ
  rw [historyMeasure, lintegral_map hF (measurable_history_snoc τ)]
  exact Measure.lintegral_compProd
    (show Measurable (fun z : (Ω × (Fin τ → ℝ)) × ℝ => F (z.1.1, Fin.snoc z.1.2 z.2))
      from hF.comp (measurable_history_snoc τ))



















end LG2021.Concentration

end
end

/- LG2021ConcentrationFreshSeed -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
























end LG2021.Concentration

end
end

/- LG2021ConcentrationNoAnticipation -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped Classical










end LG2021.Concentration

end
end

/- LG2021ConcentrationSeedCoordinates -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal









/-- The Gaussian coordinate extraction preserves the exact original seed probability law. -/
private theorem insertGaussianSeed_measurePreserving {d u : ℕ} (cfg : OracleConfig)
    (i : Fin (cfg.horizon + 1)) :
    MeasurePreserving (insertGaussianSeed (d := d) (u := u) i)
      ((gaussianRemainderMeasure d u cfg).prod (gaussian d)) (seedMeasure d u cfg) := by
  let μC := Measure.pi (fun _ : Fin (cfg.horizon + 1) =>
    Measure.pi (fun _ : Fin u => sphereMeasure d (cfg.radius / (2 * (d : ℝ)))))
  let μG := Measure.pi (fun _ : Fin cfg.horizon => gaussian d)
  have h1 := measurePreserving_prodAssoc μC μG (gaussian d)
  have h2 := (MeasurePreserving.id μC).prod
    (Measure.measurePreserving_swap (μ := μG) (ν := gaussian d))
  have h3 := (MeasurePreserving.id μC).prod
    (measurePreserving_piFinSuccAbove (fun _ : Fin (cfg.horizon + 1) => gaussian d) i).symm
  convert h3.comp (h2.comp h1) using 1 <;> rfl

private theorem measurable_insertGaussianSeed {d u : ℕ} (cfg : OracleConfig)
    (i : Fin (cfg.horizon + 1)) : Measurable (insertGaussianSeed (d := d) (u := u) i) :=
  (insertGaussianSeed_measurePreserving cfg i).measurable









end LG2021.Concentration

end
end

/- LG2021ConcentrationPairPath -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal



































end LG2021.Concentration

end
end

/- LG2021ConcentrationPairKernel -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR

private theorem measurable_firstHistoryMap_joint {Ω W B : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace B] (encode : W × B → Ω) (he : Measurable encode) (T : ℕ) :
    Measurable (fun p : (W × (Fin T → ℝ)) × B => firstHistoryMap encode p.1 p.2) :=
  (he.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd

private theorem measurable_secondHistoryMap_joint {Ω W B : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace B] (encode : W × B → Ω) (he : Measurable encode) (T : ℕ) :
    Measurable (fun p : (W × (Fin T → ℝ)) × (B × ℝ) => secondHistoryMap encode p.1 p.2) :=
  (measurable_history_snoc T).comp
    (((measurable_firstHistoryMap_joint encode he T).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)









private theorem firstObservationKernel_isMarkov {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ) :
    IsMarkovKernel (firstObservationKernel A ν hνm encode he T) := by
  letI := observationKernel_isMarkov A ν hνm hA L γ hν T
  unfold firstObservationKernel
  infer_instance

private theorem secondObservationKernel_isMarkov {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ) :
    IsMarkovKernel (secondObservationKernel A ν hνm encode he T) := by
  letI := observationKernel_isMarkov A ν hνm hA L γ hν (T + 1)
  unfold secondObservationKernel
  infer_instance

private theorem coordinateFirstPairKernel_isMarkov {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B) [IsProbabilityMeasure Q]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ) :
    IsMarkovKernel (coordinateFirstPairKernel A Q ν hνm encode he T) := by
  letI := firstObservationKernel_isMarkov A ν hνm encode he hA L γ hν T
  unfold coordinateFirstPairKernel
  infer_instance








end LG2021.Concentration

end
end

/- LG2021ConcentrationObservationPath -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal Classical















end LG2021.Concentration

end
end

/- LG2021ConcentrationPredictableMeans -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm














end LG2021.Concentration

namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm



end LG2021.Concentration

end
end

/- LG2021ConcentrationPathAccumulation -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal






end LG2021.Concentration

end
end

/- LG2021ConcentrationPredictable -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm



private theorem measurable_prefixSeed {d u n : ℕ} (p : ℕ) : Measurable (prefixSeed (d := d) (u := u) (n := n) p) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro j
  by_cases hj : j.val < p <;> simp only [prefixSeed, hj, ↓reduceIte] <;> fun_prop











private theorem measurable_beforePair (p : ℕ) : Measurable (beforePair (p := p)) := by
  unfold beforePair
  fun_prop
















private theorem measurable_pairSum {d u n : ℕ}
    (increment : (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ)
    (hinc : ∀ p, Measurable (fun w : Seed d u n × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) =>
      increment p w.1 w.2.1 w.2.2)) (p : ℕ) :
    Measurable (fun w : Seed d u n × (Fin (2 * p) → ℝ) => pairSum increment p w.1 w.2) := by
  induction p with
  | zero => exact measurable_const
  | succ p ih =>
      have hh : Measurable (fun w : Seed d u n × (Fin (2 * (p + 1)) → ℝ) =>
          (fun j : Fin (2 * p + 2) => w.2 ⟨j.val, by omega⟩)) := by fun_prop
      have hprev := (measurable_beforePair p).comp hh
      have hleft := ih.comp (measurable_fst.prodMk hprev)
      have hseed : Measurable (fun w : Seed d u n × (Fin (2 * (p + 1)) → ℝ) => prefixSeed p w.1) :=
        (measurable_prefixSeed (d := d) (u := u) (n := n) p).comp measurable_fst
      have hx : Measurable (fun w : Seed d u n × (Fin (2 * (p + 1)) → ℝ) => seedGaussian w.1 p) :=
        (measurable_seedGaussian (d := d) (u := u) (n := n) p).comp measurable_fst
      have hy := (measurable_pi_apply (⟨2 * p, by omega⟩ : Fin (2 * p + 2))).comp hh
      have hy' := (measurable_pi_apply (⟨2 * p + 1, by omega⟩ : Fin (2 * p + 2))).comp hh
      exact hleft.add ((hinc p).comp (hseed.prodMk (hprev.prodMk ((hx.prodMk hy).prodMk hy'))))


end LG2021.Concentration

end
end

/- LG2021ConcentrationKernelPrefix -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm



private theorem measurable_removeGaussianSeed {d u n : ℕ} (i : Fin (n + 1)) :
    Measurable (removeGaussianSeed (d := d) (u := u) i) := by
  unfold removeGaussianSeed Fin.removeNth
  fun_prop



























end LG2021.Concentration

end
end

/- LG2021ConcentrationPathFinite -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal




end LG2021.Concentration

end
end

/- LG2021ConcentrationPredictableEstimators -/
section

noncomputable section
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal



private theorem measurable_scalarIncrement {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν)
    (enabled : ℕ → Bool)
    (active : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Bool)
    (z : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Space d)
    (hactive : ∀ p, Measurable (active p)) (hz : ∀ p, Measurable (z p)) (p : ℕ) :
    Measurable (fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) =>
      scalarIncrement cfg K hK R anchor ν hνm enabled active z p w.1 w.2.1 w.2.2) := by
  by_cases hp : p < cfg.horizon + 1
  · simp only [scalarIncrement, dif_pos hp]
    let i : Fin (cfg.horizon + 1) := ⟨p, hp⟩
    let A := policy (u := u) cfg K hK R anchor
    have hA := policy_isOn (u := u) cfg K hK R ha
    have hmean : Measurable (fun v : Space d × (GaussianRemainder d u cfg.horizon × (Fin (2 * p) → ℝ)) =>
        scalarPredictableMean A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i)
          cfg.lambda cfg.radius v.1 v.2) := by
      letI := coordinateFirstPairKernel_isMarkov A (gaussian d) ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) hA L γ hν (2 * p)
      letI := secondObservationKernel_isMarkov A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) hA L γ hν (2 * p)
      have hC : Measurable (fun w : (Space d × (GaussianRemainder d u cfg.horizon × (Fin (2 * p) → ℝ))) × (Space d × ℝ) =>
          w.2.2 * scalarCoefficient cfg.lambda cfg.radius w.1.1 w.2.1) :=
        measurable_snd.snd.mul ((Algorithm.measurable_scalarCoefficient cfg.lambda cfg.radius).comp
          (f := fun w : (Space d × (GaussianRemainder d u cfg.horizon × (Fin (2 * p) → ℝ))) × (Space d × ℝ) => (w.1.1, w.2.1))
          (measurable_fst.fst.prodMk measurable_snd.fst))
      have hfirst := hC.stronglyMeasurable.integral_kernel_prod_right'
        (κ := (coordinateFirstPairKernel A (gaussian d) ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) (2 * p)).comap Prod.snd measurable_snd)
      have hsecond := (measurable_id : Measurable (id : ℝ → ℝ)).stronglyMeasurable.integral_kernel
        (κ := secondObservationKernel A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) (2 * p))
      exact hfirst.measurable.sub (hsecond.measurable.comp (measurable_snd.prodMk measurable_const))
    have harg : Measurable (fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) =>
        (z p (w.1, w.2.1), (removeGaussianSeed i w.1, w.2.1))) :=
      ((hz p).comp (measurable_fst.prodMk measurable_snd.fst)).prodMk
        (((measurable_removeGaussianSeed i).comp measurable_fst).prodMk measurable_snd.fst)
    have hC : Measurable (fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) =>
        scalarCoefficient cfg.lambda cfg.radius (z p (w.1, w.2.1)) w.2.2.1.1) :=
      (Algorithm.measurable_scalarCoefficient cfg.lambda cfg.radius).comp
        (f := fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) => (z p (w.1, w.2.1), w.2.2.1.1))
        (((hz p).comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd.fst.fst)
    have hset : MeasurableSet {w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) | (enabled p && active p (w.1, w.2.1)) = true} := by
      cases he : enabled p
      · simp
      · simpa only [Bool.true_and, Function.comp_apply] using measurableSet_eq_fun ((hactive p).comp (measurable_fst.prodMk measurable_snd.fst)) measurable_const
    exact Measurable.ite hset
      (((measurable_snd.snd.fst.snd.mul hC).sub measurable_snd.snd.snd).sub (hmean.comp harg)) measurable_const
  · simp only [scalarIncrement, dif_neg hp]
    exact measurable_const



end LG2021.Concentration

namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal



end LG2021.Concentration

end
end

/- LG2021ConcentrationPredictableGradient -/
section

noncomputable section
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal



private theorem measurable_gradientIncrement {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν)
    (enabled : ℕ → Bool)
    (active : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Bool)
    (z η : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Space d)
    (hactive : ∀ p, Measurable (active p)) (hz : ∀ p, Measurable (z p)) (hη : ∀ p, Measurable (η p)) (p : ℕ) :
    Measurable (fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) =>
      gradientIncrement cfg K hK R anchor ν hνm enabled active z η p w.1 w.2.1 w.2.2) := by
  by_cases hp : p < cfg.horizon + 1
  · simp only [gradientIncrement, dif_pos hp]
    let i : Fin (cfg.horizon + 1) := ⟨p, hp⟩
    let A := policy (u := u) cfg K hK R anchor
    have hA := policy_isOn (u := u) cfg K hK R ha
    have hmean : Measurable (fun v : (Space d × Space d) × (GaussianRemainder d u cfg.horizon × (Fin (2 * p) → ℝ)) =>
        gradientPredictableMean A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i)
          cfg.lambda cfg.radius v.1.1 v.1.2 v.2) := by
      letI := coordinateFirstPairKernel_isMarkov A (gaussian d) ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) hA L γ hν (2 * p)
      have hG : Measurable (fun w : ((Space d × Space d) × (GaussianRemainder d u cfg.horizon × (Fin (2 * p) → ℝ))) × (Space d × ℝ) =>
          gradientCoefficient cfg.lambda cfg.radius w.1.1.1 w.2.1) :=
        (Algorithm.measurable_gradientCoefficient cfg.lambda cfg.radius).comp
          (f := fun w : ((Space d × Space d) × (GaussianRemainder d u cfg.horizon × (Fin (2 * p) → ℝ))) × (Space d × ℝ) => (w.1.1.1, w.2.1))
          (measurable_fst.fst.fst.prodMk measurable_snd.fst)
      exact ((measurable_snd.snd.mul (hG.inner measurable_fst.fst.snd)).stronglyMeasurable.integral_kernel_prod_right'
        (κ := (coordinateFirstPairKernel A (gaussian d) ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) (2 * p)).comap Prod.snd measurable_snd)).measurable
    have hz' : Measurable (fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) => z p (w.1, w.2.1)) := (hz p).comp (f := fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) => (w.1, w.2.1)) (measurable_fst.prodMk measurable_snd.fst)
    have hη' : Measurable (fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) => η p (w.1, w.2.1)) := (hη p).comp (f := fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) => (w.1, w.2.1)) (measurable_fst.prodMk measurable_snd.fst)
    have harg : Measurable (fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) => ((z p (w.1, w.2.1), η p (w.1, w.2.1)), (removeGaussianSeed i w.1, w.2.1))) := (hz'.prodMk hη').prodMk
      (((measurable_removeGaussianSeed i).comp measurable_fst).prodMk measurable_snd.fst)
    have hG : Measurable (fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) =>
        gradientCoefficient cfg.lambda cfg.radius (z p (w.1, w.2.1)) w.2.2.1.1) :=
      (Algorithm.measurable_gradientCoefficient cfg.lambda cfg.radius).comp
        (f := fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) => (z p (w.1, w.2.1), w.2.2.1.1))
        (hz'.prodMk measurable_snd.snd.fst.fst)
    have hset : MeasurableSet {w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) | (enabled p && active p (w.1, w.2.1)) = true} := by
      cases he : enabled p
      · simp
      · simpa only [Bool.true_and, Function.comp_apply] using measurableSet_eq_fun ((hactive p).comp (measurable_fst.prodMk measurable_snd.fst)) measurable_const
    exact Measurable.ite hset (Measurable.ite
      ((measurableSet_le (measurable_const.mul hz'.norm) measurable_const).inter
        (measurableSet_le hη'.norm measurable_const))
      ((measurable_snd.snd.fst.snd.mul (hG.inner hη')).sub (hmean.comp harg)) measurable_const) measurable_const
  · simp only [gradientIncrement, dif_neg hp]
    exact measurable_const



end LG2021.Concentration

end
end

/- LG2021ConcentrationBernstein -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory






end LG2021.Concentration

end

/- LG2021OracleConfidenceArithmetic -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory









private theorem oracleConcentrationConstant_pos : 0 < oracleConcentrationConstant := by
  norm_num [oracleConcentrationConstant]

















end LG2021.Concentration

end
end

/- LG2021ConcentrationHistoryPrefix -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal



private theorem measurable_historyPrefix {Ω : Type} [MeasurableSpace Ω] {T N : ℕ} (hTN : T ≤ N) :
    Measurable (historyPrefix (Ω := Ω) hTN) := by
  unfold historyPrefix
  fun_prop



private theorem historyPrefix_snoc {Ω : Type} {T N : ℕ} (hTN : T ≤ N)
    (w : Ω × (Fin N → ℝ)) (y : ℝ) :
    historyPrefix (hTN.trans (Nat.le_succ N)) (w.1, Fin.snoc w.2 y) = historyPrefix hTN w := by
  unfold historyPrefix
  apply Prod.ext
  · rfl
  · funext j
    change Fin.snoc (α := fun _ => ℝ) w.2 y (Fin.castLE hTN j).castSucc = w.2 (Fin.castLE hTN j)
    simp only [Fin.snoc_castSucc]

/-- The actual observation process has consistent finite history marginals. -/
private theorem lintegral_historyMeasure_prefix {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) {T N : ℕ} (hTN : T ≤ N)
    (F : Ω × (Fin T → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (historyPrefix hTN w) ∂historyMeasure A P ν hνm N) =
      ∫⁻ w, F w ∂historyMeasure A P ν hνm T := by
  induction N generalizing T with
  | zero =>
      have hT : T = 0 := by omega
      subst T
      rfl
  | succ N ih =>
      by_cases hT : T = N + 1
      · subst T
        rfl
      · have hprev : T ≤ N := by omega
        rw [lintegral_historyMeasure_succ A P ν hνm hA L γ hν N (fun w => F (historyPrefix hTN w))
          (hF.comp (measurable_historyPrefix hTN))]
        have he (w : Ω × (Fin N → ℝ)) :
            (∫⁻ y, F (historyPrefix hTN (w.1, Fin.snoc w.2 y))
              ∂ν N (A.pastQueries w.1 w.2) w.2 (A.query N w.1 w.2)) =
              F (historyPrefix hprev w) := by
          letI := (hν N (A.pastQueries w.1 w.2) w.2 (A.query N w.1 w.2)
            (fun i => hA i w.1 _) (hA N w.1 w.2)).1
          simp_rw [historyPrefix_snoc hprev]
          simp
        simp_rw [he]
        exact ih hprev F hF

private theorem historyMeasure_map_prefix {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) {T N : ℕ} (hTN : T ≤ N) :
    (historyMeasure A P ν hνm N).map (historyPrefix (Ω := Ω) hTN) =
      historyMeasure A P ν hνm T := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_historyPrefix hTN)]
  exact lintegral_historyMeasure_prefix A P ν hνm hA L γ hν hTN F hF

private theorem historyMeasure_prefix_probability {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) {T N : ℕ} (hTN : T ≤ N)
    (s : Set (Ω × (Fin T → ℝ))) (hs : MeasurableSet s) :
    (historyMeasure A P ν hνm N).real ((historyPrefix hTN) ⁻¹' s) =
      (historyMeasure A P ν hνm T).real s := by
  unfold Measure.real
  rw [← Measure.map_apply (measurable_historyPrefix hTN) hs,
    historyMeasure_map_prefix A P ν hνm hA L γ hν hTN]





end LG2021.Concentration

end
end

/- LG2021ConcentrationEstimatorConfidence -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal









end LG2021.Concentration

namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal





end LG2021.Concentration

end
end

/- LG2021ConcentrationTerminalConfidence -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal







end LG2021.Concentration

end
end

/- LG2021AlgorithmInvariant -/
section

noncomputable section
namespace LG2021.Algorithm

open Set MeasureTheory BilateralProfitMHR
open scoped Classical





























end LG2021.Algorithm

end
end

/- LG2021OracleSampleComplexity -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory













end LG2021.Algorithm

end
end

/- LG2021AlgorithmTrace -/
section

noncomputable section

namespace LG2021.Algorithm

open scoped Classical







private theorem traceState_succ {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) :
    traceState cfg K R seed ys (p + 1) =
      step cfg R (canonicalOuterFrame K cfg.radius) (traceState cfg K R seed ys p)
        (seedCandidates seed (p + 1)) (seedGaussian seed p) (ys p).1 (ys p).2 := rfl

private theorem traceStage_monotone {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) :
    Monotone (traceStage cfg K R seed ys) := by
  apply monotone_nat_of_le_succ
  intro p
  simp only [traceStage]
  omega





private theorem traceState_age_eq_card {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) :
    (traceState cfg K R seed ys p).2.2.2.1 =
      ((Finset.range p).filter (fun j => traceStage cfg K R seed ys j =
        traceStage cfg K R seed ys p)).card := by
  induction p with
  | zero => simp [traceState, runState, initialState]
  | succ p ih =>
      rw [traceState_succ]
      cases h : traceWinner cfg K R seed ys p with
      | none =>
          rw [step_continues cfg R _ _ _ _ _ _ h]
          have hstage : traceStage cfg K R seed ys (p + 1) =
              traceStage cfg K R seed ys p := by simp [traceStage, h]
          change (traceState cfg K R seed ys p).2.2.2.1 + 1 = _
          rw [hstage, Finset.range_add_one, Finset.filter_insert]
          simp only [if_true]
          rw [Finset.card_insert_of_notMem (by simp)]
          exact congrArg (fun q => q + 1) ih
      | some s =>
          rw [step_restarts cfg R _ _ _ _ _ _ s h]
          change 0 = _
          have hstage : traceStage cfg K R seed ys (p + 1) =
              traceStage cfg K R seed ys p + 1 := by simp [traceStage, h]
          have hempty : (Finset.range (p + 1)).filter (fun j => traceStage cfg K R seed ys j =
              traceStage cfg K R seed ys (p + 1)) = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.2
            intro j hj
            rcases Finset.mem_filter.1 hj with ⟨hjp, hjs⟩
            have hle := traceStage_monotone cfg K R seed ys (Nat.le_of_lt_succ (Finset.mem_range.1 hjp))
            rw [hstage] at hjs
            omega
          rw [hempty]
          rfl



private theorem traceCore_succ_of_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (p : ℕ)
    (hstage : traceStage cfg K R seed ys (p + 1) = traceStage cfg K R seed ys p) :
    traceCore cfg K R seed ys (p + 1) = traceCore cfg K R seed ys p := by
  have hn : traceWinner cfg K R seed ys p = none := by
    by_contra hh
    simp only [traceStage, if_neg hh] at hstage
    omega
  unfold traceCore
  rw [traceState_succ, step_continues cfg R _ _ _ _ _ _ hn]
  rfl

private theorem eq_of_same_monotone_stage {X : Type*} (stage : ℕ → ℕ)
    (hmono : Monotone stage) (value : ℕ → X)
    (hnext : ∀ p, stage (p + 1) = stage p → value (p + 1) = value p)
    {p q : ℕ} (hpq : p ≤ q) (hstage : stage q = stage p) : value q = value p := by
  revert hstage
  induction q, hpq using Nat.le_induction with
  | base => intro _; rfl
  | succ j hpj ih =>
      intro hjs
      have hj : stage j = stage p := le_antisymm
        ((hmono (Nat.le_succ j)).trans_eq hjs) (hmono hpj)
      exact (hnext j (hjs.trans hj.symm)).trans (ih hj)

private theorem traceCore_eq_of_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) {p q : ℕ}
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys q) :
    traceCore cfg K R seed ys p = traceCore cfg K R seed ys q := by
  rcases le_total p q with hpq | hqp
  · exact (eq_of_same_monotone_stage _ (traceStage_monotone cfg K R seed ys) _
      (traceCore_succ_of_same_stage cfg K R seed ys) hpq hstage.symm).symm
  · exact eq_of_same_monotone_stage _ (traceStage_monotone cfg K R seed ys) _
      (traceCore_succ_of_same_stage cfg K R seed ys) hqp hstage



end LG2021.Algorithm

end
end

/- LG2021TraceSums -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration































end LG2021.Algorithm

end
end

/- LG2021TerminalTrace -/
section

noncomputable section

namespace LG2021.Algorithm







private theorem terminalPairs_observationPrefix {n : ℕ} (ys : Fin n → ℝ)
    (τ : ℕ) (hτ : τ ≤ n) (p : ℕ) (hp : p < τ / 2) :
    terminalPairs (observationPrefix ys τ hτ) p = terminalPairs ys p := by
  have ht : 2 * p + 1 < τ := by omega
  have hn : 2 * p + 1 < n := by omega
  simp only [terminalPairs, dif_pos ht, dif_pos hn, observationPrefix]
  rfl



private theorem terminalTrace_prefix_eq {d u n : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : Fin n → ℝ) (τ : ℕ) (hτ : τ ≤ n) {p : ℕ} (hp : p ≤ τ / 2) :
    traceState cfg K R seed (terminalPairs (observationPrefix ys τ hτ)) p =
      traceState cfg K R seed (terminalPairs ys) p := by
  unfold traceState
  congr 1
  funext i
  exact terminalPairs_observationPrefix ys τ hτ i (by have hi := i.isLt; omega)

end LG2021.Algorithm

end
end

/- LG2021RegretAggregation -/
section

namespace LG2021







end LG2021

end

/- LG2021StageAggregation -/
section

noncomputable section

namespace LG2021.Algorithm

open scoped Classical























end LG2021.Algorithm

end
end

/- LG2021StageSampleCost -/
section

noncomputable section

namespace LG2021.Algorithm

open scoped Classical















end LG2021.Algorithm

end
end

/- LG2021StageRegret -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory





private theorem traceComparatorGap_eq_of_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (L : Space d → ℝ) (xstar : Space d) {p q : ℕ}
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys q) :
    traceComparatorGap cfg K R seed ys L xstar p = traceComparatorGap cfg K R seed ys L xstar q := by
  have hcore := traceCore_eq_of_same_stage cfg K R seed ys hstage
  have hframe : (traceState cfg K R seed ys p).2.1 =
      (traceState cfg K R seed ys q).2.1 :=
    congrArg (fun z : Frame d × (Fin u → Space d) => z.1) hcore
  exact congrArg (frameGap L xstar) hframe





end LG2021.Algorithm

end
end

/- LG2021TraceMeasurable -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory
open scoped Classical

private theorem measurable_terminalPairs (n : ℕ) : Measurable (terminalPairs (n := n)) := by
  apply measurable_pi_lambda
  intro p
  unfold terminalPairs
  split_ifs <;> fun_prop

private theorem measurable_traceState {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (R : ℝ) (p : ℕ) :
    Measurable (fun w : Seed d u cfg.horizon × (ℕ → ℝ × ℝ) =>
      traceState cfg K R w.1 w.2 p) := by
  exact (measurable_runState cfg K R p).comp
    (measurable_fst.prodMk (by fun_prop))

private theorem measurable_traceWinner {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (R : ℝ) (p : ℕ) :
    Measurable (fun w : Seed d u cfg.horizon × (ℕ → ℝ × ℝ) =>
      traceWinner cfg K R w.1 w.2 p) := by
  have hst := measurable_traceState (u := u) cfg K R p
  have hx : Measurable (fun w : Seed d u cfg.horizon × (ℕ → ℝ × ℝ) => seedGaussian w.1 p) :=
    (measurable_seedGaussian (d := d) (u := u) (n := cfg.horizon) p).comp measurable_fst
  have hy : Measurable (fun w : Seed d u cfg.horizon × (ℕ → ℝ × ℝ) => (w.2 p).1) := by fun_prop
  have hy' : Measurable (fun w : Seed d u cfg.horizon × (ℕ → ℝ × ℝ) => (w.2 p).2) := by fun_prop
  exact (measurable_winner cfg).comp
    ((hst.snd.snd.snd.fst.add_const 1).prodMk (measurable_updatedScalars cfg hst hx hy hy'))

private theorem measurable_traceStage {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (R : ℝ) (p : ℕ) :
    Measurable (fun w : Seed d u cfg.horizon × (ℕ → ℝ × ℝ) =>
      traceStage cfg K R w.1 w.2 p) := by
  induction p with
  | zero => exact measurable_const
  | succ p ih =>
      have hs : MeasurableSet {w : Seed d u cfg.horizon × (ℕ → ℝ × ℝ) |
          traceWinner cfg K R w.1 w.2 p = none} :=
        measurableSet_eq_fun (measurable_traceWinner (u := u) cfg K R p) measurable_const
      have hm : Measurable (fun w : Seed d u cfg.horizon × (ℕ → ℝ × ℝ) =>
          if traceWinner cfg K R w.1 w.2 p = none then (0 : ℕ) else 1) :=
        Measurable.ite hs measurable_const measurable_const
      exact ih.add hm

private theorem measurable_frameGap {d : ℕ} {L : Space d → ℝ} (hL : Continuous L)
    (xstar : Space d) : Measurable (frameGap L xstar) := by
  have hm : Measurable (fun w : Frame d × Space d => L (frameApply w.1 w.2)) :=
    hL.measurable.comp continuous_frameApply.measurable
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.sub_const (L xstar)



private theorem measurable_terminalTraceState {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (R : ℝ) (p : ℕ) :
    Measurable (fun w : Seed d u cfg.horizon × (Fin N → ℝ) =>
      traceState cfg K R w.1 (terminalPairs w.2) p) := by
  exact (measurable_traceState cfg K R p).comp
    (measurable_fst.prodMk ((measurable_terminalPairs N).comp measurable_snd))

private theorem measurable_terminalTraceStage {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (R : ℝ) (p : ℕ) :
    Measurable (fun w : Seed d u cfg.horizon × (Fin N → ℝ) =>
      traceStage cfg K R w.1 (terminalPairs w.2) p) := by
  exact (measurable_traceStage cfg K R p).comp
    (measurable_fst.prodMk ((measurable_terminalPairs N).comp measurable_snd))



private theorem measurable_sameStageBefore {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (R : ℝ) (a p : ℕ) :
    Measurable (fun w : Seed d u cfg.horizon × (Fin N → ℝ) => sameStageBefore cfg K R a p w.1 w.2) := by
  have hs := measurableSet_eq_fun (measurable_terminalTraceStage (u := u) (N := N) cfg K R p)
    (measurable_terminalTraceStage (u := u) (N := N) cfg K R a)
  exact Measurable.ite hs measurable_const measurable_const



end LG2021.Algorithm

end
end

/- LG2021ConcentrationStageEstimators -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm







private theorem measurable_stageActive {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ) (a p : ℕ) :
    Measurable (stageActive (u := u) cfg K R a p) :=
  measurable_sameStageBefore cfg K R a p

private theorem measurable_stageCandidate {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (a : ℕ) (s : Fin u) (p : ℕ) : Measurable (stageCandidate cfg K R a s p) :=
  (measurable_pi_apply s).comp (measurable_terminalTraceState (N := 2 * p) cfg K R a).snd.snd.fst

private theorem measurable_stageDirection {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (a : ℕ) (s : Fin u) (v : Space d) (p : ℕ) : Measurable (stageDirection cfg K R a s v p) := by
  have hframe := (measurable_terminalTraceState (u := u) (N := 2 * p) cfg K R a).snd.fst
  have hu := measurable_frameUnapply.comp (hframe.prodMk (measurable_const (a := v)))
  exact (hu.sub (measurable_stageCandidate cfg K R a s p)).const_smul ((2 * cfg.radius)⁻¹)









end LG2021.Concentration

end
end

/- LG2021ConcentrationSumExpansion -/
section

noncomputable section
namespace LG2021.Concentration
open Algorithm







end LG2021.Concentration

end
end

/- LG2021ConcentrationStageExpansion -/
section

noncomputable section
namespace LG2021.Concentration
open Algorithm













end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR





end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR







end LG2021.Concentration

end
end

/- LG2021AlgorithmEllipsoidHelpers -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory ModernConvex.EllipsoidMethod


end LG2021.Algorithm

end
end

/- LG2021AlgorithmShallow -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory ModernConvex.EllipsoidMethod



end LG2021.Algorithm

end
end

/- LG2021AlgorithmVolume -/
section

/-!
Minimum-ellipsoid and protected-volume adapters. The source simplex supplies
the protected positive volume. The geometric contraction is the explicit
shallow-cut theorem.
-/

noncomputable section
namespace LG2021.Algorithm

open Matrix MeasureTheory Set ModernConvex.Ellipsoids
open LG2021.JohnHelpers
open scoped ENNReal






















end LG2021.Algorithm

end
end

/- LG2021AlgorithmSimplex -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory Set
open scoped BigOperators Classical








end LG2021.Algorithm

end
end

/- LG2021GaussianGeometryConvex -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace







end LG2021

end
end

/- LG2021AlgorithmPreservation -/
section

/-! The stopping test and its actual confidence estimates preserve every
near-minimizing point. The strict margin also justifies inward rational rounding. -/

noncomputable section
namespace LG2021.Algorithm















end LG2021.Algorithm

end
end

/- LG2021AlgorithmStageVolume -/
section

noncomputable section
namespace LG2021.Algorithm

open Set MeasureTheory Matrix ModernConvex.Ellipsoids
open scoped Classical

























end LG2021.Algorithm

end
end

/- LG2021CandidateSampling -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory



private theorem candidateCount_pos {n : ℕ} (hn : 1 ≤ n) : 0 < candidateCount n := by
  apply Nat.one_le_ceil_iff.2
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 < 3 * (n : ℝ) ^ 2 := by nlinarith
  exact mul_pos (by norm_num) (Real.log_pos hp)







end LG2021.Algorithm

end
end

/- LG2021RateAlgebra -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration













end LG2021.Algorithm

end
end

/- LG2021AlgorithmStageRate -/
section

noncomputable section
namespace LG2021.Algorithm

open Set MeasureTheory Concentration





















end LG2021.Algorithm

end
end

/- LG2021AlgorithmGoodHistory -/
section

noncomputable section
namespace LG2021.Algorithm

open Set MeasureTheory



























end LG2021.Algorithm

end
end

/- LG2021ConcentrationStageBuffers -/
section

noncomputable section
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR









end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR







end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR





end LG2021.Concentration

end
end

/- LG2021GuardedRegret -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory Set
open scoped Classical



















namespace Algorithm





end Algorithm
end LG2021

end
end

/- LG2021PairRegret -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical

























end LG2021.Concentration

end
end

/- LG2021AlgorithmParameters -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration



private theorem oracleConfig_bounds {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) :
    1 ≤ (oracleConfig d D n).radius ∧
    0 < (oracleConfig d D n).lambda ∧ (oracleConfig d D n).lambda ≤ 1 / 2 ∧
    1 ≤ (oracleConfig d D n).momentConstant ∧
    0 < (oracleConfig d D n).concentrationConstant ∧
    (oracleConfig d D n).concentrationConstant ≤ 1 ∧
    1 ≤ confidenceLog (oracleConfig d D n) (candidateCount n) := by
  have hL := (parameterLog_bounds d n hD).1
  have hr := (paperRadius_bounds hd hL).1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hl := paperLambda_bounds hd hL
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : (1 : ℝ) ≤ candidateCount n := by exact_mod_cast candidateCount_pos (by omega : 1 ≤ n)
  refine ⟨?_, hl.1, hl.2.1, ?_, oracleConcentrationConstant_pos, ?_, ?_⟩
  · change 1 ≤ paperRadius d (parameterLog d D n)
    nlinarith
  · norm_num [oracleConfig, oracleMomentConstant]
  · norm_num [oracleConfig, oracleConcentrationConstant]
  · unfold confidenceLog oracleConfig
    apply (Real.le_log_iff_exp_le (by positivity)).2
    have he := Real.exp_one_lt_three
    have hpow : (8 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnR 3
      norm_num at hp
      exact hp
    nlinarith [mul_le_mul_of_nonneg_left hu (show 0 ≤ (n : ℝ) ^ 3 by positivity)]







end LG2021.Algorithm

end
end

/- LG2021ConcentrationActualBias -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical



end LG2021.Concentration

end
end

/- LG2021ConcentrationStageBias -/
section

noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical










end LG2021.Concentration

end
end

/- LG2021ConcentrationStageEvents -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm









end LG2021.Concentration

namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm

private theorem measurableSet_scalarStageFailure {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν) (N : ℕ) (H : ℝ) :
    MeasurableSet (scalarStageFailure (u := u) cfg K hK R anchor ν hνm N H) := by
  simp only [scalarStageFailure, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro k
  have he : Measurable (fun w : Seed d u cfg.horizon × (Fin (2*N) → ℝ) =>
      stageScalarError cfg K hK R anchor ν hνm a.val k b.val
        (historyPrefix (by have hb := b.isLt; omega : 2*b.val ≤ 2*N) w)) :=
    (measurable_pairSum _ (measurable_scalarIncrement cfg K hK R anchor ha ν hνm L γ hν
      (fun p => decide (a.val ≤ p)) (stageActive cfg K R a.val) (stageCandidate cfg K R a.val k)
      (measurable_stageActive cfg K R a.val) (measurable_stageCandidate cfg K R a.val k)) b.val).comp
      (measurable_historyPrefix _)
  by_cases hab : a.val < b.val
  · simpa only [hab, true_and] using measurableSet_le measurable_const
      ((he.div_const ((b.val-a.val : ℕ) : ℝ)).abs)
  · simp [hab]

private theorem measurableSet_gradientStageFailure {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν) (N : ℕ) (H : ℝ) (v : Fin (d+1) → Space d) :
    MeasurableSet (gradientStageFailure (u := u) cfg K hK R anchor ν hνm N H v) := by
  simp only [gradientStageFailure, Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro i
  have he : Measurable (fun w : Seed d u cfg.horizon × (Fin (2*N) → ℝ) =>
      stageGradientError cfg K hK R anchor ν hνm a.val k (v i) b.val
        (historyPrefix (by have hb := b.isLt; omega : 2*b.val ≤ 2*N) w)) :=
    (measurable_pairSum _ (measurable_gradientIncrement cfg K hK R anchor ha ν hνm L γ hν
      (fun p => decide (a.val ≤ p)) (stageActive cfg K R a.val) (stageCandidate cfg K R a.val k) (stageDirection cfg K R a.val k (v i))
      (measurable_stageActive cfg K R a.val) (measurable_stageCandidate cfg K R a.val k) (measurable_stageDirection cfg K R a.val k (v i))) b.val).comp
      (measurable_historyPrefix _)
  by_cases hab : a.val < b.val
  · by_cases hm : H / oracleConcentrationConstant ≤ ((b.val-a.val : ℕ) : ℝ)
    · simpa only [hab, hm, true_and] using measurableSet_le measurable_const
        ((he.div_const ((b.val-a.val : ℕ) : ℝ)).abs)
    · simp [hm]
  · simp [hab]

end LG2021.Concentration

end
end

/- LG2021StageStarts -/
section

noncomputable section

namespace LG2021.Algorithm

open scoped Classical



private theorem trace_exists_stage_start {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (p : ℕ) :
    ∃ a ≤ p, (traceState cfg K R seed ys a).2.2.2.1 = 0 ∧
      traceStage cfg K R seed ys a = traceStage cfg K R seed ys p := by
  let S := (Finset.range (p + 1)).filter
    (fun j => traceStage cfg K R seed ys j = traceStage cfg K R seed ys p)
  have hp : p ∈ S := by simp [S]
  have hne : S.Nonempty := ⟨p, hp⟩
  let a := S.min' hne
  have ha : a ∈ S := S.min'_mem hne
  have hap : a ≤ p := by
    have h := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
    omega
  refine ⟨a, hap, ?_, (Finset.mem_filter.1 ha).2⟩
  rw [traceState_age_eq_card]
  have hempty : (Finset.range a).filter (fun j => traceStage cfg K R seed ys j =
      traceStage cfg K R seed ys a) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro j hj
    rcases Finset.mem_filter.1 hj with ⟨hja, hjs⟩
    have hjlt : j < a := Finset.mem_range.1 hja
    have hjS : j ∈ S := by
      apply Finset.mem_filter.2
      exact ⟨Finset.mem_range.2 (by omega), hjs.trans (Finset.mem_filter.1 ha).2⟩
    have haj : a ≤ j := S.min'_le j hjS
    omega
  rw [hempty]
  rfl







end LG2021.Algorithm

end
end

/- LG2021ConcentrationActualConfidence -/
section

noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

end
end

/- LG2021ConfidencePrefix -/
section

noncomputable section

namespace LG2021.Algorithm

private theorem traceLocalLoss_prefix_eq {d u n : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : Fin n → ℝ) (τ : ℕ) (hτ : τ ≤ n) (f : Space d → ℝ)
    (p : ℕ) (hp : p ≤ τ / 2) :
    traceLocalLoss cfg K R seed (terminalPairs (observationPrefix ys τ hτ)) f p =
      traceLocalLoss cfg K R seed (terminalPairs ys) f p := by
  unfold traceLocalLoss
  rw [terminalTrace_prefix_eq cfg K R seed ys τ hτ hp]





private theorem traceGap_prefix_eq {d u n : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : Fin n → ℝ) (τ : ℕ) (hτ : τ ≤ n) (f : Space d → ℝ)
    (p : ℕ) (hp : p ≤ τ / 2) (s : Fin u) :
    traceGap cfg K R seed (terminalPairs (observationPrefix ys τ hτ)) f p s =
      traceGap cfg K R seed (terminalPairs ys) f p s := by
  unfold traceGap
  rw [traceLocalLoss_prefix_eq cfg K R seed ys τ hτ f p hp,
    terminalTrace_prefix_eq cfg K R seed ys τ hτ hp]



end LG2021.Algorithm

end
end

/- LG2021WinnerSamples -/
section

noncomputable section

namespace LG2021.Algorithm



end LG2021.Algorithm

end
end

/- LG2021ConcentrationGoodHistory -/
section

noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

end
end

/- LG2021ConcentrationConfidenceEvent -/
section

noncomputable section
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



private theorem measurableSet_estimatorGood {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (F : Space d → ℝ) (γ : ℝ)
    (hν : NoiseCond K F γ ν) (N : ℕ) (v : Fin (d+1) → Space d) :
    MeasurableSet (estimatorGood (u := u) cfg K hK R anchor ν hνm N v) :=
  (measurableSet_scalarStageFailure cfg K hK R anchor ha ν hνm F γ hν N _).compl.inter
    (measurableSet_gradientStageFailure cfg K hK R anchor ha ν hνm F γ hν N _ v).compl





end LG2021.Concentration

end
end

/- LG2021ConcentrationCandidateCoordinates -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal




























end LG2021.Concentration

end
end

/- LG2021CurrentConfidence -/
section

noncomputable section

namespace LG2021.Algorithm

set_option maxHeartbeats 1000000

private theorem trace_candidate_gap_eq_of_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (f : Space d → ℝ) (s : Fin u) {p q : ℕ}
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys q) :
    traceGap cfg K R seed ys f p s = traceGap cfg K R seed ys f q s := by
  have hcore := traceCore_eq_of_same_stage cfg K R seed ys hstage
  have hframe : (traceState cfg K R seed ys p).2.1 = (traceState cfg K R seed ys q).2.1 :=
    congrArg (fun z : Frame d × (Fin u → Space d) => z.1) hcore
  have hcand : (traceState cfg K R seed ys p).2.2.1 = (traceState cfg K R seed ys q).2.2.1 :=
    congrArg (fun z : Frame d × (Fin u → Space d) => z.2) hcore
  unfold traceGap traceLocalLoss
  rw [hframe, hcand]



end LG2021.Algorithm

end
end

/- LG2021FinalRateAlgebra -/
section

noncomputable section

namespace LG2021.Algorithm













end LG2021.Algorithm

end
end

/- LG2021CandidateHitGeometry -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm

open Set MeasureTheory Concentration
open scoped Classical



private theorem measurable_frameCandidateGap {d : ℕ} (lambda : ℝ) {L : Space d → ℝ}
    (hL : Continuous L) : Measurable (fun w : Frame d × Space d => frameCandidateGap lambda L w.1 w.2) := by
  have hm : Measurable (fun w : Frame d × Space d => L (frameApply w.1 w.2)) :=
    hL.measurable.comp (continuous_frameApply (d := d)).measurable
  have hmean : Measurable (fun w : Frame d × Space d =>
      gaussianMean (fun x => L (frameApply w.1 x))) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable.comp measurable_fst
  have hint : Measurable (fun w : (Frame d × Space d) × Space d =>
      L (frameApply w.1.1 ((1-lambda) • w.2 + lambda • w.1.2))) := by
    have hp : Measurable (fun w : (Frame d × Space d) × Space d =>
        (w.1.1, (1-lambda) • w.2 + lambda • w.1.2)) := by fun_prop
    simpa only [Function.comp_def] using hm.comp hp
  have hcenter : Measurable (fun w : Frame d × Space d => L (frameApply w.1 0)) := by
    have hp : Measurable (fun w : Frame d × Space d => (w.1, (0 : Space d))) := by fun_prop
    simpa only [Function.comp_def] using hm.comp hp
  unfold frameCandidateGap surrogate
  exact (hmean.add ((hint.stronglyMeasurable.integral_prod_right'.measurable.sub hmean).div_const lambda)).sub hcenter











end LG2021.Algorithm

end
end

/- LG2021CandidateHitEvent -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm

open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal Classical







private theorem measurableSet_candidateStartValid {d u T : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (xstar : Space d) (p : ℕ) :
    MeasurableSet {w : Seed d u cfg.horizon × (Fin T → ℝ) | candidateStartValid cfg K R xstar p w} := by
  have hst := measurable_terminalTraceState (u := u) (N := T) cfg K R p
  have hb : MeasurableSet {cuts : Fin p → CutCode d |
      (interior (codedBody K cuts)).Nonempty ∧ xstar ∈ codedBody K cuts} :=
    (Set.to_countable _).measurableSet
  exact (measurableSet_eq_fun hst.snd.snd.snd.fst measurable_const).inter (hb.preimage hst.fst)

private theorem measurableSet_candidateHit {d u T : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) {L : Space d → ℝ} (hL : Continuous L) (xstar : Space d) (p : ℕ) :
    MeasurableSet {w : Seed d u cfg.horizon × (Fin T → ℝ) | candidateHit cfg K R L xstar p w} := by
  have hst := measurable_terminalTraceState (u := u) (N := T) cfg K R p
  have hgap := (measurable_frameGap hL xstar).comp hst.snd.fst
  have hscalar (s : Fin u) : Measurable (fun w : Seed d u cfg.horizon × (Fin T → ℝ) =>
      traceGap cfg K R w.1 (terminalPairs w.2) L p s) := by
    unfold traceGap traceLocalLoss
    simpa only [Function.comp_def, frameCandidateGap] using
      (measurable_frameCandidateGap cfg.lambda hL).comp
        (hst.snd.fst.prodMk ((measurable_pi_apply s).comp hst.snd.snd.fst))
  have he : {w : Seed d u cfg.horizon × (Fin T → ℝ) | candidateHit cfg K R L xstar p w} =
      ⋃ s : Fin u, {w | (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p -
        1/(cfg.horizon : ℝ))/separationFactor d ≤ traceGap cfg K R w.1 (terminalPairs w.2) L p s} := by
    ext w
    simp only [candidateHit, mem_iUnion, mem_setOf_eq]
  rw [he]
  exact MeasurableSet.iUnion (fun s => measurableSet_le ((hgap.sub_const _).div_const _) (hscalar s))

private theorem measurableSet_candidateStartFailure {d u T : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) {L : Space d → ℝ} (hL : Continuous L) (xstar : Space d) (p : ℕ) :
    MeasurableSet (candidateStartFailure (u := u) (T := T) cfg K R L xstar p) :=
  (measurableSet_candidateStartValid cfg K R xstar p).inter
    (measurableSet_candidateHit cfg K R hL xstar p).compl









end LG2021.Algorithm

end
end

/- LG2021CandidateNormSupport -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal



private theorem measurableSet_candidateSeedGood {d u : ℕ} (cfg : OracleConfig) :
    MeasurableSet {seed : Seed d u cfg.horizon | candidateSeedGood cfg seed} := by
  simp only [candidateSeedGood, setOf_forall]
  exact MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun s =>
    measurableSet_le (by fun_prop) measurable_const))



private theorem candidateSeedGood_norm_all {d u : ℕ} (cfg : OracleConfig) {seed : Seed d u cfg.horizon}
    (hr : 0 ≤ cfg.radius) (hs : candidateSeedGood cfg seed) :
    ∀ p s, ‖seedCandidates seed p s‖ ≤ cfg.radius/(2*(d : ℝ)) := by
  intro p s
  unfold seedCandidates
  split_ifs with hp
  · exact hs ⟨p,hp⟩ s
  · simpa using (div_nonneg hr (by positivity : (0 : ℝ) ≤ 2*(d : ℝ)))



end LG2021.Algorithm

end
end

/- LG2021CandidateHitTerminal -/
section

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal Classical





private theorem candidateTerminalGood_compl {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (L : Space d → ℝ) (xstar : Space d) :
    (candidateTerminalGood (N := N) (u := u) cfg K R L xstar)ᶜ =
      ⋃ p : Fin (N+1), candidateStartFailure (T := 2*N) cfg K R L xstar p := by
  ext w
  simp only [candidateTerminalGood, candidateStartFailure, mem_compl_iff, mem_setOf_eq, mem_iUnion]
  push_neg
  constructor
  · rintro ⟨p, hp, hv, hh⟩
    exact ⟨⟨p, by omega⟩, hv, hh⟩
  · rintro ⟨p, hv, hh⟩
    exact ⟨p, by omega, hv, hh⟩

private theorem measurableSet_candidateTerminalGood {d u N : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) {L : Space d → ℝ} (hL : Continuous L) (xstar : Space d) :
    MeasurableSet (candidateTerminalGood (N := N) (u := u) cfg K R L xstar) := by
  apply MeasurableSet.of_compl
  rw [candidateTerminalGood_compl]
  exact MeasurableSet.iUnion (fun p => measurableSet_candidateStartFailure cfg K R hL xstar p)



private theorem candidate_hits_propagate {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (L : Space d → ℝ) (xstar : Space d) (w : Seed d u cfg.horizon × (Fin (2*N) → ℝ))
    (hg : w ∈ candidateTerminalGood cfg K R L xstar)
    (hi : ∀ p ≤ N, (interior (codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1)).Nonempty)
    (hx : ∀ p ≤ N, xstar ∈ codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1) :
    ∀ p ≤ N, ∃ s : Fin u,
      (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p-1/(cfg.horizon : ℝ))/separationFactor d ≤
        traceGap cfg K R w.1 (terminalPairs w.2) L p s := by
  intro p hp
  obtain ⟨a, hap, ha, hstage⟩ := trace_exists_stage_start cfg K R w.1 (terminalPairs w.2) p
  obtain ⟨s, hs⟩ := hg a (hap.trans hp) ⟨ha, hi a (hap.trans hp), hx a (hap.trans hp)⟩
  refine ⟨s, ?_⟩
  rw [trace_candidate_gap_eq_of_same_stage cfg K R w.1 (terminalPairs w.2) L s hstage,
    traceComparatorGap_eq_of_same_stage cfg K R w.1 (terminalPairs w.2) L xstar hstage] at hs
  exact hs



private theorem measurableSet_candidateTerminalEvent {d u N : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) {L : Space d → ℝ} (hL : Continuous L) (xstar : Space d) :
    MeasurableSet (candidateTerminalEvent (N := N) (u := u) cfg K R L xstar) :=
  (measurableSet_candidateTerminalGood cfg K R hL xstar).inter
    ((measurableSet_candidateSeedGood cfg).preimage measurable_fst)



private theorem candidate_failure_budget_le_inverse {n N : ℕ} (hn : 1 ≤ n) (hN : N ≤ n) :
    ((N : ℝ)+1)/(3*(n : ℝ)^2) ≤ 1/(n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hNR : (N : ℝ) ≤ n := by exact_mod_cast hN
  apply (div_le_div_iff₀ (by positivity : 0 < 3*(n : ℝ)^2) (by linarith : (0 : ℝ) < n)).mpr
  nlinarith

end LG2021.Algorithm

end
end

/- LG2021CandidateHitLift -/
section

noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration

private theorem traceComparatorGap_prefix_eq {d u n : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : Fin n → ℝ) (T : ℕ) (hT : T ≤ n) (L : Space d → ℝ) (xstar : Space d)
    (p : ℕ) (hp : p ≤ T/2) :
    traceComparatorGap cfg K R seed (terminalPairs (observationPrefix ys T hT)) L xstar p =
      traceComparatorGap cfg K R seed (terminalPairs ys) L xstar p := by
  unfold traceComparatorGap
  rw [terminalTrace_prefix_eq cfg K R seed ys T hT hp]

private theorem candidate_hits_propagate_prefix {d u n N : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (L : Space d → ℝ) (xstar : Space d)
    (w : Seed d u cfg.horizon × (Fin n → ℝ)) (hpair : 2*N ≤ n)
    (hgood : historyPrefix hpair w ∈ candidateTerminalGood cfg K R L xstar)
    (hi : ∀ p ≤ N, (interior (codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1)).Nonempty)
    (hx : ∀ p ≤ N, xstar ∈ codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1) :
    ∀ p ≤ N, ∃ s : Fin u,
      (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p-1/(cfg.horizon : ℝ))/separationFactor d ≤
        traceGap cfg K R w.1 (terminalPairs w.2) L p s := by
  have hstate (p : ℕ) (hp : p ≤ N) :
      traceState cfg K R w.1 (terminalPairs (observationPrefix w.2 (2*N) hpair)) p =
        traceState cfg K R w.1 (terminalPairs w.2) p :=
    terminalTrace_prefix_eq cfg K R w.1 w.2 (2*N) hpair (by omega)
  have hhit := candidate_hits_propagate cfg K R L xstar (historyPrefix hpair w) hgood
    (by
      intro p hp
      change (interior (codedBody K (traceState cfg K R w.1
        (terminalPairs (observationPrefix w.2 (2*N) hpair)) p).1)).Nonempty
      rw [hstate p hp]
      exact hi p hp)
    (by
      intro p hp
      change xstar ∈ codedBody K (traceState cfg K R w.1
        (terminalPairs (observationPrefix w.2 (2*N) hpair)) p).1
      rw [hstate p hp]
      exact hx p hp)
  intro p hp
  obtain ⟨s, hs⟩ := hhit p hp
  refine ⟨s, ?_⟩
  change (traceComparatorGap cfg K R w.1 (terminalPairs (observationPrefix w.2 (2*N) hpair)) L xstar p -
    1/(cfg.horizon : ℝ))/separationFactor d ≤
      traceGap cfg K R w.1 (terminalPairs (observationPrefix w.2 (2*N) hpair)) L p s at hs
  rw [traceComparatorGap_prefix_eq cfg K R w.1 w.2 (2*N) hpair L xstar p (by omega),
    traceGap_prefix_eq cfg K R w.1 w.2 (2*N) hpair L p (by omega) s] at hs
  exact hs



end LG2021.Algorithm

end
end

/- LG2021PairLossMartingale -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical

















end LG2021.Concentration

end
end

/- LG2021PairLossTerminal -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical

























end LG2021.Concentration

end
end

/- LG2021PairLossTrace -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical







end LG2021.Concentration

end
end

/- LG2021ConcentrationTerminalGood -/
section

noncomputable section
set_option maxHeartbeats 1500000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory







end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory



end LG2021.Concentration

end
end

/- LG2021ComparatorNonneg -/
section

noncomputable section

namespace LG2021.Algorithm





end LG2021.Algorithm

end
end

/- LG2021PathwiseRegret -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration









end LG2021.Algorithm

end
end

/- LG2021DeterministicClosure -/
section

noncomputable section
set_option maxHeartbeats 1000000

namespace LG2021.Algorithm

open MeasureTheory Concentration Set



end LG2021.Algorithm

end
end

/- LG2021ExpectedRegret -/
section

noncomputable section

namespace LG2021

open MeasureTheory BilateralProfitMHR
open scoped ENNReal









end LG2021

end
end

/- LG2021CanonicalExpectedRegret -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Concentration
open scoped ENNReal









end LG2021.Algorithm

end
end

/- Canonical fixed-dimensional bandit theorem -/
section

noncomputable section
set_option maxHeartbeats 2000000

namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open Algorithm Concentration Set Metric






end LG2021

end
end

/- LG2021LipschitzExtension -/
section

/-!
The global extension needed only in the analysis of the bandit policy.
The infimal-convolution construction follows the existing real Lipschitz
extension proof in Mathlib; compact convexity additionally preserves convexity.
The infimal-convolution formulation supplies the global extension used in the formal proof.
-/

noncomputable section

namespace LG2021

open Set
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]













end LG2021

end
end

/- LG2021Erosion -/
section

/-!
The known-body erosion used in Appendix F of Lattimore and György (2021).
The interior Lipschitz proof adapts Mathlib's convex secant argument, using
the loss range [0,1] to obtain the exact constant. The loss and its extension
are analysis objects; the eroded body uses only the known body and scale.
-/

noncomputable section
namespace LG2021

open Set Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]









































end LG2021

end
end

/- CorollaryTransport -/
section

namespace BilateralProfitMHR.CorollaryTransport

open MeasureTheory
open scoped ENNReal











section Geometry

variable {X Y Ω : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]















end Geometry



section Observations

variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]











end Observations

end BilateralProfitMHR.CorollaryTransport

end

/- CorollaryNormalization -/
section

namespace BilateralProfitMHR.CorollaryTransport

open MeasureTheory
open scoped ENNReal

























end BilateralProfitMHR.CorollaryTransport

end

/- LG2021ErosionTransport -/
section

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal







variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]





end LG2021

end
end

/- LG2021Reduction -/
section

namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open scoped ENNReal



















end LG2021

end

/- LG2021CanonicalTransport -/
section

/-! Quantifier-preserving reduction from the canonical Lipschitz problem to
continuous convex losses, arbitrary affine dimension, and the stated noise norm.
The reduction preserves the choice of policy before the unknown loss and noise. -/

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal








end LG2021

end
end

/- LG2021NormalizedTransport -/
section

noncomputable section

namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric



end LG2021

end
end

/- LG2021SharpClosure -/
section

noncomputable section
set_option maxHeartbeats 2000000
namespace LG2021.Algorithm
open MeasureTheory Concentration Set







end LG2021.Algorithm

end
end

/- LG2021SharpRateBase -/
section

noncomputable section

namespace LG2021

open Concentration

































end LG2021

end
end

/- LG2021SharpRateAlgebra -/
section

noncomputable section

namespace LG2021.Algorithm

open Concentration






















end LG2021.Algorithm

end
end

section
namespace LG2021.Algorithm

end LG2021.Algorithm
end

/- LG2021SharpStageRate -/
section

noncomputable section

namespace LG2021.Algorithm

open Set MeasureTheory Concentration










end LG2021.Algorithm

end
end

/- LG2021SharpTransport -/
section

/-!
Transport of the explicit universal dimension bound through Lipschitz extension
and the known-body erosion. The comparator is an infimum, so the convex loss
need not be continuous at the boundary of its domain.
-/

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal











section Erosion

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]





end Erosion





end LG2021

end
end

/- LG2021SharpRateFixed -/
section

noncomputable section

namespace LG2021










end LG2021

end
end

/- LG2021SharpSourceTransport -/
section

/-!
The explicit source rate for arbitrary locations of the contained unit ball.
The loss comparator is its infimum on the compact action set; whenever the
minimum is attained this equals the source's minimum comparator.
-/

noncomputable section
namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal

















end LG2021

end
end

/- LG2021SharpMain -/
section

noncomputable section
set_option maxHeartbeats 2000000

namespace LG2021

open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open Algorithm Concentration Set Metric








end LG2021

end
end

open LG2021 MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric



open LG2021 LG2021.Algorithm LG2021.Concentration BilateralProfitMHR MeasureTheory ProbabilityTheory

theorem solution {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (F : Space d → ℝ) (hLip : LipschitzWith 1 F) (hconv : ConvexOn ℝ Set.univ F)
    (hF : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1) (xstar : Space d) (hxstar : xstar ∈ K)
    (v : Fin (d+1) → Space d) (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (hν : CorollaryTransport.UnitNoiseCond K F ν) :
    ∃ G : Set (Seed d (candidateCount n) n × (Fin n → ℝ)), MeasurableSet G ∧
      (historyMeasure (policy (u := candidateCount n) (oracleConfig d D n) K hK.isClosed.measurableSet R anchor)
        (seedMeasure d (candidateCount n) (oracleConfig d D n)) ν hνm n).real Gᶜ ≤
          100 * ((d : ℝ)+2) / (n : ℝ) ∧
      ∀ w ∈ G, TerminalGoodFacts (oracleConfig d D n) K hK.isClosed.measurableSet R anchor F xstar v w := by
  let cfg := oracleConfig d D n
  let A := policy (u := candidateCount n) cfg K hK.isClosed.measurableSet R anchor
  let P := seedMeasure d (candidateCount n) cfg
  let μ := historyMeasure A P ν hνm n
  let N := n/2
  have hN : N ≤ n := by dsimp [N]; omega
  have hNpos : 0 < N := by dsimp [N]; omega
  have hpair : 2*N ≤ n := by dsimp [N]; omega
  have hodd : n ≤ 2*N+1 := by dsimp [N]; omega
  have hnoise := CorollaryTransport.unitNoiseCond_noiseCond K F ν hν
  have hA : A.IsOn K := policy_isOn cfg K hK.isClosed.measurableSet R ha
  letI : IsProbabilityMeasure μ := historyMeasure_probability A P ν hνm hA F 1 hnoise n
  have hbounds := oracleConfig_bounds hd hn hD
  have hr : 0 < cfg.radius := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hbounds.1
  have hH : 0 ≤ confidenceLog cfg (candidateCount n) := le_trans (by norm_num : (0 : ℝ) ≤ 1) hbounds.2.2.2.2.2.2
  let E := estimatorGood (u := candidateCount n) cfg K hK.isClosed.measurableSet R anchor ν hνm N v
  let C := candidateTerminalEvent (N := N) (u := candidateCount n) cfg K R F xstar
  have hE : MeasurableSet E := measurableSet_estimatorGood cfg K hK.isClosed.measurableSet R anchor ha ν hνm F 1 hnoise N v
  have hC : MeasurableSet C := measurableSet_candidateTerminalEvent cfg K R hLip.continuous xstar
  have hEp : μ.real ((historyPrefix hpair) ⁻¹' E)ᶜ ≤ 3*((d : ℝ)+2)/(n : ℝ) := by
    change μ.real ((historyPrefix hpair) ⁻¹' Eᶜ) ≤ _
    rw [historyMeasure_prefix_probability A P ν hνm hA F 1 hnoise hpair Eᶜ hE.compl]
    exact estimatorGood_failure_le hd (by omega) (candidateCount_pos (by omega)) hD K hK.isClosed.measurableSet
      R anchor ha ν hνm F hν hF hN v
  have hCp : μ.real ((historyPrefix hpair) ⁻¹' C)ᶜ ≤ 1/(n : ℝ) := by
    change μ.real ((historyPrefix hpair) ⁻¹' Cᶜ) ≤ _
    rw [historyMeasure_prefix_probability A P ν hνm hA F 1 hnoise hpair Cᶜ hC.compl]
    exact (candidateTerminalEvent_failure_le hd hn hN hK hcv hD hdiam R anchor ha F hLip hconv xstar
      ν hνm 1 hnoise).trans (candidate_failure_budget_le_inverse (by omega) hN)
  obtain ⟨G0, hG0, hG0p, hG0good⟩ := terminal_trace_regret_good_event hd cfg hr hK hcv hdiam
    R anchor ha ν hνm F hLip hconv hF 1 hnoise N n (by dsimp [cfg, oracleConfig]; omega)
    hNpos hpair hodd xstar hxstar
  let G := ((historyPrefix hpair) ⁻¹' E) ∩ (((historyPrefix hpair) ⁻¹' C) ∩ G0)
  have hG : MeasurableSet G := (hE.preimage (measurable_historyPrefix hpair)).inter
    ((hC.preimage (measurable_historyPrefix hpair)).inter hG0)
  refine ⟨G, hG, ?_, ?_⟩
  · change μ.real Gᶜ ≤ _
    have hp : μ.real Gᶜ ≤ 3*((d : ℝ)+2)/(n : ℝ) + (1/(n : ℝ)+1/(n : ℝ)) := by
      dsimp [G]
      rw [Set.compl_inter, Set.compl_inter]
      exact (measureReal_union_le _ _).trans (add_le_add hEp
        ((measureReal_union_le _ _).trans (add_le_add hCp hG0p)))
    apply hp.trans
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ d by positivity]) hnR.le
  · intro w hw
    have hge : historyPrefix hpair w ∈ E := hw.1
    have hgc : historyPrefix hpair w ∈ C := hw.2.1
    have hseed := candidateSeedGood_norm_all cfg hr.le hgc.2
    refine ⟨hseed, ?_, ?_, ?_, ?_⟩
    · exact estimatorGood_full_scalar hd (by omega) hD hK hcv hdiam R anchor ha ν hνm F hLip hF hν hN hpair w v hseed hge
    · exact estimatorGood_full_gradient hd (by omega) hD hK hcv hdiam R anchor ha ν hνm F hLip hconv hF hν hN hpair w v hH hseed hge
    · exact candidate_hits_propagate_prefix cfg K R F xstar w hpair hgc.1
    · exact hG0good w hw.2.2
