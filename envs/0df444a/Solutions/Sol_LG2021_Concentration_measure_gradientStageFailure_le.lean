-- Prove2me | solution 1 for LG2021.Concentration.measure_gradientStageFailure_le
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T16:43:35.872489+00:00
-- url     : https://prove2.me/submissions/d7a4991d-19e9-4a2b-941e-56df094ffe33

import Definitions.Def_LG2021_Policy
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

/-- A global second-order upper bound for the real exponential. -/
private theorem exp_le_one_add_add_sq_mul_exp_abs (x : ℝ) :
    Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  norm_num [Finset.sum_range_succ, ← Complex.ofReal_exp, ← Complex.ofReal_sub,
    ← Complex.ofReal_add, ← Complex.ofReal_one, ← Complex.ofReal_pow,
    Complex.norm_real, Real.norm_eq_abs] at h
  have h' : Real.exp x - (1 + x) ≤ x ^ 2 * Real.exp |x| :=
    (le_abs_self _).trans h
  linarith




















end LG2021.Concentration

end

/- LG2021ConcentrationProducts -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- Exponential-square envelopes control a product without an independence hypothesis. -/
private theorem exp_abs_mul_le_average_exp_sq (u v : ℝ) :
    Real.exp |u * v| ≤ (Real.exp (u ^ 2) + Real.exp (v ^ 2)) / 2 := by
  have harg : |u * v| ≤ (u ^ 2 + v ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|u| - |v|), sq_abs u, sq_abs v]
  have hconv := convexOn_exp.2 (Set.mem_univ (u ^ 2)) (Set.mem_univ (v ^ 2))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hconv
  calc
    _ ≤ Real.exp ((u ^ 2 + v ^ 2) / 2) := Real.exp_le_exp.mpr harg
    _ = Real.exp ((1 / 2) * u ^ 2 + (1 / 2) * v ^ 2) := by congr 1; ring
    _ ≤ (1 / 2) * Real.exp (u ^ 2) + (1 / 2) * Real.exp (v ^ 2) := hconv
    _ = _ := by ring

/-- Two exponential-square bounds give an exponential-absolute moment for their product. -/
private theorem exp_abs_product_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXI : Integrable (fun ω => Real.exp ((X ω) ^ 2)) P)
    (hYI : Integrable (fun ω => Real.exp ((Y ω) ^ 2)) P)
    (hXM : (∫ ω, Real.exp ((X ω) ^ 2) ∂P) ≤ 2)
    (hYM : (∫ ω, Real.exp ((Y ω) ^ 2) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp |X ω * Y ω|) P ∧
      (∫ ω, Real.exp |X ω * Y ω| ∂P) ≤ 2 := by
  have hJ := (hXI.add hYI).div_const 2
  have hI : Integrable (fun ω => Real.exp |X ω * Y ω|) P := by
    apply hJ.mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.add_apply] using
        exp_abs_mul_le_average_exp_sq (X ω) (Y ω)
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ ω, (Real.exp ((X ω) ^ 2) + Real.exp ((Y ω) ^ 2)) / 2 ∂P :=
      integral_mono hI hJ (fun ω => exp_abs_mul_le_average_exp_sq (X ω) (Y ω))
    _ = ((∫ ω, Real.exp ((X ω) ^ 2) ∂P) +
        (∫ ω, Real.exp ((Y ω) ^ 2) ∂P)) / 2 := by
      rw [integral_div, integral_add hXI hYI]
    _ ≤ 2 := by linarith

/-- The product estimate at arbitrary positive radii. -/
private theorem exp_abs_product_moment_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hXI : Integrable (fun ω => Real.exp ((X ω) ^ 2 / a ^ 2)) P)
    (hYI : Integrable (fun ω => Real.exp ((Y ω) ^ 2 / b ^ 2)) P)
    (hXM : (∫ ω, Real.exp ((X ω) ^ 2 / a ^ 2) ∂P) ≤ 2)
    (hYM : (∫ ω, Real.exp ((Y ω) ^ 2 / b ^ 2) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp (|X ω * Y ω| / (a * b))) P ∧
      (∫ ω, Real.exp (|X ω * Y ω| / (a * b)) ∂P) ≤ 2 := by
  have h := exp_abs_product_moment P (fun ω => X ω / a) (fun ω => Y ω / b)
    (hX.div_const a) (hY.div_const b)
    (by simpa only [div_pow] using hXI) (by simpa only [div_pow] using hYI)
    (by simpa only [div_pow] using hXM) (by simpa only [div_pow] using hYM)
  simpa only [div_mul_div_comm, abs_div, abs_of_pos (mul_pos ha hb)] using h

/-- A bounded parameter leaves enough exponential integrability to absorb a quadratic factor. -/
private theorem sq_mul_exp_abs_le_exp_abs (v s : ℝ) (hs : |s| ≤ 1 / 2) :
    v ^ 2 * Real.exp |s * v| ≤ 8 * Real.exp |v| := by
  have hpow : v ^ 2 ≤ 8 * Real.exp (|v| / 2) := by
    have h := Real.quadratic_le_exp_of_nonneg (show 0 ≤ |v| / 2 by positivity)
    nlinarith [sq_abs v, abs_nonneg v]
  have harg : |s * v| ≤ |v| / 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_right hs (abs_nonneg v)]
  calc
    _ ≤ (8 * Real.exp (|v| / 2)) * Real.exp (|v| / 2) :=
      mul_le_mul hpow (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (by positivity)
    _ = 8 * Real.exp |v| := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Centered exponential-absolute moments yield a quadratic MGF bound on a fixed interval. -/
private theorem mgf_le_of_exp_abs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hI : Integrable (fun ω => Real.exp |X ω|) P)
    (hM : (∫ ω, Real.exp |X ω| ∂P) ≤ 2)
    (hzero : (∫ ω, X ω ∂P) = 0)
    {s : ℝ} (hs : |s| ≤ 1 / 2) :
    Integrable (fun ω => Real.exp (s * X ω)) P ∧
      mgf X P s ≤ Real.exp (16 * s ^ 2) := by
  have hXI : Integrable X P := by
    apply hI.mono' hX.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      have h := Real.add_one_le_exp |X ω|
      linarith
  have hEI : Integrable (fun ω => Real.exp (s * X ω)) P := by
    apply hI.mono' (by fun_prop)
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hs (abs_nonneg (X ω))
    have hle := le_abs_self (s * X ω)
    rw [abs_mul] at hle
    nlinarith [abs_nonneg (X ω)]
  have hJ : Integrable (fun ω => 1 + s * X ω + 8 * s ^ 2 * Real.exp |X ω|) P :=
    ((integrable_const 1).add (hXI.const_mul s)).add (hI.const_mul (8 * s ^ 2))
  refine ⟨hEI, ?_⟩
  change (∫ ω, Real.exp (s * X ω) ∂P) ≤ _
  calc
    _ ≤ ∫ ω, 1 + s * X ω + 8 * s ^ 2 * Real.exp |X ω| ∂P := by
      apply integral_mono hEI hJ
      intro ω
      have h := exp_le_one_add_add_sq_mul_exp_abs (s * X ω)
      have h' := mul_le_mul_of_nonneg_left (sq_mul_exp_abs_le_exp_abs (X ω) s hs)
        (sq_nonneg s)
      nlinarith
    _ = 1 + 8 * s ^ 2 * (∫ ω, Real.exp |X ω| ∂P) := by
      have hA : Integrable (fun ω => 1 + s * X ω) P :=
        (integrable_const 1).add (hXI.const_mul s)
      rw [integral_add hA
        (hI.const_mul (8 * s ^ 2)), integral_add (integrable_const 1) (hXI.const_mul s)]
      simp [integral_const_mul, hzero]
    _ ≤ 1 + 16 * s ^ 2 := by nlinarith [sq_nonneg s]
    _ ≤ Real.exp (16 * s ^ 2) := by simpa [add_comm] using Real.add_one_le_exp (16 * s ^ 2)


/-- The bounded-parameter MGF estimate after a positive change of scale. -/
private theorem mgf_le_of_exp_abs_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {r : ℝ} (hr : 0 < r)
    (hI : Integrable (fun ω => Real.exp (|X ω| / r)) P)
    (hM : (∫ ω, Real.exp (|X ω| / r) ∂P) ≤ 2)
    (hzero : (∫ ω, X ω ∂P) = 0)
    {t : ℝ} (ht : |t| * r ≤ 1 / 2) :
    Integrable (fun ω => Real.exp (t * X ω)) P ∧
      mgf X P t ≤ Real.exp (16 * r ^ 2 * t ^ 2) := by
  have h := mgf_le_of_exp_abs P (fun ω => X ω / r) (hX.div_const r)
    (by simpa only [abs_div, abs_of_pos hr] using hI)
    (by simpa only [abs_div, abs_of_pos hr] using hM)
    (by simp [integral_div, hzero])
    (s := t * r) (by simpa only [abs_mul, abs_of_pos hr] using ht)
  have heq : (fun ω => Real.exp ((t * r) * (X ω / r))) =
      (fun ω => Real.exp (t * X ω)) := by
    funext ω
    congr 1
    field_simp [ne_of_gt hr]
  refine ⟨heq ▸ h.1, ?_⟩
  have hb := h.2
  change (∫ ω, Real.exp ((t * r) * (X ω / r)) ∂P) ≤ _ at hb
  rw [heq] at hb
  change (∫ ω, Real.exp (t * X ω) ∂P) ≤ _
  convert hb using 1 <;> ring_nf


end LG2021.Concentration

end

/- LG2021ConcentrationCentering -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- Exponential-absolute moments control the first absolute moment. -/
private theorem integral_abs_le_one_of_exp_abs {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hI : Integrable (fun ω => Real.exp |X ω|) P)
    (hM : (∫ ω, Real.exp |X ω| ∂P) ≤ 2) :
    Integrable X P ∧ (∫ ω, |X ω| ∂P) ≤ 1 ∧ |∫ ω, X ω ∂P| ≤ 1 := by
  have hXI : Integrable X P := by
    apply hI.mono' hX.aestronglyMeasurable
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    have := Real.add_one_le_exp |X ω|
    linarith
  have hXA : Integrable (fun ω => |X ω|) P := hXI.abs
  have hA : (∫ ω, |X ω| ∂P) ≤ 1 := by
    have hJA : Integrable (fun ω => 1 + |X ω|) P := (integrable_const 1).add hXA
    have h := integral_mono hJA hI
      (fun ω => by simpa only [add_comm] using Real.add_one_le_exp |X ω|)
    rw [integral_add (integrable_const 1) hXA] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    linarith
  refine ⟨hXI, hA, ?_⟩
  have h := norm_integral_le_integral_norm (μ := P) X
  simp only [Real.norm_eq_abs] at h
  exact h.trans hA

/-- A pointwise envelope for the centered exponential-absolute moment. -/
private theorem exp_abs_sub_quarter_le (x a : ℝ) (ha : |a| ≤ 1) :
    Real.exp (|x - a| / 4) ≤ (4 / 3) * (3 / 4 + Real.exp |x| / 4) := by
  have harg : |x - a| / 4 ≤ |x| / 4 + 1 / 4 := by
    have := abs_sub x a
    linarith
  have hquarter : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ |x|)
    (show (0 : ℝ) ≤ 3 / 4 by norm_num) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have hconv' : Real.exp (|x| / 4) ≤ 3 / 4 + Real.exp |x| / 4 := by
    have heq1 : (1 / 4 : ℝ) * |x| = |x| / 4 := by ring
    have heq2 : (1 / 4 : ℝ) * Real.exp |x| = Real.exp |x| / 4 := by ring
    simpa only [heq1, heq2] using hconv
  calc
    _ ≤ Real.exp (|x| / 4 + 1 / 4) := Real.exp_le_exp.mpr harg
    _ = Real.exp (|x| / 4) * Real.exp (1 / 4) := Real.exp_add _ _
    _ ≤ (3 / 4 + Real.exp |x| / 4) * (4 / 3) :=
      mul_le_mul hconv' hquarter (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Centering costs at most a factor four in the exponential-absolute scale. -/
private theorem exp_abs_centered_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hI : Integrable (fun ω => Real.exp |X ω|) P)
    (hM : (∫ ω, Real.exp |X ω| ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp (|X ω - ∫ a, X a ∂P| / 4)) P ∧
      (∫ ω, Real.exp (|X ω - ∫ a, X a ∂P| / 4) ∂P) ≤ 2 ∧
      (∫ ω, (X ω - ∫ a, X a ∂P) ∂P) = 0 := by
  obtain ⟨hXI, _, hmean⟩ := integral_abs_le_one_of_exp_abs P X hX hI hM
  have hJ : Integrable (fun ω => (4 / 3) * (3 / 4 + Real.exp |X ω| / 4)) P :=
    ((integrable_const (3 / 4 : ℝ)).add (hI.div_const 4)).const_mul (4 / 3)
  have hEI : Integrable (fun ω => Real.exp (|X ω - ∫ a, X a ∂P| / 4)) P := by
    apply hJ.mono' (by fun_prop)
    refine Filter.Eventually.of_forall fun ω => ?_
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      exp_abs_sub_quarter_le (X ω) (∫ a, X a ∂P) hmean
  refine ⟨hEI, ?_, ?_⟩
  · calc
      _ ≤ ∫ ω, (4 / 3) * (3 / 4 + Real.exp |X ω| / 4) ∂P :=
        integral_mono hEI hJ (fun ω => exp_abs_sub_quarter_le (X ω) _ hmean)
      _ = (4 / 3) * (3 / 4 + (∫ ω, Real.exp |X ω| ∂P) / 4) := by
        rw [integral_const_mul, integral_add (integrable_const (3 / 4 : ℝ)) (hI.div_const 4)]
        simp [integral_div]
      _ ≤ 2 := by linarith
  · rw [integral_sub hXI (integrable_const _)]
    simp


/-- Centering at an arbitrary exponential-absolute radius. -/
private theorem exp_abs_centered_moment_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {r : ℝ} (hr : 0 < r)
    (hI : Integrable (fun ω => Real.exp (|X ω| / r)) P)
    (hM : (∫ ω, Real.exp (|X ω| / r) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp (|X ω - ∫ a, X a ∂P| / (4 * r))) P ∧
      (∫ ω, Real.exp (|X ω - ∫ a, X a ∂P| / (4 * r)) ∂P) ≤ 2 ∧
      (∫ ω, (X ω - ∫ a, X a ∂P) ∂P) = 0 := by
  have hI' : Integrable (fun ω => Real.exp |X ω / r|) P := by
    simpa only [abs_div, abs_of_pos hr] using hI
  have hM' : (∫ ω, Real.exp |X ω / r| ∂P) ≤ 2 := by
    simpa only [abs_div, abs_of_pos hr] using hM
  have h := exp_abs_centered_moment P (fun ω => X ω / r) (hX.div_const r) hI' hM'
  have heq : (fun ω => Real.exp (|X ω / r - ∫ a, X a / r ∂P| / 4)) =
      (fun ω => Real.exp (|X ω - ∫ a, X a ∂P| / (4 * r))) := by
    funext ω
    rw [integral_div, ← sub_div, abs_div, abs_of_pos hr]
    congr 1
    ring
  refine ⟨heq ▸ h.1, heq ▸ h.2.1, ?_⟩
  have hXI' := (integral_abs_le_one_of_exp_abs P (fun ω => X ω / r)
    (hX.div_const r) hI' hM').1.const_mul r
  have hfun : (fun ω => r * (X ω / r)) = X := by
    funext ω
    field_simp [ne_of_gt hr]
  rw [hfun] at hXI'
  rw [integral_sub hXI' (integrable_const _)]
  simp


end LG2021.Concentration

end

/- LG2021ConcentrationEstimators -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

private theorem likelihoodRatio_nonneg {d : ℕ} {lambda : ℝ} (hlambda : lambda < 1)
    (z x : Space d) : 0 ≤ likelihoodRatio lambda z x := by
  unfold likelihoodRatio
  positivity

private theorem truncation_zero_or_one {d : ℕ} (lambda r : ℝ) (z x : Space d) :
    truncation lambda r z x = 0 ∨ truncation lambda r z x = 1 := by
  unfold truncation
  split_ifs <;> simp

private theorem truncation_eq_one_iff {d : ℕ} (lambda r : ℝ) (z x : Space d) :
    truncation lambda r z x = 1 ↔
      likelihoodRatio lambda z x ≤ Real.exp 1 / (1 - lambda) ^ d ∧
      ‖x‖ ≤ r / (d : ℝ) := by
  unfold truncation
  split_ifs <;> simp_all

/-- Bernoulli's inequality bounds the likelihood-ratio cutoff uniformly in dimension. -/
private theorem likelihood_cutoff_le_six {d : ℕ} {lambda : ℝ}
    (hlambda : 0 ≤ lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2) :
    Real.exp 1 / (1 - lambda) ^ d ≤ 6 := by
  have hpow : (1 / 2 : ℝ) ≤ (1 - lambda) ^ d := by
    have h := one_add_mul_le_pow (a := -lambda) (by linarith : (-2 : ℝ) ≤ -lambda) d
    simp only [mul_neg, ← sub_eq_add_neg] at h
    linarith
  apply (div_le_iff₀ (by positivity : 0 < (1 - lambda) ^ d)).2
  have hexp := Real.exp_one_lt_three
  nlinarith



/-- The directional multiplier retains the one-dimensional Gaussian projection. -/
private theorem abs_gradientWeight_le {d : ℕ} {lambda : ℝ}
    (r : ℝ) (z x : Space d) (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2)
    (hd : (d : ℝ) * lambda ≤ 1 / 2) :
    |likelihoodRatio lambda z x * truncation lambda r z x / (1 - lambda) ^ 2| ≤ 24 := by
  have hR := likelihoodRatio_nonneg (show lambda < 1 by linarith) z x
  rcases truncation_zero_or_one lambda r z x with hI | hI
  · simp [hI]
  · have hRmax := ((truncation_eq_one_iff lambda r z x).1 hI).1
    have hR6 := hRmax.trans (likelihood_cutoff_le_six hpos.le hsmall hd)
    have hden : (1 / 4 : ℝ) ≤ (1 - lambda) ^ 2 := by nlinarith
    simp only [hI, mul_one, abs_of_nonneg (div_nonneg hR (sq_nonneg _))]
    apply (div_le_iff₀ (by positivity : 0 < (1 - lambda) ^ 2)).2
    nlinarith




end LG2021.Concentration

end

/- LG2021ConcentrationObservation -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- A bounded deterministic mean can be added to normalized square-exponential noise. -/
private theorem exp_square_shift_envelope (x a : ℝ) (ha : |a| ≤ 1) :
    Real.exp ((x + a) ^ 2 / 16) ≤ (4 / 3) * (3 / 4 + Real.exp (x ^ 2) / 4) := by
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_abs a, abs_nonneg a]
  have harg : (x + a) ^ 2 / 16 ≤ x ^ 2 / 4 + 1 / 4 := by
    nlinarith [sq_nonneg (x - a), sq_nonneg x]
  have hquarter : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (x ^ 2))
    (show (0 : ℝ) ≤ 3 / 4 by norm_num) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (show (3 / 4 : ℝ) + 1 / 4 = 1 by norm_num)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have hconv' : Real.exp (x ^ 2 / 4) ≤ 3 / 4 + Real.exp (x ^ 2) / 4 := by
    have heq1 : (1 / 4 : ℝ) * x ^ 2 = x ^ 2 / 4 := by ring
    have heq2 : (1 / 4 : ℝ) * Real.exp (x ^ 2) = Real.exp (x ^ 2) / 4 := by ring
    simpa only [heq1, heq2] using hconv
  calc
    _ ≤ Real.exp (x ^ 2 / 4 + 1 / 4) := Real.exp_le_exp.mpr harg
    _ = Real.exp (x ^ 2 / 4) * Real.exp (1 / 4) := Real.exp_add _ _
    _ ≤ (3 / 4 + Real.exp (x ^ 2) / 4) * (4 / 3) :=
      mul_le_mul hconv' hquarter (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- The shifted observation has an explicit exponential-square radius four. -/
private theorem exp_square_observation_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {a : ℝ} (ha : |a| ≤ 1)
    (hI : Integrable (fun ω => Real.exp ((X ω - a) ^ 2)) P)
    (hM : (∫ ω, Real.exp ((X ω - a) ^ 2) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp ((X ω) ^ 2 / 16)) P ∧
      (∫ ω, Real.exp ((X ω) ^ 2 / 16) ∂P) ≤ 2 := by
  have hJ : Integrable (fun ω => (4 / 3) * (3 / 4 + Real.exp ((X ω - a) ^ 2) / 4)) P :=
    ((integrable_const (3 / 4 : ℝ)).add (hI.div_const 4)).const_mul (4 / 3)
  have hbound (ω : Ω) : Real.exp ((X ω) ^ 2 / 16) ≤
      (4 / 3) * (3 / 4 + Real.exp ((X ω - a) ^ 2) / 4) := by
    simpa only [sub_add_cancel] using exp_square_shift_envelope (X ω - a) a ha
  have hEI : Integrable (fun ω => Real.exp ((X ω) ^ 2 / 16)) P := by
    apply hJ.mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hbound ω
  refine ⟨hEI, ?_⟩
  calc
    _ ≤ ∫ ω, (4 / 3) * (3 / 4 + Real.exp ((X ω - a) ^ 2) / 4) ∂P :=
      integral_mono hEI hJ hbound
    _ = (4 / 3) * (3 / 4 + (∫ ω, Real.exp ((X ω - a) ^ 2) ∂P) / 4) := by
      rw [integral_const_mul, integral_add (integrable_const (3 / 4 : ℝ)) (hI.div_const 4)]
      simp [integral_div]
    _ ≤ 2 := by linarith

/-- The normalized observation-kernel assumptions imply the observation moment bound at every legal history. -/
private theorem unitNoiseCond_observation_moment {E : Type} {K : Set E} {L : E → ℝ}
    (ν : BilateralProfitMHR.ObsKernel E)
    (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (τ : ℕ) (xs : Fin τ → E) (ys : Fin τ → ℝ) (x : E)
    (hxs : ∀ i, xs i ∈ K) (hx : x ∈ K) :
    Integrable (fun z : ℝ => Real.exp (z ^ 2 / 16)) (ν τ xs ys x) ∧
      (∫ z : ℝ, Real.exp (z ^ 2 / 16) ∂(ν τ xs ys x)) ≤ 2 := by
  obtain ⟨hp, _, _, hi, hm⟩ := hν τ xs ys x hxs hx
  letI := hp
  exact exp_square_observation_moment (ν τ xs ys x) id measurable_id
    (by rw [abs_of_nonneg (hL x hx).1]; exact (hL x hx).2) hi hm










end LG2021.Concentration

end

/- LG2021ConcentrationKernelMoments -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- A uniform conditional nonnegative moment transfers to the joint law of a query and observation. -/
private theorem compProd_snd_moment_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) [IsProbabilityMeasure P] (κ : Kernel A B) [IsMarkovKernel κ]
    (f : B → ℝ) (hf : Measurable f) (hfnonneg : ∀ y, 0 ≤ f y) (C : ℝ)
    (hcond : ∀ᵐ a ∂P, Integrable f (κ a) ∧ (∫ y, f y ∂κ a) ≤ C) :
    Integrable (fun p : A × B => f p.2) (P ⊗ₘ κ) ∧
      (∫ p, f p.2 ∂(P ⊗ₘ κ)) ≤ C := by
  have hsm : StronglyMeasurable (fun p : A × B => f p.2) := (hf.comp measurable_snd).stronglyMeasurable
  have hJ : Integrable (fun a => ∫ y, ‖f y‖ ∂κ a) P := by
    apply (integrable_const C).mono' hf.stronglyMeasurable.norm.integral_kernel.aestronglyMeasurable
    filter_upwards [hcond] with a ha
    have hpos : 0 ≤ ∫ y, f y ∂κ a := integral_nonneg hfnonneg
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hfnonneg _), abs_of_nonneg hpos] using ha.2
  have hI : Integrable (fun p : A × B => f p.2) (P ⊗ₘ κ) :=
    (Measure.integrable_compProd_iff hsm.aestronglyMeasurable).2 ⟨hcond.mono (fun _ h => h.1), hJ⟩
  refine ⟨hI, ?_⟩
  rw [Measure.integral_compProd hI]
  have hJ' : Integrable (fun a => ∫ y, f y ∂κ a) P := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hfnonneg _)] using hJ
  calc
    _ ≤ ∫ _a, C ∂P := integral_mono_ae hJ' (integrable_const C) (hcond.mono (fun _ h => h.2))
    _ = C := by simp

/-- A moment of the query is unchanged when a Markov observation is appended. -/
private theorem compProd_fst_moment {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) [IsProbabilityMeasure P] (κ : Kernel A B) [IsMarkovKernel κ]
    (f : A → ℝ) (hf : Measurable f) (hI : Integrable f P) :
    Integrable (fun p : A × B => f p.1) (P ⊗ₘ κ) ∧
      (∫ p, f p.1 ∂(P ⊗ₘ κ)) = ∫ a, f a ∂P := by
  have hsm : StronglyMeasurable (fun p : A × B => f p.1) := (hf.comp measurable_fst).stronglyMeasurable
  have hJ : Integrable (fun p : A × B => f p.1) (P ⊗ₘ κ) := by
    apply (Measure.integrable_compProd_iff hsm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun a =>
        (show Integrable (fun _y : B => f a) (κ a) from integrable_const (f a))
    · simpa using hI.norm
  refine ⟨hJ, ?_⟩
  rw [Measure.integral_compProd hJ]
  simp

/-- A bounded random multiplier preserves the square-exponential radius with the expected scale. -/
private theorem exp_square_bounded_mul_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X A : Ω → ℝ) (hX : Measurable X) (hA : Measurable A)
    {r B : ℝ} (hr : 0 < r) (hB : 0 < B) (hbound : ∀ ω, |A ω| ≤ B)
    (hI : Integrable (fun ω => Real.exp ((X ω) ^ 2 / r ^ 2)) P)
    (hM : (∫ ω, Real.exp ((X ω) ^ 2 / r ^ 2) ∂P) ≤ 2) :
    Integrable (fun ω => Real.exp ((A ω * X ω) ^ 2 / (B * r) ^ 2)) P ∧
      (∫ ω, Real.exp ((A ω * X ω) ^ 2 / (B * r) ^ 2) ∂P) ≤ 2 := by
  have hb (ω : Ω) : Real.exp ((A ω * X ω) ^ 2 / (B * r) ^ 2) ≤
      Real.exp ((X ω) ^ 2 / r ^ 2) := by
    apply Real.exp_le_exp.mpr
    have ha2 : (A ω) ^ 2 ≤ B ^ 2 := by
      nlinarith [hbound ω, abs_nonneg (A ω), sq_abs (A ω)]
    calc
      _ ≤ (B ^ 2 * (X ω) ^ 2) / (B * r) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        nlinarith [mul_le_mul_of_nonneg_right ha2 (sq_nonneg (X ω))]
      _ = _ := by field_simp [ne_of_gt hB, ne_of_gt hr]
  have hJ : Integrable (fun ω => Real.exp ((A ω * X ω) ^ 2 / (B * r) ^ 2)) P := by
    apply hI.mono' (by fun_prop)
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb ω
  exact ⟨hJ, (integral_mono hJ hI hb).trans hM⟩





end LG2021.Concentration

end

/- LG2021GaussianMoments -/
section

noncomputable section

namespace LG2021

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal





private theorem gaussian_inner_map {d : ℕ} (q : Space d) :
    (gaussian d).map (fun x => inner ℝ q x) =
      (gaussianReal 0 1).map (fun x : ℝ => ‖q‖ * x) := by
  calc
    _ = gaussianReal 0 (‖q‖ ^ 2).toNNReal := by
      change (stdGaussian (Space d)).map (innerSL ℝ q) = _
      rw [IsGaussian.map_eq_gaussianReal]
      simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
        innerSL_apply_norm]
    _ = _ := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · ext
        simp





private theorem gaussian_shift_exp_pdf_bound (s a x : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : |a| ≤ 1) :
    gaussianPDFReal 0 1 x * Real.exp ((s * x - a) ^ 2 / 64) ≤
      2 * gaussianPDFReal 0 2 x := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hp2 : 0 < 2 * Real.pi := by positivity
  have hp4 : 0 < 4 * Real.pi := by positivity
  have hsqrt2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 hp2
  have hsqrt4 : 0 < Real.sqrt (4 * Real.pi) := Real.sqrt_pos.2 hp4
  have hr2 := Real.sq_sqrt hp2.le
  have hr4 := Real.sq_sqrt hp4.le
  have hratio : (Real.sqrt (2 * Real.pi))⁻¹ ≤
      (3 / 2 : ℝ) * (Real.sqrt (4 * Real.pi))⁻¹ := by
    have hroot : Real.sqrt (4 * Real.pi) ≤ (3 / 2 : ℝ) * Real.sqrt (2 * Real.pi) := by
      nlinarith [Real.sqrt_nonneg (2 * Real.pi), Real.sqrt_nonneg (4 * Real.pi)]
    have hratio' : (1 : ℝ) / Real.sqrt (2 * Real.pi) ≤
        (3 / 2 : ℝ) / Real.sqrt (4 * Real.pi) :=
      (div_le_div_iff₀ hsqrt2 hsqrt4).2 (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul] using hratio'
  have hexp : Real.exp (1 / 32 : ℝ) ≤ 4 / 3 := by
    have h := Real.exp_le_two_add_div_two_sub (x := (1 / 32 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h
    linarith
  have hasq : a ^ 2 ≤ 1 := by
    rcases abs_le.mp ha with ⟨ha0, ha1⟩
    nlinarith
  have hssq : s ^ 2 ≤ 1 := by nlinarith
  have hsxsq : (s * x) ^ 2 ≤ x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hssq (sq_nonneg x)]
  have harg : -(x ^ 2) / 2 + (s * x - a) ^ 2 / 64 ≤
      1 / 32 - x ^ 2 / 4 := by
    nlinarith [sq_nonneg (s * x + a), sq_nonneg x]
  have hcoef : (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (1 / 32 : ℝ) ≤
      2 * (Real.sqrt (4 * Real.pi))⁻¹ := by
    calc
      _ ≤ ((3 / 2 : ℝ) * (Real.sqrt (4 * Real.pi))⁻¹) * (4 / 3 : ℝ) :=
        mul_le_mul hratio hexp (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  simp only [gaussianPDFReal, NNReal.coe_one, NNReal.coe_ofNat, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  calc
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (1 / 32 - x ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
    _ = ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (1 / 32 : ℝ)) *
        Real.exp (-x ^ 2 / 4) := by rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ (2 * (Real.sqrt (4 * Real.pi))⁻¹) * Real.exp (-x ^ 2 / 4) :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
    _ = _ := by
      rw [show 2 * Real.pi * 2 = 4 * Real.pi by ring]
      norm_num
      ring

private theorem gaussianReal_shift_exp_square (s a : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : |a| ≤ 1) :
    Integrable (fun x : ℝ => Real.exp ((s * x - a) ^ 2 / 64)) (gaussianReal 0 1) ∧
      (∫ x : ℝ, Real.exp ((s * x - a) ^ 2 / 64) ∂gaussianReal 0 1) ≤ 2 := by
  have hdom := gaussian_shift_exp_pdf_bound s a
  have hprod : Integrable
      (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp ((s * x - a) ^ 2 / 64)) :=
    ((integrable_gaussianPDFReal 0 2).const_mul 2).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (gaussianPDFReal_nonneg 0 1 x) (Real.exp_pos _).le)]
        exact hdom x hs hs1 ha)
  have hint : Integrable (fun x : ℝ => Real.exp ((s * x - a) ^ 2 / 64))
      (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x))).2
    simpa only [toReal_gaussianPDF, smul_eq_mul] using hprod
  refine ⟨hint, ?_⟩
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  calc
    _ ≤ ∫ x : ℝ, 2 * gaussianPDFReal 0 2 x :=
      integral_mono hprod ((integrable_gaussianPDFReal 0 2).const_mul 2)
        (fun x => hdom x hs hs1 ha)
    _ = 2 := by
      rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 (by norm_num : (2 : ℝ≥0) ≠ 0)]
      norm_num

private theorem gaussian_projection_shift_exp_square {d : ℕ} (q : Space d) (a : ℝ)
    (hq : ‖q‖ ≤ 1) (ha : |a| ≤ 1) :
    Integrable (fun x => Real.exp ((inner ℝ q x - a) ^ 2 / 64)) (gaussian d) ∧
      (∫ x, Real.exp ((inner ℝ q x - a) ^ 2 / 64) ∂gaussian d) ≤ 2 := by
  have h := gaussianReal_shift_exp_square ‖q‖ a (norm_nonneg _) hq ha
  have hmapint : Integrable (fun y : ℝ => Real.exp ((y - a) ^ 2 / 64))
      ((gaussian d).map (fun x => inner ℝ q x)) := by
    rw [gaussian_inner_map]
    exact (integrable_map_measure (f := fun x : ℝ => ‖q‖ * x)
      (g := fun y : ℝ => Real.exp ((y - a) ^ 2 / 64)) (by fun_prop) (by fun_prop)).2 h.1
  have hint : Integrable (fun x => Real.exp ((inner ℝ q x - a) ^ 2 / 64))
      (gaussian d) :=
    (integrable_map_measure (f := fun x : Space d => inner ℝ q x)
      (g := fun y : ℝ => Real.exp ((y - a) ^ 2 / 64)) (by fun_prop) (by fun_prop)).1 hmapint
  refine ⟨hint, ?_⟩
  calc
    _ = ∫ y : ℝ, Real.exp ((y - a) ^ 2 / 64)
        ∂((gaussian d).map (fun x => inner ℝ q x)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x : ℝ, Real.exp ((‖q‖ * x - a) ^ 2 / 64) ∂gaussianReal 0 1 := by
      rw [gaussian_inner_map, integral_map (by fun_prop) (by fun_prop)]
    _ ≤ 2 := h.2

















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



/-- The gradient estimator is a product of a boundedly weighted observation and a Gaussian projection.
The product-moment step is the admissible-radius form of Lemma 2.7.7 in Roman Vershynin,
High-Dimensional Probability: An Introduction with Applications in Data Science,
Cambridge University Press, 2018, used in Lattimore–György Lemma 4(d). -/
private theorem directionalGradientEstimator_moment {d : ℕ}
    (P : Measure (Space d)) [IsProbabilityMeasure P]
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z η : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    {q : ℝ} (hq : 0 < q)
    (hprojI : Integrable (fun x => Real.exp ((inner ℝ (x - lambda • z) η) ^ 2 / q ^ 2)) P)
    (hprojM : (∫ x, Real.exp ((inner ℝ (x - lambda • z) η) ^ 2 / q ^ 2) ∂P) ≤ 2)
    (hobs : ∀ᵐ x ∂P, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2) :
    Integrable (fun p : Space d × ℝ =>
      Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / (96 * q))) (P ⊗ₘ κ) ∧
    (∫ p : Space d × ℝ,
      Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / (96 * q))
        ∂(P ⊗ₘ κ)) ≤ 2 := by
  let A : Space d × ℝ → ℝ := fun p =>
    likelihoodRatio lambda z p.1 * truncation lambda r z p.1 / (1 - lambda) ^ 2
  have hA : Measurable A := by
    exact (((Algorithm.measurable_likelihoodRatio lambda).comp
      (measurable_const.prodMk measurable_fst)).mul
      ((Algorithm.measurable_truncation lambda r).comp
        (measurable_const.prodMk measurable_fst))).div_const _
  obtain ⟨hI, hM⟩ := compProd_snd_moment_le P κ (fun y : ℝ => Real.exp (y ^ 2 / 16))
    (by fun_prop) (fun _ => (Real.exp_pos _).le) 2 hobs
  have hweighted := exp_square_bounded_mul_moment (P ⊗ₘ κ) Prod.snd A measurable_snd hA
    (r := 4) (B := 24) (by norm_num) (by norm_num)
    (fun p => abs_gradientWeight_le r z p.1 hpos hsmall hd)
    (by norm_num at hI ⊢; exact hI) (by norm_num at hM ⊢; exact hM)
  have hprojection := compProd_fst_moment P κ
    (fun x => Real.exp ((inner ℝ (x - lambda • z) η) ^ 2 / q ^ 2)) (by fun_prop) hprojI
  have h := exp_abs_product_moment_scaled (P ⊗ₘ κ)
    (fun p : Space d × ℝ => A p * p.2) (fun p => inner ℝ (p.1 - lambda • z) η)
    (hA.mul measurable_snd) (by fun_prop) (a := 96) (b := q) (by norm_num) hq
    (by norm_num at hweighted ⊢; exact hweighted.1) hprojection.1
    (by norm_num at hweighted ⊢; exact hweighted.2) (hprojection.2 ▸ hprojM)
  have heq : (fun p : Space d × ℝ =>
      Real.exp (|(A p * p.2) * inner ℝ (p.1 - lambda • z) η| / (96 * q))) =
      (fun p : Space d × ℝ =>
        Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / (96 * q))) := by
    funext p
    simp only [directionalGradientCoefficient, gradientCoefficient, real_inner_smul_left]
    dsimp [A]
    congr 3
    ring
  exact heq ▸ h


/-- The concrete Gaussian-gradient estimator has a universal exponential-absolute radius.
This completes the moment bound corresponding to Lattimore–György Lemma 4(d), with a
larger explicit universal constant and with an arbitrary conditional observation kernel. -/
private theorem gaussian_directionalGradientEstimator_moment {d : ℕ}
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z η : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    (hz : lambda * ‖z‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hobs : ∀ᵐ x ∂gaussian d, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2) :
    Integrable (fun p : Space d × ℝ =>
      Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / 768))
        ((gaussian d) ⊗ₘ κ) ∧
    (∫ p : Space d × ℝ,
      Real.exp (|p.2 * directionalGradientCoefficient lambda r z η p.1| / 768)
        ∂((gaussian d) ⊗ₘ κ)) ≤ 2 := by
  have ha : |lambda * inner ℝ η z| ≤ 1 := by
    rw [abs_mul, abs_of_pos hpos]
    have hi := abs_real_inner_le_norm η z
    calc
      _ ≤ lambda * (‖η‖ * ‖z‖) := mul_le_mul_of_nonneg_left hi hpos.le
      _ ≤ lambda * ‖z‖ := by nlinarith [mul_le_mul_of_nonneg_right hη (norm_nonneg z)]
      _ ≤ 1 := hz
  have hproj := gaussian_projection_shift_exp_square η (lambda * inner ℝ η z) hη ha
  have heq : (fun x : Space d => Real.exp ((inner ℝ η x - lambda * inner ℝ η z) ^ 2 / 64)) =
      (fun x : Space d => Real.exp ((inner ℝ (x - lambda • z) η) ^ 2 / (8 : ℝ) ^ 2)) := by
    funext x
    rw [← real_inner_comm (x - lambda • z) η, inner_sub_right, real_inner_smul_right]
    norm_num
  rw [heq] at hproj
  have h := directionalGradientEstimator_moment (gaussian d) κ r z η hpos hsmall hd
    (q := 8) (by norm_num) hproj.1 hproj.2 hobs
  norm_num at h ⊢
  exact h


end LG2021.Concentration

end

/- LG2021ConcentrationParameters -/
section

set_option autoImplicit false

namespace LG2021.Concentration






















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

/-- A finite exponential-absolute moment implies ordinary integrability. -/
private theorem integrable_of_exp_abs_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX : Measurable X) {r : ℝ} (hr : 0 < r)
    (hI : Integrable (fun ω => Real.exp (|X ω| / r)) P) : Integrable X P := by
  apply (hI.const_mul r).mono' hX.aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  have he := Real.add_one_le_exp (|X ω| / r)
  have hmul := mul_le_mul_of_nonneg_left he hr.le
  have hcancel : r * (|X ω| / r) = |X ω| := by field_simp
  nlinarith

/-- The actual gradient estimate has centered exponential-absolute radius `3072`. -/
private theorem gaussian_gradientEstimator_centered_moment {d : ℕ}
    (κ : Kernel (Space d) ℝ) [IsMarkovKernel κ] {lambda : ℝ} (r : ℝ) (z η : Space d)
    (hpos : 0 < lambda) (hsmall : lambda ≤ 1 / 2) (hd : (d : ℝ) * lambda ≤ 1 / 2)
    (hz : lambda * ‖z‖ ≤ 1) (hη : ‖η‖ ≤ 1)
    (hobs : ∀ᵐ x ∂gaussian d, Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2) :
    Integrable (fun p : Space d × ℝ => p.2 * directionalGradientCoefficient lambda r z η p.1)
      ((gaussian d) ⊗ₘ κ) ∧
    Integrable (fun p : Space d × ℝ => Real.exp
      (|p.2 * directionalGradientCoefficient lambda r z η p.1 -
        ∫ q : Space d × ℝ, q.2 * directionalGradientCoefficient lambda r z η q.1
          ∂((gaussian d) ⊗ₘ κ)| / 3072)) ((gaussian d) ⊗ₘ κ) ∧
    (∫ p : Space d × ℝ, Real.exp
      (|p.2 * directionalGradientCoefficient lambda r z η p.1 -
        ∫ q : Space d × ℝ, q.2 * directionalGradientCoefficient lambda r z η q.1
          ∂((gaussian d) ⊗ₘ κ)| / 3072) ∂((gaussian d) ⊗ₘ κ)) ≤ 2 := by
  have hG : Measurable (fun p : Space d × ℝ => gradientCoefficient lambda r z p.1) :=
    (Algorithm.measurable_gradientCoefficient lambda r).comp
      (f := fun p : Space d × ℝ => (z, p.1)) (measurable_const.prodMk measurable_fst)
  have hX : Measurable (fun p : Space d × ℝ => p.2 * directionalGradientCoefficient lambda r z η p.1) :=
    measurable_snd.mul (hG.inner measurable_const)
  have hm := gaussian_directionalGradientEstimator_moment κ r z η hpos hsmall hd hz hη hobs
  have hc := exp_abs_centered_moment_scaled ((gaussian d) ⊗ₘ κ)
    (fun p : Space d × ℝ => p.2 * directionalGradientCoefficient lambda r z η p.1)
    hX (r := 768) (by norm_num) hm.1 hm.2
  refine ⟨integrable_of_exp_abs_scaled _ _ hX (r := 768) (by norm_num) hm.1, ?_⟩
  norm_num at hc
  exact ⟨hc.1, hc.2.1⟩






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

private theorem lintegral_historyMeasure_zero {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable)
    (F : Ω × (Fin 0 → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂historyMeasure A P ν hνm 0) = ∫⁻ ω, F (ω, Fin.elim0) ∂P := by
  exact lintegral_map hF (by fun_prop)

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



private theorem ignoreSeedRight_isOn {X Ω B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace B] (A : QueryAlg X Ω) {K : Set X} (hA : A.IsOn K) :
    (ignoreSeedRight B A).IsOn K := fun τ w ys => hA τ w.1 ys

private theorem measurable_average_seed {Ω B : Type} [MeasurableSpace Ω] [MeasurableSpace B]
    (Q : Measure B) [SFinite Q] (τ : ℕ)
    (F : (Ω × B) × (Fin τ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun w : Ω × (Fin τ → ℝ) => ∫⁻ b, F ((w.1, b), w.2) ∂Q) := by
  exact (hF.comp (show Measurable (fun z : (Ω × (Fin τ → ℝ)) × B =>
    ((z.1.1, z.2), z.1.2)) from by fun_prop)).lintegral_prod_right'

/-- An unused independent seed coordinate remains independent of the entire observation history.
This identity is the Fubini step needed to reveal learner randomness only when it is consumed. -/
private theorem lintegral_history_ignoreSeedRight {X Ω B : Type}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace B]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure B) [IsProbabilityMeasure Q]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (τ : ℕ)
    (F : (Ω × B) × (Fin τ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂historyMeasure (ignoreSeedRight B A) (P.prod Q) ν hνm τ) =
      ∫⁻ w, ∫⁻ b, F ((w.1, b), w.2) ∂Q ∂historyMeasure A P ν hνm τ := by
  have hAB := ignoreSeedRight_isOn (B := B) A hA
  induction τ with
  | zero =>
      rw [lintegral_historyMeasure_zero _ _ _ _ F hF,
        lintegral_historyMeasure_zero _ _ _ _ _ (measurable_average_seed Q 0 F hF)]
      exact lintegral_prod _ ((hF.comp (by fun_prop)).aemeasurable)
  | succ τ ih =>
      let κ := observationKernel (ignoreSeedRight B A) ν hνm τ
      letI : IsMarkovKernel κ := observationKernel_isMarkov _ ν hνm hAB L γ hν τ
      let G : (Ω × B) × (Fin τ → ℝ) → ℝ≥0∞ := fun w =>
        ∫⁻ y, F (w.1, Fin.snoc w.2 y) ∂κ w
      have hG : Measurable G :=
        (hF.comp (measurable_history_snoc τ)).lintegral_kernel_prod_right' (κ := κ)
      rw [lintegral_historyMeasure_succ _ _ _ _ hAB L γ hν τ F hF]
      change (∫⁻ w, G w ∂historyMeasure (ignoreSeedRight B A) (P.prod Q) ν hνm τ) = _
      rw [ih G hG, lintegral_historyMeasure_succ A P ν hνm hA L γ hν τ _
        (measurable_average_seed Q (τ + 1) F hF)]
      apply lintegral_congr
      intro w
      letI := (hν τ (A.pastQueries w.1 w.2) w.2 (A.query τ w.1 w.2)
        (fun i => hA i w.1 _) (hA τ w.1 w.2)).1
      change (∫⁻ b, ∫⁻ y, F ((w.1, b), Fin.snoc w.2 y)
        ∂ν τ (A.pastQueries w.1 w.2) w.2 (A.query τ w.1 w.2) ∂Q) =
          ∫⁻ y, ∫⁻ b, F ((w.1, b), Fin.snoc w.2 y) ∂Q
            ∂ν τ (A.pastQueries w.1 w.2) w.2 (A.query τ w.1 w.2)
      apply lintegral_lintegral_swap
      exact (hF.comp (show Measurable (fun z : B × ℝ =>
        ((w.1, z.1), Fin.snoc w.2 z.2)) from by
          exact (measurable_const.prodMk measurable_fst).prodMk
            (by apply measurable_pi_lambda; intro i; refine Fin.lastCases ?_ (fun j => ?_) i <;>
              simp only [Fin.snoc_last, Fin.snoc_castSucc] <;> fun_prop))).aemeasurable


/-- Policies agreeing through a finite prefix have exactly the same history law through that prefix. -/
private theorem historyMeasure_congr_before {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A A' : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable) :
    ∀ τ, (∀ i < τ, ∀ ω ys, A.query i ω ys = A'.query i ω ys) →
      historyMeasure A P ν hνm τ = historyMeasure A' P ν hνm τ := by
  intro τ
  induction τ with
  | zero => intro h; rfl
  | succ τ ih =>
      intro h
      have hk : observationKernel A ν hνm τ = observationKernel A' ν hνm τ := by
        apply Kernel.ext
        intro w
        change ν τ (A.pastQueries w.1 w.2) w.2 (A.query τ w.1 w.2) =
          ν τ (A'.pastQueries w.1 w.2) w.2 (A'.query τ w.1 w.2)
        rw [h τ (by omega)]
        congr 1
        funext i
        exact h i (by omega) w.1 _
      simp only [historyMeasure, ih (fun i hi => h i (by omega)), hk]



private theorem reparametrizeSeed_isOn {X Ω Ω' : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (A : QueryAlg X Ω) (f : Ω' → Ω) (hf : Measurable f)
    {K : Set X} (hA : A.IsOn K) : (reparametrizeSeed A f hf).IsOn K :=
  fun τ ω ys => hA τ (f ω) ys

/-- The history law respects actual measurable seed reparameterization. -/
private theorem lintegral_history_reparametrizeSeed {X Ω Ω' : Type}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
    (A : QueryAlg X Ω) (f : Ω' → Ω) (hf : Measurable f)
    (P : Measure Ω') [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (τ : ℕ)
    (F : Ω × (Fin τ → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F (f w.1, w.2) ∂historyMeasure (reparametrizeSeed A f hf) P ν hνm τ) =
      ∫⁻ w, F w ∂historyMeasure A (P.map f) ν hνm τ := by
  letI : IsProbabilityMeasure (P.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  have hAf := reparametrizeSeed_isOn A f hf hA
  induction τ with
  | zero =>
      rw [lintegral_historyMeasure_zero _ _ _ _ (fun w : Ω' × (Fin 0 → ℝ) => F (f w.1, w.2))
        (hF.comp ((hf.comp measurable_fst).prodMk measurable_snd)),
        lintegral_historyMeasure_zero _ _ _ _ F hF]
      exact (lintegral_map (hF.comp (measurable_id.prodMk measurable_const)) hf).symm
  | succ τ ih =>
      let κ := observationKernel A ν hνm τ
      letI : IsMarkovKernel κ := observationKernel_isMarkov A ν hνm hA L γ hν τ
      let G : Ω × (Fin τ → ℝ) → ℝ≥0∞ := fun w => ∫⁻ y, F (w.1, Fin.snoc w.2 y) ∂κ w
      have hG : Measurable G :=
        (hF.comp (measurable_history_snoc τ)).lintegral_kernel_prod_right' (κ := κ)
      rw [lintegral_historyMeasure_succ _ _ _ _ hAf L γ hν τ
        (fun w : Ω' × (Fin (τ + 1) → ℝ) => F (f w.1, w.2))
        (hF.comp ((hf.comp measurable_fst).prodMk measurable_snd)),
        lintegral_historyMeasure_succ _ _ _ _ hA L γ hν τ F hF]
      exact ih G hG




/-- Exact finite-history factorization at the time a previously unused private coordinate is revealed. -/
private theorem lintegral_history_independent_coordinate {X Ω W B : Type}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace B]
    (A : QueryAlg X Ω) (S : Measure Ω) [IsProbabilityMeasure S]
    (P : Measure W) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (encode : W × B → Ω) (he : MeasurePreserving encode (P.prod Q) S) (b0 : B)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ)
    (hunused : ∀ τ < T, ∀ w b ys, A.query τ (encode (w, b)) ys = A.query τ (encode (w, b0)) ys)
    (F : Ω × (Fin T → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂historyMeasure A S ν hνm T) =
      ∫⁻ w, ∫⁻ b, F (encode (w.1, b), w.2) ∂Q
        ∂historyMeasure (freezeCoordinatePolicy A encode he.measurable b0) P ν hνm T := by
  let A0 := freezeCoordinatePolicy A encode he.measurable b0
  have hA0 : A0.IsOn K := fun τ w ys => hA τ (encode (w, b0)) ys
  have hcongr : historyMeasure (reparametrizeSeed A encode he.measurable) (P.prod Q) ν hνm T =
      historyMeasure (ignoreSeedRight B A0) (P.prod Q) ν hνm T := by
    apply historyMeasure_congr_before
    intro τ hτ w ys
    exact hunused τ hτ w.1 w.2 ys
  have hFenc : Measurable (fun w : (W × B) × (Fin T → ℝ) => F (encode w.1, w.2)) :=
    hF.comp ((he.measurable.comp measurable_fst).prodMk measurable_snd)
  have hmap := lintegral_history_reparametrizeSeed A encode he.measurable (P.prod Q)
    ν hνm hA L γ hν T F hF
  rw [he.map_eq, hcongr] at hmap
  exact hmap.symm.trans (lintegral_history_ignoreSeedRight A0 P Q ν hνm hA0 L γ hν T _ hFenc)


end LG2021.Concentration

end
end

/- LG2021ConcentrationNoAnticipation -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped Classical

/-- The oracle state uses only candidate blocks through the current pair and earlier Gaussian vectors. -/
private theorem runState_seed_prefix {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (s t : Seed d u cfg.horizon) : ∀ (p : ℕ) (ys : Fin p → ℝ × ℝ),
    (∀ j ≤ p, seedCandidates s j = seedCandidates t j) →
    (∀ j < p, seedGaussian s j = seedGaussian t j) →
    runState cfg K R s p ys = runState cfg K R t p ys := by
  intro p
  induction p with
  | zero =>
      intro ys hc hg
      simp only [runState, initialState, hc 0 le_rfl]
  | succ p ih =>
      intro ys hc hg
      simp only [runState]
      rw [ih (fun i => ys i.castSucc) (fun j hj => hc j (by omega))
        (fun j hj => hg j (by omega)), hc (p + 1) le_rfl, hg p (by omega)]

/-- The next query is unchanged by modifications of seed coordinates that have not been consumed. -/
private theorem proposedQuery_seed_prefix {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (τ : ℕ) (s t : Seed d u cfg.horizon) (ys : Fin τ → ℝ)
    (hc : ∀ j ≤ τ / 2, seedCandidates s j = seedCandidates t j)
    (hg : ∀ j ≤ τ / 2, seedGaussian s j = seedGaussian t j) :
    proposedQuery cfg K R τ s ys = proposedQuery cfg K R τ t ys := by
  unfold proposedQuery
  rw [runState_seed_prefix cfg K R s t (τ / 2) (pairedHistory ys) hc
    (fun j hj => hg j (by omega)), hg (τ / 2) le_rfl]

/-- The legal fallback preserves the same finite-prefix dependence as the proposed query. -/
private theorem policy_seed_prefix {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (τ : ℕ) (s t : Seed d u cfg.horizon) (ys : Fin τ → ℝ)
    (hc : ∀ j ≤ τ / 2, seedCandidates s j = seedCandidates t j)
    (hg : ∀ j ≤ τ / 2, seedGaussian s j = seedGaussian t j) :
    (policy (u := u) cfg K hK R anchor).query τ s ys =
      (policy (u := u) cfg K hK R anchor).query τ t ys := by
  change (if proposedQuery cfg K R τ s ys ∈ K then proposedQuery cfg K R τ s ys else anchor) = _
  rw [proposedQuery_seed_prefix cfg K R τ s t ys hc hg]
  rfl

/-- In particular, the history before pair `p` cannot depend on its fresh Gaussian coordinate. -/
private theorem policy_before_pair_seed_prefix {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (p τ : ℕ) (hτ : τ < 2 * p) (s t : Seed d u cfg.horizon) (ys : Fin τ → ℝ)
    (hc : ∀ j ≤ p, seedCandidates s j = seedCandidates t j)
    (hg : ∀ j < p, seedGaussian s j = seedGaussian t j) :
    (policy (u := u) cfg K hK R anchor).query τ s ys =
      (policy (u := u) cfg K hK R anchor).query τ t ys := by
  apply policy_seed_prefix cfg K hK R anchor τ s t ys
  · intro j hj
    apply hc j
    omega
  · intro j hj
    apply hg j
    omega


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

/-- Changing the inserted Gaussian value leaves every earlier Gaussian coordinate unchanged. -/
private theorem seedGaussian_insert_before {d u n : ℕ} (i : Fin (n + 1))
    (w : GaussianRemainder d u n) (x y : Space d) (j : ℕ) (hj : j < i.val) :
    seedGaussian (insertGaussianSeed i (w, x)) j =
      seedGaussian (insertGaussianSeed i (w, y)) j := by
  have hjn : j < n + 1 := hj.trans i.isLt
  simp only [seedGaussian, dif_pos hjn, insertGaussianSeed]
  have hji : (⟨j, hjn⟩ : Fin (n + 1)) < i := hj
  rw [Fin.insertNth_apply_below hji, Fin.insertNth_apply_below hji]

/-- The actual history before a pair is independent of the value of its inserted Gaussian coordinate. -/
private theorem policy_insertGaussianSeed_before {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (i : Fin (cfg.horizon + 1)) (τ : ℕ) (hτ : τ < 2 * i.val)
    (w : GaussianRemainder d u cfg.horizon) (x y : Space d) (ys : Fin τ → ℝ) :
    (policy (u := u) cfg K hK R anchor).query τ (insertGaussianSeed i (w, x)) ys =
      (policy (u := u) cfg K hK R anchor).query τ (insertGaussianSeed i (w, y)) ys := by
  apply policy_before_pair_seed_prefix cfg K hK R anchor i.val τ hτ _ _ ys
  · intro j hj
    rfl
  · intro j hj
    exact seedGaussian_insert_before i w x y j hj





end LG2021.Concentration

end
end

/- LG2021ConcentrationPairPath -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal



private theorem measurable_firstHistoryMap {Ω W B : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace B] (encode : W × B → Ω) (he : Measurable encode) {T : ℕ}
    (w : W × (Fin T → ℝ)) : Measurable (firstHistoryMap encode w) :=
  (he.comp (measurable_const.prodMk measurable_id)).prodMk measurable_const



private theorem measurable_secondHistoryMap {Ω W B : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace B] (encode : W × B → Ω) (he : Measurable encode) {T : ℕ}
    (w : W × (Fin T → ℝ)) : Measurable (secondHistoryMap encode w) :=
  (measurable_history_snoc T).comp
    (((measurable_firstHistoryMap encode he w).comp measurable_fst).prodMk measurable_snd)



private theorem measurable_pairHistoryMap {Ω W B : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace B] (encode : W × B → Ω) (he : Measurable encode) {T : ℕ}
    (w : W × (Fin T → ℝ)) : Measurable (pairHistoryMap encode w) :=
  (measurable_history_snoc (T + 1)).comp
    (((measurable_secondHistoryMap encode he w).comp measurable_fst).prodMk measurable_snd)





private theorem coordinateFirstKernel_isMarkov {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν)
    {T : ℕ} (w : W × (Fin T → ℝ)) : IsMarkovKernel (coordinateFirstKernel A ν hνm encode he w) := by
  letI := observationKernel_isMarkov A ν hνm hA L γ hν T
  unfold coordinateFirstKernel
  infer_instance

private theorem coordinateSecondKernel_isMarkov {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν)
    {T : ℕ} (w : W × (Fin T → ℝ)) : IsMarkovKernel (coordinateSecondKernel A ν hνm encode he w) := by
  letI := observationKernel_isMarkov A ν hνm hA L γ hν (T + 1)
  unfold coordinateSecondKernel
  infer_instance



private theorem coordinatePairMeasure_probability {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B) [IsProbabilityMeasure Q]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν)
    {T : ℕ} (w : W × (Fin T → ℝ)) : IsProbabilityMeasure (coordinatePairMeasure A Q ν hνm encode he w) := by
  letI := coordinateFirstKernel_isMarkov A ν hνm encode he hA L γ hν w
  letI := coordinateSecondKernel_isMarkov A ν hνm encode he hA L γ hν w
  unfold coordinatePairMeasure
  infer_instance

private theorem lintegral_coordinatePairMeasure {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B) [IsProbabilityMeasure Q]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν)
    {T : ℕ} (w : W × (Fin T → ℝ)) (F : (B × ℝ) × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂coordinatePairMeasure A Q ν hνm encode he w) =
      ∫⁻ x, ∫⁻ y, ∫⁻ y', F ((x, y), y') ∂coordinateSecondKernel A ν hνm encode he w (x, y)
        ∂coordinateFirstKernel A ν hνm encode he w x ∂Q := by
  letI := coordinateFirstKernel_isMarkov A ν hνm encode he hA L γ hν w
  letI := coordinateSecondKernel_isMarkov A ν hνm encode he hA L γ hν w
  unfold coordinatePairMeasure
  rw [Measure.lintegral_compProd hF]
  exact Measure.lintegral_compProd
    (hF.lintegral_kernel_prod_right' (κ := coordinateSecondKernel A ν hνm encode he w))

/-- Two actual observation steps are represented without an independence assumption between them. -/
private theorem lintegral_historyMeasure_two_steps {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ)
    (F : Ω × (Fin (T + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂historyMeasure A P ν hνm (T + 2)) =
      ∫⁻ w, ∫⁻ y, ∫⁻ y', F (w.1, Fin.snoc (Fin.snoc w.2 y) y')
        ∂observationKernel A ν hνm (T + 1) (w.1, Fin.snoc w.2 y)
        ∂observationKernel A ν hνm T w ∂historyMeasure A P ν hνm T := by
  letI := observationKernel_isMarkov A ν hνm hA L γ hν (T + 1)
  have hG : Measurable (fun w : Ω × (Fin (T + 1) → ℝ) =>
      ∫⁻ y', F (w.1, Fin.snoc w.2 y') ∂observationKernel A ν hνm (T + 1) w) :=
    (hF.comp (measurable_history_snoc (T + 1))).lintegral_kernel_prod_right'
  rw [lintegral_historyMeasure_succ A P ν hνm hA L γ hν (T + 1) F hF]
  exact lintegral_historyMeasure_succ A P ν hνm hA L γ hν T _ hG


/-- Reveal a fresh coordinate and then draw the two adaptive observations in their actual order. -/
private theorem lintegral_history_pair_factorization {X Ω W B : Type}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace B]
    (A : QueryAlg X Ω) (S : Measure Ω) [IsProbabilityMeasure S]
    (P : Measure W) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (encode : W × B → Ω) (he : MeasurePreserving encode (P.prod Q) S) (b0 : B)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ)
    (hunused : ∀ τ < T, ∀ w b ys, A.query τ (encode (w, b)) ys = A.query τ (encode (w, b0)) ys)
    (F : Ω × (Fin (T + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂historyMeasure A S ν hνm (T + 2)) =
      ∫⁻ w, ∫⁻ p, F (pairHistoryMap encode w p) ∂coordinatePairMeasure A Q ν hνm encode he.measurable w
        ∂historyMeasure (freezeCoordinatePolicy A encode he.measurable b0) P ν hνm T := by
  letI := observationKernel_isMarkov A ν hνm hA L γ hν T
  letI := observationKernel_isMarkov A ν hνm hA L γ hν (T + 1)
  let G1 : Ω × (Fin (T + 1) → ℝ) → ℝ≥0∞ := fun w =>
    ∫⁻ y', F (w.1, Fin.snoc w.2 y') ∂observationKernel A ν hνm (T + 1) w
  have hG1 : Measurable G1 :=
    (hF.comp (measurable_history_snoc (T + 1))).lintegral_kernel_prod_right'
  let G0 : Ω × (Fin T → ℝ) → ℝ≥0∞ := fun w =>
    ∫⁻ y, G1 (w.1, Fin.snoc w.2 y) ∂observationKernel A ν hνm T w
  have hG0 : Measurable G0 :=
    (hG1.comp (measurable_history_snoc T)).lintegral_kernel_prod_right'
  rw [lintegral_historyMeasure_two_steps A S ν hνm hA L γ hν T F hF]
  change (∫⁻ w, G0 w ∂historyMeasure A S ν hνm T) = _
  rw [lintegral_history_independent_coordinate A S P Q encode he b0 ν hνm hA L γ hν T hunused G0 hG0]
  apply lintegral_congr
  intro w
  symm
  exact lintegral_coordinatePairMeasure A Q ν hνm encode he.measurable hA L γ hν w
    (fun p => F (pairHistoryMap encode w p)) (hF.comp (measurable_pairHistoryMap encode he.measurable w))




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











private theorem firstObservationKernel_isMarkov {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ) :
    IsMarkovKernel (firstObservationKernel A ν hνm encode he T) := by
  letI := observationKernel_isMarkov A ν hνm hA L γ hν T
  unfold firstObservationKernel
  infer_instance



private theorem coordinateFirstPairKernel_isMarkov {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B) [IsProbabilityMeasure Q]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ) :
    IsMarkovKernel (coordinateFirstPairKernel A Q ν hνm encode he T) := by
  letI := firstObservationKernel_isMarkov A ν hνm encode he hA L γ hν T
  unfold coordinateFirstPairKernel
  infer_instance



private theorem coordinateFirstPairKernel_apply {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B) [IsProbabilityMeasure Q]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν)
    {T : ℕ} (w : W × (Fin T → ℝ)) :
    coordinateFirstPairKernel A Q ν hνm encode he T w = Q ⊗ₘ coordinateFirstKernel A ν hνm encode he w := by
  letI := firstObservationKernel_isMarkov A ν hνm encode he hA L γ hν T
  rw [coordinateFirstPairKernel, Kernel.compProd_apply_eq_compProd_sectR]
  congr 1




end LG2021.Concentration

end
end

/- LG2021ConcentrationObservationPath -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal Classical





/-- The exact policy observation kernel has the normalized raw observation moment at every history. -/
private theorem observationKernel_unit_moment {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (w : Ω × (Fin T → ℝ)) :
    Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (observationKernel A ν hνm T w) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂observationKernel A ν hνm T w) ≤ 2 :=
  unitNoiseCond_observation_moment ν hν hL T (A.pastQueries w.1 w.2) w.2 (A.query T w.1 w.2)
    (fun i => hA i w.1 _) (hA T w.1 w.2)






/-- The actual pair-law directional estimate has centered exponential-absolute radius `3072`. -/
private theorem gaussianPolicy_gradientPair_centered_moment {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (i : Fin (cfg.horizon + 1)) (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) (z η : Space d)
    (hpos : 0 < cfg.lambda) (hsmall : cfg.lambda ≤ 1 / 2) (hd : (d : ℝ) * cfg.lambda ≤ 1 / 2)
    (hz : cfg.lambda * ‖z‖ ≤ 1) (hη : ‖η‖ ≤ 1) :
    let A := policy (u := u) cfg K hK R anchor
    let κ := coordinateFirstKernel A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
    let κ' := coordinateSecondKernel A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
    let μ := ((gaussian d) ⊗ₘ κ) ⊗ₘ κ'
    let mean := ∫ q : Space d × ℝ, q.2 * directionalGradientCoefficient cfg.lambda cfg.radius z η q.1
      ∂((gaussian d) ⊗ₘ κ)
    Integrable (fun p : (Space d × ℝ) × ℝ => Real.exp
      (|p.1.2 * directionalGradientCoefficient cfg.lambda cfg.radius z η p.1.1 - mean| / 3072)) μ ∧
    (∫ p : (Space d × ℝ) × ℝ, Real.exp
      (|p.1.2 * directionalGradientCoefficient cfg.lambda cfg.radius z η p.1.1 - mean| / 3072) ∂μ) ≤ 2 ∧
    (∫ p : (Space d × ℝ) × ℝ,
      (p.1.2 * directionalGradientCoefficient cfg.lambda cfg.radius z η p.1.1 - mean) ∂μ) = 0 := by
  let A := policy (u := u) cfg K hK R anchor
  let κ := coordinateFirstKernel A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
  let κ' := coordinateSecondKernel A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
  have hA : A.IsOn K := policy_isOn cfg K hK R ha
  have hnoise := BilateralProfitMHR.CorollaryTransport.unitNoiseCond_noiseCond K L ν hν
  letI : IsMarkovKernel κ := coordinateFirstKernel_isMarkov A ν hνm _ _ hA L 1 hnoise w
  letI : IsMarkovKernel κ' := coordinateSecondKernel_isMarkov A ν hνm _ _ hA L 1 hnoise w
  have hc := gaussian_gradientEstimator_centered_moment κ cfg.radius z η hpos hsmall hd hz hη
    (Filter.Eventually.of_forall fun x =>
      observationKernel_unit_moment A ν hνm hA L hν hL _ (firstHistoryMap (insertGaussianSeed i) w x))
  have hG : Measurable (fun p : Space d × ℝ => gradientCoefficient cfg.lambda cfg.radius z p.1) :=
    (Algorithm.measurable_gradientCoefficient cfg.lambda cfg.radius).comp
      (f := fun p : Space d × ℝ => (z, p.1)) (measurable_const.prodMk measurable_fst)
  have hX : Measurable (fun p : Space d × ℝ => p.2 * directionalGradientCoefficient cfg.lambda cfg.radius z η p.1) :=
    measurable_snd.mul (hG.inner measurable_const)
  have hm := compProd_fst_moment ((gaussian d) ⊗ₘ κ) κ' _
    ((((hX.sub_const _).abs).div_const 3072).exp) hc.2.1
  have hraw := compProd_fst_moment ((gaussian d) ⊗ₘ κ) κ' _ hX hc.1
  refine ⟨hm.1, hm.2.trans_le hc.2.2, ?_⟩
  rw [integral_sub hraw.1 (integrable_const _), hraw.2]
  simp [κ, A]


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

private theorem gaussianPolicy_gradientPredictable_moment {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (i : Fin (cfg.horizon + 1)) (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) (z η : Space d)
    (hpos : 0 < cfg.lambda) (hsmall : cfg.lambda ≤ 1 / 2) (hd : (d : ℝ) * cfg.lambda ≤ 1 / 2)
    (hz : cfg.lambda * ‖z‖ ≤ 1) (hη : ‖η‖ ≤ 1) :
    let X := fun p : (Space d × ℝ) × ℝ =>
      p.1.2 * directionalGradientCoefficient cfg.lambda cfg.radius z η p.1.1 -
        gradientPredictableMean (policy (u := u) cfg K hK R anchor) ν hνm
          (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) cfg.lambda cfg.radius z η w
    let μ := coordinatePairMeasure (policy (u := u) cfg K hK R anchor) (gaussian d) ν hνm
        (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
    Integrable (fun p => Real.exp (|X p| / 3072)) μ ∧
      (∫ p, Real.exp (|X p| / 3072) ∂μ) ≤ 2 ∧ (∫ p, X p ∂μ) = 0 := by
  have hA := policy_isOn (u := u) cfg K hK R ha
  have hn := BilateralProfitMHR.CorollaryTransport.unitNoiseCond_noiseCond K L ν hν
  dsimp only
  unfold gradientPredictableMean
  rw [coordinateFirstPairKernel_apply _ _ _ _ _ _ hA L 1 hn w]
  exact gaussianPolicy_gradientPair_centered_moment cfg K hK R anchor ha i ν hνm L hν hL
    w z η hpos hsmall hd hz hη

end LG2021.Concentration

end
end

/- LG2021ConcentrationPathAccumulation -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal

/-- A single conditional pair MGF bound propagates on the actual finite path law.
The accumulated previous value must depend only on the already consumed coordinates. -/
private theorem lintegral_exp_pair_step_le {X Ω W B : Type}
    [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace B]
    (A : QueryAlg X Ω) (S : Measure Ω) [IsProbabilityMeasure S]
    (P : Measure W) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (encode : W × B → Ω) (he : MeasurePreserving encode (P.prod Q) S) (b0 : B)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ)
    (hunused : ∀ τ < T, ∀ w b ys, A.query τ (encode (w, b)) ys = A.query τ (encode (w, b0)) ys)
    (before : Ω × (Fin T → ℝ) → ℝ) (after : Ω × (Fin (T + 2) → ℝ) → ℝ)
    (hbefore : Measurable before) (hafter : Measurable after)
    (hknown : ∀ (w : W × (Fin T → ℝ)) b, before (encode (w.1, b), w.2) = before (encode (w.1, b0), w.2))
    (increment : (W × (Fin T → ℝ)) → (B × ℝ) × ℝ → ℝ)
    (hadd : ∀ w p, after (pairHistoryMap encode w p) = before (encode (w.1, b0), w.2) + increment w p)
    (t v : ℝ)
    (hMGF : ∀ᵐ w ∂historyMeasure (freezeCoordinatePolicy A encode he.measurable b0) P ν hνm T,
      Integrable (fun p => Real.exp (t * increment w p)) (coordinatePairMeasure A Q ν hνm encode he.measurable w) ∧
      (∫ p, Real.exp (t * increment w p) ∂coordinatePairMeasure A Q ν hνm encode he.measurable w) ≤ Real.exp v) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (t * after w)) ∂historyMeasure A S ν hνm (T + 2)) ≤
      ENNReal.ofReal (Real.exp v) *
        ∫⁻ w, ENNReal.ofReal (Real.exp (t * before w)) ∂historyMeasure A S ν hνm T := by
  let H := historyMeasure (freezeCoordinatePolicy A encode he.measurable b0) P ν hνm T
  have hprev : (∫⁻ w, ENNReal.ofReal (Real.exp (t * before (encode (w.1, b0), w.2))) ∂H) =
      ∫⁻ w, ENNReal.ofReal (Real.exp (t * before w)) ∂historyMeasure A S ν hνm T := by
    rw [lintegral_history_independent_coordinate A S P Q encode he b0 ν hνm hA L γ hν T hunused
      (fun w => ENNReal.ofReal (Real.exp (t * before w))) (by fun_prop)]
    apply lintegral_congr
    intro w
    simp_rw [hknown w]
    simp
  rw [lintegral_history_pair_factorization A S P Q encode he b0 ν hνm hA L γ hν T hunused
    (fun w => ENNReal.ofReal (Real.exp (t * after w))) (by fun_prop)]
  calc
    _ ≤ ∫⁻ w, ENNReal.ofReal (Real.exp v) *
        ENNReal.ofReal (Real.exp (t * before (encode (w.1, b0), w.2))) ∂H := by
      apply lintegral_mono_ae
      filter_upwards [hMGF] with w hw
      have hmoment : (∫⁻ p, ENNReal.ofReal (Real.exp (t * increment w p))
          ∂coordinatePairMeasure A Q ν hνm encode he.measurable w) ≤ ENNReal.ofReal (Real.exp v) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hw.1
          (Filter.Eventually.of_forall fun p => (Real.exp_pos _).le)]
        exact ENNReal.ofReal_le_ofReal hw.2
      simp_rw [hadd w, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      calc
        _ ≤ ENNReal.ofReal (Real.exp (t * before (encode (w.1, b0), w.2))) * ENNReal.ofReal (Real.exp v) := by
          gcongr
        _ = _ := mul_comm _ _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hprev]

/-- A finite nonnegative exponential integral gives the corresponding ordinary MGF estimate. -/
private theorem integral_exp_le_of_lintegral_exp_le {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (hX : Measurable X) (t v : ℝ)
    (hb : (∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P) ≤ ENNReal.ofReal (Real.exp v)) :
    Integrable (fun ω => Real.exp (t * X ω)) P ∧
      (∫ ω, Real.exp (t * X ω) ∂P) ≤ Real.exp v := by
  have hnonneg : 0 ≤ᵐ[P] (fun ω => Real.exp (t * X ω)) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hI : Integrable (fun ω => Real.exp (t * X ω)) P :=
    (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) hnonneg).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)
  refine ⟨hI, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnonneg] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos v).le).1 hb


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



private theorem seedGaussian_prefixSeed_before {d u n : ℕ} (p j : ℕ) (s : Seed d u n) (hj : j < p) :
    seedGaussian (prefixSeed p s) j = seedGaussian s j := by
  unfold seedGaussian
  split_ifs with h
  · simp [prefixSeed, hj]
  · rfl

private theorem prefixSeed_eq_of_coords {d u n : ℕ} (p : ℕ) (s t : Seed d u n)
    (hc : s.1 = t.1) (hg : ∀ j < p, seedGaussian s j = seedGaussian t j) :
    prefixSeed p s = prefixSeed p t := by
  apply Prod.ext
  · exact hc
  funext j
  by_cases hj : j.val < p
  · have h := hg j.val hj
    simpa only [prefixSeed, seedGaussian, dif_pos j.isLt, hj, ↓reduceIte] using h
  · simp [prefixSeed, hj]

private theorem prefixSeed_insertGaussian_before {d u n : ℕ} (i : Fin (n + 1))
    (p : ℕ) (hp : p ≤ i.val) (w : GaussianRemainder d u n) (x y : Space d) :
    prefixSeed p (insertGaussianSeed i (w, x)) = prefixSeed p (insertGaussianSeed i (w, y)) := by
  apply prefixSeed_eq_of_coords p (insertGaussianSeed i (w, x)) (insertGaussianSeed i (w, y)) rfl
  intro j hj
  exact seedGaussian_insert_before i w x y j (by omega)



private theorem measurable_beforePair (p : ℕ) : Measurable (beforePair (p := p)) := by
  unfold beforePair
  fun_prop





/-- Cumulative statistics constructed this way cannot depend on a future Gaussian coordinate. -/
private theorem pairSum_eq_of_coords {d u n : ℕ}
    (increment : (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ)
    (s t : Seed d u n) (hc : s.1 = t.1) : ∀ (p : ℕ) (ys : Fin (2 * p) → ℝ),
    (∀ j < p, seedGaussian s j = seedGaussian t j) → pairSum increment p s ys = pairSum increment p t ys := by
  intro p
  induction p with
  | zero => intros; rfl
  | succ p ih =>
      intro ys hg
      simp only [pairSum]
      rw [ih _ (fun j hj => hg j (by omega)),
        prefixSeed_eq_of_coords p s t hc (fun j hj => hg j (by omega)), hg p (by omega)]

private theorem pairSum_insertGaussian_before {d u n : ℕ}
    (increment : (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ)
    (i : Fin (n + 1)) (p : ℕ) (hp : p ≤ i.val) (w : GaussianRemainder d u n)
    (x y : Space d) (ys : Fin (2 * p) → ℝ) :
    pairSum increment p (insertGaussianSeed i (w, x)) ys =
      pairSum increment p (insertGaussianSeed i (w, y)) ys := by
  apply pairSum_eq_of_coords increment (insertGaussianSeed i (w, x)) (insertGaussianSeed i (w, y)) rfl p ys
  intro j hj
  exact seedGaussian_insert_before i w x y j (by omega)


private theorem seedGaussian_insert_current {d u n : ℕ} (i : Fin (n + 1))
    (w : GaussianRemainder d u n) (x : Space d) :
    seedGaussian (insertGaussianSeed i (w, x)) i.val = x := by
  simp [seedGaussian, insertGaussianSeed, i.isLt]

private theorem pairSum_snoc {d u n : ℕ}
    (increment : (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ)
    (p : ℕ) (s : Seed d u n) (ys : Fin (2 * p) → ℝ) (y y' : ℝ) :
    pairSum increment (p + 1) s (Fin.snoc (Fin.snoc ys y) y') =
      pairSum increment p s ys + increment p (prefixSeed p s) ys ((seedGaussian s p, y), y') := by
  have hb : beforePair (fun j : Fin (2 * p + 2) =>
      (Fin.snoc (α := fun _ => ℝ) (Fin.snoc ys y) y') ⟨j.val, by omega⟩) = ys := by
    funext j
    change Fin.snoc (α := fun _ => ℝ) (Fin.snoc ys y) y' j.castSucc.castSucc = ys j
    simp only [Fin.snoc_castSucc]
  dsimp only [pairSum]
  rw [hb]
  simp (disch := omega) [Fin.snoc]

private theorem pairSum_pairHistoryMap {d u n : ℕ}
    (increment : (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ)
    (i : Fin (n + 1)) (w : GaussianRemainder d u n × (Fin (2 * i.val) → ℝ))
    (p : (Space d × ℝ) × ℝ) :
    pairSum increment (i.val + 1) (pairHistoryMap (insertGaussianSeed i) w p).1
        (pairHistoryMap (insertGaussianSeed i) w p).2 =
      pairSum increment i.val (insertGaussianSeed i (w.1, 0)) w.2 +
        increment i.val (prefixSeed i.val (insertGaussianSeed i (w.1, 0))) w.2 p := by
  dsimp only [pairHistoryMap]
  rw [pairSum_snoc, pairSum_insertGaussian_before increment i i.val le_rfl w.1 p.1.1 0 w.2,
    prefixSeed_insertGaussian_before i i.val le_rfl w.1 p.1.1 0, seedGaussian_insert_current]

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







private theorem seedGaussian_insert_remove_ne {d u n : ℕ} (i : Fin (n + 1))
    (s : Seed d u n) (x : Space d) (j : ℕ) (hji : j ≠ i.val) :
    seedGaussian (insertGaussianSeed i (removeGaussianSeed i s, x)) j = seedGaussian s j := by
  unfold seedGaussian
  split_ifs with hj
  · have hfin : (⟨j, hj⟩ : Fin (n + 1)) ≠ i := fun h => hji (congrArg Fin.val h)
    simp [insertGaussianSeed, removeGaussianSeed, Fin.insertNth_removeNth, hfin]
  · rfl

private theorem seedGaussian_canonical_le {d u n : ℕ} (i : Fin (n + 1))
    (w : GaussianRemainder d u n) (x : Space d) (j : ℕ) (hj : j ≤ i.val) :
    seedGaussian (insertGaussianSeed i (canonicalGaussianRemainder i w, x)) j =
      seedGaussian (insertGaussianSeed i (w, x)) j := by
  by_cases he : j = i.val
  · subst j
    rw [seedGaussian_insert_current, seedGaussian_insert_current]
  · have hlt : j < i.val := by omega
    rw [canonicalGaussianRemainder, seedGaussian_insert_remove_ne i _ x j he,
      seedGaussian_prefixSeed_before i.val j _ hlt]
    exact seedGaussian_insert_before i w 0 x j hlt

private theorem policy_query_canonicalGaussianRemainder {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (i : Fin (cfg.horizon + 1)) (w : GaussianRemainder d u cfg.horizon) (x : Space d)
    (τ : ℕ) (hτ : τ ≤ 2 * i.val + 1) (ys : Fin τ → ℝ) :
    (policy (u := u) cfg K hK R anchor).query τ
      (insertGaussianSeed i (canonicalGaussianRemainder i w, x)) ys =
    (policy (u := u) cfg K hK R anchor).query τ (insertGaussianSeed i (w, x)) ys := by
  apply policy_seed_prefix
  · intro j hj
    rfl
  · intro j hj
    exact seedGaussian_canonical_le i w x j (by omega)



private theorem observationKernel_canonicalGaussianRemainder {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (i : Fin (cfg.horizon + 1)) (w : GaussianRemainder d u cfg.horizon) (x : Space d)
    (τ : ℕ) (hτ : τ ≤ 2 * i.val + 1) (ys : Fin τ → ℝ) :
    observationKernel (policy (u := u) cfg K hK R anchor) ν hνm τ
      (insertGaussianSeed i (canonicalGaussianRemainder i w, x), ys) =
    observationKernel (policy (u := u) cfg K hK R anchor) ν hνm τ
      (insertGaussianSeed i (w, x), ys) := by
  change ν τ _ ys _ = ν τ _ ys _
  rw [policy_query_canonicalGaussianRemainder cfg K hK R anchor i w x τ hτ ys]
  congr 1
  funext j
  exact policy_query_canonicalGaussianRemainder cfg K hK R anchor i w x j
    (Nat.le_trans (Nat.le_of_lt j.isLt) hτ) _

private theorem coordinateFirstKernel_canonicalGaussianRemainder {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (i : Fin (cfg.horizon + 1))
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) :
    coordinateFirstKernel (policy (u := u) cfg K hK R anchor) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) (canonicalGaussianRemainder i w.1, w.2) =
    coordinateFirstKernel (policy (u := u) cfg K hK R anchor) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w := by
  apply Kernel.ext
  intro x
  exact observationKernel_canonicalGaussianRemainder cfg K hK R anchor ν hνm i w.1 x
    (2 * i.val) (by omega) w.2

private theorem coordinateSecondKernel_canonicalGaussianRemainder {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (i : Fin (cfg.horizon + 1))
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) :
    coordinateSecondKernel (policy (u := u) cfg K hK R anchor) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) (canonicalGaussianRemainder i w.1, w.2) =
    coordinateSecondKernel (policy (u := u) cfg K hK R anchor) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w := by
  apply Kernel.ext
  intro p
  exact observationKernel_canonicalGaussianRemainder cfg K hK R anchor ν hνm i w.1 p.1
    (2 * i.val + 1) le_rfl (Fin.snoc w.2 p.2)

private theorem coordinatePairMeasure_canonicalGaussianRemainder {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (i : Fin (cfg.horizon + 1))
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) :
    coordinatePairMeasure (policy (u := u) cfg K hK R anchor) (gaussian d) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) (canonicalGaussianRemainder i w.1, w.2) =
    coordinatePairMeasure (policy (u := u) cfg K hK R anchor) (gaussian d) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w := by
  unfold coordinatePairMeasure
  rw [coordinateFirstKernel_canonicalGaussianRemainder, coordinateSecondKernel_canonicalGaussianRemainder]





end LG2021.Concentration

end
end

/- LG2021ConcentrationPathFinite -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal

/-- Conditional exponential moments accumulate over the concrete adaptive paired path law. -/
private theorem lintegral_exp_pairSum_le {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ) (γ : ℝ)
    (hν : NoiseCond K L γ ν)
    (increment : (p : ℕ) → Seed d u cfg.horizon → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ)
    (hinc : ∀ p, Measurable (fun w : Seed d u cfg.horizon ×
      ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) => increment p w.1 w.2.1 w.2.2))
    (t : ℝ) (v : ℕ → ℝ) (N : ℕ) (hN : N ≤ cfg.horizon + 1)
    (hstep : ∀ p < N, ∀ hp : p < cfg.horizon + 1,
      ∀ᵐ w ∂historyMeasure (freezeCoordinatePolicy (policy (u := u) cfg K hK R anchor)
        (insertGaussianSeed ⟨p, hp⟩) (measurable_insertGaussianSeed cfg ⟨p, hp⟩) 0)
        (gaussianRemainderMeasure d u cfg) ν hνm (2 * p),
      let inc := increment p (prefixSeed p (insertGaussianSeed ⟨p, hp⟩ (w.1, 0))) w.2
      let μ := coordinatePairMeasure (policy (u := u) cfg K hK R anchor) (gaussian d) ν hνm
        (insertGaussianSeed ⟨p, hp⟩) (measurable_insertGaussianSeed cfg ⟨p, hp⟩) w
      Integrable (fun z => Real.exp (t * inc z)) μ ∧
        (∫ z, Real.exp (t * inc z) ∂μ) ≤ Real.exp (v p)) :
    (∫⁻ w, ENNReal.ofReal (Real.exp (t * pairSum increment N w.1 w.2))
      ∂historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N)) ≤
      ENNReal.ofReal (Real.exp (∑ p ∈ Finset.range N, v p)) := by
  have hA := policy_isOn (u := u) cfg K hK R ha
  induction N with
  | zero =>
      letI := historyMeasure_probability (policy (u := u) cfg K hK R anchor)
        (seedMeasure d u cfg) ν hνm hA L γ hν 0
      simp [pairSum]
  | succ N ih =>
      have hp : N < cfg.horizon + 1 := by omega
      have hprev := ih (by omega) (fun p hpn hp => hstep p (by omega) hp)
      have hbound := lintegral_exp_pair_step_le
        (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg)
        (gaussianRemainderMeasure d u cfg) (gaussian d)
        (insertGaussianSeed ⟨N, hp⟩) (insertGaussianSeed_measurePreserving cfg ⟨N, hp⟩)
        0 ν hνm hA L γ hν (2 * N)
        (fun τ hτ w x ys => policy_insertGaussianSeed_before cfg K hK R anchor ⟨N, hp⟩ τ hτ w x 0 ys)
        (fun w => pairSum increment N w.1 w.2) (fun w => pairSum increment (N + 1) w.1 w.2)
        (measurable_pairSum increment hinc N) (measurable_pairSum increment hinc (N + 1))
        (fun w x => pairSum_insertGaussian_before increment ⟨N, hp⟩ N le_rfl w.1 x 0 w.2)
        (fun w => increment N (prefixSeed N (insertGaussianSeed ⟨N, hp⟩ (w.1, 0))) w.2)
        (pairSum_pairHistoryMap increment ⟨N, hp⟩) t (v N) (hstep N (by omega) hp)
      calc
        _ ≤ ENNReal.ofReal (Real.exp (v N)) *
            ∫⁻ w, ENNReal.ofReal (Real.exp (t * pairSum increment N w.1 w.2))
              ∂historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N) := hbound
        _ ≤ ENNReal.ofReal (Real.exp (v N)) *
            ENNReal.ofReal (Real.exp (∑ p ∈ Finset.range N, v p)) := by gcongr
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, Finset.sum_range_succ]
          congr 2
          ring


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

/-- The actual stopped directional increment satisfies its bounded-parameter MGF estimate. -/
private theorem gradientIncrement_pair_mgf {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (enabled : ℕ → Bool)
    (active : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Bool)
    (z η : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Space d)
    (hpos : 0 < cfg.lambda) (hsmall : cfg.lambda ≤ 1 / 2) (hd : (d : ℝ) * cfg.lambda ≤ 1 / 2)
    (i : Fin (cfg.horizon + 1))
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) {t : ℝ} (ht : |t| * 3072 ≤ 1 / 2) :
    let inc := gradientIncrement cfg K hK R anchor ν hνm enabled active z η i.val
      (prefixSeed i.val (insertGaussianSeed i (w.1, 0))) w.2
    let μ := coordinatePairMeasure (policy (u := u) cfg K hK R anchor) (gaussian d) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
    Integrable (fun q => Real.exp (t * inc q)) μ ∧
      (∫ q, Real.exp (t * inc q) ∂μ) ≤
        Real.exp (if enabled i.val then 16 * 3072^2 * t^2 else 0) := by
  dsimp only
  have hA := policy_isOn (u := u) cfg K hK R ha
  have hn := BilateralProfitMHR.CorollaryTransport.unitNoiseCond_noiseCond K L ν hν
  letI := coordinatePairMeasure_probability _ (gaussian d) ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) hA L 1 hn w
  simp only [gradientIncrement, dif_pos i.isLt]
  by_cases he : enabled i.val = true
  · simp only [he, Bool.true_and, ↓reduceIte]
    split_ifs with hac hbounds
    · have h := gaussianPolicy_gradientPredictable_moment cfg K hK R anchor ha i ν hνm L hν hL
        (canonicalGaussianRemainder i w.1, w.2)
        (z i.val (prefixSeed i.val (insertGaussianSeed i (w.1, 0)), w.2))
        (η i.val (prefixSeed i.val (insertGaussianSeed i (w.1, 0)), w.2)) hpos hsmall hd hbounds.1 hbounds.2
      dsimp only at h
      rw [coordinatePairMeasure_canonicalGaussianRemainder] at h
      apply mgf_le_of_exp_abs_scaled _ _ _ (by norm_num : (0 : ℝ) < 3072) h.1 h.2.1 h.2.2 ht
      have hG : Measurable (fun q : (Space d × ℝ) × ℝ => gradientCoefficient cfg.lambda cfg.radius (z i.val (prefixSeed i.val (insertGaussianSeed i (w.1, 0)), w.2)) q.1.1) := (Algorithm.measurable_gradientCoefficient cfg.lambda cfg.radius).comp
        (f := fun q : (Space d × ℝ) × ℝ =>
          (z i.val (prefixSeed i.val (insertGaussianSeed i (w.1, 0)), w.2), q.1.1))
        (measurable_const.prodMk measurable_fst.fst)
      exact (measurable_fst.snd.mul (hG.inner measurable_const)).sub_const _
    all_goals
      simp only [mul_zero, Real.exp_zero]
      refine ⟨integrable_const 1, ?_⟩
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      exact Real.one_le_exp (by positivity)
  · have he' : enabled i.val = false := Bool.eq_false_iff.mpr he
    simp [he']

end LG2021.Concentration

end
end

/- LG2021ConcentrationBernstein -/
section

set_option autoImplicit false

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory

/-- Optimizing the Chernoff parameter on a finite MGF interval yields the Bernstein regimes. -/
private theorem measure_ge_le_of_bounded_mgf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    {V τ : ℝ} (hV : 0 < V) (hτ : 0 < τ)
    (hmgf : ∀ t : ℝ, 0 ≤ t → t ≤ τ →
      Integrable (fun ω => Real.exp (t * X ω)) P ∧ mgf X P t ≤ Real.exp (V * t ^ 2))
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ X ω} ≤ Real.exp (-min (ε ^ 2 / (4 * V)) (ε * τ / 2)) := by
  let t := min (ε / (2 * V)) τ
  have ht : 0 ≤ t := le_min (div_nonneg hε (by positivity)) hτ.le
  have htτ : t ≤ τ := min_le_right _ _
  obtain ⟨hI, hM⟩ := hmgf t ht htτ
  calc
    _ ≤ Real.exp (-t * ε) * mgf X P t := measure_ge_le_exp_mul_mgf ε ht hI
    _ ≤ Real.exp (-t * ε) * Real.exp (V * t ^ 2) := by gcongr
    _ = Real.exp (-t * ε + V * t ^ 2) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      by_cases h : ε / (2 * V) ≤ τ
      · have ht' : t = ε / (2 * V) := min_eq_left h
        have heq : -t * ε + V * t ^ 2 = -(ε ^ 2 / (4 * V)) := by
          rw [ht']
          field_simp
          <;> ring
        rw [heq]
        exact neg_le_neg (min_le_left _ _)
      · have ht' : t = τ := min_eq_right (le_of_not_ge h)
        have hετ : 2 * V * τ ≤ ε := by
          have h' : τ ≤ ε / (2 * V) := le_of_not_ge h
          have h'' := (le_div_iff₀ (show 0 < 2 * V by positivity)).1 h'
          nlinarith
        have hbound : -t * ε + V * t ^ 2 ≤ -(ε * τ / 2) := by
          rw [ht']
          nlinarith [mul_le_mul_of_nonneg_right hετ hτ.le]
        exact hbound.trans (neg_le_neg (min_le_right _ _))

/-- A symmetric finite MGF interval gives the two-sided Bernstein bound. -/
private theorem measure_abs_ge_le_of_bounded_mgf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    {V τ : ℝ} (hV : 0 < V) (hτ : 0 < τ)
    (hmgf : ∀ t : ℝ, |t| ≤ τ →
      Integrable (fun ω => Real.exp (t * X ω)) P ∧ mgf X P t ≤ Real.exp (V * t ^ 2))
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |X ω|} ≤
      2 * Real.exp (-min (ε ^ 2 / (4 * V)) (ε * τ / 2)) := by
  have hp := measure_ge_le_of_bounded_mgf P X hV hτ
    (fun t ht htτ => hmgf t (by simpa only [abs_of_nonneg ht] using htτ)) hε
  have hn := measure_ge_le_of_bounded_mgf P (fun ω => -X ω) hV hτ
    (fun t ht htτ => by
      have h := hmgf (-t) (by simpa only [abs_neg, abs_of_nonneg ht] using htτ)
      simpa only [mul_neg, neg_mul, neg_sq, mgf] using h) hε
  have heq : {ω | ε ≤ |X ω|} = {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [heq]
  exact (measureReal_union_le _ _).trans (by linarith)


end LG2021.Concentration

end

/- LG2021OracleConfidenceArithmetic -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory








private theorem oracleMomentConstant_pos : 0 < oracleMomentConstant := by norm_num [oracleMomentConstant]
private theorem oracleConcentrationConstant_pos : 0 < oracleConcentrationConstant := by
  norm_num [oracleConcentrationConstant]





private theorem gradient_confidence_quadratic_exponent {H m : ℝ}
    (hH : 0 ≤ H) (hm : 0 < m) :
    H ≤ (m*gradientConfidenceThreshold H m)^2/(64*m*(3072 : ℝ)^2) := by
  have hC := oracleConcentrationConstant_pos
  have hsq : (Real.sqrt (H/(oracleConcentrationConstant*m)))^2 =
      H/(oracleConcentrationConstant*m) := Real.sq_sqrt (by positivity)
  have hcoef : 64*(3072 : ℝ)^2*oracleConcentrationConstant ≤ oracleMomentConstant^2 := by
    norm_num [oracleConcentrationConstant, oracleMomentConstant]
  unfold gradientConfidenceThreshold
  rw [mul_pow, mul_pow, hsq]
  apply (le_div_iff₀ (by positivity : 0 < 64*m*(3072 : ℝ)^2)).2
  apply (mul_le_mul_iff_right₀ (show 0 < oracleConcentrationConstant*m by positivity)).1
  have hmul := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ H*m^2 by positivity)
  field_simp
  nlinarith

private theorem gradient_confidence_linear_exponent {H m : ℝ}
    (hH : 0 ≤ H) (hm : 0 < m) (hmany : H/oracleConcentrationConstant ≤ m) :
    H ≤ (m*gradientConfidenceThreshold H m)/(4*(3072 : ℝ)) := by
  have hC := oracleConcentrationConstant_pos
  let s := Real.sqrt (H/(oracleConcentrationConstant*m))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2 = H/(oracleConcentrationConstant*m) := Real.sq_sqrt (by positivity)
  have hhm : H ≤ oracleConcentrationConstant*m := by
    have h := (div_le_iff₀ hC).1 hmany
    nlinarith
  have hs1 : s ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one (by positivity : 0 < oracleConcentrationConstant*m)).2 hhm
  have hs2 : s^2 ≤ s := by nlinarith
  have hHeq : H = oracleConcentrationConstant*m*s^2 := by
    rw [hsq]
    field_simp
  have hcoef : 4*(3072 : ℝ)*oracleConcentrationConstant ≤ oracleMomentConstant := by
    norm_num [oracleConcentrationConstant, oracleMomentConstant]
  unfold gradientConfidenceThreshold
  change H ≤ m*(oracleMomentConstant*s)/(4*(3072 : ℝ))
  apply (le_div_iff₀ (by norm_num : 0 < 4*(3072 : ℝ))).2
  rw [hHeq]
  have h1 := mul_le_mul_of_nonneg_left hs2 (show 0 ≤ oracleMomentConstant*m by have hM := oracleMomentConstant_pos; positivity)
  have h2 := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ m*s^2 by positivity)
  nlinarith

private theorem gradient_confidence_bernstein_exponent {H m : ℝ}
    (hH : 0 ≤ H) (hm : 0 < m) (hmany : H/oracleConcentrationConstant ≤ m) :
    H ≤ min ((m*gradientConfidenceThreshold H m)^2/(64*m*(3072 : ℝ)^2))
      ((m*gradientConfidenceThreshold H m)/(4*(3072 : ℝ))) :=
  le_min (gradient_confidence_quadratic_exponent hH hm)
    (gradient_confidence_linear_exponent hH hm hmany)







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



private theorem sum_enabled {M : Type*} [AddCommMonoid M] (enabled : ℕ → Bool) (N : ℕ) (v : M) :
    (∑ p ∈ Finset.range N, if enabled p then v else 0) = enabledCount enabled N • v := by
  rw [← Finset.sum_filter]
  simp [enabledCount]

private theorem enabledCount_interval (a b : ℕ) :
    enabledCount (fun p => decide (a ≤ p)) b = b - a := by
  unfold enabledCount
  have he : (Finset.range b).filter (fun p => decide (a ≤ p)) = Finset.Ico a b := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq, Finset.mem_Ico]
    tauto
  rw [he, Nat.card_Ico]



end LG2021.Concentration

namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal

/-- Concrete stopped directional estimates accumulate exponential moments under the actual path law. -/
private theorem gradient_pairSum_mgf {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (enabled : ℕ → Bool)
    (active : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Bool)
    (z η : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Space d)
    (hactive : ∀ p, Measurable (active p)) (hz : ∀ p, Measurable (z p)) (hη : ∀ p, Measurable (η p))
    (hpos : 0 < cfg.lambda) (hsmall : cfg.lambda ≤ 1 / 2) (hd : (d : ℝ) * cfg.lambda ≤ 1 / 2)
    (N : ℕ) (hN : N ≤ cfg.horizon + 1) {t : ℝ} (ht : |t| * 3072 ≤ 1 / 2) :
    let P := historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N)
    let X := fun w : Seed d u cfg.horizon × (Fin (2 * N) → ℝ) => pairSum (gradientIncrement cfg K hK R anchor ν hνm enabled active z η) N w.1 w.2
    Integrable (fun w => Real.exp (t * X w)) P ∧
      mgf X P t ≤ Real.exp ((16 * (enabledCount enabled N : ℝ) * 3072^2) * t^2) := by
  have hn := BilateralProfitMHR.CorollaryTransport.unitNoiseCond_noiseCond K L ν hν
  have hinc := measurable_gradientIncrement cfg K hK R anchor ha ν hνm L 1 hn enabled active z η hactive hz hη
  have hb := lintegral_exp_pairSum_le cfg K hK R anchor ha ν hνm L 1 hn
    (gradientIncrement cfg K hK R anchor ν hνm enabled active z η) hinc t
    (fun p => if enabled p then 16 * 3072^2 * t^2 else 0) N hN
    (fun p hp hph => Filter.Eventually.of_forall fun w =>
      gradientIncrement_pair_mgf cfg K hK R anchor ha ν hνm L hν hL enabled active z η
        hpos hsmall hd ⟨p, hph⟩ w ht)
  have hfull := integral_exp_le_of_lintegral_exp_le
    (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N))
    (fun w => pairSum (gradientIncrement cfg K hK R anchor ν hνm enabled active z η) N w.1 w.2)
    (measurable_pairSum _ hinc N) t _ hb
  refine ⟨hfull.1, ?_⟩
  change (∫ w : Seed d u cfg.horizon × (Fin (2 * N) → ℝ), Real.exp (t * pairSum (gradientIncrement cfg K hK R anchor ν hνm enabled active z η) N w.1 w.2) ∂_) ≤ _
  convert hfull.2 using 1
  rw [sum_enabled]
  simp only [nsmul_eq_mul]
  congr 1
  ring

/-- The actual directional process obeys the Bernstein confidence radius in its quadratic regime. -/
private theorem gradient_pairSum_mean_confidence {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (enabled : ℕ → Bool)
    (active : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Bool)
    (z η : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Space d)
    (hactive : ∀ p, Measurable (active p)) (hz : ∀ p, Measurable (z p)) (hη : ∀ p, Measurable (η p))
    (hpos : 0 < cfg.lambda) (hsmall : cfg.lambda ≤ 1 / 2) (hd : (d : ℝ) * cfg.lambda ≤ 1 / 2)
    (N : ℕ) (hN : N ≤ cfg.horizon + 1) (H : ℝ) (hH : 0 ≤ H) (hm : 0 < enabledCount enabled N)
    (hmany : H / oracleConcentrationConstant ≤ (enabledCount enabled N : ℝ)) :
    (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N)).real
      {w | gradientConfidenceThreshold H (enabledCount enabled N : ℝ) ≤
        |pairSum (gradientIncrement cfg K hK R anchor ν hνm enabled active z η) N w.1 w.2 /
          (enabledCount enabled N : ℝ)|} ≤ 2 * Real.exp (-H) := by
  have hn := BilateralProfitMHR.CorollaryTransport.unitNoiseCond_noiseCond K L ν hν
  let P := historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N)
  let X := fun w : Seed d u cfg.horizon × (Fin (2 * N) → ℝ) => pairSum (gradientIncrement cfg K hK R anchor ν hνm enabled active z η) N w.1 w.2
  let m : ℝ := enabledCount enabled N
  have hmp : 0 < m := by dsimp [m]; exact_mod_cast hm
  letI : IsProbabilityMeasure P := historyMeasure_probability _ _ ν hνm
    (policy_isOn (u := u) cfg K hK R ha) L 1 hn (2 * N)
  have hb := measure_abs_ge_le_of_bounded_mgf P X (V := 16 * m * 3072^2) (τ := 1 / (2 * 3072))
    (by positivity) (by norm_num)
    (fun t ht => gradient_pairSum_mgf cfg K hK R anchor ha ν hνm L hν hL
      enabled active z η hactive hz hη hpos hsmall hd N hN (by linarith))
    (ε := m * gradientConfidenceThreshold H m)
    (by unfold gradientConfidenceThreshold; exact mul_nonneg hmp.le (mul_nonneg oracleMomentConstant_pos.le (Real.sqrt_nonneg _)))
  have heq : {w | gradientConfidenceThreshold H m ≤ |X w / m|} =
      {w | m * gradientConfidenceThreshold H m ≤ |X w|} := by
    ext w
    simp only [Set.mem_setOf_eq, abs_div, abs_of_pos hmp, le_div_iff₀ hmp, mul_comm m]
  change P.real {w | gradientConfidenceThreshold H m ≤ |X w / m|} ≤ _
  rw [heq]
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.exp_le_exp.mpr
  have hnum := gradient_confidence_bernstein_exponent hH hmp hmany
  convert neg_le_neg hnum using 1 <;> congr 2 <;> ring

end LG2021.Concentration

end
end

/- LG2021ConcentrationTerminalConfidence -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal

/-- Finite unions of prefix events are measured on the same terminal adaptive history law. -/
private theorem terminal_prefix_union_le {X Ω ι : Type} [MeasurableSpace X] [MeasurableSpace Ω] [Fintype ι]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν)
    (N : ℕ) (T : ι → ℕ) (hT : ∀ i, T i ≤ N)
    (E : (i : ι) → Set (Ω × (Fin (T i) → ℝ))) (hE : ∀ i, MeasurableSet (E i))
    (ε : ι → ℝ) (hε : ∀ i, (historyMeasure A P ν hνm (T i)).real (E i) ≤ ε i) :
    (historyMeasure A P ν hνm N).real {w | ∃ i, historyPrefix (hT i) w ∈ E i} ≤ ∑ i, ε i := by
  letI := historyMeasure_probability A P ν hνm hA L γ hν N
  have heq : {w | ∃ i, historyPrefix (hT i) w ∈ E i} = ⋃ i, (historyPrefix (hT i)) ⁻¹' E i := by
    ext w
    simp
  rw [heq]
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [historyMeasure_prefix_probability A P ν hνm hA L γ hν (hT i) (E i) (hE i)]
  exact hε i



/-- Uniform directional confidence for a finite family of actual stopped comparisons. -/
private theorem gradient_terminal_union_confidence {d u : ℕ} {ι : Type} [Fintype ι] (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (enabled : ι → ℕ → Bool)
    (active : ι → (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Bool)
    (z η : ι → (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Space d)
    (hactive : ∀ i p, Measurable (active i p)) (hz : ∀ i p, Measurable (z i p)) (hη : ∀ i p, Measurable (η i p))
    (hpos : 0 < cfg.lambda) (hsmall : cfg.lambda ≤ 1 / 2) (hd : (d : ℝ) * cfg.lambda ≤ 1 / 2)
    (N : ℕ) (hN : N ≤ cfg.horizon + 1) (T : ι → ℕ) (hT : ∀ i, T i ≤ N)
    (H : ℝ) (hH : 0 ≤ H) (allowed : ι → Prop)
    (hm : ∀ i, allowed i → 0 < enabledCount (enabled i) (T i))
    (hmany : ∀ i, allowed i → H / oracleConcentrationConstant ≤ (enabledCount (enabled i) (T i) : ℝ)) :
    (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N)).real
      {w | ∃ i, allowed i ∧
        gradientConfidenceThreshold H (enabledCount (enabled i) (T i) : ℝ) ≤
          |pairSum (gradientIncrement cfg K hK R anchor ν hνm (enabled i) (active i) (z i) (η i))
            (T i) w.1 (historyPrefix (Nat.mul_le_mul_left 2 (hT i)) w).2 /
              (enabledCount (enabled i) (T i) : ℝ)|} ≤
        (Fintype.card ι : ℝ) * (2 * Real.exp (-H)) := by
  have hn := BilateralProfitMHR.CorollaryTransport.unitNoiseCond_noiseCond K L ν hν
  let A := policy (u := u) cfg K hK R anchor
  have hA := policy_isOn (u := u) cfg K hK R ha
  let E (i : ι) : Set (Seed d u cfg.horizon × (Fin (2 * T i) → ℝ)) :=
    {w | allowed i ∧ gradientConfidenceThreshold H (enabledCount (enabled i) (T i) : ℝ) ≤
      |pairSum (gradientIncrement cfg K hK R anchor ν hνm (enabled i) (active i) (z i) (η i))
        (T i) w.1 w.2 / (enabledCount (enabled i) (T i) : ℝ)|}
  have hE (i : ι) : MeasurableSet (E i) := by
    have hx := measurable_pairSum _
      (measurable_gradientIncrement cfg K hK R anchor ha ν hνm L 1 hn
        (enabled i) (active i) (z i) (η i) (hactive i) (hz i) (hη i)) (T i)
    by_cases hi : allowed i
    · simpa only [E, hi, true_and] using measurableSet_le measurable_const ((hx.div_const (enabledCount (enabled i) (T i) : ℝ)).abs)
    · simp [E, hi]
  have hb (i : ι) : (historyMeasure A (seedMeasure d u cfg) ν hνm (2 * T i)).real (E i) ≤ 2 * Real.exp (-H) := by
    by_cases hi : allowed i
    · simpa only [E, hi, true_and] using gradient_pairSum_mean_confidence cfg K hK R anchor ha ν hνm L hν hL
        (enabled i) (active i) (z i) (η i) (hactive i) (hz i) (hη i) hpos hsmall hd (T i) ((hT i).trans hN) H hH (hm i hi) (hmany i hi)
    · simp [E, hi, (Real.exp_pos (-H)).le]
  have hh := terminal_prefix_union_le A (seedMeasure d u cfg) ν hνm hA L 1 hn
    (2 * N) (fun i => 2 * T i) (fun i => Nat.mul_le_mul_left 2 (hT i)) E hE
    (fun _ => 2 * Real.exp (-H)) hb
  simpa only [E, Set.mem_setOf_eq, historyPrefix, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh

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





end LG2021.Concentration

end
end

/- LG2021StageStarts -/
section

noncomputable section

namespace LG2021.Algorithm

open scoped Classical











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





















end LG2021.Algorithm

end
end

/- LG2021CandidateHitLift -/
section

noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration







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

theorem solution {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < cfg.lambda) (hsmall : cfg.lambda ≤ 1 / 2) (hd : (d : ℝ) * cfg.lambda ≤ 1 / 2)
    (N : ℕ) (hN : N ≤ cfg.horizon + 1) (H : ℝ) (hH : 0 ≤ H) (v : Fin (d+1) → Space d) :
    (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N)).real
      (gradientStageFailure cfg K hK R anchor ν hνm N H v) ≤
        ((N+1 : ℕ) : ℝ)^2 * u * (d+1) * (2 * Real.exp (-H)) := by
  let ι := Fin (N+1) × Fin (N+1) × Fin u × Fin (d+1)
  have h := gradient_terminal_union_confidence (ι := ι) cfg K hK R anchor ha ν hνm L hν hL
    (fun i p => decide (i.1.val ≤ p))
    (fun i => stageActive cfg K R i.1.val)
    (fun i => stageCandidate cfg K R i.1.val i.2.2.1)
    (fun i => stageDirection cfg K R i.1.val i.2.2.1 (v i.2.2.2))
    (fun i => measurable_stageActive cfg K R i.1.val)
    (fun i => measurable_stageCandidate cfg K R i.1.val i.2.2.1)
    (fun i => measurable_stageDirection cfg K R i.1.val i.2.2.1 (v i.2.2.2))
    hpos hsmall hd N hN (fun i => i.2.1.val) (fun i => by have hi := i.2.1.isLt; omega)
    H hH (fun i => i.1.val < i.2.1.val ∧ H / oracleConcentrationConstant ≤ ((i.2.1.val-i.1.val : ℕ) : ℝ))
    (fun i hi => by rw [enabledCount_interval]; omega)
    (fun i hi => by simpa only [enabledCount_interval] using hi.2)
  have heq : {w | ∃ i : ι, (i.1.val < i.2.1.val ∧ H / oracleConcentrationConstant ≤ ((i.2.1.val-i.1.val : ℕ) : ℝ)) ∧
      gradientConfidenceThreshold H ((i.2.1.val-i.1.val : ℕ) : ℝ) ≤
      |stageGradientError cfg K hK R anchor ν hνm i.1.val i.2.2.1 (v i.2.2.2) i.2.1.val
        (historyPrefix (by have hi := i.2.1.isLt; omega : 2*i.2.1.val ≤ 2*N) w) /
          ((i.2.1.val-i.1.val : ℕ) : ℝ)|} = gradientStageFailure cfg K hK R anchor ν hνm N H v := by
    ext w
    simp only [gradientStageFailure, Set.mem_setOf_eq, Prod.exists, ι, and_assoc]
  simp only [enabledCount_interval] at h
  change (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2*N)).real
    {w | ∃ i : ι, (i.1.val < i.2.1.val ∧ H / oracleConcentrationConstant ≤ ((i.2.1.val-i.1.val : ℕ) : ℝ)) ∧
      gradientConfidenceThreshold H ((i.2.1.val-i.1.val : ℕ) : ℝ) ≤
      |stageGradientError cfg K hK R anchor ν hνm i.1.val i.2.2.1 (v i.2.2.2) i.2.1.val
        (historyPrefix (by have hi := i.2.1.isLt; omega : 2*i.2.1.val ≤ 2*N) w) /
          ((i.2.1.val-i.1.val : ℕ) : ℝ)|} ≤ _ at h
  rw [heq] at h
  convert h using 1
  simp [ι, pow_two, mul_assoc]
