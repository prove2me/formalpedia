-- Prove2me | solution 1 for LG2021.Algorithm.candidateTerminalEvent_failure_le
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T16:50:49.338528+00:00
-- url     : https://prove2.me/submissions/95c55796-b219-4e32-a009-6c60d8a5f53a

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

private theorem isClosed_cutSet {d : ℕ} (cut : Cut d) : IsClosed (cutSet cut) :=
  isClosed_le (by fun_prop) continuous_const

private theorem convex_cutSet {d : ℕ} (cut : Cut d) : Convex ℝ (cutSet cut) :=
  convex_halfSpace_le ⟨(innerSL ℝ cut.1).map_add, (innerSL ℝ cut.1).map_smul⟩ cut.2

private theorem isCompact_activeBody {d p : ℕ} {K : Set (Space d)} (hK : IsCompact K)
    (cuts : Fin p → Cut d) : IsCompact (activeBody K cuts) :=
  hK.inter_right (isClosed_iInter fun i => isClosed_cutSet (cuts i))

private theorem convex_activeBody {d p : ℕ} {K : Set (Space d)} (hK : Convex ℝ K)
    (cuts : Fin p → Cut d) : Convex ℝ (activeBody K cuts) :=
  hK.inter (convex_iInter fun i => convex_cutSet (cuts i))

private theorem zero_cutSet {d : ℕ} : cutSet (0 : Cut d) = Set.univ := by
  ext x
  simp [cutSet]

private theorem matrixAction_add {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x y : Space d) :
    matrixAction M (x + y) = matrixAction M x + matrixAction M y := by
  simp [matrixAction, mulVec_add]

private theorem matrixAction_sub {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x y : Space d) :
    matrixAction M (x - y) = matrixAction M x - matrixAction M y := by
  simp [matrixAction, mulVec_sub]







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





private theorem euclidean_unitBall_iff {m : ℕ} (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace.equiv (Fin m) ℝ x ∈ unitBall m ↔
      x ∈ Metric.closedBall 0 1 := by
  have hdot : (EuclideanSpace.equiv (Fin m) ℝ x) ⬝ᵥ
      (EuclideanSpace.equiv (Fin m) ℝ x) = ‖x‖ ^ 2 := by
    simpa only [EuclideanSpace.equiv, PiLp.coe_continuousLinearEquiv, dotProduct, pow_two]
      using (EuclideanSpace.real_norm_sq_eq x).symm
  simp only [ModernConvex.Ellipsoids.unitBall, Set.mem_setOf_eq]
  rw [hdot, Metric.mem_closedBall, dist_zero_right]
  constructor <;> intro h <;> nlinarith [norm_nonneg x]





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





private theorem exists_outerFrame {d : ℕ} {S : Set (Fin d → ℝ)} (hS : IsSolid S) :
    ∃ F : NativeFrame d, OuterFrameSpec S F := by
  obtain ⟨E, hE, _⟩ := (lowner_fritz_john S hS).2.1
  obtain ⟨A, c, hA, rfl⟩ := hE.1
  exact ⟨(A, c), hA, hE⟩



private theorem chosenOuterFrame_spec {d : ℕ} {S : Set (Fin d → ℝ)} (hS : IsSolid S) :
    OuterFrameSpec S (chosenOuterFrame S) := by
  unfold chosenOuterFrame
  rw [dif_pos (exists_outerFrame hS)]
  exact Classical.choose_spec (exists_outerFrame hS)





private theorem nativeCodedBody_solid {d p : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) (hcv : Convex ℝ K) (cuts : Fin p → CutCode d)
    (hi : (interior (codedBody K cuts)).Nonempty) : IsSolid (nativeCodedBody K cuts) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hc := (isCompact_activeBody hK (fun i => decodeCut (cuts i))).image e.continuous
  have hv := (convex_activeBody hcv (fun i => decodeCut (cuts i))).linear_image e.toLinearMap
  have hint : (interior (nativeCodedBody K cuts)).Nonempty := by
    have h := hi.image e.toHomeomorph
    rw [e.toHomeomorph.image_interior] at h
    exact h
  exact ⟨hc.isClosed, hc.isBounded, hv, hint⟩



private theorem measurable_canonicalOuterFrame {d p : ℕ} (K : Set (Space d)) (r : ℝ) :
    Measurable (canonicalOuterFrame (p := p) K r) := measurable_of_countable _

private theorem chosenOuterFrame_coded_spec {d p : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) (hcv : Convex ℝ K) (cuts : Fin p → CutCode d)
    (hi : (interior (codedBody K cuts)).Nonempty) :
    let S := nativeCodedBody K cuts
    let F := chosenOuterFrame S
    F.1.det ≠ 0 ∧ IsMinVolCircumscribed S (ellipsoid F.1 F.2) ∧
      S ⊆ ellipsoid F.1 F.2 ∧
      ellipsoid ((1 / (d : ℝ)) • F.1) F.2 ⊆ S := by
  dsimp only
  have hsolid := nativeCodedBody_solid hK hcv cuts hi
  have hs := chosenOuterFrame_spec hsolid
  exact ⟨hs.1, hs.2, hs.2.2.1,
    ((lowner_fritz_john _ hsolid).2.2 _ _ hs.1 hs.2).1⟩

private theorem codedBody_snoc {d p : ℕ} (K : Set (Space d)) (cuts : Fin p → CutCode d)
    (cut : CutCode d) : codedBody K (Fin.snoc cuts cut) = codedBody K cuts ∩ cutSet (decodeCut cut) := by
  ext x
  simp only [codedBody, activeBody, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro h
    refine ⟨⟨h.1, fun i => ?_⟩, ?_⟩
    · simpa only [Fin.snoc_castSucc] using h.2 i.castSucc
    · simpa only [Fin.snoc_last] using h.2 (Fin.last p)
  · intro h
    refine ⟨h.1.1, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using h.2
    · simpa only [Fin.snoc_castSucc] using h.1.2 j



private theorem codedBody_snoc_zero {d p : ℕ} (K : Set (Space d)) (cuts : Fin p → CutCode d) :
    codedBody K (Fin.snoc cuts 0) = codedBody K cuts := by
  rw [codedBody_snoc]
  have hz : decodeCut (0 : CutCode d) = 0 := by
    simp [decodeCut]
    rfl
  rw [hz, zero_cutSet, Set.inter_univ]

private theorem ball_scaled_unit_parameterization {d : ℕ} {r : ℝ} (hr : 0 < r) (x : Space d) :
    x ∈ Metric.closedBall 0 r ↔ ∃ u : Fin d → ℝ,
      u ∈ unitBall d ∧ x = r • (EuclideanSpace.equiv (Fin d) ℝ).symm u := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  constructor
  · intro hx
    refine ⟨e (r⁻¹ • x), ?_, ?_⟩
    · apply (LG2021.euclidean_unitBall_iff (r⁻¹ • x)).mpr
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      have hxn : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      calc
        r⁻¹ * ‖x‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hxn (inv_nonneg.mpr hr.le)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · simp [e, smul_smul, hr.ne']
  · rintro ⟨u, hu, rfl⟩
    have hunit : ‖e.symm u‖ ≤ 1 := by
      have hu' : e (e.symm u) ∈ unitBall d := by
        rw [e.apply_symm_apply]
        exact hu
      have h := (LG2021.euclidean_unitBall_iff (e.symm u)).mp hu'
      simpa only [Metric.mem_closedBall, dist_zero_right] using h
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact (mul_le_mul_of_nonneg_left hunit hr.le).trans_eq (mul_one r)

private theorem native_frame_image_ball {d : ℕ} (F : Frame d) {r : ℝ} (hr : 0 < r) :
    (EuclideanSpace.equiv (Fin d) ℝ) '' (frameApply F '' Metric.closedBall 0 r) =
      ellipsoid (r • F.1) ((EuclideanSpace.equiv (Fin d) ℝ) F.2) := by
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have heval (u : Fin d → ℝ) : e (frameApply F (r • e.symm u)) =
      (r • F.1) *ᵥ u + e F.2 := by
    change e (e.symm (F.1 *ᵥ e (r • e.symm u)) + F.2) = _
    rw [map_add, e.apply_symm_apply, map_smul, e.apply_symm_apply,
      mulVec_smul, smul_mulVec]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨u, hu, rfl⟩ := (ball_scaled_unit_parameterization hr z).mp hz
    exact ⟨u, hu, heval u⟩
  · rintro ⟨u, hu, hx⟩
    refine ⟨frameApply F (r • e.symm u), ⟨r • e.symm u, ?_, rfl⟩, ?_⟩
    · exact (ball_scaled_unit_parameterization hr _).mpr ⟨u, hu, rfl⟩
    · exact (heval u).trans hx.symm

private theorem canonicalOuterFrame_image_ball {d p : ℕ} (K : Set (Space d))
    {r : ℝ} (hr : 0 < r) (cuts : Fin p → CutCode d) :
    (EuclideanSpace.equiv (Fin d) ℝ) ''
      (frameApply (canonicalOuterFrame K r cuts) '' Metric.closedBall 0 r) =
      ellipsoid (chosenOuterFrame (nativeCodedBody K cuts)).1
        (chosenOuterFrame (nativeCodedBody K cuts)).2 := by
  rw [native_frame_image_ball _ hr]
  simp only [canonicalOuterFrame, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
    ContinuousLinearEquiv.apply_symm_apply]

private theorem codedBody_subset_canonicalOuterFrame {d p : ℕ} {K : Set (Space d)}
    (hK : IsCompact K) (hcv : Convex ℝ K) {r : ℝ} (hr : 0 < r)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty) :
    codedBody K cuts ⊆ frameApply (canonicalOuterFrame K r cuts) '' Metric.closedBall 0 r := by
  intro x hx
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have hnative : e x ∈ nativeCodedBody K cuts := ⟨x, hx, rfl⟩
  have he := (chosenOuterFrame_coded_spec hK hcv cuts hi).2.2.1 hnative
  rw [← canonicalOuterFrame_image_ball K hr cuts] at he
  obtain ⟨y, hy, hxy⟩ := he
  have hxy' : y = x := e.injective hxy
  simpa only [hxy'] using hy



private theorem canonicalOuterFrame_inner_ball {d p : ℕ} (hd : 0 < d) {K : Set (Space d)}
    (hK : IsCompact K) (hcv : Convex ℝ K) {r : ℝ} (hr : 0 < r)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty) :
    frameApply (canonicalOuterFrame K r cuts) '' Metric.closedBall 0 (r / (d : ℝ)) ⊆
      codedBody K cuts := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hd
  have hrad : 0 < r / (d : ℝ) := div_pos hr hdreal
  have hfactor : (r / (d : ℝ)) * r⁻¹ = 1 / (d : ℝ) := by field_simp
  have himage := native_frame_image_ball (canonicalOuterFrame K r cuts) hrad
  simp only [canonicalOuterFrame, ContinuousLinearEquiv.apply_symm_apply, smul_smul,
    hfactor] at himage
  intro x hx
  let e := EuclideanSpace.equiv (Fin d) ℝ
  have he : e x ∈ ellipsoid ((1 / (d : ℝ)) •
      (chosenOuterFrame (nativeCodedBody K cuts)).1)
      (chosenOuterFrame (nativeCodedBody K cuts)).2 := by
    rw [← himage]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := (chosenOuterFrame_coded_spec hK hcv cuts hi).2.2.2 he
  have hyx' : y = x := e.injective hyx
  simpa only [hyx'] using hy

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

private theorem measurable_gaussian_normalize (d : ℕ) (R : ℝ) :
    Measurable (fun x : Space d => (R / ‖x‖) • x) := by fun_prop











end LG2021

end
end

/- Normalized Gaussian norm support -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
private theorem norm_gaussian_normalize_le {d : ℕ} {R : ℝ} (hR : 0 ≤ R) (x : Space d) :
    ‖(R/‖x‖) • x‖ ≤ R := by
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR (norm_nonneg x))]
  by_cases hx : ‖x‖ = 0
  · simp only [hx, div_zero, mul_zero]
    exact hR
  · rw [div_mul_cancel₀ R hx]

private theorem sphereMeasure_norm_gt_zero {d : ℕ} {R : ℝ} (hR : 0 ≤ R) :
    (sphereMeasure d R).real {z | R < ‖z‖} = 0 := by
  unfold sphereMeasure Measure.real
  rw [Measure.map_apply (measurable_gaussian_normalize d R)
    (measurableSet_lt measurable_const measurable_norm)]
  have heq : (fun x : Space d => (R/‖x‖) • x) ⁻¹' {z | R < ‖z‖} = ∅ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact norm_gaussian_normalize_le hR x
  rw [heq, measure_empty, ENNReal.toReal_zero]


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




end LG2021.Concentration

end
end

/- LG2021ConcentrationSeedCoordinates -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal





















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



































end LG2021.Concentration

end
end

/- LG2021ConcentrationKernelPrefix -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm































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

private theorem historyPrefix_measurePreserving {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) {T N : ℕ} (hTN : T ≤ N) :
    MeasurePreserving (historyPrefix (Ω := Ω) hTN)
      (historyMeasure A P ν hνm N) (historyMeasure A P ν hνm T) :=
  ⟨measurable_historyPrefix hTN, historyMeasure_map_prefix A P ν hνm hA L γ hν hTN⟩



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

private theorem canonicalOuterFrame_snoc_zero {d p : ℕ} (K : Set (Space d)) (r : ℝ)
    (cuts : Fin p → CutCode d) :
    canonicalOuterFrame K r (Fin.snoc cuts 0) = canonicalOuterFrame K r cuts := by
  unfold canonicalOuterFrame nativeCodedBody
  rw [codedBody_snoc_zero]

private theorem step_frame {d u p : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (st : State d u p) (hframe : st.2.1 = canonicalOuterFrame K cfg.radius st.1)
    (next : Fin u → Space d) (x : Space d) (y y' : ℝ) :
    (step cfg R (canonicalOuterFrame K cfg.radius) st next x y y').2.1 =
      canonicalOuterFrame K cfg.radius (step cfg R (canonicalOuterFrame K cfg.radius) st next x y y').1 := by
  cases h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') with
  | none =>
      simp only [step, h, continueState]
      rw [canonicalOuterFrame_snoc_zero]
      exact hframe
  | some s => simp only [step, h, restartState]

private theorem runState_frame {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (p : ℕ) (ys : Fin p → ℝ × ℝ) :
    (runState cfg K R seed p ys).2.1 =
      canonicalOuterFrame K cfg.radius (runState cfg K R seed p ys).1 := by
  induction p with
  | zero => rfl
  | succ p ih =>
      exact step_frame cfg K R _ (ih _) _ _ _ _















private theorem matrixAction_smul {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (a : ℝ) (x : Space d) : matrixAction M (a • x) = a • matrixAction M x := by
  simp [matrixAction, Matrix.mulVec_smul]

private theorem frame_lipschitz_of_inner_ball {d : ℕ} (F : Frame d) {K : Set (Space d)}
    {t D : ℝ} (ht : 0 < t)
    (hinner : frameApply F '' Metric.closedBall 0 t ⊆ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) :
    LipschitzWith (D / t).toNNReal (frameApply F) := by
  have hzero : frameApply F 0 ∈ K := hinner ⟨0, by simpa using ht.le, rfl⟩
  have hnorm (x : Space d) : ‖matrixAction F.1 x‖ ≤ (D / t) * ‖x‖ := by
    by_cases hx : x = 0
    · subst x
      simp [matrixAction]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let u := (t / ‖x‖) • x
    have hu : u ∈ Metric.closedBall (0 : Space d) t := by
      simp [u, Metric.mem_closedBall, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht, abs_of_pos (div_pos ht hxpos), hxpos.ne']
    have hd := hdiam (frameApply F u) (hinner ⟨u, hu, rfl⟩) (frameApply F 0) hzero
    have hdist : dist (frameApply F u) (frameApply F 0) = ‖matrixAction F.1 u‖ := by
      simp [frameApply, matrixAction, dist_eq_norm]
    rw [hdist, show u = (t / ‖x‖) • x from rfl, matrixAction_smul, norm_smul,
      Real.norm_eq_abs, abs_of_pos (div_pos ht hxpos)] at hd
    calc
      ‖matrixAction F.1 x‖ = (‖x‖ / t) * ((t / ‖x‖) * ‖matrixAction F.1 x‖) := by field_simp
      _ ≤ (‖x‖ / t) * D := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = (D / t) * ‖x‖ := by ring
  apply LipschitzWith.of_dist_le'
  intro x y
  have he : frameApply F x - frameApply F y = matrixAction F.1 (x - y) := by
    rw [matrixAction_sub]
    simp [frameApply]
  simpa only [dist_eq_norm, he] using hnorm (x - y)

private theorem canonicalOuterFrame_lipschitz {d p : ℕ} (hd : 0 < d)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {r D : ℝ} (hr : 0 < r) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty) :
    LipschitzWith ((d : ℝ) * D / r).toNNReal (frameApply (canonicalOuterFrame K r cuts)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hinner := canonicalOuterFrame_inner_ball hd hK hcv hr cuts hi
  have h := frame_lipschitz_of_inner_ball (canonicalOuterFrame K r cuts)
    (div_pos hr hdR) (hinner.trans (show codedBody K cuts ⊆ K from fun _ hx => hx.1)) hdiam
  have he : D / (r / (d : ℝ)) = (d : ℝ) * D / r := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simpa only [he] using h

private theorem canonical_loss_lipschitz {d p : ℕ} (hd : 0 < d)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {r D : ℝ} (hr : 0 < r) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty)
    (F : Space d → ℝ) (hF : LipschitzWith 1 F) :
    LipschitzWith ((d : ℝ) * D / r).toNNReal
      (fun x => F (frameApply (canonicalOuterFrame K r cuts) x)) := by
  simpa only [one_mul, Function.comp_def] using hF.comp (canonicalOuterFrame_lipschitz hd hK hcv hr hdiam cuts hi)

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









end LG2021.Algorithm

end
end

/- LG2021ConcentrationStageEstimators -/
section

noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm





















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











private theorem frame_loss_convex {d : ℕ} (F : Frame d) {f : Space d → ℝ}
    (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (fun x => f (frameApply F x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have he : frameApply F (a • x + b • y) = a • frameApply F x + b • frameApply F y := by
    simp only [frameApply, matrixAction_add, matrixAction_smul]
    calc
      _ = a • matrixAction F.1 x + b • matrixAction F.1 y + (a + b) • F.2 := by rw [hab, one_smul]
      _ = _ := by module
  change f (frameApply F (a • x + b • y)) ≤ _
  rw [he]
  exact hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab



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

private theorem candidateCount_lower (n : ℕ) :
    48 * Real.log (3 * (n : ℝ) ^ 2) ≤ (candidateCount n : ℝ) := Nat.le_ceil _

private theorem independent_candidate_failure_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : Set X) (hE : MeasurableSet E)
    (hprob : (1 / 48 : ℝ) ≤ μ.real E) (u : ℕ) :
    (Measure.pi (fun _ : Fin u => μ)).real {z | ∀ i, z i ∉ E} ≤
      Real.exp (-(u : ℝ) / 48) := by
  have heq : {z : Fin u → X | ∀ i, z i ∉ E} = Set.pi Set.univ (fun _ => Eᶜ) := by
    ext z
    simp
  rw [heq, Measure.real, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.toReal_pow]
  change (μ.real Eᶜ) ^ u ≤ Real.exp (-(u : ℝ) / 48)
  have hc : μ.real Eᶜ ≤ 47 / 48 := by
    rw [measureReal_compl hE]
    norm_num
    linarith
  have hexp : (47 / 48 : ℝ) ≤ Real.exp (-1 / 48) := by
    have h := Real.add_one_le_exp (-1 / 48 : ℝ)
    linarith
  calc
    _ ≤ (47 / 48 : ℝ) ^ u := pow_le_pow_left₀ (measureReal_nonneg) hc u
    _ ≤ Real.exp (-1 / 48) ^ u := pow_le_pow_left₀ (by norm_num) hexp u
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

private theorem candidate_failure_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (E : Set X) (hE : MeasurableSet E)
    (hprob : (1 / 48 : ℝ) ≤ μ.real E) {n : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin (candidateCount n) => μ)).real {z | ∀ i, z i ∉ E} ≤
      1 / (3 * (n : ℝ) ^ 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (independent_candidate_failure_le μ E hE hprob _).trans
  calc
    _ ≤ Real.exp (-Real.log (3 * (n : ℝ) ^ 2)) := by
      apply Real.exp_le_exp.2
      have h := candidateCount_lower n
      linarith
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div]

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

















private theorem gaussianMean_sub_value_le_gap {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {r : ℝ} {x : Space d} (hx : x ∈ Metric.closedBall 0 r) :
    gaussianMean f - f x ≤ gaussianGap r f := by
  have hb := ((isCompact_closedBall (0 : Space d) r).image hf.continuous).bddBelow
  exact sub_le_sub_left (csInf_le hb (mem_image_of_mem f hx)) _

namespace Algorithm



private theorem canonical_loss_comparator_gap_le {d p : ℕ} (hd : 0 < d)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {r D : ℝ} (hr : 0 < r) (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty)
    (L : Space d → ℝ) (hL : LipschitzWith 1 L)
    (xstar : Space d) (hxstar : xstar ∈ codedBody K cuts) :
    gaussianMean (fun x => L (frameApply (canonicalOuterFrame K r cuts) x)) - L xstar ≤
      gaussianGap r (fun x => L (frameApply (canonicalOuterFrame K r cuts) x)) := by
  obtain ⟨x, hx, he⟩ := codedBody_subset_canonicalOuterFrame hK hcv hr cuts hi hxstar
  have h := gaussianMean_sub_value_le_gap
    (canonical_loss_lipschitz hd hK hcv hr hdiam cuts hi L hL) hx
  simpa only [he] using h

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













private theorem insertCandidateSeed_measurePreserving {d u : ℕ} (cfg : OracleConfig)
    (i : Fin (cfg.horizon + 1)) :
    MeasurePreserving (insertCandidateSeed (d := d) (u := u) i)
      ((candidateRemainderMeasure d u cfg).prod (candidateBlockMeasure d u cfg))
      (seedMeasure d u cfg) := by
  let μC := Measure.pi (fun _ : Fin cfg.horizon => candidateBlockMeasure d u cfg)
  let μG := Measure.pi (fun _ : Fin (cfg.horizon + 1) => gaussian d)
  let μB := candidateBlockMeasure d u cfg
  have h1 := measurePreserving_prodAssoc μC μG μB
  have h2 := (MeasurePreserving.id μC).prod
    (Measure.measurePreserving_swap (μ := μG) (ν := μB))
  have h3 := (measurePreserving_prodAssoc μC μB μG).symm
  have h4 := (Measure.measurePreserving_swap (μ := μC) (ν := μB)).prod (MeasurePreserving.id μG)
  have h5 := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (cfg.horizon + 1) => candidateBlockMeasure d u cfg) i).symm.prod
      (MeasurePreserving.id μG)
  convert h5.comp (h4.comp (h3.comp (h2.comp h1))) using 1 <;> rfl

private theorem measurable_insertCandidateSeed {d u : ℕ} (cfg : OracleConfig)
    (i : Fin (cfg.horizon + 1)) : Measurable (insertCandidateSeed (d := d) (u := u) i) :=
  (insertCandidateSeed_measurePreserving cfg i).measurable

private theorem seedCandidates_insert_before {d u n : ℕ} (i : Fin (n + 1))
    (w : CandidateRemainder d u n) (x y : Fin u → Space d) (j : ℕ) (hj : j < i.val) :
    seedCandidates (insertCandidateSeed i (w, x)) j =
      seedCandidates (insertCandidateSeed i (w, y)) j := by
  have hjn : j < n + 1 := hj.trans i.isLt
  simp only [seedCandidates, dif_pos hjn, insertCandidateSeed]
  have hji : (⟨j, hjn⟩ : Fin (n + 1)) < i := hj
  rw [Fin.insertNth_apply_below hji, Fin.insertNth_apply_below hji]

private theorem policy_insertCandidateSeed_before {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (i : Fin (cfg.horizon + 1)) (τ : ℕ) (hτ : τ < 2 * i.val)
    (w : CandidateRemainder d u cfg.horizon) (x y : Fin u → Space d) (ys : Fin τ → ℝ) :
    (policy (u := u) cfg K hK R anchor).query τ (insertCandidateSeed i (w, x)) ys =
      (policy (u := u) cfg K hK R anchor).query τ (insertCandidateSeed i (w, y)) ys := by
  apply policy_seed_prefix cfg K hK R anchor τ _ _ ys
  · intro j hj
    exact seedCandidates_insert_before i w x y j (by omega)
  · intro j hj
    rfl

/-- Fresh stage candidates are independent of the preceding adaptive observation history. -/
private theorem candidate_coordinate_history_factorization {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (i : Fin (cfg.horizon + 1)) (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν)
    (F : Seed d u cfg.horizon × (Fin (2 * i.val) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F w ∂historyMeasure (policy (u := u) cfg K hK R anchor)
      (seedMeasure d u cfg) ν hνm (2 * i.val)) =
    ∫⁻ w, ∫⁻ x, F (insertCandidateSeed i (w.1, x), w.2) ∂candidateBlockMeasure d u cfg
      ∂historyMeasure (freezeCoordinatePolicy (policy (u := u) cfg K hK R anchor)
        (insertCandidateSeed i) (measurable_insertCandidateSeed cfg i) 0)
        (candidateRemainderMeasure d u cfg) ν hνm (2 * i.val) := by
  apply lintegral_history_independent_coordinate
    (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg)
    (candidateRemainderMeasure d u cfg) (candidateBlockMeasure d u cfg) (insertCandidateSeed i)
    (insertCandidateSeed_measurePreserving cfg i) 0 ν hνm (policy_isOn cfg K hK R ha)
    L γ hν (2 * i.val) _ F hF
  intro τ hτ w x ys
  exact policy_insertCandidateSeed_before cfg K hK R anchor i τ hτ w x 0 ys

/-- Drawing a candidate block does not change the newly computed geometric frame. -/
private theorem step_frame_independent_candidates {d u p : ℕ} (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d) (st : State d u p)
    (c c' : Fin u → Space d) (x : Space d) (y y' : ℝ) :
    (step cfg R rounding st c x y y').2.1 = (step cfg R rounding st c' x y y').2.1 := by
  cases h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') <;>
    simp only [step, h] <;> rfl

/-- At a stage restart the geometry is determined before the new candidate block is exposed. -/
private theorem runState_frame_insertCandidateSeed {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (i : Fin (cfg.horizon + 1))
    (w : CandidateRemainder d u cfg.horizon) (x y : Fin u → Space d)
    (ys : Fin i.val → ℝ × ℝ) :
    (runState cfg K R (insertCandidateSeed i (w, x)) i.val ys).2.1 =
      (runState cfg K R (insertCandidateSeed i (w, y)) i.val ys).2.1 := by
  rcases i with ⟨p, hp⟩
  cases p with
  | zero => rfl
  | succ p =>
      have hstate := runState_seed_prefix cfg K R
        (insertCandidateSeed ⟨p + 1, hp⟩ (w, x)) (insertCandidateSeed ⟨p + 1, hp⟩ (w, y))
        p (fun j => ys j.castSucc)
        (fun j hj => seedCandidates_insert_before (⟨p + 1, hp⟩ : Fin (cfg.horizon + 1))
          w x y j (show j < p + 1 by omega)) (fun j hj => rfl)
      simp only [runState]
      rw [hstate]
      exact step_frame_independent_candidates cfg R _ _ _ _ _ _ _


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



private theorem separationFactor_ge_one {d : ℕ} (hd : 0 < d) : 1 ≤ separationFactor d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 1 ≤ Real.sqrt (d : ℝ) := Real.one_le_sqrt.2 hdR
  unfold separationFactor
  nlinarith [mul_le_mul hdR hs (by norm_num) (Nat.cast_nonneg d)]









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

private theorem canonical_candidate_probability {d n p : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (cuts : Fin p → CutCode d) (hi : (interior (codedBody K cuts)).Nonempty)
    (L : Space d → ℝ) (hL : LipschitzWith 1 L) (hLc : ConvexOn ℝ univ L)
    (xstar : Space d) (hx : xstar ∈ codedBody K cuts) :
    (1/48 : ℝ) ≤
      (sphereMeasure d ((oracleConfig d D n).radius/(2*(d : ℝ)))).real {z |
        (frameGap L xstar (canonicalOuterFrame K (oracleConfig d D n).radius cuts)-1/(n : ℝ))/
          separationFactor d ≤
        frameCandidateGap (oracleConfig d D n).lambda L
          (canonicalOuterFrame K (oracleConfig d D n).radius cuts) z} := by
  let r := (oracleConfig d D n).radius
  have hr : 0 < r := by have h := (oracleConfig_bounds hd hn hD).1; dsimp [r]; linarith
  have hLip := canonical_loss_lipschitz hd hK hcv hr hdiam cuts hi L hL
  have hconv := frame_loss_convex (canonicalOuterFrame K r cuts) hLc
  have hlim : (((d : ℝ)*D/r).toNNReal : ℝ) ≤ paperLipschitz d D (parameterLog d D n) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    rfl
  have hsep := paper_strong_separation hd (by omega : 0 < n) hD hlim hLip hconv
  have hcomp := canonical_loss_comparator_gap_le hd hK hcv hr hdiam cuts hi L hL xstar hx
  have hk : 0 < separationFactor d := lt_of_lt_of_le zero_lt_one (separationFactor_ge_one hd)
  apply (by norm_num : (1/48 : ℝ) ≤ 1/24).trans
  apply hsep.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz
  exact (div_le_div_of_nonneg_right (sub_le_sub_right hcomp _) hk.le).trans hz

private theorem step_cuts_age_independent_candidates {d u p : ℕ} (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p+1) → CutCode d) → Frame d) (st : State d u p)
    (c c' : Fin u → Space d) (x : Space d) (y y' : ℝ) :
    (step cfg R rounding st c x y y').1 = (step cfg R rounding st c' x y y').1 ∧
      (step cfg R rounding st c x y y').2.2.2.1 = (step cfg R rounding st c' x y y').2.2.2.1 := by
  cases h : winner cfg (st.2.2.2.1+1) (updatedScalars cfg st x y y') <;>
    simp [step, h, continueState, restartState]

private theorem runState_cuts_age_insertCandidateSeed {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (i : Fin (cfg.horizon+1))
    (w : CandidateRemainder d u cfg.horizon) (x y : Fin u → Space d)
    (ys : Fin i.val → ℝ × ℝ) :
    (runState cfg K R (insertCandidateSeed i (w,x)) i.val ys).1 =
      (runState cfg K R (insertCandidateSeed i (w,y)) i.val ys).1 ∧
    (runState cfg K R (insertCandidateSeed i (w,x)) i.val ys).2.2.2.1 =
      (runState cfg K R (insertCandidateSeed i (w,y)) i.val ys).2.2.2.1 := by
  rcases i with ⟨p,hp⟩
  cases p with
  | zero => exact ⟨rfl,rfl⟩
  | succ p =>
      have hstate := runState_seed_prefix cfg K R
        (insertCandidateSeed ⟨p+1,hp⟩ (w,x)) (insertCandidateSeed ⟨p+1,hp⟩ (w,y)) p
        (fun j => ys j.castSucc)
        (fun j hj => seedCandidates_insert_before (⟨p+1,hp⟩ : Fin (cfg.horizon+1)) w x y j (show j < p+1 by omega))
        (fun j hj => rfl)
      simp only [runState]
      rw [hstate]
      exact step_cuts_age_independent_candidates cfg R _ _ _ _ _ _ _

private theorem traceState_candidates_at_start {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ)
    (hage : (traceState cfg K R seed ys p).2.2.2.1 = 0) :
    (traceState cfg K R seed ys p).2.2.1 = seedCandidates seed p := by
  cases p with
  | zero => rfl
  | succ p =>
      cases hw : traceWinner cfg K R seed ys p with
      | none =>
          rw [traceState_succ, step_continues cfg R _ _ _ _ _ _ hw] at hage
          change (traceState cfg K R seed ys p).2.2.2.1 + 1 = 0 at hage
          omega
      | some s => rw [traceState_succ, step_restarts cfg R _ _ _ _ _ _ s hw]; rfl

private theorem seedCandidates_insert_at {d u n : ℕ} (i : Fin (n+1))
    (w : CandidateRemainder d u n) (x : Fin u → Space d) :
    seedCandidates (insertCandidateSeed i (w,x)) i.val = x := by
  simp only [seedCandidates, dif_pos i.isLt, insertCandidateSeed, Fin.insertNth_apply_same]

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

private theorem candidateStartValid_insert {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (xstar : Space d) (i : Fin (cfg.horizon+1))
    (w : CandidateRemainder d u cfg.horizon) (x y : Fin u → Space d)
    (ys : Fin (2*i.val) → ℝ) :
    candidateStartValid cfg K R xstar i.val (insertCandidateSeed i (w,x),ys) ↔
      candidateStartValid cfg K R xstar i.val (insertCandidateSeed i (w,y),ys) := by
  have h := runState_cuts_age_insertCandidateSeed cfg K R i w x y (fun j => terminalPairs ys j)
  dsimp only [candidateStartValid, traceState]
  rw [h.1, h.2]

private theorem candidateStartFailure_insert_subset {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (L : Space d → ℝ) (xstar : Space d)
    (i : Fin (cfg.horizon+1)) (w : CandidateRemainder d u cfg.horizon)
    (ys : Fin (2*i.val) → ℝ) :
    {x : Fin u → Space d | (insertCandidateSeed i (w,x),ys) ∈
      candidateStartFailure cfg K R L xstar i.val} ⊆
    {x | ∀ s, x s ∉ {z |
      (frameGap L xstar (traceState cfg K R (insertCandidateSeed i (w,0)) (terminalPairs ys) i.val).2.1 -
        1/(cfg.horizon : ℝ))/separationFactor d ≤ frameCandidateGap cfg.lambda L
          (traceState cfg K R (insertCandidateSeed i (w,0)) (terminalPairs ys) i.val).2.1 z}} := by
  intro x hx s hs
  have hage := hx.1.1
  have hcand := traceState_candidates_at_start cfg K R (insertCandidateSeed i (w,x)) (terminalPairs ys) i.val hage
  rw [seedCandidates_insert_at] at hcand
  have hframe := runState_frame_insertCandidateSeed cfg K R i w x 0 (fun j => terminalPairs ys j)
  change (traceState cfg K R (insertCandidateSeed i (w,x)) (terminalPairs ys) i.val).2.1 = _ at hframe
  apply hx.2
  refine ⟨s, ?_⟩
  change (_ - _)/_ ≤ frameCandidateGap cfg.lambda L _ _
  change (frameGap L xstar _ - _)/_ ≤ _
  rw [hframe, hcand]
  exact hs

private theorem candidateStartFailure_fiber_le {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ)
    (L : Space d → ℝ) (hL : LipschitzWith 1 L) (hLc : ConvexOn ℝ univ L) (xstar : Space d)
    (i : Fin (n+1)) (w : CandidateRemainder d (candidateCount n) n) (ys : Fin (2*i.val) → ℝ) :
    candidateBlockMeasure d (candidateCount n) (oracleConfig d D n)
      {x | (insertCandidateSeed i (w,x),ys) ∈
        candidateStartFailure (oracleConfig d D n) K R L xstar i.val} ≤
          ENNReal.ofReal (1/(3*(n : ℝ)^2)) := by
  let cfg := oracleConfig d D n
  let seed0 := insertCandidateSeed i (w,0)
  let st := traceState cfg K R seed0 (terminalPairs ys) i.val
  let E : Set (Space d) := {z | (frameGap L xstar st.2.1 - 1/(n : ℝ))/separationFactor d ≤
    frameCandidateGap cfg.lambda L st.2.1 z}
  by_cases hvalid : candidateStartValid cfg K R xstar i.val (seed0,ys)
  · have hmE : Measurable (fun z : Space d => frameCandidateGap cfg.lambda L st.2.1 z) := by
      simpa only [Function.comp_def] using (measurable_frameCandidateGap cfg.lambda hL.continuous).comp
        (show Measurable (fun z : Space d => (st.2.1,z)) from measurable_const.prodMk measurable_id)
    have hE : MeasurableSet E := measurableSet_le measurable_const hmE
    have hframe := runState_frame cfg K R seed0 i.val (fun j => terminalPairs ys j)
    change st.2.1 = canonicalOuterFrame K cfg.radius st.1 at hframe
    have hprob : (1/48 : ℝ) ≤ (sphereMeasure d (cfg.radius/(2*(d : ℝ)))).real E := by
      dsimp only [E]
      rw [hframe]
      exact canonical_candidate_probability hd hn hK hcv hD hdiam st.1 hvalid.2.1 L hL hLc xstar hvalid.2.2
    have hfailure := candidate_failure_le (sphereMeasure d (cfg.radius/(2*(d : ℝ)))) E hE hprob (by omega : 0 < n)
    have hsub := candidateStartFailure_insert_subset cfg K R L xstar i w ys
    have hreal := (measureReal_mono hsub (measure_ne_top _ _)).trans hfailure
    have h := ENNReal.ofReal_le_ofReal hreal
    rw [ofReal_measureReal] at h
    exact h
  · have hempty : {x : Fin (candidateCount n) → Space d | (insertCandidateSeed i (w,x),ys) ∈
        candidateStartFailure cfg K R L xstar i.val} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro hx
      exact hvalid ((candidateStartValid_insert cfg K R xstar i w x 0 ys).mp hx.1)
    rw [hempty, measure_empty]
    exact bot_le

private theorem candidateStartFailure_probability_le {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ)
    (anchor : Space d) (ha : anchor ∈ K)
    (L : Space d → ℝ) (hL : LipschitzWith 1 L) (hLc : ConvexOn ℝ univ L) (xstar : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (γ : ℝ) (hν : NoiseCond K L γ ν)
    (i : Fin (n+1)) :
    (historyMeasure (policy (u := candidateCount n) (oracleConfig d D n) K hK.isClosed.measurableSet R anchor)
      (seedMeasure d (candidateCount n) (oracleConfig d D n)) ν hνm (2*i.val)).real
      (candidateStartFailure (oracleConfig d D n) K R L xstar i.val) ≤ 1/(3*(n : ℝ)^2) := by
  let cfg := oracleConfig d D n
  let A := policy (u := candidateCount n) cfg K hK.isClosed.measurableSet R anchor
  let B := candidateStartFailure (u := candidateCount n) (T := 2*i.val) cfg K R L xstar i.val
  have hB : MeasurableSet B := measurableSet_candidateStartFailure cfg K R hL.continuous xstar i.val
  let A0 := freezeCoordinatePolicy A (insertCandidateSeed i) (measurable_insertCandidateSeed cfg i) 0
  have hA0 : A0.IsOn K := fun τ w ys => policy_isOn cfg K hK.isClosed.measurableSet R ha τ _ ys
  letI := historyMeasure_probability A0 (candidateRemainderMeasure d (candidateCount n) cfg)
    ν hνm hA0 L γ hν (2*i.val)
  have hfac := candidate_coordinate_history_factorization cfg K hK.isClosed.measurableSet R anchor ha i ν hνm L γ hν
    (B.indicator 1) (measurable_const.indicator hB)
  have hbound : historyMeasure A (seedMeasure d (candidateCount n) cfg) ν hνm (2*i.val) B ≤
      ENNReal.ofReal (1/(3*(n : ℝ)^2)) := by
    rw [← lintegral_indicator_one hB, hfac]
    calc
      _ ≤ ∫⁻ _w, ENNReal.ofReal (1/(3*(n : ℝ)^2))
          ∂historyMeasure A0 (candidateRemainderMeasure d (candidateCount n) cfg) ν hνm (2*i.val) := by
        apply lintegral_mono
        intro w
        have hf : Measurable (fun x => (insertCandidateSeed i (w.1,x),w.2)) :=
          ((measurable_insertCandidateSeed cfg i).comp (measurable_const.prodMk measurable_id)).prodMk measurable_const
        change (∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) (insertCandidateSeed i (w.1,x),w.2)
          ∂candidateBlockMeasure d (candidateCount n) cfg) ≤ _
        have he := lintegral_indicator_const_comp (μ := candidateBlockMeasure d (candidateCount n) cfg) hf hB 1
        have hb := candidateStartFailure_fiber_le hd hn hK hcv hD hdiam R L hL hLc xstar i w.1 w.2
        exact he.trans_le (by simpa only [one_mul, B, cfg, Set.preimage] using hb)
      _ = _ := by simp
  have h := ENNReal.toReal_mono (by finiteness) hbound
  simpa only [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(3*(n : ℝ)^2))] using h

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

private theorem ae_candidateSeedGood {d u : ℕ} (cfg : OracleConfig) (hr : 0 ≤ cfg.radius) :
    ∀ᵐ seed ∂seedMeasure d u cfg, candidateSeedGood cfg seed := by
  let r := cfg.radius/(2*(d : ℝ))
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hs : ∀ᵐ z ∂sphereMeasure d r, ‖z‖ ≤ r := by
    rw [ae_iff]
    simpa only [not_le] using (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
      (sphereMeasure_norm_gt_zero (d := d) hr0)
  have hblock : ∀ᵐ z ∂candidateBlockMeasure d u cfg, ∀ s, ‖z s‖ ≤ r := by
    apply ae_all_iff.mpr
    intro s
    exact (measurePreserving_eval (fun _ : Fin u => sphereMeasure d r) s).quasiMeasurePreserving.ae hs
  have hblocks : ∀ᵐ z ∂Measure.pi (fun _ : Fin (cfg.horizon+1) => candidateBlockMeasure d u cfg),
      ∀ p s, ‖z p s‖ ≤ r := by
    apply ae_all_iff.mpr
    intro p
    exact (measurePreserving_eval (fun _ : Fin (cfg.horizon+1) => candidateBlockMeasure d u cfg) p).quasiMeasurePreserving.ae hblock
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin (cfg.horizon+1) => gaussian d)) :=
    Measure.pi.instIsProbabilityMeasure _
  exact (measurePreserving_fst (μ := Measure.pi (fun _ : Fin (cfg.horizon+1) => candidateBlockMeasure d u cfg))
    (ν := Measure.pi (fun _ : Fin (cfg.horizon+1) => gaussian d))).quasiMeasurePreserving.ae hblocks



private theorem ae_history_candidateSeedGood {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (hr : 0 ≤ cfg.radius) (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ) :
    ∀ᵐ w ∂historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm T,
      candidateSeedGood cfg w.1 := by
  let A := policy (u := u) cfg K hK R anchor
  let P := seedMeasure d u cfg
  have hs0 : ∀ᵐ w ∂historyMeasure A P ν hνm 0, candidateSeedGood cfg w.1 := by
    unfold historyMeasure
    apply (ae_map_iff (by fun_prop)
      ((measurableSet_candidateSeedGood cfg).preimage measurable_fst)).mpr
    exact ae_candidateSeedGood cfg hr
  exact (historyPrefix_measurePreserving A P ν hνm (policy_isOn cfg K hK R ha)
    L γ hν (Nat.zero_le T)).quasiMeasurePreserving.ae hs0

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

private theorem candidateStartFailure_prefix {d u T Q : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (L : Space d → ℝ) (xstar : Space d)
    (hTQ : T ≤ Q) {p : ℕ} (hp : p ≤ T/2)
    (w : Seed d u cfg.horizon × (Fin Q → ℝ)) :
    historyPrefix hTQ w ∈ candidateStartFailure cfg K R L xstar p ↔
      w ∈ candidateStartFailure cfg K R L xstar p := by
  let F : State d u p → Prop := fun st =>
    (st.2.2.2.1 = 0 ∧ (interior (codedBody K st.1)).Nonempty ∧ xstar ∈ codedBody K st.1) ∧
      ¬∃ s : Fin u, (frameGap L xstar st.2.1 - 1/(cfg.horizon : ℝ))/separationFactor d ≤
        frameCandidateGap cfg.lambda L st.2.1 (st.2.2.1 s)
  change F (traceState cfg K R w.1 (terminalPairs (observationPrefix w.2 T hTQ)) p) ↔
    F (traceState cfg K R w.1 (terminalPairs w.2) p)
  rw [terminalTrace_prefix_eq cfg K R w.1 w.2 T hTQ hp]



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



private theorem candidateTerminalGood_failure_le {d n N : ℕ} (hd : 0 < d) (hn : 2 ≤ n) (hN : N ≤ n)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (L : Space d → ℝ) (hL : LipschitzWith 1 L) (hLc : ConvexOn ℝ univ L) (xstar : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (γ : ℝ) (hν : NoiseCond K L γ ν) :
    (historyMeasure (policy (u := candidateCount n) (oracleConfig d D n) K hK.isClosed.measurableSet R anchor)
      (seedMeasure d (candidateCount n) (oracleConfig d D n)) ν hνm (2*N)).real
        (candidateTerminalGood (oracleConfig d D n) K R L xstar)ᶜ ≤
          ((N : ℝ)+1)/(3*(n : ℝ)^2) := by
  let cfg := oracleConfig d D n
  let A := policy (u := candidateCount n) cfg K hK.isClosed.measurableSet R anchor
  let P := seedMeasure d (candidateCount n) cfg
  have hA := policy_isOn (u := candidateCount n) cfg K hK.isClosed.measurableSet R ha
  letI := historyMeasure_probability A P ν hνm hA L γ hν (2*N)
  rw [candidateTerminalGood_compl]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _p : Fin (N+1), 1/(3*(n : ℝ)^2) := by
      apply Finset.sum_le_sum
      intro p hp
      have htime : 2*p.val ≤ 2*N := by omega
      have he : candidateStartFailure (u := candidateCount n) (T := 2*N) cfg K R L xstar p.val =
          (historyPrefix htime) ⁻¹' candidateStartFailure (u := candidateCount n) (T := 2*p.val) cfg K R L xstar p.val := by
        ext w
        exact (candidateStartFailure_prefix cfg K R L xstar htime (by omega : p.val ≤ 2*p.val/2) w).symm
      change (historyMeasure A P ν hνm (2*N)).real (candidateStartFailure cfg K R L xstar p.val) ≤ _
      rw [he, historyMeasure_prefix_probability A P ν hνm hA L γ hν htime _
        (measurableSet_candidateStartFailure cfg K R hL.continuous xstar p.val)]
      exact candidateStartFailure_probability_le hd hn hK hcv hD hdiam R anchor ha L hL hLc xstar
        ν hνm γ hν ⟨p.val, by omega⟩
    _ = _ := by simp; ring











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

theorem solution {d n N : ℕ} (hd : 0 < d) (hn : 2 ≤ n) (hN : N ≤ n)
    {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (L : Space d → ℝ) (hL : LipschitzWith 1 L) (hLc : ConvexOn ℝ univ L) (xstar : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (γ : ℝ) (hν : NoiseCond K L γ ν) :
    (historyMeasure (policy (u := candidateCount n) (oracleConfig d D n) K hK.isClosed.measurableSet R anchor)
      (seedMeasure d (candidateCount n) (oracleConfig d D n)) ν hνm (2*N)).real
        (candidateTerminalEvent (oracleConfig d D n) K R L xstar)ᶜ ≤
          ((N : ℝ)+1)/(3*(n : ℝ)^2) := by
  let cfg := oracleConfig d D n
  let A := policy (u := candidateCount n) cfg K hK.isClosed.measurableSet R anchor
  let P := historyMeasure A (seedMeasure d (candidateCount n) cfg) ν hνm (2*N)
  letI : IsProbabilityMeasure P := historyMeasure_probability A _ ν hνm
    (policy_isOn cfg K hK.isClosed.measurableSet R ha) L γ hν _
  have hs := ae_history_candidateSeedGood (u := candidateCount n) cfg K hK.isClosed.measurableSet R anchor ha
    (by have h := (oracleConfig_bounds hd hn hD).1; dsimp [cfg]; linarith) ν hνm L γ hν (2*N)
  have hzero : P.real {w | ¬candidateSeedGood cfg w.1} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (ae_iff.mp hs)
  have hb := candidateTerminalGood_failure_le hd hn hN hK hcv hD hdiam R anchor ha L hL hLc xstar ν hνm γ hν
  change P.real (candidateTerminalEvent cfg K R L xstar)ᶜ ≤ _
  rw [candidateTerminalEvent, compl_inter]
  have hz : P.real {w | candidateSeedGood cfg w.1}ᶜ = 0 := hzero
  exact (measureReal_union_le _ _).trans (by rw [hz, add_zero]; exact hb)
