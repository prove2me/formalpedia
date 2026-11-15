-- Prove2me | solution 1 for LG2021.Concentration.terminal_trace_regret_good_event
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T16:54:42.675482+00:00
-- url     : https://prove2.me/submissions/a713846e-14d7-4b1e-9e69-898c3742d42a

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























































end LG2021.Algorithm

end
end

/- LG2021AlgorithmGeometry -/
section

noncomputable section

namespace LG2021.Algorithm

open MeasureTheory Matrix
open scoped Classical






























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





private theorem gaussian_map_neg (d : ℕ) :
    (gaussian d).map (fun x => -x) = gaussian d := by
  simpa only [gaussian, LinearIsometryEquiv.coe_neg] using
    (stdGaussian_map (LinearIsometryEquiv.neg ℝ : Space d ≃ₗᵢ[ℝ] Space d))







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









private theorem measurable_seedGaussian {d u n : ℕ} (p : ℕ) :
    Measurable (fun seed : Seed d u n => seedGaussian seed p) := by
  unfold seedGaussian
  split_ifs <;> fun_prop



















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

private theorem integrable_lipschitz_gaussian_affine {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (a : ℝ) (z : Space d) :
    Integrable (fun x => f (a • x + z)) (gaussian d) := by
  have hx : Integrable (fun x : Space d => x) (gaussian d) := by
    unfold gaussian
    exact IsGaussian.integrable_fun_id
  have hmajor : Integrable (fun x : Space d => ‖f 0‖ +
      (K : ℝ) * (|a| * ‖x‖ + ‖z‖)) (gaussian d) :=
    (integrable_const _).add (((hx.norm.const_mul |a|).add (integrable_const _)).const_mul _)
  apply hmajor.mono' (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  filter_upwards with x
  calc
    ‖f (a • x + z)‖ ≤ ‖f 0‖ + ‖f 0 - f (a • x + z)‖ := norm_le_insert _ _
    _ ≤ ‖f 0‖ + (K : ℝ) * ‖a • x + z‖ := by
      gcongr
      simpa only [zero_sub, norm_neg] using hf.norm_sub_le 0 (a • x + z)
    _ ≤ ‖f 0‖ + (K : ℝ) * (|a| * ‖x‖ + ‖z‖) := by
      gcongr
      simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le (a • x) z

private theorem integrable_lipschitz_gaussian {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) : Integrable f (gaussian d) := by
  simpa using integrable_lipschitz_gaussian_affine hf 1 0

private theorem gaussianMean_ge_value_zero {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ Set.univ f) : f 0 ≤ gaussianMean f := by
  have hx : Integrable (fun x : Space d => x) (gaussian d) := by
    unfold gaussian
    exact IsGaussian.integrable_fun_id
  have h := hc.map_integral_le hf.continuous.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hx (integrable_lipschitz_gaussian hf)
  simpa [gaussianMean, gaussian] using h







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








private theorem pastQueries_snoc {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ω : Ω) {τ : ℕ} (ys : Fin τ → ℝ) (y : ℝ) :
    A.pastQueries ω (Fin.snoc ys y) = Fin.snoc (A.pastQueries ω ys) (A.query τ ω ys) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, QueryAlg.pastQueries]
    congr 1
    funext k
    change Fin.snoc (α := fun _ => ℝ) ys y k.castSucc = ys k
    simp only [Fin.snoc_castSucc]
  · simp only [Fin.snoc_castSucc, QueryAlg.pastQueries]
    congr 1
    funext k
    change Fin.snoc (α := fun _ => ℝ) ys y (Fin.castLE j.isLt.le k).castSucc = ys (Fin.castLE j.isLt.le k)
    simp only [Fin.snoc_castSucc]










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

private theorem coordinatePairKernel_isMarkov {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B) [IsProbabilityMeasure Q]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ) :
    IsMarkovKernel (coordinatePairKernel A Q ν hνm encode he T) := by
  letI := coordinateFirstPairKernel_isMarkov A Q ν hνm encode he hA L γ hν T
  letI := secondObservationKernel_isMarkov A ν hνm encode he hA L γ hν T
  unfold coordinatePairKernel
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

private theorem coordinatePairKernel_apply {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B) [IsProbabilityMeasure Q]
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν)
    {T : ℕ} (w : W × (Fin T → ℝ)) :
    coordinatePairKernel A Q ν hνm encode he T w = coordinatePairMeasure A Q ν hνm encode he w := by
  letI := coordinateFirstPairKernel_isMarkov A Q ν hνm encode he hA L γ hν T
  letI := secondObservationKernel_isMarkov A ν hνm encode he hA L γ hν T
  rw [coordinatePairKernel, Kernel.compProd_apply_eq_compProd_sectR,
    coordinateFirstPairKernel_apply A Q ν hνm encode he hA L γ hν w]
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

/-- At the second query of a pair the first observation of that pair is not yet used by the state. -/
private theorem pairedHistory_snoc_ignores_last (p : ℕ) (ys : Fin (2 * p) → ℝ) (y y' : ℝ) :
    pairedHistory (Fin.snoc ys y) = pairedHistory (Fin.snoc ys y') := by
  funext i
  have hi : i.val < p := by have := i.isLt; omega
  have h1 : 2 * i.val < 2 * p := by omega
  have h2 : 2 * i.val + 1 < 2 * p := by omega
  simp only [pairedHistory, Fin.snoc, Fin.val_mk, dif_pos h1, dif_pos h2]

/-- The center query depends only on the history preceding the pair, even after legal fallback. -/
private theorem policy_center_query_fixed {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (i : Fin (cfg.horizon + 1))
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) (x : Space d) (y : ℝ) :
    (policy (u := u) cfg K hK R anchor).query (2 * i.val + 1)
      (insertGaussianSeed i (w.1, x)) (Fin.snoc w.2 y) =
    (policy (u := u) cfg K hK R anchor).query (2 * i.val + 1)
      (insertGaussianSeed i (w.1, 0)) (Fin.snoc w.2 0) := by
  have hstate := runState_seed_prefix cfg K R
    (insertGaussianSeed i (w.1, x)) (insertGaussianSeed i (w.1, 0))
    ((2 * i.val + 1) / 2) (pairedHistory (Fin.snoc w.2 0))
    (fun j hj => rfl) (fun j hj => seedGaussian_insert_before i w.1 x 0 j (by omega))
  have hproposal : proposedQuery cfg K R (2 * i.val + 1)
      (insertGaussianSeed i (w.1, x)) (Fin.snoc w.2 y) =
      proposedQuery cfg K R (2 * i.val + 1)
        (insertGaussianSeed i (w.1, 0)) (Fin.snoc w.2 0) := by
    unfold proposedQuery
    rw [pairedHistory_snoc_ignores_last i.val w.2 y 0, hstate]
    simp only [show (2 * i.val + 1) % 2 = 1 by omega, one_ne_zero, false_and, ↓reduceIte]
  change (if proposedQuery cfg K R (2 * i.val + 1) (insertGaussianSeed i (w.1, x))
      (Fin.snoc w.2 y) ∈ K then _ else anchor) = _
  rw [hproposal]
  rfl











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

private theorem seedGaussian_insert_remove_prefix_le {d u n : ℕ} (i : Fin (n + 1))
    (s : Seed d u n) (j : ℕ) (hj : j ≤ i.val) :
    seedGaussian (insertGaussianSeed i (removeGaussianSeed i (prefixSeed i.val s),
      seedGaussian s i.val)) j = seedGaussian s j := by
  by_cases he : j = i.val
  · subst j
    exact seedGaussian_insert_current i _ _
  · rw [seedGaussian_insert_remove_ne i _ _ j he,
      seedGaussian_prefixSeed_before i.val j s (by omega)]

private theorem policy_query_insert_remove_prefix {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (i : Fin (cfg.horizon + 1)) (s : Seed d u cfg.horizon)
    (τ : ℕ) (hτ : τ ≤ 2 * i.val + 1) (ys : Fin τ → ℝ) :
    (policy (u := u) cfg K hK R anchor).query τ
      (insertGaussianSeed i (removeGaussianSeed i (prefixSeed i.val s), seedGaussian s i.val)) ys =
      (policy (u := u) cfg K hK R anchor).query τ s ys := by
  apply policy_seed_prefix
  · intro j hj
    rfl
  · intro j hj
    exact seedGaussian_insert_remove_prefix_le i s j (by omega)

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

private theorem historyPrefix_self {Ω : Type} {T : ℕ} (w : Ω × (Fin T → ℝ)) :
    historyPrefix le_rfl w = w := by
  rfl

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







private theorem guarded_query_mem {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (R : ℝ) (seed : Seed d u cfg.horizon) (τ : ℕ) (ys : Fin τ → ℝ)
    (hbody : (interior (codedBody K (runState cfg K R seed (τ / 2) (pairedHistory ys)).1)).Nonempty) :
    proposedQuery cfg K R τ seed ys ∈ K := by
  let st := runState cfg K R seed (τ / 2) (pairedHistory ys)
  have hframe := runState_frame cfg K R seed (τ / 2) (pairedHistory ys)
  have hinner := canonicalOuterFrame_inner_ball hd hK hcv hr st.1 hbody
  have hlegal : ∀ z : Space d, ‖z‖ ≤ cfg.radius / (d : ℝ) → frameApply st.2.1 z ∈ K := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : Space d) (cfg.radius / (d : ℝ)) := by
      simpa using hz
    have h := hinner ⟨z, hz', rfl⟩
    rw [← hframe] at h
    exact h.1
  dsimp only [proposedQuery]
  split_ifs with h
  · exact hlegal _ h.2
  · apply hlegal 0
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    rw [norm_zero]
    exact (div_pos hr hdR).le

private theorem policy_query_eq_proposed {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (R : ℝ) (anchor : Space d) (seed : Seed d u cfg.horizon) (τ : ℕ) (ys : Fin τ → ℝ)
    (hbody : (interior (codedBody K (runState cfg K R seed (τ / 2) (pairedHistory ys)).1)).Nonempty) :
    (policy cfg K hK.isClosed.measurableSet R anchor).query τ seed ys =
      proposedQuery cfg K R τ seed ys := by
  exact if_pos (guarded_query_mem hd cfg hr hK hcv R seed τ ys hbody)



private theorem policy_query_off_guard {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (R : ℝ) (anchor : Space d) (seed : Seed d u cfg.horizon) (τ : ℕ) (ys : Fin τ → ℝ)
    (hbody : (interior (codedBody K (runState cfg K R seed (τ / 2) (pairedHistory ys)).1)).Nonempty)
    (hguard : ¬(τ % 2 = 0 ∧ ‖seedGaussian seed (τ / 2)‖ ≤ cfg.radius / (d : ℝ))) :
    (policy cfg K hK.isClosed.measurableSet R anchor).query τ seed ys =
      frameApply (runState cfg K R seed (τ / 2) (pairedHistory ys)).2.1 0 := by
  rw [policy_query_eq_proposed hd cfg hr hK hcv R anchor seed τ ys hbody]
  exact if_neg hguard

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





private theorem terminalPairs_eq_pairedHistory {n : ℕ} (ys : Fin n → ℝ) (i : Fin (n / 2)) :
    terminalPairs ys i = pairedHistory ys i := by
  have hi := i.isLt
  have hp : 2 * i.val + 1 < n := by omega
  simp only [terminalPairs, dif_pos hp, pairedHistory]

private theorem terminalPairs_observationPrefix {n : ℕ} (ys : Fin n → ℝ)
    (τ : ℕ) (hτ : τ ≤ n) (p : ℕ) (hp : p < τ / 2) :
    terminalPairs (observationPrefix ys τ hτ) p = terminalPairs ys p := by
  have ht : 2 * p + 1 < τ := by omega
  have hn : 2 * p + 1 < n := by omega
  simp only [terminalPairs, dif_pos ht, dif_pos hn, observationPrefix]
  rfl

private theorem runState_pairedHistory_eq_terminalTrace {d u n : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : Fin n → ℝ) (τ : ℕ) (hτ : τ ≤ n) :
    runState cfg K R seed (τ / 2) (pairedHistory (observationPrefix ys τ hτ)) =
      traceState cfg K R seed (terminalPairs ys) (τ / 2) := by
  unfold traceState
  congr 1
  funext i
  exact (terminalPairs_eq_pairedHistory (observationPrefix ys τ hτ) i).symm.trans
    (terminalPairs_observationPrefix ys τ hτ i i.isLt)



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



private theorem measurable_radialGuard {d : ℕ} (r : ℝ) : Measurable (radialGuard (d := d) r) :=
  Measurable.ite (measurableSet_le measurable_id.norm measurable_const)
    measurable_id measurable_const

private theorem radialGuard_mem_closedBall {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (x : Space d) :
    radialGuard r x ∈ Metric.closedBall 0 r := by
  unfold radialGuard
  split_ifs with hx
  · simpa using hx
  · simpa using hr

private theorem integrable_radialGuard_loss {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (r : ℝ) :
    Integrable (fun x => f (radialGuard r x)) (gaussian d) := by
  have hi := (integrable_lipschitz_gaussian hf).norm.add (integrable_const ‖f 0‖)
  apply hi.mono' (hf.continuous.measurable.comp (measurable_radialGuard r)).aestronglyMeasurable
  filter_upwards with x
  change ‖f (radialGuard r x)‖ ≤ ‖f x‖ + ‖f 0‖
  unfold radialGuard
  split_ifs
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact le_add_of_nonneg_left (norm_nonneg _)

private theorem gaussian_integral_neg {d : ℕ} {f : Space d → ℝ} (hf : Measurable f) :
    (∫ x, f (-x) ∂gaussian d) = ∫ x, f x ∂gaussian d := by
  have h := integral_map (μ := gaussian d) (φ := fun x : Space d => -x)
    (by fun_prop) hf.aestronglyMeasurable
  rw [gaussian_map_neg] at h
  exact h.symm

private theorem integrable_gaussian_neg {d : ℕ} {f : Space d → ℝ} (hf : Measurable f)
    (hi : Integrable f (gaussian d)) : Integrable (fun x => f (-x)) (gaussian d) := by
  have h := (integrable_map_measure (μ := gaussian d) (f := fun x : Space d => -x)
    hf.aestronglyMeasurable (by fun_prop)).1
  rw [gaussian_map_neg] at h
  exact h hi

/-- Radial truncation to the center decreases the Gaussian mean of a convex loss.
The proof uses sign symmetry, so it has no truncation-tail error. -/
private theorem gaussianMean_radialGuard_le {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ univ f) (r : ℝ) :
    (∫ x, f (radialGuard r x) ∂gaussian d) ≤ gaussianMean f := by
  have hm : Measurable (fun x => f (radialGuard r x)) :=
    hf.continuous.measurable.comp (measurable_radialGuard r)
  have hi := integrable_radialGuard_loss hf r
  have hfi := integrable_lipschitz_gaussian hf
  have hpoint (x : Space d) : f (radialGuard r x) + f (radialGuard r (-x)) ≤ f x + f (-x) := by
    by_cases hx : ‖x‖ ≤ r
    · simp only [radialGuard, norm_neg, hx, ↓reduceIte, le_refl]
    · have hm := hc.2 (mem_univ x) (mem_univ (-x))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      have he : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) = 0 := by module
      rw [he] at hm
      simp only [smul_eq_mul] at hm
      simp only [radialGuard, norm_neg, hx, ↓reduceIte]
      linarith
  have h := integral_mono (hi.add (integrable_gaussian_neg hm hi))
    (hfi.add (integrable_gaussian_neg hf.continuous.measurable hfi)) hpoint
  change (∫ x, f (radialGuard r x) + f (radialGuard r (-x)) ∂gaussian d) ≤
    (∫ x, f x + f (-x) ∂gaussian d) at h
  rw [integral_add hi (integrable_gaussian_neg hm hi),
    integral_add hfi (integrable_gaussian_neg hf.continuous.measurable hfi),
    gaussian_integral_neg hm, gaussian_integral_neg hf.continuous.measurable] at h
  unfold gaussianMean
  linarith

/-- Expected excess loss of the actual guarded query followed by the center. -/
private theorem guarded_pair_regret_le {d : ℕ} {f : Space d → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hc : ConvexOn ℝ univ f) {r b : ℝ}
    (hr : 0 ≤ r) (hb : 0 ≤ b)
    (hbounded : ∀ x ∈ Metric.closedBall 0 r, f x ≤ 1) :
    (∫ x, f (radialGuard r x) + f 0 - 2 * b ∂gaussian d) ≤
      2 * min 1 (gaussianMean f - b) := by
  have hi := integrable_radialGuard_loss hf r
  have he : (∫ x, f (radialGuard r x) + f 0 - 2 * b ∂gaussian d) =
      (∫ x, f (radialGuard r x) ∂gaussian d) + f 0 - 2 * b := by
    have hsum : Integrable (fun x => f (radialGuard r x) + f 0) (gaussian d) :=
      hi.add (integrable_const _)
    rw [integral_sub hsum (integrable_const _),
      integral_add hi (integrable_const _)]
    simp
  rw [he, mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  apply le_min
  · have hf0 := hbounded 0 (by simpa using hr)
    have hmean : (∫ x, f (radialGuard r x) ∂gaussian d) ≤ 1 := by
      have h := integral_mono hi (integrable_const (1 : ℝ))
        (fun x => hbounded _ (radialGuard_mem_closedBall hr x))
      simpa using h
    linarith
  · have hguard := gaussianMean_radialGuard_le hf hc r
    have hzero := gaussianMean_ge_value_zero hf hc
    linarith



namespace Algorithm

private theorem convexOn_loss_frame {d : ℕ} {L : Space d → ℝ}
    (hL : ConvexOn ℝ univ L) (F : Frame d) :
    ConvexOn ℝ univ (fun x => L (frameApply F x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have he : frameApply F (a • x + b • y) = a • frameApply F x + b • frameApply F y := by
    simp only [frameApply, matrixAction_add, matrixAction_smul]
    have hz : a • F.2 + b • F.2 = F.2 := by rw [← add_smul, hab, one_smul]
    simp only [smul_add]
    calc
      _ = a • matrixAction F.1 x + b • matrixAction F.1 y + (a • F.2 + b • F.2) :=
        congrArg (fun v => a • matrixAction F.1 x + b • matrixAction F.1 y + v) hz.symm
      _ = _ := by abel
  change L (frameApply F (a • x + b • y)) ≤
    a • L (frameApply F x) + b • L (frameApply F y)
  rw [he]
  exact hL.2 (mem_univ _) (mem_univ _) ha hb hab



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



private theorem measurable_coordinatePairLoss {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (encode : W × B → Ω) (he : Measurable encode) {T : ℕ}
    (w : W × (Fin T → ℝ)) (L : X → ℝ) (hL : Measurable L) :
    Measurable (coordinatePairLoss A encode w L) := by
  exact (hL.comp ((A.query_measurable T).comp
    ((measurable_firstHistoryMap encode he w).comp measurable_fst.fst))).add
      (hL.comp ((A.query_measurable (T + 1)).comp
        ((measurable_secondHistoryMap encode he w).comp measurable_fst)))

private theorem coordinatePairLoss_mem_Icc {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (encode : W × B → Ω) {T : ℕ}
    (w : W × (Fin T → ℝ)) (L : X → ℝ) {K : Set X} (hA : A.IsOn K)
    (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1) (p : (B × ℝ) × ℝ) :
    coordinatePairLoss A encode w L p ∈ Icc (0 : ℝ) 2 := by
  have h1 := hL _ (hA T (encode (w.1, p.1.1)) w.2)
  have h2 := hL _ (hA (T + 1) (encode (w.1, p.1.1)) (Fin.snoc w.2 p.1.2))
  unfold coordinatePairLoss
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Bounded losses have centered variance proxy one under the actual adaptive
pair law. This does not require independence of the two observations. -/
private theorem coordinatePairLoss_centered_mgf {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (Q : Measure B) [IsProbabilityMeasure Q] (ν : ObsKernel X) (hνm : ν.IsMeasurable)
    (encode : W × B → Ω) (he : Measurable encode) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (hLm : Measurable L) (γ : ℝ) (hν : NoiseCond K L γ ν)
    (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1) {T : ℕ} (w : W × (Fin T → ℝ)) :
    let μ := coordinatePairMeasure A Q ν hνm encode he w
    Integrable (coordinatePairLoss A encode w L) μ ∧
      HasSubgaussianMGF (fun p => coordinatePairLoss A encode w L p -
        ∫ q, coordinatePairLoss A encode w L q ∂μ) 1 μ := by
  let μ := coordinatePairMeasure A Q ν hνm encode he w
  letI : IsProbabilityMeasure μ := coordinatePairMeasure_probability A Q ν hνm encode he hA L γ hν w
  have hm := measurable_coordinatePairLoss A encode he w L hLm
  have hb : ∀ᵐ p ∂μ, coordinatePairLoss A encode w L p ∈ Icc (0 : ℝ) 2 :=
    Filter.Eventually.of_forall (coordinatePairLoss_mem_Icc A encode w L hA hL)
  refine ⟨Integrable.of_mem_Icc 0 2 hm.aemeasurable hb, ?_⟩
  convert hasSubgaussianMGF_of_mem_Icc hm.aemeasurable hb using 1 <;> norm_num

private theorem seedGaussian_insert_same {d u n : ℕ} (i : Fin (n + 1))
    (w : GaussianRemainder d u n) (x : Space d) :
    seedGaussian (insertGaussianSeed i (w, x)) i.val = x := by
  simp [seedGaussian, i.isLt, insertGaussianSeed]

private theorem runState_insertGaussianSeed_current {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (i : Fin (cfg.horizon + 1))
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) (x : Space d) :
    runState cfg K R (insertGaussianSeed i (w.1, x)) ((2 * i.val) / 2) (pairedHistory w.2) =
      runState cfg K R (insertGaussianSeed i (w.1, 0)) ((2 * i.val) / 2) (pairedHistory w.2) := by
  apply runState_seed_prefix
  · intro j hj
    rfl
  · intro j hj
    exact seedGaussian_insert_before i w.1 x 0 j (by omega)

/-- In a healthy state the first actual query is precisely the radial Gaussian
guard in the frozen current frame. -/
private theorem gaussianPolicy_first_query_guarded {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (R : ℝ) (anchor : Space d) (i : Fin (cfg.horizon + 1))
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ))
    (hbody : (interior (codedBody K (runState cfg K R (insertGaussianSeed i (w.1, 0))
      ((2 * i.val) / 2) (pairedHistory w.2)).1)).Nonempty) (x : Space d) :
    (policy (u := u) cfg K hK.isClosed.measurableSet R anchor).query (2 * i.val)
      (insertGaussianSeed i (w.1, x)) w.2 =
      frameApply (runState cfg K R (insertGaussianSeed i (w.1, 0))
        ((2 * i.val) / 2) (pairedHistory w.2)).2.1 (radialGuard (cfg.radius / d) x) := by
  have hs := runState_insertGaussianSeed_current cfg K R i w x
  have hbody' : (interior (codedBody K (runState cfg K R (insertGaussianSeed i (w.1, x))
      ((2 * i.val) / 2) (pairedHistory w.2)).1)).Nonempty := by rwa [hs]
  rw [policy_query_eq_proposed hd cfg hr hK hcv R anchor _ _ _ hbody']
  unfold proposedQuery
  rw [hs]
  simp only [show (2 * i.val) % 2 = 0 by omega, true_and,
    show (2 * i.val) / 2 = i.val by omega, seedGaussian_insert_same]
  unfold radialGuard
  split_ifs <;> rfl

private theorem runState_snoc_pair_history {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (p : ℕ) (ys : Fin (2 * p) → ℝ) (y : ℝ) :
    HEq (runState cfg K R seed ((2 * p + 1) / 2) (pairedHistory (Fin.snoc ys y)))
      (runState cfg K R seed ((2 * p) / 2) (pairedHistory ys)) := by
  have hp1 : (2 * p + 1) / 2 = p := by omega
  have hp0 : (2 * p) / 2 = p := by omega
  congr! 1 <;> try omega
  apply Function.hfunext (congrArg Fin (show (2 * p + 1) / 2 = (2 * p) / 2 by omega))
  intro i j hij
  have hv : i.val = j.val := Fin.val_eq_val_of_heq hij
  have h1 : 2 * i.val < 2 * p := by have := i.isLt; omega
  have h2 : 2 * i.val + 1 < 2 * p := by have := i.isLt; omega
  have hj : j.val < p := by have := j.isLt; omega
  have hj2 : 2 * j.val + 1 < 2 * p := by omega
  apply heq_of_eq
  simp [pairedHistory, Fin.snoc, hv, hj, hj2]

private theorem frame_eq_of_state_heq {d u p q : ℕ} (hpq : p = q)
    {s : State d u p} {t : State d u q} (h : HEq s t) : s.2.1 = t.2.1 := by
  subst q
  exact congrArg (fun st : State d u p => st.2.1) (eq_of_heq h)

private theorem codedBody_eq_of_state_heq {d u p q : ℕ} (K : Set (Space d)) (hpq : p = q)
    {s : State d u p} {t : State d u q} (h : HEq s t) : codedBody K s.1 = codedBody K t.1 := by
  subst q
  cases eq_of_heq h
  rfl

private theorem gaussianPolicy_second_query_center {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (R : ℝ) (anchor : Space d) (i : Fin (cfg.horizon + 1))
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ))
    (hbody : (interior (codedBody K (runState cfg K R (insertGaussianSeed i (w.1, 0))
      ((2 * i.val) / 2) (pairedHistory w.2)).1)).Nonempty) (x : Space d) (y : ℝ) :
    (policy (u := u) cfg K hK.isClosed.measurableSet R anchor).query (2 * i.val + 1)
      (insertGaussianSeed i (w.1, x)) (Fin.snoc w.2 y) =
      frameApply (runState cfg K R (insertGaussianSeed i (w.1, 0))
        ((2 * i.val) / 2) (pairedHistory w.2)).2.1 0 := by
  rw [policy_center_query_fixed cfg K hK.isClosed.measurableSet R anchor i w x y]
  have hs := runState_snoc_pair_history cfg K R (insertGaussianSeed i (w.1, 0)) i.val w.2 0
  have he : (2 * i.val + 1) / 2 = (2 * i.val) / 2 := by omega
  have hframe : (runState cfg K R (insertGaussianSeed i (w.1, 0))
      ((2 * i.val + 1) / 2) (pairedHistory (Fin.snoc w.2 0))).2.1 =
      (runState cfg K R (insertGaussianSeed i (w.1, 0))
      ((2 * i.val) / 2) (pairedHistory w.2)).2.1 := by
    exact frame_eq_of_state_heq he hs
  have hbody' : (interior (codedBody K (runState cfg K R (insertGaussianSeed i (w.1, 0))
      ((2 * i.val + 1) / 2) (pairedHistory (Fin.snoc w.2 0))).1)).Nonempty := by
    rwa [codedBody_eq_of_state_heq K he hs]
  rw [policy_query_off_guard hd cfg hr hK hcv R anchor _ _ _ hbody' (by omega), hframe]

/-- The exact predictable regret of one feasible Gaussian/center pair. The
current frame is the concrete canonical frame computed by the policy, and the
measure is the actual sequential observation law. -/
private theorem gaussianPolicy_pair_expected_regret_le {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {D : ℝ} (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (R : ℝ) (anchor : Space d) (ha : anchor ∈ K) (i : Fin (cfg.horizon + 1))
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLip : LipschitzWith 1 L) (hConv : ConvexOn ℝ univ L)
    (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1) (γ : ℝ) (hν : NoiseCond K L γ ν)
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ))
    (hbody : (interior (codedBody K (runState cfg K R (insertGaussianSeed i (w.1, 0))
      ((2 * i.val) / 2) (pairedHistory w.2)).1)).Nonempty)
    (xstar : Space d) (hxstar : xstar ∈ K) :
    let A := policy (u := u) cfg K hK.isClosed.measurableSet R anchor
    let μ := coordinatePairMeasure A (gaussian d) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
    let F := (runState cfg K R (insertGaussianSeed i (w.1, 0))
      ((2 * i.val) / 2) (pairedHistory w.2)).2.1
    (∫ p, coordinatePairLoss A (insertGaussianSeed i) w L p - 2 * L xstar ∂μ) ≤
      2 * min 1 (gaussianMean (fun x => L (frameApply F x)) - L xstar) := by
  let A := policy (u := u) cfg K hK.isClosed.measurableSet R anchor
  let κ := coordinateFirstKernel A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
  let κ' := coordinateSecondKernel A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
  let st := runState cfg K R (insertGaussianSeed i (w.1, 0)) ((2 * i.val) / 2) (pairedHistory w.2)
  let f : Space d → ℝ := fun x => L (frameApply st.2.1 x)
  have hA : A.IsOn K := policy_isOn cfg K hK.isClosed.measurableSet R ha
  letI : IsMarkovKernel κ := coordinateFirstKernel_isMarkov A ν hνm _ _ hA L γ hν w
  letI : IsMarkovKernel κ' := coordinateSecondKernel_isMarkov A ν hνm _ _ hA L γ hν w
  have hframe : st.2.1 = canonicalOuterFrame K cfg.radius st.1 :=
    runState_frame cfg K R _ _ _
  have hf : LipschitzWith ((d : ℝ) * D / cfg.radius).toNNReal f := by
    dsimp only [f]
    rw [hframe]
    exact canonical_loss_lipschitz hd hK hcv hr hdiam st.1 hbody L hLip
  have hfc : ConvexOn ℝ univ f := convexOn_loss_frame hConv st.2.1
  have hinner := canonicalOuterFrame_inner_ball hd hK hcv hr st.1 hbody
  have hfb : ∀ x ∈ Metric.closedBall 0 (cfg.radius / (d : ℝ)), f x ≤ 1 := by
    intro x hx
    have hmem := (hinner ⟨x, hx, rfl⟩).1
    rw [← hframe] at hmem
    exact (hL _ hmem).2
  let G : Space d → ℝ := fun x => f (radialGuard (cfg.radius / d) x) + f 0 - 2 * L xstar
  have hGm : Measurable G :=
    ((hf.continuous.measurable.comp (measurable_radialGuard _)).add_const _).sub_const _
  have hGi : Integrable G (gaussian d) :=
    ((integrable_radialGuard_loss hf _).add (integrable_const _)).sub (integrable_const _)
  have h1 := compProd_fst_moment (gaussian d) κ G hGm hGi
  have h2 := compProd_fst_moment ((gaussian d) ⊗ₘ κ) κ' (fun p => G p.1)
    (hGm.comp measurable_fst) h1.1
  have hpoint (p : (Space d × ℝ) × ℝ) :
      coordinatePairLoss A (insertGaussianSeed i) w L p - 2 * L xstar = G p.1.1 := by
    unfold coordinatePairLoss
    rw [gaussianPolicy_first_query_guarded hd cfg hr hK hcv R anchor i w hbody p.1.1,
      gaussianPolicy_second_query_center hd cfg hr hK hcv R anchor i w hbody p.1.1 p.1.2]
  change (∫ p, coordinatePairLoss A (insertGaussianSeed i) w L p - 2 * L xstar
      ∂(((gaussian d) ⊗ₘ κ) ⊗ₘ κ')) ≤ 2 * min 1 (gaussianMean f - L xstar)
  calc
    _ = ∫ p, G p.1.1 ∂(((gaussian d) ⊗ₘ κ) ⊗ₘ κ') := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ x, G x ∂gaussian d := h2.2.trans h1.2
    _ ≤ _ := guarded_pair_regret_le hf hfc (div_nonneg hr.le (Nat.cast_nonneg _))
      (hL xstar hxstar).1 hfb

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

private theorem measurable_coordinatePairLoss_joint {X Ω W B : Type} [MeasurableSpace X]
    [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace B]
    (A : QueryAlg X Ω) (encode : W × B → Ω) (he : Measurable encode)
    (L : X → ℝ) (hL : Measurable L) (T : ℕ) :
    Measurable (fun p : (W × (Fin T → ℝ)) × ((B × ℝ) × ℝ) =>
      coordinatePairLoss A encode p.1 L p.2) := by
  have h1 : Measurable (fun p : (W × (Fin T → ℝ)) × ((B × ℝ) × ℝ) =>
      firstHistoryMap encode p.1 p.2.1.1) := (measurable_firstHistoryMap_joint encode he T).comp
    (measurable_fst.prodMk measurable_snd.fst.fst)
  have h2 : Measurable (fun p : (W × (Fin T → ℝ)) × ((B × ℝ) × ℝ) =>
      secondHistoryMap encode p.1 p.2.1) := (measurable_secondHistoryMap_joint encode he T).comp
    (measurable_fst.prodMk measurable_snd.fst)
  exact (hL.comp ((A.query_measurable T).comp h1)).add
    (hL.comp ((A.query_measurable (T + 1)).comp h2))



private theorem measurable_pairLossMean {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B)
    [IsProbabilityMeasure Q] (ν : ObsKernel X) (hνm : ν.IsMeasurable)
    (encode : W × B → Ω) (he : Measurable encode) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (hLm : Measurable L) (γ : ℝ) (hν : NoiseCond K L γ ν) (T : ℕ) :
    Measurable (pairLossMean (T := T) A Q ν hνm encode he L) := by
  letI := coordinatePairKernel_isMarkov A Q ν hνm encode he hA L γ hν T
  exact ((measurable_coordinatePairLoss_joint A encode he L hLm T).stronglyMeasurable.integral_kernel_prod_right'
    (κ := coordinatePairKernel A Q ν hνm encode he T)).measurable

private theorem pairLossMean_eq_integral {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B)
    [IsProbabilityMeasure Q] (ν : ObsKernel X) (hνm : ν.IsMeasurable)
    (encode : W × B → Ω) (he : Measurable encode) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν) {T : ℕ} (w : W × (Fin T → ℝ)) :
    pairLossMean A Q ν hνm encode he L w =
      ∫ p, coordinatePairLoss A encode w L p ∂coordinatePairMeasure A Q ν hνm encode he w := by
  unfold pairLossMean
  rw [coordinatePairKernel_apply A Q ν hνm encode he hA L γ hν w]



private theorem measurable_pairLossIncrement {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLm : Measurable L) (γ : ℝ) (hν : NoiseCond K L γ ν) (p : ℕ) :
    Measurable (fun w : Seed d u cfg.horizon × ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) =>
      pairLossIncrement cfg K hK R anchor ν hνm L p w.1 w.2.1 w.2.2) := by
  unfold pairLossIncrement
  split_ifs with hp
  · let i : Fin (cfg.horizon + 1) := ⟨p, hp⟩
    let A := policy (u := u) cfg K hK R anchor
    have hw : Measurable (fun w : Seed d u cfg.horizon ×
        ((Fin (2 * p) → ℝ) × ((Space d × ℝ) × ℝ)) => (removeGaussianSeed i w.1, w.2.1)) :=
      ((measurable_removeGaussianSeed i).comp measurable_fst).prodMk measurable_snd.fst
    have hraw := (measurable_coordinatePairLoss_joint A (insertGaussianSeed i)
      (measurable_insertGaussianSeed cfg i) L hLm (2 * p)).comp (hw.prodMk measurable_snd.snd)
    exact hraw.sub ((measurable_pairLossMean A (gaussian d) ν hνm (insertGaussianSeed i)
      (measurable_insertGaussianSeed cfg i) (policy_isOn cfg K hK R ha) L hLm γ hν (2 * p)).comp hw)
  · exact measurable_const

private theorem pairLossIncrement_centered_mgf {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLm : Measurable L) (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1)
    (γ : ℝ) (hν : NoiseCond K L γ ν) (i : Fin (cfg.horizon + 1))
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) :
    HasSubgaussianMGF
      (pairLossIncrement cfg K hK R anchor ν hνm L i.val
        (prefixSeed i.val (insertGaussianSeed i (w.1, 0))) w.2) 1
      (coordinatePairMeasure (policy (u := u) cfg K hK R anchor) (gaussian d) ν hνm
        (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w) := by
  let A := policy (u := u) cfg K hK R anchor
  have hA := policy_isOn (u := u) cfg K hK R ha
  have h := (coordinatePairLoss_centered_mgf A (gaussian d) ν hνm (insertGaussianSeed i)
    (measurable_insertGaussianSeed cfg i) hA L hLm γ hν hL (canonicalGaussianRemainder i w.1, w.2)).2
  rw [coordinatePairMeasure_canonicalGaussianRemainder cfg K hK R anchor ν hνm i w] at h
  convert h using 1
  funext z
  simp only [pairLossIncrement, dif_pos i.isLt]
  rw [pairLossMean_eq_integral A (gaussian d) ν hνm (insertGaussianSeed i)
    (measurable_insertGaussianSeed cfg i) hA L γ hν]
  rw [show removeGaussianSeed i (prefixSeed i.val (insertGaussianSeed i (w.1, 0))) =
      canonicalGaussianRemainder i w.1 from rfl,
    coordinatePairMeasure_canonicalGaussianRemainder cfg K hK R anchor ν hνm i w]

/-- The cumulative actual bounded-loss martingale has variance proxy equal to
the number of completed pairs. -/
private theorem pairLossSum_hasSubgaussianMGF {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLm : Measurable L) (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1)
    (γ : ℝ) (hν : NoiseCond K L γ ν) (N : ℕ) (hN : N ≤ cfg.horizon + 1) :
    HasSubgaussianMGF
      (fun w => pairSum (pairLossIncrement (u := u) cfg K hK R anchor ν hνm L) N w.1 w.2)
      (N : NNReal) (historyMeasure (policy (u := u) cfg K hK R anchor)
        (seedMeasure d u cfg) ν hνm (2 * N)) := by
  let inc := pairLossIncrement (u := u) cfg K hK R anchor ν hνm L
  have hm := measurable_pairLossIncrement (u := u) cfg K hK R anchor ha ν hνm L hLm γ hν
  have ht (t : ℝ) := lintegral_exp_pairSum_le cfg K hK R anchor ha ν hνm L γ hν
    inc hm t (fun _ => t ^ 2 / 2) N hN (by
      intro p hp hp'
      apply Filter.Eventually.of_forall
      intro w
      have h := pairLossIncrement_centered_mgf cfg K hK R anchor ha ν hνm L hLm hL γ hν ⟨p, hp'⟩ w
      exact ⟨h.integrable_exp_mul t, by simpa only [mgf, NNReal.coe_one, one_mul] using h.mgf_le t⟩)
  have hbound (t : ℝ) := integral_exp_le_of_lintegral_exp_le
    (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N))
    (fun w => pairSum inc N w.1 w.2) (measurable_pairSum inc hm N)
    t (∑ p ∈ Finset.range N, t ^ 2 / 2) (ht t)
  refine ⟨fun t => (hbound t).1, fun t => ?_⟩
  simpa only [mgf, Finset.sum_const, Finset.card_range, nsmul_eq_mul, NNReal.coe_natCast,
    mul_div_assoc] using (hbound t).2

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

private theorem pairSum_eq_sum {d u n : ℕ}
    (increment : (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ)
    (N : ℕ) (s : Seed d u n) (ys : Fin (2 * N) → ℝ) :
    pairSum increment N s ys = ∑ p : Fin N,
      increment p.val (prefixSeed p.val s)
        (fun j => ys ⟨j.val, by have := p.isLt; have := j.isLt; omega⟩)
        ((seedGaussian s p.val, ys ⟨2 * p.val, by have := p.isLt; omega⟩),
          ys ⟨2 * p.val + 1, by have := p.isLt; omega⟩) := by
  induction N with
  | zero => simp [pairSum]
  | succ N ih =>
      simp only [pairSum, ih, Fin.sum_univ_castSucc]
      apply congrArg₂ (fun a b : ℝ => a + b)
      · apply Finset.sum_congr rfl
        intro p hp
        rfl
      · rfl





private theorem realPathLoss_snoc {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (L : X → ℝ) (ω : Ω) {τ : ℕ} (ys : Fin τ → ℝ) (y : ℝ) :
    realPathLoss A L (ω, Fin.snoc ys y) = realPathLoss A L (ω, ys) + L (A.query τ ω ys) := by
  simp [realPathLoss, pastQueries_snoc, Fin.sum_univ_castSucc]



private theorem sum_fin_pairs (N : ℕ) (f : Fin (2 * N) → ℝ) :
    (∑ j : Fin (2 * N), f j) = ∑ p : Fin N,
      (f ⟨2 * p.val, by have := p.isLt; omega⟩ +
        f ⟨2 * p.val + 1, by have := p.isLt; omega⟩) := by
  let e : Fin N × Fin 2 ≃ Fin (2 * N) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm N 2))
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Fin.sum_univ_two]
  congr 1 <;> congr 1 <;> apply Fin.ext <;> simp [e, finProdFinEquiv] <;> omega





private theorem pairLossSum_eq_realPathLoss_sub_predictable {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (N : ℕ) (hN : N ≤ cfg.horizon + 1)
    (w : Seed d u cfg.horizon × (Fin (2 * N) → ℝ)) :
    pairSum (pairLossIncrement cfg K hK R anchor ν hνm L) N w.1 w.2 =
      realPathLoss (policy (u := u) cfg K hK R anchor) L w -
        predictablePairLossTotal cfg K hK R anchor ν hνm L N w := by
  rw [pairSum_eq_sum, realPathLoss, sum_fin_pairs, predictablePairLossTotal, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpn : p.val < cfg.horizon + 1 := p.isLt.trans_le hN
  let i : Fin (cfg.horizon + 1) := ⟨p.val, hpn⟩
  simp only [pairLossIncrement, pairLossPredictableMean, dif_pos hpn]
  congr 1
  dsimp only [coordinatePairLoss]
  rw [policy_query_insert_remove_prefix cfg K hK R anchor i w.1 (2 * p.val) (by dsimp [i]; omega),
    policy_query_insert_remove_prefix cfg K hK R anchor i w.1 (2 * p.val + 1) (by dsimp [i]; omega)]
  have he : Fin.snoc
      (fun j : Fin (2 * p.val) => w.2 ⟨j.val, by have := p.isLt; have := j.isLt; omega⟩)
      (w.2 ⟨2 * p.val, by have := p.isLt; omega⟩) =
      (fun j : Fin (2 * p.val + 1) => w.2 ⟨j.val, by have := p.isLt; have := j.isLt; omega⟩) := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.snoc_last, Fin.val_last]
    · simp only [Fin.snoc_castSucc, Fin.val_castSucc]
  rw [he]
  rfl

private theorem pairLossSum_tail {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLm : Measurable L) (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1)
    (γ : ℝ) (hν : NoiseCond K L γ ν) (N : ℕ) (hN : N ≤ cfg.horizon + 1)
    (hNpos : 0 < N) {H : ℝ} (hH : 0 ≤ H) :
    (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg) ν hνm (2 * N)).real
      {w | Real.sqrt (2 * (N : ℝ) * H) ≤
        pairSum (pairLossIncrement cfg K hK R anchor ν hνm L) N w.1 w.2} ≤ Real.exp (-H) := by
  have h := (pairLossSum_hasSubgaussianMGF (u := u) cfg K hK R anchor ha ν hνm L hLm hL γ hν N hN).measure_ge_le
    (Real.sqrt_nonneg (2 * (N : ℝ) * H))
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have he : -(Real.sqrt (2 * (N : ℝ) * H)) ^ 2 / (2 * (N : ℝ)) = -H := by
    rw [Real.sq_sqrt (by positivity)]
    field_simp
  simpa only [NNReal.coe_natCast, he] using h

/-- Extending a legal path by `N-T` queries adds at most `N-T` loss. -/
private theorem realPathLoss_le_prefix_add {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (L : X → ℝ) {K : Set X} (hA : A.IsOn K)
    (hL : ∀ x ∈ K, L x ≤ 1) {T N : ℕ} (hTN : T ≤ N) (w : Ω × (Fin N → ℝ)) :
    realPathLoss A L w ≤ realPathLoss A L (historyPrefix hTN w) + (N - T : ℕ) := by
  induction N generalizing T with
  | zero =>
      have hT : T = 0 := by omega
      subst T
      simp [realPathLoss]
  | succ N ih =>
      by_cases hT : T = N + 1
      · subst T
        simp only [historyPrefix_self, Nat.sub_self, Nat.cast_zero, add_zero, le_refl]
      · have hprev : T ≤ N := by omega
        let w0 : Ω × (Fin N → ℝ) := (w.1, Fin.init w.2)
        have hc : realPathLoss A L w = realPathLoss A L w0 + L (A.query N w0.1 w0.2) := by
          simpa only [Fin.snoc_init_self] using
            realPathLoss_snoc A L w.1 (Fin.init w.2) (w.2 (Fin.last N))
        have hp : historyPrefix hTN w = historyPrefix hprev w0 := by
          simpa only [w0, Fin.snoc_init_self, Prod.eta] using
            historyPrefix_snoc hprev w0 (w.2 (Fin.last N))
        have hbound := ih hprev w0
        have hlast := hL _ (hA N w0.1 w0.2)
        have hcount : N + 1 - T = (N - T) + 1 := by omega
        rw [hc, hp, hcount, Nat.cast_add, Nat.cast_one]
        linarith

/-- On the terminal history space, realized regret is bounded by the exact
predictable pair regret plus a Gaussian martingale deviation and the unpaired
query, if present. -/
private theorem terminal_pairLoss_good_event {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLm : Measurable L) (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1)
    (γ : ℝ) (hν : NoiseCond K L γ ν) (N n : ℕ)
    (hN : N ≤ cfg.horizon + 1) (hNpos : 0 < N)
    (hpair : 2 * N ≤ n) (hodd : n ≤ 2 * N + 1) {H : ℝ} (hH : 0 ≤ H)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ G : Set (Seed d u cfg.horizon × (Fin n → ℝ)), MeasurableSet G ∧
      (historyMeasure (policy (u := u) cfg K hK R anchor) (seedMeasure d u cfg)
        ν hνm n).real Gᶜ ≤ Real.exp (-H) ∧
      ∀ w ∈ G, realPathLoss (policy (u := u) cfg K hK R anchor) L w - (n : ℝ) * b ≤
        predictablePairLossTotal cfg K hK R anchor ν hνm L N (historyPrefix hpair w) -
          2 * (N : ℝ) * b + Real.sqrt (2 * (N : ℝ) * H) + 1 := by
  let A := policy (u := u) cfg K hK R anchor
  let inc := pairLossIncrement (u := u) cfg K hK R anchor ν hνm L
  let a := Real.sqrt (2 * (N : ℝ) * H)
  let G0 : Set (Seed d u cfg.horizon × (Fin (2 * N) → ℝ)) :=
    {w | pairSum inc N w.1 w.2 ≤ a}
  have hG0 : MeasurableSet G0 := measurableSet_le
    (measurable_pairSum inc (measurable_pairLossIncrement cfg K hK R anchor ha ν hνm L hLm γ hν) N)
    measurable_const
  let G := (historyPrefix hpair) ⁻¹' G0
  have hA := policy_isOn (u := u) cfg K hK R ha
  letI := historyMeasure_probability A (seedMeasure d u cfg) ν hνm hA L γ hν (2 * N)
  refine ⟨G, hG0.preimage (measurable_historyPrefix hpair), ?_, ?_⟩
  · change (historyMeasure A (seedMeasure d u cfg) ν hνm n).real
      ((historyPrefix hpair) ⁻¹' G0ᶜ) ≤ Real.exp (-H)
    rw [historyMeasure_prefix_probability A (seedMeasure d u cfg) ν hνm hA L γ hν hpair G0ᶜ hG0.compl]
    apply le_trans (measureReal_mono (μ := historyMeasure A (seedMeasure d u cfg) ν hνm (2 * N))
      (show G0ᶜ ⊆ {w | a ≤ pairSum inc N w.1 w.2} from fun w hw =>
        (lt_of_not_ge (show ¬pairSum inc N w.1 w.2 ≤ a from hw)).le))
    exact pairLossSum_tail cfg K hK R anchor ha ν hνm L hLm hL γ hν N hN hNpos hH
  · intro w hw
    have he := pairLossSum_eq_realPathLoss_sub_predictable cfg K hK R anchor ν hνm L N hN
      (historyPrefix hpair w)
    have hsum : realPathLoss A L (historyPrefix hpair w) -
        predictablePairLossTotal cfg K hK R anchor ν hνm L N (historyPrefix hpair w) ≤ a := by
      rw [← he]
      exact hw
    have hcost := realPathLoss_le_prefix_add A L hA (fun x hx => (hL x hx).2) hpair w
    have hlast : ((n - 2 * N : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show n - 2 * N ≤ 1 by omega)
    have hcount : 2 * (N : ℝ) ≤ n := by exact_mod_cast hpair
    have hbase := mul_le_mul_of_nonneg_right hcount hb
    change realPathLoss A L w - (n : ℝ) * b ≤ _
    dsimp only [a] at hsum
    linarith

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

private theorem pairLossPredictableMean_le_traceGap {d u n : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {D : ℝ} (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLip : LipschitzWith 1 L) (hConv : ConvexOn ℝ univ L)
    (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1) (γ : ℝ) (hν : NoiseCond K L γ ν)
    (seed : Seed d u cfg.horizon) (ys : Fin n → ℝ) (p : ℕ)
    (hp : p < cfg.horizon + 1) (hpn : 2 * p ≤ n)
    (hbody : (interior (codedBody K (traceState cfg K R seed (terminalPairs ys) p).1)).Nonempty)
    (xstar : Space d) (hxstar : xstar ∈ K) :
    pairLossPredictableMean cfg K hK.isClosed.measurableSet R anchor ν hνm L p
      (prefixSeed p seed) (observationPrefix ys (2 * p) hpn) - 2 * L xstar ≤
      2 * min 1 (traceComparatorGap cfg K R seed (terminalPairs ys) L xstar p) := by
  let i : Fin (cfg.horizon + 1) := ⟨p, hp⟩
  let w : GaussianRemainder d u cfg.horizon × (Fin (2 * p) → ℝ) :=
    (removeGaussianSeed i (prefixSeed p seed), observationPrefix ys (2 * p) hpn)
  let s0 := insertGaussianSeed i (w.1, (0 : Space d))
  have hseed : runState cfg K R s0 ((2 * p) / 2) (pairedHistory w.2) =
      runState cfg K R seed ((2 * p) / 2) (pairedHistory w.2) := by
    apply runState_seed_prefix
    · intro j hj
      rfl
    · intro j hj
      have hjp : j < p := by omega
      change seedGaussian (insertGaussianSeed i (removeGaussianSeed i (prefixSeed p seed), 0)) j = _
      rw [seedGaussian_insert_remove_ne i _ _ j (by dsimp [i]; omega),
        seedGaussian_prefixSeed_before p j seed hjp]
  have he : (2 * p) / 2 = p := by omega
  have hstate : HEq (runState cfg K R s0 ((2 * p) / 2) (pairedHistory w.2))
      (traceState cfg K R seed (terminalPairs ys) p) := by
    rw [hseed]
    change HEq (runState cfg K R seed ((2 * p) / 2)
      (pairedHistory (observationPrefix ys (2 * p) hpn))) _
    rw [runState_pairedHistory_eq_terminalTrace]
    congr! 1
  have hframe := frame_eq_of_state_heq he hstate
  have hbody' : (interior (codedBody K (runState cfg K R s0 ((2 * p) / 2)
      (pairedHistory w.2)).1)).Nonempty := by
    rwa [codedBody_eq_of_state_heq K he hstate]
  have hbound := gaussianPolicy_pair_expected_regret_le hd cfg hr hK hcv hdiam R anchor ha i
    ν hνm L hLip hConv hL γ hν w hbody' xstar hxstar
  let A := policy (u := u) cfg K hK.isClosed.measurableSet R anchor
  let μ := coordinatePairMeasure A (gaussian d) ν hνm (insertGaussianSeed i)
    (measurable_insertGaussianSeed cfg i) w
  have hA := policy_isOn (u := u) cfg K hK.isClosed.measurableSet R ha
  letI : IsProbabilityMeasure μ := coordinatePairMeasure_probability A (gaussian d) ν hνm
    (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) hA L γ hν w
  have hi := (coordinatePairLoss_centered_mgf A (gaussian d) ν hνm (insertGaussianSeed i)
    (measurable_insertGaussianSeed cfg i) hA L hLip.continuous.measurable γ hν hL w).1
  have hmean : pairLossPredictableMean cfg K hK.isClosed.measurableSet R anchor ν hνm L p
      (prefixSeed p seed) (observationPrefix ys (2 * p) hpn) - 2 * L xstar =
      ∫ z, coordinatePairLoss A (insertGaussianSeed i) w L z - 2 * L xstar ∂μ := by
    simp only [pairLossPredictableMean, dif_pos hp]
    rw [pairLossMean_eq_integral A (gaussian d) ν hνm (insertGaussianSeed i)
      (measurable_insertGaussianSeed cfg i) hA L γ hν w]
    rw [integral_sub hi (integrable_const _)]
    simp
  rw [hmean]
  change (∫ z, coordinatePairLoss A (insertGaussianSeed i) w L z - 2 * L xstar ∂μ) ≤
    2 * min 1 (gaussianMean (fun x => L (frameApply
      (runState cfg K R s0 ((2 * p) / 2) (pairedHistory w.2)).2.1 x)) - L xstar) at hbound
  rw [hframe] at hbound
  exact hbound

private theorem predictablePairLossTotal_le_traceGap_sum {d u n : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {D : ℝ} (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLip : LipschitzWith 1 L) (hConv : ConvexOn ℝ univ L)
    (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1) (γ : ℝ) (hν : NoiseCond K L γ ν)
    (N : ℕ) (hN : N ≤ cfg.horizon + 1) (hpair : 2 * N ≤ n)
    (w : Seed d u cfg.horizon × (Fin n → ℝ))
    (hbody : ∀ p < N, (interior (codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1)).Nonempty)
    (xstar : Space d) (hxstar : xstar ∈ K) :
    predictablePairLossTotal cfg K hK.isClosed.measurableSet R anchor ν hνm L N
      (historyPrefix hpair w) - 2 * (N : ℝ) * L xstar ≤
      2 * ∑ p ∈ Finset.range N, min 1 (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p) := by
  have hpoint (p : Fin N) := pairLossPredictableMean_le_traceGap hd cfg hr hK hcv hdiam R anchor ha
    ν hνm L hLip hConv hL γ hν w.1 w.2 p.val (p.isLt.trans_le hN)
      (by have := p.isLt; omega) (hbody p.val p.isLt) xstar hxstar
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hpoint p)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have hfin : (∑ p : Fin N, min 1 (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p)) =
      ∑ p ∈ Finset.range N, min 1 (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p) :=
    Fin.sum_univ_eq_sum_range
      (fun p : ℕ => min 1 (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p)) N
  rw [hfin] at hsum
  have htotal : predictablePairLossTotal cfg K hK.isClosed.measurableSet R anchor ν hνm L N
      (historyPrefix hpair w) = ∑ p : Fin N,
      pairLossPredictableMean cfg K hK.isClosed.measurableSet R anchor ν hνm L p.val
        (prefixSeed p.val w.1) (observationPrefix w.2 (2 * p.val) (by have := p.isLt; omega)) := by
    unfold predictablePairLossTotal
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
  rw [htotal]
  have he : 2 * (N : ℝ) * L xstar = (N : ℝ) * (2 * L xstar) := by ring
  rw [he]
  exact hsum



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

theorem solution {d u : ℕ} (hd : 0 < d) (cfg : OracleConfig)
    (hr : 0 < cfg.radius) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    {D : ℝ} (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLip : LipschitzWith 1 L) (hConv : ConvexOn ℝ univ L)
    (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1) (γ : ℝ) (hν : NoiseCond K L γ ν)
    (N n : ℕ) (hN : N ≤ cfg.horizon + 1) (hNpos : 0 < N)
    (hpair : 2 * N ≤ n) (hodd : n ≤ 2 * N + 1)
    (xstar : Space d) (hxstar : xstar ∈ K) :
    ∃ G : Set (Seed d u cfg.horizon × (Fin n → ℝ)), MeasurableSet G ∧
      (historyMeasure (policy (u := u) cfg K hK.isClosed.measurableSet R anchor) (seedMeasure d u cfg)
        ν hνm n).real Gᶜ ≤ 1 / (n : ℝ) ∧
      ∀ w ∈ G,
        (∀ p < N, (interior (codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1)).Nonempty) →
        realPathLoss (policy (u := u) cfg K hK.isClosed.measurableSet R anchor) L w - (n : ℝ) * L xstar ≤
          2 * (∑ p ∈ Finset.range N, min 1 (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p)) +
            Real.sqrt ((n : ℝ) * Real.log n) + 1 := by
  have hnNat : 0 < n := by omega
  have hn : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  obtain ⟨G, hG, hprob, hgood⟩ := terminal_pairLoss_good_event (u := u)
    cfg K hK.isClosed.measurableSet R anchor ha ν hνm L hLip.continuous.measurable hL γ hν
    N n hN hNpos hpair hodd hlog (L xstar) (hL xstar hxstar).1
  refine ⟨G, hG, ?_, ?_⟩
  · simpa only [Real.exp_neg, Real.exp_log hn, one_div] using hprob
  · intro w hw hbody
    have hbound := hgood w hw
    have hmeans := predictablePairLossTotal_le_traceGap_sum hd cfg hr hK hcv hdiam R anchor ha
      ν hνm L hLip hConv hL γ hν N hN hpair w hbody xstar hxstar
    have hNR : 2 * (N : ℝ) ≤ n := by exact_mod_cast hpair
    have hsqrt : Real.sqrt (2 * (N : ℝ) * Real.log n) ≤ Real.sqrt ((n : ℝ) * Real.log n) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hNR hlog)
    linarith
