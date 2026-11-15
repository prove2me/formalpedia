-- Prove2me | solution 1 for LG2021.Concentration.estimatorGood_full_scalar
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-14T16:57:05.210243+00:00
-- url     : https://prove2.me/submissions/d394428a-de12-4c7d-b9b0-34382df22370

import Definitions.Def_LG2021_Policy
import Theorems.Thm_LG2021_Concentration_parameter_observation_bias_bounds
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

private theorem codedBody_snoc_subset {d p : ℕ} (K : Set (Space d)) (cuts : Fin p → CutCode d)
    (cut : CutCode d) : codedBody K (Fin.snoc cuts cut) ⊆ codedBody K cuts := by
  rw [codedBody_snoc]
  exact Set.inter_subset_left

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





























private theorem step_codedBody_subset {d u p : ℕ} (cfg : OracleConfig) (R : ℝ)
    (K : Set (Space d)) (rounding : (Fin (p + 1) → CutCode d) → Frame d)
    (st : State d u p) (next : Fin u → Space d) (x : Space d) (y y' : ℝ) :
    codedBody K (step cfg R rounding st next x y y').1 ⊆ codedBody K st.1 := by
  cases h : winner cfg (st.2.2.2.1 + 1) (updatedScalars cfg st x y y') <;>
    simp only [step, h, continueState, restartState] <;>
    exact codedBody_snoc_subset K st.1 _

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





private theorem truncation_eq_one_iff {d : ℕ} (lambda r : ℝ) (z x : Space d) :
    truncation lambda r z x = 1 ↔
      likelihoodRatio lambda z x ≤ Real.exp 1 / (1 - lambda) ^ d ∧
      ‖x‖ ≤ r / (d : ℝ) := by
  unfold truncation
  split_ifs <;> simp_all










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













private theorem coordinateFirstKernel_isMarkov {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {K : Set X} (hA : A.IsOn K) (L : X → ℝ) (γ : ℝ) (hν : NoiseCond K L γ ν)
    {T : ℕ} (w : W × (Fin T → ℝ)) : IsMarkovKernel (coordinateFirstKernel A ν hνm encode he w) := by
  letI := observationKernel_isMarkov A ν hνm hA L γ hν T
  unfold coordinateFirstKernel
  infer_instance

















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

/-- The exact policy observation kernel has the normalized raw observation moment at every history. -/
private theorem observationKernel_unit_moment {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (hL : ∀ x ∈ K, L x ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) (w : Ω × (Fin T → ℝ)) :
    Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (observationKernel A ν hνm T w) ∧
      (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂observationKernel A ν hνm T w) ≤ 2 :=
  unitNoiseCond_observation_moment ν hν hL T (A.pastQueries w.1 w.2) w.2 (A.query T w.1 w.2)
    (fun i => hA i w.1 _) (hA T w.1 w.2)

private theorem observationKernel_unit_mean {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable) {K : Set X} (hA : A.IsOn K)
    (L : X → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (T : ℕ) (w : Ω × (Fin T → ℝ)) :
    (∫ y : ℝ, y ∂observationKernel A ν hνm T w) = L (A.query T w.1 w.2) :=
  (hν T (A.pastQueries w.1 w.2) w.2 (A.query T w.1 w.2)
    (fun i => hA i w.1 _) (hA T w.1 w.2)).2.2.1







end LG2021.Concentration

end
end

/- LG2021ConcentrationPredictableMeans -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm









private theorem gaussianPolicy_scalarPredictableMean_eq {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (i : Fin (cfg.horizon + 1)) (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (L : Space d → ℝ) (hν : BilateralProfitMHR.CorollaryTransport.UnitNoiseCond K L ν)
    (w : GaussianRemainder d u cfg.horizon × (Fin (2 * i.val) → ℝ)) (z : Space d) :
    scalarPredictableMean (policy (u := u) cfg K hK R anchor) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) cfg.lambda cfg.radius z w =
    (∫ q : Space d × ℝ, q.2 * scalarCoefficient cfg.lambda cfg.radius z q.1
      ∂((gaussian d) ⊗ₘ coordinateFirstKernel (policy (u := u) cfg K hK R anchor) ν hνm
        (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w)) -
      L ((policy (u := u) cfg K hK R anchor).query (2 * i.val + 1)
        (insertGaussianSeed i (w.1, 0)) (Fin.snoc w.2 0)) := by
  have hA := policy_isOn (u := u) cfg K hK R ha
  have hn := BilateralProfitMHR.CorollaryTransport.unitNoiseCond_noiseCond K L ν hν
  unfold scalarPredictableMean
  rw [coordinateFirstPairKernel_apply _ _ _ _ _ _ hA L 1 hn w]
  congr 1
  exact observationKernel_unit_mean _ ν hνm hA L hν _ (secondHistoryMap (insertGaussianSeed i) w (0, 0))




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







private theorem seedGaussian_prefixSeed_before {d u n : ℕ} (p j : ℕ) (s : Seed d u n) (hj : j < p) :
    seedGaussian (prefixSeed p s) j = seedGaussian s j := by
  unfold seedGaussian
  split_ifs with h
  · simp [prefixSeed, hj]
  · rfl



























end LG2021.Concentration

end
end

/- LG2021ConcentrationKernelPrefix -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm











private theorem seedGaussian_insert_remove_ne {d u n : ℕ} (i : Fin (n + 1))
    (s : Seed d u n) (x : Space d) (j : ℕ) (hji : j ≠ i.val) :
    seedGaussian (insertGaussianSeed i (removeGaussianSeed i s, x)) j = seedGaussian s j := by
  unfold seedGaussian
  split_ifs with hj
  · have hfin : (⟨j, hj⟩ : Fin (n + 1)) ≠ i := fun h => hji (congrArg Fin.val h)
    simp [insertGaussianSeed, removeGaussianSeed, Fin.insertNth_removeNth, hfin]
  · rfl



















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

























private theorem confidenceRadius_eq_scalarThreshold (p : Algorithm.OracleConfig)
    (hc : p.momentConstant = oracleMomentConstant)
    (hC : p.concentrationConstant = oracleConcentrationConstant) (u m : ℕ) :
    Algorithm.confidenceRadius p u m =
      scalarConfidenceThreshold p.lambda (Algorithm.confidenceLog p u) (m : ℝ)+
        1/(8*p.radius*(p.horizon : ℝ)) := by
  simp only [Algorithm.confidenceRadius, scalarConfidenceThreshold, hc, hC]

end LG2021.Concentration

end
end

/- LG2021ConcentrationHistoryPrefix -/
section

noncomputable section

namespace LG2021.Concentration

open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal



















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





private theorem traceWinner_eq_none_of_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (p : ℕ)
    (hstage : traceStage cfg K R seed ys (p + 1) = traceStage cfg K R seed ys p) :
    traceWinner cfg K R seed ys p = none := by
  by_contra hh
  simp only [traceStage, if_neg hh] at hstage
  omega

private theorem traceScalarSums_succ {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (p : ℕ) (s : Fin u)
    (hstage : traceStage cfg K R seed ys (p + 1) = traceStage cfg K R seed ys p) :
    (traceState cfg K R seed ys (p + 1)).2.2.2.2.1 s =
      (traceState cfg K R seed ys p).2.2.2.2.1 s + traceScalarUpdate cfg K R seed ys p s := by
  have hn := traceWinner_eq_none_of_same_stage cfg K R seed ys p hstage
  rw [traceState_succ, step_continues cfg R _ _ _ _ _ _ hn]
  simp only [continueState, updatedScalars, traceScalarUpdate]
  ring



private theorem stage_sum_identity {E : Type*} [AddCommMonoid E]
    (stage : ℕ → ℕ) (hmono : Monotone stage) (F D : ℕ → E)
    (hstep : ∀ p, stage (p + 1) = stage p → F (p + 1) = F p + D p)
    {t p : ℕ} (htp : t ≤ p) (hstage : stage p = stage t) :
    F p = F t + ∑ j ∈ Finset.Ico t p, D j := by
  revert hstage
  induction p, htp using Nat.le_induction with
  | base => intro _; simp
  | succ j htj ih =>
      intro hj
      have htag : stage j = stage t := le_antisymm
        ((hmono (Nat.le_succ j)).trans_eq hj) (hmono htj)
      rw [hstep j (hj.trans htag.symm), ih htag, Finset.sum_Ico_succ_top htj]
      simp only [add_assoc]

private theorem traceScalarSums_eq_start_add_sum {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (s : Fin u) {t p : ℕ} (htp : t ≤ p)
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys t) :
    (traceState cfg K R seed ys p).2.2.2.2.1 s =
      (traceState cfg K R seed ys t).2.2.2.2.1 s +
        ∑ j ∈ Finset.Ico t p, traceScalarUpdate cfg K R seed ys j s :=
  stage_sum_identity _ (traceStage_monotone cfg K R seed ys)
    (fun j => (traceState cfg K R seed ys j).2.2.2.2.1 s)
    (fun j => traceScalarUpdate cfg K R seed ys j s)
    (fun j hj => traceScalarSums_succ cfg K R seed ys j s hj) htp hstage



private theorem traceState_sums_zero_of_age_zero {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (p : ℕ)
    (hage : (traceState cfg K R seed ys p).2.2.2.1 = 0) :
    (traceState cfg K R seed ys p).2.2.2.2.1 = 0 ∧
      (traceState cfg K R seed ys p).2.2.2.2.2 = 0 := by
  cases p with
  | zero => exact ⟨rfl, rfl⟩
  | succ p =>
      rw [traceState_succ] at hage ⊢
      cases h : traceWinner cfg K R seed ys p with
      | none =>
          rw [step_continues cfg R _ _ _ _ _ _ h] at hage
          change (traceState cfg K R seed ys p).2.2.2.1 + 1 = 0 at hage
          omega
      | some s =>
          rw [step_restarts cfg R _ _ _ _ _ _ s h]
          exact ⟨rfl, rfl⟩

private theorem traceCandidates_eq_between_same_stage {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) {t j p : ℕ} (htj : t ≤ j) (hjp : j ≤ p)
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys t) :
    (traceState cfg K R seed ys j).2.2.1 = (traceState cfg K R seed ys t).2.2.1 := by
  have htag : traceStage cfg K R seed ys j = traceStage cfg K R seed ys t := by
    apply le_antisymm
    · exact (traceStage_monotone cfg K R seed ys hjp).trans_eq hstage
    · exact traceStage_monotone cfg K R seed ys htj
  exact congrArg (fun z : Frame d × (Fin u → Space d) => z.2)
    (traceCore_eq_of_same_stage cfg K R seed ys htag)

private theorem traceScalarSums_eq_start_add_fixed_sum {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (s : Fin u) {t p : ℕ} (htp : t ≤ p)
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys t) :
    (traceState cfg K R seed ys p).2.2.2.2.1 s =
      (traceState cfg K R seed ys t).2.2.2.2.1 s +
        ∑ j ∈ Finset.Ico t p, ((ys j).1 * scalarCoefficient cfg.lambda cfg.radius
          ((traceState cfg K R seed ys t).2.2.1 s) (seedGaussian seed j) - (ys j).2) := by
  rw [traceScalarSums_eq_start_add_sum cfg K R seed ys s htp hstage]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rcases Finset.mem_Ico.1 hj with ⟨htj, hjp⟩
  unfold traceScalarUpdate
  rw [traceCandidates_eq_between_same_stage cfg K R seed ys htj hjp.le hstage]



private theorem traceAge_eq_start_add_sub {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) {t p : ℕ} (htp : t ≤ p)
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys t) :
    (traceState cfg K R seed ys p).2.2.2.1 =
      (traceState cfg K R seed ys t).2.2.2.1 + (p - t) := by
  have h := stage_sum_identity _ (traceStage_monotone cfg K R seed ys)
    (fun j => (traceState cfg K R seed ys j).2.2.2.1) (fun _ => (1 : ℕ))
    (fun j hj => by
      have hn := traceWinner_eq_none_of_same_stage cfg K R seed ys j hj
      rw [traceState_succ, step_continues cfg R _ _ _ _ _ _ hn]
      rfl) htp hstage
  simpa using h

private theorem traceUpdatedScalars_eq_fixed_sum {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (s : Fin u) {t p : ℕ} (htp : t ≤ p)
    (hstage : traceStage cfg K R seed ys p = traceStage cfg K R seed ys t) :
    updatedScalars cfg (traceState cfg K R seed ys p) (seedGaussian seed p)
        (ys p).1 (ys p).2 s =
      (traceState cfg K R seed ys t).2.2.2.2.1 s +
        ∑ j ∈ Finset.Ico t (p + 1), ((ys j).1 * scalarCoefficient cfg.lambda cfg.radius
          ((traceState cfg K R seed ys t).2.2.1 s) (seedGaussian seed j) - (ys j).2) := by
  unfold updatedScalars
  rw [traceScalarSums_eq_start_add_fixed_sum cfg K R seed ys s htp hstage,
    traceCandidates_eq_between_same_stage cfg K R seed ys htp le_rfl hstage,
    Finset.sum_Ico_succ_top htp]
  ring



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



private theorem historyAt_eq {N p : ℕ} (ys : Fin N → ℝ) (hp : 2 * p ≤ N) :
    historyAt ys p = observationPrefix ys (2 * p) hp := by
  simp only [historyAt, dif_pos hp]

/-- The recursive statistic is exactly the sum of its actual observed pair increments. -/
private theorem pairSum_eq_sum_terminal {d u n N : ℕ}
    (increment : (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ)
    (s : Seed d u n) (ys : Fin N → ℝ) (p : ℕ) (hp : 2 * p ≤ N) :
    pairSum increment p s (historyAt ys p) =
      ∑ j ∈ Finset.range p, increment j (prefixSeed j s) (historyAt ys j)
        ((seedGaussian s j, (terminalPairs ys j).1), (terminalPairs ys j).2) := by
  induction p with
  | zero => simp [pairSum]
  | succ p ih =>
      have hp' : 2 * p ≤ N := by omega
      have hlast : 2 * p + 1 < N := by omega
      rw [Finset.sum_range_succ, ← ih hp']
      rw [historyAt_eq ys hp, historyAt_eq ys hp']
      simp only [pairSum, terminalPairs, dif_pos hlast]
      rfl

end LG2021.Concentration

end
end

/- LG2021ConcentrationStageExpansion -/
section

noncomputable section
namespace LG2021.Concentration
open Algorithm

private theorem traceState_prefix_historyAt {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (s : Seed d u cfg.horizon) (ys : Fin N → ℝ) {j p : ℕ} (hj : 2 * j ≤ N) (hp : p ≤ j) :
    traceState cfg K R (prefixSeed j s) (terminalPairs (historyAt ys j)) p =
      traceState cfg K R s (terminalPairs ys) p := by
  rw [historyAt_eq ys hj, terminalTrace_prefix_eq cfg K R _ ys (2 * j) hj (by omega)]
  unfold traceState
  apply runState_seed_prefix
  · intro k hk
    rfl
  · intro k hk
    exact seedGaussian_prefixSeed_before j k s (by omega)

private theorem traceWinner_prefix_historyAt {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (s : Seed d u cfg.horizon) (ys : Fin N → ℝ) {j p : ℕ} (hj : 2 * j ≤ N) (hp : p < j) :
    traceWinner cfg K R (prefixSeed j s) (terminalPairs (historyAt ys j)) p =
      traceWinner cfg K R s (terminalPairs ys) p := by
  unfold traceWinner
  rw [traceState_prefix_historyAt cfg K R s ys hj hp.le, seedGaussian_prefixSeed_before j p s hp,
    historyAt_eq ys hj, terminalPairs_observationPrefix ys (2 * j) hj p (by omega)]

private theorem traceStage_prefix_historyAt {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (s : Seed d u cfg.horizon) (ys : Fin N → ℝ) {j p : ℕ} (hj : 2 * j ≤ N) (hp : p ≤ j) :
    traceStage cfg K R (prefixSeed j s) (terminalPairs (historyAt ys j)) p =
      traceStage cfg K R s (terminalPairs ys) p := by
  induction p with
  | zero => rfl
  | succ p ih =>
      rw [traceStage, traceStage, ih (by omega), traceWinner_prefix_historyAt cfg K R s ys hj (by omega)]

private theorem stageCandidate_prefix_historyAt {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (s : Seed d u cfg.horizon) (ys : Fin N → ℝ) {a j : ℕ} (hj : 2 * j ≤ N) (ha : a ≤ j) (k : Fin u) :
    stageCandidate cfg K R a k j (prefixSeed j s, historyAt ys j) =
      (traceState cfg K R s (terminalPairs ys) a).2.2.1 k := by
  unfold stageCandidate
  rw [traceState_prefix_historyAt cfg K R s ys hj ha]



private theorem stageActive_prefix_historyAt {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (s : Seed d u cfg.horizon) (ys : Fin N → ℝ) {a j : ℕ} (hj : 2 * j ≤ N) (ha : a ≤ j) :
    stageActive cfg K R a j (prefixSeed j s, historyAt ys j) =
      decide (traceStage cfg K R s (terminalPairs ys) j = traceStage cfg K R s (terminalPairs ys) a) := by
  unfold stageActive sameStageBefore
  rw [traceStage_prefix_historyAt cfg K R s ys hj le_rfl, traceStage_prefix_historyAt cfg K R s ys hj ha]
  split_ifs <;> simp_all

end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR



private theorem stageScalarError_eq_sum {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (a b : ℕ) (k : Fin u)
    (s : Seed d u cfg.horizon) (ys : Fin (2 * b) → ℝ) (hab : a < b) (hb : b ≤ cfg.horizon + 1)
    (hstage : traceStage cfg K R s (terminalPairs ys) (b-1) = traceStage cfg K R s (terminalPairs ys) a) :
    stageScalarError cfg K hK R anchor ν hνm a k b (s, ys) =
      ∑ j ∈ Finset.Ico a b,
        ((terminalPairs ys j).1 * scalarCoefficient cfg.lambda cfg.radius
          ((traceState cfg K R s (terminalPairs ys) a).2.2.1 k) (seedGaussian s j) -
          (terminalPairs ys j).2 - stageScalarCenter cfg K hK R anchor ν hνm a k s ys j) := by
  let inc := scalarIncrement cfg K hK R anchor ν hνm (fun p => decide (a ≤ p))
    (stageActive cfg K R a) (stageCandidate cfg K R a k)
  have he := pairSum_eq_sum_terminal inc s ys b le_rfl
  have hself : historyAt ys b = ys := by rw [historyAt_eq ys le_rfl]; rfl
  rw [hself] at he
  change stageScalarError cfg K hK R anchor ν hνm a k b (s, ys) = _ at he
  rw [he]
  have hfilter : (Finset.range b).filter (fun j => a ≤ j) = Finset.Ico a b := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  rw [← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  have hjb := Finset.mem_range.1 hj
  have hjN : 2 * j ≤ 2 * b := by omega
  have hjh : j < cfg.horizon + 1 := by omega
  by_cases haj : a ≤ j
  · have htag : traceStage cfg K R s (terminalPairs ys) j = traceStage cfg K R s (terminalPairs ys) a := by
      have h1 := traceStage_monotone cfg K R s (terminalPairs ys) haj
      have h2 := traceStage_monotone cfg K R s (terminalPairs ys) (show j ≤ b-1 by omega)
      omega
    simp only [inc, scalarIncrement, dif_pos hjh, decide_eq_true haj, Bool.true_and,
      stageActive_prefix_historyAt cfg K R s ys hjN haj, htag, decide_true, ↓reduceIte,
      stageCandidate_prefix_historyAt cfg K R s ys hjN haj, stageScalarCenter]
    rw [if_pos haj]
  · simp only [inc, scalarIncrement, dif_pos hjh, decide_eq_false haj, decide_false, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, haj]

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

/-- The scalar stopped error equals the actual updated buffer minus its predictable centers. -/
private theorem stageScalarError_eq_updated_sub_centers {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (a b : ℕ) (k : Fin u)
    (s : Seed d u cfg.horizon) (ys : Fin (2 * b) → ℝ) (hab : a < b) (hb : b ≤ cfg.horizon + 1)
    (hstage : traceStage cfg K R s (terminalPairs ys) (b-1) = traceStage cfg K R s (terminalPairs ys) a)
    (hage : (traceState cfg K R s (terminalPairs ys) a).2.2.2.1 = 0) :
    stageScalarError cfg K hK R anchor ν hνm a k b (s, ys) =
      updatedScalars cfg (traceState cfg K R s (terminalPairs ys) (b-1)) (seedGaussian s (b-1))
        (terminalPairs ys (b-1)).1 (terminalPairs ys (b-1)).2 k -
          ∑ j ∈ Finset.Ico a b, stageScalarCenter cfg K hK R anchor ν hνm a k s ys j := by
  rw [stageScalarError_eq_sum cfg K hK R anchor ν hνm a b k s ys hab hb hstage,
    Finset.sum_sub_distrib]
  have hu := traceUpdatedScalars_eq_fixed_sum cfg K R s (terminalPairs ys) k (show a ≤ b-1 by omega) hstage
  have hz := (traceState_sums_zero_of_age_zero cfg K R s (terminalPairs ys) a hage).1
  rw [hz] at hu
  have hbp : b-1+1=b := by omega
  simpa only [hbp, Pi.zero_apply, zero_add] using congrArg
    (fun q => q - ∑ j ∈ Finset.Ico a b, stageScalarCenter cfg K hK R anchor ν hνm a k s ys j) hu.symm



/-- Averaging bounded individual biases costs the same bias after normalization. -/
private theorem abs_average_bias_le (a b : ℕ) (hab : a < b) (M : ℕ → ℝ) (θ β : ℝ)
    (hM : ∀ j ∈ Finset.Ico a b, |M j - θ| ≤ β) :
    |(∑ j ∈ Finset.Ico a b, M j) / ((b-a : ℕ) : ℝ) - θ| ≤ β := by
  have hm : (0 : ℝ) < (b-a : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hab
  have heq : (∑ j ∈ Finset.Ico a b, M j) / ((b-a : ℕ) : ℝ) - θ =
      (∑ j ∈ Finset.Ico a b, (M j - θ)) / ((b-a : ℕ) : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    field_simp
  rw [heq, abs_div, abs_of_pos hm]
  apply (div_le_iff₀ hm).2
  calc
    |∑ j ∈ Finset.Ico a b, (M j - θ)| ≤ ∑ j ∈ Finset.Ico a b, |M j - θ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Ico a b, β := Finset.sum_le_sum hM
    _ = β * ((b-a : ℕ) : ℝ) := by simp [mul_comm]

/-- A centered cumulative estimate and the genuine pointwise bias bounds yield the actual mean error. -/
private theorem abs_average_error_le (a b : ℕ) (hab : a < b) (M : ℕ → ℝ) (raw err θ β ε : ℝ)
    (herr : err = raw - ∑ j ∈ Finset.Ico a b, M j)
    (hM : ∀ j ∈ Finset.Ico a b, |M j - θ| ≤ β)
    (hconf : |err / ((b-a : ℕ) : ℝ)| ≤ ε) :
    |raw / ((b-a : ℕ) : ℝ) - θ| ≤ ε + β := by
  have hbias := abs_average_bias_le a b hab M θ β hM
  have heq : raw / ((b-a : ℕ) : ℝ) - θ =
      err / ((b-a : ℕ) : ℝ) + ((∑ j ∈ Finset.Ico a b, M j) / ((b-a : ℕ) : ℝ) - θ) := by
    rw [herr]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hconf hbias)

end LG2021.Concentration

namespace LG2021.Concentration
open Algorithm BilateralProfitMHR

private theorem traceSampleCount_eq_interval {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (a b : ℕ) (s : Seed d u cfg.horizon) (ys : Fin (2*b) → ℝ) (hab : a < b)
    (hstage : traceStage cfg K R s (terminalPairs ys) (b-1) = traceStage cfg K R s (terminalPairs ys) a)
    (hage : (traceState cfg K R s (terminalPairs ys) a).2.2.2.1 = 0) :
    traceSampleCount cfg K R s (terminalPairs ys) (b-1) = b-a := by
  unfold traceSampleCount
  rw [traceAge_eq_start_add_sub cfg K R s (terminalPairs ys) (show a ≤ b-1 by omega) hstage, hage]
  omega

/-- Exact scalar-buffer confidence from the stopped deviation and the actual predictable biases. -/
private theorem traceScalar_confidence_of_stageError {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (a b : ℕ) (k : Fin u)
    (s : Seed d u cfg.horizon) (ys : Fin (2 * b) → ℝ) (hab : a < b) (hb : b ≤ cfg.horizon + 1)
    (hstage : traceStage cfg K R s (terminalPairs ys) (b-1) = traceStage cfg K R s (terminalPairs ys) a)
    (hage : (traceState cfg K R s (terminalPairs ys) a).2.2.2.1 = 0)
    (F : Space d → ℝ) (β ε : ℝ)
    (hbias : ∀ j ∈ Finset.Ico a b,
      |stageScalarCenter cfg K hK R anchor ν hνm a k s ys j - traceGap cfg K R s (terminalPairs ys) F (b-1) k| ≤ β)
    (hconf : |stageScalarError cfg K hK R anchor ν hνm a k b (s, ys) / ((b-a : ℕ) : ℝ)| ≤ ε) :
    |traceScalar cfg K R s (terminalPairs ys) (b-1) k - traceGap cfg K R s (terminalPairs ys) F (b-1) k| ≤ ε + β := by
  have he := stageScalarError_eq_updated_sub_centers cfg K hK R anchor ν hνm a b k s ys hab hb hstage hage
  have hx := abs_average_error_le a b hab _ _ _ _ β ε he hbias hconf
  simpa only [traceScalar, scalarEstimate, traceSampleCount_eq_interval cfg K R a b s ys hab hstage hage] using hx



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

/-- The actual measurable scalar and directional predictable centers have the
numerical bias guaranteed by the explicit estimator lemma. All observation
moments, feasible-query identities, and canonical frame bounds are discharged. -/
private theorem gaussianPolicy_predictable_bias_bounds {d n u : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (R : ℝ) (anchor : Space d) (ha : anchor ∈ K) (i : Fin (n + 1))
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLip : LipschitzWith 1 L) (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1)
    (hν : CorollaryTransport.UnitNoiseCond K L ν)
    (w : GaussianRemainder d u n × (Fin (2 * i.val) → ℝ))
    (hbody : (interior (codedBody K (runState (oracleConfig d D n) K R (insertGaussianSeed i (w.1, 0))
      ((2 * i.val) / 2) (pairedHistory w.2)).1)).Nonempty)
    (z η : Space d) (hz : ‖z‖ ≤ (oracleConfig d D n).radius / (2 * (d : ℝ))) (hη : ‖η‖ ≤ 1) :
    let cfg := oracleConfig d D n
    let A := policy (u := u) cfg K hK.isClosed.measurableSet R anchor
    let f := fun x => L (frameApply (runState cfg K R (insertGaussianSeed i (w.1, 0))
      ((2 * i.val) / 2) (pairedHistory w.2)).2.1 x)
    |scalarPredictableMean A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i)
        cfg.lambda cfg.radius z w - (surrogate cfg.lambda f z - f 0)| ≤
      1 / (8 * cfg.radius * (n : ℝ)) ∧
    |gradientPredictableMean A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i)
        cfg.lambda cfg.radius z η w - fderiv ℝ (surrogate cfg.lambda f) z η| ≤
      1 / (8 * cfg.radius * (n : ℝ)) := by
  let cfg := oracleConfig d D n
  let A := policy (u := u) cfg K hK.isClosed.measurableSet R anchor
  let st := runState cfg K R (insertGaussianSeed i (w.1, 0)) ((2 * i.val) / 2) (pairedHistory w.2)
  let f : Space d → ℝ := fun x => L (frameApply st.2.1 x)
  let κ := coordinateFirstKernel A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) w
  have hA := policy_isOn (u := u) cfg K hK.isClosed.measurableSet R ha
  have hnoise := CorollaryTransport.unitNoiseCond_noiseCond K L ν hν
  letI : IsMarkovKernel κ := coordinateFirstKernel_isMarkov A ν hνm _ _ hA L 1 hnoise w
  have hr : 0 < cfg.radius := (paperRadius_bounds hd (parameterLog_bounds d n hD).1).2.1
  have hframe : st.2.1 = canonicalOuterFrame K cfg.radius st.1 := runState_frame cfg K R _ _ _
  have hf : LipschitzWith ((d : ℝ) * D / cfg.radius).toNNReal f := by
    dsimp only [f]
    rw [hframe]
    exact canonical_loss_lipschitz hd hK hcv hr hdiam st.1 hbody L hLip
  have hinner := canonicalOuterFrame_inner_ball hd hK hcv hr st.1 hbody
  have hzmem : frameApply st.2.1 0 ∈ K := by
    have hzero : (0 : Space d) ∈ Metric.closedBall 0 (cfg.radius / (d : ℝ)) := by
      simp only [Metric.mem_closedBall, dist_self]
      positivity
    have h := (hinner ⟨0, hzero, rfl⟩).1
    rwa [← hframe] at h
  have hf0 : |f 0| ≤ 1 := by
    rw [abs_of_nonneg (hL _ hzmem).1]
    exact (hL _ hzmem).2
  have hLipbound : (((d : ℝ) * D / cfg.radius).toNNReal : ℝ) ≤
      paperLipschitz d D (parameterLog d D n) := by
    rw [Real.coe_toNNReal _ (by positivity)]
    rfl
  have hobs : ∀ᵐ x ∂gaussian d,
      Integrable (fun y : ℝ => Real.exp (y ^ 2 / 16)) (κ x) ∧
        (∫ y : ℝ, Real.exp (y ^ 2 / 16) ∂κ x) ≤ 2 :=
    Filter.Eventually.of_forall fun x =>
      observationKernel_unit_moment A ν hνm hA L hν hL (2 * i.val)
        (firstHistoryMap (insertGaussianSeed i) w x)
  have hmean : ∀ᵐ x ∂gaussian d,
      truncation cfg.lambda cfg.radius z x = 1 → (∫ y, y ∂κ x) = f x := by
    apply Filter.Eventually.of_forall
    intro x hx
    have hxnorm := ((truncation_eq_one_iff cfg.lambda cfg.radius z x).1 hx).2
    have he := observationKernel_unit_mean A ν hνm hA L hν (2 * i.val)
      (firstHistoryMap (insertGaussianSeed i) w x)
    change (∫ y, y ∂κ x) = L (A.query (2 * i.val) (insertGaussianSeed i (w.1, x)) w.2) at he
    rw [gaussianPolicy_first_query_guarded hd cfg hr hK hcv R anchor i w hbody x] at he
    simpa only [radialGuard, if_pos hxnorm] using he
  have hb := parameter_observation_bias_bounds hd hn hD hf hf0 hLipbound z η hz hη κ hobs hmean
  have hs := gaussianPolicy_scalarPredictableMean_eq cfg K hK.isClosed.measurableSet R anchor ha i
    ν hνm L hν w z
  rw [gaussianPolicy_second_query_center hd cfg hr hK hcv R anchor i w hbody 0 0] at hs
  have hg : gradientPredictableMean A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i)
      cfg.lambda cfg.radius z η w =
      ∫ q : Space d × ℝ, q.2 * directionalGradientCoefficient cfg.lambda cfg.radius z η q.1
        ∂((gaussian d) ⊗ₘ κ) := by
    unfold gradientPredictableMean
    rw [coordinateFirstPairKernel_apply A (gaussian d) ν hνm (insertGaussianSeed i)
      (measurable_insertGaussianSeed cfg i) hA L 1 hnoise w]
  change |scalarPredictableMean A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i)
      cfg.lambda cfg.radius z w - (surrogate cfg.lambda f z - f 0)| ≤ _ ∧
    |gradientPredictableMean A ν hνm (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i)
      cfg.lambda cfg.radius z η w - fderiv ℝ (surrogate cfg.lambda f) z η| ≤ _
  constructor
  · rw [hs]
    change |((∫ q : Space d × ℝ, q.2 * scalarCoefficient cfg.lambda cfg.radius z q.1
      ∂((gaussian d) ⊗ₘ κ)) - f 0) - (surrogate cfg.lambda f z - f 0)| ≤ _
    rw [sub_sub_sub_cancel_right]
    exact hb.1
  · rw [hg]
    exact hb.2

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

private theorem traceBody_antitone {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (s : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) :
    Antitone (fun p => codedBody K (traceState cfg K R s ys p).1) := by
  apply antitone_nat_of_succ_le
  intro p
  rw [traceState_succ]
  exact step_codedBody_subset cfg R K _ _ _ _ _ _

private theorem runState_frozen_current_historyAt {d u N : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (s : Seed d u cfg.horizon) (ys : Fin N → ℝ)
    (i : Fin (cfg.horizon + 1)) (hi : 2 * i.val ≤ N) :
    HEq (runState cfg K R
      (insertGaussianSeed i (removeGaussianSeed i (prefixSeed i.val s), 0))
      ((2 * i.val) / 2) (pairedHistory (historyAt ys i.val)))
      (traceState cfg K R s (terminalPairs ys) i.val) := by
  have hseed : runState cfg K R
      (insertGaussianSeed i (removeGaussianSeed i (prefixSeed i.val s), 0))
      ((2 * i.val) / 2) (pairedHistory (historyAt ys i.val)) =
      runState cfg K R s ((2 * i.val) / 2) (pairedHistory (historyAt ys i.val)) := by
    apply runState_seed_prefix
    · intro j hj
      rfl
    · intro j hj
      rw [seedGaussian_insert_remove_ne i _ _ j (by omega),
        seedGaussian_prefixSeed_before i.val j s (by omega)]
  rw [hseed, historyAt_eq ys hi, runState_pairedHistory_eq_terminalTrace]
  congr! 1
  omega




private theorem stage_scalar_bias_bound {d n u N : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D)
    (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (hLip : LipschitzWith 1 L) (hL : ∀ x ∈ K, L x ∈ Icc (0 : ℝ) 1)
    (hν : CorollaryTransport.UnitNoiseCond K L ν)
    (s : Seed d u n) (ys : Fin N → ℝ) (a j p : ℕ) (k : Fin u)
    (hj : j < n + 1) (hjN : 2 * j ≤ N) (hjp : j ≤ p)
    (hstage : traceStage (oracleConfig d D n) K R s (terminalPairs ys) j =
      traceStage (oracleConfig d D n) K R s (terminalPairs ys) a)
    (hbody : (interior (codedBody K
      (traceState (oracleConfig d D n) K R s (terminalPairs ys) p).1)).Nonempty)
    (hz : ‖(traceState (oracleConfig d D n) K R s (terminalPairs ys) a).2.2.1 k‖ ≤
      (oracleConfig d D n).radius / (2 * (d : ℝ)))
 :
    let cfg := oracleConfig d D n
    |stageScalarCenter cfg K hK.isClosed.measurableSet R anchor ν hνm a k s ys j -
      traceGap cfg K R s (terminalPairs ys) L a k| ≤ 1 / (8 * cfg.radius * (n : ℝ)) := by
  let cfg := oracleConfig d D n
  let i : Fin (n + 1) := ⟨j, hj⟩
  let w : GaussianRemainder d u n × (Fin (2 * i.val) → ℝ) :=
    (removeGaussianSeed i (prefixSeed j s), historyAt ys j)
  let s0 := insertGaussianSeed i (w.1, (0 : Space d))
  have he : (2 * i.val) / 2 = j := by dsimp [i]; omega
  have hstate : HEq (runState cfg K R s0 ((2 * i.val) / 2) (pairedHistory w.2))
      (traceState cfg K R s (terminalPairs ys) j) :=
    runState_frozen_current_historyAt cfg K R s ys i hjN
  have hbodyj : (interior (codedBody K (traceState cfg K R s (terminalPairs ys) j).1)).Nonempty :=
    hbody.mono (interior_mono (traceBody_antitone cfg K R s (terminalPairs ys) hjp))
  have hbody' : (interior (codedBody K (runState cfg K R s0 ((2 * i.val) / 2)
      (pairedHistory w.2)).1)).Nonempty := by
    rwa [codedBody_eq_of_state_heq K he hstate]
  have hcore := traceCore_eq_of_same_stage cfg K R s (terminalPairs ys) hstage
  have hframeja : (traceState cfg K R s (terminalPairs ys) j).2.1 =
      (traceState cfg K R s (terminalPairs ys) a).2.1 :=
    congrArg (fun t : Frame d × (Fin u → Space d) => t.1) hcore
  have hframe := (frame_eq_of_state_heq he hstate).trans hframeja
  have hb := gaussianPolicy_predictable_bias_bounds hd hn hD hK hcv hdiam R anchor ha i
    ν hνm L hLip hL hν w hbody'
    ((traceState cfg K R s (terminalPairs ys) a).2.2.1 k)
    0 hz (by simp)
  have hs := hb.1
  change |scalarPredictableMean _ _ _ _ _ _ _ _ w -
      (surrogate cfg.lambda (fun x => L (frameApply
        (runState cfg K R s0 ((2 * i.val) / 2) (pairedHistory w.2)).2.1 x)) _ -
       L (frameApply (runState cfg K R s0 ((2 * i.val) / 2) (pairedHistory w.2)).2.1 0))| ≤ _ at hs
  rw [hframe] at hs
  have hjcfg : j < (oracleConfig d D n).horizon + 1 := hj
  dsimp only
  simp only [stageScalarCenter, dif_pos hjcfg]
  exact hs

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

private theorem trace_candidates_at_age_zero {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : ℕ → ℝ × ℝ) (p : ℕ)
    (hage : (traceState cfg K R seed ys p).2.2.2.1 = 0) :
    (traceState cfg K R seed ys p).2.2.1 = seedCandidates seed p := by
  cases p with
  | zero => rfl
  | succ q =>
      rw [traceState_succ] at hage ⊢
      cases h : traceWinner cfg K R seed ys q with
      | none =>
          rw [step_continues cfg R _ _ _ _ _ _ h] at hage
          change (traceState cfg K R seed ys q).2.2.2.1 + 1 = 0 at hage
          omega
      | some s =>
          rw [step_restarts cfg R _ _ _ _ _ _ s h]
          rfl

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

private theorem paper_traceScalar_confidence_of_stageError {d n u : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (F : Space d → ℝ)
    (hLip : LipschitzWith 1 F) (hF : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1)
    (hν : CorollaryTransport.UnitNoiseCond K F ν)
    (a b : ℕ) (k : Fin u) (s : Seed d u n) (ys : Fin (2*b) → ℝ)
    (hab : a < b) (hb : b ≤ n + 1)
    (hstage : traceStage (oracleConfig d D n) K R s (terminalPairs ys) (b-1) =
      traceStage (oracleConfig d D n) K R s (terminalPairs ys) a)
    (hage : (traceState (oracleConfig d D n) K R s (terminalPairs ys) a).2.2.2.1 = 0)
    (hbody : (interior (codedBody K (traceState (oracleConfig d D n) K R s (terminalPairs ys) (b-1)).1)).Nonempty)
    (hz : ‖(traceState (oracleConfig d D n) K R s (terminalPairs ys) a).2.2.1 k‖ ≤
      (oracleConfig d D n).radius / (2 * (d : ℝ)))
    (hconf : |stageScalarError (oracleConfig d D n) K hK.isClosed.measurableSet R anchor ν hνm a k b (s, ys) /
      ((b-a : ℕ) : ℝ)| ≤ scalarConfidenceThreshold (oracleConfig d D n).lambda (confidenceLog (oracleConfig d D n) u) ((b-a : ℕ) : ℝ)) :
    |traceScalar (oracleConfig d D n) K R s (terminalPairs ys) (b-1) k -
      traceGap (oracleConfig d D n) K R s (terminalPairs ys) F (b-1) k| ≤
        confidenceRadius (oracleConfig d D n) u (traceSampleCount (oracleConfig d D n) K R s (terminalPairs ys) (b-1)) := by
  let cfg := oracleConfig d D n
  change traceStage cfg K R s (terminalPairs ys) (b-1) = traceStage cfg K R s (terminalPairs ys) a at hstage
  have hcore := traceCore_eq_of_same_stage cfg K R s (terminalPairs ys) hstage
  have hf : (traceState cfg K R s (terminalPairs ys) (b-1)).2.1 =
      (traceState cfg K R s (terminalPairs ys) a).2.1 :=
    congrArg (fun t : Frame d × (Fin u → Space d) => t.1) hcore
  have hc : (traceState cfg K R s (terminalPairs ys) (b-1)).2.2.1 =
      (traceState cfg K R s (terminalPairs ys) a).2.2.1 :=
    congrArg (fun t : Frame d × (Fin u → Space d) => t.2) hcore
  have hgap : traceGap cfg K R s (terminalPairs ys) F (b-1) k = traceGap cfg K R s (terminalPairs ys) F a k := by
    unfold traceGap traceLocalLoss
    rw [hf, hc]
  have hbound := traceScalar_confidence_of_stageError cfg K hK.isClosed.measurableSet R anchor
    ν hνm a b k s ys hab hb hstage hage F
    (1 / (8 * cfg.radius * (n : ℝ))) (scalarConfidenceThreshold cfg.lambda (confidenceLog cfg u) ((b-a : ℕ) : ℝ))
    (fun j hj => by
      have hjab := Finset.mem_Ico.1 hj
      have htag : traceStage cfg K R s (terminalPairs ys) j = traceStage cfg K R s (terminalPairs ys) a := by
        have h1 := traceStage_monotone cfg K R s (terminalPairs ys) hjab.1
        have h2 := traceStage_monotone cfg K R s (terminalPairs ys) (show j ≤ b-1 by omega)
        omega
      have hh := stage_scalar_bias_bound hd hn hD hK hcv hdiam R anchor ha ν hνm F hLip hF hν
        s ys a j (b-1) k (by omega) (by omega) (by omega) htag hbody hz
      rw [hgap]
      exact hh) hconf
  convert hbound using 1
  rw [confidenceRadius_eq_scalarThreshold cfg rfl rfl,
    traceSampleCount_eq_interval cfg K R a b s ys hab hstage hage]
  rfl

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

private theorem traceScalar_prefix_eq {d u n : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (R : ℝ) (seed : Seed d u cfg.horizon)
    (ys : Fin n → ℝ) (τ : ℕ) (hτ : τ ≤ n) (p : ℕ) (hp : p < τ / 2) (s : Fin u) :
    traceScalar cfg K R seed (terminalPairs (observationPrefix ys τ hτ)) p s =
      traceScalar cfg K R seed (terminalPairs ys) p s := by
  unfold traceScalar traceSampleCount
  rw [terminalTrace_prefix_eq cfg K R seed ys τ hτ hp.le,
    terminalPairs_observationPrefix ys τ hτ p hp]



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

/-- Outside the concrete scalar failure event, every healthy actual oracle state has valid scalar estimates. -/
private theorem scalar_confidence_of_not_stage_failure {d n u N : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (F : Space d → ℝ)
    (hLip : LipschitzWith 1 F) (hF : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1)
    (hν : CorollaryTransport.UnitNoiseCond K F ν) (hN : N ≤ n)
    (s : Seed d u n) (ys : Fin (2*N) → ℝ)
    (hseed : ∀ a ≤ N, ∀ k, ‖seedCandidates s a k‖ ≤ (oracleConfig d D n).radius / (2 * (d : ℝ)))
    (hgood : (s, ys) ∉ scalarStageFailure (oracleConfig d D n) K hK.isClosed.measurableSet R anchor ν hνm N
      (confidenceLog (oracleConfig d D n) u)) :
    ∀ p < N, (interior (codedBody K (traceState (oracleConfig d D n) K R s (terminalPairs ys) p).1)).Nonempty →
      ∀ k, |traceScalar (oracleConfig d D n) K R s (terminalPairs ys) p k -
        traceGap (oracleConfig d D n) K R s (terminalPairs ys) F p k| ≤
          confidenceRadius (oracleConfig d D n) u (traceSampleCount (oracleConfig d D n) K R s (terminalPairs ys) p) := by
  intro p hp hbody k
  let cfg := oracleConfig d D n
  have hprefix : 2 * (p+1) ≤ 2 * N := by omega
  let zs := observationPrefix ys (2*(p+1)) hprefix
  obtain ⟨a, hap, hage, htag⟩ := trace_exists_stage_start cfg K R s (terminalPairs zs) p
  have hab : a < p+1 := by omega
  have hstate : traceState cfg K R s (terminalPairs zs) p = traceState cfg K R s (terminalPairs ys) p :=
    terminalTrace_prefix_eq cfg K R s ys (2*(p+1)) hprefix (by omega)
  have hbody' : (interior (codedBody K (traceState cfg K R s (terminalPairs zs) p).1)).Nonempty := by rwa [hstate]
  have hz : ‖(traceState cfg K R s (terminalPairs zs) a).2.2.1 k‖ ≤ cfg.radius / (2 * (d : ℝ)) := by
    rw [trace_candidates_at_age_zero cfg K R s (terminalPairs zs) a hage]
    exact hseed a (by omega) k
  have hconf : |stageScalarError cfg K hK.isClosed.measurableSet R anchor ν hνm a k (p+1) (s, zs) /
      ((p+1-a : ℕ) : ℝ)| ≤ scalarConfidenceThreshold cfg.lambda (confidenceLog cfg u) ((p+1-a : ℕ) : ℝ) := by
    apply le_of_lt
    apply lt_of_not_ge
    intro hh
    apply hgood
    exact ⟨⟨a, by omega⟩, ⟨p+1, by omega⟩, k, hab, hh⟩
  have hh := paper_traceScalar_confidence_of_stageError hd hn hD hK hcv hdiam R anchor ha ν hνm F hLip hF hν
    a (p+1) k s zs hab (by omega) (by simpa using htag.symm) hage (by simpa using hbody') hz hconf
  simp only [Nat.add_sub_cancel] at hh
  change |traceScalar cfg K R s (terminalPairs (observationPrefix ys (2*(p+1)) hprefix)) p k -
      traceGap cfg K R s (terminalPairs (observationPrefix ys (2*(p+1)) hprefix)) F p k| ≤
    confidenceRadius cfg u (traceSampleCount cfg K R s (terminalPairs (observationPrefix ys (2*(p+1)) hprefix)) p) at hh
  rw [traceScalar_prefix_eq cfg K R s ys (2*(p+1)) hprefix p (by omega) k,
    traceGap_prefix_eq cfg K R s ys (2*(p+1)) hprefix F p (by omega) k] at hh
  simpa only [traceSampleCount, terminalTrace_prefix_eq cfg K R s ys (2*(p+1)) hprefix (by omega : p ≤ (2*(p+1))/2)] using hh

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

theorem solution {d n u N : ℕ} (hd : 0 < d) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) {K : Set (Space d)} (hK : IsCompact K) (hcv : Convex ℝ K)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) (R : ℝ) (anchor : Space d) (ha : anchor ∈ K)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (F : Space d → ℝ)
    (hLip : LipschitzWith 1 F) (hF : ∀ x ∈ K, F x ∈ Set.Icc (0 : ℝ) 1)
    (hν : CorollaryTransport.UnitNoiseCond K F ν) (hN : N ≤ n) (hpair : 2*N ≤ n)
    (w : Seed d u n × (Fin n → ℝ)) (v : Fin (d+1) → Space d)
    (hseed : ∀ a k, ‖seedCandidates w.1 a k‖ ≤ (oracleConfig d D n).radius / (2*(d : ℝ)))
    (hg : historyPrefix hpair w ∈ estimatorGood (oracleConfig d D n) K hK.isClosed.measurableSet R anchor ν hνm N v) :
    ∀ p < N, (interior (codedBody K (traceState (oracleConfig d D n) K R w.1 (terminalPairs w.2) p).1)).Nonempty → ∀ k,
      |traceScalar (oracleConfig d D n) K R w.1 (terminalPairs w.2) p k -
        traceGap (oracleConfig d D n) K R w.1 (terminalPairs w.2) F p k| ≤
      confidenceRadius (oracleConfig d D n) u (traceSampleCount (oracleConfig d D n) K R w.1 (terminalPairs w.2) p) := by
  let cfg := oracleConfig d D n
  have hs := scalar_confidence_of_not_stage_failure hd hn hD hK hcv hdiam R anchor ha ν hνm F hLip hF hν hN
    w.1 (observationPrefix w.2 (2*N) hpair) (fun a _ k => hseed a k) hg.1
  intro p hp hbody k
  have hstate := terminalTrace_prefix_eq cfg K R w.1 w.2 (2*N) hpair (by omega : p ≤ (2*N)/2)
  have hh := hs p hp (by rwa [hstate]) k
  rw [traceScalar_prefix_eq cfg K R w.1 w.2 (2*N) hpair p (by omega) k,
    traceGap_prefix_eq cfg K R w.1 w.2 (2*N) hpair F p (by omega) k] at hh
  dsimp only [cfg] at hstate
  simpa only [traceSampleCount, hstate] using hh
