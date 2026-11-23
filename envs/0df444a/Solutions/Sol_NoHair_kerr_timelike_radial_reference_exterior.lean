-- Prove2me | solution 1 for NoHair.kerr_timelike_radial_reference_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T07:27:48.121134+00:00
-- url     : https://prove2.me/submissions/d5317264-f729-455a-bf01-dee82ec6c078

import Theorems.Thm_NoHair_kerr_stationary_uniform_timelike_radius
import Theorems.Thm_NoHair_kerrNewman_outerHorizon_futureTrapped
import Theorems.Thm_NoHair_kerrNewman_exterior_timelikeAccess
import Theorems.Thm_NoHair_ksRadius_superlevel_frontier
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair NoHair.KNE Set
open scoped ContDiff Manifold BigOperators Topology
noncomputable section

private abbrev I4 := 𝓘(ℝ, E4)

private theorem inclusion_deriv (U : TopologicalSpace.Opens E4) (x : U) :
    (mfderiv I4 I4 (Subtype.val : U → E4) x : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 :=
  mfderiv_extChartAt_self (I := I4) (x := x)

private theorem inclusion_diff (U : TopologicalSpace.Opens E4) (x : U) :
    MDifferentiableAt I4 I4 (Subtype.val : U → E4) x :=
  (contMDiff_subtype_val (I := I4) (U := U) (n := ∞)).mdifferentiableAt (by simp)

private theorem basis_entry (A : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    matrixBilin A (coordBasis i) (coordBasis j) = A i j := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp (coordBasis i)) (WithLp.ofLp (coordBasis j)) = _
  simp only [coordBasis, EuclideanSpace.single, PiLp.ofLp_single]
  rw [Matrix.toLinearMap₂'_apply]
  simp_rw [← Finset.smul_sum]
  simp [Pi.single_apply, ite_smul, Finset.sum_ite_eq, Finset.sum_ite_eq']

private theorem standard_isometry (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    IsKerrNewmanDOC (kerrNewmanMetricField m a e) (kerrNewmanFieldField a e)
      ((Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e) m a e := by
  classical
  let U := kerrNewmanSpacetime a
  let b := kerrNewmanOuterRadius m a e
  let S := kerrNewmanDOC m a e
  have hb : 0 < b := add_pos_of_pos_of_nonneg hp.1 (Real.sqrt_nonneg _)
  obtain ⟨base,_⟩ := (ksRadius_superlevel_frontier a b hb).2.nonempty
  have hS : IsOpen S := isOpen_lt continuous_const (continuous_ksRadius a)
  let ψ (y : E4) : U := if hy : y ∈ U then ⟨y,hy⟩ else base
  have hv (y : E4) (hy : y ∈ S) : (ψ y).val = y := by
    have hyU : y ∈ U := lt_trans hb hy
    simp [ψ, hyU]
  have hgerm : EqOn ((Subtype.val : U → E4) ∘ ψ) id S := hv
  have hsm : ContMDiffOn I4 I4 ∞ ψ S := by
    intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U ψ S z).mp
    exact ((contMDiff_id (I := I4)).contMDiffOn.congr (fun w hw => hgerm hw)) z hz
  have hder (y : E4) (hy : y ∈ S) :
      (mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 := by
    have hψ := ((hsm y hy).contMDiffAt (hS.mem_nhds hy)).mdifferentiableAt (by simp)
    have hc := mfderiv_comp y (inclusion_diff U (ψ y)) hψ
    rw [inclusion_deriv] at hc
    change mfderiv I4 I4 ((Subtype.val : U → E4) ∘ ψ) y = (mfderiv I4 I4 ψ y : E4 →L[ℝ] E4) at hc
    rw [← hc, mfderiv_eq_fderiv, (hgerm.eventuallyEq_of_mem (hS.mem_nhds hy)).fderiv_eq, fderiv_id]
  have hcoeff (A : E4 → Matrix (Fin 4) (Fin 4) ℝ) (y : E4) (hy : y ∈ S) (i j : Fin 4) :
      pullbackCoeffs (M := U) (fun x => matrixBilin (A x.val)) ψ y i j = A y i j := by
    unfold pullbackCoeffs
    rw [hder y hy]
    change matrixBilin (A (ψ y).val) (coordBasis i) (coordBasis j) = A y i j
    rw [hv y hy, basis_entry]
  refine ⟨0,ψ,?_,?_⟩
  · refine ⟨Subtype.val, ?_, ?_, ?_, ?_, hsm, contMDiff_subtype_val.contMDiffOn⟩
    · intro y hy
      change (ψ y).val ∈ S
      rwa [hv y hy]
    · exact fun _ hx => hx
    · exact fun _ hy => hv _ hy
    · exact fun x hx => Subtype.ext (hv x.val hx)
  · intro y hy
    constructor
    · ext i j
      exact hcoeff (kerrNewmanMetric m a e) y hy i j
    · rw [Real.cos_zero, one_smul, Real.sin_zero, zero_smul, add_zero]
      ext i j
      exact hcoeff (kerrNewmanField a e) y hy i j

private theorem cartesian_outside (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (x : kerrNewmanSpacetime a) : spatialRadius x.val ≤ ksRadius a x.val + |a| := by
  let r := ksRadius a x.val
  let k := ksNull a x.val
  have hr : 0 < r := x.property
  have hrel : k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 = 1 := ks_rel a x.val hr
  have hs : spatialRadius x.val ^ 2 = x.val 1 ^ 2 + x.val 2 ^ 2 + x.val 3 ^ 2 := Real.sq_sqrt (by positivity)
  rw [ks_x1 a x.val hr, ks_x2 a x.val hr, ks_x3 a x.val hr] at hs
  change spatialRadius x.val ^ 2 = (r*k 1-a*k 2)^2 + (a*k 1+r*k 2)^2 + (r*k 3)^2 at hs
  have hid : spatialRadius x.val ^ 2 = r^2 + a^2 - (a*k 3)^2 := by
    linear_combination hs + (r^2+a^2)*hrel
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg hr.le (abs_nonneg a))).mp
  change spatialRadius x.val ^ 2 ≤ (r+|a|)^2
  nlinarith only [hid, sq_abs a, sq_nonneg (a*k 3), mul_nonneg hr.le (abs_nonneg a)]

private theorem radial_past_future (m a R : ℝ) (hp : IsKerrNewmanBlackHoleParams m a 0)
    (hR : kerrNewmanOuterRadius m a 0 ≤ R) :
    let A := {x : kerrNewmanSpacetime a | R < ksRadius a x.val}
    let D := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a 0
    let g := kerrNewmanMetricField m a 0
    let T := kerrNewmanTimeDirection m a 0
    chronoPastSet g T A = D ∧ D ⊆ chronoFutureSet g T A := by
  let A := {x : kerrNewmanSpacetime a | R < ksRadius a x.val}
  let B := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion (R+|a|)
  have hBA : B ⊆ A := by
    intro z hz
    change R + |a| < spatialRadius z.val at hz
    change R < ksRadius a z.val
    linarith [cartesian_outside m a 0 hp z]
  have access := kerrNewman_exterior_timelikeAccess m a 0 hp (R+|a|)
  have trap := (kerrNewman_outerHorizon_futureTrapped m a 0 hp).2
  refine ⟨Subset.antisymm ?_ ?_, ?_⟩
  · intro x hx
    obtain ⟨z,hz,γ,hγ,h0,h1⟩ := mem_iUnion₂.mp hx
    change kerrNewmanOuterRadius m a 0 < ksRadius a x.val
    by_contra! h
    have hend := trap γ hγ (h0 ▸ h : ksRadius a (γ 0).val ≤ kerrNewmanOuterRadius m a 0)
    rw [h1] at hend
    exact (not_lt_of_ge hend) (lt_of_le_of_lt hR hz)
  · intro x hx
    obtain ⟨z,hz,hγ⟩ := mem_iUnion₂.mp ((access hx).1)
    exact mem_iUnion₂.mpr ⟨z,hBA hz,hγ⟩
  · intro x hx
    obtain ⟨z,hz,hγ⟩ := mem_iUnion₂.mp ((access hx).2)
    exact mem_iUnion₂.mpr ⟨z,hBA hz,hγ⟩

theorem solution (m a R : ℝ) (hp : IsKerrNewmanBlackHoleParams m a 0)
    (φ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a)
    (hφ : ∀ s x, (φ s x).val = x.val + s • coordBasis 0)
    (hsym : IsSymmetryFlow (kerrNewmanMetricField m a 0) (kerrNewmanFieldField a 0) φ)
    (htime : ∀ x : kerrNewmanSpacetime a, R < ksRadius a x.val →
      kerrNewmanMetricField m a 0 x (flowGenerator φ x) (flowGenerator φ x) < 0) :
    let A := {x : kerrNewmanSpacetime a | R < ksRadius a x.val}
    let g := kerrNewmanMetricField m a 0
    let T := kerrNewmanTimeDirection m a 0
    let D := domainOfOuterCommunications g T A
    D = (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a 0 ∧
      futureEventHorizon g T A =
        {x : kerrNewmanSpacetime a | ksRadius a x.val = kerrNewmanOuterRadius m a 0} ∧
      IsKerrNewmanDOC g (kerrNewmanFieldField a 0) D m a 0 := by
  let b := kerrNewmanOuterRadius m a 0
  let A := {x : kerrNewmanSpacetime a | R < ksRadius a x.val}
  let S := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a 0
  let g := kerrNewmanMetricField m a 0
  let T := kerrNewmanTimeDirection m a 0
  have hcut : 2*m ≤ R := by
    have h := (kerr_stationary_uniform_timelike_radius m a R 0 hp.1
      (by norm_num) φ hφ hsym).mp (by simpa using htime)
    simpa using h
  have hs : Real.sqrt (m^2-a^2-0^2) ≤ m :=
    Real.sqrt_le_iff.mpr ⟨hp.1.le,by nlinarith only [sq_nonneg a]⟩
  have hb : 0 < b := add_pos_of_pos_of_nonneg hp.1 (Real.sqrt_nonneg _)
  have hbR : b ≤ R := by
    change m+Real.sqrt (m^2-a^2-0^2) ≤ R
    linarith
  obtain ⟨hP,hF⟩ := radial_past_future m a R hp hbR
  have hD : domainOfOuterCommunications g T A = S := by
    unfold domainOfOuterCommunications
    rw [hP]
    exact inter_eq_right.mpr hF
  refine ⟨hD, ?_, ?_⟩
  · unfold futureEventHorizon
    rw [hP]
    exact (ksRadius_superlevel_frontier a b hb).1
  · rw [hD]
    exact standard_isometry m a 0 hp
