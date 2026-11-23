-- Prove2me | solution 1 for NoHair.kerrNewman_chronology_at_infinity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:38:06.114252+00:00
-- url     : https://prove2.me/submissions/780e0309-29d3-44dd-9547-a771ace85315

import Theorems.Thm_NoHair_chronology_at_infinity_cofinal
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

private theorem radial_bounds (a : ℝ) (x : kerrNewmanSpacetime a) :
    ksRadius a x.val ≤ spatialRadius x.val ∧ spatialRadius x.val ≤ ksRadius a x.val + |a| := by
  let r := ksRadius a x.val
  let k := ksNull a x.val
  have hr : 0 < r := x.property
  have hunit : k 1 ^ 2 + k 2 ^ 2 + k 3 ^ 2 = 1 := ks_rel a x.val hr
  have hcart : spatialRadius x.val ^ 2 = x.val 1 ^ 2 + x.val 2 ^ 2 + x.val 3 ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [ks_x1 a x.val hr, ks_x2 a x.val hr, ks_x3 a x.val hr] at hcart
  change spatialRadius x.val ^ 2 = (r*k 1-a*k 2)^2 + (a*k 1+r*k 2)^2 + (r*k 3)^2 at hcart
  have hsq : spatialRadius x.val ^ 2 = r^2 + a^2 - (a*k 3)^2 := by
    linear_combination hcart + (r^2+a^2)*hunit
  have hk : 0 ≤ 1 - (k 3)^2 := by nlinarith only [hunit, sq_nonneg (k 1), sq_nonneg (k 2)]
  constructor
  · apply (sq_le_sq₀ hr.le (Real.sqrt_nonneg _)).mp
    change r^2 ≤ spatialRadius x.val ^ 2
    nlinarith only [hsq, mul_nonneg (sq_nonneg a) hk]
  · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg hr.le (abs_nonneg a))).mp
    change spatialRadius x.val ^ 2 ≤ (r+|a|)^2
    nlinarith only [hsq, sq_abs a, sq_nonneg (a*k 3), mul_nonneg hr.le (abs_nonneg a)]


theorem solution (m a e R₀ : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) :
    let g := kerrNewmanMetricField m a e
    let T := kerrNewmanTimeDirection m a e
    let A := fun R : ℝ => {x : kerrNewmanSpacetime a | R < ksRadius a x.val}
    let C := fun R : ℝ => (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' exteriorRegion R
    let D := (Subtype.val : kerrNewmanSpacetime a → E4) ⁻¹' kerrNewmanDOC m a e
    (∀ R, A R ⊆ C R ∧ C (R + |a|) ⊆ A R) ∧
    ∀ B : ℝ → Set (kerrNewmanSpacetime a), Antitone B →
      (∀ R, ∃ S, A S ⊆ B R) → (∀ R, ∃ S, B S ⊆ A R) →
      chronoPastAtInfinity g T B R₀ = D ∧
      domainOfOuterCommunicationsAtInfinity g T B R₀ = D ∧
      futureEventHorizonAtInfinity g T B R₀ =
        {x : kerrNewmanSpacetime a | ksRadius a x.val = kerrNewmanOuterRadius m a e} ∧
      IsKerrNewmanDOC g (kerrNewmanFieldField a e)
        (domainOfOuterCommunicationsAtInfinity g T B R₀) m a e := by
  let U := kerrNewmanSpacetime a
  let g := kerrNewmanMetricField m a e
  let T := kerrNewmanTimeDirection m a e
  let b := kerrNewmanOuterRadius m a e
  let A := fun R : ℝ => {x : U | R < ksRadius a x.val}
  let C := fun R : ℝ => (Subtype.val : U → E4) ⁻¹' exteriorRegion R
  let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
  have hb : 0 < b := add_pos_of_pos_of_nonneg hp.1 (Real.sqrt_nonneg _)
  have hA : Antitone A := by
    intro R S hRS x hx
    exact lt_of_le_of_lt hRS hx
  have hAC (R : ℝ) : A R ⊆ C R ∧ C (R + |a|) ⊆ A R := by
    constructor
    · intro x hx
      exact lt_of_lt_of_le hx (radial_bounds a x).1
    · intro x hx
      change R + |a| < spatialRadius x.val at hx
      change R < ksRadius a x.val
      linarith [(radial_bounds a x).2]
  have hPast : chronoPastAtInfinity g T A 0 = D := by
    ext x
    constructor
    · intro hx
      have hsignal : x ∈ chronoPastSet g T (A b) := hx b hb.le
      obtain ⟨z,hz,γ,hγ,h0,h1⟩ := mem_iUnion₂.mp hsignal
      change b < ksRadius a x.val
      by_contra! h
      have hend := (kerrNewman_outerHorizon_futureTrapped m a e hp).2 γ hγ
        (h0 ▸ h : ksRadius a (γ 0).val ≤ b)
      rw [h1] at hend
      exact (not_lt_of_ge hend) hz
    · intro hx R _
      have haccess := kerrNewman_exterior_timelikeAccess m a e hp (R + |a|)
      obtain ⟨z,hz,hγ⟩ := mem_iUnion₂.mp ((haccess hx).1)
      exact mem_iUnion₂.mpr ⟨z,(hAC R).2 hz,hγ⟩
  have hFuture : D ⊆ chronoFutureAtInfinity g T A 0 := by
    intro x hx R _
    have haccess := kerrNewman_exterior_timelikeAccess m a e hp (R + |a|)
    obtain ⟨z,hz,hγ⟩ := mem_iUnion₂.mp ((haccess hx).2)
    exact mem_iUnion₂.mpr ⟨z,(hAC R).2 hz,hγ⟩
  have hDomain : domainOfOuterCommunicationsAtInfinity g T A 0 = D := by
    rw [domainOfOuterCommunicationsAtInfinity,hPast]
    exact inter_eq_right.mpr hFuture
  have hHorizon : futureEventHorizonAtInfinity g T A 0 =
      {x : U | ksRadius a x.val = b} := by
    rw [futureEventHorizonAtInfinity,hPast]
    exact (ksRadius_superlevel_frontier a b hb).1
  refine ⟨hAC,?_⟩
  intro B hB hAB hBA
  obtain ⟨hP,_,hD,hH,_⟩ := chronology_at_infinity_cofinal g T B A R₀ 0 hB hA hAB hBA
  have hExterior : domainOfOuterCommunicationsAtInfinity g T B R₀ = D := hD.trans hDomain
  refine ⟨hP.trans hPast,hExterior,hH.trans hHorizon,?_⟩
  rw [hExterior]
  exact standard_isometry m a e hp
