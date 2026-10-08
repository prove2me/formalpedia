-- Prove2me | solution 1 for Kakutani1941.FixedPoint.kakutani_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-08T02:30:02.521151+00:00
-- url     : https://prove2.me/submissions/ed077460-16ce-4cc1-8af8-efd98b2a9a91

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me 982fe7f0-c22a-4da7-a4a3-fdfdcdc6013a.
-- Complete Kakutani proof via finite continuous approximations; full accepted Brouwer proof attributed in place.
import Definitions.Def_Kakutani1941_FixedPoint_ClosedConvexSubset
import Definitions.Def_Kakutani1941_FixedPoint_UpperSemicontinuous
import Mathlib
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false


-- BEGIN MODULE AttributedBrouwer
section
-- Prove2me | solution 1 for AGT.brouwer_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T00:04:33.239295+00:00
-- url     : https://prove2.me/submissions/bea51b77-73ac-4067-ac0a-2358d27236f9

/-
  A self-contained proof of Brouwer's fixed-point theorem (Milnor's analytic proof),
  submitted for the Prove2me theorem `AGT.brouwer_fixed_point`.
-/

set_option autoImplicit false


/-!
# No `C¹` retraction of the closed unit ball onto its boundary sphere

This is the analytic core of Brouwer's fixed-point theorem, following Milnor's
proof.  Let `r` be a continuously differentiable map, defined on a neighbourhood
`U` of the closed unit ball `B` of a finite-dimensional real inner product
space, which sends `B` into the unit sphere and fixes the sphere pointwise.  Put
`h = r - id` (which vanishes on the sphere) and `g t = id + t • h`.

* For small `t > 0` the map `g t` is an injective self-map of `B` whose image
  contains the open unit ball, so `μ (g t '' B) = μ B`; by the change of
  variables formula, `∫ x in B, det (D (g t) x) = μ B`.
* The left-hand side is a polynomial in `t`, hence the identity persists at
  `t = 1`, where `g 1 = r` has singular derivative everywhere on the open ball
  (its values lie on the unit sphere), so the integral is `0 < μ B`.
-/

namespace BrouwerProof

open Metric MeasureTheory Set Filter

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The displacement `r - id`. -/
noncomputable def hmap (r : F → F) : F → F := fun x => r x - x

/-- The interpolation `id + t • (r - id)` between the identity and `r`. -/
noncomputable def gmap (r : F → F) (t : ℝ) : F → F := fun x => x + t • hmap r x

/-- The derivative of `gmap r t` at `x`. -/
noncomputable def Dg (r : F → F) (t : ℝ) (x : F) : F →L[ℝ] F :=
  ContinuousLinearMap.id ℝ F + t • fderiv ℝ (hmap r) x

variable {U : Set F} {r : F → F}

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem hmap_contDiffOn (hr : ContDiffOn ℝ 1 r U) : ContDiffOn ℝ 1 (hmap r) U :=
  hr.sub contDiffOn_id

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem hasFDerivAt_hmap (hU : IsOpen U) (hr : ContDiffOn ℝ 1 r U) {x : F} (hx : x ∈ U) :
    HasFDerivAt (hmap r) (fderiv ℝ (hmap r) x) x := by
  have : DifferentiableAt ℝ (hmap r) x :=
    ((hmap_contDiffOn hr).differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
  exact this.hasFDerivAt

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem hasFDerivAt_gmap (hU : IsOpen U) (hr : ContDiffOn ℝ 1 r U) {x : F} (hx : x ∈ U) (t : ℝ) :
    HasFDerivAt (gmap r t) (Dg r t x) x := by
  have h := (hasFDerivAt_hmap hU hr hx).const_smul t
  exact (hasFDerivAt_id x).add h

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem continuousOn_Dg (hU : IsOpen U) (hr : ContDiffOn ℝ 1 r U) (t : ℝ) :
    ContinuousOn (fun x => Dg r t x) U := by
  have := (hmap_contDiffOn hr).continuousOn_fderiv_of_isOpen hU le_rfl
  exact continuousOn_const.add (this.const_smul t)

omit [MeasurableSpace F] [BorelSpace F] in
/-- Positivity of `det (1 + t A)` for `t ‖A‖ < 1`. -/
theorem det_id_add_smul_pos (A : F →L[ℝ] F) {C t : ℝ} (hC : ‖A‖ ≤ C) (ht0 : 0 ≤ t)
    (htC : t * C < 1) : 0 < (ContinuousLinearMap.id ℝ F + t • A).det := by
  set φ : ℝ → ℝ := fun s => (ContinuousLinearMap.id ℝ F + s • A).det with hφ
  have hcont : Continuous φ :=
    ContinuousLinearMap.continuous_det.comp (by fun_prop)
  have hC0 : 0 ≤ C := le_trans (norm_nonneg A) hC
  have hne : ∀ s ∈ Icc (0 : ℝ) t, φ s ≠ 0 := by
    rintro s ⟨hs0, hst⟩ hzero
    have hsC : s * C < 1 := by nlinarith
    have hker : LinearMap.ker ((ContinuousLinearMap.id ℝ F + s • A) : F →ₗ[ℝ] F) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro v hv
      have hv' : v + s • A v = 0 := hv
      by_contra hv0
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      have hvv : v = -(s • A v) := by linear_combination (norm := module) hv'
      have h1 : ‖v‖ = ‖s • A v‖ := by
        have := congrArg norm hvv
        rwa [norm_neg] at this
      have h2 : ‖s • A v‖ ≤ s * C * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0]
        have hA := A.le_opNorm v
        calc s * ‖A v‖ ≤ s * (‖A‖ * ‖v‖) := mul_le_mul_of_nonneg_left hA hs0
          _ ≤ s * (C * ‖v‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC (norm_nonneg v)) hs0
          _ = s * C * ‖v‖ := by ring
      nlinarith
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) hker
  have h0 : φ 0 = 1 := by simp [hφ, ContinuousLinearMap.det]
  by_contra hcon
  push Not at hcon
  have hmem : (0 : ℝ) ∈ Icc (φ t) (φ 0) := ⟨hcon, by rw [h0]; norm_num⟩
  obtain ⟨s, hs, hsz⟩ := intermediate_value_Icc' ht0 hcont.continuousOn hmem
  exact hne s hs hsz

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem gmap_eq (r : F → F) (t : ℝ) (x : F) : gmap r t x = (1 - t) • x + t • r x := by
  simp only [gmap, hmap]
  module

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem gmap_mapsTo (hnorm : ∀ x ∈ closedBall (0 : F) 1, ‖r x‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : MapsTo (gmap r t) (closedBall (0 : F) 1) (closedBall (0 : F) 1) := by
  intro x hx
  have hx1 : ‖x‖ ≤ 1 := by simpa [dist_eq_norm] using hx
  have hrx : ‖r x‖ = 1 := hnorm x hx
  rw [mem_closedBall, dist_zero_right, gmap_eq]
  calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
    _ = (1 - t) * ‖x‖ + t * ‖r x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), abs_of_nonneg ht0]
    _ ≤ 1 := by rw [hrx]; nlinarith

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem gmap_mapsTo_ball (hnorm : ∀ x ∈ closedBall (0 : F) 1, ‖r x‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : MapsTo (gmap r t) (ball (0 : F) 1) (ball (0 : F) 1) := by
  intro x hx
  have hx1 : ‖x‖ < 1 := by simpa [dist_eq_norm] using hx
  have hrx : ‖r x‖ = 1 := hnorm x (ball_subset_closedBall hx)
  rw [mem_ball, dist_zero_right, gmap_eq]
  calc ‖(1 - t) • x + t • r x‖ ≤ ‖(1 - t) • x‖ + ‖t • r x‖ := norm_add_le _ _
    _ = (1 - t) * ‖x‖ + t * ‖r x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), abs_of_nonneg ht0]
    _ < 1 := by rw [hrx]; nlinarith

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem gmap_injOn {C : NNReal} (hlip : LipschitzOnWith C (hmap r) (closedBall (0 : F) 1))
    {t : ℝ} (ht0 : 0 ≤ t) (htC : t * C < 1) : InjOn (gmap r t) (closedBall (0 : F) 1) := by
  intro x hx y hy hxy
  have hdist : dist (hmap r x) (hmap r y) ≤ C * dist x y := hlip.dist_le_mul x hx y hy
  have hkey : dist x y = t * dist (hmap r x) (hmap r y) := by
    have h1 : x - y = t • (hmap r y - hmap r x) := by
      have h0 : gmap r t x - gmap r t y = 0 := sub_eq_zero.mpr hxy
      simp only [gmap] at h0
      linear_combination (norm := module) h0
    rw [dist_eq_norm, dist_eq_norm, h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0,
      norm_sub_rev]
  have hd0 : (0:ℝ) ≤ dist x y := dist_nonneg
  have hdd : dist x y ≤ t * ((C : ℝ) * dist x y) := by
    calc dist x y = t * dist (hmap r x) (hmap r y) := hkey
      _ ≤ t * (C * dist x y) := mul_le_mul_of_nonneg_left hdist ht0
  have : dist x y = 0 := by nlinarith
  exact dist_eq_zero.mp this

omit [MeasurableSpace F] [BorelSpace F] in
/-- The image of the ball under `gmap r t` contains the open unit ball. -/
theorem ball_subset_gmap_image (hU : IsOpen U) (hBU : closedBall (0 : F) 1 ⊆ U)
    (hr : ContDiffOn ℝ 1 r U) (hnorm : ∀ x ∈ closedBall (0 : F) 1, ‖r x‖ = 1)
    (hid : ∀ x ∈ sphere (0 : F) 1, r x = x) {C : ℝ}
    (hA : ∀ x ∈ closedBall (0 : F) 1, ‖fderiv ℝ (hmap r) x‖ ≤ C) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (htC : t * C < 1) :
    ball (0 : F) 1 ⊆ gmap r t '' closedBall (0 : F) 1 := by
  set B : Set F := closedBall (0 : F) 1 with hB
  set S : Set F := gmap r t '' B with hS
  have hgcont : ContinuousOn (gmap r t) B := by
    have hrc : ContinuousOn r B := (hr.continuousOn).mono hBU
    have : ContinuousOn (fun x => x + t • (r x - x)) B := by
      exact continuousOn_id.add ((hrc.sub continuousOn_id).const_smul t)
    exact this
  have hScpt : IsCompact S := (isCompact_closedBall _ _).image_of_continuousOn hgcont
  have hSclosed : IsClosed S := hScpt.isClosed
  set A : Set F := S ∩ ball (0 : F) 1 with hA'
  -- `A` is nonempty
  have hAne : A.Nonempty := by
    refine ⟨gmap r t 0, ⟨0, by simp [hB], rfl⟩, ?_⟩
    exact gmap_mapsTo_ball hnorm ht0 ht1 (by simp)
  -- `A` is open
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨⟨x, hxB, rfl⟩, hyball⟩
    -- the preimage point is interior
    have hxball : x ∈ ball (0 : F) 1 := by
      rcases lt_or_eq_of_le (by simpa [hB, dist_eq_norm] using hxB : ‖x‖ ≤ 1) with h | h
      · simpa [mem_ball, dist_eq_norm] using h
      · exfalso
        have hxs : x ∈ sphere (0 : F) 1 := by simp [← h]
        have : gmap r t x = x := by
          rw [gmap, hmap, hid x hxs]
          simp
        rw [this] at hyball
        have : ‖x‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hyball
        rw [← h] at this
        exact lt_irrefl _ this
    have hxU : x ∈ U := hBU hxB
    -- the derivative at `x` is invertible
    have hdetpos : 0 < (Dg r t x).det := by
      rw [Dg]
      exact det_id_add_smul_pos _ (hA x hxB) ht0 htC
    have hker : LinearMap.ker ((Dg r t x : F →L[ℝ] F) : F →ₗ[ℝ] F) = ⊥ := by
      by_contra hk
      exact hdetpos.ne' (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
    have hinj : Function.Injective ((Dg r t x : F →L[ℝ] F) : F →ₗ[ℝ] F) :=
      LinearMap.ker_eq_bot.mp hker
    have hbij : Function.Bijective ((Dg r t x : F →L[ℝ] F) : F →ₗ[ℝ] F) :=
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
    set e : F ≃L[ℝ] F :=
      (LinearEquiv.ofBijective ((Dg r t x : F →L[ℝ] F) : F →ₗ[ℝ] F) hbij).toContinuousLinearEquiv
      with he
    have hecoe : (e : F →L[ℝ] F) = Dg r t x := by
      ext v
      rfl
    -- `gmap r t` is an open map near `x`
    have hstrict : HasStrictFDerivAt (gmap r t) (e : F →L[ℝ] F) x := by
      have hcda : ContDiffAt ℝ 1 (gmap r t) x := by
        have h1 : ContDiffAt ℝ 1 r x := (hr x hxU).contDiffAt (hU.mem_nhds hxU)
        have : ContDiffAt ℝ 1 (fun y => y + t • (r y - y)) x :=
          contDiffAt_id.add (((h1.sub contDiffAt_id)).const_smul t)
        exact this
      have hfd : fderiv ℝ (gmap r t) x = Dg r t x := (hasFDerivAt_gmap hU hr hxU t).fderiv
      have := hcda.hasStrictFDerivAt one_ne_zero
      rw [hfd, ← hecoe] at this
      exact this
    have hmapnhds : Filter.map (gmap r t) (nhds x) = nhds (gmap r t x) :=
      hstrict.map_nhds_eq_of_equiv
    have himg : gmap r t '' ball (0 : F) 1 ∈ nhds (gmap r t x) := by
      rw [← hmapnhds]
      exact Filter.image_mem_map (isOpen_ball.mem_nhds hxball)
    refine Filter.mem_of_superset himg ?_
    rintro z ⟨w, hw, rfl⟩
    exact ⟨⟨w, ball_subset_closedBall hw, rfl⟩, gmap_mapsTo_ball hnorm ht0 ht1 hw⟩
  -- connectedness of the ball finishes the proof
  have hconn : IsPreconnected (ball (0 : F) 1) := (convex_ball (0 : F) 1).isPreconnected
  by_contra hsub
  rw [Set.not_subset] at hsub
  obtain ⟨y, hyball, hyS⟩ := hsub
  have hcover : ball (0 : F) 1 ⊆ A ∪ Sᶜ := by
    intro z hz
    by_cases hzS : z ∈ S
    · exact Or.inl ⟨hzS, hz⟩
    · exact Or.inr hzS
  have h1 : (ball (0 : F) 1 ∩ A).Nonempty := by
    obtain ⟨a, ha⟩ := hAne
    exact ⟨a, ha.2, ha⟩
  have h2 : (ball (0 : F) 1 ∩ Sᶜ).Nonempty := ⟨y, hyball, hyS⟩
  obtain ⟨z, _, hz1, hz2⟩ := hconn A Sᶜ hAopen hSclosed.isOpen_compl hcover h1 h2
  exact hz2 hz1.1

/-- The change of variables formula: for small `t`, the integral of the Jacobian determinant of
`gmap r t` over the ball is the measure of the ball. -/
theorem integral_det_Dg [Nontrivial F] (hU : IsOpen U) (hBU : closedBall (0 : F) 1 ⊆ U)
    (hr : ContDiffOn ℝ 1 r U) (hnorm : ∀ x ∈ closedBall (0 : F) 1, ‖r x‖ = 1)
    (hid : ∀ x ∈ sphere (0 : F) 1, r x = x) {C : NNReal}
    (hlip : LipschitzOnWith C (hmap r) (closedBall (0 : F) 1))
    (hA : ∀ x ∈ closedBall (0 : F) 1, ‖fderiv ℝ (hmap r) x‖ ≤ C) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (htC : t * (C : ℝ) < 1) :
    ∫ x in closedBall (0 : F) 1, (Dg r t x).det ∂(Measure.addHaar : Measure F)
      = (Measure.addHaar (closedBall (0 : F) 1) : ENNReal).toReal := by
  set μ : Measure F := Measure.addHaar with hμ
  set B : Set F := closedBall (0 : F) 1 with hB
  have hmeas : MeasurableSet B := measurableSet_closedBall
  have hpos : ∀ x ∈ B, 0 < (Dg r t x).det := by
    intro x hx
    rw [Dg]
    exact det_id_add_smul_pos _ (hA x hx) ht0 htC
  have hderiv : ∀ x ∈ B, HasFDerivWithinAt (gmap r t) (Dg r t x) B x := fun x hx =>
    (hasFDerivAt_gmap hU hr (hBU hx) t).hasFDerivWithinAt
  have hinj : InjOn (gmap r t) B := gmap_injOn hlip ht0 htC
  have hchange := lintegral_abs_det_fderiv_eq_addHaar_image μ hmeas hderiv hinj
  -- the image of the ball has the same measure as the ball
  have himg : μ (gmap r t '' B) = μ B := by
    have h2 : gmap r t '' B ⊆ B := image_subset_iff.mpr (gmap_mapsTo hnorm ht0 ht1.le)
    have h1 : ball (0 : F) 1 ⊆ gmap r t '' B :=
      ball_subset_gmap_image hU hBU hr hnorm hid (fun x hx => hA x hx) ht0 ht1 htC
    refine le_antisymm (measure_mono h2) ?_
    calc μ B = μ (ball (0 : F) 1) := Measure.addHaar_closedBall_eq_addHaar_ball μ 0 1
      _ ≤ μ (gmap r t '' B) := measure_mono h1
  have habs : ∫⁻ x in B, ENNReal.ofReal |(Dg r t x).det| ∂μ
      = ∫⁻ x in B, ENNReal.ofReal ((Dg r t x).det) ∂μ := by
    apply setLIntegral_congr_fun hmeas
    intro x hx
    simp only [abs_of_pos (hpos x hx)]
  have hcontdet : ContinuousOn (fun x => (Dg r t x).det) B :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn (continuousOn_Dg hU hr t)).mono hBU
  have hmeasf : AEStronglyMeasurable (fun x => (Dg r t x).det) (μ.restrict B) :=
    hcontdet.aestronglyMeasurable hmeas
  have hnonneg : 0 ≤ᵐ[μ.restrict B] fun x => (Dg r t x).det :=
    (ae_restrict_iff' hmeas).mpr (Filter.Eventually.of_forall fun x hx => (hpos x hx).le)
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeasf, ← habs, hchange, himg]

/-- Expansion of `det (1 + t M)` as a polynomial in `t` with coefficients built from `M`. -/
theorem det_one_add_smul_expand {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    (1 + t • M).det = ∑ σ : Equiv.Perm (Fin n), ∑ S : Finset (Fin n),
      t ^ (Finset.univ \ S).card * ((Equiv.Perm.sign σ : ℝ) *
        ((∏ i ∈ S, (1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i)
          * ∏ i ∈ Finset.univ \ S, M (σ i) i)) := by
  classical
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hent : ∀ i, (1 + t • M) (σ i) i
      = (1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i + t * M (σ i) i := by
    intro i; simp
  rw [Finset.prod_congr rfl (fun i _ => hent i), Finset.prod_add, Finset.powerset_univ,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  ring

/-- The integral of the Jacobian determinant of `gmap r t` is a polynomial in `t`. -/
theorem exists_polynomial_integral_det (hU : IsOpen U) (hBU : closedBall (0 : F) 1 ⊆ U)
    (hr : ContDiffOn ℝ 1 r U) :
    ∃ P : Polynomial ℝ, ∀ t : ℝ,
      P.eval t = ∫ x in closedBall (0 : F) 1, (Dg r t x).det ∂(Measure.addHaar : Measure F) := by
  classical
  set μ : Measure F := Measure.addHaar with hμ
  set B : Set F := closedBall (0 : F) 1 with hB
  set n := Module.finrank ℝ F with hn
  set bas := Module.finBasis ℝ F with hbas
  set M : F → Matrix (Fin n) (Fin n) ℝ := fun x =>
    LinearMap.toMatrix bas bas ((fderiv ℝ (hmap r) x : F →ₗ[ℝ] F)) with hM
  -- the determinant, expanded
  have hdet : ∀ (t : ℝ) (x : F), (Dg r t x).det
      = ∑ σ : Equiv.Perm (Fin n), ∑ S : Finset (Fin n),
        t ^ (Finset.univ \ S).card * ((Equiv.Perm.sign σ : ℝ) *
          ((∏ i ∈ S, (1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i)
            * ∏ i ∈ Finset.univ \ S, M x (σ i) i)) := by
    intro t x
    have hmat : (Dg r t x).det = Matrix.det (1 + t • M x) := by
      rw [Dg, ContinuousLinearMap.det, ← LinearMap.det_toMatrix bas]
      congr 1
      have hco : ((ContinuousLinearMap.id ℝ F + t • fderiv ℝ (hmap r) x : F →L[ℝ] F) : F →ₗ[ℝ] F)
          = LinearMap.id + t • ((fderiv ℝ (hmap r) x : F →L[ℝ] F) : F →ₗ[ℝ] F) := by
        ext v; simp
      rw [hco, map_add, map_smul, LinearMap.toMatrix_id]
    rw [hmat, det_one_add_smul_expand]
  -- continuity of the coefficients
  have hMcont : ContinuousOn M U := by
    have hΦ : Continuous fun T : F →L[ℝ] F =>
        LinearMap.toMatrix bas bas ((T : F →ₗ[ℝ] F)) := by
      let Φ : (F →L[ℝ] F) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
        (LinearMap.toMatrix bas bas).toLinearMap.comp (ContinuousLinearMap.coeLM ℝ)
      exact Φ.continuous_of_finiteDimensional
    exact hΦ.comp_continuousOn ((hmap_contDiffOn hr).continuousOn_fderiv_of_isOpen hU le_rfl)
  set w : Equiv.Perm (Fin n) → Finset (Fin n) → F → ℝ := fun σ S x =>
    (Equiv.Perm.sign σ : ℝ) * ((∏ i ∈ S, (1 : Matrix (Fin n) (Fin n) ℝ) (σ i) i)
      * ∏ i ∈ Finset.univ \ S, M x (σ i) i) with hw
  have hwcont : ∀ σ S, ContinuousOn (w σ S) B := by
    intro σ S
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.mul continuousOn_const
    apply continuousOn_finsetProd
    intro i _
    have hent : Continuous fun m : Matrix (Fin n) (Fin n) ℝ => m (σ i) i := by
      fun_prop
    exact (hent.comp_continuousOn hMcont).mono hBU
  have hint : ∀ (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (t : ℝ),
      IntegrableOn (fun x => t ^ (Finset.univ \ S).card * w σ S x) B μ := by
    intro σ S t
    exact (continuousOn_const.mul (hwcont σ S)).integrableOn_compact (isCompact_closedBall _ _)
  refine ⟨∑ σ : Equiv.Perm (Fin n), ∑ S : Finset (Fin n),
    Polynomial.C (∫ x in B, w σ S x ∂μ) * Polynomial.X ^ (Finset.univ \ S).card, fun t => ?_⟩
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  have hrw : ∫ x in B, (Dg r t x).det ∂μ
      = ∫ x in B, ∑ σ : Equiv.Perm (Fin n), ∑ S : Finset (Fin n),
          t ^ (Finset.univ \ S).card * w σ S x ∂μ := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x _
    exact hdet t x
  rw [hrw, integral_finsetSum _ (fun σ _ => ?_)]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    rw [integral_finsetSum _ (fun S _ => hint σ S t)]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hc : ∫ a in B, t ^ (Finset.univ \ S).card * w σ S a ∂μ
        = t ^ (Finset.univ \ S).card * ∫ a in B, w σ S a ∂μ := integral_const_mul _ _
    rw [hc]
    ring
  · exact integrable_finsetSum _ (fun S _ => hint σ S t)

omit [MeasurableSpace F] [BorelSpace F] in
/-- A `C¹` map into the unit sphere has singular derivative at interior points. -/
theorem det_fderiv_eq_zero_of_norm_eq_one {V : Set F} (hV : IsOpen V)
    (hr : ∀ x ∈ V, DifferentiableAt ℝ r x) (hnorm : ∀ x ∈ V, ‖r x‖ = 1) {x : F} (hx : x ∈ V) :
    (fderiv ℝ r x).det = 0 := by
  have hdr : HasFDerivAt r (fderiv ℝ r x) x := (hr x hx).hasFDerivAt
  -- the derivative is orthogonal to `r x`
  have horth : ∀ v : F, inner ℝ (r x) (fderiv ℝ r x v) = 0 := by
    intro v
    have hq : HasFDerivAt (fun y => (inner ℝ (r y) (r y) : ℝ))
        ((fderivInnerCLM ℝ (r x, r x)).comp ((fderiv ℝ r x).prod (fderiv ℝ r x))) x :=
      HasFDerivAt.inner ℝ hdr hdr
    have hconst : (fun y => (inner ℝ (r y) (r y) : ℝ)) =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [hV.mem_nhds hx] with y hy
      rw [real_inner_self_eq_norm_sq, hnorm y hy]
      norm_num
    have hcst : HasFDerivAt (fun _ : F => (1 : ℝ)) (0 : F →L[ℝ] ℝ) x := hasFDerivAt_const _ _
    have hq0 : HasFDerivAt (fun y => (inner ℝ (r y) (r y) : ℝ)) (0 : F →L[ℝ] ℝ) x :=
      hconst.hasFDerivAt_iff.mpr hcst
    have heq := hq0.unique hq
    have happ := congrArg (fun T : F →L[ℝ] ℝ => T v) heq
    simp only [zero_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply] at happ
    have hsym : inner ℝ (fderiv ℝ r x v) (r x) = inner ℝ (r x) (fderiv ℝ r x v) :=
      real_inner_comm _ _
    linarith [happ, hsym]
  by_contra hdet
  have hker : LinearMap.ker ((fderiv ℝ r x) : F →ₗ[ℝ] F) = ⊥ := by
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  have hinj : Function.Injective ((fderiv ℝ r x) : F →ₗ[ℝ] F) := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective ((fderiv ℝ r x) : F →ₗ[ℝ] F) :=
    LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨v, hv⟩ := hsurj (r x)
  have hzero : (inner ℝ (r x) (r x) : ℝ) = 0 := by
    have := horth v
    rwa [show fderiv ℝ r x v = r x from hv] at this
  rw [real_inner_self_eq_norm_sq, hnorm x hx] at hzero
  norm_num at hzero

/-- There is no `C¹` retraction from the closed unit ball onto the unit sphere. -/
theorem no_retraction [Nontrivial F] {U : Set F} (hU : IsOpen U)
    (hBU : closedBall (0 : F) 1 ⊆ U) (r : F → F) (hr : ContDiffOn ℝ 1 r U)
    (hnorm : ∀ x ∈ closedBall (0 : F) 1, ‖r x‖ = 1)
    (hid : ∀ x ∈ sphere (0 : F) 1, r x = x) : False := by
  set μ : Measure F := Measure.addHaar with hμ
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ (hmap r) x := fun x hx =>
    ((hmap_contDiffOn hr).differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
  -- a Lipschitz bound for the displacement on the ball
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ x ∈ closedBall (0 : F) 1, ‖fderiv ℝ (hmap r) x‖ ≤ C₀ :=
    (isCompact_closedBall _ _).exists_bound_of_continuousOn
      (((hmap_contDiffOn hr).continuousOn_fderiv_of_isOpen hU le_rfl).mono hBU)
  set C : NNReal := ⟨max C₀ 0, le_max_right _ _⟩ with hC
  have hA : ∀ x ∈ closedBall (0 : F) 1, ‖fderiv ℝ (hmap r) x‖ ≤ (C : ℝ) := by
    intro x hx
    exact le_trans (hC₀ x hx) (le_max_left _ _)
  have hlip : LipschitzOnWith C (hmap r) (closedBall (0 : F) 1) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun x hx => hdiff x (hBU hx))
    · intro x hx
      rw [← NNReal.coe_le_coe]
      exact hA x hx
    · exact convex_closedBall _ _
  -- the polynomial
  obtain ⟨P, hP⟩ := exists_polynomial_integral_det hU hBU hr
  set m : ℝ := (μ (closedBall (0 : F) 1)).toReal with hm
  set t₀ : ℝ := min (1 / 2) (1 / (2 * ((C : ℝ) + 1))) with ht₀
  have hCpos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  have ht₀pos : 0 < t₀ := lt_min (by norm_num) (by positivity)
  have hroots : ∀ t ∈ Ioo (0 : ℝ) t₀, P.eval t = m := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1.le
    have ht1 : t < 1 := lt_of_lt_of_le ht.2 (le_trans (min_le_left _ _) (by norm_num))
    have htC : t * (C : ℝ) < 1 := by
      have h1 : t < 1 / (2 * ((C : ℝ) + 1)) := lt_of_lt_of_le ht.2 (min_le_right _ _)
      have h2 : (0 : ℝ) ≤ (C : ℝ) := C.coe_nonneg
      rw [lt_div_iff₀ (by positivity)] at h1
      nlinarith
    rw [hP t]
    exact integral_det_Dg hU hBU hr hnorm hid hlip hA ht0 ht1 htC
  -- a polynomial constant on an interval is constant
  have hPconst : P = Polynomial.C m := by
    have hinf : (Ioo (0 : ℝ) t₀).Infinite := Set.Ioo_infinite ht₀pos
    have hsub : Ioo (0 : ℝ) t₀ ⊆ {x | (P - Polynomial.C m).IsRoot x} := by
      intro t ht
      simp [Polynomial.IsRoot, hroots t ht]
    have : P - Polynomial.C m = 0 :=
      Polynomial.eq_zero_of_infinite_isRoot _ (hinf.mono hsub)
    exact sub_eq_zero.mp this
  -- the value at `t = 1`
  have hDg1 : ∀ x ∈ U, Dg r 1 x = fderiv ℝ r x := by
    intro x hx
    have hrd : DifferentiableAt ℝ r x :=
      (hr.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx)
    have hfd : fderiv ℝ (hmap r) x = fderiv ℝ r x - ContinuousLinearMap.id ℝ F := by
      exact (hrd.hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
    rw [Dg, hfd, one_smul]
    abel
  have hzero : ∀ x ∈ ball (0 : F) 1, (Dg r 1 x).det = 0 := by
    intro x hx
    rw [hDg1 x (hBU (ball_subset_closedBall hx))]
    refine det_fderiv_eq_zero_of_norm_eq_one isOpen_ball ?_ ?_ hx
    · intro y hy
      exact (hr.differentiableOn one_ne_zero).differentiableAt
        (hU.mem_nhds (hBU (ball_subset_closedBall hy)))
    · intro y hy
      exact hnorm y (ball_subset_closedBall hy)
  have hae : (closedBall (0 : F) 1 : Set F) =ᵐ[μ] ball (0 : F) 1 := by
    rw [ae_eq_set]
    constructor
    · rw [closedBall_sdiff_ball]
      exact Measure.addHaar_sphere _ _ _
    · simp [sdiff_eq_empty.mpr ball_subset_closedBall]
  have hval1 : P.eval 1 = 0 := by
    rw [hP 1, setIntegral_congr_set hae]
    rw [setIntegral_congr_fun measurableSet_ball hzero]
    simp
  -- but the polynomial is the constant `m > 0`
  have hmpos : 0 < m := by
    have h1 : 0 < μ (closedBall (0 : F) 1) :=
      lt_of_lt_of_le (measure_ball_pos μ 0 one_pos) (measure_mono ball_subset_closedBall)
    have h2 : μ (closedBall (0 : F) 1) ≠ ⊤ := (measure_closedBall_lt_top).ne
    rw [hm]
    exact ENNReal.toReal_pos h1.ne' h2
  rw [hPconst] at hval1
  simp at hval1
  linarith

end BrouwerProof


/-!
# Brouwer's fixed-point theorem for `C¹` self-maps of the closed unit ball

If a `C¹` self-map `g` of the closed unit ball had no fixed point, then sending
`x` to the point where the ray from `g x` through `x` meets the unit sphere
would be a `C¹` retraction of the ball onto the sphere, which
`BrouwerProof.no_retraction` forbids.
-/

namespace BrouwerProof

open Metric MeasureTheory Set Filter

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Brouwer's theorem for `C¹` self-maps of the closed unit ball. -/
theorem smooth_brouwer_ball (g : F → F) (hg : ContDiff ℝ 1 g)
    (hmap : MapsTo g (closedBall 0 1) (closedBall (0 : F) 1)) :
    ∃ x ∈ closedBall (0 : F) 1, g x = x := by
  by_contra hcon
  push Not at hcon
  rcases subsingleton_or_nontrivial F with hs | hnt
  · exact hcon 0 (by simp) (Subsingleton.elim _ _)
  -- the data of the ray construction
  set u : F → F := fun x => x - g x with hu
  set bb : F → ℝ := fun x => inner ℝ x (u x) with hbb
  set aa : F → ℝ := fun x => ‖u x‖ ^ 2 with haa
  set DD : F → ℝ := fun x => bb x ^ 2 + aa x * (1 - ‖x‖ ^ 2) with hDD
  set tt : F → ℝ := fun x => (-bb x + Real.sqrt (DD x)) / aa x with htt
  set r : F → F := fun x => x + tt x • u x with hr
  -- smoothness of the auxiliary functions
  have hucont : ContDiff ℝ 1 u := contDiff_id.sub hg
  have hbbc : ContDiff ℝ 1 bb := ContDiff.inner ℝ contDiff_id hucont
  have haac : ContDiff ℝ 1 aa := by
    have : ContDiff ℝ 1 (fun x => (inner ℝ (u x) (u x) : ℝ)) := ContDiff.inner ℝ hucont hucont
    simpa [haa, real_inner_self_eq_norm_sq] using this
  have hnormsq : ContDiff ℝ 1 (fun x : F => ‖x‖ ^ 2) := by
    have : ContDiff ℝ 1 (fun x : F => (inner ℝ x x : ℝ)) := ContDiff.inner ℝ contDiff_id contDiff_id
    simpa [real_inner_self_eq_norm_sq] using this
  have hDDc : ContDiff ℝ 1 DD := by
    apply ContDiff.add (hbbc.pow 2)
    exact haac.mul (contDiff_const.sub hnormsq)
  -- the open set on which the construction makes sense
  set O : Set F := {x | u x ≠ 0 ∧ 0 < DD x} with hO
  have hOopen : IsOpen O := by
    have h1 : IsOpen {x : F | u x ≠ 0} := isOpen_ne_fun hucont.continuous continuous_const
    have h2 : IsOpen {x : F | 0 < DD x} := isOpen_lt continuous_const hDDc.continuous
    simpa [hO, ofPred_and] using h1.inter h2
  -- basic facts on the closed unit ball
  have hball : ∀ x ∈ closedBall (0 : F) 1, ‖x‖ ≤ 1 := by
    intro x hx; simpa [dist_eq_norm] using hx
  have hune : ∀ x ∈ closedBall (0 : F) 1, u x ≠ 0 := by
    intro x hx h
    exact hcon x hx (by rw [hu] at h; simpa [sub_eq_zero, eq_comm] using h)
  have haapos : ∀ x ∈ closedBall (0 : F) 1, 0 < aa x := by
    intro x hx
    have := hune x hx
    simp only [haa]
    positivity
  have hbbnonneg : ∀ x ∈ closedBall (0 : F) 1, ‖x‖ = 1 → 0 < bb x := by
    intro x hx hx1
    have hgx : ‖g x‖ ≤ 1 := hball _ (hmap hx)
    have hb : bb x = ‖x‖ ^ 2 - inner ℝ x (g x) := by
      simp [hbb, hu, inner_sub_right]
    rw [hb, hx1]
    have hcs : inner ℝ x (g x) ≤ 1 := by
      calc (inner ℝ x (g x) : ℝ) ≤ ‖x‖ * ‖g x‖ := real_inner_le_norm _ _
        _ ≤ 1 := by rw [hx1]; linarith
    rcases lt_or_eq_of_le hcs with h | h
    · simpa using by linarith
    · exfalso
      have : ‖x - g x‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x (g x) + ‖g x‖ ^ 2 := by
        rw [← norm_sub_sq_real]
      rw [hx1, ← h] at this
      have hle : ‖x - g x‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg (g x)]
      have : x - g x = 0 := by
        have h0 : ‖x - g x‖ = 0 := by nlinarith [norm_nonneg (x - g x)]
        exact norm_eq_zero.mp h0
      exact hcon x hx (by simpa [sub_eq_zero, eq_comm] using this)
  have hDDpos : ∀ x ∈ closedBall (0 : F) 1, 0 < DD x := by
    intro x hx
    rcases lt_or_eq_of_le (hball x hx) with h | h
    · have h1 : 0 < aa x := haapos x hx
      have h2 : 0 < 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
      have : 0 ≤ bb x ^ 2 := sq_nonneg _
      simp only [hDD]
      nlinarith
    · have hb := hbbnonneg x hx h
      have hDx : DD x = bb x ^ 2 := by simp [hDD, h]
      rw [hDx]
      exact pow_pos hb 2
  have hBO : closedBall (0 : F) 1 ⊆ O := fun x hx => ⟨hune x hx, hDDpos x hx⟩
  -- `r` is `C¹` on `O`
  have hrC1 : ContDiffOn ℝ 1 r O := by
    intro x hx
    have hax : aa x ≠ 0 := by
      intro h
      have : u x = 0 := by
        have : ‖u x‖ ^ 2 = 0 := h
        have : ‖u x‖ = 0 := by nlinarith [norm_nonneg (u x)]
        exact norm_eq_zero.mp this
      exact hx.1 this
    have hsqrt : ContDiffAt ℝ 1 (fun y => Real.sqrt (DD y)) x :=
      (Real.contDiffAt_sqrt (ne_of_gt hx.2)).comp x hDDc.contDiffAt
    have htta : ContDiffAt ℝ 1 tt x :=
      ContDiffAt.div (((hbbc.contDiffAt).neg).add hsqrt) haac.contDiffAt hax
    have : ContDiffAt ℝ 1 r x := contDiffAt_id.add (htta.smul hucont.contDiffAt)
    exact this.contDiffWithinAt
  -- `r` maps the ball into the sphere
  have hnorm : ∀ x ∈ closedBall (0 : F) 1, ‖r x‖ = 1 := by
    intro x hx
    have ha : 0 < aa x := haapos x hx
    have hD : 0 < DD x := hDDpos x hx
    set s := Real.sqrt (DD x) with hs
    have hs2 : s ^ 2 = DD x := Real.sq_sqrt hD.le
    have hkey : ‖r x‖ ^ 2 = 1 := by
      have hexp : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * (tt x * bb x) + tt x ^ 2 * aa x := by
        rw [hr]
        simp only
        rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have htx : tt x = (-bb x + s) / aa x := by simp only [htt, hs]
      have hD' : DD x = bb x ^ 2 + aa x * (1 - ‖x‖ ^ 2) := by simp only [hDD]
      rw [hexp, htx]
      field_simp
      linear_combination hs2 + hD'
    have : ‖r x‖ = 1 := by
      nlinarith [norm_nonneg (r x)]
    exact this
  -- `r` fixes the sphere
  have hid : ∀ x ∈ sphere (0 : F) 1, r x = x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by simpa [dist_eq_norm] using hx
    have hxB : x ∈ closedBall (0 : F) 1 := by simp [mem_closedBall, dist_eq_norm, hx1]
    have hb := hbbnonneg x hxB hx1
    have hD : DD x = bb x ^ 2 := by simp [hDD, hx1]
    have : tt x = 0 := by
      simp only [htt]
      rw [hD, Real.sqrt_sq hb.le]
      simp
    rw [hr]
    simp [this]
  exact no_retraction hOopen hBO r hrC1 hnorm hid

end BrouwerProof


/-!
# Brouwer's fixed-point theorem for continuous self-maps of the closed unit ball

A continuous self-map of the ball with no fixed point moves every point by at
least some `ε > 0`; a smooth map uniformly close to it (slightly shrunk so
that it still maps the ball into itself) would then also be fixed-point free,
contradicting `BrouwerProof.smooth_brouwer_ball`.
-/

namespace BrouwerProof

open Metric MeasureTheory Set Filter

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The radial retraction of the whole space onto the closed unit ball. -/
noncomputable def radial (x : F) : F := (max 1 ‖x‖)⁻¹ • x

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem continuous_radial : Continuous (radial : F → F) := by
  unfold radial
  fun_prop (disch := intro x; positivity)

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem radial_mem (x : F) : radial x ∈ closedBall (0 : F) 1 := by
  have h1 : (1 : ℝ) ≤ max 1 ‖x‖ := le_max_left _ _
  have h2 : ‖x‖ ≤ max 1 ‖x‖ := le_max_right _ _
  have hpos : 0 < max 1 ‖x‖ := lt_of_lt_of_le one_pos h1
  simp only [mem_closedBall, dist_zero_right, radial, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hpos, inv_mul_eq_div]
  rw [div_le_one hpos]
  exact h2

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem radial_eq_self {x : F} (hx : x ∈ closedBall (0 : F) 1) : radial x = x := by
  have hx' : ‖x‖ ≤ 1 := by simpa [dist_eq_norm] using hx
  simp [radial, max_eq_left hx']

/-- Brouwer's theorem for continuous self-maps of the closed unit ball. -/
theorem brouwer_ball (f : F → F) (hf : ContinuousOn f (closedBall 0 1))
    (hmap : MapsTo f (closedBall 0 1) (closedBall (0 : F) 1)) :
    ∃ x ∈ closedBall (0 : F) 1, f x = x := by
  by_contra hcon
  push Not at hcon
  set B : Set F := closedBall (0 : F) 1 with hB
  have hBcpt : IsCompact B := isCompact_closedBall _ _
  -- the globally defined extension `f₁` of `f`
  set f₁ : F → F := fun x => f (radial x) with hf₁
  have hf₁cont : Continuous f₁ :=
    hf.comp_continuous continuous_radial radial_mem
  have hf₁eq : ∀ x ∈ B, f₁ x = f x := fun x hx => by
    simp only [hf₁, radial_eq_self hx]
  have hf₁map : ∀ x, f₁ x ∈ B := fun x => hmap (radial_mem x)
  -- the minimal displacement
  obtain ⟨x₀, hx₀B, hx₀⟩ := hBcpt.exists_isMinOn ⟨0, by simp [hB]⟩
    (by fun_prop : ContinuousOn (fun x => ‖f₁ x - x‖) B)
  set ε : ℝ := ‖f₁ x₀ - x₀‖ with hε
  have hεpos : 0 < ε := by
    rw [hε, norm_pos_iff, sub_ne_zero]
    rw [hf₁eq x₀ hx₀B]
    exact hcon x₀ hx₀B
  have hεmin : ∀ x ∈ B, ε ≤ ‖f₁ x - x‖ := fun x hx => hx₀ hx
  -- a smooth approximation of `f₁`
  have huc : UniformContinuousOn f₁ (closedBall (0 : F) 2) :=
    (isCompact_closedBall _ _).uniformContinuousOn_of_continuous hf₁cont.continuousOn
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 6) (by linarith)
  obtain ⟨g, hgsmooth, hg⟩ :=
    hf₁cont.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (ε := min ρ 1)
      (lt_min hρpos one_pos)
  have hgapprox : ∀ a ∈ B, dist (g a) (f₁ a) ≤ ε / 6 := by
    intro a ha
    refine hg a (ε / 6) (fun x hx => ?_)
    have hxa : dist x a < min ρ 1 := by simpa [dist_eq_norm] using hx
    have ha2 : a ∈ closedBall (0 : F) 2 := by
      have : ‖a‖ ≤ 1 := by simpa [hB, dist_eq_norm] using ha
      simp only [mem_closedBall, dist_zero_right]; linarith
    have hx2 : x ∈ closedBall (0 : F) 2 := by
      have h1 : ‖a‖ ≤ 1 := by simpa [hB, dist_eq_norm] using ha
      have h2 : dist x a < 1 := lt_of_lt_of_le hxa (min_le_right _ _)
      have : ‖x‖ ≤ ‖x - a‖ + ‖a‖ := by
        simpa using norm_add_le (x - a) a
      rw [← dist_eq_norm] at this
      simp only [mem_closedBall, dist_zero_right]
      linarith
    exact (hρ x hx2 a ha2 (lt_of_lt_of_le hxa (min_le_left _ _))).le
  -- shrink `g` so that it maps the ball into itself
  set δ : ℝ := ε / 6 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set g' : F → F := fun x => (1 + δ)⁻¹ • g x with hg'
  have h1δ : (0 : ℝ) < 1 + δ := by linarith
  have hgnorm : ∀ x ∈ B, ‖g x‖ ≤ 1 + δ := by
    intro x hx
    have h1 : ‖f₁ x‖ ≤ 1 := by simpa [hB, dist_eq_norm] using hf₁map x
    have h2 : ‖g x - f₁ x‖ ≤ δ := by simpa [dist_eq_norm] using hgapprox x hx
    calc ‖g x‖ = ‖(g x - f₁ x) + f₁ x‖ := by congr 1; abel
      _ ≤ ‖g x - f₁ x‖ + ‖f₁ x‖ := norm_add_le _ _
      _ ≤ δ + 1 := add_le_add h2 h1
      _ = 1 + δ := by ring
  have hg'map : MapsTo g' B B := by
    intro x hx
    have := hgnorm x hx
    simp only [hB, mem_closedBall, dist_zero_right, hg', norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos h1δ, inv_mul_eq_div]
    rw [div_le_one h1δ]
    exact this
  have hg'close : ∀ x ∈ B, ‖g' x - f₁ x‖ ≤ 2 * δ := by
    intro x hx
    have h2 : ‖g x - f₁ x‖ ≤ δ := by simpa [dist_eq_norm] using hgapprox x hx
    have h3 : ‖g' x - g x‖ ≤ δ := by
      have : g' x - g x = ((1 + δ)⁻¹ - 1) • g x := by rw [hg']; module
      rw [this, norm_smul]
      have habs : |(1 + δ)⁻¹ - 1| = δ / (1 + δ) := by
        have hrw : (1 + δ)⁻¹ - 1 = -(δ / (1 + δ)) := by field_simp; ring
        rw [hrw, abs_neg, abs_of_nonneg (by positivity)]
      rw [Real.norm_eq_abs, habs]
      calc δ / (1 + δ) * ‖g x‖ ≤ δ / (1 + δ) * (1 + δ) := by
            apply mul_le_mul_of_nonneg_left (hgnorm x hx) (by positivity)
        _ = δ := by field_simp
    calc ‖g' x - f₁ x‖ = ‖(g' x - g x) + (g x - f₁ x)‖ := by congr 1; abel
      _ ≤ ‖g' x - g x‖ + ‖g x - f₁ x‖ := norm_add_le _ _
      _ ≤ δ + δ := add_le_add h3 h2
      _ = 2 * δ := by ring
  have hg'smooth : ContDiff ℝ 1 g' := by
    apply ContDiff.const_smul
    exact hgsmooth.of_le (by exact_mod_cast le_top)
  obtain ⟨x, hxB, hxfix⟩ := smooth_brouwer_ball g' hg'smooth hg'map
  have h1 := hεmin x hxB
  have h2 := hg'close x hxB
  rw [hxfix] at h2
  have : ‖f₁ x - x‖ = ‖x - f₁ x‖ := norm_sub_rev _ _
  rw [hδ] at h2
  linarith [this ▸ h1]

end BrouwerProof


/-!
# Brouwer's fixed-point theorem on a compact convex set

The ball case is transported to an arbitrary nonempty compact convex subset `K`
of a finite-dimensional real normed space in two steps: first, in an inner
product space, by composing with the nearest-point projection onto `K` (which is
`1`-Lipschitz), and then, in a general finite-dimensional space, by transporting
along a linear homeomorphism onto a Euclidean space.
-/

namespace BrouwerProof

open Metric MeasureTheory Set Filter

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

open Classical in
/-- The nearest-point projection onto a set `K` (junk value `0` if no nearest point exists). -/
noncomputable def proj (K : Set F) (x : F) : F :=
  if h : ∃ y ∈ K, ∀ z ∈ K, ‖x - y‖ ≤ ‖x - z‖ then h.choose else 0

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem proj_spec {K : Set F} (hcpt : IsCompact K) (hne : K.Nonempty) (x : F) :
    proj K x ∈ K ∧ ∀ z ∈ K, ‖x - proj K x‖ ≤ ‖x - z‖ := by
  have hex : ∃ y ∈ K, ∀ z ∈ K, ‖x - y‖ ≤ ‖x - z‖ := by
    obtain ⟨y, hyK, hy⟩ := hcpt.exists_isMinOn hne (by fun_prop : ContinuousOn (fun z => ‖x - z‖) K)
    exact ⟨y, hyK, fun z hz => hy hz⟩
  rw [proj, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  exact ⟨h1, h2⟩

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem proj_mem {K : Set F} (hcpt : IsCompact K) (hne : K.Nonempty) (x : F) : proj K x ∈ K :=
  (proj_spec hcpt hne x).1

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem proj_eq_self {K : Set F} (hcpt : IsCompact K) (hne : K.Nonempty) {x : F} (hx : x ∈ K) :
    proj K x = x := by
  have h := (proj_spec hcpt hne x).2 x hx
  simp only [sub_self, norm_zero] at h
  have : ‖x - proj K x‖ = 0 := le_antisymm h (norm_nonneg _)
  rwa [norm_sub_eq_zero_iff, eq_comm] at this

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The variational characterisation of the nearest point in a convex set. -/
theorem inner_proj_le_zero {K : Set F} (hconv : Convex ℝ K) (hcpt : IsCompact K)
    (hne : K.Nonempty) (x : F) {z : F} (hz : z ∈ K) :
    inner ℝ (x - proj K x) (z - proj K x) ≤ 0 := by
  set y := proj K x with hy
  have hyK : y ∈ K := proj_mem hcpt hne x
  have hmin : ∀ w ∈ K, ‖x - y‖ ≤ ‖x - w‖ := (proj_spec hcpt hne x).2
  set c : ℝ := inner ℝ (x - y) (z - y) with hc
  set A : ℝ := ‖z - y‖ ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 2 * t * c ≤ t ^ 2 * A := by
    intro t ht0 ht1
    have hmem : y + t • (z - y) ∈ K := by
      have := hconv hyK hz (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1
      module
    have h := hmin _ hmem
    have hexp : ‖x - (y + t • (z - y))‖ ^ 2 = ‖x - y‖ ^ 2 - 2 * t * c + t ^ 2 * A := by
      have hrw : x - (y + t • (z - y)) = (x - y) - t • (z - y) := by abel
      rw [hrw, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, ← hc, ← hA]
      ring
    nlinarith [pow_le_pow_left₀ (norm_nonneg (x - y)) h 2]
  by_contra hcon
  push Not at hcon
  have hApos : 0 < A := by
    rcases hA0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hzy : z - y = 0 := by
        have : ‖z - y‖ = 0 := by nlinarith [norm_nonneg (z - y)]
        exact norm_eq_zero.mp this
      rw [hc, hzy, inner_zero_right] at hcon
      exact lt_irrefl 0 hcon
  set t : ℝ := min 1 (c / A) with ht
  have htpos : 0 < t := lt_min one_pos (div_pos hcon hApos)
  have htle : t ≤ 1 := min_le_left _ _
  have htA : t * A ≤ c := by
    have : t ≤ c / A := min_le_right _ _
    calc t * A ≤ (c / A) * A := by nlinarith
      _ = c := by field_simp
  have := key t htpos htle
  nlinarith

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
theorem lipschitz_proj {K : Set F} (hconv : Convex ℝ K) (hcpt : IsCompact K) (hne : K.Nonempty) :
    LipschitzWith 1 (proj K) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  set p := proj K x with hp
  set q := proj K y with hq
  have h1 : inner ℝ (x - p) (q - p) ≤ 0 := inner_proj_le_zero hconv hcpt hne x (proj_mem hcpt hne y)
  have h2 : inner ℝ (y - q) (p - q) ≤ 0 := inner_proj_le_zero hconv hcpt hne y (proj_mem hcpt hne x)
  have hident : inner ℝ (x - y) (p - q)
      = - inner ℝ (x - p) (q - p) - inner ℝ (y - q) (p - q) + ‖p - q‖ ^ 2 := by
    have e1 : x - y = (x - p) + (-(y - q)) + (p - q) := by abel
    have e2 : q - p = -(p - q) := by abel
    rw [e1, inner_add_left, inner_add_left, inner_neg_left, e2, inner_neg_right,
      real_inner_self_eq_norm_sq]
    ring
  have hkey : ‖p - q‖ ^ 2 ≤ inner ℝ (x - y) (p - q) := by rw [hident]; linarith
  have hcs : inner ℝ (x - y) (p - q) ≤ ‖x - y‖ * ‖p - q‖ := real_inner_le_norm _ _
  rcases eq_or_lt_of_le (norm_nonneg (p - q)) with h0 | h0
  · simp [dist_eq_norm, ← h0]
  · rw [dist_eq_norm, dist_eq_norm]
    have hsq : ‖p - q‖ * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖ := by nlinarith
    have := le_of_mul_le_mul_right (by linarith [hsq] : ‖p - q‖ * ‖p - q‖ ≤ ‖x - y‖ * ‖p - q‖) h0
    simpa using this

/-- Brouwer's fixed-point theorem in a finite-dimensional real inner product space. -/
theorem brouwer_inner {K : Set F} (hconv : Convex ℝ K) (hcpt : IsCompact K) (hne : K.Nonempty)
    (f : F → F) (hf : ContinuousOn f K) (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  obtain ⟨R, hR, hKR⟩ : ∃ R > 0, K ⊆ closedBall (0 : F) R := by
    obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall (0 : F)
    refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), hR.trans ?_⟩
    exact closedBall_subset_closedBall (le_max_left _ _)
  set G : F → F := fun x => R⁻¹ • f (proj K (R • x)) with hG
  have hprojcont : Continuous (proj K) := (lipschitz_proj hconv hcpt hne).continuous
  have hGcont : ContinuousOn G (closedBall (0 : F) 1) := by
    apply ContinuousOn.smul continuousOn_const
    apply ContinuousOn.comp (hf.mono (subset_refl K)) _ (fun x _ => proj_mem hcpt hne _)
    exact (hprojcont.comp (continuous_const.smul continuous_id)).continuousOn
  have hGmap : MapsTo G (closedBall 0 1) (closedBall (0 : F) 1) := by
    intro x _
    have hmem : f (proj K (R • x)) ∈ K := hfK (proj_mem hcpt hne _)
    have : ‖f (proj K (R • x))‖ ≤ R := by
      simpa [dist_eq_norm] using hKR hmem
    simp only [mem_closedBall, dist_zero_right, hG, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos hR]
    rw [inv_mul_le_iff₀ hR]
    simpa using this
  obtain ⟨x, hx, hfx⟩ := brouwer_ball G hGcont hGmap
  refine ⟨R • x, ?_, ?_⟩
  · have : R • x = f (proj K (R • x)) := by
      have := congrArg (fun z => R • z) hfx
      simp only [hG, smul_inv_smul₀ (ne_of_gt hR)] at this
      exact this.symm
    rw [this]
    exact hfK (proj_mem hcpt hne _)
  · have hxK : R • x = f (proj K (R • x)) := by
      have := congrArg (fun z => R • z) hfx
      simp only [hG, smul_inv_smul₀ (ne_of_gt hR)] at this
      exact this.symm
    have hmemK : R • x ∈ K := by rw [hxK]; exact hfK (proj_mem hcpt hne _)
    rw [proj_eq_self hcpt hne hmemK] at hxK
    exact hxK.symm

end InnerProduct

/-- **Brouwer's fixed-point theorem.** Every continuous self-map of a nonempty compact convex
subset of a finite-dimensional real normed space has a fixed point. -/
theorem brouwer_fixed_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKconv : Convex ℝ K) (hKcpt : IsCompact K)
    (hKne : K.Nonempty) (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  set L : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp) with hL
  set K' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := L '' K with hK'
  have hK'conv : Convex ℝ K' := by
    have := hKconv.linear_image L.toLinearEquiv.toLinearMap
    simpa [hK'] using this
  have hK'cpt : IsCompact K' := hKcpt.image L.continuous
  have hK'ne : K'.Nonempty := hKne.image _
  set g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
    := fun y => L (f (L.symm y)) with hg
  have hgcont : ContinuousOn g K' := by
    apply L.continuous.comp_continuousOn
    apply hf.comp (L.symm.continuous.continuousOn)
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hx
  have hgmap : Set.MapsTo g K' K' := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, hfK hx, by simp [hg]⟩
  obtain ⟨y, hy, hfy⟩ := brouwer_inner hK'conv hK'cpt hK'ne g hgcont hgmap
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨x, hx, ?_⟩
  have : L (f x) = L x := by simpa [hg] using hfy
  exact L.injective this

end BrouwerProof


/-- **Brouwer fixed-point theorem** -- the Prove2me target statement. -/
theorem AGT.brouwer_fixed_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E} (hKconv : Convex ℝ K) (hKcpt : IsCompact K)
    (hKne : K.Nonempty) (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x :=
  BrouwerProof.brouwer_fixed_point hKconv hKcpt hKne f hf hfK
end
-- END MODULE AttributedBrouwer

-- BEGIN MODULE ApproximateSelection
section
set_option autoImplicit false
namespace Kakutani1941.FixedPoint.Proof
open Set Metric Finset

lemma exists_approximate_fixed_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (S : Set E) (hSc : IsCompact S) (hSv : Convex ℝ S)
    (hSn : S.Nonempty) (Φ : E → Set E) (hsub : ∀ x ∈ S, Φ x ⊆ S)
    (hne : ∀ x ∈ S, (Φ x).Nonempty) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ S, ∀ (L : E →L[ℝ] ℝ) (c : ℝ),
      (∀ u ∈ S, dist u x < ε → ∀ v ∈ Φ u, L v ≤ c) → L x ≤ c := by
  classical
  obtain ⟨t,htS,htfin,htcover⟩ := hSc.finite_cover_balls hε
  let F : Finset E := htfin.toFinset
  have hFS : ∀ a ∈ F, a ∈ S := fun a ha => htS (htfin.mem_toFinset.mp ha)
  let ψ : E → E := fun a => if ha : a ∈ S then (hne a ha).choose else hSn.choose
  have hψ : ∀ a ∈ F, ψ a ∈ Φ a := by
    intro a ha
    dsimp [ψ]
    rw [dif_pos (hFS a ha)]
    exact (hne a (hFS a ha)).choose_spec
  let q : E → E → ℝ := fun a x => max (ε-dist x a) 0
  let D : E → ℝ := fun x => ∑ a ∈ F, q a x
  have hq : ∀ a x, 0 ≤ q a x := fun a x => le_max_right _ _
  have hD : ∀ x ∈ S, 0 < D x := by
    intro x hx
    obtain ⟨a,hat,hxa⟩ := Set.mem_iUnion₂.mp (htcover hx)
    have ha : a ∈ F := htfin.mem_toFinset.mpr hat
    have hpos : 0 < q a x := lt_max_of_lt_left (sub_pos.mpr hxa)
    exact hpos.trans_le (Finset.single_le_sum (fun b _ => hq b x) ha)
  let w : E → E → ℝ := fun a x => q a x / D x
  have hw : ∀ x ∈ S, ∀ a, 0 ≤ w a x := fun x hx a => div_nonneg (hq a x) (hD x hx).le
  have hsum : ∀ x ∈ S, ∑ a ∈ F, w a x = 1 := by
    intro x hx
    dsimp [w]
    rw [← Finset.sum_div]
    exact div_self (hD x hx).ne'
  let f : E → E := fun x => ∑ a ∈ F, w a x • ψ a
  have hqc : ∀ a, Continuous (q a) := by intro a; dsimp [q]; fun_prop
  have hDc : Continuous D := by dsimp [D]; fun_prop
  have hfc : ContinuousOn f S := by
    apply continuousOn_finsetSum
    intro a _
    exact ((hqc a).continuousOn.div hDc.continuousOn (fun x hx => (hD x hx).ne')).smul continuousOn_const
  have hfm : Set.MapsTo f S S := by
    intro x hx
    exact hSv.sum_mem (fun a _ => hw x hx a) (hsum x hx)
      (fun a ha => hsub a (hFS a ha) (hψ a ha))
  obtain ⟨x,hx,hfix⟩ := AGT.brouwer_fixed_point hSv hSc hSn f hfc hfm
  refine ⟨x,hx,?_⟩
  intro L c hlocal
  have hterm : ∀ a ∈ F, w a x * L (ψ a) ≤ w a x * c := by
    intro a ha
    by_cases hz : w a x = 0
    · simp [hz]
    · have hqne : q a x ≠ 0 := by
        intro hzero
        apply hz
        simp [w,hzero]
      have hdist : dist a x < ε := by
        by_contra hn
        have hle : ε-dist x a ≤ 0 := by rw [dist_comm x a]; linarith
        exact hqne (max_eq_right hle)
      exact mul_le_mul_of_nonneg_left (hlocal a (hFS a ha) hdist (ψ a) (hψ a ha)) (hw x hx a)
  have he : L x = ∑ a ∈ F, w a x * L (ψ a) := by
    conv_lhs => rw [← hfix]
    simp only [f,map_sum,map_smul,smul_eq_mul]
  rw [he]
  calc
    _ ≤ ∑ a ∈ F, w a x * c := Finset.sum_le_sum hterm
    _ = c := by rw [← Finset.sum_mul,hsum x hx,one_mul]
end Kakutani1941.FixedPoint.Proof
end
-- END MODULE ApproximateSelection

-- BEGIN MODULE LocalUpperBound
section

open Set Filter Topology Metric
namespace Kakutani1941.FixedPoint.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma graph_closed {S : Set E} (hS : IsClosed S) (Φ : E → Set E)
    (husc : IsUpperSemicontinuous S Φ) :
    IsClosed {p : E × E | p.1 ∈ S ∧ p.2 ∈ Φ p.1} := by
  apply IsSeqClosed.isClosed
  intro u p hu hup
  have hx : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp hup
  have hy : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) :=
    continuous_snd.continuousAt.tendsto.comp hup
  have hpS : p.1 ∈ S := hS.mem_of_tendsto hx (Eventually.of_forall (fun n => (hu n).1))
  exact ⟨hpS, husc (fun n => (u n).1) (fun n => (u n).2) p.1 p.2
    (fun n => (hu n).1) hpS hx (fun n => (hu n).2) hy⟩

lemma local_upper_bound {S : Set E} (hS : IsCompact S) (Φ : E → Set E)
    (hsub : ∀ x ∈ S, Φ x ⊆ S) (husc : IsUpperSemicontinuous S Φ)
    (g : E → ℝ) (hg : Continuous g) (x : E) (c : ℝ)
    (hxc : ∀ y ∈ Φ x, g y < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, dist s x < δ → ∀ y ∈ Φ s, g y < c := by
  let bad : Set (E × E) := {p | p.1 ∈ S ∧ p.2 ∈ Φ p.1} ∩ {p | c ≤ g p.2}
  have hbadclosed : IsClosed bad :=
    (graph_closed hS.isClosed Φ husc).inter
      (isClosed_le continuous_const (hg.comp continuous_snd))
  have hbadcompact : IsCompact bad := (hS.prod hS).of_isClosed_subset hbadclosed
    (fun p hp => ⟨hp.1.1, hsub p.1 hp.1.1 hp.1.2⟩)
  have himage : IsClosed (Prod.fst '' bad) := (hbadcompact.image continuous_fst).isClosed
  have hx : x ∈ (Prod.fst '' bad)ᶜ := by
    rintro ⟨p, hp, hpfirst⟩
    have hmem : p.2 ∈ Φ x := hpfirst ▸ hp.1.2
    exact (not_le_of_gt (hxc p.2 hmem)) hp.2
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp himage.isOpen_compl x hx
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsx y hy
  by_contra h
  have hp : (s, y) ∈ bad := ⟨⟨hs, hy⟩, le_of_not_gt h⟩
  exact (hball (mem_ball.mpr hsx)) ⟨(s, y), hp, rfl⟩

end Kakutani1941.FixedPoint.Proof
end
-- END MODULE LocalUpperBound

-- BEGIN MODULE ApproximationLimit
section

open Set Filter Topology Metric
namespace Kakutani1941.FixedPoint.Proof
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma fixed_point_of_approximations (S : Set E) (hS : IsCompact S) (Φ : E → Set E)
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (husc : IsUpperSemicontinuous S Φ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x ∈ S, ∀ (L : E →L[ℝ] ℝ) (c : ℝ),
      (∀ u ∈ S, dist u x < ε → ∀ v ∈ Φ u, L v ≤ c) → L x ≤ c) :
    ∃ x ∈ S, x ∈ Φ x := by
  choose x hx hprop using fun n : ℕ =>
    happrox (1 / ((n : ℝ) + 1)) (by positivity)
  obtain ⟨x₀, hx₀, φ, hφ, hlim⟩ := hS.tendsto_subseq hx
  refine ⟨x₀, hx₀, ?_⟩
  by_contra hnot
  obtain ⟨L, c, hsep, hcx⟩ := geometric_hahn_banach_closed_point
    (hΦ x₀ hx₀).2.2 (hΦ x₀ hx₀).2.1 hnot
  obtain ⟨δ, hδ, hlocal⟩ := local_upper_bound hS Φ (fun s hs => (hΦ s hs).1)
    husc L L.continuous x₀ c hsep
  have hnear : ∀ᶠ n in atTop, dist (x (φ n)) x₀ < δ / 2 := by
    exact hlim.eventually (ball_mem_nhds x₀ (half_pos hδ))
  have hepslim : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have heps : ∀ᶠ n in atTop, 1 / ((φ n : ℝ) + 1) < δ / 2 :=
    hepslim.eventually (gt_mem_nhds (half_pos hδ))
  have hle : ∀ᶠ n in atTop, L (x (φ n)) ≤ c := by
    filter_upwards [hnear, heps] with n hnx hnε
    apply hprop (φ n) L c
    intro u hu hun v hv
    have hux : dist u x₀ < δ := by
      have ht := dist_triangle u (x (φ n)) x₀
      linarith
    exact (hlocal u hu hux v hv).le
  have hfinal : L x₀ ≤ c := le_of_tendsto (L.continuous.continuousAt.tendsto.comp hlim) hle
  exact (not_le_of_gt hcx) hfinal

end Kakutani1941.FixedPoint.Proof
end
-- END MODULE ApproximationLimit

-- BEGIN MODULE FullKakutani
section

namespace Kakutani1941.FixedPoint

/-- Corollary, p. 458: Kakutani's theorem on a bounded closed convex set. -/
theorem kakutani_fixed_point {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hSbounded : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hSconvex : Convex ℝ S) (hSnonempty : S.Nonempty)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (hΦne : ∀ x ∈ S, (Φ x).Nonempty)
    (husc : IsUpperSemicontinuous S Φ) :
    ∃ x₀ ∈ S, x₀ ∈ Φ x₀ := by
  have hSc : IsCompact S := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hSclosed,hSbounded⟩
  exact Proof.fixed_point_of_approximations S hSc Φ hΦ husc
    (fun ε hε => Proof.exists_approximate_fixed_point S hSc hSconvex hSnonempty Φ
      (fun x hx => (hΦ x hx).1) hΦne ε hε)

end Kakutani1941.FixedPoint

end
-- END MODULE FullKakutani

-- BEGIN MODULE PublicSolution
section
open Kakutani1941.FixedPoint

theorem solution {m : ℕ} {S : Set (EuclideanSpace ℝ (Fin m))}
    (hSbounded : Bornology.IsBounded S) (hSclosed : IsClosed S)
    (hSconvex : Convex ℝ S) (hSnonempty : S.Nonempty)
    (Φ : EuclideanSpace ℝ (Fin m) → Set (EuclideanSpace ℝ (Fin m)))
    (hΦ : ∀ x ∈ S, IsClosedConvexSubset S (Φ x))
    (hΦne : ∀ x ∈ S, (Φ x).Nonempty)
    (husc : IsUpperSemicontinuous S Φ) :
    ∃ x₀ ∈ S, x₀ ∈ Φ x₀ := by
  exact Kakutani1941.FixedPoint.kakutani_fixed_point hSbounded hSclosed hSconvex hSnonempty Φ hΦ hΦne husc


end
-- END MODULE PublicSolution

#print axioms Kakutani1941.FixedPoint.kakutani_fixed_point
#print axioms solution
