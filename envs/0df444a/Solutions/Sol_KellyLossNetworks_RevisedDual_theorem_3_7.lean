-- Prove2me | solution 1 for KellyLossNetworks.RevisedDual.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-08T02:15:29.149358+00:00
-- url     : https://prove2.me/submissions/94d28215-e977-48f5-8010-5c43a6c835b9

-- SPDX-License-Identifier: Apache-2.0
-- Complete proof of Prove2Me bca6fcfa-05d6-4c6a-ab11-e038b4eb1be6.
-- Complete revised-dual proof; full accepted Brouwer and Erlang bodies are attributed in place.
import Definitions.Def_KellyLossNetworks_RevisedDual_Problem
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_LossNetwork
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

-- BEGIN MODULE AttributedErlang
section
-- Prove2me | solution 1 for KellyStochasticNetworks.erlang_fixed_point_unique
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T00:17:41.784747+00:00
-- url     : https://prove2.me/submissions/989ed90f-0e4b-4872-a983-071d6cbc621b


namespace KellyStochasticNetworks

open Finset

/-! ### Products of summable families over `Fin R → ℕ` -/

lemma sn3_hasSum_pi_prod (R : ℕ) : ∀ (f : Fin R → ℕ → ℝ) (a : Fin R → ℝ),
    (∀ i n, 0 ≤ f i n) → (∀ i, HasSum (f i) (a i)) →
    HasSum (fun n : Fin R → ℕ => ∏ i, f i (n i)) (∏ i, a i) := by
  induction R with
  | zero =>
    intro f a _ _
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact hasSum_single default (fun b hb => (hb (Subsingleton.elim b default)).elim)
  | succ R ih =>
    intro f a h0 ha
    set g : (Fin R → ℕ) → ℝ := fun n => ∏ i, f i.succ (n i) with hgdef
    have ih' : HasSum g (∏ i : Fin R, a i.succ) := ih (fun i : Fin R => f i.succ) (fun i : Fin R => a i.succ)
      (fun (i : Fin R) n => h0 _ _) (fun i : Fin R => ha _)
    have hf0 : ∀ n, 0 ≤ f 0 n := fun n => h0 0 n
    have hg0 : ∀ n, 0 ≤ g n := fun n => Finset.prod_nonneg fun i _ => h0 _ _
    have hsum : Summable fun x : ℕ × (Fin R → ℕ) => f 0 x.1 * g x.2 := by
      apply summable_mul_of_summable_norm
      · simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using (ha 0).summable
      · simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using ih'.summable
    have hm := HasSum.mul (ha 0) ih' hsum
    have hfun : (fun n : Fin (R + 1) → ℕ => ∏ i, f i (n i)) ∘ (Fin.consEquiv (fun _ => ℕ))
        = fun x : ℕ × (Fin R → ℕ) => f 0 x.1 * g x.2 := by
      funext x
      simp [Fin.consEquiv, Fin.prod_univ_succ, hgdef]
    rw [← (Fin.consEquiv (fun _ : Fin (R + 1) => ℕ)).hasSum_iff, hfun, Fin.prod_univ_succ]
    exact hm

/-! ### The immigration–death network: detailed balance of product weights -/

lemma sn3_Tout_Tin {R : ℕ} (k : Fin R) (n : Fin R → ℕ) : Tout k (Tin k n) = n := by
  funext i; unfold Tout Tin; split_ifs with h <;> simp_all

lemma sn3_Tin_Tout {R : ℕ} (k : Fin R) (m : Fin R → ℕ) (hm : 1 ≤ m k) : Tin k (Tout k m) = m := by
  funext i; unfold Tout Tin; split_ifs with h <;> simp_all

lemma sn3_rates {R : ℕ} (ν : Fin R → ℝ) (n m : Fin R → ℕ) :
    openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ)) n m
      = (∑ k, if m = Tin k n then ν k else 0) + ∑ j, if m = Tout j n then (n j : ℝ) else 0 := by
  unfold openMigrationRates closedMigrationRates
  simp only [zero_mul, ite_self, Finset.sum_const_zero, one_mul, zero_add]
  ring

lemma sn3_prod_update {R : ℕ} (g : Fin R → ℕ → ℝ) (n : Fin R → ℕ) (k : Fin R) :
    ∏ r, g r (Tin k n r) = g k (n k + 1) * ∏ r ∈ univ.erase k, g r (n r) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ k)]
  congr 1
  · simp [Tin]
  · apply Finset.prod_congr rfl
    intro r hr
    have : r ≠ k := Finset.ne_of_mem_erase hr
    simp [Tin, this]

lemma sn3_term {R : ℕ} (ν : Fin R → ℝ) (g : Fin R → ℕ → ℝ)
    (hg : ∀ r t, g r (t + 1) * ((t : ℝ) + 1) = g r t * ν r) (n m : Fin R → ℕ) (k : Fin R) :
    (∏ r, g r (n r)) * (if m = Tin k n then ν k else 0)
      = (∏ r, g r (m r)) * (if n = Tout k m then (m k : ℝ) else 0) := by
  by_cases h : m = Tin k n
  · subst h
    rw [if_pos rfl, if_pos (sn3_Tout_Tin k n).symm, sn3_prod_update]
    have e : (Tin k n k : ℝ) = (n k : ℝ) + 1 := by simp [Tin]
    rw [e, ← Finset.mul_prod_erase univ (fun r => g r (n r)) (mem_univ k)]
    have := hg k (n k)
    calc g k (n k) * (∏ r ∈ univ.erase k, g r (n r)) * ν k
        = (g k (n k) * ν k) * ∏ r ∈ univ.erase k, g r (n r) := by ring
      _ = (g k (n k + 1) * ((n k : ℝ) + 1)) * ∏ r ∈ univ.erase k, g r (n r) := by rw [this]
      _ = _ := by ring
  · rw [if_neg h]
    by_cases h2 : n = Tout k m
    · rw [if_pos h2]
      by_cases hmk : 1 ≤ m k
      · exact absurd (by rw [h2, sn3_Tin_Tout k m hmk]) h
      · have : m k = 0 := by omega
        simp [this]
    · rw [if_neg h2]; simp

lemma sn3_detailed {R : ℕ} (ν : Fin R → ℝ) (g : Fin R → ℕ → ℝ)
    (hg : ∀ r t, g r (t + 1) * ((t : ℝ) + 1) = g r t * ν r) :
    DetailedBalance (fun n : Fin R → ℕ => ∏ r, g r (n r))
      (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ))) := by
  intro n m
  simp only [sn3_rates, mul_add, Finset.mul_sum]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl; intro k _
    exact (sn3_term ν g hg m n k).symm
  · apply Finset.sum_congr rfl; intro k _
    exact sn3_term ν g hg n m k

lemma sn3_full_of_detailed {S : Type*} (π : S → ℝ) (q : S → S → ℝ) (h : DetailedBalance π q) :
    FullBalance π q := by
  intro j
  rw [← tsum_mul_left]
  congr 1; ext k; exact h j k

lemma sn3_hg (ν : ℝ) (c : ℝ) (t : ℕ) :
    c * (ν ^ (t + 1) / ((t + 1).factorial : ℝ)) * ((t : ℝ) + 1) = c * (ν ^ t / (t.factorial : ℝ)) * ν := by
  rw [Nat.factorial_succ]
  push_cast
  have : (t.factorial : ℝ) ≠ 0 := by positivity
  have : (t : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma sn3_lossWeight_detailed {R : ℕ} (ν : Fin R → ℝ) :
    DetailedBalance (fun n : Fin R → ℕ => lossWeight ν n)
      (openMigrationRates (fun _ _ => (0 : ℝ)) (fun _ => 1) ν (fun _ m => (m : ℝ))) := by
  have := sn3_detailed ν (fun r t => ν r ^ t / (t.factorial : ℝ)) (fun r t => by
    have := sn3_hg (ν r) 1 t; simpa using this)
  exact this

/-! ### Erlang's formula: bounds and strict monotonicity -/

/-- The denominator `∑_{k ≤ N} ν^k / k!`. -/
noncomputable def sn3S (N : ℕ) (ν : ℝ) : ℝ := ∑ k ∈ range (N + 1), ν ^ k / (k.factorial : ℝ)

lemma sn3_erlang_eq (ν : ℝ) (N : ℕ) : erlang ν N = (ν ^ N / (N.factorial : ℝ)) / sn3S N ν := rfl

lemma sn3_S_ge (N : ℕ) {ν : ℝ} (_hν : 0 ≤ ν) :
    ν ^ N / (N.factorial : ℝ) + ∑ k ∈ range N, ν ^ k / (k.factorial : ℝ) = sn3S N ν := by
  unfold sn3S; rw [sum_range_succ]; ring

lemma sn3_S_pos (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) : 1 ≤ sn3S N ν := by
  unfold sn3S
  rw [sum_range_succ']
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  have : 0 ≤ ∑ k ∈ range N, ν ^ (k + 1) / ((k + 1).factorial : ℝ) :=
    sum_nonneg (fun k _ => by positivity)
  linarith

lemma sn3_erlang_nonneg (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) : 0 ≤ erlang ν N := by
  rw [sn3_erlang_eq]
  have := sn3_S_pos N hν
  positivity

lemma sn3_erlang_lt_one (N : ℕ) (hN : 1 ≤ N) {ν : ℝ} (hν : 0 ≤ ν) : erlang ν N < 1 := by
  rw [sn3_erlang_eq, div_lt_one (by linarith [sn3_S_pos N hν]), ← sn3_S_ge N hν]
  have h1 : 1 ≤ ∑ k ∈ range N, ν ^ k / (k.factorial : ℝ) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rw [sum_range_succ']
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    have : 0 ≤ ∑ k ∈ range M, ν ^ (k + 1) / ((k + 1).factorial : ℝ) :=
      sum_nonneg (fun k _ => by positivity)
    linarith
  linarith

lemma sn3_pow_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {i k : ℕ} (hki : k ≤ i) :
    a ^ i * b ^ k ≤ b ^ i * a ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hki
  have h1 : a ^ d ≤ b ^ d := pow_le_pow_left₀ ha hab d
  have h2 : 0 ≤ a ^ k := pow_nonneg ha k
  have h3 : 0 ≤ b ^ k := pow_nonneg (le_trans ha hab) k
  calc a ^ (k + d) * b ^ k = (a ^ k * b ^ k) * a ^ d := by ring
    _ ≤ (a ^ k * b ^ k) * b ^ d := mul_le_mul_of_nonneg_left h1 (mul_nonneg h2 h3)
    _ = b ^ (k + d) * a ^ k := by ring

lemma sn3_erlang_strict (N : ℕ) (hN : 1 ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    erlang a N < erlang b N := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  rw [sn3_erlang_eq, sn3_erlang_eq,
    div_lt_div_iff₀ (by linarith [sn3_S_pos N ha]) (by linarith [sn3_S_pos N hb])]
  unfold sn3S
  rw [Finset.mul_sum, Finset.mul_sum, ← sub_neg, ← Finset.sum_sub_distrib]
  have key : ∀ k ∈ range (N + 1), a ^ N / (N.factorial : ℝ) * (b ^ k / (k.factorial : ℝ))
      - b ^ N / (N.factorial : ℝ) * (a ^ k / (k.factorial : ℝ))
      = (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial) := by
    intro k _; ring
  rw [Finset.sum_congr rfl key]
  have hle : ∀ k ∈ range (N + 1),
      (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial) ≤ 0 := by
    intro k hk
    have hk' : k ≤ N := by simp at hk; omega
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [sn3_pow_le ha (le_of_lt hab) hk'])
      (by positivity)
  have hlt : (a ^ N * b ^ 0 - b ^ N * a ^ 0) / ((N.factorial : ℝ) * (Nat.factorial 0 : ℕ)) < 0 := by
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one]
    apply div_neg_of_neg_of_pos _ (by positivity)
    have := pow_lt_pow_left₀ hab ha (by omega : N ≠ 0)
    linarith
  have h := Finset.sum_lt_sum (s := range (N + 1))
    (f := fun k => (a ^ N * b ^ k - b ^ N * a ^ k) / ((N.factorial : ℝ) * k.factorial))
    (g := fun _ => (0 : ℝ)) hle ⟨0, by simp, hlt⟩
  simp only [Finset.sum_const_zero] at h
  exact h

/-- The carried load `ν(1 − E(ν, N)) = ∑_{k ≤ N} k ν^k/k! / ∑_{k ≤ N} ν^k/k!`. -/
lemma sn3_carried_eq (N : ℕ) {ν : ℝ} (hν : 0 ≤ ν) :
    ν * (1 - erlang ν N)
      = (∑ k ∈ range (N + 1), (k : ℝ) * (ν ^ k / (k.factorial : ℝ))) / sn3S N ν := by
  have hS := sn3_S_pos N hν
  have hS0 : sn3S N ν ≠ 0 := by linarith
  rw [sn3_erlang_eq, eq_div_iff hS0]
  have e1 : ν * (1 - ν ^ N / (N.factorial : ℝ) / sn3S N ν) * sn3S N ν
      = ν * (sn3S N ν - ν ^ N / (N.factorial : ℝ)) := by field_simp
  rw [e1, ← sn3_S_ge N hν, sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.factorial_succ]
  push_cast
  have : (k.factorial : ℝ) ≠ 0 := by positivity
  have : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

lemma sn3_carried_strict (N : ℕ) (hN : 1 ≤ N) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    a * (1 - erlang a N) < b * (1 - erlang b N) := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha hab)
  rw [sn3_carried_eq N ha, sn3_carried_eq N hb,
    div_lt_div_iff₀ (by linarith [sn3_S_pos N ha]) (by linarith [sn3_S_pos N hb])]
  unfold sn3S
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_pos]
  set w : ℕ → ℝ → ℝ := fun k ν => ν ^ k / (k.factorial : ℝ) with hw
  set X : ℕ → ℕ → ℝ := fun i k => w i b * w k a - w i a * w k b with hX
  have hD1 : (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i b * w k a)
      - (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i a * w k b)
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * X i k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _
    simp only [hX]; ring
  have hD2 : ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * X i k
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), -((k : ℝ) * X i k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro k _
    simp only [hX]; ring
  have hterm : ∀ i k : ℕ, 0 ≤ ((i : ℝ) - k) * X i k := by
    intro i k
    simp only [hX, hw]
    have e : b ^ i / (i.factorial : ℝ) * (a ^ k / (k.factorial : ℝ))
        - a ^ i / (i.factorial : ℝ) * (b ^ k / (k.factorial : ℝ))
        = (b ^ i * a ^ k - a ^ i * b ^ k) / ((i.factorial : ℝ) * k.factorial) := by ring
    rw [e]
    rcases le_total k i with hki | hik
    · have hc : (k : ℝ) ≤ i := by exact_mod_cast hki
      apply mul_nonneg (by linarith)
      apply div_nonneg _ (by positivity)
      linarith [sn3_pow_le ha (le_of_lt hab) hki]
    · have hc : (i : ℝ) ≤ k := by exact_mod_cast hik
      apply mul_nonneg_of_nonpos_of_nonpos (by linarith)
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      linarith [sn3_pow_le ha (le_of_lt hab) hik]
  have h2D : 2 * ((∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i b * w k a)
      - (∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i a * w k b))
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((i : ℝ) - k) * X i k := by
    rw [hD1, two_mul]
    nth_rewrite 2 [hD2]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _
    ring
  have hpos : 0 < ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), ((i : ℝ) - k) * X i k := by
    apply Finset.sum_pos' (fun i _ => Finset.sum_nonneg (fun k _ => hterm i k))
    refine ⟨1, by simp; omega, ?_⟩
    apply Finset.sum_pos' (fun k _ => hterm 1 k)
    refine ⟨0, by simp, ?_⟩
    simp only [hX, hw]
    norm_num
    linarith
  have hconv : ∀ ν₁ ν₂ : ℝ, (∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1),
      (i : ℝ) * (ν₁ ^ i / (i.factorial : ℝ)) * (ν₂ ^ j / (j.factorial : ℝ)))
      = ∑ i ∈ range (N + 1), ∑ k ∈ range (N + 1), (i : ℝ) * w i ν₁ * w k ν₂ := fun _ _ => rfl
  rw [hconv b a, hconv a b]
  linarith

end KellyStochasticNetworks

open KellyStochasticNetworks

lemma sn3_load_nonneg {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ) (hν : ∀ r, 0 < ν r)
    (E : Fin J → ℝ) (hK : ∀ j, E j ∈ Set.Icc (0 : ℝ) 1) (j : Fin J) :
    0 ≤ ∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - E i) ^ (A i r) := by
  apply Finset.sum_nonneg; intro r _
  apply mul_nonneg (mul_nonneg (by positivity) (le_of_lt (hν r)))
  apply Finset.prod_nonneg; intro i _
  exact pow_nonneg (by linarith [(hK i).2]) _

lemma sn3_unique {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) (E E' : Fin J → ℝ)
    (hK : ∀ j, E j ∈ Set.Icc (0 : ℝ) 1) (hF : ErlangFixedPoint A ν C E)
    (hK' : ∀ j, E' j ∈ Set.Icc (0 : ℝ) 1) (hF' : ErlangFixedPoint A ν C E') : E = E' := by
  -- loads, reduced intensities, and the fact that no link is fully blocked
  set L : (Fin J → ℝ) → Fin J → ℝ := fun E j => ∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - E i) ^ (A i r)
    with hLdef
  have hρ0 : ∀ (E : Fin J → ℝ), (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) → ∀ j, 0 ≤ (1 - E j)⁻¹ * L E j := by
    intro E hK j
    exact mul_nonneg (inv_nonneg.2 (by linarith [(hK j).2])) (sn3_load_nonneg A ν hν E hK j)
  have hlt : ∀ (E : Fin J → ℝ), (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) → ErlangFixedPoint A ν C E →
      ∀ j, E j < 1 := by
    intro E hK hF j
    rw [hF j]; exact sn3_erlang_lt_one _ (hC j) (hρ0 E hK j)
  have hcar : ∀ (E : Fin J → ℝ), (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) → ErlangFixedPoint A ν C E →
      ∀ j, (1 - E j)⁻¹ * L E j * (1 - erlang ((1 - E j)⁻¹ * L E j) (C j)) = L E j := by
    intro E hK hF j
    rw [← hF j]
    have : 1 - E j ≠ 0 := by linarith [hlt E hK hF j]
    field_simp
  -- logarithmic coordinates
  set x : (Fin J → ℝ) → Fin J → ℝ := fun E j => -Real.log (1 - E j) with hx
  have hexp : ∀ (E : Fin J → ℝ), (∀ j, E j < 1) → ∀ j, Real.exp (-x E j) = 1 - E j := by
    intro E h j; simp only [hx, neg_neg]; exact Real.exp_log (by linarith [h j])
  have hprod : ∀ (E : Fin J → ℝ), (∀ j, E j < 1) → ∀ r,
      ∏ i, (1 - E i) ^ (A i r) = Real.exp (-∑ i, (A i r : ℝ) * x E i) := by
    intro E h r
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_congr rfl; intro i _
    rw [← hexp E h i, ← Real.exp_nat_mul]; congr 1; ring
  have hl := hlt E hK hF
  have hl' := hlt E' hK' hF'
  -- the per-link terms are nonnegative, and vanish only when the blocking agrees
  set T : Fin J → ℝ := fun j => (x E j - x E' j) * (L E j - L E' j) with hT
  have hTpos : ∀ j, E j ≠ E' j → 0 < T j := by
    intro j hne
    have hmono : ∀ a b : ℝ, 0 ≤ a → a ≤ b → erlang a (C j) ≤ erlang b (C j) := by
      intro a b ha hab
      rcases eq_or_lt_of_le hab with h | h
      · rw [h]
      · exact le_of_lt (sn3_erlang_strict _ (hC j) ha h)
    have key : ∀ (E E' : Fin J → ℝ), (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) → ErlangFixedPoint A ν C E →
        (∀ j, E' j ∈ Set.Icc (0 : ℝ) 1) → ErlangFixedPoint A ν C E' → E j < E' j →
        x E j < x E' j ∧ L E j < L E' j := by
      intro E E' hK hF hK' hF' hlt'
      have h1 := hlt E hK hF j
      have h2 := hlt E' hK' hF' j
      constructor
      · simp only [hx, neg_lt_neg_iff]
        exact Real.log_lt_log (by linarith) (by linarith)
      · have hρ : (1 - E j)⁻¹ * L E j < (1 - E' j)⁻¹ * L E' j := by
          by_contra hc
          push Not at hc
          have := hmono _ _ (hρ0 E' hK' j) hc
          rw [← hF j, ← hF' j] at this
          linarith
        rw [← hcar E hK hF j, ← hcar E' hK' hF' j]
        exact sn3_carried_strict _ (hC j) (hρ0 E hK j) hρ
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨h1, h2⟩ := key E E' hK hF hK' hF' h
      simp only [hT]; nlinarith
    · obtain ⟨h1, h2⟩ := key E' E hK' hF' hK hF h
      simp only [hT]; nlinarith
  have hTnn : ∀ j, 0 ≤ T j := by
    intro j
    by_cases h : E j = E' j
    · simp only [hT, hx, h, sub_self, zero_mul, le_refl]
    · exact le_of_lt (hTpos j h)
  -- the sum of the per-link terms is a sum over routes of nonpositive terms
  set s : (Fin J → ℝ) → Fin R → ℝ := fun E r => ∑ i, (A i r : ℝ) * x E i with hs
  have hLe : ∀ (E : Fin J → ℝ), (∀ j, E j < 1) → ∀ j,
      L E j = ∑ r, (A j r : ℝ) * ν r * Real.exp (-s E r) := by
    intro E h j
    simp only [hLdef, hs]
    apply Finset.sum_congr rfl; intro r _
    rw [hprod E h r]
  have hsum : ∑ j, T j = ∑ r, ν r * ((s E r - s E' r) *
      (Real.exp (-s E r) - Real.exp (-s E' r))) := by
    simp only [hT]
    rw [show (∑ j, (x E j - x E' j) * (L E j - L E' j))
        = ∑ j, ∑ r, (x E j - x E' j) * ((A j r : ℝ) * ν r *
            (Real.exp (-s E r) - Real.exp (-s E' r))) from by
      apply Finset.sum_congr rfl; intro j _
      rw [hLe E hl j, hLe E' hl' j, ← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _; ring]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro r _
    simp only [hs]
    rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  have hroute : ∀ r, ν r * ((s E r - s E' r) * (Real.exp (-s E r) - Real.exp (-s E' r))) ≤ 0 := by
    intro r
    apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hν r))
    rcases le_total (s E r) (s E' r) with h | h
    · have := Real.exp_le_exp.2 (neg_le_neg h)
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    · have := Real.exp_le_exp.2 (neg_le_neg h)
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hle0 : ∑ j, T j ≤ 0 := by
    rw [hsum]; exact Finset.sum_nonpos (fun r _ => hroute r)
  have hzero : ∀ j ∈ Finset.univ, T j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hTnn j)).1
      (le_antisymm hle0 (Finset.sum_nonneg (fun j _ => hTnn j)))
  funext j
  by_contra hne
  have := hTpos j hne
  rw [hzero j (Finset.mem_univ j)] at this
  exact lt_irrefl _ this

lemma sn3_exists {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃ E : Fin J → ℝ, (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ ErlangFixedPoint A ν C E := by
  set ρt : (Fin J → ℝ) → Fin J → ℝ := fun E j => ∑ r, (A j r : ℝ) * ν r *
    ((1 - E j) ^ (A j r - 1) * ∏ i ∈ Finset.univ.erase j, (1 - E i) ^ (A i r)) with hρt
  set F : (Fin J → ℝ) → (Fin J → ℝ) := fun E j => erlang (ρt E j) (C j) with hF
  set K : Set (Fin J → ℝ) := Set.Icc 0 1 with hK
  have hmemK : ∀ E, E ∈ K ↔ ∀ j, E j ∈ Set.Icc (0 : ℝ) 1 := by
    intro E
    simp only [hK, Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply]
    exact ⟨fun h j => ⟨h.1 j, h.2 j⟩, fun h => ⟨fun j => (h j).1, fun j => (h j).2⟩⟩
  have hρt0 : ∀ E ∈ K, ∀ j, 0 ≤ ρt E j := by
    intro E hE j
    have h := (hmemK E).1 hE
    apply Finset.sum_nonneg; intro r _
    apply mul_nonneg (mul_nonneg (by positivity) (le_of_lt (hν r)))
    apply mul_nonneg (pow_nonneg (by linarith [(h j).2]) _)
    apply Finset.prod_nonneg; intro i _
    exact pow_nonneg (by linarith [(h i).2]) _
  have hρc : ∀ j, Continuous fun E : Fin J → ℝ => ρt E j := by
    intro j
    simp only [hρt]
    fun_prop
  have hcont : ContinuousOn F K := by
    apply continuousOn_pi.2; intro j
    simp only [hF, erlang]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro E hE
    have := sn3_S_pos (C j) (hρt0 E hE j)
    unfold sn3S at this
    linarith
  have hmaps : Set.MapsTo F K K := by
    intro E hE
    exact (hmemK _).2 fun j => ⟨sn3_erlang_nonneg _ (hρt0 E hE j),
      le_of_lt (sn3_erlang_lt_one _ (hC j) (hρt0 E hE j))⟩
  have hne : K.Nonempty := ⟨0, (hmemK 0).2 fun j => by simp⟩
  obtain ⟨E, hE, hfix⟩ := AGT.brouwer_fixed_point (convex_Icc 0 1) isCompact_Icc hne F hcont hmaps
  refine ⟨E, (hmemK E).1 hE, fun j => ?_⟩
  have h1 : E j = erlang (ρt E j) (C j) := (congrFun hfix j).symm
  have hlt : E j < 1 := by rw [h1]; exact sn3_erlang_lt_one _ (hC j) (hρt0 E hE j)
  have hne1 : (1 - E j) ≠ 0 := by linarith
  have hρ : ρt E j = (1 - E j)⁻¹ * ∑ r, (A j r : ℝ) * ν r * ∏ i, (1 - E i) ^ (A i r) := by
    simp only [hρt]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (1 - E i) ^ (A i r)) (Finset.mem_univ j)]
    rcases Nat.eq_zero_or_pos (A j r) with h0 | hpos
    · simp [h0]
    · obtain ⟨a, ha⟩ : ∃ a, A j r = a + 1 := ⟨A j r - 1, by omega⟩
      rw [ha, Nat.add_sub_cancel, pow_succ]
      field_simp
  conv_lhs => rw [h1]
  rw [hρ]

theorem KellyStochasticNetworks.erlang_fixed_point_unique {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃! E : Fin J → ℝ, (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ ErlangFixedPoint A ν C E := by
  obtain ⟨E, hEK, hEfix⟩ := sn3_exists A ν C hν hC
  exact ⟨E, ⟨hEK, hEfix⟩, fun E' hE' => sn3_unique A ν C hν hC E' E hE'.1 hE'.2 hEK hEfix⟩
end
-- END MODULE AttributedErlang

-- BEGIN MODULE ScalarInverse
section

open Set Finset
open KellyStochasticNetworks
namespace KellyLossNetworks.RevisedDual.Proof

lemma carried_le_capacity (C : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    v * (1 - erlang v C) ≤ C := by
  rw [sn3_carried_eq C hv]
  apply (div_le_iff₀ (by linarith [sn3_S_pos C hv])).mpr
  rw [sn3S, mul_sum]
  apply sum_le_sum
  intro k hk
  have hkC : k ≤ C := Nat.le_of_lt_succ (mem_range.mp hk)
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkC) (by positivity)

lemma erlang_continuousOn (C : ℕ) : ContinuousOn (fun v : ℝ => erlang v C) (Ici 0) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro v hv
    have hp := sn3_S_pos C hv
    change sn3S C v ≠ 0
    linarith

lemma erlang_zero (C : ℕ) (hC : 1 ≤ C) : erlang 0 C = 0 := by
  simp [erlang, zero_pow (by omega : C ≠ 0)]

lemma exists_erlang_inverse (C : ℕ) (hC : 1 ≤ C) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) : ∃ v : ℝ, 0 ≤ v ∧ erlang v C = p := by
  let v : ℝ := (C : ℝ) / (1 - p) + 1
  have hd : 0 < 1 - p := sub_pos.mpr hp1
  have hv : 0 < v := by dsimp [v]; positivity
  have hvc : (C : ℝ) < v * (1 - p) := by
    dsimp [v]
    rw [add_mul, div_mul_cancel₀ _ hd.ne']
    linarith
  have hc := carried_le_capacity C hv.le
  have hpv : p < erlang v C := by nlinarith
  have hcont := (erlang_continuousOn C).mono (Icc_subset_Ici_self : Icc 0 v ⊆ Ici 0)
  obtain ⟨w, hw, he⟩ := intermediate_value_Icc hv.le hcont
    (show p ∈ Icc (erlang 0 C) (erlang v C) by rw [erlang_zero C hC]; exact ⟨hp0, hpv.le⟩)
  exact ⟨w, hw.1, he⟩

lemma exists_load_coordinate (C : ℕ) (hC : 1 ≤ C) {y : ℝ} (hy : 0 ≤ y) :
    ∃ v : ℝ, 0 ≤ v ∧ -Real.log (1 - erlang v C) = y := by
  have he0 := Real.exp_pos (-y)
  have he1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨v, hv, hvp⟩ := exists_erlang_inverse C hC
    (show 0 ≤ 1 - Real.exp (-y) by linarith)
    (show 1 - Real.exp (-y) < 1 by linarith)
  refine ⟨v, hv, ?_⟩
  rw [hvp, sub_sub_cancel, Real.log_exp, neg_neg]

lemma load_coordinate_injective (C : ℕ) (hC : 1 ≤ C) {v w : ℝ}
    (hv : 0 ≤ v) (hw : 0 ≤ w)
    (he : -Real.log (1 - erlang v C) = -Real.log (1 - erlang w C)) : v = w := by
  have hev := sn3_erlang_lt_one C hC hv
  have hew := sn3_erlang_lt_one C hC hw
  have hl : Real.log (1 - erlang v C) = Real.log (1 - erlang w C) := by linarith
  have harg := Real.log_injOn_pos (sub_pos.mpr hev) (sub_pos.mpr hew) hl
  have heq : erlang v C = erlang w C := by linarith
  rcases lt_trichotomy v w with hlt | hequal | hgt
  · have := sn3_erlang_strict C hC hv hlt; linarith
  · exact hequal
  · have := sn3_erlang_strict C hC hw hgt; linarith

end KellyLossNetworks.RevisedDual.Proof
end
-- END MODULE ScalarInverse

-- BEGIN MODULE PrimitiveTangent
section

open MeasureTheory Set
namespace KellyLossNetworks.RevisedDual.Proof

lemma primitive_intervalIntegrable (u : ℝ → ℝ)
    (hu : MonotoneOn u (Ici 0)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable u volume a b := by
  apply MonotoneOn.intervalIntegrable
  apply hu.mono
  intro x hx
  exact (le_min ha hb).trans hx.1

lemma primitive_strict_tangent (u : ℝ → ℝ)
    (hu : StrictMonoOn u (Ici 0)) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hne : z ≠ y) :
    u y * (z - y) < (∫ t in (0 : ℝ)..z, u t) - ∫ t in (0 : ℝ)..y, u t := by
  have h0y := primitive_intervalIntegrable u hu.monotoneOn (le_refl 0) hy
  have hyz := primitive_intervalIntegrable u hu.monotoneOn hy hz
  have hsum := intervalIntegral.integral_add_adjacent_intervals h0y hyz
  rcases lt_or_gt_of_ne hne with hzy | hyzlt
  · have hpos : 0 < ∫ t in z..y, (u y - u t) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
        (intervalIntegrable_const.sub hyz.symm) _ hzy
      intro t ht
      exact sub_pos.mpr (hu (le_trans hz ht.1.le) hy ht.2)
    rw [intervalIntegral.integral_sub intervalIntegrable_const hyz.symm,
      intervalIntegral.integral_const] at hpos
    have hrev := intervalIntegral.integral_symm (f := u) (μ := volume) y z
    simp only [smul_eq_mul] at hpos
    linarith
  · have hpos : 0 < ∫ t in y..z, (u t - u y) := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
        (hyz.sub intervalIntegrable_const) _ hyzlt
      intro t ht
      exact sub_pos.mpr (hu hy (le_trans hy ht.1.le) ht.1)
    rw [intervalIntegral.integral_sub hyz intervalIntegrable_const,
      intervalIntegral.integral_const] at hpos
    simp only [smul_eq_mul] at hpos
    linarith

lemma primitive_tangent (u : ℝ → ℝ)
    (hu : StrictMonoOn u (Ici 0)) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    u y * (z - y) ≤ (∫ t in (0 : ℝ)..z, u t) - ∫ t in (0 : ℝ)..y, u t := by
  by_cases h : z = y
  · simp [h]
  · exact (primitive_strict_tangent u hu hy hz h).le

end KellyLossNetworks.RevisedDual.Proof
end
-- END MODULE PrimitiveTangent

-- BEGIN MODULE Utilization
section

open Set
open KellyStochasticNetworks
namespace KellyLossNetworks.RevisedDual.Proof

lemma utilization_coordinate (C : ℕ) (hC : 1 ≤ C) {v : ℝ} (hv : 0 ≤ v) :
    U (-Real.log (1 - erlang v C)) C = v * (1 - erlang v C) := by
  have hex : ∃ w : ℝ, 0 ≤ w ∧ -Real.log (1 - erlang w C) =
      -Real.log (1 - erlang v C) := ⟨v, hv, rfl⟩
  rw [U, dif_pos hex]
  have heq : hex.choose = v := load_coordinate_injective C hC hex.choose_spec.1 hv
    hex.choose_spec.2
  rw [heq]

lemma load_coordinate_strictMono (C : ℕ) (hC : 1 ≤ C) :
    StrictMonoOn (fun v : ℝ => -Real.log (1 - erlang v C)) (Ici 0) := by
  intro v hv w hw hvw
  have he := sn3_erlang_strict C hC hv hvw
  have hw1 := sn3_erlang_lt_one C hC hw
  exact neg_lt_neg (Real.log_lt_log (sub_pos.mpr hw1) (by linarith))

lemma utilization_strictMono (C : ℕ) (hC : 1 ≤ C) :
    StrictMonoOn (fun y : ℝ => U y C) (Ici 0) := by
  intro y hy z hz hyz
  change U y C < U z C
  obtain ⟨v, hv, hvy⟩ := exists_load_coordinate C hC hy
  obtain ⟨w, hw, hwz⟩ := exists_load_coordinate C hC hz
  have hvw : v < w := by
    by_contra h
    have hle := (load_coordinate_strictMono C hC).monotoneOn hw hv (le_of_not_gt h)
    rw [hvy, hwz] at hle
    exact (not_le_of_gt hyz) hle
  rw [← hvy, ← hwz, utilization_coordinate C hC hv, utilization_coordinate C hC hw]
  exact sn3_carried_strict C hC hv hvw

lemma utilization_nonneg (C : ℕ) (hC : 1 ≤ C) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ U y C := by
  obtain ⟨v, hv, hvy⟩ := exists_load_coordinate C hC hy
  rw [← hvy, utilization_coordinate C hC hv]
  exact mul_nonneg hv (sub_nonneg.mpr (sn3_erlang_lt_one C hC hv).le)

lemma utilization_zero (C : ℕ) (hC : 1 ≤ C) : U 0 C = 0 := by
  have hh := utilization_coordinate C hC (le_refl (0 : ℝ))
  simpa [erlang_zero C hC] using hh

lemma utilization_primitive_tangent (C : ℕ) (hC : 1 ≤ C) {y z : ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z) :
    U y C * (z - y) ≤ (∫ t in (0 : ℝ)..z, U t C) - ∫ t in (0 : ℝ)..y, U t C :=
  primitive_tangent (fun t => U t C) (utilization_strictMono C hC) hy hz

lemma utilization_primitive_strict_tangent (C : ℕ) (hC : 1 ≤ C) {y z : ℝ}
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hne : z ≠ y) :
    U y C * (z - y) < (∫ t in (0 : ℝ)..z, U t C) - ∫ t in (0 : ℝ)..y, U t C :=
  primitive_strict_tangent (fun t => U t C) (utilization_strictMono C hC) hy hz hne

end KellyLossNetworks.RevisedDual.Proof
end
-- END MODULE Utilization

-- BEGIN MODULE FixedPointCoordinates
section
set_option autoImplicit false
namespace KellyLossNetworks.RevisedDual.Proof
open KellyStochasticNetworks Finset

lemma fixedpoint_coordinates {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j)
    (E : Fin J → ℝ) (hK : ∀ j, E j ∈ Set.Icc (0:ℝ) 1)
    (hF : ErlangFixedPoint A ν C E) :
    (∀ j, 0 ≤ -Real.log (1-E j)) ∧
      StationarityConditions A ν C (fun j => -Real.log (1-E j)) ∧
      E = fun j => 1-Real.exp (-(-Real.log (1-E j))) := by
  let L : Fin J → ℝ := fun j => ∑ r, (A j r:ℝ)*ν r*∏ i, (1-E i)^(A i r)
  let ρ : Fin J → ℝ := fun j => (1-E j)⁻¹ * L j
  have hρ : ∀ j, 0 ≤ ρ j := fun j => mul_nonneg
    (inv_nonneg.mpr (sub_nonneg.mpr (hK j).2)) (sn3_load_nonneg A ν hν E hK j)
  have hlt : ∀ j, E j < 1 := by
    intro j
    rw [hF j]
    exact sn3_erlang_lt_one (C j) (hC j) (hρ j)
  have hexp : ∀ j, Real.exp (-(-Real.log (1-E j))) = 1-E j := by
    intro j
    rw [neg_neg,Real.exp_log (sub_pos.mpr (hlt j))]
  have hprod : ∀ r, Real.exp (-∑ i, (-Real.log (1-E i))*(A i r:ℝ)) =
      ∏ i, (1-E i)^(A i r) := by
    intro r
    rw [← Finset.sum_neg_distrib,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [show -((-Real.log (1-E i))*(A i r:ℝ)) = (A i r:ℝ)*(-(-Real.log (1-E i))) by ring,
      Real.exp_nat_mul,hexp i]
  refine ⟨?_,?_,?_⟩
  · intro j
    exact neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr (hlt j).le) (by linarith [(hK j).1]))
  · intro j
    have hu := utilization_coordinate (C j) (hC j) (hρ j)
    have hE : erlang (ρ j) (C j) = E j := (hF j).symm
    rw [hE] at hu
    rw [hu]
    simp_rw [hprod]
    change L j = ((1-E j)⁻¹ * L j)*(1-E j)
    have hn : 1-E j ≠ 0 := (sub_pos.mpr (hlt j)).ne'
    field_simp
  · funext j
    rw [hexp j]
    ring
end KellyLossNetworks.RevisedDual.Proof
end
-- END MODULE FixedPointCoordinates

-- BEGIN MODULE ExponentialTangent
section
set_option autoImplicit false
namespace KellyLossNetworks.RevisedDual.Proof
open Finset

lemma exponential_tangent (a b : ℝ) :
    Real.exp a + Real.exp a * (b-a) ≤ Real.exp b := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b-a)) (Real.exp_pos a).le
  rw [← Real.exp_add] at h
  rw [show a+(b-a)=b by ring] at h
  nlinarith

lemma route_tangent {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (y z : Fin J → ℝ) :
    (∑ r, ν r * Real.exp (-∑ j, y j * (A j r : ℝ))) -
      ∑ j, (z j-y j) * (∑ r, (A j r : ℝ)*ν r*Real.exp (-∑ i, y i*(A i r : ℝ))) ≤
      ∑ r, ν r * Real.exp (-∑ j, z j * (A j r : ℝ)) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin R)))
    (fun r _ => mul_le_mul_of_nonneg_left
      (exponential_tangent (-∑ j, y j*(A j r:ℝ)) (-∑ j, z j*(A j r:ℝ))) (hν r))
  have he : (∑ r, ν r * (Real.exp (-∑ j, y j*(A j r:ℝ)) +
      Real.exp (-∑ j, y j*(A j r:ℝ)) * ((-∑ j, z j*(A j r:ℝ))-(-∑ j, y j*(A j r:ℝ))))) =
      (∑ r, ν r * Real.exp (-∑ j, y j*(A j r:ℝ))) -
      ∑ j, (z j-y j) * (∑ r, (A j r:ℝ)*ν r*Real.exp (-∑ i, y i*(A i r:ℝ))) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    have hinner : (∑ j, (z j-y j)*((A j r:ℝ)*ν r*Real.exp (-∑ i, y i*(A i r:ℝ)))) =
        (∑ j, (z j-y j)*(A j r:ℝ)) * (ν r*Real.exp (-∑ i, y i*(A i r:ℝ))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hinner]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he] at h
  exact h
end KellyLossNetworks.RevisedDual.Proof
end
-- END MODULE ExponentialTangent

-- BEGIN MODULE StationaryOptimum
section
set_option autoImplicit false
namespace KellyLossNetworks.RevisedDual.Proof
open Finset

lemma objective_strict_of_stationary {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 ≤ ν r)
    (hu : ∀ j, StrictMonoOn (fun z => U z (C j)) (Set.Ici 0))
    (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j) (hs : StationarityConditions A ν C y)
    (z : Fin J → ℝ) (hz : ∀ j, 0 ≤ z j) (hne : z ≠ y) :
    revisedDualObjective A ν C y < revisedDualObjective A ν C z := by
  have hp : ∀ j, U (y j) (C j)*(z j-y j) ≤
      (∫ t in (0:ℝ)..z j, U t (C j)) - ∫ t in (0:ℝ)..y j, U t (C j) :=
    fun j => primitive_tangent _ (hu j) (hy j) (hz j)
  obtain ⟨j,hj⟩ := Function.ne_iff.mp hne
  have hstrict := Finset.sum_lt_sum (s := (univ : Finset (Fin J))) (fun j _ => hp j)
    ⟨j,mem_univ j,primitive_strict_tangent _ (hu j) (hy j) (hz j) hj⟩
  have hroute := route_tangent A ν hν y z
  have he : (∑ j, (z j-y j)*(∑ r, (A j r:ℝ)*ν r*Real.exp (-∑ i,y i*(A i r:ℝ)))) =
      ∑ j, U (y j) (C j)*(z j-y j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j,mul_comm]
  rw [he] at hroute
  rw [Finset.sum_sub_distrib] at hstrict
  unfold revisedDualObjective
  linarith

lemma unique_optimum_of_stationary {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 ≤ ν r)
    (hu : ∀ j, StrictMonoOn (fun z => U z (C j)) (Set.Ici 0))
    (y : Fin J → ℝ) (hy : ∀ j, 0 ≤ y j) (hs : StationarityConditions A ν C y) :
    IsRevisedDualOptimum A ν C y ∧
      ∀ z, IsRevisedDualOptimum A ν C z → z = y := by
  constructor
  · refine ⟨hy,fun z hz => ?_⟩
    by_cases he : z = y
    · rw [he]
    · exact (objective_strict_of_stationary A ν C hν hu y hy hs z hz he).le
  · intro z hz
    by_contra he
    exact (not_lt_of_ge (hz.2 y hy))
      (objective_strict_of_stationary A ν C hν hu y hy hs z hz.1 he)
end KellyLossNetworks.RevisedDual.Proof
end
-- END MODULE StationaryOptimum

-- BEGIN MODULE FullRevisedDual
section

namespace KellyLossNetworks.RevisedDual

/-- **Theorem 3.7.** Equations (3.1) and (3.2) have a unique solution `(E_1, …, E_J)`, given in
terms of the optimum `y` of the revised dual problem (3.5) by `E_j = 1 − exp(−y_j)`.

Stated as: if `ν_r > 0` for every route and `C_j ≥ 1` for every link, the revised dual problem
(3.5) has an optimum `y`, every optimum equals `y`, and a vector `E` is a solution of
(3.1)–(3.2) in `[0, 1]^J` if and only if `E_j = 1 − exp(−y_j)` for every `j`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, Theorem 3.7.

**Formalization Note.** (3.1)–(3.2) is the published `KellyStochasticNetworks.ErlangFixedPoint`
with Erlang's formula `KellyStochasticNetworks.erlang`; solutions are sought in `[0, 1]^J`, the
range the paper uses on p. 338. The hypotheses `ν_r > 0` and `C_j ≥ 1` are the paper's implicit
standing assumptions (a link with `C_j = 0` makes (3.4) meaningless). Existence and uniqueness of
the solution alone is the Proved platform theorem
`KellyStochasticNetworks.erlang_fixed_point_unique`; this statement adds that the solution is
`1 − exp(−y)` for the optimum `y` of (3.5). -/
theorem theorem_3_7 {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃ y : Fin J → ℝ, IsRevisedDualOptimum A ν C y ∧
      (∀ y' : Fin J → ℝ, IsRevisedDualOptimum A ν C y' → y' = y) ∧
      ∀ E : Fin J → ℝ,
        ((∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ KellyStochasticNetworks.ErlangFixedPoint A ν C E) ↔
          E = fun j => 1 - Real.exp (-y j) := by
  obtain ⟨E,hE,huniq⟩ := KellyStochasticNetworks.erlang_fixed_point_unique A ν C hν hC
  obtain ⟨hy,hstat,hcoord⟩ := Proof.fixedpoint_coordinates A ν C hν hC E hE.1 hE.2
  obtain ⟨hopt,hoptuniq⟩ := Proof.unique_optimum_of_stationary A ν C (fun r => (hν r).le)
    (fun j => Proof.utilization_strictMono (C j) (hC j)) _ hy hstat
  refine ⟨(fun j => -Real.log (1-E j)),hopt,hoptuniq,?_⟩
  intro E'
  constructor
  · intro hE'
    exact (huniq E' hE').trans hcoord
  · intro he
    have heq : E' = E := he.trans hcoord.symm
    rw [heq]
    exact hE

end KellyLossNetworks.RevisedDual

end
-- END MODULE FullRevisedDual

-- BEGIN MODULE PublicSolution
section
open KellyLossNetworks.RevisedDual

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃ y : Fin J → ℝ, IsRevisedDualOptimum A ν C y ∧
      (∀ y' : Fin J → ℝ, IsRevisedDualOptimum A ν C y' → y' = y) ∧
      ∀ E : Fin J → ℝ,
        ((∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ KellyStochasticNetworks.ErlangFixedPoint A ν C E) ↔
          E = fun j => 1 - Real.exp (-y j) := by
  exact KellyLossNetworks.RevisedDual.theorem_3_7 A ν C hν hC


end
-- END MODULE PublicSolution

#print axioms KellyLossNetworks.RevisedDual.theorem_3_7
#print axioms solution
