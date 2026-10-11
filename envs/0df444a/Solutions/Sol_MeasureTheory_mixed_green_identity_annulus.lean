-- Prove2me | solution 1 for MeasureTheory.mixed_green_identity_annulus
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T12:25:00.255991+00:00
-- url     : https://prove2.me/submissions/94f8ebae-40a5-4bd3-b2db-6a709cabe831

import Definitions.Def_HunterPDE_Newtonian_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Theorems.Thm_MeasureTheory_integral_directional_derivative_annulus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open MeasureTheory HunterPDE.Newtonian
open scoped ContDiff
open MeasureTheory HunterPDE.Newtonian Metric Set Filter
open scoped ContDiff Topology

noncomputable section
namespace MixedGreenMainWork

variable {n : ℕ}

/-- Mixed partials of a `C²` function agree with the bilinear second derivative. -/
theorem fderiv_fderiv_apply_apply {K : (EuclideanSpace ℝ (Fin n)) → ℝ} {z : EuclideanSpace ℝ (Fin n)} (hK : ContDiffAt ℝ 2 K z)
    (a b : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun w => fderiv ℝ K w a) z b = fderiv ℝ (fderiv ℝ K) z b a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ K) z :=
    (hK.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const a)]
  simp

theorem partialDeriv_comm {K : (EuclideanSpace ℝ (Fin n)) → ℝ} {z : EuclideanSpace ℝ (Fin n)} (hK : ContDiffAt ℝ 2 K z) (i j : Fin n) :
    partialDeriv (partialDeriv K i) j z = secondPartial K i j z := by
  unfold secondPartial partialDeriv
  rw [fderiv_fderiv_apply_apply hK, fderiv_fderiv_apply_apply hK]
  exact hK.isSymmSndFDerivAt (by simp) _ _

theorem hasFDerivAt_comp_sub {u : (EuclideanSpace ℝ (Fin n)) → ℝ} {x y : EuclideanSpace ℝ (Fin n)}
    (hu : DifferentiableAt ℝ u (x - y)) :
    HasFDerivAt (fun y => u (x - y)) ((fderiv ℝ u (x - y)).comp (-ContinuousLinearMap.id ℝ _)) y :=
  hu.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)

theorem fderiv_mul_comp_sub_apply {u w : (EuclideanSpace ℝ (Fin n)) → ℝ} {x y : EuclideanSpace ℝ (Fin n)}
    (hu : DifferentiableAt ℝ u (x - y)) (hw : DifferentiableAt ℝ w y) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => u (x - y) * w y) y v =
      -(fderiv ℝ u (x - y) v) * w y + u (x - y) * fderiv ℝ w y v := by
  have h : HasFDerivAt (fun y => u (x - y) * w y)
      (u (x - y) • fderiv ℝ w y +
        w y • (fderiv ℝ u (x - y)).comp (-ContinuousLinearMap.id ℝ _)) y :=
    (hasFDerivAt_comp_sub hu).mul hw.hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    map_neg, smul_eq_mul]
  ring

theorem sphere_ne_zero {s : ℝ} (hs : 0 < s) (w0 : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : -(s • w0.1) ≠ 0 := by
  have hw0 : ‖w0.1‖ = 1 := by simpa using w0.2
  intro h
  have := congrArg norm h
  rw [norm_neg, norm_smul, hw0, norm_zero, mul_one, Real.norm_of_nonneg hs.le] at this
  exact hs.ne' this

theorem main (n : ℕ) (hn : 0 < n) (K : (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hK : ContDiffOn ℝ ∞ K {0}ᶜ)
    (g : (EuclideanSpace ℝ (Fin n)) → ℝ) (hg : ContDiff ℝ 2 g)
    (x : EuclideanSpace ℝ (Fin n)) (R r : ℝ) (hR : 0 < R)
    (hr : 0 < r) (hrR : r < R) (i j : Fin n) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      secondPartial K i j (x - y) * g y) =
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      K (x - y) * secondPartial g i j y)
    - R ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        K (-(R • w.1)) * partialDeriv g j (x + R • w.1) * w.1 i
        + partialDeriv K i (-(R • w.1)) * g (x + R • w.1) * w.1 j
        ∂volume.toSphere)
    + r ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        K (-(r • w.1)) * partialDeriv g j (x + r • w.1) * w.1 i
        + partialDeriv K i (-(r • w.1)) * g (x + r • w.1) * w.1 j
        ∂volume.toSphere) := by
  -- regularity of the kernel away from the origin
  have hK3 : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ContDiffAt ℝ 3 K z := fun z hz =>
    (hK.contDiffAt (isOpen_compl_singleton.mem_nhds hz)).of_le (by first | simp | exact_mod_cast (le_top : ((3 : ℕ) : ℕ∞) ≤ ⊤) | exact WithTop.coe_le_coe.2 le_top)
  set P : (EuclideanSpace ℝ (Fin n)) → ℝ := partialDeriv K i with hP
  have hP2 : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → ContDiffAt ℝ 2 P z := fun z hz =>
    ((hK3 z hz).fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  set dg : (EuclideanSpace ℝ (Fin n)) → ℝ := partialDeriv g j with hdg
  have hdg1 : ContDiff ℝ 1 dg :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hsub : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ x → x - y ≠ 0 := fun y hy h => hy (sub_eq_zero.1 h).symm
  have hsubC : ∀ (u : (EuclideanSpace ℝ (Fin n)) → ℝ) (m : ℕ) (y : EuclideanSpace ℝ (Fin n)), ContDiffAt ℝ m u (x - y) →
      ContDiffAt ℝ m (fun y => u (x - y)) y := fun u m y hu =>
    hu.comp y (contDiffAt_const.sub contDiffAt_id)
  -- the two vector fields
  set φ : (EuclideanSpace ℝ (Fin n)) → ℝ := fun y => P (x - y) * g y with hφ
  set ψ : (EuclideanSpace ℝ (Fin n)) → ℝ := fun y => K (x - y) * dg y with hψ
  have hφC : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ x → ContDiffAt ℝ 1 φ y := fun y hy =>
    (hsubC P 1 y ((hP2 _ (hsub y hy)).of_le (by norm_num))).mul
      (hg.contDiffAt.of_le (by norm_num))
  have hψC : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ x → ContDiffAt ℝ 1 ψ y := fun y hy =>
    (hsubC K 1 y ((hK3 _ (hsub y hy)).of_le (by norm_num))).mul hdg1.contDiffAt
  have I1 := MeasureTheory.integral_directional_derivative_annulus hn hr hrR
    (fun y _ hy => hφC y hy) (EuclideanSpace.single j 1)
  have I2 := MeasureTheory.integral_directional_derivative_annulus hn hr hrR
    (fun y _ hy => hψC y hy) (EuclideanSpace.single i 1)
  -- pointwise identity on the annulus
  have hx_notin : ∀ y ∈ ball x R \ closedBall x r, y ≠ x := by
    intro y hy hyx
    subst hyx
    exact hy.2 (mem_closedBall_self hr.le)
  have hpt : ∀ y : EuclideanSpace ℝ (Fin n), y ≠ x →
      fderiv ℝ φ y (EuclideanSpace.single j 1) + fderiv ℝ ψ y (EuclideanSpace.single i 1) =
        -(secondPartial K i j (x - y) * g y) + K (x - y) * secondPartial g i j y := by
    intro y hy
    have hz := hsub y hy
    rw [hφ, hψ,
      fderiv_mul_comp_sub_apply ((hP2 _ hz).differentiableAt (by norm_num))
        (hg.differentiable (by norm_num) y),
      fderiv_mul_comp_sub_apply ((hK3 _ hz).differentiableAt (by norm_num))
        (hdg1.differentiable (by norm_num) y)]
    have h1 : fderiv ℝ P (x - y) (EuclideanSpace.single j 1) = secondPartial K i j (x - y) :=
      partialDeriv_comm ((hK3 _ hz).of_le (by norm_num)) i j
    have h2 : fderiv ℝ K (x - y) (EuclideanSpace.single i 1) = P (x - y) := rfl
    have h3 : fderiv ℝ g y (EuclideanSpace.single j 1) = dg y := rfl
    have h4 : fderiv ℝ dg y (EuclideanSpace.single i 1) = secondPartial g i j y := rfl
    rw [h1, h2, h3, h4]
    ring
  -- integrability on the annulus
  have hcpt : IsCompact (closedBall x R \ ball x r) := (isCompact_closedBall x R).diff isOpen_ball
  have hAsub : ball x R \ closedBall x r ⊆ closedBall x R \ ball x r :=
    diff_subset_diff ball_subset_closedBall ball_subset_closedBall
  have hne : ∀ y ∈ closedBall x R \ ball x r, y ≠ x := by
    intro y hy hyx
    subst hyx
    exact hy.2 (mem_ball_self hr)
  have hintφ : IntegrableOn (fun y => fderiv ℝ φ y (EuclideanSpace.single j 1))
      (ball x R \ closedBall x r) := by
    refine (ContinuousOn.integrableOn_compact hcpt ?_).mono_set hAsub
    intro y hy
    exact (((hφC y (hne y hy)).continuousAt_fderiv one_ne_zero).clm_apply
      continuousAt_const).continuousWithinAt
  have hintψ : IntegrableOn (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1))
      (ball x R \ closedBall x r) := by
    refine (ContinuousOn.integrableOn_compact hcpt ?_).mono_set hAsub
    intro y hy
    exact (((hψC y (hne y hy)).continuousAt_fderiv one_ne_zero).clm_apply
      continuousAt_const).continuousWithinAt
  have hintK : IntegrableOn (fun y => K (x - y) * secondPartial g i j y)
      (ball x R \ closedBall x r) := by
    refine (ContinuousOn.integrableOn_compact hcpt ?_).mono_set hAsub
    intro y hy
    have hKc : ContinuousAt (fun y => K (x - y)) y :=
      (hsubC K 1 y ((hK3 _ (hsub y (hne y hy))).of_le (by norm_num))).continuousAt
    have hgc : Continuous (secondPartial g i j) :=
      (hdg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hKc.mul hgc.continuousAt).continuousWithinAt
  have hmeas : MeasurableSet (ball x R \ closedBall x r) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hLHS : (∫ y in ball x R \ closedBall x r, secondPartial K i j (x - y) * g y) =
      (∫ y in ball x R \ closedBall x r, K (x - y) * secondPartial g i j y)
        - ((∫ y in ball x R \ closedBall x r, fderiv ℝ φ y (EuclideanSpace.single j 1))
          + ∫ y in ball x R \ closedBall x r, fderiv ℝ ψ y (EuclideanSpace.single i 1)) := by
    have hs := integral_sub hintK (hintφ.add hintψ)
    refine Eq.trans ?_ (hs.trans ?_)
    swap
    · congr 1
      exact integral_add hintφ hintψ
    apply setIntegral_congr_fun hmeas
    intro y hy
    simp only [Pi.add_apply]
    rw [hpt y (hx_notin y hy)]
    ring
  refine hLHS.trans ?_
  rw [I1, I2]
  -- boundary integrals
  have hbd : ∀ s : ℝ, 0 < s →
      (∫ w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        K (-(s • w.1)) * partialDeriv g j (x + s • w.1) * w.1 i
        + partialDeriv K i (-(s • w.1)) * g (x + s • w.1) * w.1 j ∂volume.toSphere) =
      (∫ w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        φ (x + s • w.1) * inner ℝ (EuclideanSpace.single j (1 : ℝ)) w.1 ∂volume.toSphere)
      + ∫ w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ψ (x + s • w.1) * inner ℝ (EuclideanSpace.single i (1 : ℝ)) w.1 ∂volume.toSphere := by
    intro s hs
    have hxs : ∀ w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, x - (x + s • w.1) = -(s • w.1) := fun w => by
      rw [sub_add_cancel_left]
    have hcw : ∀ k : Fin n, Continuous fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => w.1 k := fun k =>
      (EuclideanSpace.proj k).continuous.comp continuous_subtype_val
    have hcpt' : Continuous fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => x + s • w.1 :=
      continuous_const.add (continuous_subtype_val.const_smul s)
    have hcneg : Continuous fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => -(s • w.1) :=
      (continuous_subtype_val.const_smul s).neg
    have hA : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        φ (x + s • w.1) * inner ℝ (EuclideanSpace.single j (1 : ℝ)) w.1) volume.toSphere := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      refine continuous_iff_continuousAt.2 fun w => ?_
      simp only [hφ, hxs]
      have c1 : ContinuousAt (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => P (-(s • w.1))) w :=
        ContinuousAt.comp (g := P) (f := fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => -(s • w.1)) (x := w)
          (hP2 _ (sphere_ne_zero hs w)).continuousAt hcneg.continuousAt
      have c2 := (hg.continuous.comp hcpt').continuousAt (x := w)
      refine (c1.mul c2).mul ?_
      exact (continuous_const.inner continuous_subtype_val).continuousAt
    have hB : Integrable (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        ψ (x + s • w.1) * inner ℝ (EuclideanSpace.single i (1 : ℝ)) w.1) volume.toSphere := by
      apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
      refine continuous_iff_continuousAt.2 fun w => ?_
      simp only [hψ, hxs]
      have c1 : ContinuousAt (fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => K (-(s • w.1))) w :=
        ContinuousAt.comp (g := K) (f := fun w : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => -(s • w.1)) (x := w)
          (hK3 _ (sphere_ne_zero hs w)).continuousAt hcneg.continuousAt
      have c2 := (hdg1.continuous.comp hcpt').continuousAt (x := w)
      refine (c1.mul c2).mul ?_
      exact (continuous_const.inner continuous_subtype_val).continuousAt
    rw [← integral_add hA hB]
    congr 1
    funext w
    simp only [hφ, hψ, hxs, EuclideanSpace.inner_single_left, map_one, one_mul]
    ring
  rw [hbd R hR, hbd r hr]
  ring

end MixedGreenMainWork

open MeasureTheory

theorem solution
    (n : ℕ) (hn : 0 < n) (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : ContDiffOn ℝ ∞ K {0}ᶜ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (x : EuclideanSpace ℝ (Fin n)) (R r : ℝ) (hR : 0 < R)
    (hr : 0 < r) (hrR : r < R) (i j : Fin n) :
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      secondPartial K i j (x - y) * g y) =
    (∫ y in Metric.ball x R \ Metric.closedBall x r,
      K (x - y) * secondPartial g i j y)
    - R ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        K (-(R • w.1)) * partialDeriv g j (x + R • w.1) * w.1 i
        + partialDeriv K i (-(R • w.1)) * g (x + R • w.1) * w.1 j
        ∂volume.toSphere)
    + r ^ (n - 1) *
      (∫ (w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        K (-(r • w.1)) * partialDeriv g j (x + r • w.1) * w.1 i
        + partialDeriv K i (-(r • w.1)) * g (x + r • w.1) * w.1 j
        ∂volume.toSphere) :=
  MixedGreenMainWork.main n hn K hK g hg x R r hR hr hrR i j
