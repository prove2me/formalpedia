-- Prove2me | solution 1 for OAI.QuadricCounterexample.DiskSubharmonicOn.of_C2_laplacian_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T15:58:27.721994+00:00
-- url     : https://prove2.me/submissions/68a21351-94e5-436e-8862-2a5298e63475

import Mathlib
import Definitions.Def_OAIQWQC000

section
-- module Solutions.OAIQW_QuadricCounterexample.DiskHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory Laplacian InnerProductSpace
noncomputable section

lemma _root_.OAI.IsLocalMax.second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra hn
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge hn
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ ↦ f x := by
    filter_upwards [hm,hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hd : deriv f =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [he.eventuallyEq_nhds] with y hy
    rw [hy.deriv_eq,deriv_const]
  have hz : deriv (deriv f) x=0 := by rw [hd.deriv_eq,deriv_const]
  exact hp.ne' hz

lemma deriv_affine_eventually {X : Type u1} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x v : X} (hu : ContDiffAt ℝ 2 u x) :
    deriv (fun t : ℝ ↦ u (x+t • v)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ fderiv ℝ u (x+t • v) v) := by
  have hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y :=
    hu.eventually (by norm_num) |>.mono fun _ h ↦
      h.differentiableAt (by norm_num)
  have htend : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝 0) (𝓝 x) := by
    have hc : ContinuousAt (fun t : ℝ ↦ x+t • v) 0 := by fun_prop
    simpa only [zero_smul,add_zero] using hc.tendsto
  filter_upwards [htend hd] with t ht
  have hl : HasDerivAt (fun t : ℝ ↦ x+t • v) v t := by
    simpa using (hasDerivAt_id t).smul_const v |>.const_add x
  exact (ht.hasFDerivAt.comp_hasDerivAt t hl).deriv

lemma hasDerivAt_fderiv_affine {X : Type u2} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x v : X} (hu : ContDiffAt ℝ 2 u x) :
    HasDerivAt (fun t : ℝ ↦ fderiv ℝ u (x+t • v) v)
      ((fderiv ℝ (fderiv ℝ u) x v) v) 0 := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hline : HasDerivAt (fun t : ℝ ↦ x+t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x
  have hfd' : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) (x+(0 : ℝ) • v) := by
    simpa only [zero_smul,add_zero] using hfd.hasFDerivAt
  have hh : HasDerivAt (fun t : ℝ ↦ fderiv ℝ u (x+t • v))
      (fderiv ℝ (fderiv ℝ u) x v) 0 := hfd'.comp_hasDerivAt 0 hline
  have hv : HasDerivAt (fun _ : ℝ ↦ v) 0 0 := hasDerivAt_const 0 v
  simpa only [map_zero,add_zero] using hh.clm_apply hv

lemma second_deriv_affine {X : Type u3} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x v : X} (hu : ContDiffAt ℝ 2 u x) :
    deriv (deriv (fun t : ℝ ↦ u (x+t • v))) 0 =
      (fderiv ℝ (fderiv ℝ u) x v) v := by
  rw [(deriv_affine_eventually hu).deriv_eq]
  exact (hasDerivAt_fderiv_affine hu).deriv

lemma _root_.OAI.IsLocalMax.hessian_nonpos {X : Type u4} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x : X} (hm : IsLocalMax u x) (hu : ContDiffAt ℝ 2 u x) (v : X) :
    (fderiv ℝ (fderiv ℝ u) x v) v ≤ 0 := by
  rw [← second_deriv_affine hu]
  have hc : ContinuousAt (fun t : ℝ ↦ x+t • v) 0 := by fun_prop
  have hm' : IsLocalMax (fun t : ℝ ↦ u (x+t • v)) 0 := by
    have ht : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝 0) (𝓝 x) := by
      simpa only [zero_smul,add_zero] using hc.tendsto
    change ∀ᶠ t in 𝓝 (0 : ℝ), u (x+t • v) ≤ u (x+0 • v)
    simpa only [zero_smul,add_zero] using ht.eventually hm
  apply _root_.OAI.IsLocalMax.second_deriv_nonpos hm'
  apply ContinuousAt.comp _ hc
  simpa only [zero_smul,add_zero] using hu.continuousAt

lemma _root_.OAI.IsLocalMax.complexLaplacian_nonpos {u : ℂ → ℝ} {z : ℂ}
    (hm : IsLocalMax u z) (hu : ContDiffAt ℝ 2 u z) : complexLaplacian u z ≤ 0 :=
  add_nonpos (_root_.OAI.IsLocalMax.hessian_nonpos hm hu 1) (_root_.OAI.IsLocalMax.hessian_nonpos hm hu Complex.I)

lemma rotated_hessian_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) :
    (B a) a + (B (Complex.I*a)) (Complex.I*a) =
      Complex.normSq a * ((B 1) 1 + (B Complex.I) Complex.I) := by
  have ha : a=a.re • (1 : ℂ) + a.im • Complex.I := by
    apply Complex.ext <;> simp
  have hi : Complex.I*a = (-a.im) • (1 : ℂ) + a.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  rw [hi]
  conv_lhs => lhs; rw [ha]
  simp only [map_add,map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [Complex.normSq_apply]
  ring

lemma complexLaplacian_norm_sq (z : ℂ) :
    complexLaplacian (fun x : ℂ ↦ ‖x‖^2) z=4 := by
  unfold complexLaplacian
  rw [fderiv_norm_sq]
  have hh : fderiv ℝ (fun x : ℂ ↦ ((2 : ℝ) • (innerSL ℝ (E := ℂ))) x) z =
      (2 : ℝ) • (innerSL ℝ (E := ℂ)) := ((2 : ℝ) • (innerSL ℝ (E := ℂ))).fderiv
  have he : (2 • ⇑(innerSL ℝ (E := ℂ)) : ℂ → ℂ →L[ℝ] ℝ) =
      (fun x : ℂ ↦ ((2 : ℝ) • innerSL ℝ (E := ℂ)) x) := by
    ext x y
    simp [two_smul]
  rw [he,hh]
  change 2 * @inner ℝ ℂ _ 1 1 + 2 * @inner ℝ ℂ _ Complex.I Complex.I = 4
  norm_num

lemma hessian_add {X : Type u5} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u v : X → ℝ} {x : X} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    fderiv ℝ (fderiv ℝ (u+v)) x =
      fderiv ℝ (fderiv ℝ u) x + fderiv ℝ (fderiv ℝ v) x := by
  have he : fderiv ℝ (u+v) =ᶠ[𝓝 x] (fun y ↦ fderiv ℝ u y + fderiv ℝ v y) := by
    filter_upwards [hu.eventually (by norm_num),hv.eventually (by norm_num)] with y hy hy'
    exact fderiv_add (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))
  rw [he.fderiv_eq]
  exact fderiv_add
    ((hu.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt (by norm_num))
    ((hv.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt (by norm_num))

lemma complexLaplacian_add {u v : ℂ → ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (hv : ContDiffAt ℝ 2 v z) :
    complexLaplacian (u+v) z=complexLaplacian u z+complexLaplacian v z := by
  simp only [complexLaplacian,hessian_add hu hv,add_apply]
  ring

lemma hessian_smul {X : Type u6} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {u : X → ℝ} {x : X} (hu : ContDiffAt ℝ 2 u x) (a : ℝ) :
    fderiv ℝ (fderiv ℝ (a • u)) x = a • fderiv ℝ (fderiv ℝ u) x := by
  have he : fderiv ℝ (a • u) =ᶠ[𝓝 x] (fun y ↦ a • fderiv ℝ u y) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact fderiv_const_smul (hy.differentiableAt (by norm_num)) a
  rw [he.fderiv_eq]
  exact fderiv_const_smul
    ((hu.fderiv_right (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).differentiableAt (by norm_num)) a

lemma complexLaplacian_smul {u : ℂ → ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (a : ℝ) :
    complexLaplacian (a • u) z=a*complexLaplacian u z := by
  simp only [complexLaplacian,hessian_smul hu,smul_apply,smul_eq_mul]
  ring

lemma C2_le_boundary {u : ℂ → ℝ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hc : ContinuousOn u (closedBall c R))
    (hu : ContDiffOn ℝ 2 u (ball c R))
    (hΔ : ∀ z ∈ ball c R, 0 ≤ complexLaplacian u z)
    (hb : ∀ z ∈ sphere c R, u z ≤ M) : ∀ z ∈ closedBall c R, u z ≤ M := by
  have heps (ε : ℝ) (hε : 0 < ε) (z : ℂ) (hz : z∈closedBall c R) :
      u z ≤ M+ε*(‖c‖+R)^2 := by
    let v : ℂ → ℝ := u+ε • (fun x : ℂ ↦ ‖x‖^2)
    have hvc : ContinuousOn v (closedBall c R) := hc.add (continuousOn_const.mul (by fun_prop))
    obtain ⟨x,hx,hmax⟩ := (isCompact_closedBall c R).exists_isMaxOn
      ⟨c,mem_closedBall_self hR.le⟩ hvc
    have hxb : x∈sphere c R := by
      by_contra hn
      have hxi : x∈ball c R := by
        rw [mem_ball,mem_closedBall] at *
        exact lt_of_le_of_ne hx (by simpa only [mem_sphere] using hn)
      have hux : ContDiffAt ℝ 2 u x := (hu x hxi).contDiffAt (isOpen_ball.mem_nhds hxi)
      have hnx : ContDiffAt ℝ 2 (fun y : ℂ ↦ ‖y‖^2) x := (contDiff_norm_sq ℝ).contDiffAt
      have hmx : IsLocalMax v x := by
        filter_upwards [closedBall_mem_nhds_of_mem hxi] with y hy
        exact hmax hy
      have hnΔ := _root_.OAI.IsLocalMax.complexLaplacian_nonpos hmx (hux.add (ContDiffAt.const_smul ε hnx))
      have hpΔ : complexLaplacian v x=complexLaplacian u x+4*ε := by
        change complexLaplacian (u+ε • (fun y : ℂ ↦ ‖y‖^2)) x = _
        rw [complexLaplacian_add (v := ε • (fun y : ℂ ↦ ‖y‖^2)) hux
          (ContDiffAt.const_smul ε hnx),complexLaplacian_smul hnx,
          complexLaplacian_norm_sq]
        ring
      rw [hpΔ] at hnΔ
      linarith [hΔ x hxi]
    have hnorm : ‖x‖ ≤ ‖c‖+R := by
      have hd : ‖x-c‖=R := by simpa [mem_sphere,dist_eq_norm] using hxb
      calc ‖x‖ = ‖(x-c)+c‖ := by congr 1; abel
           _ ≤ ‖x-c‖+‖c‖ := norm_add_le _ _
           _ = ‖c‖+R := by rw [hd]; ring
    have hsq : ‖x‖^2 ≤ (‖c‖+R)^2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hnorm
    have hvz := hmax hz
    have hub := hb x hxb
    change u z+ε*‖z‖^2 ≤ u x+ε*‖x‖^2 at hvz
    nlinarith [mul_le_mul_of_nonneg_left hsq hε.le, mul_nonneg hε.le (sq_nonneg ‖z‖)]
  intro z hz
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := δ/((‖c‖+R)^2+1)
  have hden : 0 < (‖c‖+R)^2+1 := by positivity
  have hp : 0 < ε := div_pos hδ hden
  have heq : ε*((‖c‖+R)^2+1)=δ := by dsimp [ε]; exact div_mul_cancel₀ _ hden.ne'
  have hh := heps ε hp z hz
  linarith

end
end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory
noncomputable section

section
variable {α : Type u7} {X : Type u8} {Y : Type u9} [TopologicalSpace α] [CompactSpace α] [T2Space α]
  [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {D : Set X} {F : α → X → Y} {F' : α → X → X →L[ℝ] Y}

omit [NormedSpace ℝ X] [ProperSpace X] [NormedSpace ℝ Y] in
lemma compactParameter_integrable {z : X} (hz : z∈D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D)) :
    Integrable (fun a ↦ F a z) μ := by
  have h : Continuous (fun a ↦ F a z) :=
    hc.comp_continuous (f := fun a ↦ (a,z)) (by fun_prop) (fun a ↦ ⟨mem_univ a,hz⟩)
  exact integrableOn_univ.mp (h.continuousOn.integrableOn_compact isCompact_univ)

omit [NormedSpace ℝ X] in
lemma compactParameter_continuousAtIntegral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D)) {z : X} (hz : z∈D) :
    ContinuousAt (fun x ↦ ∫ a, F a x ∂μ) z := by
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hD.mem_nhds hz)
  obtain ⟨C,hC⟩ := (isCompact_univ.prod (isCompact_closedBall z r)).exists_bound_of_continuousOn
    (hc.mono (prod_mono (Subset.refl univ) hball))
  apply continuousAt_of_dominated (F := fun x a ↦ F a x) (bound := fun _ ↦ C)
  · filter_upwards [hD.mem_nhds hz] with x hx
    exact (compactParameter_integrable hx hc).aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds z hr] with x hx
    exact Eventually.of_forall fun a ↦ hC (a,x) ⟨mem_univ a,hx⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun a ↦
      (hc (a,z) ⟨mem_univ a,hz⟩).continuousAt
        ((isOpen_univ.prod hD).mem_nhds ⟨mem_univ a,hz⟩) |>.comp
          (continuousAt_const.prodMk continuousAt_id)

lemma compactParameter_hasFDerivAtIntegral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D))
    (hc' : ContinuousOn (Function.uncurry F') (univ ×ˢ D))
    (hd : ∀ a z, z∈D → HasFDerivAt (F a) (F' a z) z) {z : X} (hz : z∈D) :
    HasFDerivAt (fun x ↦ ∫ a, F a x ∂μ) (∫ a, F' a z ∂μ) z := by
  obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hD.mem_nhds hz)
  obtain ⟨C,hC⟩ := (isCompact_univ.prod (isCompact_closedBall z r)).exists_bound_of_continuousOn
    (hc'.mono (prod_mono (Subset.refl univ) hball))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x a ↦ F a x) (F' := fun x a ↦ F' a x)
    (bound := fun _ ↦ C) (closedBall_mem_nhds z hr)
  · filter_upwards [hD.mem_nhds hz] with x hx
    exact (compactParameter_integrable hx hc).aestronglyMeasurable
  · exact compactParameter_integrable hz hc
  · exact (compactParameter_integrable hz hc').aestronglyMeasurable
  · exact Eventually.of_forall fun a x hx ↦ hC (a,x) ⟨mem_univ a,hx⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun a x hx ↦ hd a x (hball hx)

lemma compactParameter_secondFDerivIntegral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D))
    (hc' : ContinuousOn (Function.uncurry F') (univ ×ˢ D))
    {F'' : α → X → X →L[ℝ] X →L[ℝ] Y}
    (hc'' : ContinuousOn (Function.uncurry F'') (univ ×ˢ D))
    (hd : ∀ a z, z∈D → HasFDerivAt (F a) (F' a z) z)
    (hd' : ∀ a z, z∈D → HasFDerivAt (F' a) (F'' a z) z)
    {z : X} (hz : z∈D) :
    fderiv ℝ (fderiv ℝ (fun x ↦ ∫ a, F a x ∂μ)) z = ∫ a, F'' a z ∂μ := by
  have he : fderiv ℝ (fun x ↦ ∫ a, F a x ∂μ) =ᶠ[𝓝 z] fun x ↦ ∫ a, F' a x ∂μ := by
    filter_upwards [hD.mem_nhds hz] with x hx
    exact (compactParameter_hasFDerivAtIntegral hD hc hc' hd hx).fderiv
  rw [he.fderiv_eq]
  exact (compactParameter_hasFDerivAtIntegral hD hc' hc'' hd' hz).fderiv
lemma compactParameter_contDiffOn_one_Integral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D))
    (hc' : ContinuousOn (Function.uncurry F') (univ ×ˢ D))
    (hd : ∀ a z, z∈D → HasFDerivAt (F a) (F' a z) z) :
    ContDiffOn ℝ 1 (fun x ↦ ∫ a, F a x ∂μ) D := by
  rw [show (1 : WithTop ℕ∞)=0+1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hD]
  refine ⟨fun z hz ↦ (compactParameter_hasFDerivAtIntegral hD hc hc' hd hz).differentiableAt.differentiableWithinAt,
    fun h ↦ by simp at h, ?_⟩
  rw [contDiffOn_zero]
  have hh : ContinuousOn (fun x ↦ ∫ a, F' a x ∂μ) D :=
    fun z hz ↦ (compactParameter_continuousAtIntegral hD hc' hz).continuousWithinAt
  apply hh.congr
  intro x hx
  exact (compactParameter_hasFDerivAtIntegral hD hc hc' hd hx).fderiv

lemma compactParameter_contDiffOn_two_Integral (hD : IsOpen D)
    (hc : ContinuousOn (Function.uncurry F) (univ ×ˢ D))
    (hc' : ContinuousOn (Function.uncurry F') (univ ×ˢ D))
    {F'' : α → X → X →L[ℝ] X →L[ℝ] Y}
    (hc'' : ContinuousOn (Function.uncurry F'') (univ ×ˢ D))
    (hd : ∀ a z, z∈D → HasFDerivAt (F a) (F' a z) z)
    (hd' : ∀ a z, z∈D → HasFDerivAt (F' a) (F'' a z) z) :
    ContDiffOn ℝ 2 (fun x ↦ ∫ a, F a x ∂μ) D := by
  rw [show (2 : WithTop ℕ∞)=1+1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hD]
  refine ⟨fun z hz ↦ (compactParameter_hasFDerivAtIntegral hD hc hc' hd hz).differentiableAt.differentiableWithinAt,
    fun h ↦ by simp at h, ?_⟩
  apply (compactParameter_contDiffOn_one_Integral (μ := μ) hD hc' hc'' hd').congr
  intro x hx
  exact (compactParameter_hasFDerivAtIntegral hD hc hc' hd hx).fderiv

end

end
end QuadricCounterexample

end OAI
end

section
-- module Solutions.OAIQW_QuadricCounterexample.Plurisubharmonic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

namespace QuadricCounterexample
open Set Filter Topology Metric MeasureTheory
noncomputable section
open scoped Pointwise

attribute [local instance] Measure.Subtype.measureSpace

lemma radialFirst_hasFDerivAt {u : ℂ → ℝ} {c a z : ℂ}
    (hu : DifferentiableAt ℝ u (c+a*z)) :
    HasFDerivAt (fun x : ℂ ↦ u (c+a*x)) (radialFirst u c a z) z := by
  exact hu.hasFDerivAt.comp z ((radialLinear a).hasFDerivAt.const_add c)

lemma radialSecond_hasFDerivAt {u : ℂ → ℝ} {c a z : ℂ}
    (hu : DifferentiableAt ℝ (fderiv ℝ u) (c+a*z)) :
    HasFDerivAt (radialFirst u c a) (radialSecond u c a z) z := by
  exact ((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip (radialLinear a)).hasFDerivAt.comp z
    (hu.hasFDerivAt.comp z ((radialLinear a).hasFDerivAt.const_add c))

lemma radialFamily_maps_closedBall {c : ℂ} {R : ℝ} (_hR : 0 ≤ R)
    (a : closedBall (0 : ℂ) 1) (z : ℂ) (hz : z∈closedBall 0 R) :
    c+(a : ℂ)*z ∈ closedBall c R := by
  rw [mem_closedBall,dist_self_add_left,norm_mul]
  have ha : ‖(a : ℂ)‖≤1 := by simpa only [mem_closedBall,dist_zero_right] using a.property
  have hz' : ‖z‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hz
  nlinarith [mul_le_mul ha hz' (norm_nonneg z) (by norm_num : (0 : ℝ)≤1)]

lemma radialFamily_continuous {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hR : 0≤R) (hu : ContinuousOn u D) (hb : closedBall c R⊆D) :
    ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ u (c+(p.1 : ℂ)*p.2))
      (univ ×ˢ closedBall 0 R) := by
  exact hu.comp (by fun_prop) (fun p hp ↦ hb (radialFamily_maps_closedBall hR p.1 p.2 hp.2))

lemma radialFirst_continuous {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0≤R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D) :
    ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ radialFirst u c p.1 p.2)
      (univ ×ˢ closedBall 0 R) := by
  have hfd : ContinuousOn (fderiv ℝ u) D :=
    (hu.fderiv_of_isOpen hD (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).continuousOn
  have hf := hfd.comp (show ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦
    c+(p.1 : ℂ)*p.2) (univ ×ˢ closedBall 0 R) by fun_prop)
    (fun p hp ↦ hb (radialFamily_maps_closedBall hR p.1 p.2 hp.2))
  exact hf.clm_comp (show ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ radialLinear p.1)
    (univ ×ˢ closedBall 0 R) from (ContinuousLinearMap.mul ℝ ℂ).continuous.continuousOn.comp
      (by fun_prop) (mapsTo_univ _ _))

lemma radialSecond_continuous {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0≤R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D) :
    ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ radialSecond u c p.1 p.2)
      (univ ×ˢ closedBall 0 R) := by
  have hfd : ContinuousOn (fderiv ℝ (fderiv ℝ u)) D :=
    ((hu.fderiv_of_isOpen hD (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))).fderiv_of_isOpen
      hD (by norm_num : 0+1 ≤ (1 : WithTop ℕ∞))).continuousOn
  have hf := hfd.comp (show ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦
    c+(p.1 : ℂ)*p.2) (univ ×ˢ closedBall 0 R) by fun_prop)
    (fun p hp ↦ hb (radialFamily_maps_closedBall hR p.1 p.2 hp.2))
  have hL : ContinuousOn (fun p : closedBall (0 : ℂ) 1 × ℂ ↦ radialLinear p.1)
      (univ ×ˢ closedBall 0 R) :=
    (ContinuousLinearMap.mul ℝ ℂ).continuous.continuousOn.comp (by fun_prop) (mapsTo_univ _ _)
  exact (((ContinuousLinearMap.compL ℝ ℂ ℂ ℝ).flip).continuous.comp_continuousOn hL).clm_comp
    (hf.clm_comp hL)

lemma radialIntegral_C2 {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0<R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D) :
    ContDiffOn ℝ 2 (radialIntegral u c) (ball 0 R) := by
  let A := closedBall (0 : ℂ) 1
  let : IsFiniteMeasure (volume : Measure A) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  have hd (a : A) (z : ℂ) (hz : z∈ball 0 R) :
      HasFDerivAt (fun x ↦ u (c+(a : ℂ)*x)) (radialFirst u c a z) z := by
    have hx := hb (radialFamily_maps_closedBall hR.le a z (ball_subset_closedBall hz))
    exact radialFirst_hasFDerivAt ((hu (c+(a : ℂ)*z) hx).contDiffAt
      (hD.mem_nhds hx) |>.differentiableAt (by norm_num))
  have hd' (a : A) (z : ℂ) (hz : z∈ball 0 R) :
      HasFDerivAt (radialFirst u c a) (radialSecond u c a z) z := by
    have hx := hb (radialFamily_maps_closedBall hR.le a z (ball_subset_closedBall hz))
    exact radialSecond_hasFDerivAt
      (((hu.fderiv_of_isOpen hD (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))) _ hx).contDiffAt
        (hD.mem_nhds hx) |>.differentiableAt (by norm_num))
  have hh := compactParameter_contDiffOn_two_Integral (μ := (volume : Measure A)) isOpen_ball
    ((radialFamily_continuous hR.le hu.continuousOn hb).mono (prod_mono (Subset.refl univ) ball_subset_closedBall))
    ((radialFirst_continuous hD hR.le hu hb).mono (prod_mono (Subset.refl univ) ball_subset_closedBall))
    ((radialSecond_continuous hD hR.le hu hb).mono (prod_mono (Subset.refl univ) ball_subset_closedBall)) hd hd'
  convert hh using 1
  ext z
  exact (integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
    (fun a : ℂ ↦ u (c+a*z))).symm

attribute [local instance] OAI.QuadricCounterexample.realDualComplexGroup
attribute [local instance] OAI.QuadricCounterexample.realDualComplexSpace
lemma integral_bilinear_apply {α : Type u2} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℂ →L[ℝ] ℂ →L[ℝ] ℝ} (hF : Integrable F μ) (v w : ℂ) :
    (∫ a, F a ∂μ) v w = ∫ a, F a v w ∂μ := by
  let ev : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
    ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℝ) v
  have hv : Integrable (fun a ↦ F a v) μ := ev.integrable_comp hF
  rw [ContinuousLinearMap.integral_apply hF v,ContinuousLinearMap.integral_apply hv w]

lemma radialIntegral_laplacian {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0<R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D)
    {z : ℂ} (hz : z∈ball 0 R) :
    complexLaplacian (radialIntegral u c) z =
      ∫ a in closedBall (0 : ℂ) 1, Complex.normSq a*complexLaplacian u (c+a*z) := by
  let A := closedBall (0 : ℂ) 1
  let : IsFiniteMeasure (volume : Measure A) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  have hd (a : A) (z : ℂ) (hz : z∈ball 0 R) :
      HasFDerivAt (fun x ↦ u (c+(a : ℂ)*x)) (radialFirst u c a z) z := by
    have hx := hb (radialFamily_maps_closedBall hR.le a z (ball_subset_closedBall hz))
    exact radialFirst_hasFDerivAt ((hu (c+(a : ℂ)*z) hx).contDiffAt
      (hD.mem_nhds hx) |>.differentiableAt (by norm_num))
  have hd' (a : A) (z : ℂ) (hz : z∈ball 0 R) :
      HasFDerivAt (radialFirst u c a) (radialSecond u c a z) z := by
    have hx := hb (radialFamily_maps_closedBall hR.le a z (ball_subset_closedBall hz))
    exact radialSecond_hasFDerivAt
      (((hu.fderiv_of_isOpen hD (by norm_num : 1+1 ≤ (2 : WithTop ℕ∞))) _ hx).contDiffAt
        (hD.mem_nhds hx) |>.differentiableAt (by norm_num))
  have hF := (radialFamily_continuous hR.le hu.continuousOn hb).mono
    (prod_mono (Subset.refl univ) ball_subset_closedBall)
  have hF' := (radialFirst_continuous hD hR.le hu hb).mono
    (prod_mono (Subset.refl univ) ball_subset_closedBall)
  have hF'' := (radialSecond_continuous hD hR.le hu hb).mono
    (prod_mono (Subset.refl univ) ball_subset_closedBall)
  have hh := compactParameter_secondFDerivIntegral (μ := (volume : Measure A)) isOpen_ball
    hF hF' hF'' hd hd' hz
  have he : (fun z ↦ ∫ a : A, u (c+(a : ℂ)*z))=radialIntegral u c := by
    ext x
    exact integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
      (fun a : ℂ ↦ u (c+a*x))
  rw [he] at hh
  have hH : Integrable (fun a : A ↦ radialSecond u c a z) :=
    compactParameter_integrable (F := fun a : A ↦ radialSecond u c a) hz hF''
  have hHv (v w : ℂ) : Integrable (fun a : A ↦ radialSecond u c a z v w) := by
    let ev : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
      ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℝ) v
    have hv : Integrable (fun a : A ↦ radialSecond u c a z v) := ev.integrable_comp hH
    exact (ContinuousLinearMap.apply ℝ ℝ w).integrable_comp hv
  unfold complexLaplacian
  rw [hh,integral_bilinear_apply hH 1 1,integral_bilinear_apply hH Complex.I Complex.I,
    ← integral_add (hHv 1 1) (hHv Complex.I Complex.I)]
  rw [← integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall]
  apply integral_congr_ae
  exact Eventually.of_forall fun a ↦ by
    simpa only [radialSecond_apply,mul_one,mul_comm (a : ℂ) Complex.I] using
      rotated_hessian_trace (fderiv ℝ (fderiv ℝ u) (c+(a : ℂ)*z)) a

lemma radialIntegral_laplacian_nonneg {u : ℂ → ℝ} {D : Set ℂ} {c : ℂ} {R : ℝ}
    (hD : IsOpen D) (hR : 0<R) (hu : ContDiffOn ℝ 2 u D) (hb : closedBall c R⊆D)
    (hΔ : ∀ z∈D, 0≤complexLaplacian u z) {z : ℂ} (hz : z∈ball 0 R) :
    0≤complexLaplacian (radialIntegral u c) z := by
  rw [radialIntegral_laplacian hD hR hu hb hz]
  apply setIntegral_nonneg measurableSet_closedBall
  intro a ha
  exact mul_nonneg (Complex.normSq_nonneg a)
    (hΔ _ (hb (radialFamily_maps_closedBall hR.le ⟨a,ha⟩ z (ball_subset_closedBall hz))))

theorem C2_disk_submean {u : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D)
    (hu : ContDiffOn ℝ 2 u D) (hΔ : ∀ z∈D, 0≤complexLaplacian u z)
    {c : ℂ} {R : ℝ} (hR : 0<R) (hb : closedBall c R⊆D) :
    (volume (ball c R)).toReal*u c ≤ ∫ y in ball c R, u y := by
  let A := closedBall (0 : ℂ) 1
  let : IsFiniteMeasure (volume : Measure A) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  have he : (fun z ↦ ∫ a : A, u (c+(a : ℂ)*z))=radialIntegral u c := by
    ext x
    exact integral_subtype (s := closedBall (0 : ℂ) 1) measurableSet_closedBall
      (fun a : ℂ ↦ u (c+a*x))
  have hc : ContinuousOn (radialIntegral u c) (closedBall 0 R) := by
    rw [← he]
    exact compact_integral_continuousOn (radialFamily_continuous hR.le hu.continuousOn hb)
  have hm0 := C2_le_boundary hR hc (radialIntegral_C2 hD hR hu hb)
    (fun z hz ↦ radialIntegral_laplacian_nonneg hD hR hu hb hΔ hz)
    (M := radialIntegral u c (R : ℂ)) (by
      intro z hz
      apply le_of_eq
      apply radialIntegral_eq_of_norm_eq
      simpa only [mem_sphere,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR] using hz)
    0 (mem_closedBall_self hR.le)
  rw [radialIntegral_zero,radialIntegral_pos_radius _ _ hR] at hm0
  have hv := radialIntegral_pos_radius (fun _ ↦ (1 : ℝ)) c hR
  simp only [radialIntegral,setIntegral_const,measureReal_def,smul_eq_mul,mul_one] at hv
  have heR := complex_closedBall_ae_ball c R
  rw [measure_congr heR] at hv
  rw [← setIntegral_congr_set heR]
  have hn : R^2 ≠ 0 := pow_ne_zero _ hR.ne'
  have hscale : R^2 * (R^2)⁻¹ = 1 := mul_inv_cancel₀ hn
  have hmul := mul_le_mul_of_nonneg_left hm0 (sq_nonneg R)
  calc
    (volume (ball c R)).toReal * u c =
        R^2 * ((volume (closedBall (0 : ℂ) 1)).toReal * u c) := by
      rw [hv]
      rw [← mul_assoc,← mul_assoc,hscale,one_mul]
    _ ≤ R^2 * ((R^2)⁻¹ * ∫ y in closedBall c R, u y) := hmul
    _ = ∫ y in closedBall c R, u y := by rw [← mul_assoc,hscale,one_mul]

theorem DiskSubharmonicOn.of_C2_laplacian_nonneg_oai {u : ℂ → ℝ} {D : Set ℂ}
    (hD : IsOpen D) (hu : ContDiffOn ℝ 2 u D) (hΔ : ∀ z∈D, 0≤complexLaplacian u z) :
    DiskSubharmonicOn D u := by
  refine ⟨hu.continuousOn.upperSemicontinuousOn,fun c _ R hR hb ↦ ⟨?_,C2_disk_submean hD hu hΔ hR hb⟩⟩
  exact ((hu.continuousOn.mono hb).integrableOn_compact (isCompact_closedBall c R)).mono_set ball_subset_closedBall

end
end QuadricCounterexample

end OAI
end

theorem solution : type_of% @OAI.QuadricCounterexample.DiskSubharmonicOn.of_C2_laplacian_nonneg_oai := @OAI.QuadricCounterexample.DiskSubharmonicOn.of_C2_laplacian_nonneg_oai
