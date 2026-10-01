-- Prove2me | solution 1 for NonsmoothNewton.AugLagrangian.eta_grad_semismooth_on_surface
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:23:42.837411+00:00
-- url     : https://prove2.me/submissions/0b06c728-991b-4e00-9e4e-7ed3e1fc08b8

import Mathlib
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian

open NonsmoothNewton.Shared
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

private theorem positive_sq_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (max 0 y)^2) (2 * max 0 x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : (fun y : ℝ => (max 0 y)^2) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp [max_eq_left hy.le]
    simpa [max_eq_left hx.le] using (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq
  · rw [show 2 * max (0 : ℝ) 0 = 0 by norm_num, hasDerivAt_iff_tendsto_slope]
    have heq : slope (fun y : ℝ => (max 0 y)^2) 0 = fun y => max 0 y := by
      funext y
      rw [slope_fun_def_field]
      by_cases hy : 0 ≤ y
      · simp [max_eq_right hy, pow_two, mul_div_cancel_right₀]
      · simp [max_eq_left (le_of_not_ge hy)]
    rw [heq]
    simpa using ((show Continuous (fun y : ℝ => max 0 y) by fun_prop).continuousAt (x := 0)).tendsto.mono_left (show 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · have heq : (fun y : ℝ => (max 0 y)^2) =ᶠ[𝓝 x] fun y => y^2 := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp [max_eq_right hy.le]
    simpa [max_eq_right hx.le] using ((hasDerivAt_id x).pow 2).congr_of_eventuallyEq heq

private theorem positive_sq_C1 : ContDiff ℝ 1 (fun y : ℝ => (max 0 y)^2) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (positive_sq_deriv x).differentiableAt, ?_⟩
  have heq : deriv (fun y : ℝ => (max 0 y)^2) = fun x => 2 * max 0 x :=
    funext fun x => (positive_sq_deriv x).deriv
  rw [heq]
  fun_prop

private theorem eta_max {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    eta r g = fun z => ((max 0 (z.2 + r * g z.1))^2 - z.2^2) / (2*r) := by
  funext z
  unfold eta phi
  split_ifs with h
  · rw [max_eq_right h]
    field_simp
    <;> ring
  · rw [max_eq_left (le_of_not_ge h)]
    field_simp
    <;> ring

private theorem eta_C1 {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 1 (eta r g) := by
  rw [eta_max r hr g]
  exact ((positive_sq_C1.comp (contDiff_snd.add
    (contDiff_const.mul ((hg.of_le (by norm_num)).comp contDiff_fst)))).sub
    (contDiff_snd.pow 2)).div_const (2*r)

private theorem eta_deriv {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) :
    fderiv ℝ (eta r g) z =
      max 0 (z.2 + r * g z.1) • (fderiv ℝ g z.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
      ((max 0 (z.2 + r * g z.1) - z.2) / r) •
        ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  have hdg := ((hg.differentiable (by norm_num)) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hdt := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).add (hdg.const_mul r)
  have hdp := (positive_sq_deriv (z.2 + r * g z.1)).comp_hasFDerivAt z hdt
  have hd := (hdp.sub ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).pow 2)).mul_const ((2*r)⁻¹)
  rw [eta_max r hr g]
  simp only [div_eq_mul_inv]
  simp only [Function.comp_def, Pi.add_apply, Pi.sub_apply] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst, ContinuousLinearMap.coe_snd, smul_eq_mul]
  norm_num
  field_simp
  <;> ring

private theorem eta_deriv_pos {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : 0 ≤ z.2 + r * g z.1) :
    fderiv ℝ (eta r g) z =
      (z.2 + r * g z.1) • (fderiv ℝ g z.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
      g z.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  rw [eta_deriv r hr g hg z, max_eq_right hz]
  congr 2
  field_simp
  <;> ring

private theorem eta_deriv_neg {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : z.2 + r * g z.1 ≤ 0) :
    fderiv ℝ (eta r g) z =
      (-(z.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  simp [eta_deriv r hr g hg z, max_eq_left hz, neg_div]

private theorem eta_locLip {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g) :
    LocallyLipschitz (fun z => fderiv ℝ (eta r g) z) := by
  let E := EuclideanSpace ℝ (Fin n)
  let P : (E × ℝ) →L[ℝ] E := ContinuousLinearMap.fst ℝ E ℝ
  let S : (E × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ E ℝ
  have hgd : ContDiff ℝ 1 (fun z : E × ℝ => (fderiv ℝ g z.1).comp P) :=
    ((hg.fderiv_right (by norm_num)).comp contDiff_fst).clm_comp contDiff_const
  have ht : ContDiff ℝ 1 (fun z : E × ℝ => z.2 + r * g z.1) := by
    exact contDiff_snd.add (contDiff_const.mul ((hg.of_le (by norm_num)).comp contDiff_fst))
  have hout : ContDiff ℝ 1
      (fun p : ℝ × (((E × ℝ) →L[ℝ] ℝ) × ℝ) =>
        p.1 • p.2.1 + ((p.1 - p.2.2) / r) • S) := by fun_prop
  have hcomb := hout.locallyLipschitz.comp
    ((ht.locallyLipschitz.const_max 0).prodMk
      (hgd.locallyLipschitz.prodMk
        (show ContDiff ℝ 1 (fun z : E × ℝ => z.2) from contDiff_snd).locallyLipschitz))
  have heq : (fun z => fderiv ℝ (eta r g) z) = fun z =>
      max 0 (z.2 + r * g z.1) • (fderiv ℝ g z.1).comp P +
      ((max 0 (z.2 + r * g z.1) - z.2) / r) • S :=
    funext (eta_deriv r hr g hg)
  rw [heq]
  exact hcomb



private theorem eta_positive_neighborhood {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : 0 < z.2 + r * g z.1) :
    (fun w => fderiv ℝ (eta r g) w) =ᶠ[𝓝 z]
      (fun w => (w.2 + r * g w.1) • (fderiv ℝ g w.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
        g w.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) := by
  have ht : Continuous (fun w : EuclideanSpace ℝ (Fin n) × ℝ => w.2 + r * g w.1) := by fun_prop
  filter_upwards [ht.continuousAt.eventually (eventually_gt_nhds hz)] with w hw
  exact eta_deriv_pos r hr g hg w hw.le

private theorem eta_negative_neighborhood {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : z.2 + r * g z.1 < 0) :
    (fun w => fderiv ℝ (eta r g) w) =ᶠ[𝓝 z]
      (fun w => (-(w.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) := by
  have ht : Continuous (fun w : EuclideanSpace ℝ (Fin n) × ℝ => w.2 + r * g w.1) := by fun_prop
  filter_upwards [ht.continuousAt.eventually (eventually_lt_nhds hz)] with w hw
  exact eta_deriv_neg r hr g hg w hw.le

private theorem eta_smooth_positive {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : 0 < z.2 + r * g z.1) :
    ContDiffAt ℝ 1 (fun w => fderiv ℝ (eta r g) w) z := by
  have hgd := hg.fderiv_right (m := 1) (by norm_num)
  have hpos : ContDiff ℝ 1
      (fun w : EuclideanSpace ℝ (Fin n) × ℝ =>
        (w.2 + r * g w.1) • (fderiv ℝ g w.1).comp
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
        g w.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) := by
    exact (contDiff_snd.add (contDiff_const.mul ((hg.of_le (by norm_num)).comp contDiff_fst))).smul
      ((hgd.comp contDiff_fst).clm_comp contDiff_const) |>.add
      (((hg.of_le (by norm_num)).comp contDiff_fst).smul contDiff_const)
  exact hpos.contDiffAt.congr_of_eventuallyEq (eta_positive_neighborhood r hr g hg z hz)

private theorem eta_smooth_negative {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : z.2 + r * g z.1 < 0) :
    ContDiffAt ℝ 1 (fun w => fderiv ℝ (eta r g) w) z := by
  have hneg : ContDiff ℝ 1
      (fun w : EuclideanSpace ℝ (Fin n) × ℝ =>
        (-(w.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) := by fun_prop
  exact hneg.contDiffAt.congr_of_eventuallyEq (eta_negative_neighborhood r hr g hg z hz)

private theorem eta_hessian_positive {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : 0 < z.2 + r * g z.1)
    (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    fderiv ℝ (fun w => fderiv ℝ (eta r g) w) z v =
      (r * fderiv ℝ g z.1 v.1 + v.2) • (fderiv ℝ g z.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
      (z.2 + r * g z.1) • (fderiv ℝ (fun u => fderiv ℝ g u) z.1 v.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
      fderiv ℝ g z.1 v.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  have hdg := ((hg.differentiable (by norm_num)) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hdD := (((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hB := hdD.clm_comp (hasFDerivAt_const
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) z)
  have hA := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).add (hdg.const_mul r)
  have hd := (hA.smul hB).add (hdg.smul_const
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ))
  rw [(eta_positive_neighborhood r hr g hg z hz).fderiv_eq]
  simp only [Function.comp_def, Pi.add_def, Pi.smul_def'] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp [mul_comm]
  <;> ring_nf
  <;> simp

private theorem eta_hessian_negative {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : z.2 + r * g z.1 < 0)
    (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    fderiv ℝ (fun w => fderiv ℝ (eta r g) w) z v =
      (-(v.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  have hd := ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).mul_const r⁻¹).neg.smul_const
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  rw [(eta_negative_neighborhood r hr g hg z hz).fderiv_eq]
  simp only [div_eq_mul_inv]
  simp only [Pi.neg_apply] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp [mul_comm]
  <;> ring_nf
  <;> simp



private theorem eta_not_differentiable_surface {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) (hz : z.2+r*g z.1=0) :
    ¬ DifferentiableAt ℝ (fun w => fderiv ℝ (eta r g) w) z := by
  intro hd
  let E := EuclideanSpace ℝ (Fin n)
  have hp : DifferentiableAt ℝ (fun t : ℝ => (z.1,z.2+t)) 0 := by fun_prop
  have hcomp : DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ (eta r g) (z.1,z.2+t)) 0 := by
    have hdz : DifferentiableAt ℝ (fun w => fderiv ℝ (eta r g) w) (z.1,z.2+0) := by simpa using hd
    exact hdz.comp 0 hp
  have hc : DifferentiableAt ℝ (fun _ : ℝ => ((0,1) : E × ℝ)) 0 := by fun_prop
  have heval := hcomp.clm_apply hc
  have hlin : DifferentiableAt ℝ (fun t : ℝ => z.2+t) 0 := by fun_prop
  have hm := (heval.const_mul r).add hlin
  have heq : (fun t : ℝ => r*(fderiv ℝ (eta r g) (z.1,z.2+t) ((0,1) : E × ℝ))+(z.2+t)) =
      (fun t : ℝ => max 0 t) := by
    funext t
    rw [eta_deriv r hr g hg]
    have ht : (z.2+t)+r*g z.1=t := by linarith
    simp [ht,ContinuousLinearMap.comp_apply]
    field_simp
    <;> ring
  have hm' : DifferentiableAt ℝ (fun t : ℝ => max 0 t) 0 := by
    rw [← heq]
    exact hm
  have habs := (hm'.const_mul 2).sub (differentiableAt_id (𝕜 := ℝ) (x := (0 : ℝ)))
  apply not_differentiableAt_abs_zero
  convert! habs using 1
  funext t
  by_cases ht : 0 ≤ t
  · simp [max_eq_right ht,abs_of_nonneg ht]
    <;> ring
  · simp [max_eq_left (le_of_not_ge ht),abs_of_neg (lt_of_not_ge ht)]



private theorem bJac_two_branches {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f p m : E → F) (q : E → ℝ) (hp : ContDiff ℝ 1 p) (hm : ContDiff ℝ 1 m)
    (hq : Continuous q)
    (hbranch : ∀ x,DifferentiableAt ℝ f x →
      (0 < q x ∧ fderiv ℝ f x=fderiv ℝ p x) ∨ (q x < 0 ∧ fderiv ℝ f x=fderiv ℝ m x))
    (x : E) (V : E →L[ℝ] F) (hV : V ∈ bJac f x) :
    (0 ≤ q x ∧ V=fderiv ℝ p x) ∨ (q x ≤ 0 ∧ V=fderiv ℝ m x) := by
  have hclosed : IsClosed {a : E × (E →L[ℝ] F) |
      (0 ≤ q a.1 ∧ a.2=fderiv ℝ p a.1) ∨ (q a.1 ≤ 0 ∧ a.2=fderiv ℝ m a.1)} :=
    ((isClosed_le continuous_const (hq.comp continuous_fst)).inter
      (isClosed_eq continuous_snd ((hp.continuous_fderiv one_ne_zero).comp continuous_fst))).union
    ((isClosed_le (hq.comp continuous_fst) continuous_const).inter
      (isClosed_eq continuous_snd ((hm.continuous_fderiv one_ne_zero).comp continuous_fst)))
  obtain ⟨u,hu,hdu,hVu⟩ := hV
  apply hclosed.mem_of_tendsto (hu.prodMk_nhds hVu)
  exact Eventually.of_forall fun k => (hbranch (u k) (hdu k)).elim
    (fun h => Or.inl ⟨h.1.le,h.2⟩) (fun h => Or.inr ⟨h.1.le,h.2⟩)

private theorem clarke_norm_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x v : E) (L : F) (eps : ℝ)
    (hb : ∀ V ∈ bJac f x,‖V v-L‖ ≤ eps)
    (V : E →L[ℝ] F) (hV : V ∈ clarkeJac f x) : ‖V v-L‖ ≤ eps := by
  have hcv : Convex ℝ {W : E →L[ℝ] F | ‖W v-L‖ ≤ eps} := by
    convert! (convex_closedBall L eps).linear_preimage
      ((ContinuousLinearMap.apply ℝ F v).toLinearMap) using 1
    ext W
    simp [Metric.mem_closedBall,dist_eq_norm]
  exact convexHull_min hb hcv hV



private theorem direction_positive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : E → ℝ) (x h : E) (Q : E →L[ℝ] ℝ) (hq : HasFDerivAt q Q x)
    (hx : q x=0) (hh : 0 < Q h) :
    ∃ δ > 0,∀ (t : ℝ) (v : E),0 < t → t < δ → ‖v-h‖ < δ → 0 < q (x+t • v) := by
  let H := ‖h‖+1
  let K := ‖Q‖+1
  have hH : 0 < H := by dsimp [H]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : 0 < Q h/(4*H) := by positivity
  have hev := hq.isLittleO.bound hc
  obtain ⟨d,hd,hdb⟩ := Metric.eventually_nhds_iff.mp hev
  let δ := min 1 (min (d/H) (Q h/(4*K)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,hδ,?_⟩
  intro t v ht htδ hvδ
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδd : δ ≤ d/H := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ ≤ Q h/(4*K) := (min_le_right _ _).trans (min_le_right _ _)
  have hv : ‖v‖ ≤ H := by
    have hn := norm_le_norm_sub_add v h
    dsimp [H]
    linarith
  have hdist : dist (x+t • v) x < d := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    exact (mul_le_mul_of_nonneg_left hv ht.le).trans_lt
      ((lt_div_iff₀ hH).mp (htδ.trans_le hδd))
  have herr := hdb hdist
  simp only [hx,sub_zero,add_sub_cancel_left,map_smul,smul_eq_mul,norm_smul,
    Real.norm_eq_abs,abs_of_pos ht] at herr
  have hQ : ‖Q (v-h)‖ ≤ Q h/4 := by
    apply (Q.le_opNorm (v-h)).trans
    calc
      ‖Q‖*‖v-h‖ ≤ K*(Q h/(4*K)) := mul_le_mul
        (by dsimp [K]; linarith) (hvδ.le.trans hδc) (norm_nonneg _) hK.le
      _ = Q h/4 := by field_simp
  rw [map_sub,Real.norm_eq_abs] at hQ
  have hQlow := (abs_le.mp hQ).1
  have herlow := (abs_le.mp herr).1
  have hscale : Q h/(4*H)*(t*‖v‖) ≤ t*(Q h/4) := by
    calc
      Q h/(4*H)*(t*‖v‖) ≤ Q h/(4*H)*(t*H) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv ht.le) hc.le
      _ = t*(Q h/4) := by field_simp
  have hp : 0 < t*(Q h/2) := by positivity
  nlinarith

private theorem derivative_action_near {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E → F) (hp : ContDiff ℝ 1 p) (x h : E) (eps : ℝ) (heps : 0 < eps) :
    ∃ δ > 0,∀ (t : ℝ) (v : E),0 < t → t < δ → ‖v-h‖ < δ →
      ‖fderiv ℝ p (x+t • v) v-fderiv ℝ p x h‖ < eps := by
  have hc : Continuous (fun a : ℝ × E => fderiv ℝ p (x+a.1 • a.2) a.2) := by
    exact (hp.continuous_fderiv one_ne_zero).comp (by fun_prop) |>.clm_apply continuous_snd
  obtain ⟨δ,hδ,hd⟩ := (Metric.continuousAt_iff.mp hc.continuousAt) eps heps
  refine ⟨δ,hδ,?_⟩
  intro t v ht htd hvd
  have hh : dist (t,v) (0,h) < δ := by
    simpa [Prod.dist_eq,Real.dist_eq,abs_of_pos ht,dist_eq_norm] using max_lt htd hvd
  simpa [dist_eq_norm] using hd hh



private theorem two_branch_semismooth {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f p m : E → F) (q : E → ℝ) (hp : ContDiff ℝ 1 p) (hm : ContDiff ℝ 1 m)
    (hq : Continuous q)
    (hbranch : ∀ z,DifferentiableAt ℝ f z →
      (0 < q z ∧ fderiv ℝ f z=fderiv ℝ p z) ∨ (q z < 0 ∧ fderiv ℝ f z=fderiv ℝ m z))
    (x : E) (Q : E →L[ℝ] ℝ) (hdq : HasFDerivAt q Q x) (hx : q x=0)
    (hagree : ∀ h,Q h=0 → fderiv ℝ p x h=fderiv ℝ m x h)
    (hLip : ∃ K : NNReal,∃ U ∈ 𝓝 x,LipschitzOnWith K f U) :
    SemismoothAt f x := by
  refine ⟨hLip,?_⟩
  intro h
  rcases lt_trichotomy (Q h) 0 with hneg | hzero | hpos
  · refine ⟨fderiv ℝ m x h,?_⟩
    intro eps heps
    obtain ⟨d,hd,hds⟩ := direction_positive (fun z => -q z) x h (-Q) hdq.neg
      (by simp [hx]) (by simpa using neg_pos.mpr hneg)
    obtain ⟨e,he,hes⟩ := derivative_action_near m hm x h (eps/2) (by positivity)
    refine ⟨min d e,lt_min hd he,?_⟩
    intro t v ht htd hvd V hV
    have hqt : q (x+t • v) < 0 := by
      have hh := hds t v ht (htd.trans_le (min_le_left _ _)) (hvd.trans_le (min_le_left _ _))
      linarith
    have hnorm := hes t v ht (htd.trans_le (min_le_right _ _)) (hvd.trans_le (min_le_right _ _))
    have hb : ∀ W ∈ bJac f (x+t • v),‖W v-fderiv ℝ m x h‖ ≤ eps/2 := by
      intro W hW
      rcases bJac_two_branches f p m q hp hm hq hbranch (x+t • v) W hW with hpW | hmW
      · linarith [hpW.1]
      · simpa [hmW.2] using hnorm.le
    have hbV := clarke_norm_bound f (x+t • v) v (fderiv ℝ m x h) (eps/2) hb V hV
    linarith
  · refine ⟨fderiv ℝ p x h,?_⟩
    intro eps heps
    obtain ⟨d,hd,hds⟩ := derivative_action_near p hp x h (eps/2) (by positivity)
    obtain ⟨e,he,hes⟩ := derivative_action_near m hm x h (eps/2) (by positivity)
    refine ⟨min d e,lt_min hd he,?_⟩
    intro t v ht htd hvd V hV
    have hpnear := hds t v ht (htd.trans_le (min_le_left _ _)) (hvd.trans_le (min_le_left _ _))
    have hmnear := hes t v ht (htd.trans_le (min_le_right _ _)) (hvd.trans_le (min_le_right _ _))
    have hb : ∀ W ∈ bJac f (x+t • v),‖W v-fderiv ℝ p x h‖ ≤ eps/2 := by
      intro W hW
      rcases bJac_two_branches f p m q hp hm hq hbranch (x+t • v) W hW with hpW | hmW
      · simpa [hpW.2] using hpnear.le
      · simpa [hmW.2,hagree h hzero] using hmnear.le
    have hbV := clarke_norm_bound f (x+t • v) v (fderiv ℝ p x h) (eps/2) hb V hV
    linarith
  · refine ⟨fderiv ℝ p x h,?_⟩
    intro eps heps
    obtain ⟨d,hd,hds⟩ := direction_positive q x h Q hdq hx hpos
    obtain ⟨e,he,hes⟩ := derivative_action_near p hp x h (eps/2) (by positivity)
    refine ⟨min d e,lt_min hd he,?_⟩
    intro t v ht htd hvd V hV
    have hqt := hds t v ht (htd.trans_le (min_le_left _ _)) (hvd.trans_le (min_le_left _ _))
    have hnorm := hes t v ht (htd.trans_le (min_le_right _ _)) (hvd.trans_le (min_le_right _ _))
    have hb : ∀ W ∈ bJac f (x+t • v),‖W v-fderiv ℝ p x h‖ ≤ eps/2 := by
      intro W hW
      rcases bJac_two_branches f p m q hp hm hq hbranch (x+t • v) W hW with hpW | hmW
      · simpa [hpW.2] using hnorm.le
      · linarith [hmW.1]
    have hbV := clarke_norm_bound f (x+t • v) v (fderiv ℝ p x h) (eps/2) hb V hV
    linarith



private theorem branch_hessian_positive {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) 
    (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) × ℝ =>
        (w.2 + r * g w.1) • (fderiv ℝ g w.1).comp
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
        g w.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) z v =
      (r * fderiv ℝ g z.1 v.1 + v.2) • (fderiv ℝ g z.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
      (z.2 + r * g z.1) • (fderiv ℝ (fun u => fderiv ℝ g u) z.1 v.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) +
      fderiv ℝ g z.1 v.1 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  have hdg := ((hg.differentiable (by norm_num)) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hdD := (((hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) z.1).hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hB := hdD.clm_comp (hasFDerivAt_const
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) z)
  have hA := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).add (hdg.const_mul r)
  have hd := (hA.smul hB).add (hdg.smul_const
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ))
  simp only [Function.comp_def, Pi.add_def, Pi.smul_def'] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp [mul_comm]
  <;> ring_nf
  <;> simp

private theorem branch_hessian_negative {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (z : EuclideanSpace ℝ (Fin n) × ℝ) 
    (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) × ℝ =>
        (-(w.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) z v =
      (-(v.2 / r)) • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ := by
  have hd := ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).mul_const r⁻¹).neg.smul_const
    (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
  simp only [div_eq_mul_inv]
  simp only [Pi.neg_apply] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.ext
  intro w
  simp [mul_comm]
  <;> ring_nf
  <;> simp




theorem _root_.solution {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 2 g)
    (xbar : EuclideanSpace ℝ (Fin n)) (sbar : ℝ)
    (h43 : sbar+r*g xbar=0) :
    SemismoothAt (fun w => fderiv ℝ (eta r g) w) (xbar,sbar) := by
  let E := EuclideanSpace ℝ (Fin n)
  let z : E × ℝ := (xbar,sbar)
  let P := ContinuousLinearMap.fst ℝ E ℝ
  let S := ContinuousLinearMap.snd ℝ E ℝ
  let p : E × ℝ → ((E × ℝ) →L[ℝ] ℝ) := fun w =>
    (w.2+r*g w.1) • (fderiv ℝ g w.1).comp P+g w.1 • S
  let m : E × ℝ → ((E × ℝ) →L[ℝ] ℝ) := fun w => -(w.2/r) • S
  let q : E × ℝ → ℝ := fun w => w.2+r*g w.1
  let Q : (E × ℝ) →L[ℝ] ℝ := S+r • (fderiv ℝ g xbar).comp P
  have hgd : ContDiff ℝ 1 (fun u => fderiv ℝ g u) := hg.fderiv_right (by norm_num)
  have hp : ContDiff ℝ 1 p := by
    exact (contDiff_snd.add (contDiff_const.mul ((hg.of_le (by norm_num)).comp contDiff_fst))).smul
      ((hgd.comp contDiff_fst).clm_comp contDiff_const) |>.add
      (((hg.of_le (by norm_num)).comp contDiff_fst).smul contDiff_const)
  have hm : ContDiff ℝ 1 m := by dsimp [m]; fun_prop
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hdg := ((hg.differentiable (by norm_num)) xbar).hasFDerivAt.comp z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  have hdq : HasFDerivAt q Q z := by
    exact (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).add (hdg.const_mul r)
  have hbranch : ∀ w,DifferentiableAt ℝ (fun u => fderiv ℝ (eta r g) u) w →
      (0 < q w ∧ fderiv ℝ (fun u => fderiv ℝ (eta r g) u) w=fderiv ℝ p w) ∨
      (q w < 0 ∧ fderiv ℝ (fun u => fderiv ℝ (eta r g) u) w=fderiv ℝ m w) := by
    intro w hd
    have hne : q w ≠ 0 := fun hh => eta_not_differentiable_surface r hr g hg w hh hd
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact Or.inr ⟨hneg,(eta_negative_neighborhood r hr g hg w hneg).fderiv_eq⟩
    · exact Or.inl ⟨hpos,(eta_positive_neighborhood r hr g hg w hpos).fderiv_eq⟩
  have hagree : ∀ h,Q h=0 → fderiv ℝ p z h=fderiv ℝ m z h := by
    intro h hh
    have ht : r*fderiv ℝ g xbar h.1+h.2=0 := by
      simpa [Q,S,P,ContinuousLinearMap.comp_apply,add_comm] using hh
    dsimp [p,m,P,S]
    rw [branch_hessian_positive r hr g hg z h,branch_hessian_negative r hr g hg z h]
    have hz : z.2+r*g z.1=0 := h43
    have htt : r*fderiv ℝ g z.1 h.1+h.2=0 := ht
    simp only [htt,hz,zero_smul,zero_add]
    congr 1
    dsimp [z]
    rw [← neg_div]
    apply (eq_div_iff (ne_of_gt hr)).2
    nlinarith
  exact two_branch_semismooth _ p m q hp hm hq hbranch z Q hdq h43 hagree
    (eta_locLip r hr g hg z)

end NonsmoothNewton.AugLagrangian
