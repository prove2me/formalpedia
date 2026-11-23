-- Prove2me | solution 1 for NoHair.bounded_differential_punctured_ball_has_unique_limit
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:09:01.325894+00:00
-- url     : https://prove2.me/submissions/bbdcb46c-579d-4e83-8cda-cf622d2fce23

import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Geometry.Manifold.Instances.Icc
import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Manifold MeasureTheory Metric UniformSpace Module
open scoped ENNReal NNReal
private abbrev X := ADMPoint
private abbrev I := 𝓘(ℝ,X)
private abbrev J := 𝓘(ℝ,ℝ)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem solution (Q : Type) [MetricSpace Q] [ChartedSpace ADMPoint Q] [IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] (f : ADMPoint → Q) (r K : ℝ) (hr : 0<r) (hk : 0<K)
    (sm : ContMDiffOn 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) 1 f (Metric.ball 0 r ∩ ({0}:Set ADMPoint)ᶜ))
    (bd : ∀ x ∈ Metric.ball (0:ADMPoint) r ∩ ({0}:Set ADMPoint)ᶜ, ∀ v : ADMPoint,
      ‖mfderiv 𝓘(ℝ,ADMPoint) 𝓘(ℝ,ADMPoint) f x v‖ ≤ K*‖v‖) :
    ∃ p : UniformSpace.Completion Q, Tendsto (fun x => (f x : UniformSpace.Completion Q))
      (𝓝[≠] (0:ADMPoint)) (𝓝 p) := by
  classical
  let S := (ball (0:X) r) ∩ ({0}:Set X)ᶜ
  have op : IsOpen S := isOpen_ball.inter isOpen_compl_singleton
  have chord (x z : X) (inside : segment ℝ x z ⊆ S) : dist (f x) (f z) ≤ K*dist x z := by
    let γ := ContinuousAffineMap.lineMap (R:=ℝ) x z
    have path (t:ℝ) (ht : t∈Icc 0 1) : γ t∈S := by
      apply inside
      rw [segment_eq_image_lineMap]
      exact ⟨t,ht,rfl⟩
    have cg : ContMDiff J I 1 γ := contMDiff_iff_contDiff.mpr γ.contDiff
    have smth : ContMDiffOn J I 1 (f ∘ γ) (Icc 0 1) := sm.comp cg.contMDiffOn path
    have len := riemannianEDist_le_pathELength (I:=I) smth
      (show (f ∘ γ) 0=f x by simp [γ,ContinuousAffineMap.coe_lineMap_eq])
      (show (f ∘ γ) 1=f z by simp [γ,ContinuousAffineMap.coe_lineMap_eq]) zero_le_one
    rw [←IsRiemannianManifold.out] at len
    have speed (t:ℝ) (ht : t∈Icc 0 1) :
        ‖mfderiv J I (f ∘ γ) t 1‖ₑ ≤ ENNReal.ofReal (K*dist x z) := by
      have df := (sm.contMDiffAt (op.mem_nhds (path t ht))).mdifferentiableAt one_ne_zero
      have chain := mfderiv_comp (I':=I) t df (cg.contMDiffAt.mdifferentiableAt one_ne_zero)
      have c1 := congrArg (fun L : ℝ →L[ℝ] TangentSpace I (f (γ t)) => ‖L 1‖) chain
      change ‖mfderiv J I (f ∘ γ) t 1‖ =
        ‖mfderiv I I f (γ t) (mfderiv J I γ t 1)‖ at c1
      have vel : fderiv ℝ γ t 1=z-x := by simp [γ]
      have dval : (mfderiv J I γ t : ℝ →L[ℝ] X) = fderiv ℝ γ t := mfderiv_eq_fderiv
      have v' := (congrArg (fun L : ℝ →L[ℝ] X => L 1) dval).trans vel
      have c2 := congrArg (fun u:X => ‖mfderiv I I f (γ t) u‖) v'
      have hbd := (c1.trans c2).le.trans (bd (γ t) (path t ht) (z-x))
      simpa only [ofReal_norm,dist_eq_norm'] using ENNReal.ofReal_le_ofReal hbd
    rw [pathELength_eq_lintegral_mfderiv_Icc] at len
    have up : (∫⁻ t in Icc (0:ℝ) 1, ‖mfderiv J I (f ∘ γ) t 1‖ₑ) ≤
        ∫⁻ _t in Icc (0:ℝ) 1, ENNReal.ofReal (K*dist x z) :=
      setLIntegral_mono' measurableSet_Icc speed
    have b := len.trans up
    simpa only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,sub_zero,
      ENNReal.ofReal_one,mul_one,edist_dist,ENNReal.ofReal_le_ofReal_iff (mul_nonneg hk.le dist_nonneg)] using b
  have osc {s : ℝ} (sp : 0<s) (sr : s≤r) {x y : X} (xs : ‖x‖<s) (ys : ‖y‖<s) (xn : x≠0) (yn : y≠0) :
      dist (f x) (f y) ≤ 4*K*s := by
    let t : Finset X := {x,y}
    let P := Submodule.span ℝ (t:Set X)
    have cp : Module.finrank ℝ P ≤ 2 := (finrank_span_finset_le_card (R:=ℝ) t).trans (by
      by_cases he : x=y <;> simp [t,he])
    have proper : P ≠ ⊤ := by
      intro all
      rw [all,finrank_top] at cp
      norm_num at cp
    obtain ⟨w,hw⟩ := SetLike.exists_not_mem_of_ne_top P proper rfl
    have wn : w ≠ 0 := fun eq => hw (eq ▸ P.zero_mem)
    let z := (s/(2*‖w‖)) • w
    have wp := norm_pos_iff.mpr wn
    have zp : s/(2*‖w‖)≠0 := (div_pos sp (by positivity)).ne'
    have wz : z ∉ P := fun hz => hw ((P.smul_mem_iff zp).mp hz)
    have nz : ‖z‖=s/2 := by
      rw [show ‖z‖=‖(s/(2*‖w‖)) • w‖ from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos sp (by positivity))]
      field_simp [wp.ne']
    have inside {a:X} (ap : a∈P) (an : a≠0) (ar : ‖a‖<s) : segment ℝ a z ⊆ S := by
      intro v hv
      refine ⟨(convex_ball (0:X) r).segment_subset (mem_ball_zero_iff.mpr (ar.trans_le sr))
        (mem_ball_zero_iff.mpr (by rw [nz]; linarith)) hv,?_⟩
      change v≠0
      rw [segment_eq_image_lineMap] at hv
      obtain ⟨b,hb,rfl⟩ := hv
      by_cases hzero : b=0
      · simpa [hzero] using an
      · intro eq
        have mem : b • z ∈ P := by
          have m := P.sub_mem (show AffineMap.lineMap a z b ∈ P from eq ▸ P.zero_mem) (P.smul_mem (1-b) ap)
          simpa only [AffineMap.lineMap_apply_module,add_sub_cancel_left] using m
        exact wz ((P.smul_mem_iff hzero).mp mem)
    have xx : x∈P := Submodule.subset_span (by simp [t])
    have yy : y∈P := Submodule.subset_span (by simp [t])
    have h := dist_triangle (f x) (f z) (f y)
    rw [dist_comm (f z) (f y)] at h
    apply h.trans
    apply (add_le_add (chord x z (inside xx xn xs)) (chord y z (inside yy yn ys))).trans
    have zx := dist_le_norm_add_norm x z
    have zy := dist_le_norm_add_norm y z
    nlinarith only [mul_le_mul_of_nonneg_left zx hk.le,mul_le_mul_of_nonneg_left zy hk.le,
      mul_lt_mul_of_pos_left xs hk,mul_lt_mul_of_pos_left ys hk,congrArg (fun a:ℝ => K*a) nz,mul_pos hk sp]
  apply cauchy_map_iff_exists_tendsto.mp
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance,?_⟩
  intro ε ep
  let s := min r (ε/(8*K))
  have sp : 0<s := lt_min hr (div_pos ep (by positivity))
  let U := ball (0:X) s ∩ ({0}:Set X)ᶜ
  have nu : U ∈ 𝓝[≠] (0:X) := inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ sp)) self_mem_nhdsWithin
  let F := fun t : X => (f t : Completion Q)
  refine ⟨F '' U,Filter.image_mem_map nu,?_⟩
  rintro _ ⟨x,⟨hx,nx⟩,rfl⟩ _ ⟨y,⟨hy,ny⟩,rfl⟩
  change dist (f x : Completion Q) (f y : Completion Q)<ε
  rw [Completion.dist_eq]
  apply (osc sp (min_le_left _ _) (mem_ball_zero_iff.mp hx) (mem_ball_zero_iff.mp hy) nx ny).trans_lt
  have h := (le_div_iff₀ (by positivity : 0<8*K)).mp (min_le_right r (ε/(8*K)))
  linarith only [h,ep,mul_comm s K]
