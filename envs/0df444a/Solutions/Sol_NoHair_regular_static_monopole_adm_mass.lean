-- Prove2me | solution 1 for NoHair.regular_static_monopole_adm_mass
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:47:48.597386+00:00
-- url     : https://prove2.me/submissions/6f5b6a98-21eb-40eb-986e-5c5a11a7ec04

import Theorems.Thm_NoHair_regular_static_slice_field_equations
import Theorems.Thm_NoHair_regular_static_horizon_surface_gravity
import Theorems.Thm_NoHair_regular_static_vacuum_adm_lapse_flux
import Theorems.Thm_NoHair_regular_static_lapse_euclidean_poisson_source
import Theorems.Thm_NoHair_inverse_radius_limit_of_decaying_poisson_field
import Theorems.Thm_HunterPDE_Harmonic_sphereAverage_radial_eq_ball_laplacian
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open NoHair MeasureTheory Metric Set Filter Laplacian
open scoped Topology ContDiff Manifold

private abbrev X := ADMPoint

private lemma area_three : 3*volume.real (ball (0:X) 1)=4*Real.pi := by
  rw [measureReal_def,EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  ring

private lemma decompose_covector (L : X →L[ℝ] ℝ) (v : X) :
    L v=∑ i : Fin 3,L (EuclideanSpace.single i 1)*v i := by
  have e : (∑ i : Fin 3,v i • (EuclideanSpace.single i 1 : X))=v := by
    ext j
    simp [PiLp.smul_apply,PiLp.single_apply,Pi.single_apply,ite_mul,mul_ite]
  calc
    _ = L (∑ i : Fin 3,v i • (EuclideanSpace.single i 1 : X)) := congrArg L e.symm
    _ = _ := by simp [mul_comm]

private lemma density (N : X → ℝ) (r : ℝ) (n : ADMSphere) :
    staticLapseDensity N r n=r^2*fderiv ℝ N (r • (n:X)) (n:X) := by
  rw [decompose_covector,Finset.mul_sum]
  simp only [staticLapseDensity,spatialADMPartial,mul_assoc]

private lemma source_flux {N u : X → ℝ} (cu : ContDiff ℝ 2 u)
    (he : ∀ᶠ x in cocompact X, u x=1-N x) (qi : Integrable (fun z => -(Δ u) z)) :
    Tendsto (staticLapseFlux N) atTop (𝓝 ((∫ z, -(Δ u) z)/(4*Real.pi))) := by
  let q:=fun z => -(Δ u) z
  rw [←Metric.cobounded_eq_cocompact,←comap_norm_atTop,eventually_comap] at he
  obtain ⟨B,hB⟩:=eventually_atTop.mp he
  have loc {x : X} (hx : B<‖x‖) : u =ᶠ[𝓝 x] (fun y => 1-N y) := by
    have big : ∀ᶠ y : X in 𝓝 x, B<‖y‖ := (continuous_norm.tendsto x) (isOpen_Ioi.mem_nhds hx)
    exact big.mono fun y hy => hB ‖y‖ hy.le y rfl
  have tv : Tendsto (fun r : ℝ => ∫ z in ball (0:X) r,q z) atTop (𝓝 (∫ z,q z)) := by
    have e:=tendsto_setIntegral_of_monotone (μ:=volume) (f:=q) (s:=fun r : ℝ => ball (0:X) r)
      (fun _ => measurableSet_ball) (fun _ _ h => ball_subset_ball h) qi.integrableOn
    have full : (⋃ r : ℝ,ball (0:X) r)=univ := by
      ext x; simp only [mem_iUnion,mem_ball,dist_zero_right,mem_univ,iff_true]; exact ⟨‖x‖+1,by linarith⟩
    simpa only [full,Measure.restrict_univ] using e
  have Vp : 0<volume.real (ball (0:X) 1) :=
    ENNReal.toReal_pos (measure_ball_pos _ _ zero_lt_one).ne' (measure_ball_lt_top ..).ne
  apply (tv.div_const (4*Real.pi)).congr'
  filter_upwards [eventually_gt_atTop (max B 0)] with r hr
  obtain ⟨rb,rp⟩:=max_lt_iff.mp hr
  have extD (n : ADMSphere) : fderiv ℝ u (0+r • (n:X)) (n:X) = -fderiv ℝ N (r • (n:X)) (n:X) := by
    have nr : ‖r • (n:X)‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos rp,mem_sphere_zero_iff_norm.mp n.property,mul_one]
    have eq := (loc (x:=r • (n:X)) (nr.symm ▸ rb)).fderiv_eq (𝕜:=ℝ)
    rw [zero_add,eq,fderiv_const_sub]; rfl
  have eq:=HunterPDE.Harmonic.sphereAverage_radial_eq_ball_laplacian (n:=3) (by decide) (x:=(0:X)) rp
    (fun y _ => cu.contDiffAt (x:=y))
  rw [average_eq,setAverage_eq] at eq
  simp_rw [extD] at eq
  rw [integral_neg,Measure.toSphere_real_apply_univ] at eq
  simp only [smul_eq_mul,finrank_euclideanSpace,Fintype.card_fin] at eq
  have vr : volume.real (ball (0:X) r) = r^3*volume.real (ball (0:X) 1) := by
    rw [measureReal_def,volume.addHaar_ball_of_pos _ rp,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)]
    simp [measureReal_def,finrank_euclideanSpace]
  rw [vr] at eq
  change (∫ z in ball (0:X) r,-(Δ u) z)/(4*Real.pi)=staticLapseFlux N r
  unfold staticLapseFlux
  simp_rw [density N r]
  rw [integral_const_mul,integral_neg]
  congr 1
  push_cast at eq
  field_simp [Vp.ne',rp.ne'] at eq
  linarith only [eq]

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ,E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    ∃ μ : ℝ, 0 < μ ∧ HasStaticLapseMonopole c.N μ ∧
      Tendsto (staticLapseFlux c.N) atTop (𝓝 μ) ∧ Tendsto (staticADMFlux c.h) atTop (𝓝 μ) := by
  have heq:=regular_static_slice_field_equations g φ D c
  let e : RegularRiemannianStaticEnd c.Ω c.W c.N c.h :=
    ⟨c.openSlice,c.connectedSlice,c.compactComplement,c.hasBoundary,c.connectedBoundary,c.openExtension,
      c.extendsAcross,c.positiveSide,c.horizon,c.smoothLapse,c.smoothMetric,c.positiveMetric,c.falloff,
      heq,regular_static_horizon_surface_gravity g φ D c heq⟩
  obtain ⟨u,cu,he,h0,qi,hd,pos⟩:=regular_static_lapse_euclidean_poisson_source c.Ω c.W c.N c.h e
  let μ:=(∫ z, -(Δ u) z)/(4*Real.pi)
  have hc:=inverse_radius_limit_of_decaying_poisson_field u cu h0 qi hd
  rw [area_three] at hc
  have hf:=source_flux cu he qi
  refine ⟨μ,div_pos pos (by positivity),hc.congr' (he.mono (fun x hx => congrArg (‖x‖ * ·) hx)),hf,?_⟩
  have ha : Tendsto (fun r => (staticADMFlux c.h r-staticLapseFlux c.N r)+staticLapseFlux c.N r)
      atTop (𝓝 (0+μ)) := (regular_static_vacuum_adm_lapse_flux g φ D c).add hf
  simpa only [sub_add_cancel,zero_add] using ha
