-- Prove2me | solution 1 for OAI.RVM.family_bounded_classical_prefix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:25:50.47798+00:00
-- url     : https://prove2.me/submissions/a70b84ac-84c1-411e-8cbc-3edb5508e5c8

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_C1ClassicalPrefix_smooth
import Theorems.Thm_OAI_RVM_family_local_spatially_smooth_bounded_classical

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

lemma q_sq (v : Vec) : q v ^ 2 = 1 + ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_lt_q (v : Vec) : ‖v‖ < q v := by
  have hp := q_pos v
  have hs := q_sq v
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

lemma norm_velocity_lt_one (v : Vec) : ‖velocity v‖ < 1 := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (q_pos v))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (q_pos v)).2 (norm_lt_q v)

lemma dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_sub_right (a b c : Vec) : dot a (b - c) = dot a b - dot a c := by
  rw [dot_comm, dot_sub_left, dot_comm b a, dot_comm c a]

lemma dot_smul_right (r : ℝ) (a b : Vec) : dot a (r • b) = r * dot a b := by
  rw [dot_comm, dot_smul_left, dot_comm b a]

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ExtendedLorentz
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

lemma contDiff_cross {k : ℕ∞ω} : ContDiff ℝ k (fun z : Vec × Vec => cross z.1 z.2) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 1 * z.2 2 - z.1 2 * z.2 1)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 2 * z.2 0 - z.1 0 * z.2 2)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 0 * z.2 1 - z.1 1 * z.2 0)
    fun_prop

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_EnergyBump
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma continuousOn_integral_uniform_support
    {H W : Type*} [TopologicalSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hK : IsCompact K) (hF : ContinuousOn F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContinuousOn (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := continuousOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) continuousOn_const (g := fun x v => F (x,v))
    hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_NullConeFlux
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise

namespace RVM

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_BallCutoff
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma hasFDerivAt_integral_sphere
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ 1 F) (p : H) :
    HasFDerivAt (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure)
      (∫ n : Sphere, (fderiv ℝ F (p,n.1)).comp (ContinuousLinearMap.inl ℝ H Vec)
        ∂sphereMeasure) p := by
  let D : H × Sphere → H →L[ℝ] W := fun z =>
    (fderiv ℝ F (z.1,z.2.1)).comp (ContinuousLinearMap.inl ℝ H Vec)
  have hD : Continuous D := by
    exact ((hF.continuous_fderiv (by simp)).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall p 1) (bound:=fun _ => C) (F':=fun x n => D (x,n))
    (closedBall_mem_nhds p (by norm_num))
  · exact Eventually.of_forall (fun x => (hF.continuous.comp
      (continuous_const.prodMk continuous_subtype_val)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun n x hx => hC _ ⟨(x,n),⟨hx,mem_univ n⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun n x _ => (hF.differentiable (by simp) (x,n.1)).hasFDerivAt.comp x
      (by convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const n.1 x) using 1 <;> rfl))

lemma continuous_integral_sphere
    {H W : Type*} [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : H × Vec → W} (hF : Continuous F) :
    Continuous (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  have hc : Continuous (fun p : H × Sphere => F (p.1,p.2.1)) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hc.continuousOn
  intro x n _ hn
  exact (hn (mem_univ n)).elim

lemma contDiff_integral_sphere_nat
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    (k : ℕ) : ∀ {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W}, ContDiff ℝ k F →
      ContDiff ℝ k (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  induction k with
  | zero =>
    intro W _ _ _ F hF
    exact contDiff_zero.mpr (continuous_integral_sphere hF.continuous)
  | succ k ih =>
    intro W _ _ _ F hF
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by exact_mod_cast Nat.succ_pos k)
    let D : H × Vec → H →L[ℝ] W := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H Vec)
    have hD : ContDiff ℝ k D :=
      ((contDiff_succ_iff_fderiv.mp hF).2.2).clm_comp contDiff_const
    have he : fderiv ℝ (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) =
        (fun x => ∫ n : Sphere, D (x,n.1) ∂sphereMeasure) := by
      funext x
      exact (hasFDerivAt_integral_sphere hF1 x).fderiv
    rw [show (↑(k+1) : ℕ∞ω) = ↑k+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_sphere hF1 x).differentiableAt,?_,?_⟩
    · simp
    · rw [he]
      exact ih hD

lemma contDiff_integral_sphere
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) := by
  rw [contDiff_infty]
  intro k
  exact contDiff_integral_sphere_nat k (contDiff_infty.mp hF k)

lemma contDiff_sphereSum {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (sphereSum g) := by
  apply contDiff_integral_sphere (F:=fun p : (ℝ × Vec) × Vec => g (p.1.2+p.1.1 • p.2))
  exact hg.comp ((contDiff_snd.comp contDiff_fst).add
    ((contDiff_fst.comp contDiff_fst).smul contDiff_snd))

lemma sphereSum_radial_deriv {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (x : Vec) (r : ℝ) :
    HasDerivAt (fun t => sphereSum g (t,x))
      (∫ n : Sphere, fderiv ℝ g (x+r • n.1) n.1 ∂sphereMeasure) r := by
  let F : ℝ × Vec → ℝ := fun p => g (x+p.1 • p.2)
  have hF : ContDiff ℝ 1 F := hg.comp (contDiff_const.add (contDiff_fst.smul contDiff_snd))
  have hd := (hasFDerivAt_integral_sphere hF r).hasDerivAt
  have hDa (n : Sphere) : ((fderiv ℝ F (r,n.1)).comp
      (ContinuousLinearMap.inl ℝ ℝ Vec)) 1 = fderiv ℝ g (x+r • n.1) n.1 := by
    have hfst : HasFDerivAt (fun p : ℝ × Vec => p.1)
        (ContinuousLinearMap.fst ℝ ℝ Vec) (r,n.1) := hasFDerivAt_fst
    have hsnd : HasFDerivAt (fun p : ℝ × Vec => p.2)
        (ContinuousLinearMap.snd ℝ ℝ Vec) (r,n.1) := hasFDerivAt_snd
    have hi := (hasFDerivAt_const x (r,n.1)).add (hfst.smul hsnd)
    have he := ((hg.differentiable (by simp)) (x+r • n.1)).hasFDerivAt.comp (r,n.1) hi
    change HasFDerivAt F _ (r,n.1) at he
    rw [he.fderiv]
    simp
  have hc : Continuous (fun n : Sphere => (fderiv ℝ F (r,n.1)).comp
      (ContinuousLinearMap.inl ℝ ℝ Vec)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_subtype_val)).clm_comp continuous_const
  rw [ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) 1] at hd
  simp_rw [hDa] at hd
  exact hd

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveK
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiff_spatialPartial {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => spatialPartial g x i) :=
  ((contDiff_infty_iff_fderiv.mp hg).2).clm_apply contDiff_const

lemma sphere_area : sphereMeasure.real univ = 4*Real.pi := by
  rw [sphereMeasure,Measure.toSphere_real_apply_univ]
  simp only [Vec,finrank_euclideanSpace,Measure.real,EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  norm_num
  ring

lemma contDiff_waveK {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (waveK g) :=
  contDiff_const.mul (contDiff_fst.mul (contDiff_sphereSum hg))

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ParamPrimitive
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma deriv_slice_eq_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × H → W}
    (hF : Differentiable ℝ F) (t : ℝ) (x : H) :
    deriv (fun r => F (r,x)) t = dirD F (1,0) (t,x) := by
  exact ((hF (t,x)).hasFDerivAt.comp t
    ((hasFDerivAt_id (𝕜:=ℝ) t).prodMk (hasFDerivAt_const (𝕜:=ℝ) x t))).hasDerivAt.deriv

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


lemma contDiff_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : ContDiff ℝ ∞ F) (i : Fin 3) : ContDiff ℝ ∞ (fun x => F x i) :=
  (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF

lemma contDiff_curl {F : Vec → Vec} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (curl F) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i <;> exact (contDiff_spatialPartial (contDiff_component hF _) _).sub
    (contDiff_spatialPartial (contDiff_component hF _) _)

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRadius
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma coneDirection_norm {x y : Vec} (h : x≠y) : ‖coneDirection x y‖=1 := by
  have hr : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  simp [coneDirection,coneRadius,norm_smul,hr.ne']



section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma contDiff_dot_pair {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : Vec × Vec => dot z.1 z.2) := by
  unfold dot
  fun_prop

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceWaveSpatialIbp
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coneRadius_add (x z : Vec) : coneRadius x (x+z)=‖z‖ := by
  unfold coneRadius
  rw [show x-(x+z) = -z by abel,norm_neg]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ShiftedRho
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coneDirection_add (x z : Vec) : coneDirection x (x+z)=-(‖z‖⁻¹ • z) := by
  unfold coneDirection
  rw [coneRadius_add,show x-(x+z) = -z by abel,smul_neg]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ContinuousIntegralSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma freeWave_sphere {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (r : ℝ) (x : Vec) :
    freeWave g h (r,x) = (4*Real.pi)⁻¹ *
      ((∫ n : Sphere, g (x+r • n.1) ∂sphereMeasure) +
        r*(∫ n : Sphere, fderiv ℝ g (x+r • n.1) n.1 ∂sphereMeasure)) +
      (4*Real.pi)⁻¹ * (r*∫ n : Sphere, h (x+r • n.1) ∂sphereMeasure) := by
  rw [freeWave,← deriv_slice_eq_dirD ((contDiff_waveK hg).differentiable (by simp))]
  have hd := ((hasDerivAt_id r).mul (sphereSum_radial_deriv (hg.of_le (by simp)) x r)).const_mul ((4*Real.pi)⁻¹)
  change HasDerivAt (fun t => waveK g (t,x)) _ r at hd
  rw [hd.deriv]
  simp only [id_eq,one_mul,waveK,sphereSum]

lemma coneBoundary_radius {T a : ℝ} (hT : 0<T) (ha : a ∈ Icc 0 (T/2)) {n : Vec}
    (hn : n ∈ sphere (0:Vec) 1) (x : Vec) : coneRadius x (x+(T-a) • n)=T-a := by
  rw [coneRadius_add,norm_smul,Real.norm_of_nonneg (by linarith [ha.2]),
    show ‖n‖=1 by simpa only [mem_sphere,dist_zero_right] using hn,mul_one]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DatumElectricFluxKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma datum_velocity_support {f : Phase → ℝ} (hc : HasCompactSupport f) :
    ∃ K : Set Vec, IsCompact K ∧ ∀ y v, v∉K → f (y,v)=0 := by
  refine ⟨Prod.snd '' tsupport f,hc.image continuous_snd,?_⟩
  intro y v hv
  by_contra h
  exact hv ⟨(y,v),subset_tsupport _ h,rfl⟩

lemma datum_integrand_continuousOn {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : Continuous f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ContinuousOn (fun p : (Vec × Vec) × Vec => f (p.1.1,p.2) • H (p.1.2,p.2))
      ((univ ×ˢ sphere (0:Vec) 1) ×ˢ univ) := by
  exact (hf.comp (continuous_fst.fst.prodMk continuous_snd)).continuousOn.smul
    (hH.comp (continuous_fst.snd.prodMk continuous_snd).continuousOn
      (fun _ h => ⟨h.1.2,mem_univ _⟩))

lemma continuousOn_datum_velocity_integral {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : Continuous f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ContinuousOn (fun p : Vec × Vec => ∫ v : Vec, f (p.1,v) • H (p.2,v))
      (univ ×ˢ sphere (0:Vec) 1) := by
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  apply continuousOn_integral_uniform_support hK (datum_integrand_continuousOn hf hH)
  intro p hp v hv
  rw [hz p.1 v hv,zero_smul]

lemma continuousOn_datumElectricFluxKernel (i : Fin 3) :
    ContinuousOn (datumElectricFluxKernel i) (sphere (0:Vec) 1 ×ˢ univ) := by
  have hu : Continuous (fun p : Vec × Vec => velocity p.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hd : Continuous (fun p : Vec × Vec => 1-dot p.1 (velocity p.2)) := continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
    (continuous_fst.prodMk hu))
  have hdi : ContinuousOn (fun p : Vec × Vec => (1-dot p.1 (velocity p.2))⁻¹)
      (sphere (0:Vec) 1 ×ˢ univ) := hd.continuousOn.inv₀ (by
    intro p hp
    exact (cone_denom_pos p.2 p.1 (by simpa only [mem_sphere,dist_zero_right] using hp.1)).ne')
  exact (hdi.mul (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp continuous_fst).sub
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hu)).continuousOn).smul hu.continuousOn

lemma continuousOn_datumMagneticFluxKernel (i : Fin 3) :
    ContinuousOn (datumMagneticFluxKernel i) (sphere (0:Vec) 1 ×ˢ univ) := by
  have hu : Continuous (fun p : Vec × Vec => velocity p.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hd : Continuous (fun p : Vec × Vec => 1-dot p.1 (velocity p.2)) := continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
    (continuous_fst.prodMk hu))
  have hdi : ContinuousOn (fun p : Vec × Vec => (1-dot p.1 (velocity p.2))⁻¹)
      (sphere (0:Vec) 1 ×ˢ univ) := hd.continuousOn.inv₀ (by
    intro p hp
    exact (cone_denom_pos p.2 p.1 (by simpa only [mem_sphere,dist_zero_right] using hp.1)).ne')
  have hc := (contDiff_cross (k:=1)).continuous.comp
    (continuous_fst.prodMk (continuous_fst.sub hu))
  exact (hdi.mul ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hc).continuousOn).smul hu.continuousOn

lemma datumElectricFlux_eq (d : Datum) (t : ℝ) (x y : Vec) (i : Fin 3) :
    retardedElectricFlux (datumBoundarySolution d) t x i y =
      (coneRadius x y)⁻¹ • ∫ v : Vec, d.f₀ (y,v) • datumElectricFluxKernel i (coneDirection x y,v) := by
  unfold retardedElectricFlux
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [retardedDensity,datumBoundarySolution,retardedG,eulerianG,
    PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,datumElectricFluxKernel,mul_inv_rev,smul_smul]
  congr 1
  ring

lemma datumMagneticFlux_eq (d : Datum) (t : ℝ) (x y : Vec) (i : Fin 3) :
    retardedMagneticFlux (datumBoundarySolution d) t x i y =
      (coneRadius x y)⁻¹ • ∫ v : Vec, d.f₀ (y,v) • datumMagneticFluxKernel i (coneDirection x y,v) := by
  unfold retardedMagneticFlux
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [retardedDensity,datumBoundarySolution,retardedH,retardedG,eulerianG,
    cross_smul_right,PiLp.smul_apply,smul_eq_mul,datumMagneticFluxKernel,mul_inv_rev,smul_smul]
  congr 1
  ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_BranchIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma norm_coordinate_le (v : Vec) (i : Fin 3) : |v i|≤‖v‖ := by
  exact (PiLp.norm_apply_le v i)

lemma norm_le_three_of_coordinate_bound {v : Vec} {C : ℝ} (hC : 0≤C)
    (h : ∀ i : Fin 3, |v i|≤C) : ‖v‖≤3*C := by
  have hsq (i : Fin 3) : (v i)^2≤C^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hC] using h i)
  have hnorm := dot_self v
  simp only [dot,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hnorm
  change v 0*v 0+(v 1*v 1+v 2*v 2)=‖v‖^2 at hnorm
  nlinarith [hsq 0,hsq 1,hsq 2,norm_nonneg v]

lemma norm_initial_cone_flux {d : Datum} {C : ℝ} (i : Fin 3)
    (hb : ∀ t x y, x≠y → ‖retardedElectricFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    |t^2*dot n.1 (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))|≤C*t := by
  have hr : coneRadius x (x+t • n.1)=t := by
    simpa only [sub_zero] using coneBoundary_radius ht
      (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
  have hxy : x≠x+t • n.1 := by
    intro he
    have hh : coneRadius x (x+t • n.1)=0 := by rw [← he,coneRadius,sub_self,norm_zero]
    linarith
  have hnorm : ‖n.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using n.2
  have hf := hb t x (x+t • n.1) hxy
  rw [hr] at hf
  rw [abs_mul,abs_of_nonneg (sq_nonneg t)]
  have ha : |dot (n.1 : Vec) (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))| ≤
      ‖n.1‖*‖retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)‖ := by
    simpa only [dot_eq_inner] using
      abs_real_inner_le_norm (n.1 : Vec) (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))
  calc
    _ ≤ t^2*(‖n.1‖*‖retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)‖) :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg t)
    _ ≤ t^2*(C/t) := by rw [hnorm,one_mul]; gcongr
    _ = C*t := by field_simp

lemma norm_initial_magnetic_cone_flux {d : Datum} {C : ℝ} (i : Fin 3)
    (hb : ∀ t x y, x≠y → ‖retardedMagneticFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    |t^2*dot n.1 (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))|≤C*t := by
  have hr : coneRadius x (x+t • n.1)=t := by
    simpa only [sub_zero] using coneBoundary_radius ht
      (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
  have hxy : x≠x+t • n.1 := by
    intro he
    have hh : coneRadius x (x+t • n.1)=0 := by rw [← he,coneRadius,sub_self,norm_zero]
    linarith
  have hnorm : ‖n.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using n.2
  have hf := hb t x (x+t • n.1) hxy
  rw [hr] at hf
  rw [abs_mul,abs_of_nonneg (sq_nonneg t)]
  have ha : |dot (n.1 : Vec) (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))| ≤
      ‖n.1‖*‖retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)‖ := by
    simpa only [dot_eq_inner] using
      abs_real_inner_le_norm (n.1 : Vec) (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))
  calc
    _ ≤ t^2*(‖n.1‖*‖retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)‖) :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg t)
    _ ≤ t^2*(C/t) := by rw [hnorm,one_mul]; gcongr
    _ = C*t := by field_simp

lemma norm_sphere_integral_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Sphere → W} {C : ℝ} (hb : ∀ n, ‖g n‖≤C) :
    ‖∫ n, g n ∂sphereMeasure‖≤C*(4*Real.pi) := by
  simpa only [sphere_area] using norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)

lemma abs_sphere_integral_le {g : Sphere → ℝ} {C : ℝ} (hb : ∀ n, |g n|≤C) :
    |∫ n, g n ∂sphereMeasure|≤C*(4*Real.pi) := by
  simpa only [Real.norm_eq_abs] using norm_sphere_integral_le (g:=g) (C:=C) hb

lemma waveK_bound_of_bounded {g : Vec → ℝ} {C : ℝ} (hb : ∀ x, |g x|≤C)
    {t : ℝ} (ht : 0≤t) (x : Vec) : |waveK g (t,x)|≤t*C := by
  have hh := norm_sphere_integral_le (g:=fun n : Sphere => g (x+t • n.1))
    (fun n => hb (x+t • n.1))
  simp only [Real.norm_eq_abs] at hh
  dsimp only [waveK,sphereSum]
  rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹),abs_of_nonneg ht]
  calc
    _ ≤ (4*Real.pi)⁻¹*(t*(C*(4*Real.pi))) := by gcongr
    _ = t*C := by field_simp

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coordinate_fderiv_apply {F : Vec → Vec} (hF : Differentiable ℝ F)
    (x v : Vec) (i : Fin 3) : fderiv ℝ (fun y => F y i) x v = (fderiv ℝ F x v) i := by
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L v)
    (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x (hF x).hasFDerivAt).fderiv)

lemma freeWave_bound_global {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    {C : ℝ} (hC : 0≤C) (hg0 : ∀ x, |g x|≤C)
    (hgd : ∀ x n : Vec, ‖n‖=1 → |fderiv ℝ g x n|≤C)
    (hh0 : ∀ x, |h x|≤C) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x : Vec) :
    |freeWave g h (t,x)|≤3*C := by
  have h₁ := abs_sphere_integral_le (fun n : Sphere => hg0 (x+t • n.1))
  have h₂ := abs_sphere_integral_le (fun n : Sphere => hgd (x+t • n.1) n.1
    (mem_sphere_zero_iff_norm.mp n.2))
  have h₃ := abs_sphere_integral_le (fun n : Sphere => hh0 (x+t • n.1))
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  rw [freeWave_sphere hg]
  calc
    _ ≤ (4*Real.pi)⁻¹*(C*(4*Real.pi)+t*(C*(4*Real.pi)))+
        (4*Real.pi)⁻¹*(t*(C*(4*Real.pi))) := by
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_of_nonneg hp,abs_mul,abs_of_nonneg hp]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hp
        exact (abs_add_le _ _).trans (add_le_add h₁ (by
          rw [abs_mul,abs_of_nonneg ht.1]
          exact mul_le_mul_of_nonneg_left h₂ ht.1))
      · apply mul_le_mul_of_nonneg_left _ hp
        rw [abs_mul,abs_of_nonneg ht.1]
        exact mul_le_mul_of_nonneg_left h₃ ht.1
    _ = C+2*t*C := by field_simp; ring
    _ ≤ 3*C := by nlinarith [ht.2]

lemma abs_sphere_integral_sub_le {F G : Sphere → ℝ} {C : ℝ}
    (hF : Continuous F) (hG : Continuous G) (h : ∀ n, |F n-G n|≤C) :
    |(∫ n, F n ∂sphereMeasure)-(∫ n, G n ∂sphereMeasure)|≤C*(4*Real.pi) := by
  rw [← integral_sub (hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  exact abs_sphere_integral_le h

lemma waveK_lipschitz {g : Vec → ℝ} (hg : Continuous g) {C : ℝ}
    (h : ∀ x y, |g y-g x|≤C*‖y-x‖) {t : ℝ} (ht : 0≤t) (x y : Vec) :
    |waveK g (t,y)-waveK g (t,x)|≤t*C*‖y-x‖ := by
  have hc (x : Vec) : Continuous (fun n : Sphere => g (x+t • n.1)) :=
    hg.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))
  have hh := abs_sphere_integral_sub_le (hc y) (hc x) (C:=C*‖y-x‖) (by
    intro n
    simpa only [add_sub_add_right_eq_sub] using h (x+t • n.1) (y+t • n.1))
  simp only [waveK,← mul_sub]
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹),abs_mul,abs_of_nonneg ht]
  calc
    _ ≤ (4*Real.pi)⁻¹*(t*(C*‖y-x‖*(4*Real.pi))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh ht) (by positivity)
    _ = t*C*‖y-x‖ := by field_simp

lemma freeWave_lipschitz {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : Continuous h)
    {C : ℝ} (hC : 0≤C)
    (hg0 : ∀ x y, |g y-g x|≤C*‖y-x‖)
    (hgd : ∀ x y n : Vec, ‖n‖=1 → |fderiv ℝ g y n-fderiv ℝ g x n|≤C*‖y-x‖)
    (hh0 : ∀ x y, |h y-h x|≤C*‖y-x‖)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x y : Vec) :
    |freeWave g h (t,y)-freeWave g h (t,x)|≤3*C*‖y-x‖ := by
  have hc (z : Vec) : Continuous (fun n : Sphere => g (z+t • n.1)) :=
    hg.continuous.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))
  have hd (z : Vec) : Continuous (fun n : Sphere => fderiv ℝ g (z+t • n.1) n.1) :=
    ((hg.continuous_fderiv (by simp)).comp
      (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))).clm_apply continuous_subtype_val
  have hh' (z : Vec) : Continuous (fun n : Sphere => h (z+t • n.1)) :=
    hh.comp (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val))
  have A := abs_sphere_integral_sub_le (hc y) (hc x) (by intro n; simpa only [add_sub_add_right_eq_sub] using hg0 (x+t • n.1) (y+t • n.1))
  have B := abs_sphere_integral_sub_le (hd y) (hd x) (by intro n; simpa only [add_sub_add_right_eq_sub] using hgd (x+t • n.1) (y+t • n.1) n.1 (mem_sphere_zero_iff_norm.mp n.2))
  have D := abs_sphere_integral_sub_le (hh' y) (hh' x) (by intro n; simpa only [add_sub_add_right_eq_sub] using hh0 (x+t • n.1) (y+t • n.1))
  rw [freeWave_sphere hg,freeWave_sphere hg]
  have he : ∀ a b c d e f : ℝ, (4*Real.pi)⁻¹*(a+t*b)+(4*Real.pi)⁻¹*(t*c)-
      ((4*Real.pi)⁻¹*(d+t*e)+(4*Real.pi)⁻¹*(t*f))=
      (4*Real.pi)⁻¹*((a-d)+t*(b-e)+t*(c-f)) := by intros; ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  calc
    _ ≤ (4*Real.pi)⁻¹*(C*‖y-x‖*(4*Real.pi)+t*(C*‖y-x‖*(4*Real.pi))+t*(C*‖y-x‖*(4*Real.pi))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (abs_add_le _ _).trans
      apply add_le_add
      · apply (abs_add_le _ _).trans
        apply add_le_add A
        simpa only [abs_mul,abs_of_nonneg ht.1] using mul_le_mul_of_nonneg_left B ht.1
      · simpa only [abs_mul,abs_of_nonneg ht.1] using mul_le_mul_of_nonneg_left D ht.1
    _ = (1+2*t)*C*‖y-x‖ := by field_simp; ring
    _ ≤ 3*C*‖y-x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact mul_le_mul_of_nonneg_right (by linarith [ht.2]) hC

lemma weighted_sphere_mean_lipschitz {g : Vec → ℝ} (hg : Continuous g)
    {C : ℝ} (hC : 0≤C) (h : ∀ x y, |g y-g x|≤C*‖y-x‖)
    {w : Sphere → ℝ} (hw : Continuous w) (hwb : ∀ n, |w n|≤1)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (x y : Vec) :
    |(4*Real.pi)⁻¹*(∫ n : Sphere, t*w n*g (y+t • n.1) ∂sphereMeasure)-
      (4*Real.pi)⁻¹*(∫ n : Sphere, t*w n*g (x+t • n.1) ∂sphereMeasure)|≤C*‖y-x‖ := by
  have hc (z : Vec) : Continuous (fun n : Sphere => t*w n*g (z+t • n.1)) :=
    (continuous_const.mul hw).mul (hg.comp (continuous_const.add
      ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)))
  have hh := abs_sphere_integral_sub_le (hc y) (hc x) (C:=C*‖y-x‖) (by
    intro n
    rw [← mul_sub,abs_mul,abs_mul,abs_of_nonneg ht.1]
    have hh' : |g (y+t • n.1)-g (x+t • n.1)|≤C*‖y-x‖ := by
      simpa only [add_sub_add_right_eq_sub] using h (x+t • n.1) (y+t • n.1)
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (hwb n) ht.1) hh' (abs_nonneg _) (by simpa only [mul_one] using ht.1)).trans
      (by simpa only [mul_one] using mul_le_of_le_one_left (by positivity : 0≤C*‖y-x‖) ht.2))
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp)

lemma datum_initial_electric_flux_normalised (d : Datum) (i : Fin 3)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    t^2*dot n.1 (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1))=
      t*dot n.1 (∫ v, d.f₀ (x+t • n.1,v) • datumElectricFluxKernel i (-n.1,v)) := by
  have hn : ‖t • n.1‖=t := by simp only [norm_smul,Real.norm_of_nonneg ht.le,mem_sphere_zero_iff_norm.mp n.2,mul_one]
  rw [datumElectricFlux_eq,coneRadius_add,coneDirection_add,hn,inv_smul_smul₀ ht.ne',dot_smul_right]
  field_simp

lemma datum_initial_magnetic_flux_normalised (d : Datum) (i : Fin 3)
    {t : ℝ} (ht : 0<t) (x : Vec) (n : Sphere) :
    t^2*dot n.1 (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1))=
      t*dot n.1 (∫ v, d.f₀ (x+t • n.1,v) • datumMagneticFluxKernel i (-n.1,v)) := by
  have hn : ‖t • n.1‖=t := by simp only [norm_smul,Real.norm_of_nonneg ht.le,mem_sphere_zero_iff_norm.mp n.2,mul_one]
  rw [datumMagneticFlux_eq,coneRadius_add,coneDirection_add,hn,inv_smul_smul₀ ht.ne',dot_smul_right]
  field_simp

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_SmoothLocalExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma C1ClassicalPrefix.toSmooth {d : Datum} {s : Solution} {T : ℝ}
    (hs : C1ClassicalPrefix d s T)
    (hf : ContDiffOn ℝ ∞ s.f (particleSlab T))
    (hE : ContDiffOn ℝ ∞ s.E (fieldSlab T)) (hB : ContDiffOn ℝ ∞ s.B (fieldSlab T)) :
    SmoothClassicalPrefix d s T :=
  ⟨hf,hE,hB,hs.nonnegative,hs.E_L2,hs.B_L2,hs.compact,hs.equations,
    hs.initial_f,hs.initial_E,hs.initial_B⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_UniformDatumKernel
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_velocity_integral_bound_from_caps {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {H : Vec × Vec → W} (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ))
    (A P : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ f : Phase → ℝ,
      (∀ z, |f z|≤A) → (∀ x v, P<‖v‖ → f (x,v)=0) →
      ∀ y n : Vec, ‖n‖=1 → ‖∫ v : Vec, f (y,v) • H (n,v)‖≤C := by
  let K := closedBall (0:Vec) P
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := ((isCompact_sphere (0:Vec) 1).prod hK).exists_bound_of_continuousOn
    (hH.mono (by intro p hp; exact ⟨hp.1,mem_univ _⟩))
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  refine ⟨A*D*(volume K).toReal,by positivity,?_⟩
  intro f hf hp y n hn
  have hn' : n∈sphere (0:Vec) 1 := mem_sphere_zero_iff_norm.mpr hn
  have he : (∫ v in K, f (y,v) • H (n,v))=(∫ v, f (y,v) • H (n,v)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hp y v (by simpa only [K,mem_closedBall,dist_zero_right,not_le] using hv),zero_smul]
  rw [←he]
  have hb : ∀ v∈K, ‖f (y,v) • H (n,v)‖≤A*D := by
    intro v hv
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hf (y,v)) ((hB (n,v) ⟨hn',hv⟩).trans (le_max_left _ _)) (norm_nonneg _) hA
  exact norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hb

lemma uniform_velocity_integral_lipschitz_from_caps {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {H : Vec × Vec → W} (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ))
    (A P : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ f : Phase → ℝ, Continuous f →
      (∀ x y v, |f (y,v)-f (x,v)|≤A*‖y-x‖) → (∀ x v, P<‖v‖ → f (x,v)=0) →
      ∀ x y n : Vec, ‖n‖=1 →
      ‖(∫ v, f (y,v) • H (n,v))-(∫ v, f (x,v) • H (n,v))‖≤C*‖y-x‖ := by
  let K := closedBall (0:Vec) P
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := ((isCompact_sphere (0:Vec) 1).prod hK).exists_bound_of_continuousOn
    (hH.mono (by intro p hp; exact ⟨hp.1,mem_univ _⟩))
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  refine ⟨A*D*(volume K).toReal,by positivity,?_⟩
  intro f hf hfl hp x y n hn
  have hz (z v : Vec) (hv : v∉K) : f (z,v)=0 :=
    hp z v (by simpa only [K,mem_closedBall,dist_zero_right,not_le] using hv)
  have hn' : n∈sphere (0:Vec) 1 := mem_sphere_zero_iff_norm.mpr hn
  have hint (z : Vec) : Integrable (fun v => f (z,v) • H (n,v)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hf.comp (continuous_const.prodMk continuous_id)).smul
        (hH.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hn',mem_univ v⟩))
    · exact HasCompactSupport.intro hK (fun v hv => by rw [hz z v hv,zero_smul])
  rw [← integral_sub (hint y) (hint x)]
  have he : (∫ v in K, f (y,v) • H (n,v)-f (x,v) • H (n,v))=
      ∫ v, f (y,v) • H (n,v)-f (x,v) • H (n,v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    simp only [hz _ v hv,zero_smul,sub_self]
  rw [← he]
  have hb : ∀ v∈K, ‖f (y,v) • H (n,v)-f (x,v) • H (n,v)‖≤ A*‖y-x‖*D := by
    intro v hv
    rw [← sub_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hfl x y v) ((hB (n,v) ⟨hn',hv⟩).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  exact (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hb).trans_eq (by simp only [Measure.real]; ring)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_LowBoundaryControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coordinate_bounds_of_low_jets {F : Vec → Vec} (hF : ContDiff ℝ ∞ F)
    {C : ℝ} (hC : 0≤C) (hjets : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k F x‖≤C) :
    ∀ x : Vec, ‖F x‖≤3*C ∧
      (∀ i v, |fderiv ℝ (fun y => F y i) x v|≤(3*C)*‖v‖) ∧ ∀ i, |curl F x i|≤3*C := by
  have hA := hjets 0 (by norm_num)
  have hD := hjets 1 (by norm_num)
  have hD' : ∀ x, ‖fderiv ℝ F x‖≤ C := by
    intro x
    have hh : ‖fderiv ℝ F x‖≤C := by simpa only [norm_iteratedFDeriv_one] using hD x
    exact hh.trans le_rfl
  have hfd (x v : Vec) (i : Fin 3) : |fderiv ℝ (fun y => F y i) x v|≤ C*‖v‖ := by
    rw [coordinate_fderiv_apply (hF.differentiable (by simp))]
    exact (norm_coordinate_le _ i).trans (((fderiv ℝ F x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg v)))
  intro x
  refine ⟨?_,?_,?_⟩
  · have hh : ‖F x‖≤C := by simpa only [norm_iteratedFDeriv_zero] using hA x
    linarith [hC]
  · intro i v
    exact (hfd x v i).trans (mul_le_mul_of_nonneg_right (by
      linarith [hC]) (norm_nonneg v))
  · intro i
    have he : curl F x i=spatialPartial (fun y => F y (curlB i)) x (curlA i)-
        spatialPartial (fun y => F y (curlA i)) x (curlB i) := by
      fin_cases i <;> simp [curl,curlA,curlB]
    rw [he]
    have ha := hfd x (basis (curlA i)) (curlB i)
    have hb := hfd x (basis (curlB i)) (curlA i)
    simp only [show ∀ j : Fin 3, ‖basis j‖=1 by intro j; simp [basis,PiLp.norm_single],mul_one] at ha hb
    exact (abs_sub _ _).trans ((add_le_add ha hb).trans (by linarith [hC]))

lemma iterated_lipschitz_of_bound {F : Vec → Vec} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) {C : ℝ} (hb : ∀ x, ‖iteratedFDeriv ℝ (n+1) F x‖≤C) (x y : Vec) :
    ‖iteratedFDeriv ℝ n F y-iteratedFDeriv ℝ n F x‖≤C*‖y-x‖ := by
  exact (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ContDiff.differentiable_iteratedFDeriv (n:=∞) (m:=n) (by exact_mod_cast ENat.natCast_lt_top n) hF z)
    (fun z _ => by rw [norm_fderiv_iteratedFDeriv]; exact hb z) (mem_univ x) (mem_univ y)

lemma spatial_lipschitz_of_low_jets {F : Vec → Vec} (hF : ContDiff ℝ ∞ F)
    {C : ℝ} (hC : 0≤C) (hjets : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k F x‖≤C) :
    ∀ x y : Vec, ‖F y-F x‖≤(3*C)*‖y-x‖ ∧
      (∀ i v, |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤(3*C)*‖y-x‖*‖v‖) ∧
      ∀ i, |curl F y i-curl F x i|≤(3*C)*‖y-x‖ := by
  have hD := hjets 1 (by norm_num)
  let A := C
  have hA : 0≤A := hC
  have hval (x y : Vec) : ‖F y-F x‖≤A*‖y-x‖ := by
    apply (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hF.differentiable (by simp) z) _ (mem_univ x) (mem_univ y)
    intro z _
    have hh : ‖fderiv ℝ F z‖≤C := by simpa only [norm_iteratedFDeriv_one] using hD z
    exact hh.trans le_rfl
  let B := C
  have hB : 0≤B := hC
  have hb := iterated_lipschitz_of_bound hF 1 (hjets 2 le_rfl)
  have hder (x y v : Vec) : ‖fderiv ℝ F y v-fderiv ℝ F x v‖≤B*‖y-x‖*‖v‖ := by
    have hh := (iteratedFDeriv ℝ 1 F y-iteratedFDeriv ℝ 1 F x).le_opNorm (fun _ => v)
    simp only [sub_apply,iteratedFDeriv_one_apply,Fin.prod_univ_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hb x y) (norm_nonneg v))
  have hder' (x y v : Vec) (i : Fin 3) :
      |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤B*‖y-x‖*‖v‖ := by
    rw [coordinate_fderiv_apply (hF.differentiable (by simp)),coordinate_fderiv_apply (hF.differentiable (by simp))]
    exact (norm_coordinate_le (fderiv ℝ F y v-fderiv ℝ F x v) i).trans (hder x y v)
  suffices hh : ∀ x y : Vec, ‖F y-F x‖≤(A+2*B)*‖y-x‖ ∧
    (∀ i v, |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤(A+2*B)*‖y-x‖*‖v‖) ∧
    ∀ i, |curl F y i-curl F x i|≤(A+2*B)*‖y-x‖ by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [A,B]
    ring_nf
  intro x y
  refine ⟨(hval x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)),?_,?_⟩
  · intro i v
    exact (hder' x y v i).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)) (norm_nonneg _))
  · intro i
    have he (z : Vec) : curl F z i=spatialPartial (fun u => F u (curlB i)) z (curlA i)-
        spatialPartial (fun u => F u (curlA i)) z (curlB i) := by
      fin_cases i <;> simp [curl,curlA,curlB]
    rw [he y,he x,show ∀ a b c d : ℝ, (a-b)-(c-d)=(a-c)-(b-d) by intros; ring]
    have ha := hder' x y (basis (curlA i)) (curlB i)
    have hb' := hder' x y (basis (curlB i)) (curlA i)
    simp only [show ∀ j : Fin 3, ‖basis j‖=1 by intro j; simp [basis,PiLp.norm_single],mul_one] at ha hb'
    exact (abs_sub _ _).trans ((add_le_add ha hb').trans (by nlinarith [norm_nonneg (y-x)]))

lemma freeWave_coordinate_bound_of_low_jets {E B : Vec → Vec}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    {C : ℝ} (hC : 0≤C)
    (hEj : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k E x‖≤C)
    (hBj : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k B x‖≤C) (i : Fin 3) :
    ∀ t∈Icc (0:ℝ) 1, ∀ x : Vec,
      |freeWave (fun y => E y i) (fun y => curl B y i) (t,x)|≤18*C ∧
      |freeWave (fun y => B y i) (fun y => -curl E y i) (t,x)|≤18*C := by
  let A := 3*C
  let D := 3*C
  have hA : 0≤A := by positivity
  have hD : 0≤D := by positivity
  have hAb := coordinate_bounds_of_low_jets hE hC hEj
  have hDb := coordinate_bounds_of_low_jets hB hC hBj
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  have he : 18*C=3*(A+D) := by dsimp [A,D]; ring
  rw [he]
  intro t ht x
  constructor
  · apply freeWave_bound_global (hproj.comp hE) (add_nonneg hA hD) _ _ _ ht
    · intro y
      exact (norm_coordinate_le _ i).trans ((hAb y).1.trans (le_add_of_nonneg_right hD))
    · intro y n hn
      have hh : |fderiv ℝ (fun u => E u i) y n|≤A := by simpa only [hn,mul_one] using (hAb y).2.1 i n
      exact hh.trans (le_add_of_nonneg_right hD)
    · intro y
      exact (hDb y).2.2 i |>.trans (le_add_of_nonneg_left hA)
  · apply freeWave_bound_global (hproj.comp hB) (add_nonneg hA hD) _ _ _ ht
    · intro y
      exact (norm_coordinate_le _ i).trans ((hDb y).1.trans (le_add_of_nonneg_left hA))
    · intro y n hn
      have hh : |fderiv ℝ (fun u => B u i) y n|≤D := by simpa only [hn,mul_one] using (hDb y).2.1 i n
      exact hh.trans (le_add_of_nonneg_left hA)
    · intro y
      rw [abs_neg]
      exact (hAb y).2.2 i |>.trans (le_add_of_nonneg_right hD)

lemma freeWave_coordinate_lipschitz_of_low_jets {E B : Vec → Vec}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    {C : ℝ} (hC : 0≤C)
    (hEj : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k E x‖≤C)
    (hBj : ∀ k≤2, ∀ x, ‖iteratedFDeriv ℝ k B x‖≤C) (i : Fin 3) :
    ∀ t∈Icc (0:ℝ) 1, ∀ x y : Vec,
      |freeWave (fun z => E z i) (fun z => curl B z i) (t,y)-
        freeWave (fun z => E z i) (fun z => curl B z i) (t,x)|≤18*C*‖y-x‖ ∧
      |freeWave (fun z => B z i) (fun z => -curl E z i) (t,y)-
        freeWave (fun z => B z i) (fun z => -curl E z i) (t,x)|≤18*C*‖y-x‖ := by
  let A := 3*C
  let D := 3*C
  have hA : 0≤A := by positivity
  have hD : 0≤D := by positivity
  have hAb := spatial_lipschitz_of_low_jets hE hC hEj
  have hDb := spatial_lipschitz_of_low_jets hB hC hBj
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  have he : 18*C=3*(A+D) := by dsimp [A,D]; ring
  rw [he]
  intro t ht x y
  constructor
  · apply freeWave_lipschitz (hproj.comp hE)
      (hproj.continuous.comp (contDiff_curl hB).continuous) (add_nonneg hA hD) _ _ _ ht
    · intro z z'
      exact (norm_coordinate_le (E z'-E z) i).trans ((hAb z z').1.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _)))
    · intro z z' n hn
      have hh : |fderiv ℝ (fun u => E u i) z' n-fderiv ℝ (fun u => E u i) z n|≤A*‖z'-z‖ := by
        simpa only [hn,mul_one] using (hAb z z').2.1 i n
      exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _))
    · intro z z'
      exact ((hDb z z').2.2 i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _))
  · apply freeWave_lipschitz (hproj.comp hB)
      ((hproj.continuous.comp (contDiff_curl hE).continuous).neg) (add_nonneg hA hD) _ _ _ ht
    · intro z z'
      exact (norm_coordinate_le (B z'-B z) i).trans ((hDb z z').1.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _)))
    · intro z z' n hn
      have hh : |fderiv ℝ (fun u => B u i) z' n-fderiv ℝ (fun u => B u i) z n|≤D*‖z'-z‖ := by
        simpa only [hn,mul_one] using (hDb z z').2.1 i n
      exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _))
    · intro z z'
      simpa only [Function.comp_apply,Pi.neg_apply,neg_sub_neg,abs_sub_comm] using
        ((hAb z z').2.2 i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _))

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

variable {ι : Type*} {d : ι → Datum}
variable (hd : ∀ j, Admissible (d j))
variable {A P L J : ℝ} (hA : 0≤A) (hL : 0≤L) (hJ : 0≤J)
variable (hf : ∀ j z, |(d j).f₀ z|≤A)
variable (hp : ∀ j x v, P<‖v‖ → (d j).f₀ (x,v)=0)
variable (hl : ∀ j x y v, |(d j).f₀ (y,v)-(d j).f₀ (x,v)|≤L*‖y-x‖)
variable (hEj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).E₀ x‖≤J)
variable (hBj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).B₀ x‖≤J)

include hA hf hp in
lemma family_datum_moment_bounds :
    ∃ C : ℝ, 0≤C ∧ ∀ j x, |rho (d j).f₀ x|≤C ∧ ‖current (d j).f₀ x‖≤C := by
  obtain ⟨B,hB,hb⟩ := uniform_velocity_integral_bound_from_caps (H:=fun _ => (1:ℝ)) continuousOn_const A P hA
  obtain ⟨C,hC,hc⟩ := uniform_velocity_integral_bound_from_caps
    (((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn) A P hA
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  intro j x
  constructor
  · have hh := hb (d j).f₀ (hf j) (hp j) x (basis 0) (by simp [basis,PiLp.norm_single])
    simp only [smul_eq_mul,mul_one,Real.norm_eq_abs] at hh
    exact hh.trans (le_add_of_nonneg_right hC)
  · exact (hc (d j).f₀ (hf j) (hp j) x (basis 0) (by simp [basis,PiLp.norm_single])).trans (le_add_of_nonneg_left hB)

include hd hL hp hl in
lemma family_datum_moment_lipschitz :
    ∃ C : ℝ, 0≤C ∧ ∀ j x y, |rho (d j).f₀ y-rho (d j).f₀ x|≤C*‖y-x‖ ∧
      ‖current (d j).f₀ y-current (d j).f₀ x‖≤C*‖y-x‖ := by
  obtain ⟨B,hB,hb⟩ := uniform_velocity_integral_lipschitz_from_caps (H:=fun _ => (1:ℝ)) continuousOn_const L P hL
  obtain ⟨C,hC,hc⟩ := uniform_velocity_integral_lipschitz_from_caps
    (((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn) L P hL
  refine ⟨B+C,add_nonneg hB hC,?_⟩
  intro j x y
  constructor
  · have hh := hb (d j).f₀ (hd j).1.continuous (hl j) (hp j) x y (basis 0) (by simp [basis,PiLp.norm_single])
    simp only [smul_eq_mul,mul_one,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (norm_nonneg _))
  · exact (hc (d j).f₀ (hd j).1.continuous (hl j) (hp j) x y (basis 0) (by simp [basis,PiLp.norm_single])).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB) (norm_nonneg _))

include hA hf hp in
lemma family_datumElectricFlux_bound (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j (t : ℝ) (x y : Vec), x≠y →
      ‖retardedElectricFlux (datumBoundarySolution (d j)) t x i y‖≤C/coneRadius x y := by
  obtain ⟨C,hC,hbound⟩ := uniform_velocity_integral_bound_from_caps (continuousOn_datumElectricFluxKernel i) A P hA
  refine ⟨C,hC,?_⟩
  intro j t x y hxy
  rw [datumElectricFlux_eq,norm_smul,coneRadius,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (x-y)))]
  simpa only [div_eq_mul_inv,mul_comm C,coneRadius] using
    mul_le_mul_of_nonneg_left (hbound (d j).f₀ (hf j) (hp j) y (coneDirection x y) (coneDirection_norm hxy))
      (inv_nonneg.mpr (norm_nonneg _))

include hA hf hp in
lemma family_datumMagneticFlux_bound (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j (t : ℝ) (x y : Vec), x≠y →
      ‖retardedMagneticFlux (datumBoundarySolution (d j)) t x i y‖≤C/coneRadius x y := by
  obtain ⟨C,hC,hbound⟩ := uniform_velocity_integral_bound_from_caps (continuousOn_datumMagneticFluxKernel i) A P hA
  refine ⟨C,hC,?_⟩
  intro j t x y hxy
  rw [datumMagneticFlux_eq,norm_smul,coneRadius,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (x-y)))]
  simpa only [div_eq_mul_inv,mul_comm C,coneRadius] using
    mul_le_mul_of_nonneg_left (hbound (d j).f₀ (hf j) (hp j) y (coneDirection x y) (coneDirection_norm hxy))
      (inv_nonneg.mpr (norm_nonneg _))

include hd hL hp hl in
lemma family_datum_sphere_flux_lipschitz {H : Vec × Vec → Vec}
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Icc (0:ℝ) 1, ∀ x y : Vec,
      |(4*Real.pi)⁻¹*(∫ n : Sphere, t*dot n.1 (∫ v, (d j).f₀ (y+t • n.1,v) • H (-n.1,v)) ∂sphereMeasure)-
        (4*Real.pi)⁻¹*(∫ n : Sphere, t*dot n.1 (∫ v, (d j).f₀ (x+t • n.1,v) • H (-n.1,v)) ∂sphereMeasure)|≤C*‖y-x‖ := by
  obtain ⟨C,hC,hb⟩ := uniform_velocity_integral_lipschitz_from_caps hH L P hL
  refine ⟨C,hC,?_⟩
  intro q t ht x y
  have hhf := (hd q).1.continuous
  have hhc := (hd q).2.1
  have hb := hb (d q).f₀ hhf (hl q) (hp q)
  have hn (n : Sphere) : ‖n.1‖=1 := mem_sphere_zero_iff_norm.mp n.2
  have hc' (z : Vec) : Continuous (fun n : Sphere =>
      t*dot n.1 (∫ v, (d q).f₀ (z+t • n.1,v) • H (-n.1,v))) := by
    have hI : Continuous (fun n : Sphere => ∫ v, (d q).f₀ (z+t • n.1,v) • H (-n.1,v)) := by
      apply (continuousOn_datum_velocity_integral hhf hhc hH).comp_continuous
        ((continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)).prodMk continuous_subtype_val.neg)
      intro n
      exact ⟨mem_univ _,by simpa only [mem_sphere_zero_iff_norm,Pi.neg_apply,norm_neg] using hn n⟩
    exact continuous_const.mul ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_subtype_val.prodMk hI))
  have hh := abs_sphere_integral_sub_le (hc' y) (hc' x) (C:=C*‖y-x‖) (by
    intro n
    rw [← mul_sub,← dot_sub_right,abs_mul,abs_of_nonneg ht.1]
    have hbd : ‖(∫ v, (d q).f₀ (y+t • n.1,v) • H (-n.1,v))-
        (∫ v, (d q).f₀ (x+t • n.1,v) • H (-n.1,v))‖≤C*‖y-x‖ := by
      simpa only [add_sub_add_right_eq_sub] using hb (x+t • n.1) (y+t • n.1) (-n.1) (by simpa only [norm_neg] using hn n)
    exact (mul_le_mul_of_nonneg_left ((abs_dot_le _ _).trans
      (by simpa only [hn n,one_mul] using hbd)) ht.1).trans
        (mul_le_of_le_one_left (by positivity) ht.2))
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp)

include hd hA hJ hf hp hEj hBj in
lemma family_electricConeBoundary_datum_bound_global
    (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
      |electricConeBoundary (datumBoundarySolution (d j)) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := family_datumElectricFlux_bound hA hf hp i
  obtain ⟨D,hD,hmom⟩ := family_datum_moment_bounds hA hf hp
  let A := 18*J
  have hA : 0≤A := by positivity
  have hfree (j : ι) := freeWave_coordinate_bound_of_low_jets (hd j).2.2.2.1.1 (hd j).2.2.2.2.1.1 hJ (hEj j) (hBj j) i
  refine ⟨A+(C+2*D),by positivity,?_⟩
  intro q t ht x
  have hfree := hfree q
  have hflux := hflux q
  have hmom := hmom q
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution (d q)) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_cone_flux i hflux ht.1 x n)
  have hrho : |∫ n : Sphere, t*n.1 i*rho (d q).f₀ (x+t • n.1) ∂sphereMeasure|≤
      (t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    have hn : |n.1 i|≤1 := by
      exact (norm_coordinate_le n.1 i).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        (hmom (x+t • n.1)).1 (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = t*D := by ring
  have hj : |waveK (fun y => current (d q).f₀ y i) (t,x)|≤t*D :=
    waveK_bound_of_bounded (fun y => (norm_coordinate_le (current (d q).f₀ y) i).trans (hmom y).2) ht.1.le x
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution (d q)) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t*n.1 i*rho (d q).f₀ (x+t • n.1) ∂sphereMeasure)|≤t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hrho hp
      _ = t*D := by field_simp
  have hf := (hfree t ⟨ht.1.le,ht.2⟩ x).1
  simp only [electricConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)) hj)).trans (by
      nlinarith [ht.2])

include hd hL hJ hp hl hEj hBj in
lemma family_electricConeBoundary_datum_lipschitz (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
      |electricConeBoundary (datumBoundarySolution (d j)) t y i 0-
        electricConeBoundary (datumBoundarySolution (d j)) t x i 0|≤C*‖y-x‖ := by
  let A := 18*J
  have hA : 0≤A := by positivity
  have hfree (j : ι) := freeWave_coordinate_lipschitz_of_low_jets (hd j).2.2.2.1.1 (hd j).2.2.2.2.1.1 hJ (hEj j) (hBj j) i
  obtain ⟨B,hB,hflux⟩ := family_datum_sphere_flux_lipschitz hd hL hp hl
    (continuousOn_datumElectricFluxKernel i)
  obtain ⟨D,hD,hmom⟩ := family_datum_moment_lipschitz hd hL hp hl
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro q t ht x y
  have hfree := hfree q
  have hflux := hflux q
  have hmom := hmom q
  have hm : Continuous (rho (d q).f₀) ∧ Continuous (current (d q).f₀) := by
    constructor
    · exact (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
        simpa only [dist_eq_norm,Real.norm_eq_abs] using (hmom y x).1)).continuous
    · exact (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
        simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj : Continuous (fun v : Vec => v i) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous

  have hrho := weighted_sphere_mean_lipschitz hm.1 hD (fun x y => (hmom x y).1)
    (hproj.comp continuous_subtype_val) (fun n => (norm_coordinate_le n.1 i).trans_eq (mem_sphere_zero_iff_norm.mp n.2))
    ⟨ht.1.le,ht.2⟩ x y
  have hj := waveK_lipschitz (hproj.comp hm.2)
    (fun x y => (norm_coordinate_le (current (d q).f₀ y-current (d q).f₀ x) i).trans (hmom x y).2) ht.1.le x y
  have he : t*D*‖y-x‖≤D*‖y-x‖ := by
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hD ht.2) (norm_nonneg _)
  simp only [electricConeBoundary,sub_zero]
  simp_rw [datum_initial_electric_flux_normalised (d q) i ht.1]
  simp only [datumBoundarySolution]
  have halg (a b c e a' b' c' e' : ℝ) : (a-b-c-e)-(a'-b'-c'-e')=(a-a')-(b-b')-(c-c')-(e-e') := by ring
  rw [halg]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x y).1
      (hflux t ⟨ht.1.le,ht.2⟩ x y))) hrho)) (hj.trans he))).trans_eq (by ring)

include hd hA hJ hf hp hEj hBj in
lemma family_magneticConeBoundary_datum_bound_global
    (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
      |magneticConeBoundary (datumBoundarySolution (d j)) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := family_datumMagneticFlux_bound hA hf hp i
  obtain ⟨D,hD,hmom⟩ := family_datum_moment_bounds hA hf hp
  let A := 18*J
  have hA : 0≤A := by positivity
  have hfree (j : ι) := freeWave_coordinate_bound_of_low_jets (hd j).2.2.2.1.1 (hd j).2.2.2.2.1.1 hJ (hEj j) (hBj j) i
  refine ⟨A+(C+2*D),by positivity,?_⟩
  intro q t ht x
  have hfree := hfree q
  have hflux := hflux q
  have hmom := hmom q
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution (d q)) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_magnetic_cone_flux i hflux ht.1 x n)
  have hem (n : Sphere) (j k : Fin 3) :
      |t*n.1 j*current (d q).f₀ (x+t • n.1) k|≤t*D := by
    have hn : |n.1 j|≤1 :=
      (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    have hj : |current (d q).f₀ (x+t • n.1) k|≤D :=
      (norm_coordinate_le _ k).trans (hmom _).2
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        hj (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = _ := by ring
  have hj : |∫ n : Sphere,
      t*n.1 (curlA i)*current (d q).f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current (d q).f₀ (x+t • n.1) (curlA i) ∂sphereMeasure|≤
      (2*t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    exact (abs_sub _ _).trans ((add_le_add (hem n _ _) (hem n _ _)).trans (by ring_nf; rfl))
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution (d q)) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere,
      t*n.1 (curlA i)*current (d q).f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current (d q).f₀ (x+t • n.1) (curlA i) ∂sphereMeasure)|≤2*t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((2*t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hj hp
      _ = 2*t*D := by field_simp
  have hf := (hfree t ⟨ht.1.le,ht.2⟩ x).2
  simp only [magneticConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)).trans (by
      nlinarith [ht.2])

include hd hL hJ hp hl hEj hBj in
lemma family_magneticConeBoundary_datum_lipschitz (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ j, ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
      |magneticConeBoundary (datumBoundarySolution (d j)) t y i 0-
        magneticConeBoundary (datumBoundarySolution (d j)) t x i 0|≤C*‖y-x‖ := by
  let A := 18*J
  have hA : 0≤A := by positivity
  have hfree (j : ι) := freeWave_coordinate_lipschitz_of_low_jets (hd j).2.2.2.1.1 (hd j).2.2.2.2.1.1 hJ (hEj j) (hBj j) i
  obtain ⟨B,hB,hflux⟩ := family_datum_sphere_flux_lipschitz hd hL hp hl
    (continuousOn_datumMagneticFluxKernel i)
  obtain ⟨D,hD,hmom⟩ := family_datum_moment_lipschitz hd hL hp hl
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro q t ht x y
  have hfree := hfree q
  have hflux := hflux q
  have hmom := hmom q
  have hjc : Continuous (current (d q).f₀) := (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
    simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj (j : Fin 3) : Continuous (fun v : Vec => v j) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous

  let F : Vec → Sphere → ℝ := fun z n => t*n.1 (curlA i)*current (d q).f₀ (z+t • n.1) (curlB i)-
    t*n.1 (curlB i)*current (d q).f₀ (z+t • n.1) (curlA i)
  have hfc (z : Vec) : Continuous (F z) := by
    have hg (j k : Fin 3) : Continuous (fun n : Sphere => t*n.1 j*current (d q).f₀ (z+t • n.1) k) :=
      (continuous_const.mul ((hproj j).comp continuous_subtype_val)).mul
        (((hproj k).comp hjc).comp (continuous_const.add
          ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)))
    exact (hg _ _).sub (hg _ _)
  have hh := abs_sphere_integral_sub_le (hfc y) (hfc x) (C:=2*D*‖y-x‖) (by
    intro n
    have hterm (j k : Fin 3) : |t*n.1 j*current (d q).f₀ (y+t • n.1) k-
        t*n.1 j*current (d q).f₀ (x+t • n.1) k|≤D*‖y-x‖ := by
      rw [← mul_sub,abs_mul,abs_mul,abs_of_pos ht.1]
      have hn : |n.1 j|≤1 := (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
      have hj : |current (d q).f₀ (y+t • n.1) k-current (d q).f₀ (x+t • n.1) k|≤D*‖y-x‖ := by
        simpa only [PiLp.sub_apply,add_sub_add_right_eq_sub] using
          (norm_coordinate_le (current (d q).f₀ (y+t • n.1)-current (d q).f₀ (x+t • n.1)) k).trans
            (hmom (x+t • n.1) (y+t • n.1)).2
      exact (mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le) hj (abs_nonneg _) (by simpa using ht.1.le)).trans
        (by simpa only [mul_one] using mul_le_of_le_one_left (by positivity : 0≤D*‖y-x‖) ht.2)
    dsimp [F]
    rw [show ∀ a b c e : ℝ, (a-b)-(c-e)=(a-c)-(b-e) by intros; ring]
    exact ((abs_sub _ _).trans (add_le_add (hterm _ _) (hterm _ _))).trans_eq (by ring))
  have hj : |(4*Real.pi)⁻¹*(∫ n, F y n ∂sphereMeasure)-
      (4*Real.pi)⁻¹*(∫ n, F x n ∂sphereMeasure)|≤2*D*‖y-x‖ := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp)
  simp only [magneticConeBoundary,sub_zero]
  simp_rw [datum_initial_magnetic_flux_normalised (d q) i ht.1]
  simp only [datumBoundarySolution]
  have halg (a b c a' b' c' : ℝ) : (a-b+c)-(a'-b'+c')=(a-a')-(b-b')+(c-c') := by ring
  rw [halg]
  exact ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x y).2 (hflux t ⟨ht.1.le,ht.2⟩ x y))) hj)).trans_eq (by ring)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_GlobalContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma family_datum_restart_control {ι : Type*} {d : ι → Datum}
    (hd : ∀ j, Admissible (d j)) {A R P L J : ℝ}
    (hA : 0≤A) (hL : 0≤L) (hJ : 0≤J)
    (hf : ∀ j z, |(d j).f₀ z|≤A)
    (hrp : ∀ j (z : Phase), (d j).f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P)
    (hl : ∀ j z w, |(d j).f₀ z-(d j).f₀ w|≤L*‖z-w‖)
    (hEj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).E₀ x‖≤J)
    (hBj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).B₀ x‖≤J) :
    ∃ D D₁ : ℝ, 0≤D ∧ 0≤D₁ ∧ ∀ j, DatumRestartControl (d j) A R P D D₁ L := by
  have hp (j : ι) (x v : Vec) (hv : P<‖v‖) : (d j).f₀ (x,v)=0 := by
    by_contra hh
    exact (not_le_of_gt hv) (hrp j (x,v) hh).2
  have hfl (j : ι) (x y v : Vec) : |(d j).f₀ (y,v)-(d j).f₀ (x,v)|≤L*‖y-x‖ := by
    simpa only [Prod.mk_sub_mk,sub_self,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using hl j (y,v) (x,v)
  choose CE hCE hEe using family_electricConeBoundary_datum_bound_global hd hA hJ hf hp hEj hBj
  choose CB hCB hBb using family_magneticConeBoundary_datum_bound_global hd hA hJ hf hp hEj hBj
  choose LE hLE hEl using family_electricConeBoundary_datum_lipschitz hd hL hJ hp hfl hEj hBj
  choose LB hLB hBl using family_magneticConeBoundary_datum_lipschitz hd hL hJ hp hfl hEj hBj
  let S := ∑ i : Fin 3, (CE i+CB i)
  let N := ∑ i : Fin 3, (LE i+LB i)
  have hS : 0≤S := Finset.sum_nonneg fun i _ => add_nonneg (hCE i) (hCB i)
  have hN : 0≤N := Finset.sum_nonneg fun i _ => add_nonneg (hLE i) (hLB i)
  have hEC (i : Fin 3) : CE i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCB i]
  have hBC (i : Fin 3) : CB i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCE i]
  have hEL (i : Fin 3) : LE i≤N := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hLE j) (hLB j)) (Finset.mem_univ i)
    dsimp [N]; linarith [hLB i]
  have hBL (i : Fin 3) : LB i≤N := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hLE j) (hLB j)) (Finset.mem_univ i)
    dsimp [N]; linarith [hLE i]
  refine ⟨3*S+J,3*N+3*J,by positivity,by positivity,?_⟩
  intro j
  refine ⟨hf j,hrp j,?_,?_,?_,?_,hl j⟩
  · intro x
    have he : ‖(d j).E₀ x‖≤J := by simpa only [norm_iteratedFDeriv_zero] using hEj j 0 (by norm_num) x
    have hb : ‖(d j).B₀ x‖≤J := by simpa only [norm_iteratedFDeriv_zero] using hBj j 0 (by norm_num) x
    exact ⟨he.trans (by linarith),hb.trans (by linarith)⟩
  · intro t ht x
    exact ⟨(norm_le_three_of_coordinate_bound hS (v:=electricBoundaryField (datumBoundarySolution (d j)) t x)
      (fun i => (hEe i j t ht x).trans (hEC i))).trans (by linarith),
      (norm_le_three_of_coordinate_bound hS (v:=magneticBoundaryField (datumBoundarySolution (d j)) t x)
      (fun i => (hBb i j t ht x).trans (hBC i))).trans (by linarith)⟩
  · intro x y
    have he := (spatial_lipschitz_of_low_jets (hd j).2.2.2.1.1 hJ (hEj j) x y).1
    have hb := (spatial_lipschitz_of_low_jets (hd j).2.2.2.2.1.1 hJ (hBj j) x y).1
    exact ⟨he.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)),
      hb.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))⟩
  · intro t ht x y
    have he := norm_le_three_of_coordinate_bound (mul_nonneg hN (norm_nonneg (y-x)))
      (v:=electricBoundaryField (datumBoundarySolution (d j)) t y-electricBoundaryField (datumBoundarySolution (d j)) t x)
      (fun i => (hEl i j t ht x y).trans (mul_le_mul_of_nonneg_right (hEL i) (norm_nonneg _)))
    have hb := norm_le_three_of_coordinate_bound (mul_nonneg hN (norm_nonneg (y-x)))
      (v:=magneticBoundaryField (datumBoundarySolution (d j)) t y-magneticBoundaryField (datumBoundarySolution (d j)) t x)
      (fun i => (hBl i j t ht x y).trans (mul_le_mul_of_nonneg_right (hBL i) (norm_nonneg _)))
    constructor
    · exact he.trans (by nlinarith [mul_nonneg hJ (norm_nonneg (y-x))])
    · exact hb.trans (by nlinarith [mul_nonneg hJ (norm_nonneg (y-x))])

theorem family_bounded_classical_prefix_oai {ι : Type*} {d : ι → Datum}
    (hd : ∀ j, Admissible (d j)) {A R P L J : ℝ}
    (hA : 0≤A) (hR : 0≤R) (hP : 0≤P) (hL : 0≤L) (hJ : 0≤J)
    (hf : ∀ j z, |(d j).f₀ z|≤A)
    (hrp : ∀ j (z : Phase), (d j).f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P)
    (hl : ∀ j z w, |(d j).f₀ z-(d j).f₀ w|≤L*‖z-w‖)
    (hEj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).E₀ x‖≤J)
    (hBj : ∀ j k, k≤2 → ∀ x, ‖iteratedFDeriv ℝ k (d j).B₀ x‖≤J) :
    ∃ T : ℝ, 0<T ∧ ∀ j, ∃ s : Solution, BoundedClassicalPrefix (d j) s T := by
  obtain ⟨D,D₁,hD,hD₁,hcaps⟩ := family_datum_restart_control hd hA hL hJ hf hrp hl hEj hBj
  obtain ⟨T,hT,hfamily⟩ := family_local_spatially_smooth_bounded_classical hd hA hR hP hD hD₁ hL hcaps
  refine ⟨T,hT,?_⟩
  intro j
  obtain ⟨s,hs,heq,hf,hE,hB⟩ := hfamily j
  obtain ⟨hfs,hEs,hBs⟩ := hs.smooth hT heq hf.1 hE.1 hB.1
  exact ⟨s,hs.toSmooth hfs hEs hBs,heq,hf,hE,hB⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RVM.family_bounded_classical_prefix_oai.{u_1} := @OAI.RVM.family_bounded_classical_prefix_oai.{u_1}
