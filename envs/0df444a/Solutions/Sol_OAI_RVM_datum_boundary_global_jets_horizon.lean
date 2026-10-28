-- Prove2me | solution 1 for OAI.RVM.datum_boundary_global_jets_horizon
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:18:51.667176+00:00
-- url     : https://prove2.me/submissions/a607a350-7560-47ef-852d-d871561bfeba

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

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

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
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

lemma integral_vec_apply {g : Vec → Vec} (hg : Integrable g) (i : Fin 3) :
    (∫ v : Vec, g v) i = ∫ v : Vec, g v i := by
  exact ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hg).symm

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeArgument
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
open Set MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma sphere_norm (n : Sphere) : ‖n.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using n.2

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


lemma contDiff_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e : H) : ContDiff ℝ ∞ (dirD F e) :=
  (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveGradient
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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma contDiff_freeWave {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (freeWave g h) :=
  (contDiff_dirD (contDiff_waveK hg) (1,0)).add (contDiff_waveK hh)

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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SmoothIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u v

section SpatialDerivatives
variable {A E W : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma contDiff_iteratedFDeriv_slice {F : A × E → W} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : A × E => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E W).symm.contDiff.comp hF
  | succ n ih =>
    let G : A × E → (E [×n]→L[ℝ] W) := fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2
    change ContDiff ℝ ∞ G at ih
    have he (p : A × E) : fderiv ℝ (fun x => G (p.1,x)) p.2 =
        (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ A E) := by
      have hin : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ A E) p.2 := by
        convert (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1 <;> rfl
      exact ((ih.differentiable (by simp) p).hasFDerivAt.comp p.2 hin).fderiv
    simp only [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    change ContDiff ℝ ∞ (fun p : A × E =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm (fderiv ℝ (fun x => G (p.1,x)) p.2))
    simp_rw [he]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm.contDiff.comp
      ((ih.fderiv_right (m:=∞) (by simp)).clm_comp contDiff_const)

end SpatialDerivatives

section CompactFamily
variable {α : Type v} {E : Type u} [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma SmoothCompactFamily.ofJoint {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {G : A × E → W} (hG : ContDiff ℝ ∞ G) {ι : α → A} (hι : Continuous ι) :
    SmoothCompactFamily (fun a x => G (ι a,x)) := by
  refine ⟨fun a => hG.comp (contDiff_const.prodMk contDiff_id),fun n => ?_⟩
  exact (contDiff_iteratedFDeriv_slice hG n).continuous.comp
    ((hι.comp continuous_snd).prodMk continuous_fst)

lemma SmoothCompactFamily.continuous {F : α → E → W} (hF : SmoothCompactFamily F) :
    Continuous (fun p : E × α => F p.2 p.1) := by
  have h := (continuousMultilinearCurryFin0 ℝ E W).continuous.comp (hF.2 0)
  simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,LinearIsometryEquiv.apply_symm_apply] using h

lemma SmoothCompactFamily.derivFamily {F : α → E → W} (hF : SmoothCompactFamily F) :
    SmoothCompactFamily (fun a => fderiv ℝ (F a)) := by
  refine ⟨fun a => (hF.1 a).fderiv_right (m:=∞) (by simp),fun n => ?_⟩
  have he (p : E × α) : iteratedFDeriv ℝ n (fderiv ℝ (F p.2)) p.1 =
      continuousMultilinearCurryRightEquiv' ℝ n E W (iteratedFDeriv ℝ (n+1) (F p.2) p.1) := by
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]
  simp_rw [he]
  exact (continuousMultilinearCurryRightEquiv' ℝ n E W).continuous.comp (hF.2 (n+1))

variable [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α]
  [ProperSpace E] [CompleteSpace W]

omit [CompleteSpace W] in
lemma hasFDerivAt_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) (x : E) :
    HasFDerivAt (fun y => ∫ a, F a y ∂μ) (∫ a, fderiv ℝ (F a) x ∂μ) x := by
  have hD := hF.derivFamily.continuous
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall x 1) (bound:=fun _ => C) (F':=fun y a => fderiv ℝ (F a) y)
    (closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y => (hF.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun a y hy => hC _ ⟨(y,a),⟨hy,mem_univ a⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun a y _ => ((hF.1 a).differentiable (by simp) y).hasFDerivAt)

lemma contDiff_integral_smoothFamily_nat (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : α → E → W}, SmoothCompactFamily F → ContDiff ℝ n (fun x => ∫ a, F a x ∂μ) := by
  induction n with
  | zero =>
    intro W _ _ _ F hF
    apply contDiff_zero.mpr
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hF.continuous.continuousOn
    intro x a _ ha
    exact (ha (mem_univ a)).elim
  | succ n ih =>
    intro W _ _ _ F hF
    rw [show (↑(n+1) : ℕ∞ω) = ↑n+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_smoothFamily μ hF x).differentiableAt,by simp,?_⟩
    have he : fderiv ℝ (fun x => ∫ a, F a x ∂μ) = (fun x => ∫ a, fderiv ℝ (F a) x ∂μ) := by
      funext x
      exact (hasFDerivAt_integral_smoothFamily μ hF x).fderiv
    rw [he]
    exact ih hF.derivFamily

lemma contDiff_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) : ContDiff ℝ ∞ (fun x => ∫ a, F a x ∂μ) := by
  rw [contDiff_infty]
  exact fun n => contDiff_integral_smoothFamily_nat μ n hF

lemma norm_iteratedFDeriv_integral_le (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : α → E → W}, SmoothCompactFamily F → ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => ∫ a, F a y ∂μ) x‖ ≤
        ∫ a, ‖iteratedFDeriv ℝ n (F a) x‖ ∂μ := by
  induction n with
  | zero =>
    intro W _ _ _ F hF x
    simpa only [norm_iteratedFDeriv_zero] using norm_integral_le_integral_norm (fun a => F a x)
  | succ n ih =>
    intro W _ _ _ F hF x
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ (fun y => ∫ a, F a y ∂μ) = (fun y => ∫ a, fderiv ℝ (F a) y ∂μ) := by
      funext y
      exact (hasFDerivAt_integral_smoothFamily μ hF y).fderiv
    rw [he]
    simpa only [norm_iteratedFDeriv_fderiv] using ih hF.derivFamily x

end CompactFamily

variable {E W : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

attribute [local instance] Measure.Subtype.measureSpace in
lemma norm_iteratedFDeriv_intervalIntegral_le {F : ℝ × E → W} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) {a b : ℝ} (hab : a≤b) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ r in a..b, F (r,y)) x‖ ≤
      ∫ r in a..b, ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖ := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := norm_iteratedFDeriv_integral_le
    (E:=E) (W:=W) (volume : Measure (Icc a b)) n
    (SmoothCompactFamily.ofJoint (α:=Icc a b) hF continuous_subtype_val) x
  have he (y : E) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  have he' : (∫ r : Icc a b, ‖iteratedFDeriv ℝ n (fun y => F ((r:ℝ),y)) x‖) =
      ∫ r in a..b, ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖ := by
    rw [integral_subtype measurableSet_Icc (fun r => ‖iteratedFDeriv ℝ n (fun y => F (r,y)) x‖),
      integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
  simp_rw [he] at hh
  rwa [he'] at hh

attribute [local instance] Measure.Subtype.measureSpace in
lemma contDiff_spatial_intervalIntegral {F : ℝ × E → W} (hF : ContDiff ℝ ∞ F)
    {a b : ℝ} (hab : a≤b) : ContDiff ℝ ∞ (fun y => ∫ r in a..b, F (r,y)) := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := contDiff_integral_smoothFamily (volume : Measure (Icc a b))
    (SmoothCompactFamily.ofJoint (α:=Icc a b) hF continuous_subtype_val)
  have he (y : E) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  simpa only [he] using hh

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_TameDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

variable {U V W Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma norm_iteratedFDeriv_precomp_contraction (f : V → W) (hf : ContDiff ℝ ∞ f)
    (L : U →L[ℝ] V) (hL : ‖L‖ ≤ 1) (n : ℕ) (x : U) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  exact ((iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le _).trans (by
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hL) (norm_nonneg _)).trans_eq (mul_one _))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleTame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma smooth_compact_jets_bound {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hb (i : Fin (n+1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hc.iteratedFDeriv (i:ℕ))
    exact ⟨max C 0,le_max_right _ _,fun x => (hC x).trans (le_max_left _ _)⟩
  choose C hC hbound using hb
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro i hi x
  exact (hbound ⟨i,by omega⟩ x).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ _))

lemma norm_iteratedFDeriv_phase_slice {f : Phase → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x v : Vec) :
    ‖iteratedFDeriv ℝ n (fun y => f (y,v)) x‖ ≤ ‖iteratedFDeriv ℝ n f (x,v)‖ := by
  let g : Phase → ℝ := fun z => f (z+(0,v))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have hh := norm_iteratedFDeriv_precomp_contraction g hg (ContinuousLinearMap.inl ℝ Vec Vec)
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro w
      simp only [ContinuousLinearMap.inl_apply,Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg w),one_mul]
      exact le_rfl) n x
  simpa only [g,Function.comp_def,ContinuousLinearMap.inl_apply,iteratedFDeriv_comp_add_right,
    Prod.mk_add_mk,add_zero,zero_add] using hh

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRegularity
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

section

attribute [local instance] Measure.Subtype.measureSpace

variable (t P : ℝ)
local instance instCompactSpaceElemVecSphere : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

end

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_BoundaryJets
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

section
universe u v

lemma SmoothCompactFamily.const_smul {α : Type v} {E W : Type u} [TopologicalSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : α → E → W} (hF : SmoothCompactFamily F) {c : α → ℝ} (hc : Continuous c) :
    SmoothCompactFamily (fun a x => c a • F a x) := by
  refine ⟨fun a => (hF.1 a).const_smul _,fun n => ?_⟩
  have he (p : E × α) : iteratedFDeriv ℝ n (fun x => c p.2 • F p.2 x) p.1 =
      c p.2 • iteratedFDeriv ℝ n (F p.2) p.1 :=
    iteratedFDeriv_const_smul_apply' ((hF.1 p.2).of_le (by exact_mod_cast le_top)).contDiffAt
  simp_rw [he]
  exact (hc.comp continuous_snd).smul (hF.2 n)

lemma norm_iteratedFDeriv_add_le {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f g : U → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : U) :
    ‖iteratedFDeriv ℝ n (fun y => f y+g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖+‖iteratedFDeriv ℝ n g x‖ := by
  change ‖iteratedFDeriv ℝ n (f+g) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (i:=n) (x:=x) ((hf.of_le (by exact_mod_cast le_top)).contDiffAt)
    ((hg.of_le (by exact_mod_cast le_top)).contDiffAt)]
  exact norm_add_le _ _

lemma norm_iteratedFDeriv_sub_le {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f g : U → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (n : ℕ) (x : U) :
    ‖iteratedFDeriv ℝ n (fun y => f y-g y) x‖ ≤
      ‖iteratedFDeriv ℝ n f x‖+‖iteratedFDeriv ℝ n g x‖ := by
  change ‖iteratedFDeriv ℝ n (f-g) x‖ ≤ _
  rw [iteratedFDeriv_sub_apply (i:=n) (x:=x) ((hf.of_le (by exact_mod_cast le_top)).contDiffAt)
    ((hg.of_le (by exact_mod_cast le_top)).contDiffAt)]
  exact norm_sub_le _ _

local instance localInst_rae2e36_1 : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
lemma sphere_average_derivative_bound {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {F : Sphere → Vec → W} (hF : SmoothCompactFamily F) (n : ℕ) {C : ℝ}
    (hC : ∀ a x, ‖iteratedFDeriv ℝ n (F a) x‖≤C) (x : Vec) :
    ‖iteratedFDeriv ℝ n (fun y => (4*Real.pi)⁻¹ • ∫ a, F a y ∂sphereMeasure) x‖ ≤ C := by
  have hI := contDiff_integral_smoothFamily sphereMeasure hF
  rw [iteratedFDeriv_const_smul_apply' ((hI.of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul,
    Real.norm_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  have hi := norm_iteratedFDeriv_integral_le sphereMeasure n hF x
  have hint : Integrable (fun a => ‖iteratedFDeriv ℝ n (F a) x‖) sphereMeasure :=
    ((hF.2 n).comp (continuous_const.prodMk continuous_id)).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb := integral_mono hint (integrable_const C) (fun a => hC a x)
  simp only [integral_const,smul_eq_mul,sphere_area] at hb
  exact (mul_le_mul_of_nonneg_left (hi.trans hb) (by positivity)).trans_eq (by field_simp)

end

lemma norm_iteratedFDeriv_coordinate {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {F : U → Vec} (hF : ContDiff ℝ ∞ F) (n : ℕ) (x : U) (i : Fin 3) :
    ‖iteratedFDeriv ℝ n (fun y => F y i) x‖≤‖iteratedFDeriv ℝ n F x‖ := by
  let L := PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i
  have hL : ‖L‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [L,PiLp.proj_apply,one_mul,Real.norm_eq_abs] using norm_coordinate_le v i
  have hh := L.norm_iteratedFDeriv_comp_left (x:=x) hF.contDiffAt (by exact_mod_cast le_top : (n:ℕ∞ω)≤∞)
  exact hh.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))

lemma norm_iteratedFDeriv_curl_coordinate {F : Vec → Vec} (hF : ContDiff ℝ ∞ F)
    (n : ℕ) (x : Vec) (i : Fin 3) :
    ‖iteratedFDeriv ℝ n (fun y => curl F y i) x‖≤2*‖iteratedFDeriv ℝ (n+1) F x‖ := by
  have he : (fun y => curl F y i)=(fun y => (fderiv ℝ F y (basis (curlA i))) (curlB i)-
      (fderiv ℝ F y (basis (curlB i))) (curlA i)) := by
    funext y
    fin_cases i <;> simp [curl,curlA,curlB,spatialPartial,coordinate_fderiv_apply (hF.differentiable (by simp))]
  have hd := hF.fderiv_right (m:=∞) (by simp)
  have ha (a b : Fin 3) : ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ F y (basis a) b) x‖≤
      ‖iteratedFDeriv ℝ (n+1) F x‖ := by
    have hb := norm_iteratedFDeriv_clm_apply_const hd.contDiffAt
      (by exact_mod_cast le_top : (n:ℕ∞ω)≤∞) (x:=x) (c:=basis a)
    have hba : ‖basis a‖=1 := by
      change ‖(PiLp.single 2 a (1:ℝ) : Vec)‖=1
      simp
    rw [hba,one_mul,norm_iteratedFDeriv_fderiv] at hb
    exact (norm_iteratedFDeriv_coordinate (hd.clm_apply contDiff_const) n x b).trans hb
  rw [he]
  have haS := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) (curlB i)).contDiff.comp (hd.clm_apply (contDiff_const (c:=basis (curlA i))))
  have hbS := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) (curlA i)).contDiff.comp (hd.clm_apply (contDiff_const (c:=basis (curlB i))))
  exact (norm_iteratedFDeriv_sub_le haS hbS n x).trans ((add_le_add (ha _ _) (ha _ _)).trans_eq (by ring))

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma datum_velocity_integrable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {f : Phase → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {H : Vec × Vec → W} (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ))
    (x n : Vec) (hn : ‖n‖=1) : Integrable (fun v => f (x,v) • H (n,v)) := by
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hf.comp (continuous_const.prodMk continuous_id)).smul
      (hH.comp_continuous (continuous_const.prodMk continuous_id)
        (fun v => ⟨mem_sphere_zero_iff_norm.mpr hn,mem_univ v⟩))
  · exact HasCompactSupport.intro hK (fun v hv => by rw [hz x v hv,zero_smul])

lemma datumWeightedSphere_flux {f : Phase → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {H : Vec × Vec → Vec} (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) (t : ℝ) (x : Vec) :
    datumWeightedSphere f (fun p => dot p.1 (H (-p.1,p.2))) (t,x)=
      (4*Real.pi)⁻¹*(∫ a : Sphere, t*dot a.1 (∫ v, f (x+t • a.1,v) • H (-a.1,v)) ∂sphereMeasure) := by
  unfold datumWeightedSphere
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  have hi := datum_velocity_integrable hf hc hH (x+t • a.1) (-a.1) (by rw [norm_neg,sphere_norm a])
  have he := (innerSL ℝ a.1).integral_comp_comm hi
  simp only [innerSL_apply_apply,←dot_eq_inner,dot_smul_right] at he
  rw [←he]

lemma continuousOn_fluxWeight {H : Vec × Vec → Vec}
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ContinuousOn (fun p : Vec × Vec => dot p.1 (H (-p.1,p.2))) (sphere (0:Vec) 1 ×ˢ univ) := by
  exact (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn
    (continuous_fst.continuousOn.prodMk (hH.comp
    (continuous_fst.neg.prodMk continuous_snd).continuousOn (by
      intro p hp
      exact ⟨by simpa only [mem_sphere_zero_iff_norm,Pi.neg_apply,norm_neg] using hp.1,mem_univ _⟩)))

lemma datum_current_eq_integral {d : Datum} (hd : Admissible d) (x : Vec) (j : Fin 3) :
    current d.f₀ x j=∫ v, d.f₀ (x,v)*velocity v j := by
  have hi := datum_velocity_integrable hd.1.continuous hd.2.1
    (((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn)
    x (basis 0) (by change ‖(PiLp.single 2 0 (1:ℝ) : Vec)‖=1; simp)
  exact integral_vec_apply hi j

lemma datumWeightedSphere_rho (d : Datum) (t : ℝ) (x : Vec) (i : Fin 3) :
    datumWeightedSphere d.f₀ (fun p => p.1 i) (t,x)=
      (4*Real.pi)⁻¹*(∫ a : Sphere, t*a.1 i*rho d.f₀ (x+t • a.1) ∂sphereMeasure) := by
  unfold datumWeightedSphere rho
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  rw [integral_mul_const]
  ring

lemma datumWeightedSphere_waveCurrent {d : Datum} (hd : Admissible d) (t : ℝ) (x : Vec) (i : Fin 3) :
    datumWeightedSphere d.f₀ (fun p => velocity p.2 i) (t,x)=
      waveK (fun y => current d.f₀ y i) (t,x) := by
  simp only [datumWeightedSphere,waveK,sphereSum,integral_const_mul,datum_current_eq_integral hd]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_MagneticBoundaryJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma continuous_datumMagneticMoment (i : Fin 3) :
    Continuous (fun p : Vec × Vec => p.1 (curlA i)*velocity p.2 (curlB i)-
      p.1 (curlB i)*velocity p.2 (curlA i)) := by
  have hp (j : Fin 3) : Continuous (fun v : Vec => v j) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous
  exact ((hp _).comp continuous_fst |>.mul ((hp _).comp ((contDiff_velocity (k:=1)).continuous.comp continuous_snd))).sub
    ((hp _).comp continuous_fst |>.mul ((hp _).comp ((contDiff_velocity (k:=1)).continuous.comp continuous_snd)))

lemma datumWeightedSphere_magneticMoment {d : Datum} (hd : Admissible d) (t : ℝ) (x : Vec) (i : Fin 3) :
    datumWeightedSphere d.f₀ (fun p => p.1 (curlA i)*velocity p.2 (curlB i)-
      p.1 (curlB i)*velocity p.2 (curlA i)) (t,x)=
      (4*Real.pi)⁻¹*(∫ a : Sphere,
        t*a.1 (curlA i)*current d.f₀ (x+t • a.1) (curlB i)-
        t*a.1 (curlB i)*current d.f₀ (x+t • a.1) (curlA i) ∂sphereMeasure) := by
  unfold datumWeightedSphere
  congr 1
  apply integral_congr_ae
  filter_upwards [] with a
  have hi (j : Fin 3) : Integrable (fun v => d.f₀ (x+t • a.1,v)*velocity v j) := by
    exact datum_velocity_integrable hd.1.continuous hd.2.1
      (((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp
        ((contDiff_velocity (k:=1)).continuous.comp continuous_snd)).continuousOn)
      (x+t • a.1) a.1 (sphere_norm a)
  simp_rw [mul_sub,show ∀ j k : Fin 3, ∀ v : Vec, d.f₀ (x+t • a.1,v)*(a.1 j*velocity v k)=
    a.1 j*(d.f₀ (x+t • a.1,v)*velocity v k) by intros; ring]
  rw [integral_sub ((hi _).const_mul _) ((hi _).const_mul _),integral_const_mul,integral_const_mul,
    datum_current_eq_integral hd,datum_current_eq_integral hd]
  ring

lemma norm_iteratedFDeriv_vec_le {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {F : U → Vec} (hF : ContDiff ℝ ∞ F) (n : ℕ) {C : ℝ} (hC : 0≤C)
    (h : ∀ i : Fin 3, ∀ x, ‖iteratedFDeriv ℝ n (fun y => F y i) x‖≤C) (x : U) :
    ‖iteratedFDeriv ℝ n F x‖≤3*C := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  have hb (i : Fin 3) : |(iteratedFDeriv ℝ n F x v) i|≤C*(∏ j, ‖v j‖) := by
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).iteratedFDeriv_comp_left (x:=x)
      hF.contDiffAt (by exact_mod_cast le_top : (n:ℕ∞ω)≤∞)
    have ha := ((iteratedFDeriv ℝ n (fun y => F y i) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h i x) (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
    change ‖iteratedFDeriv ℝ n ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i) ∘ F) x v‖≤_ at ha
    rw [he] at ha
    exact ha
  exact (norm_le_three_of_coordinate_bound (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _))) hb).trans_eq (by ring)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_GlobalBoundaryBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM
attribute [local instance] Measure.Subtype.measureSpace
section SphereJets
local instance instCompactSpaceElemVecSphere_1 : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
lemma freeWave_derivative_bound_horizon {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (n : ℕ) (H : ℝ) {C : ℝ} (hC : 0≤C)
    (hg0 : ∀ x, ‖iteratedFDeriv ℝ n g x‖≤C)
    (hg1 : ∀ x, ‖iteratedFDeriv ℝ (n+1) g x‖≤C)
    (hh0 : ∀ x, ‖iteratedFDeriv ℝ n h x‖≤C)
    {t : ℝ} (ht : t∈Icc (0:ℝ) H) (x : Vec) :
    ‖iteratedFDeriv ℝ n (fun y => freeWave g h (t,y)) x‖≤(1+2*H)*C := by
  let A : Sphere → Vec → ℝ := fun a y => g (y+t • a.1)
  let B : Sphere → Vec → ℝ := fun a y => fderiv ℝ g (y+t • a.1) a.1
  let D : Sphere → Vec → ℝ := fun a y => h (y+t • a.1)
  have hA : SmoothCompactFamily A := SmoothCompactFamily.ofJoint
    (hg.comp (contDiff_snd.add ((contDiff_const (c:=t)).smul contDiff_fst))) continuous_subtype_val
  have hB : SmoothCompactFamily B := SmoothCompactFamily.ofJoint
    (((hg.fderiv_right (m:=∞) (by simp)).comp (contDiff_snd.add ((contDiff_const (c:=t)).smul contDiff_fst))).clm_apply
      contDiff_fst) continuous_subtype_val
  have hD : SmoothCompactFamily D := SmoothCompactFamily.ofJoint
    (hh.comp (contDiff_snd.add ((contDiff_const (c:=t)).smul contDiff_fst))) continuous_subtype_val
  have ha := sphere_average_derivative_bound hA n (fun a y => by
    dsimp only [A]; rw [iteratedFDeriv_comp_add_right]; exact hg0 _) x
  have hd := sphere_average_derivative_bound hD n (fun a y => by
    dsimp only [D]; rw [iteratedFDeriv_comp_add_right]; exact hh0 _) x
  have hb := sphere_average_derivative_bound hB n (fun a y => by
    change ‖iteratedFDeriv ℝ n (fun z => (fun w => fderiv ℝ g w a.1) (z+t • a.1)) y‖≤C
    rw [iteratedFDeriv_comp_add_right (f:=fun w => fderiv ℝ g w a.1) n (t • a.1) y]
    have hh' := norm_iteratedFDeriv_clm_apply_const (x:=y+t • a.1)
      (hg.fderiv_right (m:=∞) (by simp)).contDiffAt (by exact_mod_cast le_top : (n:ℕ∞ω)≤∞)
      (c:=a.1)
    rw [sphere_norm a,one_mul,norm_iteratedFDeriv_fderiv] at hh'
    exact hh'.trans (hg1 _)) x
  let a : Vec → ℝ := fun y => (4*Real.pi)⁻¹ • ∫ u, A u y ∂sphereMeasure
  let b : Vec → ℝ := fun y => (4*Real.pi)⁻¹ • ∫ u, B u y ∂sphereMeasure
  let c : Vec → ℝ := fun y => (4*Real.pi)⁻¹ • ∫ u, D u y ∂sphereMeasure
  have has : ContDiff ℝ ∞ a := (contDiff_integral_smoothFamily sphereMeasure hA).const_smul _
  have hbs : ContDiff ℝ ∞ b := (contDiff_integral_smoothFamily sphereMeasure hB).const_smul _
  have hcs : ContDiff ℝ ∞ c := (contDiff_integral_smoothFamily sphereMeasure hD).const_smul _
  have he : (fun y => freeWave g h (t,y))=(fun y => a y+t • b y+t • c y) := by
    funext y
    rw [freeWave_sphere hg]
    simp only [a,b,c,A,B,D,smul_eq_mul]
    ring
  rw [he]
  have hb' : ‖iteratedFDeriv ℝ n (fun y => t • b y) x‖≤t*C := by
    rw [iteratedFDeriv_const_smul_apply' ((hbs.of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul,
      Real.norm_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left hb ht.1
  have hc' : ‖iteratedFDeriv ℝ n (fun y => t • c y) x‖≤t*C := by
    rw [iteratedFDeriv_const_smul_apply' ((hcs.of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul,
      Real.norm_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left hd ht.1
  exact (norm_iteratedFDeriv_add_le (has.add (hbs.const_smul t)) (hcs.const_smul t) n x).trans
    ((add_le_add ((norm_iteratedFDeriv_add_le has (hbs.const_smul t) n x).trans
      (add_le_add ha hb')) hc').trans (by nlinarith [ht.2]))

end SphereJets
lemma BoundedSmooth.freeWave_coordinate_jets_horizon {E B : Vec → Vec}
    (hE : BoundedSmooth E) (hB : BoundedSmooth B) (H : ℝ) (hH : 0≤H) (n : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) H, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => freeWave (fun z => E z i) (fun z => curl B z i) (t,y)) x‖≤C ∧
      ‖iteratedFDeriv ℝ n (fun y => freeWave (fun z => B z i) (fun z => -curl E z i) (t,y)) x‖≤C := by
  obtain ⟨A,hA⟩ := hE.2 n
  obtain ⟨D,hD⟩ := hE.2 (n+1)
  obtain ⟨K,hK⟩ := hB.2 n
  obtain ⟨L,hL⟩ := hB.2 (n+1)
  let C := max A 0+2*max D 0+max K 0+2*max L 0
  have hC : 0≤C := by dsimp [C]; positivity
  have hAC : A≤C := by dsimp [C]; linarith [le_max_left A 0,le_max_right D 0,le_max_right K 0,le_max_right L 0]
  have hDC : 2*D≤C := by dsimp [C]; linarith [le_max_left D 0,le_max_right A 0,le_max_right K 0,le_max_right L 0]
  have hKC : K≤C := by dsimp [C]; linarith [le_max_left K 0,le_max_right D 0,le_max_right A 0,le_max_right L 0]
  have hLC : 2*L≤C := by dsimp [C]; linarith [le_max_left L 0,le_max_right D 0,le_max_right K 0,le_max_right A 0]
  have hD0 : 0≤D := (norm_nonneg _).trans (hD 0)
  have hL0 : 0≤L := (norm_nonneg _).trans (hL 0)
  have hp : ContDiff ℝ ∞ (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  refine ⟨(1+2*H)*C,by positivity,?_⟩
  intro t ht x
  constructor
  · apply freeWave_derivative_bound_horizon (hp.comp hE.1) (hp.comp (contDiff_curl hB.1)) n H hC
      (fun y => (norm_iteratedFDeriv_coordinate hE.1 n y i).trans ((hA y).trans hAC))
      (fun y => (norm_iteratedFDeriv_coordinate hE.1 (n+1) y i).trans ((hD y).trans (by linarith)))
      (fun y => (norm_iteratedFDeriv_curl_coordinate hB.1 n y i).trans
        ((mul_le_mul_of_nonneg_left (hL y) (by norm_num)).trans hLC)) ht x
  · apply freeWave_derivative_bound_horizon (hp.comp hB.1) (hp.comp (contDiff_curl hE.1) |>.neg) n H hC
      (fun y => (norm_iteratedFDeriv_coordinate hB.1 n y i).trans ((hK y).trans hKC))
      (fun y => (norm_iteratedFDeriv_coordinate hB.1 (n+1) y i).trans ((hL y).trans (by linarith))) _ ht x
    intro y
    change ‖iteratedFDeriv ℝ n (-(fun z => curl E z i)) y‖≤C
    rw [iteratedFDeriv_neg_apply,norm_neg]
    exact (norm_iteratedFDeriv_curl_coordinate hE.1 n y i).trans
      ((mul_le_mul_of_nonneg_left (hD y) (by norm_num)).trans hDC)

lemma datumWeightedSphere_smooth_bound_horizon {f : Phase → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) {H : Vec × Vec → ℝ}
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) (n : ℕ) (T : ℝ) (hT : 0≤T) :
    ContDiff ℝ ∞ (datumWeightedSphere f H) ∧ ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) T, ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => datumWeightedSphere f H (t,y)) x‖≤C := by
  obtain ⟨P,hP⟩ := (hc.image continuous_snd).isBounded.exists_norm_le
  have hzero (x v : Vec) (hv : v∉closedBall (0:Vec) P) : f (x,v)=0 := by
    by_contra hne
    exact hv (mem_closedBall_zero_iff.mpr (hP v ⟨(x,v),subset_tsupport _ hne,rfl⟩))
  let : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let : CompactSpace (closedBall (0:Vec) P) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : IsFiniteMeasure (volume : Measure (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  let α := Sphere × closedBall (0:Vec) P
  let μ : Measure α := sphereMeasure.prod volume
  let c : α → ℝ := fun a => H (a.1.1,a.2.1)
  let F : α → (ℝ × Vec) → ℝ := fun a p => f (p.2+p.1 • a.1.1,a.2.1)
  have hcc : Continuous c := hH.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
    (fun a => ⟨a.1.2,mem_univ _⟩)
  have hF : SmoothCompactFamily F := SmoothCompactFamily.ofJoint
    (hf.comp ((contDiff_snd.snd.add (contDiff_snd.fst.smul contDiff_fst.fst)).prodMk contDiff_fst.snd))
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have hG := hF.const_smul hcc
  have he : datumWeightedSphere f H=(fun p : ℝ × Vec => (4*Real.pi)⁻¹*p.1*(∫ a, c a*F a p ∂μ)) := by
    funext p
    have hint : Integrable (fun a : α => c a*F a p) μ :=
      (hcc.mul (hF.continuous.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hi : (∫ a : α, c a*F a p ∂μ)=
        ∫ a : Sphere, ∫ v : Vec, f (p.2+p.1 • a.1,v)*H (a.1,v) ∂volume ∂sphereMeasure := by
      rw [show μ=sphereMeasure.prod volume from rfl,integral_prod _ hint]
      apply integral_congr_ae
      exact ae_of_all _ (fun a => by
        dsimp only [c,F]
        rw [integral_subtype measurableSet_closedBall (fun v => H (a.1,v)*f (p.2+p.1 • a.1,v))]
        have hz : (∫ v in closedBall (0:Vec) P, H (a.1,v)*f (p.2+p.1 • a.1,v))=
            ∫ v : Vec, H (a.1,v)*f (p.2+p.1 • a.1,v) := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro v hv
          rw [hzero _ _ hv,mul_zero]
        rw [hz]
        apply integral_congr_ae
        exact ae_of_all _ (fun v => mul_comm _ _))
    rw [hi]
    simp only [datumWeightedSphere,integral_const_mul]
    ring
  have hs : ContDiff ℝ ∞ (datumWeightedSphere f H) := by
    rw [he]
    exact (contDiff_const.mul contDiff_fst).mul (contDiff_integral_smoothFamily μ hG)
  refine ⟨hs,?_⟩
  obtain ⟨D,hD,hd⟩ := smooth_compact_jets_bound hf hc n
  obtain ⟨L,hL⟩ := hcc.bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
  let C := max L 0
  have hC : 0≤C := le_max_right _ _
  have hcB (a : α) : |c a|≤C := (hL a).trans (le_max_left _ _)
  refine ⟨(4*Real.pi)⁻¹*(T*(μ.real univ*(C*D))),by positivity,?_⟩
  intro t ht x
  have hFt : SmoothCompactFamily (fun a : α => fun y : Vec => f (y+t • a.1.1,a.2.1)) :=
    SmoothCompactFamily.ofJoint
      (hf.comp ((contDiff_snd.add ((contDiff_const (c:=t)).smul contDiff_fst.fst)).prodMk contDiff_fst.snd))
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
  have hGt := hFt.const_smul hcc
  have hj := norm_iteratedFDeriv_integral_le μ n hGt x
  have hb (a : α) : ‖iteratedFDeriv ℝ n (fun y => c a*f (y+t • a.1.1,a.2.1)) x‖≤C*D := by
    rw [show (fun y => c a*f (y+t • a.1.1,a.2.1))=(fun y => c a • (fun z => f (z,a.2.1)) (y+t • a.1.1)) from rfl,
      iteratedFDeriv_const_smul_apply' (((hFt.1 a).of_le (by exact_mod_cast le_top)).contDiffAt),norm_smul,
      Real.norm_eq_abs,iteratedFDeriv_comp_add_right (f:=fun z => f (z,a.2.1)) n (t • a.1.1) x]
    exact mul_le_mul (hcB a) ((norm_iteratedFDeriv_phase_slice hf n _ _).trans (hd n le_rfl _))
      (norm_nonneg _) hC
  have hint : Integrable (fun a => ‖iteratedFDeriv ℝ n (fun y => c a • f (y+t • a.1.1,a.2.1)) x‖) μ :=
    ((hGt.2 n).comp (continuous_const.prodMk continuous_id)).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hij := hj.trans (integral_mono hint (integrable_const (C*D)) hb)
  simp only [integral_const,smul_eq_mul] at hij
  have hej : (fun y => datumWeightedSphere f H (t,y))=
      (fun y => ((4*Real.pi)⁻¹*t) • (∫ a, c a • f (y+t • a.1.1,a.2.1) ∂μ)) := by
    funext y
    rw [he]
    rfl
  rw [hej,iteratedFDeriv_const_smul_apply' (((contDiff_integral_smoothFamily μ hGt).of_le
    (by exact_mod_cast le_top)).contDiffAt),norm_smul,Real.norm_of_nonneg (mul_nonneg (by positivity) ht.1 : 0≤(4*Real.pi)⁻¹*t)]
  exact (mul_le_mul_of_nonneg_left hij (mul_nonneg (by positivity) ht.1)).trans (by
    have hn : 0≤μ.real univ*(C*D) := by positivity
    calc
      _ = (4*Real.pi)⁻¹*(t*(μ.real univ*(C*D))) := by ring
      _ ≤ (4*Real.pi)⁻¹*(T*(μ.real univ*(C*D))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht.2 hn) (by positivity))

lemma electricConeBoundary_datum_jets_horizon {d : Datum} (hd : Admissible d) (T : ℝ) (hT : 0≤T) (k : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T,
      ContDiff ℝ ∞ (fun x => electricConeBoundary (datumBoundarySolution d) t x i 0) ∧
      ∀ x, ‖iteratedFDeriv ℝ k (fun y => electricConeBoundary (datumBoundarySolution d) t y i 0) x‖≤C := by
  have hp (j : Fin 3) : ContDiff ℝ ∞ (fun v : Vec => v j) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).contDiff
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_jets_horizon hd.2.2.2.1 hd.2.2.2.2.1 T hT k i
  obtain ⟨hFs,B,hB,hflux⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    (continuousOn_fluxWeight (continuousOn_datumElectricFluxKernel i)) k T hT
  obtain ⟨hRs,D,hD,hrho⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    (((hp i).continuous.comp continuous_fst).continuousOn) k T hT
  obtain ⟨hJs,L,hL,hcurrent⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    (((hp i).continuous.comp ((contDiff_velocity (k:=1)).continuous.comp continuous_snd)).continuousOn) k T hT
  let a := freeWave (fun y => d.E₀ y i) (fun y => curl d.B₀ y i)
  let b := datumWeightedSphere d.f₀ (fun p => dot p.1 (datumElectricFluxKernel i (-p.1,p.2)))
  let c := datumWeightedSphere d.f₀ (fun p => p.1 i)
  let e := datumWeightedSphere d.f₀ (fun p => velocity p.2 i)
  have has : ContDiff ℝ ∞ a := contDiff_freeWave ((hp i).comp hd.2.2.2.1.1)
    ((hp i).comp (contDiff_curl hd.2.2.2.2.1.1))
  refine ⟨A+B+D+L,by positivity,?_⟩
  intro t ht
  have heq : (fun x => electricConeBoundary (datumBoundarySolution d) t x i 0)=
      (fun x => a (t,x)-b (t,x)-c (t,x)-e (t,x)) := by
    funext x
    simp only [electricConeBoundary,sub_zero]
    simp_rw [datum_initial_electric_flux_normalised d i ht.1]
    rw [←datumWeightedSphere_flux hd.1.continuous hd.2.1 (continuousOn_datumElectricFluxKernel i)]
    simp only [datumBoundarySolution]
    rw [←datumWeightedSphere_rho,←datumWeightedSphere_waveCurrent hd]
  rw [heq]
  have ha := has.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hb := hFs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hc := hRs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hd' := hJs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  refine ⟨((ha.sub hb).sub hc).sub hd',?_⟩
  intro x
  exact (norm_iteratedFDeriv_sub_le ((ha.sub hb).sub hc) hd' k x).trans (add_le_add
    ((norm_iteratedFDeriv_sub_le (ha.sub hb) hc k x).trans (add_le_add
      ((norm_iteratedFDeriv_sub_le ha hb k x).trans (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x).1
        (hflux t ⟨ht.1.le,ht.2⟩ x))) (hrho t ⟨ht.1.le,ht.2⟩ x)))
    (hcurrent t ⟨ht.1.le,ht.2⟩ x))

lemma magneticConeBoundary_datum_jets_horizon {d : Datum} (hd : Admissible d) (T : ℝ) (hT : 0≤T) (k : ℕ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) T,
      ContDiff ℝ ∞ (fun x => magneticConeBoundary (datumBoundarySolution d) t x i 0) ∧
      ∀ x, ‖iteratedFDeriv ℝ k (fun y => magneticConeBoundary (datumBoundarySolution d) t y i 0) x‖≤C := by
  have hp (j : Fin 3) : ContDiff ℝ ∞ (fun v : Vec => v j) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).contDiff
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_jets_horizon hd.2.2.2.1 hd.2.2.2.2.1 T hT k i
  obtain ⟨hFs,B,hB,hflux⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    (continuousOn_fluxWeight (continuousOn_datumMagneticFluxKernel i)) k T hT
  obtain ⟨hRs,D,hD,hmoment⟩ := datumWeightedSphere_smooth_bound_horizon hd.1 hd.2.1
    ((continuous_datumMagneticMoment i).continuousOn) k T hT
  let a := freeWave (fun y => d.B₀ y i) (fun y => -curl d.E₀ y i)
  let b := datumWeightedSphere d.f₀ (fun p => dot p.1 (datumMagneticFluxKernel i (-p.1,p.2)))
  let c := datumWeightedSphere d.f₀ (fun p => p.1 (curlA i)*velocity p.2 (curlB i)-
    p.1 (curlB i)*velocity p.2 (curlA i))
  have has : ContDiff ℝ ∞ a := contDiff_freeWave ((hp i).comp hd.2.2.2.2.1.1)
    (((hp i).comp (contDiff_curl hd.2.2.2.1.1)).neg)
  refine ⟨A+B+D,by positivity,?_⟩
  intro t ht
  have heq : (fun x => magneticConeBoundary (datumBoundarySolution d) t x i 0)=
      (fun x => a (t,x)-b (t,x)+c (t,x)) := by
    funext x
    simp only [magneticConeBoundary,sub_zero]
    simp_rw [datum_initial_magnetic_flux_normalised d i ht.1]
    rw [←datumWeightedSphere_flux hd.1.continuous hd.2.1 (continuousOn_datumMagneticFluxKernel i)]
    simp only [datumBoundarySolution]
    rw [←datumWeightedSphere_magneticMoment hd]
  rw [heq]
  have ha := has.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hb := hFs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  have hc := hRs.comp ((contDiff_const (c:=t)).prodMk contDiff_id)
  refine ⟨(ha.sub hb).add hc,?_⟩
  intro x
  exact (norm_iteratedFDeriv_add_le (ha.sub hb) hc k x).trans (add_le_add
    ((norm_iteratedFDeriv_sub_le ha hb k x).trans (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x).2
      (hflux t ⟨ht.1.le,ht.2⟩ x))) (hmoment t ⟨ht.1.le,ht.2⟩ x))

lemma datum_boundary_global_jets_horizon_oai {d : Datum} (hd : Admissible d) (T : ℝ) (hT : 0≤T) (k : ℕ) :
    ∃ C : ℝ, 0≤C ∧
      (∀ x, ‖iteratedFDeriv ℝ k d.E₀ x‖≤C ∧ ‖iteratedFDeriv ℝ k d.B₀ x‖≤C) ∧
      ∀ t∈Ioc (0:ℝ) T,
        (ContDiff ℝ ∞ (electricBoundaryField (datumBoundarySolution d) t) ∧
          ContDiff ℝ ∞ (magneticBoundaryField (datumBoundarySolution d) t)) ∧
        ∀ x, ‖iteratedFDeriv ℝ k (electricBoundaryField (datumBoundarySolution d) t) x‖≤C ∧
          ‖iteratedFDeriv ℝ k (magneticBoundaryField (datumBoundarySolution d) t) x‖≤C := by
  choose CE hCE he using electricConeBoundary_datum_jets_horizon hd T hT k
  choose CB hCB hb using magneticConeBoundary_datum_jets_horizon hd T hT k
  obtain ⟨D,hD⟩ := hd.2.2.2.1.2 k
  obtain ⟨L,hL⟩ := hd.2.2.2.2.1.2 k
  let C := max D 0+max L 0+∑ i, (CE i+CB i)
  have hC : 0≤C := add_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))
    (Finset.sum_nonneg (fun i _ => add_nonneg (hCE i) (hCB i)))
  have hEC (i) : CE i≤C := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [C]; linarith [le_max_right D 0,le_max_right L 0,hCB i]
  have hBC (i) : CB i≤C := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [C]; linarith [le_max_right D 0,le_max_right L 0,hCE i]
  refine ⟨3*C,by positivity,?_,?_⟩
  · intro x
    have hS : 0≤∑ i, (CE i+CB i) := Finset.sum_nonneg (fun i _ => add_nonneg (hCE i) (hCB i))
    constructor
    · exact (hD x).trans (by dsimp [C]; linarith [le_max_left D 0,le_max_right L 0])
    · exact (hL x).trans (by dsimp [C]; linarith [le_max_left L 0,le_max_right D 0])
  · intro t ht
    have hes : ContDiff ℝ ∞ (electricBoundaryField (datumBoundarySolution d) t) :=
      contDiff_euclidean.mpr (fun i => (he i t ht).1)
    have hbs : ContDiff ℝ ∞ (magneticBoundaryField (datumBoundarySolution d) t) :=
      contDiff_euclidean.mpr (fun i => (hb i t ht).1)
    refine ⟨⟨hes,hbs⟩,fun x => ⟨?_,?_⟩⟩
    · exact norm_iteratedFDeriv_vec_le hes k hC (fun i y => ((he i t ht).2 y).trans (hEC i)) x
    · exact norm_iteratedFDeriv_vec_le hbs k hC (fun i y => ((hb i t ht).2 y).trans (hBC i)) x

end RVM
end

end OAI
end

theorem solution : type_of% @OAI.RVM.datum_boundary_global_jets_horizon_oai := @OAI.RVM.datum_boundary_global_jets_horizon_oai
