-- Prove2me | solution 1 for OAI.RVM.exists_picard_field_limit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:22:22.487985+00:00
-- url     : https://prove2.me/submissions/60f16d99-7a37-486b-8b73-49088ab92729

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_exists_picard_regular
import Theorems.Thm_OAI_RVM_exists_smoothLorentzFlow
import Theorems.Thm_OAI_RVM_mixed_electric_physical_representation
import Theorems.Thm_OAI_RVM_mixed_magnetic_physical_representation
import Theorems.Thm_OAI_RVM_transported_comparison
import Theorems.Thm_OAI_RVM_transported_spatial_lipschitz

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

lemma contDiff_lorentz (E B : Vec) {k : ℕ∞ω} :
    ContDiff ℝ k (fun v => E+cross (velocity v) B) := by
  exact contDiff_const.add (contDiff_cross.comp (contDiff_velocity.prodMk contDiff_const))

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

lemma contDiffOn_integral_uniform_support
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {n : ℕ∞} {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hU : IsOpen U) (hK : IsCompact K)
    (hF : ContDiffOn ℝ n F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContDiffOn ℝ n (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := contDiffOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) contDiffOn_const (g := fun x v => F (x,v))
    hU hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h

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

namespace RVM

lemma RegularParticle.slice {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ContDiff ℝ 1 (fun v : Vec => f (t,x,v)) ∧ HasCompactSupport (fun v : Vec => f (t,x,v)) := by
  constructor
  · apply contDiffOn_univ.mp
    exact hf.1.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun _ _ => ht)
  · obtain ⟨K,hK,hz⟩ := hf.2 t ht
    apply compactSupport_of_zero_off (hK.image continuous_snd)
    intro v hv
    by_contra hn
    exact hv ⟨(x,v),hz t ⟨ht,le_rfl⟩ (subset_tsupport _ hn),rfl⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_Sphere
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
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology NNReal

namespace RVM

lemma integral_radial_measure {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → W) :
    (∫ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2) = ∫ r in Ioi (0 : ℝ), r^2 • f r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi (fun r => Real.toNNReal (r^2) • f r)]
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change (r^2).toNNReal • f r = r^2 • f r
    rw [NNReal.smul_def,Real.coe_toNNReal _ (sq_nonneg r)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

lemma integrable_polar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Vec → W} (hf : Integrable f) :
    Integrable (fun p : Sphere × Ioi (0 : ℝ) => f (p.2.1 • p.1.1))
      (sphereMeasure.prod (Measure.volumeIoiPow 2)) := by
  have h := (volume : Measure Vec).measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
    (Homeomorph.measurableEmbedding _)
    (g := fun p => f (((homeomorphUnitSphereProd Vec).symm p).1))
  simp only [Function.comp_def,Homeomorph.symm_apply_apply] at h
  have hi : Integrable (fun z : ({0}ᶜ : Set Vec) => f z.1) (volume.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp hf.integrableOn
  have := h.mp hi
  simpa only [homeomorphUnitSphereProd_symm_apply_coe,finrank_euclideanSpace_fin,
    Nat.reduceSub] using this

lemma integral_polar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Vec → W} (hf : Integrable f) :
    (∫ y : Vec, f y) = ∫ n : Sphere, ∫ r in Ioi (0 : ℝ), r^2 • f (r • n.1) ∂volume ∂sphereMeasure := by
  calc
    _ = ∫ z : ({0}ᶜ : Set Vec), f z.1 ∂volume.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f,restrict_compl_singleton]
    _ = ∫ p : Sphere × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂sphereMeasure.prod (Measure.volumeIoiPow 2) := by
      have h := (volume : Measure Vec).measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd Vec).symm p).1))
      simpa only [Homeomorph.symm_apply_apply,homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin,Nat.reduceSub] using h
    _ = ∫ n : Sphere, ∫ r : Ioi (0 : ℝ), f (r.1 • n.1) ∂Measure.volumeIoiPow 2
        ∂sphereMeasure := integral_prod _ (integrable_polar hf)
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun n => integral_radial_measure (fun r => f (r • n.1)))
end RVM

open Set MeasureTheory Metric
open scoped Topology ContDiff

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


lemma integrableOn_norm_rpow_neg {α R : ℝ} (hα : α<3) :
    IntegrableOn (fun z : Vec => ‖z‖ ^ (-α)) (ball (0:Vec) R) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp) (C:=1) (α:=α) (by simpa using hα)
  · exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]; simp)
  · exact (continuous_norm.measurable.pow measurable_const).aestronglyMeasurable

lemma integral_ball_norm_rpow_neg {α R : ℝ} (hα : α<3) (hR : 0≤R) :
    (∫ z in ball (0:Vec) R, ‖z‖ ^ (-α)) =
      (4*Real.pi) * R^(3-α)/(3-α) := by
  rw [← integral_indicator measurableSet_ball,
    integral_polar ((integrableOn_norm_rpow_neg hα).integrable_indicator measurableSet_ball)]
  have he (n : Sphere) :
      (∫ r in Ioi (0:ℝ), r^2 • (ball (0:Vec) R).indicator
        (fun z => ‖z‖^(-α)) (r • n.1)) = R^(3-α)/(3-α) := by
    have heq : ∀ r ∈ Ioi (0:ℝ), r^2 • (ball (0:Vec) R).indicator
        (fun z => ‖z‖^(-α)) (r • n.1) =
        (Ioo (0:ℝ) R).indicator (fun r => r^(2-α)) r := by
      intro r hr
      change 0 < r at hr
      have hn : ‖r • n.1‖=r := by simp [norm_smul,abs_of_pos hr]
      by_cases h : r<R
      · rw [indicator_of_mem (show r • n.1 ∈ ball (0:Vec) R by simpa [mem_ball_zero_iff,hn] using h),
          indicator_of_mem (show r ∈ Ioo (0:ℝ) R from ⟨hr,h⟩),hn,smul_eq_mul]
        rw [← Real.rpow_two,← Real.rpow_add hr]
        congr 1
      · rw [indicator_of_notMem (show r • n.1 ∉ ball (0:Vec) R by simpa [mem_ball_zero_iff,hn] using h),
          indicator_of_notMem (show r ∉ Ioo (0:ℝ) R from fun hh => h hh.2),smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi heq,setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self,← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hR,integral_rpow (Or.inl (by linarith : -1<2-α))]
    have hne : 2-α+1≠0 := by linarith
    rw [Real.zero_rpow hne,sub_zero]
    rw [show 2-α+1=3-α by ring]
  simp_rw [he]
  rw [integral_const,smul_eq_mul,sphere_area]
  ring

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

lemma contDiffAt_coneRadius {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (coneRadius x) y :=
  (contDiffAt_const.sub contDiffAt_id).norm ℝ (sub_ne_zero.mpr hxy)

lemma contDiffAt_coneDirection {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (coneDirection x) y :=
  ((contDiffAt_coneRadius hxy).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))).smul
    (contDiffAt_const.sub contDiffAt_id)

lemma contDiffAt_retardedDensity {k : ℕ∞ω} {f : Particle} {x y v : Vec} {t : ℝ}
    (hf : ContDiffAt ℝ k f (t-coneRadius x y,y,v)) (hxy : x≠y) :
    ContDiffAt ℝ k (retardedDensity f t x) (y,v) := by
  have hr : ContDiffAt ℝ k (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hm : ContDiffAt ℝ k (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) :=
    ((contDiffAt_const (c:=t)).sub hr).prodMk contDiffAt_id
  exact hf.comp (f:=fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hm

lemma particle_contDiffAt_positive {k : ℕ∞ω} {f : Particle}
    (hf : ContDiffOn ℝ k f particleHalfSpace) {t : ℝ} (ht : 0<t) (x v : Vec) :
    ContDiffAt ℝ k f (t,x,v) := by
  have hn : particleHalfSpace ∈ 𝓝 (t,x,v) :=
    mem_of_superset ((isOpen_lt continuous_const
      (continuous_fst : Continuous (Prod.fst : ℝ × Phase → ℝ))).mem_nhds ht)
      (fun z hz => show 0≤z.1 from hz.le)
  exact (hf _ ht.le).contDiffAt hn

lemma isOpen_retardedSpaceDomain (t : ℝ) (x : Vec) : IsOpen (retardedSpaceDomain t x) := by
  have h₁ : IsOpen {y : Vec | y≠x} := isOpen_ne
  have h₂ : IsOpen {y : Vec | 0<t-coneRadius x y} :=
    isOpen_lt continuous_const (continuous_const.sub ((continuous_const.sub continuous_id).norm))
  convert h₁.inter h₂ using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp only [retardedSpaceDomain,mem_ofPred_eq,mem_inter_iff,ne_comm]

lemma retarded_local_data {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ∃ K : Set Vec, IsCompact K ∧
      ContDiffOn ℝ 1 (retardedDensity s.f t x) (retardedSpaceDomain t x ×ˢ univ) ∧
      ∀ y ∈ retardedSpaceDomain t x, ∀ v ∉ K, retardedDensity s.f t x (y,v)=0 := by
  obtain ⟨K,hK,hz⟩ := hc t ht
  refine ⟨Prod.snd '' K,hK.image continuous_snd,?_,?_⟩
  · intro z hz
    exact (contDiffAt_retardedDensity
      (particle_contDiffAt_positive hf hz.1.2 z.1 z.2) hz.1.1).contDiffWithinAt
  · intro y hy v hv
    by_contra hne
    have htime : t-coneRadius x y ∈ Icc 0 t :=
      ⟨hy.2.le,sub_le_self _ (norm_nonneg _)⟩
    exact hv ⟨(y,v),hz _ htime (subset_tsupport _ hne),rfl⟩

lemma continuous_physicalElectricKernel_velocity {r : ℝ} {n : Vec}
    (hr : r≠0) (hn : ‖n‖=1) (E B : Vec) :
    Continuous (fun v => physicalElectricKernel r n (velocity v)
      (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hb : Continuous (fun v => fderiv ℝ velocity v (E+cross (velocity v) B)) :=
    ((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).clm_apply
      (contDiff_lorentz (k:=1) E B).continuous
  have hd : Continuous (fun v => 1-dot n (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hd0 (v : Vec) : 1-dot n (velocity v)≠0 := (cone_denom_pos v n hn).ne'
  have hnum : Continuous (fun v => 1-dot (velocity v) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hu.prodMk hu))
  have hnb : Continuous (fun v => dot n (fderiv ℝ velocity v (E+cross (velocity v) B))) :=
    (contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hb)
  exact ((hnum.div (continuous_const.mul (hd.pow 3)) (fun v => mul_ne_zero (pow_ne_zero 2 hr)
      (pow_ne_zero 3 (hd0 v)))).smul (continuous_const.sub hu)).add
    (((continuous_const.mul (hd.pow 3)).inv₀ (fun v => mul_ne_zero hr (pow_ne_zero 3 (hd0 v)))).smul
      ((hnb.smul (continuous_const.sub hu)).sub (hd.smul hb)))

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

lemma uniform_integral_bound_compact {H W : Type*}
    [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {P : Set H} {K : Set Vec} {F : H × Vec → W}
    (hP : IsCompact P) (hK : IsCompact K)
    (hF : ContinuousOn F (P ×ˢ univ)) (hz : ∀ p ∈ P, ∀ v ∉ K, F (p,v)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ p ∈ P, ‖∫ v : Vec, F (p,v)‖≤C := by
  obtain ⟨C,hC⟩ := ((hP.prod hK).image_of_continuousOn (hF.mono (by intro z hz; exact ⟨hz.1,mem_univ _⟩))).isBounded.exists_norm_le
  refine ⟨max C 0*volume.real K,mul_nonneg (le_max_right _ _) (measureReal_nonneg),?_⟩
  intro p hp
  have hc : Continuous (fun v : Vec => F (p,v)) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hp,mem_univ _⟩)
  have hi : Integrable (fun v : Vec => F (p,v)) :=
    hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz p hp))
  have hfi : (∫ v : Vec, F (p,v))=∫ v in K, F (p,v) := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (hz p hp)
  rw [hfi]
  apply le_trans (norm_integral_le_integral_norm _)
  calc
    (∫ v in K, ‖F (p,v)‖) ≤ ∫ v in K, max C 0 := by
      apply integral_mono_ae hi.norm.integrableOn
        (integrableOn_const (hK.measure_lt_top.ne))
      filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
      exact le_trans (hC _ ⟨(p,v),⟨hp,hv⟩,rfl⟩) (le_max_left _ _)
    _ = max C 0*volume.real K := by simp [mul_comm]

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

namespace RVM

lemma normalisedElectricKernel_eq {r : ℝ} (hr : r≠0) (n u b : Vec) :
    normalisedElectricKernel r n u b=r^2 • physicalElectricKernel r n u b := by
  ext i
  simp only [normalisedElectricKernel,physicalElectricKernel,PiLp.add_apply,PiLp.smul_apply,
    PiLp.sub_apply,smul_eq_mul]
  field_simp

lemma continuousOn_normalisedElectricKernel {H : Type*} [TopologicalSpace H]
    {r : H → ℝ} {n u b : H → Vec} {S : Set H}
    (hr : ContinuousOn r S) (hn : ContinuousOn n S) (hu : ContinuousOn u S)
    (hb : ContinuousOn b S) (hd : ∀ z ∈ S, 1-dot (n z) (u z)≠0) :
    ContinuousOn (fun z => normalisedElectricKernel (r z) (n z) (u z) (b z)) S := by
  have hdot (f g : H → Vec) (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun z => dot (f z) (g z)) S :=
    (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn (hf.prodMk hg)
  have hD : ContinuousOn (fun z => 1-dot (n z) (u z)) S :=
    continuousOn_const.sub (hdot n u hn hu)
  have hp : ∀ z ∈ S, (1-dot (n z) (u z))^3≠0 := fun z hz => pow_ne_zero 3 (hd z hz)
  exact (((continuousOn_const.sub (hdot u u hu hu)).div (hD.pow 3) hp).smul (hn.sub hu)).add
    ((hr.div (hD.pow 3) hp).smul (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma field_contDiffAt_positive {k : ℕ∞ω} {F : Field}
    (hF : ContDiffOn ℝ k F fieldHalfSpace) {t : ℝ} (ht : 0<t) (x : Vec) :
    ContDiffAt ℝ k F (t,x) := by
  have hn : fieldHalfSpace ∈ 𝓝 (t,x) :=
    mem_of_superset ((isOpen_lt continuous_const
      (continuous_fst : Continuous (Prod.fst : ℝ × Vec → ℝ))).mem_nhds ht)
      (fun p hp => show 0≤p.1 from hp.le)
  exact (hF _ ht.le).contDiffAt hn

lemma contDiffAt_physicalElectricKernel {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ∞ω} {r : H → ℝ} {n u b : H → Vec} {z : H}
    (hr : ContDiffAt ℝ k r z) (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hb : ContDiffAt ℝ k b z) (hr0 : r z≠0) (hd0 : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun p => physicalElectricKernel (r p) (n p) (u p) (b p)) z := by
  have hdot (f g : H → Vec) (hf : ContDiffAt ℝ k f z) (hg : ContDiffAt ℝ k g z) :
      ContDiffAt ℝ k (fun p => dot (f p) (g p)) z :=
    contDiff_dot_pair.contDiffAt.comp z (hf.prodMk hg)
  have hD : ContDiffAt ℝ k (fun p => 1-dot (n p) (u p)) z :=
    contDiffAt_const.sub (hdot n u hn hu)
  exact (((contDiffAt_const.sub (hdot u u hu hu)).div ((hr.pow 2).mul (hD.pow 3))
      (mul_ne_zero (pow_ne_zero 2 hr0) (pow_ne_zero 3 hd0))).smul (hn.sub hu)).add
    (((hr.mul (hD.pow 3)).inv (mul_ne_zero hr0 (pow_ne_zero 3 hd0))).smul
      (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma contDiffAt_retardedElectricIntegrand {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} {x y v : Vec} (hxy : x≠y) (ht : 0<t-coneRadius x y) :
    ContDiffAt ℝ 1 (fun z : Phase =>
      (s.f (t-coneRadius x z.1,z.1,z.2)*(1-dot (coneDirection x z.1) (velocity z.2))) •
        physicalElectricKernel (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)
          (fderiv ℝ velocity z.2 (s.E (t-coneRadius x z.1,z.1)+
            cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1))))) (y,v) := by
  have hr : ContDiffAt ℝ 1 (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=1) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hn : ContDiffAt ℝ 1 (fun z : Phase => coneDirection x z.1) (y,v) :=
    (contDiffAt_coneDirection (k:=1) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) (y,v) :=
    contDiff_velocity.contDiffAt.comp (y,v) contDiffAt_snd
  have harg : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius x z.1,z.1)) (y,v) :=
    (contDiffAt_const.sub hr).prodMk contDiffAt_fst
  have he := (field_contDiffAt_positive hE ht y).comp (y,v) harg
  have hm := (field_contDiffAt_positive hB ht y).comp (y,v) harg
  have hcross : ContDiffAt ℝ 1 (fun z : Phase =>
      cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1))) (y,v) :=
    contDiff_cross.contDiffAt.comp (y,v) (hu.prodMk hm)
  have hdf : ContDiff ℝ 1 (fderiv ℝ velocity) :=
    (contDiff_velocity (k:=2)).fderiv_right (by norm_num)
  have hb : ContDiffAt ℝ 1 (fun z : Phase => fderiv ℝ velocity z.2
      (s.E (t-coneRadius x z.1,z.1)+cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1)))) (y,v) :=
    (hdf.contDiffAt.comp (y,v) contDiffAt_snd).clm_apply (he.add hcross)
  have hd0 : 1-dot (coneDirection x y) (velocity v)≠0 :=
    (cone_denom_pos v _ (coneDirection_norm hxy)).ne'
  have hk := contDiffAt_physicalElectricKernel hr hn hu hb
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) hd0
  exact ((contDiffAt_retardedDensity (particle_contDiffAt_positive hf ht y v) hxy).mul
    (contDiffAt_const.sub (contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk hu)))).smul hk

lemma contDiffOn_retardedElectricDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ContDiffOn ℝ 1 (retardedElectricDensity s t x) (retardedSpaceDomain t x) := by
  obtain ⟨K,hK,_,hz⟩ := retarded_local_data hf hc ht x
  unfold retardedElectricDensity
  apply contDiffOn_integral_uniform_support (n:=1)
    (F:=fun z : Phase => (s.f (t-coneRadius x z.1,z.1,z.2)*(1-dot (coneDirection x z.1) (velocity z.2))) •
      physicalElectricKernel (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)
        (fderiv ℝ velocity z.2 (s.E (t-coneRadius x z.1,z.1)+cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1)))))
    (isOpen_retardedSpaceDomain t x) hK
  · intro z hz
    exact (contDiffAt_retardedElectricIntegrand hf hE hB hz.1.1 hz.1.2).contDiffWithinAt
  · intro y hy v hv
    change (retardedDensity s.f t x (y,v)*_) • _=0
    rw [hz y hy v hv,zero_mul,zero_smul]

lemma integrableOn_ball_of_punctured_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {R C α : ℝ} (hα : α<3)
    (hF : ContinuousOn F (ball (0:Vec) R \ {0}))
    (hb : ∀ z : Vec, 0<‖z‖ → ‖z‖<R → ‖F z‖≤C*‖z‖^(-α)) :
    IntegrableOn F (ball (0:Vec) R) := by
  have hae : (ball (0:Vec) R \ ({0} : Set Vec) : Set Vec) =ᵐ[volume] (ball (0:Vec) R : Set Vec) := by
    filter_upwards [volume.ae_ne (0:Vec)] with z hz
    apply propext
    exact ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩
  have hmeas : AEStronglyMeasurable F (volume.restrict (ball (0:Vec) R)) := by
    rw [← Measure.restrict_congr_set hae]
    exact hF.aestronglyMeasurable (measurableSet_ball.diff (measurableSet_singleton _))
  apply ((integrableOn_norm_rpow_neg hα).const_mul C).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  exact hb z (norm_pos_iff.mpr hz0) (by simpa only [mem_ball_zero_iff] using hz)

end RVM

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_MagneticMomentDensity
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

lemma contDiffOn_retardedMagneticDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ContDiffOn ℝ 1 (retardedMagneticDensity s t x) (retardedSpaceDomain t x) := by
  intro y hy
  have hn : ContDiffAt ℝ 1 (coneDirection x) y := contDiffAt_coneDirection hy.1
  exact (contDiff_cross.contDiffAt.comp y (hn.prodMk
    ((contDiffOn_retardedElectricDensity hf hE hB hc ht x).contDiffAt
      ((isOpen_retardedSpaceDomain t x).mem_nhds hy)))).contDiffWithinAt

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RetardedWeightedIntegralBound
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

lemma retarded_weighted_integral_bound_le {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec)
    {A : (Vec × Vec) × Vec → W}
    (hA : ContinuousOn A ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, ‖z‖≤R → ∀ n : Vec, ‖n‖=1 →
      ‖∫ v : Vec, s.f (t-‖z‖,x+z,v) • A ((z,n),v)‖≤C := by
  have ht : 0≤t := le_trans hR hRt
  obtain ⟨K,hK,hz⟩ := hc t ht
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  have hP : IsCompact P := (isCompact_closedBall (0:Vec) R).prod (isCompact_sphere (0:Vec) 1)
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1,p.2)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk
      ((continuous_const.add continuous_fst.fst).prodMk continuous_snd)
  have htime (z : Vec) (hz' : z ∈ closedBall (0:Vec) R) : t-‖z‖ ∈ Icc 0 t := by
    have hn : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz'
    exact ⟨by linarith,sub_le_self _ (norm_nonneg _)⟩
  have hcf : ContinuousOn (fun p : (Vec × Vec) × Vec => s.f (t-‖p.1.1‖,x+p.1.1,p.2)) (P ×ˢ univ) :=
    hf.continuousOn.comp harg.continuousOn (fun p hp => (htime p.1.1 hp.1.1).1)
  have hzero : ∀ p ∈ P, ∀ v ∉ Prod.snd '' K, s.f (t-‖p.1‖,x+p.1,v) • A (p,v)=0 := by
    intro p hp v hv
    have hsf : s.f (t-‖p.1‖,x+p.1,v)=0 := by
      by_contra hne
      exact hv ⟨(x+p.1,v),hz _ (htime p.1 hp.1) (subset_tsupport _ hne),rfl⟩
    rw [hsf,zero_smul]
  obtain ⟨C,hC,hb⟩ := uniform_integral_bound_compact hP (hK.image continuous_snd) (hcf.smul hA) hzero
  refine ⟨C,hC,?_⟩
  intro z hz n hn
  exact hb (z,n) ⟨by simpa only [mem_closedBall_zero_iff] using hz,
    by simpa only [mem_sphere,dist_zero_right] using hn⟩

lemma retarded_electric_kernel_norm_bound_le {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, 0<‖z‖ → ‖z‖≤R →
      ‖∫ v : Vec, (s.f (t-coneRadius x (x+z),x+z,v)*
        (1-dot (coneDirection x (x+z)) (velocity v))) •
        physicalElectricKernel (coneRadius x (x+z)) (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x (x+z),x+z)+
            cross (velocity v) (s.B (t-coneRadius x (x+z),x+z))))‖≤C/‖z‖^2 := by
  let S : Set ((Vec × Vec) × Vec) := (closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ
  let u : (Vec × Vec) × Vec → Vec := fun p => velocity p.2
  let n : (Vec × Vec) × Vec → Vec := fun p => p.1.2
  let b : (Vec × Vec) × Vec → Vec := fun p => fderiv ℝ velocity p.2
    (s.E (t-‖p.1.1‖,x+p.1.1)+cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1)))
  have hu : Continuous u := (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hn : Continuous n := continuous_fst.snd
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk (continuous_const.add continuous_fst.fst)
  have hmap : MapsTo (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1)) S fieldHalfSpace := by
    intro p hp
    have hnz : ‖p.1.1‖≤R := by simpa only [mem_closedBall_zero_iff] using hp.1.1
    change 0≤t-‖p.1.1‖
    linarith
  have he := hE.comp harg.continuousOn hmap
  have hm := hB.comp harg.continuousOn hmap
  have hcross : ContinuousOn (fun p : (Vec × Vec) × Vec =>
      cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1))) S :=
    (contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.continuousOn.prodMk hm)
  have hb : ContinuousOn b S :=
    (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp continuous_snd).continuousOn.clm_apply (he.add hcross)
  have hD : Continuous (fun p : (Vec × Vec) × Vec => 1-dot (n p) (u p)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hn.prodMk hu))
  have hD0 (p : (Vec × Vec) × Vec) (hp : p ∈ S) : 1-dot (n p) (u p)≠0 := by
    apply (cone_denom_pos _ _ ?_).ne'
    simpa only [n,mem_sphere,dist_zero_right] using hp.1.2
  have hN := continuousOn_normalisedElectricKernel (S:=S)
    continuous_fst.fst.norm.continuousOn hn.continuousOn hu.continuousOn hb hD0
  obtain ⟨C,hC,hbound⟩ := retarded_weighted_integral_bound_le hf hc hR hRt x (hD.continuousOn.smul hN)
  refine ⟨C,hC,?_⟩
  intro z hz0 hzR
  have hxy : x≠x+z := by
    intro h
    apply (norm_pos_iff.mp hz0)
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have hh := hbound z hzR (coneDirection x (x+z)) (coneDirection_norm hxy)
  have heq : (∫ v : Vec, s.f (t-‖z‖,x+z,v) •
      ((1-dot (coneDirection x (x+z)) (velocity v)) •
        normalisedElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))))) =
      ‖z‖^2 • ∫ v : Vec, (s.f (t-‖z‖,x+z,v)*(1-dot (coneDirection x (x+z)) (velocity v))) •
        physicalElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [normalisedElectricKernel_eq hz0.ne']
    simp only [smul_smul]
    congr 1
    ring
  change ‖∫ v : Vec, s.f (t-‖z‖,x+z,v) •
      ((1-dot (coneDirection x (x+z)) (velocity v)) •
        normalisedElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))))‖≤C at hh
  rw [heq,norm_smul,Real.norm_of_nonneg (sq_nonneg _)] at hh
  simp only [coneRadius_add]
  apply (le_div_iff₀ (sq_pos_of_pos hz0)).mpr
  simpa only [mul_comm] using hh

lemma integrableOn_retardedElectricDensity_le {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec) :
    IntegrableOn (fun z => retardedElectricDensity s t x (x+z)) (ball (0:Vec) R) := by
  have ht : 0≤t := le_trans hR hRt
  have hcont := (contDiffOn_retardedElectricDensity hf hE hB hc ht x).continuousOn
  have hm : MapsTo (fun z : Vec => x+z) (ball (0:Vec) R \ {0}) (retardedSpaceDomain t x) := by
    intro z hz
    have hn : ‖z‖<R := by simpa only [mem_ball_zero_iff] using hz.1
    have hzero : z≠0 := by simpa only [mem_singleton_iff] using hz.2
    refine ⟨?_,?_⟩
    · intro h
      apply hzero
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    · rw [coneRadius_add]
      linarith
  have hcont' := hcont.comp (continuous_const.add continuous_id).continuousOn hm
  obtain ⟨C,_,hbound⟩ := retarded_electric_kernel_norm_bound_le hf hE.continuousOn hB.continuousOn hc hR hRt x
  apply integrableOn_ball_of_punctured_bound (C:=C) (α:=2) (by norm_num) hcont'
  intro z hz hzR
  have hh := hbound z hz hzR.le
  change ‖retardedElectricDensity s t x (x+z)‖≤C*‖z‖^(-(2:ℝ))
  rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two]
  exact hh

lemma integrableOn_retardedMagneticDensity_le {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec) :
    IntegrableOn (fun z => retardedMagneticDensity s t x (x+z)) (ball (0:Vec) R) := by
  have ht : 0≤t := le_trans hR hRt
  have hm : MapsTo (fun z : Vec => x+z) (ball (0:Vec) R \ {0}) (retardedSpaceDomain t x) := by
    intro z hz
    have hn : ‖z‖<R := by simpa only [mem_ball_zero_iff] using hz.1
    have hzero : z≠0 := by simpa only [mem_singleton_iff] using hz.2
    refine ⟨?_,?_⟩
    · intro h
      apply hzero
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    · rw [coneRadius_add]
      linarith
  have hcont := (contDiffOn_retardedMagneticDensity hf hE hB hc ht x).continuousOn.comp
    (continuous_const.add continuous_id).continuousOn hm
  obtain ⟨C,_,hbound⟩ := retarded_electric_kernel_norm_bound_le hf hE.continuousOn hB.continuousOn hc hR hRt x
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=C) (by norm_num) hcont
  intro z hz hzR
  have hxy : x≠x+z := (hm ⟨by simpa only [mem_ball_zero_iff] using hzR,by simpa only [mem_singleton_iff] using norm_pos_iff.mp hz⟩).1
  calc
    ‖retardedMagneticDensity s t x (x+z)‖ ≤ ‖coneDirection x (x+z)‖*‖retardedElectricDensity s t x (x+z)‖ := norm_cross_le _ _
    _ = ‖retardedElectricDensity s t x (x+z)‖ := by rw [coneDirection_norm hxy,one_mul]
    _ ≤ C/‖z‖^2 := hbound z hz hzR.le
    _ = C*‖z‖^(-(2:ℝ)) := by rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two]; rfl

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

lemma cross_sub_right (a b c : Vec) : cross a (b-c) = cross a b-cross a c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ElectricBoundaryField
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

lemma electricConeBoundary_initial_congr {s s' : Solution}
    (hf : ∀ z, s.f (0,z)=s'.f (0,z)) (hE : ∀ x, s.E (0,x)=s'.E (0,x))
    (hB : ∀ x, s.B (0,x)=s'.B (0,x)) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    electricConeBoundary s t x i 0=electricConeBoundary s' t x i 0 := by
  have hflux (n : Sphere) : retardedElectricFlux s t x i (x+t • n.1)=
      retardedElectricFlux s' t x i (x+t • n.1) := by
    have hr : coneRadius x (x+t • n.1)=t := by
      simpa only [sub_zero] using coneBoundary_radius ht
        (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
    unfold retardedElectricFlux retardedDensity
    dsimp only
    rw [hr,sub_self]
    simp_rw [hf]
  unfold electricConeBoundary
  simp only [sub_zero]
  simp_rw [hE,hB,hflux]
  simp only [rho,current,hf]

lemma magneticConeBoundary_initial_congr {s s' : Solution}
    (hf : ∀ z, s.f (0,z)=s'.f (0,z)) (hE : ∀ x, s.E (0,x)=s'.E (0,x))
    (hB : ∀ x, s.B (0,x)=s'.B (0,x)) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticConeBoundary s t x i 0=magneticConeBoundary s' t x i 0 := by
  have hflux (n : Sphere) : retardedMagneticFlux s t x i (x+t • n.1)=
      retardedMagneticFlux s' t x i (x+t • n.1) := by
    have hr : coneRadius x (x+t • n.1)=t := by
      simpa only [sub_zero] using coneBoundary_radius ht
        (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
    unfold retardedMagneticFlux retardedDensity
    dsimp only
    rw [hr,sub_self]
    simp_rw [hf]
  unfold magneticConeBoundary
  simp only [sub_zero]
  simp_rw [hE,hB,hflux]
  simp only [current,hf]

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

lemma uniform_datum_velocity_integral_bound {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : Continuous f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ y n : Vec, ‖n‖=1 → ‖∫ v : Vec, f (y,v) • H (n,v)‖≤C := by
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  let Kx : Set Vec := Prod.fst '' tsupport f
  have hKx : IsCompact Kx := hc.image continuous_fst
  have hF := datum_integrand_continuousOn hf hH
  have hP : IsCompact (Kx ×ˢ sphere (0:Vec) 1) := hKx.prod (isCompact_sphere (0:Vec) 1)
  obtain ⟨C,hC,hbound⟩ := uniform_integral_bound_compact hP hK
    (hF.mono (by intro p hp; exact ⟨⟨mem_univ _,hp.1.2⟩,hp.2⟩))
    (show ∀ p ∈ Kx ×ˢ sphere (0:Vec) 1, ∀ v ∉ K,
      f (p.1,v) • H (p.2,v)=0 from by intro p hp v hv; rw [hz p.1 v hv,zero_smul])
  refine ⟨C,hC,?_⟩
  intro y n hn
  by_cases hy : y∈Kx
  · exact hbound (y,n) ⟨hy,by simpa only [mem_sphere,dist_zero_right] using hn⟩
  · have he (v : Vec) : f (y,v)=0 := by
      by_contra h
      exact hy ⟨(y,v),subset_tsupport _ h,rfl⟩
    simpa only [he,zero_smul,integral_zero,norm_zero] using hC

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

lemma uniform_datumElectricFlux_bound {d : Datum} (hf : Continuous d.f₀)
    (hc : HasCompactSupport d.f₀) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (t : ℝ) (x y : Vec), x≠y →
      ‖retardedElectricFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y := by
  obtain ⟨C,hC,hbound⟩ := uniform_datum_velocity_integral_bound hf hc
    (continuousOn_datumElectricFluxKernel i)
  refine ⟨C,hC,?_⟩
  intro t x y hxy
  rw [datumElectricFlux_eq,norm_smul,coneRadius,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (x-y)))]
  simpa only [div_eq_mul_inv,mul_comm C,coneRadius] using
    mul_le_mul_of_nonneg_left (hbound y (coneDirection x y) (coneDirection_norm hxy))
      (inv_nonneg.mpr (norm_nonneg _))

lemma uniform_datumMagneticFlux_bound {d : Datum} (hf : Continuous d.f₀)
    (hc : HasCompactSupport d.f₀) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (t : ℝ) (x y : Vec), x≠y →
      ‖retardedMagneticFlux (datumBoundarySolution d) t x i y‖≤C/coneRadius x y := by
  obtain ⟨C,hC,hbound⟩ := uniform_datum_velocity_integral_bound hf hc
    (continuousOn_datumMagneticFluxKernel i)
  refine ⟨C,hC,?_⟩
  intro t x y hxy
  rw [datumMagneticFlux_eq,norm_smul,coneRadius,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg (x-y)))]
  simpa only [div_eq_mul_inv,mul_comm C,coneRadius] using
    mul_le_mul_of_nonneg_left (hbound y (coneDirection x y) (coneDirection_norm hxy))
      (inv_nonneg.mpr (norm_nonneg _))

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

lemma datum_moment_bounds {d : Datum} (hf : Continuous d.f₀) (hc : HasCompactSupport d.f₀) :
    ∃ C : ℝ, 0≤C ∧ ∀ x, |rho d.f₀ x|≤C ∧ ‖current d.f₀ x‖≤C := by
  have hn : ‖basis 0‖=1 := by simp [basis,PiLp.norm_single]
  obtain ⟨C,hC,hb⟩ := uniform_datum_velocity_integral_bound (H:=fun _ : Vec × Vec => (1:ℝ))
    hf hc continuousOn_const
  obtain ⟨D,hD,hd⟩ := uniform_datum_velocity_integral_bound (H:=fun p : Vec × Vec => velocity p.2)
    hf hc ((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn
  refine ⟨C+D,add_nonneg hC hD,?_⟩
  intro x
  constructor
  · have hh := hb x (basis 0) hn
    simpa only [smul_eq_mul,mul_one,Real.norm_eq_abs,rho] using hh.trans (le_add_of_nonneg_right hD)
  · exact (hd x (basis 0) hn).trans (le_add_of_nonneg_left hC)

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

lemma BoundedSmooth.coordinate_bounds {F : Vec → Vec} (hF : BoundedSmooth F) :
    ∃ C : ℝ, 0≤C ∧ ∀ x : Vec, ‖F x‖≤C ∧
      (∀ i v, |fderiv ℝ (fun y => F y i) x v|≤C*‖v‖) ∧ ∀ i, |curl F x i|≤C := by
  obtain ⟨A,hA⟩ := hF.2 0
  obtain ⟨D,hD⟩ := hF.2 1
  have hD' : ∀ x, ‖fderiv ℝ F x‖≤ max D 0 := by
    intro x
    have hh : ‖fderiv ℝ F x‖≤D := by simpa only [norm_iteratedFDeriv_one] using hD x
    exact hh.trans (le_max_left _ _)
  have hfd (x v : Vec) (i : Fin 3) : |fderiv ℝ (fun y => F y i) x v|≤ max D 0*‖v‖ := by
    rw [coordinate_fderiv_apply (hF.1.differentiable (by simp))]
    exact (norm_coordinate_le _ i).trans (((fderiv ℝ F x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg v)))
  refine ⟨max A 0+2*max D 0,by positivity,?_⟩
  intro x
  refine ⟨?_,?_,?_⟩
  · have hh : ‖F x‖≤A := by simpa only [norm_iteratedFDeriv_zero] using hA x
    linarith [le_max_left A 0,le_max_right D 0]
  · intro i v
    exact (hfd x v i).trans (mul_le_mul_of_nonneg_right (by
      linarith [le_max_right A 0,le_max_right D 0]) (norm_nonneg v))
  · intro i
    have he : curl F x i=spatialPartial (fun y => F y (curlB i)) x (curlA i)-
        spatialPartial (fun y => F y (curlA i)) x (curlB i) := by
      fin_cases i <;> simp [curl,curlA,curlB]
    rw [he]
    have ha := hfd x (basis (curlA i)) (curlB i)
    have hb := hfd x (basis (curlB i)) (curlA i)
    simp only [show ∀ j : Fin 3, ‖basis j‖=1 by intro j; simp [basis,PiLp.norm_single],mul_one] at ha hb
    exact (abs_sub _ _).trans ((add_le_add ha hb).trans (by linarith [le_max_right A 0]))

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

lemma BoundedSmooth.freeWave_coordinate_bound {E B : Vec → Vec}
    (hE : BoundedSmooth E) (hB : BoundedSmooth B) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ x : Vec,
      |freeWave (fun y => E y i) (fun y => curl B y i) (t,x)|≤C ∧
      |freeWave (fun y => B y i) (fun y => -curl E y i) (t,x)|≤C := by
  obtain ⟨A,hA,hAb⟩ := hE.coordinate_bounds
  obtain ⟨D,hD,hDb⟩ := hB.coordinate_bounds
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  refine ⟨3*(A+D),by positivity,?_⟩
  intro t ht x
  constructor
  · apply freeWave_bound_global (hproj.comp hE.1) (add_nonneg hA hD) _ _ _ ht
    · intro y
      exact (norm_coordinate_le _ i).trans ((hAb y).1.trans (le_add_of_nonneg_right hD))
    · intro y n hn
      have hh : |fderiv ℝ (fun u => E u i) y n|≤A := by simpa only [hn,mul_one] using (hAb y).2.1 i n
      exact hh.trans (le_add_of_nonneg_right hD)
    · intro y
      exact (hDb y).2.2 i |>.trans (le_add_of_nonneg_left hA)
  · apply freeWave_bound_global (hproj.comp hB.1) (add_nonneg hA hD) _ _ _ ht
    · intro y
      exact (norm_coordinate_le _ i).trans ((hDb y).1.trans (le_add_of_nonneg_left hA))
    · intro y n hn
      have hh : |fderiv ℝ (fun u => B u i) y n|≤D := by simpa only [hn,mul_one] using (hDb y).2.1 i n
      exact hh.trans (le_add_of_nonneg_left hA)
    · intro y
      rw [abs_neg]
      exact (hAb y).2.2 i |>.trans (le_add_of_nonneg_right hD)

lemma electricConeBoundary_datum_bound_global {d : Datum} (hd : Admissible d)
    (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
      |electricConeBoundary (datumBoundarySolution d) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := uniform_datumElectricFlux_bound hd.1.continuous hd.2.1 i
  obtain ⟨D,hD,hmom⟩ := datum_moment_bounds hd.1.continuous hd.2.1
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_bound hd.2.2.2.1 hd.2.2.2.2.1 i
  refine ⟨A+(C+2*D),by positivity,?_⟩
  intro t ht x
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_cone_flux i hflux ht.1 x n)
  have hrho : |∫ n : Sphere, t*n.1 i*rho d.f₀ (x+t • n.1) ∂sphereMeasure|≤
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
  have hj : |waveK (fun y => current d.f₀ y i) (t,x)|≤t*D :=
    waveK_bound_of_bounded (fun y => (norm_coordinate_le (current d.f₀ y) i).trans (hmom y).2) ht.1.le x
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedElectricFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t*n.1 i*rho d.f₀ (x+t • n.1) ∂sphereMeasure)|≤t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hrho hp
      _ = t*D := by field_simp
  have hf := (hfree t ⟨ht.1.le,ht.2⟩ x).1
  simp only [electricConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)) hj)).trans (by
      nlinarith [ht.2])

lemma magneticConeBoundary_datum_bound_global {d : Datum} (hd : Admissible d)
    (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
      |magneticConeBoundary (datumBoundarySolution d) t x i 0|≤C := by
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  obtain ⟨C,hC,hflux⟩ := uniform_datumMagneticFlux_bound hd.1.continuous hd.2.1 i
  obtain ⟨D,hD,hmom⟩ := datum_moment_bounds hd.1.continuous hd.2.1
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_bound hd.2.2.2.1 hd.2.2.2.2.1 i
  refine ⟨A+(C+2*D),by positivity,?_⟩
  intro t ht x
  have hflux' : |∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure|≤
      (C*t)*(4*Real.pi) := by
    exact abs_sphere_integral_le (fun n => norm_initial_magnetic_cone_flux i hflux ht.1 x n)
  have hem (n : Sphere) (j k : Fin 3) :
      |t*n.1 j*current d.f₀ (x+t • n.1) k|≤t*D := by
    have hn : |n.1 j|≤1 :=
      (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
    have hj : |current d.f₀ (x+t • n.1) k|≤D :=
      (norm_coordinate_le _ k).trans (hmom _).2
    rw [abs_mul,abs_mul,abs_of_pos ht.1]
    calc
      _ ≤ t*1*D := mul_le_mul (mul_le_mul_of_nonneg_left hn ht.1.le)
        hj (abs_nonneg _) (mul_nonneg ht.1.le zero_le_one)
      _ = _ := by ring
  have hj : |∫ n : Sphere,
      t*n.1 (curlA i)*current d.f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current d.f₀ (x+t • n.1) (curlA i) ∂sphereMeasure|≤
      (2*t*D)*(4*Real.pi) := by
    apply abs_sphere_integral_le
    intro n
    exact (abs_sub _ _).trans ((add_le_add (hem n _ _) (hem n _ _)).trans (by ring_nf; rfl))
  have hp : 0≤(4*Real.pi)⁻¹ := by positivity
  have hn1 : |(4*Real.pi)⁻¹*(∫ n : Sphere, t^2*dot n.1
      (retardedMagneticFlux (datumBoundarySolution d) t x i (x+t • n.1)) ∂sphereMeasure)|≤C*t := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((C*t)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hflux' hp
      _ = C*t := by field_simp
  have hn2 : |(4*Real.pi)⁻¹*(∫ n : Sphere,
      t*n.1 (curlA i)*current d.f₀ (x+t • n.1) (curlB i)-
      t*n.1 (curlB i)*current d.f₀ (x+t • n.1) (curlA i) ∂sphereMeasure)|≤2*t*D := by
    rw [abs_mul,abs_of_nonneg hp]
    calc
      _ ≤ (4*Real.pi)⁻¹*((2*t*D)*(4*Real.pi)) := mul_le_mul_of_nonneg_left hj hp
      _ = 2*t*D := by field_simp
  have hf := (hfree t ⟨ht.1.le,ht.2⟩ x).2
  simp only [magneticConeBoundary,datumBoundarySolution,sub_zero]
  exact ((abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hf hn1)) hn2)).trans (by
      nlinarith [ht.2])

lemma datum_boundary_global_bound {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ (∀ x, ‖d.E₀ x‖≤C ∧ ‖d.B₀ x‖≤C) ∧
      ∀ t∈Ioc (0:ℝ) 1, ∀ x : Vec,
        ‖electricBoundaryField (datumBoundarySolution d) t x‖≤C ∧
        ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤C := by
  choose CE hCE hEe using fun i : Fin 3 => electricConeBoundary_datum_bound_global hd i
  choose CB hCB hBb using fun i : Fin 3 => magneticConeBoundary_datum_bound_global hd i
  obtain ⟨E₀,hE₀⟩ := hd.2.2.2.1.2 0
  obtain ⟨B₀,hB₀⟩ := hd.2.2.2.2.1.2 0
  let S := (∑ i : Fin 3, CE i)+(∑ i : Fin 3, CB i)
  have hS : 0≤S := add_nonneg (Finset.sum_nonneg (fun i _ => hCE i))
    (Finset.sum_nonneg (fun i _ => hCB i))
  let C := 3*S+max E₀ 0+max B₀ 0
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_,?_⟩
  · intro x
    constructor
    · have hh : ‖d.E₀ x‖≤E₀ := by simpa only [norm_iteratedFDeriv_zero] using hE₀ x
      dsimp [C]
      linarith [le_max_left E₀ 0,le_max_right B₀ 0]
    · have hh : ‖d.B₀ x‖≤B₀ := by simpa only [norm_iteratedFDeriv_zero] using hB₀ x
      dsimp [C]
      linarith [le_max_left B₀ 0,le_max_right E₀ 0]
  · intro t ht x
    have hEe' : ‖electricBoundaryField (datumBoundarySolution d) t x‖≤3*S := by
      apply norm_le_three_of_coordinate_bound hS
      intro i
      exact (hEe i t ht x).trans (by
        have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hCE j) (Finset.mem_univ i)
        have hh' : 0≤∑ j : Fin 3, CB j := Finset.sum_nonneg (fun j _ => hCB j)
        dsimp [S]
        linarith)
    have hBb' : ‖magneticBoundaryField (datumBoundarySolution d) t x‖≤3*S := by
      apply norm_le_three_of_coordinate_bound hS
      intro i
      exact (hBb i t ht x).trans (by
        have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => hCB j) (Finset.mem_univ i)
        have hh' : 0≤∑ j : Fin 3, CE j := Finset.sum_nonneg (fun j _ => hCE j)
        dsimp [S]
        linarith)
    have hh : 3*S≤C := by dsimp [C]; linarith [le_max_right E₀ 0,le_max_right B₀ 0]
    exact ⟨hEe'.trans hh,hBb'.trans hh⟩

lemma smooth_compact_lipschitz {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y, ‖f y-f x‖≤C*‖y-x‖ := by
  obtain ⟨D,hD⟩ := (hf.continuous_fderiv (by norm_num)).bounded_above_of_compact_support (hc.fderiv ℝ)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x y
  exact (convex_univ : Convex ℝ (univ : Set U)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable (by norm_num) z)
    (fun z _ => (hD z).trans (le_max_left _ _)) (mem_univ x) (mem_univ y)

lemma BoundedSmooth.iterated_lipschitz {F : Vec → Vec} (hF : BoundedSmooth F) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y,
      ‖iteratedFDeriv ℝ n F y-iteratedFDeriv ℝ n F x‖≤C*‖y-x‖ := by
  obtain ⟨D,hD⟩ := hF.2 (n+1)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x y
  exact (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ContDiff.differentiable_iteratedFDeriv (n:=∞) (m:=n) (by exact_mod_cast ENat.natCast_lt_top n) hF.1 z)
    (fun z _ => by
      rw [norm_fderiv_iteratedFDeriv]
      exact (hD z).trans (le_max_left _ _))
    (mem_univ x) (mem_univ y)

lemma BoundedSmooth.spatial_lipschitz {F : Vec → Vec} (hF : BoundedSmooth F) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y : Vec, ‖F y-F x‖≤C*‖y-x‖ ∧
      (∀ i v, |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤C*‖y-x‖*‖v‖) ∧
      ∀ i, |curl F y i-curl F x i|≤C*‖y-x‖ := by
  obtain ⟨D,hD⟩ := hF.2 1
  let A := max D 0
  have hA : 0≤A := le_max_right _ _
  have hval (x y : Vec) : ‖F y-F x‖≤A*‖y-x‖ := by
    apply (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hF.1.differentiable (by simp) z) _ (mem_univ x) (mem_univ y)
    intro z _
    have hh : ‖fderiv ℝ F z‖≤D := by simpa only [norm_iteratedFDeriv_one] using hD z
    exact hh.trans (le_max_left _ _)
  obtain ⟨B,hB,hb⟩ := hF.iterated_lipschitz 1
  have hder (x y v : Vec) : ‖fderiv ℝ F y v-fderiv ℝ F x v‖≤B*‖y-x‖*‖v‖ := by
    have hh := (iteratedFDeriv ℝ 1 F y-iteratedFDeriv ℝ 1 F x).le_opNorm (fun _ => v)
    simp only [sub_apply,iteratedFDeriv_one_apply,Fin.prod_univ_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hb x y) (norm_nonneg v))
  have hder' (x y v : Vec) (i : Fin 3) :
      |fderiv ℝ (fun z => F z i) y v-fderiv ℝ (fun z => F z i) x v|≤B*‖y-x‖*‖v‖ := by
    rw [coordinate_fderiv_apply (hF.1.differentiable (by simp)),coordinate_fderiv_apply (hF.1.differentiable (by simp))]
    exact (norm_coordinate_le (fderiv ℝ F y v-fderiv ℝ F x v) i).trans (hder x y v)
  refine ⟨A+2*B,by positivity,?_⟩
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

lemma uniform_datum_velocity_integral_lipschitz {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y n : Vec, ‖n‖=1 →
      ‖(∫ v : Vec, f (y,v) • H (n,v))-(∫ v : Vec, f (x,v) • H (n,v))‖≤C*‖y-x‖ := by
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  obtain ⟨A,hA,hfLip⟩ := smooth_compact_lipschitz hf hc
  obtain ⟨B,hB⟩ := ((isCompact_sphere (0:Vec) 1).prod hK).exists_bound_of_continuousOn
    (hH.mono (by intro p hp; exact ⟨hp.1,mem_univ _⟩))
  let D := max B 0
  have hD : 0≤D := le_max_right _ _
  refine ⟨A*D*(volume K).toReal,by positivity,?_⟩
  intro x y n hn
  have hn' : n∈sphere (0:Vec) 1 := mem_sphere_zero_iff_norm.mpr hn
  have hint (z : Vec) : Integrable (fun v => f (z,v) • H (n,v)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hf.continuous.comp (continuous_const.prodMk continuous_id)).smul
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
    rw [← sub_smul,norm_smul]
    apply mul_le_mul _ ((hB (n,v) ⟨hn',hv⟩).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
    simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,max_eq_left (norm_nonneg _)] using
      hfLip (x,v) (y,v)
  exact (norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hb).trans_eq (by simp only [Measure.real]; ring)

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

lemma datum_moment_lipschitz {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y, |rho d.f₀ y-rho d.f₀ x|≤C*‖y-x‖ ∧
      ‖current d.f₀ y-current d.f₀ x‖≤C*‖y-x‖ := by
  obtain ⟨A,hA,ha⟩ := uniform_datum_velocity_integral_lipschitz
    (hd.1.of_le (by simp)) hd.2.1 (H:=fun _ => (1:ℝ)) continuousOn_const
  obtain ⟨B,hB,hb⟩ := uniform_datum_velocity_integral_lipschitz
    (hd.1.of_le (by simp)) hd.2.1
    (((contDiff_velocity (k:=1)).continuous.comp continuous_snd).continuousOn)
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro x y
  constructor
  · have hh := ha x y (basis 0) (by simp [basis,PiLp.norm_single])
    simp only [smul_eq_mul,mul_one,Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (norm_nonneg _))
  · exact (hb x y (basis 0) (by simp [basis,PiLp.norm_single])).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _))

lemma BoundedSmooth.freeWave_coordinate_lipschitz {E B : Vec → Vec}
    (hE : BoundedSmooth E) (hB : BoundedSmooth B) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ x y : Vec,
      |freeWave (fun z => E z i) (fun z => curl B z i) (t,y)-
        freeWave (fun z => E z i) (fun z => curl B z i) (t,x)|≤C*‖y-x‖ ∧
      |freeWave (fun z => B z i) (fun z => -curl E z i) (t,y)-
        freeWave (fun z => B z i) (fun z => -curl E z i) (t,x)|≤C*‖y-x‖ := by
  obtain ⟨A,hA,hAb⟩ := hE.spatial_lipschitz
  obtain ⟨D,hD,hDb⟩ := hB.spatial_lipschitz
  have hproj : ContDiff ℝ ∞ (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  refine ⟨3*(A+D),by positivity,?_⟩
  intro t ht x y
  constructor
  · apply freeWave_lipschitz (hproj.comp hE.1)
      (hproj.continuous.comp (contDiff_curl hB.1).continuous) (add_nonneg hA hD) _ _ _ ht
    · intro z z'
      exact (norm_coordinate_le (E z'-E z) i).trans ((hAb z z').1.trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _)))
    · intro z z' n hn
      have hh : |fderiv ℝ (fun u => E u i) z' n-fderiv ℝ (fun u => E u i) z n|≤A*‖z'-z‖ := by
        simpa only [hn,mul_one] using (hAb z z').2.1 i n
      exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (norm_nonneg _))
    · intro z z'
      exact ((hDb z z').2.2 i).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) (norm_nonneg _))
  · apply freeWave_lipschitz (hproj.comp hB.1)
      ((hproj.continuous.comp (contDiff_curl hE.1).continuous).neg) (add_nonneg hA hD) _ _ _ ht
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

lemma datum_sphere_flux_lipschitz {f : Phase → ℝ} {H : Vec × Vec → Vec}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Icc (0:ℝ) 1, ∀ x y : Vec,
      |(4*Real.pi)⁻¹*(∫ n : Sphere, t*dot n.1 (∫ v, f (y+t • n.1,v) • H (-n.1,v)) ∂sphereMeasure)-
        (4*Real.pi)⁻¹*(∫ n : Sphere, t*dot n.1 (∫ v, f (x+t • n.1,v) • H (-n.1,v)) ∂sphereMeasure)|≤C*‖y-x‖ := by
  obtain ⟨C,hC,hb⟩ := uniform_datum_velocity_integral_lipschitz hf hc hH
  refine ⟨C,hC,?_⟩
  intro t ht x y
  have hn (n : Sphere) : ‖n.1‖=1 := mem_sphere_zero_iff_norm.mp n.2
  have hc' (z : Vec) : Continuous (fun n : Sphere =>
      t*dot n.1 (∫ v, f (z+t • n.1,v) • H (-n.1,v))) := by
    have hI : Continuous (fun n : Sphere => ∫ v, f (z+t • n.1,v) • H (-n.1,v)) := by
      apply (continuousOn_datum_velocity_integral hf.continuous hc hH).comp_continuous
        ((continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)).prodMk continuous_subtype_val.neg)
      intro n
      exact ⟨mem_univ _,by simpa only [mem_sphere_zero_iff_norm,Pi.neg_apply,norm_neg] using hn n⟩
    exact continuous_const.mul ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_subtype_val.prodMk hI))
  have hh := abs_sphere_integral_sub_le (hc' y) (hc' x) (C:=C*‖y-x‖) (by
    intro n
    rw [← mul_sub,← dot_sub_right,abs_mul,abs_of_nonneg ht.1]
    have hbd : ‖(∫ v, f (y+t • n.1,v) • H (-n.1,v))-
        (∫ v, f (x+t • n.1,v) • H (-n.1,v))‖≤C*‖y-x‖ := by
      simpa only [add_sub_add_right_eq_sub] using hb (x+t • n.1) (y+t • n.1) (-n.1) (by simpa only [norm_neg] using hn n)
    exact (mul_le_mul_of_nonneg_left ((abs_dot_le _ _).trans
      (by simpa only [hn n,one_mul] using hbd)) ht.1).trans
        (mul_le_of_le_one_left (by positivity) ht.2))
  rw [← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(4*Real.pi)⁻¹)]
  exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by field_simp)

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

lemma electricConeBoundary_datum_lipschitz {d : Datum} (hd : Admissible d) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
      |electricConeBoundary (datumBoundarySolution d) t y i 0-
        electricConeBoundary (datumBoundarySolution d) t x i 0|≤C*‖y-x‖ := by
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_lipschitz hd.2.2.2.1 hd.2.2.2.2.1 i
  obtain ⟨B,hB,hflux⟩ := datum_sphere_flux_lipschitz (hd.1.of_le (by simp)) hd.2.1
    (continuousOn_datumElectricFluxKernel i)
  obtain ⟨D,hD,hmom⟩ := datum_moment_lipschitz hd
  have hm : Continuous (rho d.f₀) ∧ Continuous (current d.f₀) := by
    constructor
    · exact (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
        simpa only [dist_eq_norm,Real.norm_eq_abs] using (hmom y x).1)).continuous
    · exact (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
        simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj : Continuous (fun v : Vec => v i) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro t ht x y
  have hrho := weighted_sphere_mean_lipschitz hm.1 hD (fun x y => (hmom x y).1)
    (hproj.comp continuous_subtype_val) (fun n => (norm_coordinate_le n.1 i).trans_eq (mem_sphere_zero_iff_norm.mp n.2))
    ⟨ht.1.le,ht.2⟩ x y
  have hj := waveK_lipschitz (hproj.comp hm.2)
    (fun x y => (norm_coordinate_le (current d.f₀ y-current d.f₀ x) i).trans (hmom x y).2) ht.1.le x y
  have he : t*D*‖y-x‖≤D*‖y-x‖ := by
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hD ht.2) (norm_nonneg _)
  simp only [electricConeBoundary,sub_zero]
  simp_rw [datum_initial_electric_flux_normalised d i ht.1]
  simp only [datumBoundarySolution]
  have halg (a b c e a' b' c' e' : ℝ) : (a-b-c-e)-(a'-b'-c'-e')=(a-a')-(b-b')-(c-c')-(e-e') := by ring
  rw [halg]
  exact ((abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add ((abs_sub _ _).trans (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x y).1
      (hflux t ⟨ht.1.le,ht.2⟩ x y))) hrho)) (hj.trans he))).trans_eq (by ring)

lemma magneticConeBoundary_datum_lipschitz {d : Datum} (hd : Admissible d) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
      |magneticConeBoundary (datumBoundarySolution d) t y i 0-
        magneticConeBoundary (datumBoundarySolution d) t x i 0|≤C*‖y-x‖ := by
  obtain ⟨A,hA,hfree⟩ := BoundedSmooth.freeWave_coordinate_lipschitz hd.2.2.2.1 hd.2.2.2.2.1 i
  obtain ⟨B,hB,hflux⟩ := datum_sphere_flux_lipschitz (hd.1.of_le (by simp)) hd.2.1
    (continuousOn_datumMagneticFluxKernel i)
  obtain ⟨D,hD,hmom⟩ := datum_moment_lipschitz hd
  have hjc : Continuous (current d.f₀) := (LipschitzWith.of_dist_le' (K:=D) (fun x y => by
    simpa only [dist_eq_norm] using (hmom y x).2)).continuous
  have hproj (j : Fin 3) : Continuous (fun v : Vec => v j) := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous
  refine ⟨A+B+2*D,by positivity,?_⟩
  intro t ht x y
  let F : Vec → Sphere → ℝ := fun z n => t*n.1 (curlA i)*current d.f₀ (z+t • n.1) (curlB i)-
    t*n.1 (curlB i)*current d.f₀ (z+t • n.1) (curlA i)
  have hfc (z : Vec) : Continuous (F z) := by
    have hg (j k : Fin 3) : Continuous (fun n : Sphere => t*n.1 j*current d.f₀ (z+t • n.1) k) :=
      (continuous_const.mul ((hproj j).comp continuous_subtype_val)).mul
        (((hproj k).comp hjc).comp (continuous_const.add
          ((continuous_const : Continuous (fun _ : Sphere => t)).smul continuous_subtype_val)))
    exact (hg _ _).sub (hg _ _)
  have hh := abs_sphere_integral_sub_le (hfc y) (hfc x) (C:=2*D*‖y-x‖) (by
    intro n
    have hterm (j k : Fin 3) : |t*n.1 j*current d.f₀ (y+t • n.1) k-
        t*n.1 j*current d.f₀ (x+t • n.1) k|≤D*‖y-x‖ := by
      rw [← mul_sub,abs_mul,abs_mul,abs_of_pos ht.1]
      have hn : |n.1 j|≤1 := (norm_coordinate_le n.1 j).trans_eq (mem_sphere_zero_iff_norm.mp n.2)
      have hj : |current d.f₀ (y+t • n.1) k-current d.f₀ (x+t • n.1) k|≤D*‖y-x‖ := by
        simpa only [PiLp.sub_apply,add_sub_add_right_eq_sub] using
          (norm_coordinate_le (current d.f₀ (y+t • n.1)-current d.f₀ (x+t • n.1)) k).trans
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
  simp_rw [datum_initial_magnetic_flux_normalised d i ht.1]
  simp only [datumBoundarySolution]
  have halg (a b c a' b' c' : ℝ) : (a-b+c)-(a'-b'+c')=(a-a')-(b-b')+(c-c') := by ring
  rw [halg]
  exact ((abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
    (add_le_add (hfree t ⟨ht.1.le,ht.2⟩ x y).2 (hflux t ⟨ht.1.le,ht.2⟩ x y))) hj)).trans_eq (by ring)

lemma datum_boundary_global_lipschitz {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ (∀ x y, ‖d.E₀ y-d.E₀ x‖≤C*‖y-x‖ ∧ ‖d.B₀ y-d.B₀ x‖≤C*‖y-x‖) ∧
      ∀ t∈Ioc (0:ℝ) 1, ∀ x y : Vec,
        ‖electricBoundaryField (datumBoundarySolution d) t y-electricBoundaryField (datumBoundarySolution d) t x‖≤C*‖y-x‖ ∧
        ‖magneticBoundaryField (datumBoundarySolution d) t y-magneticBoundaryField (datumBoundarySolution d) t x‖≤C*‖y-x‖ := by
  obtain ⟨E,hE,hEb⟩ := hd.2.2.2.1.spatial_lipschitz
  obtain ⟨B,hB,hBb⟩ := hd.2.2.2.2.1.spatial_lipschitz
  choose CE hCE he using electricConeBoundary_datum_lipschitz hd
  choose CB hCB hb using magneticConeBoundary_datum_lipschitz hd
  let S := E+B+∑ i : Fin 3, (CE i+CB i)
  have hS : 0≤S := by dsimp [S]; exact add_nonneg (add_nonneg hE hB) (Finset.sum_nonneg fun i _ => add_nonneg (hCE i) (hCB i))
  have hEC (i : Fin 3) : CE i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCB i]
  have hBC (i : Fin 3) : CB i≤S := by
    have hh := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => add_nonneg (hCE j) (hCB j)) (Finset.mem_univ i)
    dsimp [S]; linarith [hCE i]
  refine ⟨3*S,by positivity,?_,?_⟩
  · intro x y
    have hh : 0≤∑ i : Fin 3, (CE i+CB i) := Finset.sum_nonneg fun i _ => add_nonneg (hCE i) (hCB i)
    constructor
    · exact ((hEb x y).1).trans (mul_le_mul_of_nonneg_right (by dsimp [S]; linarith) (norm_nonneg _))
    · exact ((hBb x y).1).trans (mul_le_mul_of_nonneg_right (by dsimp [S]; linarith) (norm_nonneg _))
  · intro t ht x y
    constructor
    · have hh := norm_le_three_of_coordinate_bound (mul_nonneg hS (norm_nonneg (y-x)))
        (v:=electricBoundaryField (datumBoundarySolution d) t y-electricBoundaryField (datumBoundarySolution d) t x)
        (fun i => (he i t ht x y).trans (mul_le_mul_of_nonneg_right (hEC i) (norm_nonneg _)))
      exact hh.trans_eq (by ring)
    · have hh := norm_le_three_of_coordinate_bound (mul_nonneg hS (norm_nonneg (y-x)))
        (v:=magneticBoundaryField (datumBoundarySolution d) t y-magneticBoundaryField (datumBoundarySolution d) t x)
        (fun i => (hb i t ht x y).trans (mul_le_mul_of_nonneg_right (hBC i) (norm_nonneg _)))
      exact hh.trans_eq (by ring)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardBounds
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

lemma uniform_normalised_physical_kernel (P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ E B : Vec, ‖E‖≤L → ‖B‖≤L →
      ‖(1-dot n (velocity v)) • normalisedElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C := by
  let K : Set (ℝ × Vec × Vec × Vec × Vec) :=
    Icc 0 1 ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P ×ˢ
      closedBall (0:Vec) L ×ˢ closedBall (0:Vec) L
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))))
  let r : (ℝ × Vec × Vec × Vec × Vec) → ℝ := Prod.fst
  let n : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.1
  let v : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.1
  let E : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.2.1
  let B : (ℝ × Vec × Vec × Vec × Vec) → Vec := fun p => p.2.2.2.2
  have hr : Continuous r := continuous_fst
  have hn : Continuous n := continuous_snd.fst
  have hv : Continuous v := continuous_snd.snd.fst
  have hE : Continuous E := continuous_snd.snd.snd.fst
  have hB : Continuous B := continuous_snd.snd.snd.snd
  have hu := (contDiff_velocity (k:=1)).continuous.comp hv
  have ha : Continuous (fun p => fderiv ℝ velocity (v p) (E p+cross (velocity (v p)) (B p))) :=
    (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp hv).clm_apply
      (hE.add ((contDiff_cross (k:=1)).continuous.comp (hu.prodMk hB)))
  have hd : Continuous (fun p => 1-dot (n p) (velocity (v p))) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hn.prodMk hu))
  have hk := hd.continuousOn.smul (continuousOn_normalisedElectricKernel
    hr.continuousOn hn.continuousOn hu.continuousOn ha.continuousOn (S:=K) (by
      intro p hp
      exact (cone_denom_pos (v p) (n p) (by simpa only [n,mem_sphere,dist_zero_right] using hp.2.1)).ne'))
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hk).isBounded.exists_norm_le
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro r hr n hn v hv E B hE hB
  apply le_trans (hC _ ⟨(r,n,v,E,B),?_,rfl⟩) (le_max_right _ _)
  exact ⟨hr,by simpa only [mem_sphere,dist_zero_right] using hn,
    by simpa only [mem_closedBall_zero_iff] using hv,
    by simpa only [mem_closedBall_zero_iff] using hE,
    by simpa only [mem_closedBall_zero_iff] using hB⟩

lemma uniform_physical_kernel (P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ E B : Vec, ‖E‖≤L → ‖B‖≤L →
      ‖(1-dot n (velocity v)) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C/r^2 := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_physical_kernel P L
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv E B hE hB
  have hh := hb r ⟨hr.1.le,hr.2⟩ n hn v hv E B hE hB
  rw [normalisedElectricKernel_eq hr.1.ne',smul_comm (1-dot n (velocity v)),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (by simpa only [mul_comm] using hh)

lemma physical_integral_bound {A P C r : ℝ} {n E B : Vec} {f : Vec → ℝ}
    (hA : 0≤A)
    (hbound : ∀ v : Vec, ‖v‖≤P →
      ‖(1-dot n (velocity v)) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤C/r^2)
    (hf : ∀ v, |f v|≤A) (hs : ∀ v, P<‖v‖ → f v=0) :
    ‖∫ v : Vec, (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))‖≤
      (A*C*volume.real (closedBall (0:Vec) P))/r^2 := by
  let g : Vec → Vec := fun v => (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
    (fderiv ℝ velocity v (E+cross (velocity v) B))
  have he : (∫ v in closedBall (0:Vec) P, g v)=∫ v, g v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hv' : P<‖v‖ := by simpa only [mem_closedBall_zero_iff,not_le] using hv
    simp [g,hs v hv']
  change ‖∫ v, g v‖≤_
  rw [← he]
  have hb : ∀ v∈closedBall (0:Vec) P, ‖g v‖≤A*(C/r^2) := by
    intro v hv
    have hv' : ‖v‖≤P := mem_closedBall_zero_iff.mp hv
    dsimp [g]
    rw [mul_smul,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul (hf v) (hbound v hv') (norm_nonneg _) hA
  have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume) (isCompact_closedBall (0:Vec) P).measure_lt_top hb
  exact hh.trans_eq (by ring)

lemma uniform_retarded_density_bound (A P L : ℝ) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (T : ℝ), T≤1 →
      (∀ t∈Icc 0 T, ∀ z, |s.f (t,z)|≤A) →
      (∀ t∈Icc 0 T, ∀ (x v : Vec), s.f (t,x,v)≠0 →
        ‖v‖≤P ∧ ‖s.E (t,x)‖≤L ∧ ‖s.B (t,x)‖≤L) →
      ∀ t∈Icc 0 T, ∀ (x z : Vec), 0<‖z‖ → ‖z‖≤t →
        ‖retardedElectricDensity s t x (x+z)‖≤C/‖z‖^2 ∧
        ‖retardedMagneticDensity s t x (x+z)‖≤C/‖z‖^2 := by
  obtain ⟨K,hK,hk⟩ := uniform_physical_kernel P L
  refine ⟨A*K*volume.real (closedBall (0:Vec) P),by positivity,?_⟩
  intro s T hT hf hs t ht x z hz hzt
  have htime : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  have hxy : x≠x+z := by
    intro he
    have hh : z=0 := add_left_cancel (show x+z=x+0 by simpa using he.symm)
    exact (norm_pos_iff.mp hz) hh
  have he : ‖retardedElectricDensity s t x (x+z)‖≤
      (A*K*volume.real (closedBall (0:Vec) P))/‖z‖^2 := by
    by_cases hn : ∃ v : Vec, s.f (t-‖z‖,x+z,v)≠0
    · obtain ⟨v,hv⟩ := hn
      have hEB := hs _ htime _ v hv
      unfold retardedElectricDensity
      rw [coneRadius_add]
      apply physical_integral_bound hA
      · intro u hu
        exact hk ‖z‖ ⟨hz,hzt.trans (ht.2.trans hT)⟩ _ (coneDirection_norm hxy)
          u hu _ _ hEB.2.1 hEB.2.2
      · intro u
        exact hf _ htime (x+z,u)
      · intro u hu
        by_contra hnu
        exact (not_lt_of_ge (hs _ htime _ u hnu).1) hu
    · have hzero : ∀ v : Vec, s.f (t-‖z‖,x+z,v)=0 := by simpa using hn
      simp only [retardedElectricDensity,coneRadius_add,hzero,zero_mul,zero_smul,integral_zero,norm_zero]
      positivity
  refine ⟨he,?_⟩
  exact (norm_cross_le _ _).trans (by simpa only [coneDirection_norm hxy,one_mul] using he)

lemma kernel_tip_le_on {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {C R : ℝ} (hR : 0≤R) (hF : IntegrableOn F (ball (0:Vec) R))
    (hb : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C/‖z‖^2) :
    ‖∫ z in ball (0:Vec) R, F z‖≤4*Real.pi*C*R := by
  have hbound : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C*‖z‖^(-(2:ℝ)) := by
    simpa only [Real.rpow_neg (norm_nonneg _),Real.rpow_two,div_eq_mul_inv] using hb
  have hi := integrableOn_norm_rpow_neg (R:=R) (by norm_num : (2:ℝ)<3)
  calc
    _ ≤ ∫ z in ball (0:Vec) R, ‖F z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in ball (0:Vec) R, C*‖z‖^(-(2:ℝ)) := integral_mono_ae hF.norm (hi.const_mul C) hbound
    _ = 4*Real.pi*C*R := by
      rw [integral_const_mul,integral_ball_norm_rpow_neg (by norm_num : (2:ℝ)<3) hR]
      norm_num only [show (3:ℝ)-2=1 by norm_num,Real.rpow_one,div_one]
      ring

namespace SmoothLorentzFlow

lemma spatial_travel_bound {E B : Field} (F : SmoothLorentzFlow E B) (z : Phase)
    {T t : ℝ} (ht : t∈Icc 0 T) : ‖(F.forward z t).1-z.1‖≤t := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f:=fun r => (F.forward z r).1) (f':=fun r => velocity (F.forward z r).2)
    (fun r (_ : r∈Icc 0 T) => ((ContinuousLinearMap.fst ℝ Vec Vec).hasFDerivAt.comp_hasDerivAt r (F.ode z r)).hasDerivWithinAt)
    (fun r (_ : r∈Ico 0 T) => (norm_velocity_lt_one _).le) t ht
  simpa only [F.initial,one_mul,sub_zero] using hh

lemma momentum_travel_bound {E B : Field} (F : SmoothLorentzFlow E B) (z : Phase)
    {T t R L : ℝ} (ht : t∈Icc 0 T) (hz : ‖z.1‖+T≤R)
    (_hL : 0≤L) (hE : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R → ‖E (r,x)‖≤L)
    (hB : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R → ‖B (r,x)‖≤L) :
    ‖(F.forward z t).2-z.2‖≤(2*L)*t := by
  have hspace (r : ℝ) (hr : r∈Icc 0 T) : ‖(F.forward z r).1‖≤R := by
    calc
      _ ≤ ‖(F.forward z r).1-z.1‖+‖z.1‖ := norm_le_norm_sub_add _ _
      _ ≤ r+‖z.1‖ := add_le_add (F.spatial_travel_bound z hr) le_rfl
      _ ≤ R := by linarith [hr.2]
  have hb (r : ℝ) (hr : r∈Ico 0 T) :
      ‖E (r,(F.forward z r).1)+cross (velocity (F.forward z r).2) (B (r,(F.forward z r).1))‖≤2*L := by
    have hh := Ico_subset_Icc_self hr
    calc
      _ ≤ ‖E (r,(F.forward z r).1)‖+‖cross (velocity (F.forward z r).2) (B (r,(F.forward z r).1))‖ := norm_add_le _ _
      _ ≤ L + 1*L := add_le_add (hE r hh _ (hspace r hh))
        ((norm_cross_le _ _).trans (mul_le_mul (norm_velocity_lt_one _).le
          (hB r hh _ (hspace r hh)) (norm_nonneg _) (by norm_num)))
      _ = 2*L := by ring
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f:=fun r => (F.forward z r).2)
    (f':=fun r => E (r,(F.forward z r).1)+cross (velocity (F.forward z r).2) (B (r,(F.forward z r).1)))
    (fun r (_ : r∈Icc 0 T) => ((ContinuousLinearMap.snd ℝ Vec Vec).hasFDerivAt.comp_hasDerivAt r (F.ode z r)).hasDerivWithinAt) hb t ht
  simpa only [F.initial,sub_zero] using hh

lemma transport_for {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) (t : ℝ) (z : Phase) :
    s.f (t,F.forward z t)=s.f (0,z) := by
  have hd (r : ℝ) : HasDerivAt (fun r => s.f (r,F.forward z r)) (0:ℝ) r := by
    have hh := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (F.ode z r))
    change HasDerivAt (fun r => s.f (r,F.forward z r))
      (fderiv ℝ s.f (r,F.forward z r) (1,lorentzField E B (r,F.forward z r))) r at hh
    rw [hV] at hh
    exact hh
  have he := is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) t 0
  simpa only [F.initial] using he

lemma transport_for_inverse {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) (t : ℝ) (z : Phase) :
    s.f (t,z)=s.f (0,F.backward (t,z)) := by
  simpa only [F.right_inverse] using F.transport_for hf hV t (F.backward (t,z))

lemma transported_sup_bound {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) {A : ℝ}
    (hA : ∀ z, |s.f (0,z)|≤A) (t : ℝ) (z : Phase) : |s.f (t,z)|≤A := by
  rw [F.transport_for_inverse hf hV]
  exact hA _

lemma transported_phase_bound {E B : Field} (F : SmoothLorentzFlow E B) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hV : TransportFor s E B) {R₀ P₀ T L t : ℝ}
    (h₀ : ∀ z : Phase, s.f (0,z)≠0 → ‖z.1‖≤R₀ ∧ ‖z.2‖≤P₀)
    (hL : 0≤L) (hE : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R₀+T → ‖E (r,x)‖≤L)
    (hB : ∀ r∈Icc 0 T, ∀ x : Vec, ‖x‖≤R₀+T → ‖B (r,x)‖≤L)
    (ht : t∈Icc 0 T) (z : Phase) (hz : s.f (t,z)≠0) :
    ‖z.1‖≤R₀+t ∧ ‖z.2‖≤P₀+2*L*t := by
  let z₀ := F.backward (t,z)
  have he : F.forward z₀ t=z := F.right_inverse t z
  have hz₀ : s.f (0,z₀)≠0 := by
    rw [← F.transport_for_inverse hf hV]
    exact hz
  have hb := h₀ z₀ hz₀
  have hx := F.spatial_travel_bound z₀ ht
  have hv := F.momentum_travel_bound z₀ ht (by linarith [hb.1]) hL hE hB
  rw [he] at hx hv
  constructor
  · exact (norm_le_norm_sub_add z.1 z₀.1).trans (by linarith [hb.1])
  · exact (norm_le_norm_sub_add z.2 z₀.2).trans (by linarith [hb.2])

end SmoothLorentzFlow

lemma mixed_physical_vector {s : Solution} {E B : Field}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ s.E) (hB' : ContDiff ℝ ∞ s.B)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s E B)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor s) {t : ℝ} (ht : 0<t) (x : Vec) :
    s.E (t,x)=electricBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity {s with E:=E,B:=B} t x (x+z) ∧
    s.B (t,x)=magneticBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity {s with E:=E,B:=B} t x (x+z) := by
  have hf1 : ContDiffOn ℝ 1 s.f particleHalfSpace := (hf.of_le (by simp)).contDiffOn
  have hE1 : ContDiffOn ℝ 1 E fieldHalfSpace := (hE.of_le (by simp)).contDiffOn
  have hB1 : ContDiffOn ℝ 1 B fieldHalfSpace := (hB.of_le (by simp)).contDiffOn
  constructor
  · ext i
    have hD := integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
    exact (mixed_electric_physical_representation (s:={s with E:=E,B:=B})
      hf1 hE1 hB1 hc hV hE' hB' hρ hj hM ht x i).trans
      (by simpa only [electricBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
        smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => electricConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)
  · ext i
    have hD := integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
    exact (mixed_magnetic_physical_representation (s:={s with E:=E,B:=B})
      hf1 hE1 hB1 hc hV hE' hB' hj hM ht x i).trans
      (by simpa only [magneticBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
        smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => magneticConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

lemma scaled_kernel_tip_le_on {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {C R : ℝ} (hR : 0≤R) (hF : IntegrableOn F (ball (0:Vec) R))
    (hb : ∀ᵐ z ∂volume.restrict (ball (0:Vec) R), ‖F z‖≤C/‖z‖^2) :
    ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) R, F z‖≤C*R := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(4*Real.pi)⁻¹)]
  calc
    _ ≤ (4*Real.pi)⁻¹*(4*Real.pi*C*R) :=
      mul_le_mul_of_nonneg_left (kernel_tip_le_on hR hF hb) (by positivity)
    _ = C*R := by field_simp

lemma mixed_fields_bound {s : Solution} {E B : Field}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ s.E) (hB' : ContDiff ℝ ∞ s.B)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s E B)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor s) {t C D : ℝ} (ht : 0<t) (x : Vec)
    (hD : ‖electricBoundaryField s t x‖≤D ∧ ‖magneticBoundaryField s t x‖≤D)
    (hden : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t →
      ‖retardedElectricDensity {s with E:=E,B:=B} t x (x+z)‖≤C/‖z‖^2 ∧
      ‖retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)‖≤C/‖z‖^2) :
    ‖s.E (t,x)‖≤D+C*t ∧ ‖s.B (t,x)‖≤D+C*t := by
  have hf1 : ContDiffOn ℝ 1 s.f particleHalfSpace := (hf.of_le (by simp)).contDiffOn
  have hE1 : ContDiffOn ℝ 1 E fieldHalfSpace := (hE.of_le (by simp)).contDiffOn
  have hB1 : ContDiffOn ℝ 1 B fieldHalfSpace := (hB.of_le (by simp)).contDiffOn
  have he := mixed_physical_vector hf hE hB hE' hB' hc hV hρ hj hM ht x
  have hEe : ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,
      retardedElectricDensity {s with E:=E,B:=B} t x (x+z)‖≤C*t := by
    apply scaled_kernel_tip_le_on ht.le
      (integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x)
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact (hden z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le).1
  have hBb : ‖(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t,
      retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)‖≤C*t := by
    apply scaled_kernel_tip_le_on ht.le
      (integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x)
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact (hden z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le).2
  constructor
  · rw [he.1]
    exact (norm_add_le _ _).trans (add_le_add hD.1 hEe)
  · rw [he.2]
    exact (norm_add_le _ _).trans (add_le_add hD.2 hBb)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma datum_particle_bounds {d : Datum} (hd : Admissible d) :
    ∃ A R P : ℝ, 0≤A ∧ 0≤R ∧ 0≤P ∧ (∀ z, |d.f₀ z|≤A) ∧
      ∀ z : Phase, d.f₀ z≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P := by
  obtain ⟨A,hA⟩ := hd.1.continuous.bounded_above_of_compact_support hd.2.1
  obtain ⟨R,hR⟩ := (hd.2.1.image continuous_fst).isBounded.exists_norm_le
  obtain ⟨P,hP⟩ := (hd.2.1.image continuous_snd).isBounded.exists_norm_le
  refine ⟨max A 0,max R 0,max P 0,le_max_right _ _,le_max_right _ _,le_max_right _ _,
    fun z => (hA z).trans (le_max_left _ _),?_⟩
  intro z hz
  exact ⟨(hR _ ⟨z,subset_tsupport _ hz,rfl⟩).trans (le_max_left _ _),
    (hP _ ⟨z,subset_tsupport _ hz,rfl⟩).trans (le_max_left _ _)⟩

lemma PicardRegular.boundary_eq {d : Datum} {s : Solution} (hs : PicardRegular d s)
    {t : ℝ} (ht : 0<t) (x : Vec) :
    electricBoundaryField s t x=electricBoundaryField (datumBoundarySolution d) t x ∧
    magneticBoundaryField s t x=magneticBoundaryField (datumBoundarySolution d) t x := by
  constructor
  · ext i
    exact electricConeBoundary_initial_congr (s':=datumBoundarySolution d)
      hs.initial_f hs.initial_E hs.initial_B ht x i
  · ext i
    exact magneticConeBoundary_initial_congr (s':=datumBoundarySolution d)
      hs.initial_f hs.initial_E hs.initial_B ht x i

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PicardKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma compact_parameter_lipschitz
    {U W Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {K : Set U} {S : Set W} {g : U × W → Z}
    (hK : IsCompact K) (hS : IsCompact S) (hconv : Convex ℝ S)
    (hg : ∀ q∈K ×ˢ S, ContDiffAt ℝ 1 g q) :
    ∃ C : ℝ, 0≤C ∧ ∀ p∈K, ∀ x∈S, ∀ y∈S, ‖g (p,y)-g (p,x)‖≤C*‖y-x‖ := by
  have hd : ContinuousOn (fderiv ℝ g) (K ×ˢ S) :=
    fun q hq => ((hg q hq).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨D,hD⟩ := ((hK.prod hS).image_of_continuousOn hd).isBounded.exists_norm_le
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro p hp x hx y hy
  apply hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => ((hg (p,z) ⟨hp,hz⟩).differentiableAt (by norm_num)).comp z
      ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z)).differentiableAt) _ hx hy
  intro z hz
  have hf := ((hg (p,z) ⟨hp,hz⟩).differentiableAt (by norm_num)).hasFDerivAt.comp z
    ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z))
  rw [hf.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _)
  intro v
  change ‖fderiv ℝ g (p,z) (0,v)‖≤ max D 0*‖v‖
  have hh := (fderiv ℝ g (p,z)).le_opNorm (0,v)
  simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg v)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    ((hD _ ⟨(p,z),⟨hp,hz⟩,rfl⟩).trans (le_max_left _ _)) (norm_nonneg v))

lemma contDiffAt_normalisedElectricKernel {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] {k : ℕ∞ω}
    {r : H → ℝ} {n u b : H → Vec} {z : H}
    (hr : ContDiffAt ℝ k r z) (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hb : ContDiffAt ℝ k b z) (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun p => normalisedElectricKernel (r p) (n p) (u p) (b p)) z := by
  have hdot (f g : H → Vec) (hf : ContDiffAt ℝ k f z) (hg : ContDiffAt ℝ k g z) :
      ContDiffAt ℝ k (fun p => dot (f p) (g p)) z :=
    contDiff_dot_pair.contDiffAt.comp z (hf.prodMk hg)
  have hD : ContDiffAt ℝ k (fun p => 1-dot (n p) (u p)) z :=
    contDiffAt_const.sub (hdot n u hn hu)
  exact (((contDiffAt_const.sub (hdot u u hu hu)).div (hD.pow 3) (pow_ne_zero 3 hd)).smul
      (hn.sub hu)).add ((hr.div (hD.pow 3) (pow_ne_zero 3 hd)).smul
      (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma normalisedPhysicalIntegrand_smoothAt {p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec)}
    (hd : 1-dot p.1.2.1 (velocity p.1.2.2)≠0) :
    ContDiffAt ℝ ∞ normalisedPhysicalIntegrand p := by
  let v : ((ℝ × Vec × Vec) × (ℝ × Vec × Vec)) → Vec := fun p => p.1.2.2
  have hv : ContDiff ℝ ∞ v := contDiff_fst.snd.snd
  have hu : ContDiff ℝ ∞ (fun p => velocity (v p)) := contDiff_velocity.comp hv
  have hb : ContDiff ℝ ∞ (fun p => fderiv ℝ velocity (v p)
      (p.2.2.1+cross (velocity (v p)) p.2.2.2)) :=
    (((contDiff_velocity (k:=∞)).fderiv_right (by simp)).comp hv).clm_apply
      (contDiff_snd.snd.fst.add (contDiff_cross.comp (hu.prodMk contDiff_snd.snd.snd)))
  have hD : ContDiff ℝ ∞ (fun p => 1-dot p.1.2.1 (velocity (v p))) :=
    contDiff_const.sub (contDiff_dot_pair.comp (contDiff_fst.snd.fst.prodMk hu))
  exact (contDiffAt_snd.fst.mul hD.contDiffAt).smul
    (contDiffAt_normalisedElectricKernel contDiffAt_fst.fst contDiffAt_fst.snd.fst
      hu.contDiffAt hb.contDiffAt hd)

lemma uniform_normalised_integrand_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a b : ℝ, |a|≤A → |b|≤A →
      ∀ E B E' B' : Vec, ‖E‖≤L → ‖B‖≤L → ‖E'‖≤L → ‖B'‖≤L →
      ‖normalisedPhysicalIntegrand ((r,n,v),(a,E,B))-
        normalisedPhysicalIntegrand ((r,n,v),(b,E',B'))‖≤
          C*max |a-b| (max ‖E-E'‖ ‖B-B'‖) := by
  let K : Set (ℝ × Vec × Vec) := Icc (0:ℝ) 1 ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  let S : Set (ℝ × Vec × Vec) := closedBall (0:ℝ) A ×ˢ closedBall (0:Vec) L ×ˢ closedBall (0:Vec) L
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere _ _).prod (isCompact_closedBall _ _))
  have hS : IsCompact S := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : Convex ℝ S := (convex_closedBall _ _).prod ((convex_closedBall _ _).prod (convex_closedBall _ _))
  obtain ⟨C,hC,hb⟩ := compact_parameter_lipschitz hK hS hc (g:=normalisedPhysicalIntegrand) (by
    intro p hp
    apply (normalisedPhysicalIntegrand_smoothAt ?_).of_le (by simp)
    exact (cone_denom_pos p.1.2.2 p.1.2.1
      (by simpa only [mem_sphere,dist_zero_right] using hp.1.2.1)).ne')
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a b ha hb' E B E' B' hE hB hE' hB'
  have hh := hb (r,n,v) ⟨hr,by simpa only [mem_sphere,dist_zero_right] using hn,
      by simpa only [mem_closedBall_zero_iff] using hv⟩
    (b,E',B') ⟨by simpa only [mem_closedBall_zero_iff,Real.norm_eq_abs] using hb',
      by simpa only [mem_closedBall_zero_iff] using hE',by simpa only [mem_closedBall_zero_iff] using hB'⟩
    (a,E,B) ⟨by simpa only [mem_closedBall_zero_iff,Real.norm_eq_abs] using ha,
      by simpa only [mem_closedBall_zero_iff] using hE,by simpa only [mem_closedBall_zero_iff] using hB⟩
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs] using hh

lemma normalisedPhysicalIntegrand_eq {r : ℝ} (hr : r≠0) (n v : Vec) (a : ℝ) (E B : Vec) :
    normalisedPhysicalIntegrand ((r,n,v),(a,E,B)) = r^2 •
      ((a*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
        (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  simp only [normalisedPhysicalIntegrand,normalisedElectricKernel_eq hr]
  exact smul_comm _ _ _

lemma uniform_physical_integrand_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a b : ℝ, |a|≤A → |b|≤A →
      ∀ E B E' B' : Vec, ‖E‖≤L → ‖B‖≤L → ‖E'‖≤L → ‖B'‖≤L →
      ‖(a*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B))-
        (b*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E'+cross (velocity v) B'))‖≤
          (C/r^2)*max |a-b| (max ‖E-E'‖ ‖B-B'‖) := by
  obtain ⟨C,hC,hb⟩ := uniform_normalised_integrand_lipschitz A P L
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a b ha hb' E B E' B' hE hB hE' hB'
  have hh := hb r ⟨hr.1.le,hr.2⟩ n hn v hv a b ha hb' E B E' B' hE hB hE' hB'
  rw [normalisedPhysicalIntegrand_eq hr.1.ne',normalisedPhysicalIntegrand_eq hr.1.ne',
    ← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] at hh
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr (by simpa only [mul_comm] using hh)

lemma integrable_physical_integrand {f : Vec → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) {r : ℝ} (hr : r≠0) {n : Vec} (hn : ‖n‖=1) (E B : Vec) :
    Integrable (fun v : Vec => (f v*(1-dot n (velocity v))) •
      physicalElectricKernel r n (velocity v) (fderiv ℝ velocity v (E+cross (velocity v) B))) := by
  have hd : Continuous (fun v => 1-dot n (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
      (continuous_const.prodMk (contDiff_velocity (k:=1)).continuous))
  exact ((hf.mul hd).smul (continuous_physicalElectricKernel_velocity hr hn E B)).integrable_of_hasCompactSupport
    (hc.mul_right.smul_right)

lemma uniform_physical_integral_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Ioc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ f g : Vec → ℝ, Continuous f → Continuous g → HasCompactSupport f → HasCompactSupport g →
      (∀ v, |f v|≤A ∧ |g v|≤A) → (∀ v, P<‖v‖ → f v=0 ∧ g v=0) →
      ∀ E B E' B' : Vec, ‖E‖≤L → ‖B‖≤L → ‖E'‖≤L → ‖B'‖≤L →
      ∀ D : ℝ, (∀ v, |f v-g v|≤D) → ‖E-E'‖≤D → ‖B-B'‖≤D →
      ‖(∫ v : Vec, (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B)))-
        (∫ v : Vec, (g v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E'+cross (velocity v) B')))‖≤ C*D/r^2 := by
  obtain ⟨K,hK,hk⟩ := uniform_physical_integrand_lipschitz A P L
  refine ⟨K*volume.real (closedBall (0:Vec) P),by positivity,?_⟩
  intro r hr n hn f g hf hg hfc hgc hab hs E B E' B' hE hB hE' hB' D hD hEd hBd
  rw [← integral_sub (integrable_physical_integrand hf hfc hr.1.ne' hn E B)
    (integrable_physical_integrand hg hgc hr.1.ne' hn E' B')]
  let H : Vec → Vec := fun v =>
    (f v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E+cross (velocity v) B))-
    (g v*(1-dot n (velocity v))) • physicalElectricKernel r n (velocity v)
          (fderiv ℝ velocity v (E'+cross (velocity v) B'))
  change ‖∫ v, H v‖≤_
  have he : (∫ v in closedBall (0:Vec) P, H v)=∫ v, H v := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    obtain ⟨hvf,hvg⟩ := hs v (by simpa only [mem_closedBall_zero_iff,not_le] using hv)
    simp only [H,hvf,hvg,zero_mul,zero_smul,sub_self]
  rw [← he]
  have hh := norm_setIntegral_le_of_norm_le_const (μ:=volume)
    (isCompact_closedBall (0:Vec) P).measure_lt_top (C:=(K/r^2)*D) (f:=H) (by
      intro v hv
      exact (hk r hr n hn v (mem_closedBall_zero_iff.mp hv) (f v) (g v) (hab v).1 (hab v).2
        E B E' B' hE hB hE' hB').trans
          (mul_le_mul_of_nonneg_left (max_le (hD v) (max_le hEd hBd)) (by positivity)))
  exact hh.trans_eq (by ring)

lemma uniform_retarded_density_lipschitz (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s s' : Solution) (T : ℝ), T≤1 →
      ContDiff ℝ ∞ s.f → ContDiff ℝ ∞ s'.f →
      CompactOnFiniteHorizons s → CompactOnFiniteHorizons s' →
      (∀ t∈Icc 0 T, ∀ x v, |s.f (t,x,v)|≤A ∧ |s'.f (t,x,v)|≤A) →
      (∀ t∈Icc 0 T, ∀ x v, P<‖v‖ → s.f (t,x,v)=0 ∧ s'.f (t,x,v)=0) →
      (∀ t∈Icc 0 T, ∀ x, ‖s.E (t,x)‖≤L ∧ ‖s.B (t,x)‖≤L ∧
        ‖s'.E (t,x)‖≤L ∧ ‖s'.B (t,x)‖≤L) →
      ∀ t∈Icc 0 T, ∀ x x' z : Vec, 0<‖z‖ → ‖z‖≤t → ∀ D : ℝ,
      (∀ v, |s.f (t-‖z‖,x+z,v)-s'.f (t-‖z‖,x'+z,v)|≤D) →
      ‖s.E (t-‖z‖,x+z)-s'.E (t-‖z‖,x'+z)‖≤D →
      ‖s.B (t-‖z‖,x+z)-s'.B (t-‖z‖,x'+z)‖≤D →
        ‖retardedElectricDensity s t x (x+z)-retardedElectricDensity s' t x' (x'+z)‖≤C*D/‖z‖^2 ∧
        ‖retardedMagneticDensity s t x (x+z)-retardedMagneticDensity s' t x' (x'+z)‖≤C*D/‖z‖^2 := by
  obtain ⟨C,hC,hk⟩ := uniform_physical_integral_lipschitz A P L
  refine ⟨C,hC,?_⟩
  intro s s' T hT hf hf' hc hc' hab hs hEB t ht x x' z hz hzt D hD hEd hBd
  have htime : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  have hxy : x≠x+z := by
    intro he
    have hh : z=0 := add_left_cancel (show x+z=x+0 by simpa using he.symm)
    exact (norm_pos_iff.mp hz) hh
  have hn : ‖-(‖z‖⁻¹ • z)‖=1 := by simpa only [coneDirection_add] using coneDirection_norm hxy
  obtain ⟨hfc,hcomp⟩ := (show RegularParticle s.f from ⟨(hf.of_le (by simp)).contDiffOn,hc⟩).slice htime.1 (x+z)
  obtain ⟨hgc,hcomp'⟩ := (show RegularParticle s'.f from ⟨(hf'.of_le (by simp)).contDiffOn,hc'⟩).slice htime.1 (x'+z)
  have he : ‖retardedElectricDensity s t x (x+z)-retardedElectricDensity s' t x' (x'+z)‖≤C*D/‖z‖^2 := by
    simp only [retardedElectricDensity,coneRadius_add,coneDirection_add]
    exact hk ‖z‖ ⟨hz,hzt.trans (ht.2.trans hT)⟩ _ hn _ _ hfc.continuous hgc.continuous hcomp hcomp'
      (fun v => ⟨(hab _ htime (x+z) v).1,(hab _ htime (x'+z) v).2⟩)
      (fun v hv => ⟨(hs _ htime (x+z) v hv).1,(hs _ htime (x'+z) v hv).2⟩)
      _ _ _ _ (hEB _ htime (x+z)).1 (hEB _ htime (x+z)).2.1
      (hEB _ htime (x'+z)).2.2.1 (hEB _ htime (x'+z)).2.2.2 D hD hEd hBd
  refine ⟨he,?_⟩
  simp only [retardedMagneticDensity,coneDirection_add,← cross_sub_right]
  exact (norm_cross_le _ _).trans (by simpa only [hn,one_mul] using he)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardContraction
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

lemma norm_boundary_integral_difference {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F G : Vec → W} {a b : W} {t C D : ℝ} (ht : 0≤t)
    (hF : IntegrableOn F (ball (0:Vec) t)) (hG : IntegrableOn G (ball (0:Vec) t))
    (hab : ‖a-b‖≤D)
    (hFG : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t → ‖F z-G z‖≤C/‖z‖^2) :
    ‖(a+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z)-
      (b+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, G z)‖≤D+C*t := by
  rw [show (a+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, F z)-
      (b+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, G z)=
      (a-b)+(4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, (F z-G z) by
        rw [integral_sub hF hG,smul_sub]; abel]
  apply (norm_add_le _ _).trans (add_le_add hab ?_)
  apply scaled_kernel_tip_le_on ht (hF.sub hG)
  filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  exact hFG z (norm_pos_iff.mpr hz0) (mem_ball_zero_iff.mp hz).le

lemma mixed_fields_difference_bound {d : Datum} {s s' : Solution} {E B E' B' : Field}
    (hs : PicardRegular d s) (hs' : PicardRegular d s')
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
    (hV : TransportFor s E B) (hV' : TransportFor s' E' B')
    {t C D : ℝ} (ht : 0<t) (x x' : Vec)
    (hb : ‖electricBoundaryField (datumBoundarySolution d) t x-
        electricBoundaryField (datumBoundarySolution d) t x'‖≤D ∧
      ‖magneticBoundaryField (datumBoundarySolution d) t x-
        magneticBoundaryField (datumBoundarySolution d) t x'‖≤D)
    (hden : ∀ z : Vec, 0<‖z‖ → ‖z‖≤t →
      ‖retardedElectricDensity {s with E:=E,B:=B} t x (x+z)-
        retardedElectricDensity {s' with E:=E',B:=B'} t x' (x'+z)‖≤C/‖z‖^2 ∧
      ‖retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)-
        retardedMagneticDensity {s' with E:=E',B:=B'} t x' (x'+z)‖≤C/‖z‖^2) :
    ‖s.E (t,x)-s'.E (t,x')‖≤D+C*t ∧ ‖s.B (t,x)-s'.B (t,x')‖≤D+C*t := by
  have he := mixed_physical_vector hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
    hs.smooth_rho hs.smooth_current hs.maxwell ht x
  have he' := mixed_physical_vector hs'.smooth_f hE' hB' hs'.smooth_E hs'.smooth_B hs'.compact hV'
    hs'.smooth_rho hs'.smooth_current hs'.maxwell ht x'
  have hf1 := (hs.smooth_f.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=particleHalfSpace)
  have hg1 := (hs'.smooth_f.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=particleHalfSpace)
  have hE1 := (hE.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hB1 := (hB.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hE1' := (hE'.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hB1' := (hB'.of_le (by simp : (1:ℕ∞ω)≤∞)).contDiffOn (s:=fieldHalfSpace)
  have hbe := hs.boundary_eq ht x
  have hbe' := hs'.boundary_eq ht x'
  constructor
  · rw [he.1,he'.1,hbe.1,hbe'.1]
    exact norm_boundary_integral_difference ht.le
      (integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hs.compact ht.le le_rfl x)
      (integrableOn_retardedElectricDensity_le (s:={s' with E:=E',B:=B'}) hg1 hE1' hB1' hs'.compact ht.le le_rfl x')
      hb.1 (fun z hz hzt => (hden z hz hzt).1)
  · rw [he.2,he'.2,hbe.2,hbe'.2]
    exact norm_boundary_integral_difference ht.le
      (integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hs.compact ht.le le_rfl x)
      (integrableOn_retardedMagneticDensity_le (s:={s' with E:=E',B:=B'}) hg1 hE1' hB1' hs'.compact ht.le le_rfl x')
      hb.2 (fun z hz hzt => (hden z hz hzt).2)

theorem uniform_global_picard_invariance {d : Datum} (hd : Admissible d) :
    ∃ T A R P L : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧
      GlobalFieldBound T L (fun p : ℝ × Vec => d.E₀ p.2) (fun p : ℝ × Vec => d.B₀ p.2) ∧
      ∀ U : ℝ, 0≤U → U≤T → ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → GlobalFieldBound U L E B →
        ∀ s : Solution, PicardRegular d s → TransportFor s E B →
          LocalParticleBound U A R P s.f ∧ GlobalFieldBound U L s.E s.B := by
  obtain ⟨A,R₀,P₀,hA,hR₀,hP₀,hf₀,hphase₀⟩ := datum_particle_bounds hd
  let R := R₀+1
  let P := P₀+1
  obtain ⟨D,hD,hDEB,hboundary⟩ := datum_boundary_global_bound hd
  let L := D+1
  have hL : 0<L := by dsimp [L]; linarith
  obtain ⟨C,hC,hdensity⟩ := uniform_retarded_density_bound A P L hA
  let T := min 1 (min ((2*L+1)⁻¹) ((C+1)⁻¹))
  have hT : 0<T := by dsimp [T]; positivity
  have hT1 : T≤1 := min_le_left _ _
  have hT2 : T≤(2*L+1)⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hT3 : T≤(C+1)⁻¹ := (min_le_right _ _).trans (min_le_right _ _)
  have hLT : 2*L*T≤1 := by
    have hh : T*(2*L+1)≤1 := (le_div_iff₀ (by positivity : 0<2*L+1)).mp (by simpa only [one_div] using hT2)
    nlinarith
  have hCT : C*T≤1 := by
    have hh : T*(C+1)≤1 := (le_div_iff₀ (by positivity : 0<C+1)).mp (by simpa only [one_div] using hT3)
    nlinarith
  refine ⟨T,A,R,P,L,hT,hT1,hA,by dsimp [R]; linarith,by dsimp [P]; linarith,hL,?_,?_⟩
  · intro t ht x
    exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
      (hDEB x).2.trans (by dsimp [L]; linarith)⟩
  · intro U hU0 hU E B hE hB hEB s hs hV
    have hU1 : U≤1 := hU.trans hT1
    have hLU : 2*L*U≤1 := (mul_le_mul_of_nonneg_left hU (by positivity)).trans hLT
    have hCU : C*U≤1 := (mul_le_mul_of_nonneg_left hU hC).trans hCT
    obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
    have hf : ∀ t∈Icc 0 U, ∀ z, |s.f (t,z)|≤A := by
      intro t ht z
      exact F.transported_sup_bound hs.smooth_f hV (fun z => by rw [hs.initial_f]; exact hf₀ z) t z
    have hphase : ∀ t∈Icc 0 U, ∀ z : Phase, s.f (t,z)≠0 → ‖z.1‖≤R ∧ ‖z.2‖≤P := by
      intro t ht z hz
      have hh := F.transported_phase_bound hs.smooth_f hV
        (R₀:=R₀) (P₀:=P₀) (T:=U) (L:=L)
        (fun z hz => hphase₀ z (by simpa only [hs.initial_f] using hz)) hL.le
        (fun r hr x hx => (hEB r hr x).1)
        (fun r hr x hx => (hEB r hr x).2) ht z hz
      constructor
      · dsimp [R]
        linarith [hh.1,ht.2]
      · dsimp [P]
        have hh' : 2*L*t≤2*L*U := mul_le_mul_of_nonneg_left ht.2 (by positivity)
        linarith [hh.2]
    refine ⟨fun t ht x v => ⟨hf t ht (x,v),hphase t ht (x,v)⟩,?_⟩
    intro t ht x
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      rw [hs.initial_E,hs.initial_B]
      exact ⟨(hDEB x).1.trans (by dsimp [L]; linarith),
        (hDEB x).2.trans (by dsimp [L]; linarith)⟩
    · have hbd := hboundary t ⟨ht0,ht.2.trans hU1⟩ x
      rw [← (hs.boundary_eq ht0 x).1,← (hs.boundary_eq ht0 x).2] at hbd
      have hdens := hdensity {s with E:=E,B:=B} U hU1 hf (by
        intro r hr y v hv
        exact ⟨(hphase r hr (y,v) hv).2,hEB r hr y⟩) t ht x
      have hh := mixed_fields_bound hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
        hs.smooth_rho hs.smooth_current hs.maxwell ht0 x hbd hdens
      have hh' : C*t≤C*U := mul_le_mul_of_nonneg_left ht.2 hC
      have hbound : D+C*t≤L := by dsimp [L]; linarith
      exact ⟨hh.1.trans hbound,hh.2.trans hbound⟩

lemma uniform_picard_comparison (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (d : Datum) (s s' : Solution) (E B E' B' : Field),
      PicardRegular d s → PicardRegular d s' →
      ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → ContDiff ℝ ∞ E' → ContDiff ℝ ∞ B' →
      TransportFor s E B → TransportFor s' E' B' →
      ∀ T : ℝ, T≤1 →
      (∀ r∈Icc 0 T, ∀ x v, |s.f (r,x,v)|≤A ∧ |s'.f (r,x,v)|≤A) →
      (∀ r∈Icc 0 T, ∀ x v, P<‖v‖ → s.f (r,x,v)=0 ∧ s'.f (r,x,v)=0) →
      GlobalFieldBound T L E B → GlobalFieldBound T L E' B' →
      ∀ t∈Ioc 0 T, ∀ x x' : Vec, ∀ D H J : ℝ,
      (‖electricBoundaryField (datumBoundarySolution d) t x-
          electricBoundaryField (datumBoundarySolution d) t x'‖≤D ∧
        ‖magneticBoundaryField (datumBoundarySolution d) t x-
          magneticBoundaryField (datumBoundarySolution d) t x'‖≤D) →
      (∀ r∈Icc 0 T, ∀ z v, |s.f (r,x+z,v)-s'.f (r,x'+z,v)|≤H) →
      (∀ r∈Icc 0 T, ∀ z, ‖E (r,x+z)-E' (r,x'+z)‖≤J ∧
        ‖B (r,x+z)-B' (r,x'+z)‖≤J) →
      ‖s.E (t,x)-s'.E (t,x')‖≤D+C*(max H J)*t ∧
      ‖s.B (t,x)-s'.B (t,x')‖≤D+C*(max H J)*t := by
  obtain ⟨C,hC,hk⟩ := uniform_retarded_density_lipschitz A P L
  refine ⟨C,hC,?_⟩
  intro d s s' E B E' B' hs hs' hE hB hE' hB' hV hV' T hT hab hp hEB hEB' t ht x x' D H J hb hf hdiff
  apply mixed_fields_difference_bound hs hs' hE hB hE' hB' hV hV' ht.1 x x' hb
  intro z hz hzt
  have hr : t-‖z‖∈Icc 0 T := ⟨by linarith,by linarith [ht.2,norm_nonneg z]⟩
  exact hk {s with E:=E,B:=B} {s' with E:=E',B:=B'} T hT hs.smooth_f hs'.smooth_f
    hs.compact hs'.compact hab hp
    (fun r hr y => ⟨(hEB r hr y).1,(hEB r hr y).2,(hEB' r hr y).1,(hEB' r hr y).2⟩)
    t ⟨ht.1.le,ht.2⟩ x x' z hz hzt (max H J)
    (fun v => (hf _ hr z v).trans (le_max_left _ _))
    ((hdiff _ hr z).1.trans (le_max_right _ _)) ((hdiff _ hr z).2.trans (le_max_right _ _))

theorem uniform_picard_control {d : Datum} (hd : Admissible d) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      FieldControl T L N (fun p : ℝ × Vec => d.E₀ p.2) (fun p : ℝ × Vec => d.B₀ p.2) ∧
      (∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B → FieldControl T L N E B →
        ∀ s : Solution, PicardRegular d s → TransportFor s E B →
          LocalParticleBound T A R P s.f ∧ PhaseParticleLip T M s.f ∧ FieldControl T L N s.E s.B) ∧
      (∀ (E B E' B' : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
        ContDiff ℝ ∞ E' → ContDiff ℝ ∞ B' → FieldControl T L N E B → FieldControl T L N E' B' →
        ∀ (s s' : Solution), PicardRegular d s → PicardRegular d s' →
          TransportFor s E B → TransportFor s' E' B' →
        ∀ D : ℝ, 0≤D →
          (∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D ∧ ‖B (t,x)-B' (t,x)‖≤D) →
          ∀ t∈Icc 0 T, ∀ x, ‖s.E (t,x)-s'.E (t,x)‖≤D/2 ∧ ‖s.B (t,x)-s'.B (t,x)‖≤D/2) := by
  obtain ⟨T₀,A,R,P,L,hT₀,hT₀1,hA,hR,hP,hL,h₀,hstep⟩ := uniform_global_picard_invariance hd
  obtain ⟨D₀,hD₀,hDinit,hDb⟩ := datum_boundary_global_lipschitz hd
  obtain ⟨A₁,hA₁,hAf⟩ := smooth_compact_lipschitz (hd.1.of_le (by simp)) hd.2.1
  have hAf' (z w : Phase) : |d.f₀ z-d.f₀ w|≤A₁*‖z-w‖ := by
    simpa only [Real.norm_eq_abs] using hAf w z
  obtain ⟨C,hC,hcomp⟩ := uniform_picard_comparison A P L
  let N := D₀+1
  let M := A₁*Real.exp 1
  let K := 1+2*N+L
  have hN : 0<N := by dsimp [N]; linarith
  have hM : 0≤M := by dsimp [M]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  let T := min T₀ (min K⁻¹ (min (C*(M+N)+1)⁻¹ (2*C*(2*M+1)+1)⁻¹))
  have hT : 0<T := by dsimp [T]; positivity
  have hTT : T≤T₀ := min_le_left _ _
  have hT1 : T≤1 := hTT.trans hT₀1
  have hTK : K*T≤1 := by
    have hh : T≤K⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ hK).mp (show T≤1/K by simpa only [one_div] using hh)
    nlinarith
  have hTC : C*(M+N)*T≤1 := by
    have hh : T≤(C*(M+N)+1)⁻¹ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh' := (le_div_iff₀ (by positivity : 0<C*(M+N)+1)).mp
      (show T≤1/(C*(M+N)+1) by simpa only [one_div] using hh)
    nlinarith
  have hTC' : 2*C*(2*M+1)*T≤1 := by
    have hh : T≤(2*C*(2*M+1)+1)⁻¹ :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh' := (le_div_iff₀ (by positivity : 0<2*C*(2*M+1)+1)).mp
      (show T≤1/(2*C*(2*M+1)+1) by simpa only [one_div] using hh)
    nlinarith
  have hexp {r : ℝ} (hr : r≤T) : Real.exp (K*r)≤Real.exp 1 :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left hr hK.le).trans hTK)
  have hbase {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
      (hc : FieldControl T L N E B) {s : Solution} (hs : PicardRegular d s) (hV : TransportFor s E B) :=
    hstep T hT.le hTT E B hE hB hc.1 s hs hV
  have hflip {E B : Field} (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
      (hc : FieldControl T L N E B) {s : Solution} (hs : PicardRegular d s) (hV : TransportFor s E B) :
      PhaseParticleLip T M s.f := by
    intro t ht z z'
    have hh := transported_spatial_lipschitz hs hE hB hV hA₁ hL.le hN.le hAf'
      (fun r hr x => (hc.1 r hr x).2) (fun r hr x y => (hc.2 r hr x y).1)
      (fun r hr x y => (hc.2 r hr x y).2) ht z z'
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp le_rfl) hA₁) (norm_nonneg _))
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,?_,?_,?_⟩
  · constructor
    · exact fun t ht x => h₀ t ⟨ht.1,ht.2.trans hTT⟩ x
    · intro t ht x y
      exact ⟨(hDinit x y).1.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)),
        (hDinit x y).2.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _))⟩
  · intro E B hE hB hc s hs hV
    have hp := (hbase hE hB hc hs hV).1
    have hf := hflip hE hB hc hs hV
    refine ⟨hp,hf,(hbase hE hB hc hs hV).2,?_⟩
    intro t ht x y
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      rw [hs.initial_E,hs.initial_E,hs.initial_B,hs.initial_B]
      exact ⟨(hDinit x y).1.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)),
        (hDinit x y).2.trans (mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _))⟩
    · have hh := hcomp d s s E B E B hs hs hE hB hE hB hV hV T hT1
        (fun r hr z v => ⟨(hp r hr z v).1,(hp r hr z v).1⟩)
        (by
          intro r hr z v hv
          have hz : s.f (r,z,v)=0 := by
            by_contra hn
            exact (not_lt_of_ge ((hp r hr z v).2 hn).2) hv
          exact ⟨hz,hz⟩)
        hc.1 hc.1 t ⟨ht0,ht.2⟩ y x (D₀*‖y-x‖) (M*‖y-x‖) (N*‖y-x‖)
        (hDb t ⟨ht0,ht.2.trans hT1⟩ x y)
        (by
          intro r hr z v
          simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero,
            max_eq_left (norm_nonneg _),add_sub_add_right_eq_sub] using hf r hr (y+z,v) (x+z,v))
        (by
          intro r hr z
          simpa only [add_sub_add_right_eq_sub] using hc.2 r hr (x+z) (y+z))
      have hm : max (M*‖y-x‖) (N*‖y-x‖)≤(M+N)*‖y-x‖ := by
        apply max_le <;> nlinarith [norm_nonneg (y-x)]
      have hb : D₀*‖y-x‖+C*max (M*‖y-x‖) (N*‖y-x‖)*t≤N*‖y-x‖ := by
        calc
          _ ≤ D₀*‖y-x‖+C*((M+N)*‖y-x‖)*T := add_le_add le_rfl
            (mul_le_mul (mul_le_mul_of_nonneg_left hm hC) ht.2 ht.1 (by positivity))
          _ = (D₀+C*(M+N)*T)*‖y-x‖ := by ring
          _ ≤ N*‖y-x‖ := mul_le_mul_of_nonneg_right (by dsimp [N]; linarith) (norm_nonneg _)
      exact ⟨hh.1.trans hb,hh.2.trans hb⟩
  · intro E B E' B' hE hB hE' hB' hc hc' s s' hs hs' hV hV' D hD hdiff t ht x
    have hp := (hbase hE hB hc hs hV).1
    have hp' := (hbase hE' hB' hc' hs' hV').1
    rcases eq_or_lt_of_le ht.1 with he|ht0
    · subst t
      simp only [hs.initial_E,hs'.initial_E,hs.initial_B,hs'.initial_B,sub_self,norm_zero]
      exact ⟨by positivity,by positivity⟩
    · have hfd (r : ℝ) (hr : r∈Icc 0 T) (z : Phase) : |s.f (r,z)-s'.f (r,z)|≤2*M*D := by
        have hh := transported_comparison hs.smooth_f hs'.smooth_f hE hB hE' hB' hV hV'
          hs.initial_f hs'.initial_f hA₁ hL.le hN.le hD hAf'
          (fun u hu w => (hc.1 u hu w).2) (fun u hu w w' => (hc.2 u hu w w').1)
          (fun u hu w w' => (hc.2 u hu w w').2)
          (fun u hu w => (hdiff u hu w).1) (fun u hu w => (hdiff u hu w).2) hr z z
        simp only [sub_self,norm_zero,zero_add] at hh
        apply hh.trans
        calc
          A₁*(2*D*r)*Real.exp ((1+2*N+L)*r) = (2*D*r)*(A₁*Real.exp (K*r)) := by ring
          _ ≤ (2*D*r)*M := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hexp hr.2) hA₁) (mul_nonneg (mul_nonneg (by norm_num) hD) hr.1)
          _ ≤ (2*D*1)*M := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hr.2.trans hT1) (by positivity)) hM
          _ = 2*M*D := by ring
      have hh := hcomp d s s' E B E' B' hs hs' hE hB hE' hB' hV hV' T hT1
        (fun r hr z v => ⟨(hp r hr z v).1,(hp' r hr z v).1⟩)
        (by
          intro r hr z v hv
          constructor
          · by_contra hn
            exact (not_lt_of_ge ((hp r hr z v).2 hn).2) hv
          · by_contra hn
            exact (not_lt_of_ge ((hp' r hr z v).2 hn).2) hv)
        hc.1 hc'.1 t ⟨ht0,ht.2⟩ x x 0 (2*M*D) D (by simp)
        (fun r hr z v => hfd r hr (x+z,v)) (fun r hr z => hdiff r hr (x+z))
      have hm : max (2*M*D) D≤(2*M+1)*D := by apply max_le <;> nlinarith
      have hb : 0+C*max (2*M*D) D*t≤D/2 := by
        calc
          _ ≤ C*((2*M+1)*D)*T := by
            simpa only [zero_add] using mul_le_mul (mul_le_mul_of_nonneg_left hm hC) ht.2 ht.1 (by positivity)
          _ = (2*C*(2*M+1)*T)*(D/2) := by ring
          _ ≤ 1*(D/2) := mul_le_mul_of_nonneg_right hTC' (by positivity)
          _ = D/2 := one_mul _
      exact ⟨hh.1.trans hb,hh.2.trans hb⟩

theorem exists_contractive_picard_sequence {d : Datum} (hd : Admissible d) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∃ S : ℕ → Solution, S 0=datumBoundarySolution d ∧
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, FieldControl T L N (S n).E (S n).B) ∧
        (∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        ∀ n, ∀ t∈Icc 0 T, ∀ x,
          ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
          ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,h₀,hstep,hcontract⟩ := uniform_picard_control hd
  let Q := {s : Solution // ContDiff ℝ ∞ s.E ∧ ContDiff ℝ ∞ s.B}
  have hchoose (q : Q) : ∃ r : Q, PicardRegular d r.1 ∧ TransportFor r.1 q.1.E q.1.B := by
    obtain ⟨s,hs,hV⟩ := exists_picard_regular hd q.2.1 q.2.2
    exact ⟨⟨s,hs.smooth_E,hs.smooth_B⟩,hs,hV⟩
  choose step hs using hchoose
  let q₀ : Q := ⟨datumBoundarySolution d,
    hd.2.2.2.1.1.comp contDiff_snd,hd.2.2.2.2.1.1.comp contDiff_snd⟩
  let q : ℕ → Q := fun n => step^[n] q₀
  have hrec (n : ℕ) : q (n+1)=step (q n) := Function.iterate_succ_apply' step n q₀
  have hbound (n : ℕ) : FieldControl T L N (q n).1.E (q n).1.B := by
    induction n with
    | zero => exact h₀
    | succ n ih =>
      rw [hrec]
      exact (hstep _ _ (q n).2.1 (q n).2.2 ih _ (hs (q n)).1 (hs (q n)).2).2.2
  have hreg (n : ℕ) : PicardRegular d (q (n+1)).1 ∧ TransportFor (q (n+1)).1 (q n).1.E (q n).1.B ∧
      LocalParticleBound T A R P (q (n+1)).1.f ∧ PhaseParticleLip T M (q (n+1)).1.f := by
    rw [hrec]
    exact ⟨(hs (q n)).1,(hs (q n)).2,
      (hstep _ _ (q n).2.1 (q n).2.2 (hbound n) _ (hs (q n)).1 (hs (q n)).2).1,
      (hstep _ _ (q n).2.1 (q n).2.2 (hbound n) _ (hs (q n)).1 (hs (q n)).2).2.1⟩
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,fun n => (q n).1,rfl,
    fun n => (q n).2,hbound,hreg,?_⟩
  intro n
  induction n with
  | zero =>
    intro t ht x
    have h0 := (hbound 0).1 t ht x
    have h1 := (hbound 1).1 t ht x
    simp only [pow_zero,mul_one]
    constructor
    · exact (norm_sub_le _ _).trans (by linarith [h0.1,h1.1])
    · exact (norm_sub_le _ _).trans (by linarith [h0.2,h1.2])
  | succ n ih =>
    have hh := hcontract (q (n+1)).1.E (q (n+1)).1.B (q n).1.E (q n).1.B
      (q (n+1)).2.1 (q (n+1)).2.2 (q n).2.1 (q n).2.2 (hbound (n+1)) (hbound n)
      (q (n+1+1)).1 (q (n+1)).1 (hreg (n+1)).1 (hreg n).1 (hreg (n+1)).2.1 (hreg n).2.1
      (2*L*(1/2:ℝ)^n) (by positivity) ih
    intro t ht x
    convert hh t ht x using 1 <;> rw [pow_succ] <;> ring_nf

lemma exists_uniform_limit_geometric {X W : Type*} [NormedAddCommGroup W] [CompleteSpace W]
    {F : ℕ → X → W} {S : Set X} {C : ℝ}
    (h : ∀ n, ∀ x∈S, ‖F (n+1) x-F n x‖≤C*(1/2:ℝ)^n) :
    ∃ f : X → W, TendstoUniformlyOn F f atTop S := by
  let g : ℕ → X → W := fun n x => F (n+1) x-F n x
  have hu : Summable (fun n => C*(1/2:ℝ)^n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ)<1)).mul_left C
  have hh := tendstoUniformlyOn_tsum_nat hu (f:=g) h
  refine ⟨fun x => F 0 x+∑' n, g n x,?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x hx
  have he : (∑ i∈Finset.range n, g i x)=F n x-F 0 x := Finset.sum_range_sub (fun n => F n x) n
  specialize hn x hx
  rw [he,dist_eq_norm] at hn
  rw [dist_eq_norm]
  convert hn using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  abel

theorem exists_picard_field_limit_oai {d : Datum} (hd : Admissible d) :
    ∃ T A R P L N M : ℝ, 0<T ∧ T≤1 ∧ 0≤A ∧ 0<R ∧ 0<P ∧ 0<L ∧ 0<N ∧ 0≤M ∧
      ∃ (S : ℕ → Solution) (E B : Field), S 0=datumBoundarySolution d ∧
        (∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B) ∧
        (∀ n, FieldControl T L N (S n).E (S n).B) ∧
        (∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
          LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f) ∧
        (∀ n, ∀ t∈Icc 0 T, ∀ x,
          ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
          ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) ∧
        TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T} ∧
        TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T} ∧
        ContinuousOn E {p | p.1∈Icc 0 T} ∧ ContinuousOn B {p | p.1∈Icc 0 T} ∧
        FieldControl T L N E B := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,S,hS0,hsm,hc,hr,hg⟩ := exists_contractive_picard_sequence hd
  obtain ⟨E,hE⟩ := exists_uniform_limit_geometric (F:=fun n => (S n).E) (C:=2*L) (fun n (p : ℝ × Vec) (hp : p.1∈Icc 0 T) => (hg n p.1 hp p.2).1)
  obtain ⟨B,hB⟩ := exists_uniform_limit_geometric (F:=fun n => (S n).B) (C:=2*L) (fun n (p : ℝ × Vec) (hp : p.1∈Icc 0 T) => (hg n p.1 hp p.2).2)
  refine ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,S,E,B,hS0,hsm,hc,hr,hg,hE,hB,
    hE.continuousOn (Frequently.of_forall fun n => (hsm n).1.continuous.continuousOn),
    hB.continuousOn (Frequently.of_forall fun n => (hsm n).2.continuous.continuousOn),?_,?_⟩
  · intro t ht x
    exact ⟨le_of_tendsto (hE.tendsto_at (x:=(t,x)) ht).norm (Eventually.of_forall fun n => (hc n).1 t ht x |>.1),
      le_of_tendsto (hB.tendsto_at (x:=(t,x)) ht).norm (Eventually.of_forall fun n => (hc n).1 t ht x |>.2)⟩
  · intro t ht x y
    exact ⟨le_of_tendsto ((hE.tendsto_at (x:=(t,y)) ht).sub (hE.tendsto_at (x:=(t,x)) ht)).norm
      (Eventually.of_forall fun n => (hc n).2 t ht x y |>.1),
      le_of_tendsto ((hB.tendsto_at (x:=(t,y)) ht).sub (hB.tendsto_at (x:=(t,x)) ht)).norm
      (Eventually.of_forall fun n => (hc n).2 t ht x y |>.2)⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.exists_picard_field_limit_oai := @OAI.RVM.exists_picard_field_limit_oai
