-- Prove2me | solution 1 for OAI.RVM.classical_shifted_magnetic_physical_representation_before
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:17:15.573927+00:00
-- url     : https://prove2.me/submissions/c2c553ef-96c9-462f-a12a-2242c7327e8a

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Definitions.Def_OAIQ073V001
import Theorems.Thm_OAI_RVM_integrated_magneticMomentDensity_actual_before

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

lemma dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_smul_right (r : ℝ) (a b : Vec) : dot a (r • b) = r * dot a b := by
  rw [dot_comm, dot_smul_left, dot_comm b a]

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

lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma spatialPartial_mul {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y*g y) x i =
      f x*spatialPartial g x i+g x*spatialPartial f x i := by
  change fderiv ℝ (f*g) x (basis i) = _
  rw [fderiv_mul hf hg]
  rfl

lemma spatialPartial_sub {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y-g y) x i =
      spatialPartial f x i-spatialPartial g x i := by
  change fderiv ℝ (f-g) x (basis i) = _
  rw [fderiv_sub hf hg]
  rfl

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

lemma integral_mul_spatialPartial {F g : Vec → ℝ}
    (hF : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (i : Fin 3) :
    (∫ v, F v * spatialPartial g v i) =
      -(∫ v, spatialPartial F v i * g v) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hF.continuous.mul
      ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (basis i)).mul_left
  · exact (hF.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact fun x _ => hF.differentiable (by simp) x
  · exact fun x _ => hg.differentiable (by simp) x

lemma hasFDerivAt_integral_uniform_support
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    HasFDerivAt (fun x => ∫ v : Vec, F (x,v))
      ((∫ v : Vec, fderiv ℝ F (p,v)).comp (ContinuousLinearMap.inl ℝ H Vec)) p := by
  have h := hasFDerivAt_convolution_right_with_param
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (g := fun x v => F (x,v)) hU hK (fun x v hx hv => hzero x hx v hv)
    (locallyIntegrable_const (1 : ℝ)) hF (p,0) hp
  have hi : HasFDerivAt (fun x : H => (x,(0 : Vec)))
      (ContinuousLinearMap.inl ℝ H Vec) p := by
    convert (hasFDerivAt_id p).prodMk (hasFDerivAt_const (0 : Vec) p) using 1 <;> rfl
  have hc := h.comp p hi
  have hls : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W) 1 =
      ContinuousLinearMap.id ℝ W := by ext w; simp
  change HasFDerivAt (fun x => convolution (fun _ => (1 : ℝ)) (fun v => F (x,v))
    (ContinuousLinearMap.lsmul ℝ ℝ) volume 0)
    ((convolution (fun _ => (1 : ℝ)) (fun v => fderiv ℝ F (p,v))
      (ContinuousLinearMap.precompR (H × Vec) (ContinuousLinearMap.lsmul ℝ ℝ)) volume 0).comp
      (ContinuousLinearMap.inl ℝ H Vec)) p at hc
  simp only [convolution_def, zero_sub, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, hls,
    ContinuousLinearMap.id_comp] at hc
  have hn (x : H) : (∫ v : Vec, F (x,-v)) = ∫ v : Vec, F (x,v) :=
    integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  have hn' : (∫ v : Vec, fderiv ℝ F (p,-v)) = ∫ v : Vec, fderiv ℝ F (p,v) :=
    integral_neg_eq_self (fun v : Vec => fderiv ℝ F (p,v)) volume
  simpa only [hn, hn'] using hc

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

lemma compactSupport_param_fderiv
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    HasCompactSupport (fun v : Vec => fderiv ℝ F (p,v)) := by
  apply compactSupport_of_zero_off hK
  intro v hv
  have hn : U ×ˢ Kᶜ ∈ 𝓝 (p,v) :=
    (hU.prod hK.isClosed.isOpen_compl).mem_nhds ⟨hp,hv⟩
  have hz : F =ᶠ[𝓝 (p,v)] (fun _ => 0) := by
    filter_upwards [hn] with y hy
    exact hzero y.1 hy.1 y.2 hy.2
  simpa only [fderiv_const_apply] using hz.fderiv_eq (𝕜 := ℝ)

lemma integrable_param_fderiv
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    Integrable (fun v : Vec => fderiv ℝ F (p,v)) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (p,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_param_fderiv hU hK hp hzero)

lemma fderiv_integral_uniform_support_apply
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W} {p : H}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (b : H) :
    fderiv ℝ (fun x => ∫ v : Vec, F (x,v)) p b =
      ∫ v : Vec, fderiv ℝ F (p,v) (b,0) := by
  rw [(hasFDerivAt_integral_uniform_support hU hK hp hF hzero).fderiv]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using
    (ContinuousLinearMap.integral_apply (integrable_param_fderiv hU hK hp hF hzero) (b,0))

lemma contDiff_reassociate {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : (ℝ × Vec) × Vec => (z.1.1,z.1.2,z.2)) :=
  contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)

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

lemma deriv_time_slice {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {G : ℝ × Vec → W} {t : ℝ} {x : Vec} (hG : DifferentiableAt ℝ G (t,x)) :
    deriv (fun r => G (r,x)) t = fderiv ℝ G (t,x) (1,0) :=
  (hG.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

lemma spatialPartial_time_slice {G : ℝ × Vec → ℝ} {t : ℝ} {x : Vec}
    (hG : DifferentiableAt ℝ G (t,x)) (i : Fin 3) :
    spatialPartial (fun y => G (t,y)) x i = fderiv ℝ G (t,x) (0,basis i) := by
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    (hG.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).fderiv

lemma field_differentiableAt_positive {F : Field}
    (hF : ContDiffOn ℝ 1 F fieldHalfSpace) {t : ℝ} (ht : 0 < t) (x : Vec) :
    DifferentiableAt ℝ F (t,x) := by
  apply (hF.contDiffAt _).differentiableAt (by simp)
  apply Filter.mem_of_superset
    ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  intro z hz
  change 0 ≤ z.1
  exact le_of_lt hz

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

lemma integral_mul_divergence {F : Vec → Vec} {g : Vec → ℝ}
    (hF : ContDiff ℝ 1 F) (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) :
    (∫ x, g x * divergence F x) = -(∫ x, fderiv ℝ g x (F x)) := by
  have hFi (i : Fin 3) : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  have hI (i : Fin 3) : Integrable (fun x => g x * spatialPartial (fun y => F y i) x i) :=
    (hg.continuous.mul (((hFi i).continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport hc.mul_right
  have hJ (i : Fin 3) : Integrable (fun x => F x i * spatialPartial g x i) :=
    ((hFi i).continuous.mul ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (basis i)).mul_left
  simp only [divergence, Finset.mul_sum]
  conv_rhs => enter [1,2,x]; rw [clm_sum_basis]
  change (∫ x, ∑ i : Fin 3, g x * spatialPartial (fun y => F y i) x i) =
    -(∫ x, ∑ i : Fin 3, F x i * spatialPartial g x i)
  rw [integral_finsetSum _ (fun i _ => hI i), integral_finsetSum _ (fun i _ => hJ i)]
  simp_rw [mul_comm (g _) (spatialPartial _ _ _)]
  have he (i : Fin 3) : (∫ x, spatialPartial (fun y => F y i) x i * g x) =
      -(∫ x, F x i * spatialPartial g x i) := by
    have hh := integral_mul_spatialPartial (hFi i) hg hc i
    linarith
  simp only [he, Finset.sum_neg_distrib]

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

lemma continuous_divergence {F : Vec → Vec} (hF : ContDiff ℝ 1 F) :
    Continuous (divergence F) := by
  unfold divergence spatialPartial
  apply continuous_finsetSum
  intro i _
  have hi : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

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

lemma contDiff_coneArgument (T ε : ℝ) (x₀ : Vec) {k : ℕ∞} :
    ContDiff ℝ k (coneArgument T ε x₀) :=
  ((contDiff_const.sub contDiff_fst).pow 2 |>.sub
    ((contDiff_snd.sub contDiff_const).norm_sq ℝ)).div_const ε

lemma contDiff_coneCutoff (T ε : ℝ) (x₀ : Vec) {k : ℕ∞} :
    ContDiff ℝ k (coneCutoff T ε x₀) :=
  Real.smoothTransition.contDiff.comp (contDiff_coneArgument T ε x₀)

lemma deriv_transition_nonneg (u : ℝ) : 0 ≤ deriv Real.smoothTransition u :=
  Real.smoothTransition.monotone.deriv_nonneg

lemma deriv_transition_zero_neg {u : ℝ} (hu : u < 0) :
    deriv Real.smoothTransition u = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [gt_mem_nhds hu] with v hv
    exact Real.smoothTransition.zero_of_nonpos hv.le
  rw [he.deriv_eq,deriv_const]

lemma coneArgument_fderiv (T ε : ℝ) (x₀ : Vec) (p v : ℝ × Vec) :
    fderiv ℝ (coneArgument T ε x₀) p v =
      (-2*(T-p.1)*v.1 - 2*⟪p.2-x₀,v.2⟫)/ε := by
  have hd := (((hasFDerivAt_const T p).sub (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).pow 2).sub
    (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).sub (hasFDerivAt_const x₀ p)).norm_sq)
  have hh := hd.const_smul ε⁻¹
  have he : (fun y => ε⁻¹ • (((T-y.1)^2)-‖y.2-x₀‖^2)) = coneArgument T ε x₀ := by
    ext y
    simp [coneArgument,div_eq_mul_inv,mul_comm]
  change HasFDerivAt (fun y => ε⁻¹ • ((T-y.1)^2-‖y.2-x₀‖^2)) _ p at hh
  rw [he] at hh
  rw [hh.fderiv]
  simp [smul_eq_mul, div_eq_mul_inv, inner_sub_left]
  ring

lemma coneCutoff_fderiv (T ε : ℝ) (x₀ : Vec) (p v : ℝ × Vec) :
    fderiv ℝ (coneCutoff T ε x₀) p v =
      deriv Real.smoothTransition (coneArgument T ε x₀ p) *
        ((-2*(T-p.1)*v.1-2*⟪p.2-x₀,v.2⟫)/ε) := by
  have hθ := (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have hg := (contDiff_coneArgument T ε x₀ (k := 1)).differentiable (by simp)
  have hh := (hθ (coneArgument T ε x₀ p)).hasDerivAt.comp_hasFDerivAt p (hg p).hasFDerivAt
  change HasFDerivAt (coneCutoff T ε x₀) _ p at hh
  rw [hh.fderiv]
  simpa [smul_eq_mul] using congrArg
    (fun c : ℝ => deriv Real.smoothTransition (coneArgument T ε x₀ p) * c)
    (coneArgument_fderiv T ε x₀ p v)

lemma coneArgument_neg_outside {T ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc 0 T)
    {x x₀ : Vec} (hx : x ∉ closedBall x₀ T) : coneArgument T ε x₀ (t,x) < 0 := by
  have hr : T < ‖x-x₀‖ := by simpa [mem_closedBall,dist_eq_norm] using hx
  dsimp [coneArgument]
  apply div_neg_of_neg_of_pos _ hε
  have hR : 0 ≤ T-t := sub_nonneg.mpr ht.2
  have he : T-t < ‖x-x₀‖ := lt_of_le_of_lt (sub_le_self _ ht.1) hr
  nlinarith [sq_lt_sq₀ hR (norm_nonneg (x-x₀)) |>.mpr he]

lemma coneCutoff_zero_outside {T ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc 0 T)
    {x x₀ : Vec} (hx : x ∉ closedBall x₀ T) : coneCutoff T ε x₀ (t,x) = 0 :=
  Real.smoothTransition.zero_of_nonpos (coneArgument_neg_outside hε ht hx).le

lemma deriv_transition_zero_gt_one {u : ℝ} (hu : 1 < u) :
    deriv Real.smoothTransition u = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 u] fun _ => (1 : ℝ) := by
    filter_upwards [lt_mem_nhds hu] with v hv
    exact Real.smoothTransition.one_of_one_le hv.le
  rw [he.deriv_eq,deriv_const]

lemma continuous_radialConeWeight (R ε : ℝ) : Continuous (radialConeWeight R ε) := by
  have hθ := (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by simp)
  exact ((continuous_const.mul continuous_id).div_const ε).mul
    (hθ.comp ((continuous_const.sub (continuous_id.pow 2)).div_const ε))

lemma radialConeWeight_nonneg {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) (R : ℝ) :
    0 ≤ radialConeWeight R ε r :=
  mul_nonneg (by positivity) (deriv_transition_nonneg _)

lemma deriv_radial_cone (R ε r : ℝ) :
    HasDerivAt (fun z => Real.smoothTransition ((R^2-z^2)/ε))
      (-radialConeWeight R ε r) r := by
  have hθ := (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)
  have hh := (hθ _).hasDerivAt.comp r
    (((hasDerivAt_const r (R^2)).sub ((hasDerivAt_id r).pow 2)).div_const ε)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [radialConeWeight,Pi.sub_apply,id_eq,Pi.pow_apply,
    Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,zero_sub]
  ring

lemma radialConeWeight_mass {R : ℝ} (hR : 0 ≤ R) (ε : ℝ) :
    (∫ r in 0..R, radialConeWeight R ε r) = Real.smoothTransition (R^2/ε) := by
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR
    (Real.smoothTransition.continuous.comp ((continuous_const.sub (continuous_id.pow 2)).div_const ε)).continuousOn
    (fun r _ => deriv_radial_cone R ε r)
    ((continuous_radialConeWeight R ε).neg.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_neg] at hf
  simp only [Function.comp_def,Pi.sub_apply,Pi.pow_apply,id_eq,sub_self,zero_div,Real.smoothTransition.zero,zero_sub,zero_pow (by norm_num : 2 ≠ 0),sub_zero] at hf
  linarith

lemma radialConeWeight_local {R ε δ r : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hεδ : ε < R*δ) (hr : r ∈ Icc 0 R) (hfar : δ ≤ R-r) :
    radialConeWeight R ε r = 0 := by
  have ha : 1 < (R^2-r^2)/ε := by
    apply (lt_div_iff₀ hε).mpr
    have hh : ε < R*(R-r) := hεδ.trans_le (mul_le_mul_of_nonneg_left hfar hR.le)
    nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
  simp [radialConeWeight,deriv_transition_zero_gt_one ha]

lemma radialConeWeight_tendsto {R : ℝ} (hR : 0 < R) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Icc 0 R)) :
    Filter.Tendsto (fun ε => ∫ r in 0..R, radialConeWeight R ε r * F r)
      (𝓝[>] (0 : ℝ)) (𝓝 (F R)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ,hδ,hclose⟩ := (Metric.continuousWithinAt_iff.mp (hF R ⟨hR.le,le_rfl⟩))
    (η/2) (by positivity)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < min (R^2) (R*δ) := by
    apply Filter.eventually_of_mem (Ioo_mem_nhdsGT (by positivity : 0 < min (R^2) (R*δ)))
    intro ε hε
    exact hε
  filter_upwards [hev] with ε hε
  have hw : ContinuousOn (radialConeWeight R ε) (Icc 0 R) := (continuous_radialConeWeight R ε).continuousOn
  have hwI := (continuous_radialConeWeight R ε).intervalIntegrable (μ := volume) 0 R
  have hFI : IntervalIntegrable (fun r => radialConeWeight R ε r * F r) volume 0 R :=
    (hw.mul hF).intervalIntegrable_of_Icc (μ := volume) hR.le
  have hm : (∫ r in 0..R, radialConeWeight R ε r) = 1 := by
    rw [radialConeWeight_mass hR.le]
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ hε.1).mpr (by simpa using (lt_of_lt_of_le hε.2 (min_le_left _ _)).le)
  have heq : (∫ r in 0..R, radialConeWeight R ε r * F r) - F R =
      ∫ r in 0..R, radialConeWeight R ε r * (F r-F R) := by
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hFI (hwI.mul_const _),intervalIntegral.integral_mul_const,hm,one_mul]
  have hb : ‖∫ r in 0..R, radialConeWeight R ε r * (F r-F R)‖ ≤ η/2 := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le hR.le
      (g := fun r => radialConeWeight R ε r * (η/2)) (μ := volume)
      (ae_of_all _ (fun r hr => show ‖radialConeWeight R ε r * (F r-F R)‖ ≤
          radialConeWeight R ε r * (η/2) from by
        have hr' : r ∈ Icc 0 R := ⟨hr.1.le,hr.2⟩
        have hp := radialConeWeight_nonneg hε.1 hr'.1 R
        by_cases hd : δ ≤ R-r
        · rw [radialConeWeight_local hR hε.1 (lt_of_lt_of_le hε.2 (min_le_right _ _)) hr' hd]
          simp
        · have hd' : dist r R < δ := by
            rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hr.2)]
            linarith
          have hc := hclose hr' hd'
          rw [Real.dist_eq] at hc
          simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg hp]
          exact mul_le_mul_of_nonneg_left hc.le hp)) (hwI.mul_const _)
    simpa only [intervalIntegral.integral_mul_const,hm,one_mul] using hh
  rw [dist_eq_norm,heq]
  exact hb.trans_lt (by linarith)

lemma sphere_norm (n : Sphere) : ‖n.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using n.2

lemma radialConeWeight_zero_above {R ε r : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hr : R < r) :
    radialConeWeight R ε r = 0 := by
  have ha : (R^2-r^2)/ε < 0 := by
    apply div_neg_of_neg_of_pos _ hε
    nlinarith [sq_lt_sq₀ hR (hR.trans hr.le) |>.mpr hr]
  simp [radialConeWeight,deriv_transition_zero_neg ha]

lemma radialConeWeight_integral_Ioi {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (F : ℝ → ℝ) :
    (∫ r in Ioi 0, radialConeWeight R ε r * F r) =
      ∫ r in 0..R, radialConeWeight R ε r * F r := by
  rw [intervalIntegral.integral_of_le hR]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro r hr
  have hrr : R < r := by
    by_contra hn
    exact hr.2 ⟨hr.1,not_lt.mp hn⟩
  rw [radialConeWeight_zero_above hR hε hrr,zero_mul]

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

section
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

lemma continuous_dot : Continuous (fun p : Vec × Vec => dot p.1 p.2) := by
  simp only [dot_eq_inner]
  exact continuous_fst.inner continuous_snd

lemma contDiff_ballCutoff (R ε : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (ballCutoff R ε) := by
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (contDiff_id.norm_sq ℝ)).div_const ε)

lemma ballCutoff_fderiv (R ε : ℝ) (x h : Vec) :
    fderiv ℝ (ballCutoff R ε) x h =
      -(2/ε)*deriv Real.smoothTransition ((R^2-‖x‖^2)/ε)*dot x h := by
  have hθ := (Real.smoothTransition.contDiff (n:=1)).differentiable (by simp)
  have hi := ((hasFDerivAt_const (R^2) x).sub ((hasFDerivAt_id x).norm_sq)).const_smul ε⁻¹
  have harg : (fun y : Vec => ε⁻¹ • (R^2-‖y‖^2)) =
      (fun y : Vec => (R^2-‖y‖^2)/ε) := by
    ext y
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
  change HasFDerivAt (fun y : Vec => ε⁻¹ • (R^2-‖y‖^2)) _ x at hi
  rw [harg] at hi
  have hh := (hθ _).hasDerivAt.comp_hasFDerivAt x hi
  change HasFDerivAt (ballCutoff R ε) _ x at hh
  rw [hh.fderiv]
  simp [smul_eq_mul,div_eq_mul_inv,← dot_eq_inner]
  ring

lemma ballCutoff_zero {R ε : ℝ} (hR : 0≤R) (hε : 0<ε) {x : Vec}
    (hx : x ∉ closedBall (0:Vec) R) : ballCutoff R ε x=0 := by
  have hh := coneCutoff_zero_outside hε (show (0:ℝ) ∈ Icc 0 R from ⟨le_rfl,hR⟩) hx
  simpa only [coneCutoff,coneArgument,ballCutoff,sub_zero] using hh

lemma ballCutoff_compact {R ε : ℝ} (hR : 0≤R) (hε : 0<ε) :
    HasCompactSupport (ballCutoff R ε) :=
  compactSupport_of_zero_off (isCompact_closedBall (0:Vec) R) (fun _ hx => ballCutoff_zero hR hε hx)

lemma ballCutoff_tendsto {R : ℝ} {x : Vec} (hR : 0<R) :
    Tendsto (fun ε => ballCutoff R ε x) (𝓝[>] (0:ℝ))
      (𝓝 ((ball (0:Vec) R).indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hxr : ‖x‖<R
  · rw [indicator_of_mem (by simpa only [mem_ball_zero_iff] using hxr)]
    have hsq : 0<R^2-‖x‖^2 := by nlinarith [norm_nonneg x]
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hsq] with ε hε
    symm
    apply Real.smoothTransition.one_of_one_le
    exact (le_div_iff₀ hε.1).mpr (by simpa using hε.2.le)
  · have hrx : R≤‖x‖ := le_of_not_gt hxr
    rw [indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hxr)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    symm
    apply Real.smoothTransition.zero_of_nonpos
    apply div_nonpos_of_nonpos_of_nonneg _ hε.le
    nlinarith [norm_nonneg x]

lemma ballCutoff_integral_tendsto {R : ℝ} (hR : 0<R) {F : Vec → ℝ}
    (hF : Continuous F) :
    Tendsto (fun ε => ∫ x, ballCutoff R ε x * F x) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x in ball (0:Vec) R, F x)) := by
  have hh : Tendsto (fun ε => ∫ x, ballCutoff R ε x * F x)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x, (ball (0:Vec) R).indicator F x)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      ((closedBall (0:Vec) R).indicator (fun x => ‖F x‖))
    · exact Eventually.of_forall (fun ε => ((contDiff_ballCutoff R ε (k:=1)).continuous.mul hF).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      filter_upwards [] with x
      by_cases hx : x ∈ closedBall (0:Vec) R
      · rw [indicator_of_mem hx,norm_mul,ballCutoff,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one _)
      · rw [indicator_of_notMem hx,ballCutoff_zero hR.le hε hx,zero_mul,norm_zero]
    · exact (integrable_indicator_iff measurableSet_closedBall).mpr
        (hF.norm.continuousOn.integrableOn_compact (isCompact_closedBall (0:Vec) R))
    · filter_upwards [] with x
      have ht := (ballCutoff_tendsto (x:=x) hR).mul_const (F x)
      convert ht using 1
      all_goals try with_reducible_and_instances rfl
      by_cases hx : x ∈ ball (0:Vec) R <;> simp [hx]
  simpa only [integral_indicator measurableSet_ball] using hh

lemma ballCutoff_divergence {R ε : ℝ} (hR : 0≤R) (hε : 0<ε)
    {F : Vec → Vec} (hF : ContDiff ℝ 1 F) :
    (∫ x, ballCutoff R ε x * divergence F x) =
      ∫ x, (2/ε)*deriv Real.smoothTransition ((R^2-‖x‖^2)/ε)*dot x (F x) := by
  rw [integral_mul_divergence hF (contDiff_ballCutoff R ε) (ballCutoff_compact hR hε),← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ballCutoff_fderiv]
  ring

lemma ballShell_polar {R ε : ℝ} (hR : 0≤R) (hε : 0<ε)
    {F : Vec → Vec} (hF : ContDiff ℝ 1 F) :
    (∫ x : Vec, (2/ε)*deriv Real.smoothTransition ((R^2-‖x‖^2)/ε)*dot x (F x)) =
      ∫ r in 0..R, radialConeWeight R ε r *
        (∫ n : Sphere, r^2*dot n.1 (F (r • n.1)) ∂sphereMeasure) := by
  let G : Vec → ℝ := fun x => (2/ε)*deriv Real.smoothTransition ((R^2-‖x‖^2)/ε)*dot x (F x)
  have hG : Continuous G := by
    exact (continuous_const.mul (((Real.smoothTransition.contDiff (n:=2)).continuous_deriv
      (by simp)).comp ((continuous_const.sub (continuous_id.norm.pow 2)).div_const ε))).mul
      (continuous_dot.comp (continuous_id.prodMk hF.continuous))
  have hK : HasCompactSupport G := by
    apply compactSupport_of_zero_off (isCompact_closedBall (0:Vec) R)
    intro x hx
    have hr : R<‖x‖ := by simpa only [mem_closedBall_zero_iff,not_le] using hx
    have harg : (R^2-‖x‖^2)/ε<0 := by
      apply div_neg_of_neg_of_pos _ hε
      nlinarith [norm_nonneg x]
    simp [G,deriv_transition_zero_neg harg]
  have he (r : ℝ) (n : Sphere) : r^2 • G (r • n.1) =
      radialConeWeight R ε r * (r^2*dot n.1 (F (r • n.1))) := by
    have hn : ‖r • n.1‖^2=r^2 := by simp [norm_smul,Real.norm_eq_abs,sq_abs]
    simp only [G,hn,radialConeWeight,dot_smul_left,smul_eq_mul]
    ring
  change (∫ x : Vec, G x) = _
  rw [integral_polar (hG.integrable_of_hasCompactSupport hK)]
  simp_rw [he,radialConeWeight_integral_Ioi hR hε]
  have hc : Continuous (fun p : ℝ × Sphere => radialConeWeight R ε p.1 *
      (p.1^2*dot p.2.1 (F (p.1 • p.2.1)))) :=
    ((continuous_radialConeWeight R ε).comp continuous_fst).mul
      ((continuous_fst.pow 2).mul (continuous_dot.comp
        ((continuous_subtype_val.comp continuous_snd).prodMk
          (hF.continuous.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))))))
  have hi : Integrable (fun p : ℝ × Sphere => radialConeWeight R ε p.1 *
      (p.1^2*dot p.2.1 (F (p.1 • p.2.1))))
      ((volume.restrict (uIoc 0 R)).prod sphereMeasure) := by
    let : IsFiniteMeasure sphereMeasure := inferInstance
    let : IsFiniteMeasureOnCompacts ((volume : Measure ℝ).prod sphereMeasure) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    rw [uIoc_of_le hR,Measure.restrict_prod_eq_prod_univ]
    exact (hc.continuousOn.integrableOn_compact
      (μ := (volume : Measure ℝ).prod sphereMeasure)
      (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono_left Ioc_subset_Icc_self)
  rw [← intervalIntegral_integral_swap hi]
  apply intervalIntegral.integral_congr
  intro r _
  exact integral_const_mul _ _

lemma divergence_ball {R : ℝ} (hR : 0<R) {F : Vec → Vec} (hF : ContDiff ℝ 1 F) :
    (∫ x in ball (0:Vec) R, divergence F x) =
      ∫ n : Sphere, R^2*dot n.1 (F (R • n.1)) ∂sphereMeasure := by
  have hc : Continuous (fun p : ℝ × Sphere => p.1^2*dot p.2.1 (F (p.1 • p.2.1))) :=
    (continuous_fst.pow 2).mul (continuous_dot.comp
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (hF.continuous.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)))))
  have hh : Continuous (fun r => ∫ n : Sphere, r^2*dot n.1 (F (r • n.1)) ∂sphereMeasure) := by
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hc.continuousOn
    intro r n _ hn
    exact (hn (mem_univ n)).elim
  have hleft := ballCutoff_integral_tendsto hR (continuous_divergence hF)
  have hright := radialConeWeight_tendsto hR hh.continuousOn
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [ballCutoff_divergence hR.le hε hF,ballShell_polar hR.le hε hF]
end RVM
end

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

lemma integral_ball_polar {g : Vec → ℝ} (hg : Continuous g) {R : ℝ} (hR : 0≤R) :
    (∫ x in ball (0:Vec) R, g x) =
      ∫ r in 0..R, r^2*sphereSum g (r,0) := by
  have hi : Integrable ((ball (0:Vec) R).indicator g) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((hg.continuousOn.integrableOn_compact (isCompact_closedBall (0:Vec) R)).mono_set ball_subset_closedBall)
  rw [← integral_indicator measurableSet_ball,integral_polar hi]
  have he (n : Sphere) : (∫ r in Ioi (0:ℝ), r^2 • (ball (0:Vec) R).indicator g (r • n.1)) =
      ∫ r in 0..R, r^2*g (r • n.1) := by
    have hf : ∀ r ∈ Ioi (0:ℝ), r^2 • (ball (0:Vec) R).indicator g (r • n.1) =
        (Ioo (0:ℝ) R).indicator (fun r => r^2*g (r • n.1)) r := by
      intro r hr
      change 0 < r at hr
      have hn : ‖r • n.1‖=r := by simp [norm_smul,abs_of_pos hr]
      by_cases hh : r<R
      · rw [indicator_of_mem (show r • n.1 ∈ ball (0:Vec) R by simpa [mem_ball_zero_iff,hn] using hh),
          indicator_of_mem (show r ∈ Ioo (0:ℝ) R from ⟨hr,hh⟩),smul_eq_mul]
      · rw [indicator_of_notMem (show r • n.1 ∉ ball (0:Vec) R by simpa [mem_ball_zero_iff,hn] using hh),
          indicator_of_notMem (show r ∉ Ioo (0:ℝ) R from fun h => hh h.2),smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hf,setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self,← integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le hR]
  simp_rw [he]
  have hc : Continuous (fun p : ℝ × Sphere => p.1^2*g (p.1 • p.2.1)) :=
    (continuous_fst.pow 2).mul (hg.comp (continuous_fst.smul
      (continuous_subtype_val.comp continuous_snd)))
  have hi2 : Integrable (fun p : ℝ × Sphere => p.1^2*g (p.1 • p.2.1))
      ((volume.restrict (uIoc 0 R)).prod sphereMeasure) := by
    let : IsFiniteMeasure sphereMeasure := inferInstance
    let : IsFiniteMeasureOnCompacts ((volume : Measure ℝ).prod sphereMeasure) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    rw [uIoc_of_le hR,Measure.restrict_prod_eq_prod_univ]
    exact (hc.continuousOn.integrableOn_compact
      (μ := (volume : Measure ℝ).prod sphereMeasure)
      (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono_left Ioc_subset_Icc_self)
  rw [← intervalIntegral_integral_swap hi2]
  apply intervalIntegral.integral_congr
  intro r _
  simp only [sphereSum,zero_add]
  exact integral_const_mul _ _

lemma contDiff_gradient {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (gradient g) := by
  exact (InnerProductSpace.toDual ℝ Vec).symm.contDiff.comp
    (contDiff_infty_iff_fderiv.mp hg).2

lemma continuous_laplace {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) : Continuous (laplace g) :=
  continuous_divergence ((contDiff_gradient hg).of_le (by simp))

lemma sphereSum_flux {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) {R : ℝ} (hR : 0<R) :
    R^2 * deriv (fun r => sphereSum g (r,0)) R =
      ∫ r in 0..R, r^2*sphereSum (laplace g) (r,0) := by
  rw [(sphereSum_radial_deriv (hg.of_le (by simp)) 0 R).deriv]
  have hdiv := divergence_ball hR ((contDiff_gradient hg).of_le (by simp))
  change (∫ x in ball (0:Vec) R, laplace g x) = _ at hdiv
  rw [integral_ball_polar (continuous_laplace hg) hR.le] at hdiv
  rw [hdiv,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with n
  simp only [zero_add,dot_eq_inner,inner_gradient_right,conj_trivial]
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

lemma continuous_sphereSum {g : Vec → ℝ} (hg : Continuous g) : Continuous (sphereSum g) := by
  apply continuous_integral_sphere (F:=fun p : (ℝ × Vec) × Vec => g (p.1.2+p.1.1 • p.2))
  exact hg.comp ((continuous_snd.comp continuous_fst).add
    ((continuous_fst.comp continuous_fst).smul continuous_snd))

lemma sphereSum_radial_darboux_zero {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0<R) :
    2*deriv (fun r => sphereSum g (r,0)) R +
      R*deriv (deriv (fun r => sphereSum g (r,0))) R =
      R*sphereSum (laplace g) (R,0) := by
  let F : ℝ → ℝ := fun r => sphereSum g (r,0)
  have hF : ContDiff ℝ ∞ F := (contDiff_sphereSum hg).comp (contDiff_id.prodMk contDiff_const)
  have hFd : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  let H : ℝ → ℝ := fun r => r^2*sphereSum (laplace g) (r,0)
  have hh : Continuous H := (continuous_id.pow 2).mul
    ((continuous_sphereSum (continuous_laplace hg)).comp (continuous_id.prodMk continuous_const))
  have he : (fun r => r^2*deriv F r) =ᶠ[𝓝 R] (fun r => ∫ s in 0..r, H s) := by
    filter_upwards [Ioi_mem_nhds hR] with r hr
    exact sphereSum_flux hg hr
  have hl := ((hasDerivAt_id R).pow 2).mul
    (hFd.differentiable (by simp) R).hasDerivAt
  have hr := intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable 0 R)
    hh.stronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt
  have h := hl.unique (hr.congr_of_eventuallyEq he)
  dsimp only [H] at h
  norm_num at h
  change 2*deriv F R+R*deriv (deriv F) R=R*sphereSum (laplace g) (R,0)
  nlinarith

lemma sphereSum_radial_wave_zero {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    {R : ℝ} (hR : 0<R) :
    deriv (deriv (fun r => r*sphereSum g (r,0))) R =
      R*sphereSum (laplace g) (R,0) := by
  let F : ℝ → ℝ := fun r => sphereSum g (r,0)
  have hF : ContDiff ℝ ∞ F := (contDiff_sphereSum hg).comp (contDiff_id.prodMk contDiff_const)
  have hFd : ContDiff ℝ ∞ (deriv F) := (contDiff_infty_iff_deriv.mp hF).2
  have hd : deriv (fun r => r*F r) = fun r => F r+r*deriv F r := by
    funext r
    change deriv (id * F) r = _
    convert ((hasDerivAt_id r).mul (hF.differentiable (by simp) r).hasDerivAt).deriv using 1; simp
  change deriv (deriv (fun r => r*F r)) R = _
  rw [hd]
  change deriv (F + id * deriv F) R = _
  rw [((hF.differentiable (by simp) R).hasDerivAt.add
    ((hasDerivAt_id R).mul (hFd.differentiable (by simp) R).hasDerivAt)).deriv]
  have h := sphereSum_radial_darboux_zero hg hR
  change 2*deriv F R+R*deriv (deriv F) R = _ at h
  dsimp only [id]
  nlinarith

lemma sphereSum_spatialPartial {g : Vec → ℝ} (hg : ContDiff ℝ 1 g)
    (r : ℝ) (x : Vec) (i : Fin 3) :
    spatialPartial (fun y => sphereSum g (r,y)) x i =
      sphereSum (fun y => spatialPartial g y i) (r,x) := by
  let F : Vec × Vec → ℝ := fun p => g (p.1+r • p.2)
  have hF : ContDiff ℝ 1 F := hg.comp (contDiff_fst.add (contDiff_snd.const_smul r))
  have hd := (hasFDerivAt_integral_sphere hF x).fderiv
  have hDa (n : Sphere) : ((fderiv ℝ F (x,n.1)).comp
      (ContinuousLinearMap.inl ℝ Vec Vec)) (basis i) =
      fderiv ℝ g (x+r • n.1) (basis i) := by
    have hi : HasFDerivAt (fun p : Vec × Vec => p.1+r • p.2)
        ((ContinuousLinearMap.fst ℝ Vec Vec)+r • ContinuousLinearMap.snd ℝ Vec Vec) (x,n.1) :=
      (hasFDerivAt_fst).add ((hasFDerivAt_snd).const_smul r)
    have he := ((hg.differentiable (by simp)) (x+r • n.1)).hasFDerivAt.comp (x,n.1) hi
    change HasFDerivAt F _ (x,n.1) at he
    rw [he.fderiv]
    simp
  have hc : Continuous (fun n : Sphere => (fderiv ℝ F (x,n.1)).comp
      (ContinuousLinearMap.inl ℝ Vec Vec)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_subtype_val)).clm_comp continuous_const
  unfold spatialPartial sphereSum
  change (fderiv ℝ (fun y => ∫ n : Sphere, F (y,n.1) ∂sphereMeasure) x) (basis i) = _
  rw [hd,ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)) (basis i)]
  apply integral_congr_ae
  exact ae_of_all _ hDa

lemma contDiff_spatialPartial {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x => spatialPartial g x i) :=
  ((contDiff_infty_iff_fderiv.mp hg).2).clm_apply contDiff_const

lemma gradient_apply (g : Vec → ℝ) (x : Vec) (i : Fin 3) :
    gradient g x i = spatialPartial g x i := by
  have h := inner_gradient_left (𝕜:=ℝ) (f:=g) (x:=x) (y:=basis i)
  rw [← dot_eq_inner] at h
  simpa [dot,basis,spatialPartial] using h

lemma laplace_eq_sum (g : Vec → ℝ) (x : Vec) :
    laplace g x = ∑ i : Fin 3, spatialPartial (fun y => spatialPartial g y i) x i := by
  simp only [laplace,divergence,gradient_apply]

lemma sphereSum_sum {ι : Type*} (s : Finset ι) {G : ι → Vec → ℝ}
    (hG : ∀ i ∈ s, Continuous (G i)) (p : ℝ × Vec) :
    sphereSum (fun x => ∑ i ∈ s, G i x) p = ∑ i ∈ s, sphereSum (G i) p := by
  unfold sphereSum
  apply integral_finsetSum
  intro i hi
  have h : Continuous (fun n : Sphere => G i (p.2+p.1 • n.1)) :=
    (hG i hi).comp (continuous_const.add (continuous_subtype_val.const_smul p.1))
  exact h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma sphereSum_spatial_laplace {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (r : ℝ) (x : Vec) :
    laplace (fun y => sphereSum g (r,y)) x = sphereSum (laplace g) (r,x) := by
  rw [laplace_eq_sum]
  have he : ∀ i, (fun y => spatialPartial (fun z => sphereSum g (r,z)) y i) =
      (fun y => sphereSum (fun z => spatialPartial g z i) (r,y)) := by
    intro i
    funext y
    exact sphereSum_spatialPartial (hg.of_le (by simp)) r y i
  calc
    _ = ∑ i : Fin 3, spatialPartial (fun y => sphereSum (fun z => spatialPartial g z i) (r,y)) x i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [he i]
    _ = ∑ i : Fin 3, sphereSum (fun y => spatialPartial (fun z => spatialPartial g z i) y i) (r,x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact sphereSum_spatialPartial ((contDiff_spatialPartial hg i).of_le (by simp)) r x i
    _ = sphereSum (laplace g) (r,x) := by
      rw [← sphereSum_sum Finset.univ (fun i _ =>
        (contDiff_spatialPartial (contDiff_spatialPartial hg i) i).continuous)]
      congr 1
      funext y
      exact (laplace_eq_sum g y).symm

lemma spatialPartial_translate {g : Vec → ℝ} (hg : Differentiable ℝ g)
    (c x : Vec) (i : Fin 3) :
    spatialPartial (fun y => g (c+y)) x i = spatialPartial g (c+x) i := by
  have h := (hg (c+x)).hasFDerivAt.comp x
    ((hasFDerivAt_const c x).add (hasFDerivAt_id x))
  change HasFDerivAt (fun y => g (c+y)) _ x at h
  unfold spatialPartial
  rw [h.fderiv]
  simp

lemma laplace_translate {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (c x : Vec) :
    laplace (fun y => g (c+y)) x = laplace g (c+x) := by
  rw [laplace_eq_sum,laplace_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => spatialPartial (fun z => g (c+z)) y i) =
      fun y => spatialPartial g (c+y) i := by
    funext y
    exact spatialPartial_translate (hg.differentiable (by simp)) c y i
  rw [he]
  exact spatialPartial_translate ((contDiff_spatialPartial hg i).differentiable (by simp)) c x i

lemma sphereSum_radial_wave {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    (x : Vec) {R : ℝ} (hR : 0<R) :
    deriv (deriv (fun r => r*sphereSum g (r,x))) R =
      R*sphereSum (laplace g) (R,x) := by
  have hs (r : ℝ) : sphereSum (fun y => g (x+y)) (r,0) = sphereSum g (r,x) := by
    simp only [sphereSum,zero_add]
  have hl (r : ℝ) : sphereSum (laplace (fun y => g (x+y))) (r,0) =
      sphereSum (laplace g) (r,x) := by
    simp only [sphereSum,laplace_translate hg,zero_add]
  have hx : ContDiff ℝ ∞ (fun y => g (x+y)) := hg.comp (contDiff_const.add contDiff_id)
  convert sphereSum_radial_wave_zero hx hR using 1
  · congr 2
    funext r
    rw [hs]
  · rw [hl]

lemma spatialPartial_const_mul {g : Vec → ℝ} (hg : Differentiable ℝ g)
    (c : ℝ) (x : Vec) (i : Fin 3) :
    spatialPartial (fun y => c*g y) x i = c*spatialPartial g x i := by
  unfold spatialPartial
  rw [((hg x).hasFDerivAt.const_mul c).fderiv]
  simp

lemma laplace_const_mul {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (c : ℝ) (x : Vec) :
    laplace (fun y => c*g y) x = c*laplace g x := by
  simp only [laplace_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => spatialPartial (fun z => c*g z) y i) =
      fun y => c*spatialPartial g y i := by
    funext y
    exact spatialPartial_const_mul (hg.differentiable (by simp)) c y i
  rw [he,spatialPartial_const_mul ((contDiff_spatialPartial hg i).differentiable (by simp))]

lemma sphere_area : sphereMeasure.real univ = 4*Real.pi := by
  rw [sphereMeasure,Measure.toSphere_real_apply_univ]
  simp only [Vec,finrank_euclideanSpace,Measure.real,EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  norm_num
  ring

lemma contDiff_waveK {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (waveK g) :=
  contDiff_const.mul (contDiff_fst.mul (contDiff_sphereSum hg))

lemma waveK_zero (g : Vec → ℝ) (x : Vec) : waveK g (0,x)=0 := by simp [waveK]

lemma waveK_initial_velocity {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) :
    deriv (fun t => waveK g (t,x)) 0 = g x := by
  have hd := ((hasDerivAt_id (0:ℝ)).mul
    (sphereSum_radial_deriv (hg.of_le (by simp)) x 0)).const_mul ((4*Real.pi)⁻¹)
  change HasDerivAt (fun t => waveK g (t,x)) _ 0 at hd
  rw [hd.deriv]
  simp only [id_eq,one_mul,zero_mul,add_zero,sphereSum,zero_smul,add_zero,integral_const,
    smul_eq_mul,sphere_area]
  field_simp

lemma waveK_equation_pos {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec)
    {t : ℝ} (ht : 0<t) :
    deriv (deriv (fun r => waveK g (r,x))) t = laplace (fun y => waveK g (t,y)) x := by
  have hF : ContDiff ℝ ∞ (fun r => r*sphereSum g (r,x)) :=
    contDiff_id.mul ((contDiff_sphereSum hg).comp (contDiff_id.prodMk contDiff_const))
  have he : deriv (fun r => waveK g (r,x)) =
      fun r => (4*Real.pi)⁻¹ * deriv (fun r => r*sphereSum g (r,x)) r := by
    funext r
    exact ((hF.differentiable (by simp) r).hasDerivAt.const_mul _).deriv
  rw [he]
  rw [(((contDiff_infty_iff_deriv.mp hF).2.differentiable (by simp) t).hasDerivAt.const_mul _).deriv]
  rw [sphereSum_radial_wave hg x ht]
  have hS : ContDiff ℝ ∞ (fun y => sphereSum g (t,y)) :=
    (contDiff_sphereSum hg).comp (contDiff_const.prodMk contDiff_id)
  change _ = laplace (fun y => (4*Real.pi)⁻¹ * (t*sphereSum g (t,y))) x
  rw [laplace_const_mul (contDiff_const.mul hS),laplace_const_mul hS,sphereSum_spatial_laplace hg]

lemma waveK_equation {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec)
    {t : ℝ} (ht : 0≤t) :
    deriv (deriv (fun r => waveK g (r,x))) t = laplace (fun y => waveK g (t,y)) x := by
  have hF : ContDiff ℝ ∞ (fun r => waveK g (r,x)) :=
    (contDiff_waveK hg).comp (contDiff_id.prodMk contDiff_const)
  have hc : Continuous (deriv (deriv (fun r => waveK g (r,x)))) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hF).2).2.continuous
  have hr : Continuous (fun t => laplace (fun y => waveK g (t,y)) x) := by
    have he : (fun t => laplace (fun y => waveK g (t,y)) x) =
        fun t => (4*Real.pi)⁻¹ * (t*sphereSum (laplace g) (t,x)) := by
      funext t
      have hS : ContDiff ℝ ∞ (fun y => sphereSum g (t,y)) :=
        (contDiff_sphereSum hg).comp (contDiff_const.prodMk contDiff_id)
      change laplace (fun y => (4*Real.pi)⁻¹ * (t*sphereSum g (t,y))) x = _
      rw [laplace_const_mul (contDiff_const.mul hS),laplace_const_mul hS,sphereSum_spatial_laplace hg]
    rw [he]
    exact (continuous_id.mul ((continuous_sphereSum (continuous_laplace hg)).comp
      (continuous_id.prodMk continuous_const))).const_mul _
  have he : EqOn (deriv (deriv (fun r => waveK g (r,x))))
      (fun t => laplace (fun y => waveK g (t,y)) x) (Ioi 0) :=
    fun _ ht => waveK_equation_pos hg x ht
  exact he.closure hc hr (by simpa only [closure_Ioi,mem_Ici] using ht)
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


lemma hasFDerivAt_intervalIntegral
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ 1 F) (a b : ℝ) (p : H) :
    HasFDerivAt (fun x => ∫ s in a..b, F (x,s))
      (∫ s in a..b, (fderiv ℝ F (p,s)).comp (ContinuousLinearMap.inl ℝ H ℝ)) p := by
  let D : H × ℝ → H →L[ℝ] W := fun z =>
    (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H ℝ)
  have hD : Continuous D := (hF.continuous_fderiv (by simp)).clm_comp continuous_const
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod isCompact_uIcc).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s:=closedBall p 1) (bound:=fun _ => C) (F':=fun x s => D (x,s))
    (closedBall_mem_nhds p (by norm_num))
  · exact Eventually.of_forall (fun x => (hF.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    intro x hx
    exact hC _ ⟨(x,s),⟨hx,uIoc_subset_uIcc hs⟩,rfl⟩
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun s x _ => (hF.differentiable (by simp) (x,s)).hasFDerivAt.comp x
      (by convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const s x) using 1 <;> rfl))

lemma contDiff_intervalIntegral_nat
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    (k : ℕ) : ∀ {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W}, ContDiff ℝ ∞ F → ∀ a b,
      ContDiff ℝ k (fun x => ∫ s in a..b, F (x,s)) := by
  induction k with
  | zero =>
    intro W _ _ _ F hF a b
    have hd : Differentiable ℝ (fun x => ∫ s in a..b, F (x,s)) :=
      fun x => (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) a b x).differentiableAt
    exact contDiff_zero.mpr hd.continuous
  | succ k ih =>
    intro W _ _ _ F hF a b
    let D : H × ℝ → H →L[ℝ] W := fun z =>
      (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ H ℝ)
    have hD : ContDiff ℝ ∞ D :=
      (contDiff_infty_iff_fderiv.mp hF).2.clm_comp contDiff_const
    have he : fderiv ℝ (fun x => ∫ s in a..b, F (x,s)) =
        (fun x => ∫ s in a..b, D (x,s)) := by
      funext x
      exact (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) a b x).fderiv
    rw [show (↑(k+1) : ℕ∞ω) = ↑k+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) a b x).differentiableAt,?_,?_⟩
    · simp
    · rw [he]
      exact ih hD a b

lemma contDiff_intervalIntegral
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ s in a..b, F (x,s)) := by
  rw [contDiff_infty]
  intro k
  exact contDiff_intervalIntegral_nat k hF a b

lemma paramPrimitive_scale {H W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : H × ℝ → W) (p : ℝ × H) :
    paramPrimitive F p = p.1 • ∫ u in (0:ℝ)..1, F (p.2,p.1*u) := by
  simpa [paramPrimitive] using (intervalIntegral.smul_integral_comp_mul_left (fun s => F (p.2,s)) p.1
    (a:=0) (b:=1)).symm

lemma contDiff_paramPrimitive
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (paramPrimitive F) := by
  have he : paramPrimitive F = fun p => p.1 • ∫ u in (0:ℝ)..1, F (p.2,p.1*u) :=
    funext (paramPrimitive_scale F)
  rw [he]
  apply contDiff_fst.smul
  apply contDiff_intervalIntegral (F:=fun z : (ℝ × H) × ℝ => F (z.1.2,z.1.1*z.2))
  exact hF.comp ((contDiff_snd.comp contDiff_fst).prodMk
    ((contDiff_fst.comp contDiff_fst).mul contDiff_snd))

lemma paramPrimitive_fderiv_apply
    {H : Type} {W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × ℝ → W} (hF : ContDiff ℝ ∞ F) (t : ℝ) (p : H) (dt : ℝ) (dp : H) :
    fderiv ℝ (paramPrimitive F) (t,p) (dt,dp) =
      dt • F (p,t) + (∫ s in 0..t, (fderiv ℝ F (p,s)).comp
        (ContinuousLinearMap.inl ℝ H ℝ)) dp := by
  have hJ : Differentiable ℝ (paramPrimitive F) := (contDiff_paramPrimitive hF).differentiable (by simp)
  have htime := (hJ (t,p)).hasFDerivAt.comp t
    ((hasFDerivAt_id (𝕜:=ℝ) t).prodMk (hasFDerivAt_const (𝕜:=ℝ) p t))
  have hc : Continuous (fun s => F (p,s)) := hF.continuous.comp (continuous_const.prodMk continuous_id)
  have hFTC := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have ht : fderiv ℝ (paramPrimitive F) (t,p) (1,0) = F (p,t) := by
    exact htime.hasDerivAt.unique hFTC
  have hparam := (hJ (t,p)).hasFDerivAt.comp p
    ((hasFDerivAt_const (𝕜:=ℝ) t p).prodMk (hasFDerivAt_id (𝕜:=ℝ) p))
  have hp := hparam.unique (hasFDerivAt_intervalIntegral (hF.of_le (by simp)) 0 t p)
  have hp' := congrArg (fun L : H →L[ℝ] W => L dp) hp
  change fderiv ℝ (paramPrimitive F) (t,p) (0,dp) = _ at hp'
  rw [show (dt,dp) = dt • (1,0) + (0,dp) by simp,map_add,map_smul,ht,hp']

lemma contDiff_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e : H) : ContDiff ℝ ∞ (dirD F e) :=
  (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

lemma dirD_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e v x : H) :
    dirD (dirD F e) v x = fderiv ℝ (fderiv ℝ F) x v e := by
  unfold dirD
  rw [fderiv_clm_apply ((contDiff_infty_iff_fderiv.mp hF).2.differentiable (by simp) x)
    (differentiableAt_const e)]
  simp

lemma dirD_comm {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e v x : H) :
    dirD (dirD F e) v x = dirD (dirD F v) e x := by
  rw [dirD_dirD hF,dirD_dirD hF]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq v e

lemma deriv_slice_eq_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × H → W}
    (hF : Differentiable ℝ F) (t : ℝ) (x : H) :
    deriv (fun r => F (r,x)) t = dirD F (1,0) (t,x) := by
  exact ((hF (t,x)).hasFDerivAt.comp t
    ((hasFDerivAt_id (𝕜:=ℝ) t).prodMk (hasFDerivAt_const (𝕜:=ℝ) x t))).hasDerivAt.deriv

lemma deriv_deriv_slice_eq_dirD {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × H → W}
    (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : H) :
    deriv (deriv (fun r => F (r,x))) t = dirD (dirD F (1,0)) (1,0) (t,x) := by
  have he : deriv (fun r => F (r,x)) = fun r => dirD F (1,0) (r,x) := by
    funext r
    exact deriv_slice_eq_dirD (hF.differentiable (by simp)) r x
  rw [he]
  exact deriv_slice_eq_dirD ((contDiff_dirD hF (1,0)).differentiable (by simp)) t x

lemma dirD_prod_left {H G W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : H × G → W} (hF : Differentiable ℝ F) (e x : H) (y : G) :
    dirD (fun z => F (z,y)) e x = dirD F (e,0) (x,y) := by
  have h := (hF (x,y)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (𝕜:=ℝ) y x))
  change HasFDerivAt (fun z => F (z,y)) _ x at h
  unfold dirD
  rw [h.fderiv]
  simp

lemma contDiff_volterra {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    {F : (ℝ × H) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (volterra F) :=
  (contDiff_paramPrimitive hF).comp (contDiff_fst.prodMk contDiff_id)

lemma dirD_volterra {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    {F : (ℝ × H) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (e p : ℝ × H) :
    dirD (volterra F) e p = e.1*F (p,p.1) + volterra (dirD F (e,0)) p := by
  have h := ((contDiff_paramPrimitive hF).differentiable (by simp) (p.1,p)).hasFDerivAt.comp (f:=fun z : ℝ × H => (z.1,z)) p
    (((hasFDerivAt_id (𝕜:=ℝ) p).fst).prodMk (hasFDerivAt_id (𝕜:=ℝ) p))
  change HasFDerivAt (volterra F) _ p at h
  unfold dirD
  rw [h.fderiv]
  change fderiv ℝ (paramPrimitive F) (p.1,p) (e.1,e) = _
  rw [paramPrimitive_fderiv_apply hF]
  congr 1
  have hc : Continuous (fun s => (fderiv ℝ F (p,s)).comp
      (ContinuousLinearMap.inl ℝ (ℝ × H) ℝ)) :=
    ((hF.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_comp continuous_const
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 p.1)]
  rfl

lemma laplace_slice_eq_dirD {F : ℝ × Vec → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : Vec) :
    laplace (fun y => F (t,y)) x =
      ∑ i : Fin 3, dirD (dirD F (0,basis i)) (0,basis i) (t,x) := by
  rw [laplace_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun y => spatialPartial (fun z => F (t,z)) y i) =
      fun y => dirD F (0,basis i) (t,y) := by
    funext y
    exact spatialPartial_time_slice (hF.differentiable (by simp) (t,y)) i
  rw [he]
  exact spatialPartial_time_slice ((contDiff_dirD hF (0,basis i)).differentiable (by simp) (t,x)) i

lemma laplace_volterra {F : (ℝ × Vec) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : Vec) :
    laplace (fun y => volterra F (t,y)) x =
      ∫ s in 0..t, laplace (fun y => F ((t,y),s)) x := by
  rw [laplace_slice_eq_dirD (contDiff_volterra hF)]
  have he (i : Fin 3) : dirD (volterra F) (0,basis i) =
      volterra (dirD F ((0,basis i),0)) := by
    funext p
    simpa only [zero_mul,zero_add] using dirD_volterra hF (0,basis i) p
  simp_rw [he]
  have he' (i : Fin 3) : dirD (volterra (dirD F ((0,basis i),0))) (0,basis i) (t,x) =
      volterra (dirD (dirD F ((0,basis i),0)) ((0,basis i),0)) (t,x) := by
    simpa only [zero_mul,zero_add] using
      dirD_volterra (contDiff_dirD hF ((0,basis i),0)) (0,basis i) (t,x)
  simp_rw [he']
  have hc (i : Fin 3) : Continuous (fun s => dirD (dirD F ((0,basis i),0))
      ((0,basis i),0) ((t,x),s)) :=
    (contDiff_dirD (contDiff_dirD hF _) _).continuous.comp (continuous_const.prodMk continuous_id)
  rw [show (∑ i : Fin 3, volterra (dirD (dirD F ((0,basis i),0)) ((0,basis i),0)) (t,x)) =
      ∫ s in 0..t, ∑ i : Fin 3, dirD (dirD F ((0,basis i),0)) ((0,basis i),0) ((t,x),s) by
        exact (intervalIntegral.integral_finsetSum (fun i _ => (hc i).intervalIntegrable 0 t)).symm]
  apply intervalIntegral.integral_congr
  intro s _
  have hFs : ContDiff ℝ ∞ (fun p => F (p,s)) := hF.comp (contDiff_id.prodMk contDiff_const)
  change _ = laplace (fun y => F ((t,y),s)) x
  rw [laplace_slice_eq_dirD hFs]
  apply Finset.sum_congr rfl
  intro i _
  have hf := hF.differentiable (by simp)
  have hdir : dirD (fun z => F (z,s)) (0,basis i) =
      fun p => dirD F ((0,basis i),0) (p,s) := by
    funext p
    exact dirD_prod_left hf _ p s
  rw [hdir,dirD_prod_left ((contDiff_dirD hF _).differentiable (by simp))]

lemma contDiff_sourceWaveKernel {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (sourceWaveKernel ρ) := by
  have hF : ContDiff ℝ ∞ (fun z : ((ℝ × Vec) × ℝ) × Vec =>
      ρ (z.1.2,z.1.1.2+(z.1.1.1-z.1.2) • z.2)) := by
    apply hρ.comp
    apply (contDiff_snd.comp contDiff_fst).prodMk
    apply (contDiff_snd.comp (contDiff_fst.comp contDiff_fst)).add
    exact ((contDiff_fst.comp (contDiff_fst.comp contDiff_fst)).sub
      (contDiff_snd.comp contDiff_fst)).smul contDiff_snd
  exact contDiff_const.mul (((contDiff_fst.comp contDiff_fst).sub contDiff_snd).mul
    (contDiff_integral_sphere hF))

lemma contDiff_sourceWave {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (sourceWave ρ) := contDiff_volterra (contDiff_sourceWaveKernel hρ)

lemma sourceWaveKernel_boundary (ρ : ℝ × Vec → ℝ) (p : ℝ × Vec) :
    sourceWaveKernel ρ (p,p.1) = 0 := by
  simp [sourceWaveKernel,waveK]

lemma sourceWave_timeDerivative {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    dirD (sourceWave ρ) (1,0) = volterra (dirD (sourceWaveKernel ρ) ((1,0),0)) := by
  funext p
  simpa only [sourceWave,one_mul,sourceWaveKernel_boundary,zero_add] using
    dirD_volterra (contDiff_sourceWaveKernel hρ) (1,0) p

lemma sourceWaveKernel_timeDerivative {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (t s : ℝ) (x : Vec) :
    dirD (sourceWaveKernel ρ) ((1,0),0) ((t,x),s) =
      deriv (fun r => waveK (fun y => ρ (s,y)) (r,x)) (t-s) := by
  have hK := contDiff_sourceWaveKernel hρ
  rw [← dirD_prod_left (hK.differentiable (by simp)) (1,0) (t,x) s]
  have hs : ContDiff ℝ ∞ (fun p => sourceWaveKernel ρ (p,s)) :=
    hK.comp (contDiff_id.prodMk contDiff_const)
  rw [← deriv_slice_eq_dirD (hs.differentiable (by simp))]
  change deriv (fun r => waveK (fun y => ρ (s,y)) (r-s,x)) t = _
  exact deriv_comp_sub_const (fun r => waveK (fun y => ρ (s,y)) (r,x)) s t

lemma sourceWaveKernel_secondTime {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (t s : ℝ) (x : Vec) :
    dirD (dirD (sourceWaveKernel ρ) ((1,0),0)) ((1,0),0) ((t,x),s) =
      deriv (deriv (fun r => waveK (fun y => ρ (s,y)) (r,x))) (t-s) := by
  have hK := contDiff_dirD (contDiff_sourceWaveKernel hρ) ((1,0),0)
  rw [← dirD_prod_left (hK.differentiable (by simp)) (1,0) (t,x) s]
  have hs : ContDiff ℝ ∞ (fun p => dirD (sourceWaveKernel ρ) ((1,0),0) (p,s)) :=
    hK.comp (contDiff_id.prodMk contDiff_const)
  rw [← deriv_slice_eq_dirD (hs.differentiable (by simp))]
  have he : (fun r => dirD (sourceWaveKernel ρ) ((1,0),0) ((r,x),s)) =
      fun r => deriv (fun u => waveK (fun y => ρ (s,y)) (u,x)) (r-s) := by
    funext r
    exact sourceWaveKernel_timeDerivative hρ r s x
  rw [he,deriv_comp_sub_const]

lemma sourceWave_initial_value (ρ : ℝ × Vec → ℝ) (x : Vec) :
    sourceWave ρ (0,x) = 0 := by simp [sourceWave,volterra]

lemma sourceWave_initial_velocity {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) (x : Vec) :
    deriv (fun t => sourceWave ρ (t,x)) 0 = 0 := by
  rw [deriv_slice_eq_dirD ((contDiff_sourceWave hρ).differentiable (by simp)),sourceWave_timeDerivative hρ]
  simp [volterra]

lemma sourceWave_equation {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) (x : Vec)
    {t : ℝ} (ht : 0≤t) :
    deriv (deriv (fun r => sourceWave ρ (r,x))) t =
      laplace (fun y => sourceWave ρ (t,y)) x + ρ (t,x) := by
  rw [deriv_deriv_slice_eq_dirD (contDiff_sourceWave hρ),sourceWave_timeDerivative hρ,
    dirD_volterra (contDiff_dirD (contDiff_sourceWaveKernel hρ) ((1,0),0)),one_mul,
    sourceWaveKernel_timeDerivative hρ t t x,sub_self]
  have hρt : ContDiff ℝ ∞ (fun y => ρ (t,y)) := hρ.comp (contDiff_const.prodMk contDiff_id)
  rw [waveK_initial_velocity hρt]
  change _ = laplace (fun y => volterra (sourceWaveKernel ρ) (t,y)) x + _
  rw [laplace_volterra (contDiff_sourceWaveKernel hρ),add_comm]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hst : s≤t := (by simpa only [uIcc_of_le ht] using hs : s ∈ Icc 0 t).2
  dsimp only
  rw [sourceWaveKernel_secondTime hρ]
  have hρs : ContDiff ℝ ∞ (fun y => ρ (s,y)) := hρ.comp (contDiff_const.prodMk contDiff_id)
  exact waveK_equation hρs x (sub_nonneg.mpr hst)

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

lemma spatialPartial_sum {ι : Type*} (s : Finset ι) {f : ι → Vec → ℝ}
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (x : Vec) (j : Fin 3) :
    spatialPartial (fun y => ∑ i ∈ s, f i y) x j = ∑ i ∈ s, spatialPartial (f i) x j := by
  unfold spatialPartial
  rw [fderiv_fun_sum (fun i hi => hf i hi x)]
  simp

lemma spatialPartial_comm {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) (i j : Fin 3) :
    spatialPartial (fun y => spatialPartial g y i) x j =
      spatialPartial (fun y => spatialPartial g y j) x i :=
  dirD_comm hg (basis i) (basis j) x

lemma curl_curl_component {F : Vec → Vec} (hF : ContDiff ℝ ∞ F) (x : Vec) (i : Fin 3) :
    curl (curl F) x i = spatialPartial (divergence F) x i-laplace (fun y => F y i) x := by
  have hc (i j : Fin 3) : DifferentiableAt ℝ (fun y => spatialPartial (fun z => F z i) y j) x :=
    (contDiff_spatialPartial (contDiff_component hF i) j).differentiable (by simp) x
  have hsum : spatialPartial (divergence F) x i =
      ∑ j : Fin 3, spatialPartial (fun y => spatialPartial (fun z => F z j) y j) x i := by
    apply spatialPartial_sum
    intro j _
    exact (contDiff_spatialPartial (contDiff_component hF j) j).differentiable (by simp)
  rw [hsum,laplace_eq_sum]
  fin_cases i <;> simp [curl, Fin.sum_univ_succ]
  all_goals simp only [spatialPartial_sub (hc _ _) (hc _ _)]
  · rw [spatialPartial_comm (contDiff_component hF 1) x 0 1,
      spatialPartial_comm (contDiff_component hF 2) x 0 2]
    ring
  · rw [spatialPartial_comm (contDiff_component hF 2) x 1 2,
      spatialPartial_comm (contDiff_component hF 0) x 1 0]
    ring
  · rw [spatialPartial_comm (contDiff_component hF 0) x 2 0,
      spatialPartial_comm (contDiff_component hF 1) x 2 1]
    ring
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace


lemma deriv_moving_local_energy {e : ℝ × Vec → ℝ} {S : ℝ × Vec → Vec}
    {U : Set ℝ} (hU : IsOpen U)
    (he : ContDiffOn ℝ 1 e (U ×ˢ (univ : Set Vec)))
    (hSg : ContDiffOn ℝ 1 S (U ×ˢ (univ : Set Vec)))
    (hcons : ∀ t ∈ U, ∀ x, deriv (fun r => e (r,x)) t + divergence (fun y => S (t,y)) x = 0)
    {g : ℝ × Vec → ℝ} {K : Set Vec} (hK : IsCompact K)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ (univ : Set Vec)))
    (hz : ∀ r ∈ U, ∀ x ∉ K, g (r,x)=0)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun r => ∫ x : Vec, g (r,x) * e (r,x))
      (∫ x : Vec, fderiv ℝ g (t,x) (1,0) * e (t,x) +
        fderiv ℝ g (t,x) (0,S (t,x))) t := by
  have hE := he
  have hF : ContDiffOn ℝ 1 (fun p => g p * e p)
      (U ×ˢ (univ : Set Vec)) := hg.mul hE
  have hzF : ∀ r ∈ U, ∀ x ∉ K, g (r,x)*e (r,x)=0 := by
    intro r hr x hx
    rw [hz r hr x hx,zero_mul]
  have hd := hasFDerivAt_integral_uniform_support hU hK ht hF hzF
  have hi := fderiv_integral_uniform_support_apply hU hK ht hF hzF (1:ℝ)
  have hgg : ContDiff ℝ 1 (fun x => g (t,x)) := by
    apply ContDiffOn.comp_contDiff hg (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hS : ContDiff ℝ 1 (fun x => S (t,x)) := by
    apply ContDiffOn.comp_contDiff hSg
      (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hEc : Continuous (fun x => e (t,x)) := by
    apply hE.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hgD : Continuous (fun x => fderiv ℝ g (t,x)) := by
    apply (hg.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) (by simp)).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hDc : HasCompactSupport (fun x => fderiv ℝ g (t,x)) :=
    compactSupport_param_fderiv hU hK ht hz
  have hgC : HasCompactSupport (fun x => g (t,x)) :=
    compactSupport_of_zero_off hK (hz t ht)
  have hgDapply (v : ℝ × Vec) : HasCompactSupport (fun x => fderiv ℝ g (t,x) v) := by
    apply compactSupport_of_zero_off hDc
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_apply]
  have hIt : Integrable (fun x => fderiv ℝ g (t,x) (1,0) * e (t,x)) :=
    ((hgD.clm_apply continuous_const).mul hEc).integrable_of_hasCompactSupport
      (hgDapply (1,0)).mul_right
  have hIa : Integrable (fun x => g (t,x) * divergence (fun y => S (t,y)) x) :=
    (hgg.continuous.mul (continuous_divergence hS)).integrable_of_hasCompactSupport hgC.mul_right
  have hIs : Integrable (fun x => fderiv ℝ (fun y => g (t,y)) x (S (t,x))) :=
    ((hgg.continuous_fderiv (by simp)).clm_apply hS.continuous).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hgC.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx,zero_apply]))
  have heq : ∀ x : Vec,
      fderiv ℝ (fun p => g p * e p) (t,x) (1,0) =
        fderiv ℝ g (t,x) (1,0) * e (t,x) -
          g (t,x) * divergence (fun y => S (t,y)) x := by
    intro x
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hg' := (hg.contDiffAt hn).differentiableAt (by simp)
    have hE' := (hE.contDiffAt hn).differentiableAt (by simp)
    change fderiv ℝ (g * e) (t,x) (1,0) = _
    rw [fderiv_mul hg' hE',add_apply,
      smul_apply,smul_apply,
      smul_eq_mul,smul_eq_mul,← deriv_time_slice hE']
    have hl := hcons t ht x
    rw [show deriv (fun r => e (r,x)) t =
      -divergence (fun y => S (t,y)) x by linarith]
    ring
  have hxder (x v : Vec) : fderiv ℝ (fun y => g (t,y)) x v = fderiv ℝ g (t,x) (0,v) := by
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hh := ((hg.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    change HasFDerivAt (fun y => g (t,y)) _ x at hh
    rw [hh.fderiv]
    simp
  have hh : deriv (fun r => ∫ x : Vec, g (r,x) * e (r,x)) t =
      ∫ x : Vec, fderiv ℝ g (t,x) (1,0) * e (t,x) +
        fderiv ℝ g (t,x) (0,S (t,x)) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g (r,x) * e (r,x)) t 1 = _
    rw [hi]
    simp only [heq]
    rw [integral_sub hIt hIa,integral_mul_divergence hS hgg hgC,sub_neg_eq_add]
    simp_rw [← hxder]
    exact (integral_add hIt hIs).symm
  exact hh ▸ hd.differentiableAt.hasDerivAt
lemma cone_energy_integrand_nonpos {R ε t : ℝ} {e : ℝ} {S : Vec}
    (hε : 0 < ε) (ht : t ≤ R) (he : 0 ≤ e) (hS : ‖S‖ ≤ e) (x x₀ : Vec) :
    fderiv ℝ (coneCutoff R ε x₀) (t,x) (1,0) * e +
      fderiv ℝ (coneCutoff R ε x₀) (t,x) (0,S) ≤ 0 := by
  rw [coneCutoff_fderiv,coneCutoff_fderiv]
  simp only [inner_zero_right,mul_zero,mul_one,sub_zero,zero_sub]
  have heq : deriv Real.smoothTransition (coneArgument R ε x₀ (t,x)) *
      ((-2*(R-t))/ε) * e + deriv Real.smoothTransition (coneArgument R ε x₀ (t,x)) *
      (-(2*⟪x-x₀,S⟫)/ε) =
      -((2/ε)*deriv Real.smoothTransition (coneArgument R ε x₀ (t,x)) *
      ((R-t)*e+⟪x-x₀,S⟫)) := by ring
  rw [heq]
  apply neg_nonpos.mpr
  by_cases hr : ‖x-x₀‖ ≤ R-t
  · apply mul_nonneg (mul_nonneg (by positivity) (deriv_transition_nonneg _))
    have hc := real_inner_le_norm (-(x-x₀)) S
    simp only [inner_neg_left,norm_neg] at hc
    nlinarith [mul_le_mul_of_nonneg_left hS (norm_nonneg (x-x₀)),
      mul_le_mul_of_nonneg_right hr he]
  · have hn : coneArgument R ε x₀ (t,x) < 0 := by
      dsimp [coneArgument]
      apply div_neg_of_neg_of_pos _ hε
      have hR : 0 ≤ R-t := sub_nonneg.mpr ht
      push Not at hr
      nlinarith [sq_lt_sq₀ hR (norm_nonneg (x-x₀)) |>.mpr hr]
    simp [deriv_transition_zero_neg hn]

lemma causal_local_energy_vanishes {e : ℝ × Vec → ℝ} {S : ℝ × Vec → Vec} {T : ℝ}
    (hT : 0 ≤ T)
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hS : ContDiffOn ℝ 1 S (Ioi 0 ×ˢ (univ : Set Vec)))
    (hec : ContinuousOn e (Icc 0 T ×ˢ (univ : Set Vec)))
    (he0 : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ e (t,x))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x, ‖S (t,x)‖ ≤ e (t,x))
    (hcons : ∀ t ∈ Ioo 0 T, ∀ x,
      deriv (fun r => e (r,x)) t + divergence (fun y => S (t,y)) x = 0)
    (hinit : ∀ x, e (0,x)=0) (x₀ : Vec) : e (T,x₀)=0 := by
  let R := T+1
  let g := coneCutoff R 1 x₀
  let G : ℝ → ℝ := fun t => ∫ x : Vec, g (t,x)*e (t,x)
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 R := by intro t ht; exact ⟨ht.1,by dsimp [R]; linarith [ht.2]⟩
  have hgc : ContDiff ℝ 1 g := contDiff_coneCutoff R 1 x₀
  have hgz : ∀ t ∈ Icc 0 T, ∀ x ∉ closedBall x₀ R, g (t,x)=0 := by
    intro t ht x hx
    exact coneCutoff_zero_outside (by norm_num) (hsub ht) hx
  have hGc : ContinuousOn G (Icc 0 T) := by
    apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ R)
      (hgc.continuous.continuousOn.mul hec)
    intro t ht x hx
    change g (t,x)*e (t,x)=0
    rw [hgz t ht x hx,zero_mul]
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) :=
    deriv_moving_local_energy isOpen_Ioo
      (he.mono (by intro p hp; exact ⟨hp.1.1,hp.2⟩))
      (hS.mono (by intro p hp; exact ⟨hp.1.1,hp.2⟩)) hcons
      (isCompact_closedBall x₀ R) hgc.contDiffOn
      (fun r hr x hx => hgz r ⟨hr.1.le,hr.2.le⟩ x hx) ht
  have hanti : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hGc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hder t ht).deriv]
      apply integral_nonpos
      intro x
      exact cone_energy_integrand_nonpos (by norm_num) (hsub ⟨ht.1.le,ht.2.le⟩).2
        (he0 t ⟨ht.1.le,ht.2.le⟩ x) (hflux t ht x) x x₀
  have hG0 : G 0 = 0 := by simp [G,hinit]
  have hGn : ∀ x, 0 ≤ g (T,x)*e (T,x) := fun x =>
    mul_nonneg (Real.smoothTransition.nonneg _) (he0 T ⟨hT,le_rfl⟩ x)
  have hGT : G T = 0 := le_antisymm
    (by simpa only [hG0] using hanti ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩ hT)
    (integral_nonneg hGn)
  have hTc : Continuous (fun x => g (T,x)*e (T,x)) :=
    (hgc.continuous.comp (continuous_const.prodMk continuous_id)).mul
      (hec.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨⟨hT,le_rfl⟩,mem_univ x⟩))
  have hI : Integrable (fun x => g (T,x)*e (T,x)) :=
    hTc.integrable_of_hasCompactSupport ((compactSupport_of_zero_off (isCompact_closedBall x₀ R)
      (hgz T ⟨hT,le_rfl⟩)).mul_right)
  have hae := (integral_eq_zero_iff_of_nonneg hGn hI).mp hGT
  have hpoint := congrFun (Measure.eq_of_ae_eq (μ:=volume) hae hTc continuous_const) x₀
  have hval : g (T,x₀)=1 := by simp [g,coneCutoff,coneArgument,R]
  simpa only [hval,one_mul,Pi.zero_apply] using hpoint

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

lemma integrable_conePotential {ρ : ℝ × Vec → ℝ} (hρ : Continuous ρ)
    {t : ℝ} (_ht : 0≤t) (x : Vec) :
    IntegrableOn (fun z : Vec => ρ (t-‖z‖,x+z)/‖z‖) (ball 0 t) := by
  have hc : Continuous (fun z : Vec => ρ (t-‖z‖,x+z)) :=
    hρ.comp ((continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id))
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0:Vec) t).image hc).isBounded.exists_norm_le
  apply integrableOn_ball_of_norm_le_rpow (by simp)
    (α:=1) (C:=C) (by simp)
  · apply ae_restrict_of_forall_mem measurableSet_ball
    intro z hz
    have hh := hC _ ⟨z,ball_subset_closedBall hz,rfl⟩
    rw [norm_div,norm_norm,Real.rpow_neg_one,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (norm_nonneg z))
  · exact (hc.measurable.div continuous_norm.measurable).aestronglyMeasurable

lemma sourceWave_ball {ρ : ℝ × Vec → ℝ} (hρ : Continuous ρ)
    {t : ℝ} (ht : 0≤t) (x : Vec) :
    sourceWave ρ (t,x) = (4*Real.pi)⁻¹ *
      ∫ z in ball (0:Vec) t, ρ (t-‖z‖,x+z)/‖z‖ := by
  have hi := (integrable_conePotential hρ ht x).integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball,integral_polar hi]
  have he (n : Sphere) :
      (∫ r in Ioi (0:ℝ), r^2 • (ball (0:Vec) t).indicator
        (fun z => ρ (t-‖z‖,x+z)/‖z‖) (r • n.1)) =
      ∫ r in 0..t, r*ρ (t-r,x+r • n.1) := by
    have hf : ∀ r ∈ Ioi (0:ℝ), r^2 • (ball (0:Vec) t).indicator
        (fun z => ρ (t-‖z‖,x+z)/‖z‖) (r • n.1) =
        (Ioo (0:ℝ) t).indicator (fun r => r*ρ (t-r,x+r • n.1)) r := by
      intro r hr
      change 0 < r at hr
      have hn : ‖r • n.1‖=r := by simp [norm_smul,abs_of_pos hr]
      by_cases hh : r<t
      · rw [indicator_of_mem (show r • n.1 ∈ ball (0:Vec) t by simpa [mem_ball_zero_iff,hn] using hh),
          indicator_of_mem (show r ∈ Ioo (0:ℝ) t from ⟨hr,hh⟩),smul_eq_mul,hn]
        field_simp
      · rw [indicator_of_notMem (show r • n.1 ∉ ball (0:Vec) t by simpa [mem_ball_zero_iff,hn] using hh),
          indicator_of_notMem (show r ∉ Ioo (0:ℝ) t from fun h => hh h.2),smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hf,setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self,← integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le ht]
  simp_rw [he]
  have hc : Continuous (fun p : ℝ × Sphere => p.1*ρ (t-p.1,x+p.1 • p.2.1)) :=
    continuous_fst.mul (hρ.comp ((continuous_const.sub continuous_fst).prodMk
      (continuous_const.add (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)))))
  have hi2 : Integrable (fun p : ℝ × Sphere => p.1*ρ (t-p.1,x+p.1 • p.2.1))
      ((volume.restrict (uIoc 0 t)).prod sphereMeasure) := by
    let : IsFiniteMeasure sphereMeasure := inferInstance
    let : IsFiniteMeasureOnCompacts ((volume : Measure ℝ).prod sphereMeasure) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    rw [uIoc_of_le ht,Measure.restrict_prod_eq_prod_univ]
    exact (hc.continuousOn.integrableOn_compact
      (μ := (volume : Measure ℝ).prod sphereMeasure)
      (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono_left Ioc_subset_Icc_self)
  rw [← intervalIntegral_integral_swap hi2]
  have hs : sourceWave ρ (t,x) = (4*Real.pi)⁻¹ *
      ∫ s in 0..t, (t-s)*(∫ n : Sphere, ρ (s,x+(t-s) • n.1) ∂sphereMeasure) := by
    simp only [sourceWave,volterra,sourceWaveKernel,waveK,sphereSum]
    exact intervalIntegral.integral_const_mul _ _
  rw [hs]
  congr 1
  calc
    _ = ∫ r in 0..t, r*(∫ n : Sphere, ρ (t-r,x+r • n.1) ∂sphereMeasure) := by
      have hh := intervalIntegral.integral_comp_sub_left
        (fun r => r*(∫ n : Sphere, ρ (t-r,x+r • n.1) ∂sphereMeasure)) (a:=0) (b:=t) t
      simpa only [sub_self,sub_zero,sub_sub_cancel] using hh
    _ = _ := intervalIntegral.integral_congr (fun r _ => (integral_const_mul _ _).symm)

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

lemma dirD_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : Differentiable ℝ F) (p e : H) (i : Fin 3) :
    dirD (fun z => F z i) e p = dirD F e p i := by
  have h := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp p (hF p).hasFDerivAt
  change HasFDerivAt (fun z => F z i) _ p at h
  unfold dirD
  rw [h.fderiv]
  rfl

lemma divergence_smul {g : Vec → ℝ} {F : Vec → Vec} {x : Vec}
    (hg : DifferentiableAt ℝ g x) (hF : DifferentiableAt ℝ F x) :
    divergence (fun y => g y • F y) x =
      dot (gradient g x) (F x) + g x * divergence F x := by
  have hc (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF
  have hm (i : Fin 3) : spatialPartial (fun y => g y * F y i) x i =
      g x * spatialPartial (fun y => F y i) x i + F x i * spatialPartial g x i :=
    spatialPartial_mul hg (hc i) i
  simp only [divergence,PiLp.smul_apply,smul_eq_mul,hm,dot,
    gradient_apply,Finset.sum_add_distrib,Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma waveGradient_apply (u : ℝ × Vec → ℝ) (p : ℝ × Vec) (i : Fin 3) :
    waveGradient u p i = dirD u (0,basis i) p := rfl

lemma contDiff_waveGradient {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (waveGradient u) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_dirD hu (0,basis i)

lemma waveGradient_slice {u : ℝ × Vec → ℝ} (hu : Differentiable ℝ u) (t : ℝ) (x : Vec) :
    waveGradient u (t,x) = gradient (fun y => u (t,y)) x := by
  ext i
  rw [waveGradient_apply,gradient_apply,spatialPartial_time_slice (hu (t,x))]
  rfl

lemma divergence_waveGradient {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    divergence (fun y => waveGradient u (t,y)) x = laplace (fun y => u (t,y)) x := by
  have he : (fun y => waveGradient u (t,y)) = gradient (fun y => u (t,y)) :=
    funext (waveGradient_slice (hu.differentiable (by simp)) t)
  rw [he]
  rfl

lemma waveGradient_time {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    deriv (fun r => waveGradient u (r,x)) t = waveGradient (dirD u (1,0)) (t,x) := by
  rw [deriv_slice_eq_dirD ((contDiff_waveGradient hu).differentiable (by simp))]
  ext i
  rw [← dirD_component ((contDiff_waveGradient hu).differentiable (by simp)),waveGradient_apply]
  exact dirD_comm hu (0,basis i) (1,0) (t,x)

lemma contDiff_waveEnergy {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (waveEnergy u) :=
  (((contDiff_dirD hu (1,0)).pow 2).add ((contDiff_waveGradient hu).norm_sq ℝ)).div_const 2

lemma contDiff_waveFlux {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (waveFlux u) := (contDiff_dirD hu (1,0)).neg.smul (contDiff_waveGradient hu)

lemma waveEnergy_nonneg (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : 0 ≤ waveEnergy u p := by
  dsimp [waveEnergy]
  positivity

lemma waveFlux_bound (u : ℝ × Vec → ℝ) (p : ℝ × Vec) : ‖waveFlux u p‖ ≤ waveEnergy u p := by
  rw [waveFlux,norm_smul,Real.norm_eq_abs,abs_neg]
  have h := sq_nonneg (|dirD u (1,0) p|-‖waveGradient u p‖)
  have hh := sq_abs (dirD u (1,0) p)
  dsimp [waveEnergy]
  nlinarith

lemma waveEnergy_deriv {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    deriv (fun r => waveEnergy u (r,x)) t =
      dirD u (1,0) (t,x)*dirD (dirD u (1,0)) (1,0) (t,x) +
      dot (waveGradient u (t,x)) (waveGradient (dirD u (1,0)) (t,x)) := by
  have ht : DifferentiableAt ℝ (fun r : ℝ => dirD u (1,0) (r,x)) t := by
    exact DifferentiableAt.comp (f:=fun r : ℝ => (r,x)) (g:=dirD u (1,0)) t
      ((contDiff_dirD hu (1,0)).differentiable (by simp) (t,x))
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hx : DifferentiableAt ℝ (fun r : ℝ => waveGradient u (r,x)) t := by
    exact DifferentiableAt.comp (f:=fun r : ℝ => (r,x)) (g:=waveGradient u) t
      ((contDiff_waveGradient hu).differentiable (by simp) (t,x))
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hd := ((ht.hasDerivAt.pow 2).add hx.hasDerivAt.norm_sq).div_const 2
  change HasDerivAt (fun r => waveEnergy u (r,x)) _ t at hd
  rw [hd.deriv,deriv_slice_eq_dirD ((contDiff_dirD hu (1,0)).differentiable (by simp)),
    waveGradient_time hu,← dot_eq_inner]
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
  ring

lemma waveFlux_divergence {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    divergence (fun y => waveFlux u (t,y)) x =
      -dirD u (1,0) (t,x)*laplace (fun y => u (t,y)) x -
      dot (waveGradient u (t,x)) (waveGradient (dirD u (1,0)) (t,x)) := by
  have ht : DifferentiableAt ℝ (fun y : Vec => dirD u (1,0) (t,y)) x :=
    ((contDiff_dirD hu (1,0)).differentiable (by simp) (t,x)).comp x
    ((differentiableAt_const t).prodMk differentiableAt_id)
  have hx : DifferentiableAt ℝ (fun y : Vec => waveGradient u (t,y)) x :=
    ((contDiff_waveGradient hu).differentiable (by simp) (t,x)).comp x
    ((differentiableAt_const t).prodMk differentiableAt_id)
  unfold waveFlux
  rw [divergence_smul (g:=fun y => -(dirD u (1,0) (t,y))) ht.neg hx,
    divergence_waveGradient hu]
  have hg : gradient (fun y => -dirD u (1,0) (t,y)) x = -waveGradient (dirD u (1,0)) (t,x) := by
    ext i
    rw [gradient_apply,PiLp.neg_apply,waveGradient_apply]
    unfold spatialPartial
    rw [fderiv_fun_neg,neg_apply]
    congr 1
    exact spatialPartial_time_slice ((contDiff_dirD hu (1,0)).differentiable (by simp) (t,x)) i
  rw [hg]
  simp only [dot,PiLp.neg_apply,neg_mul,Finset.sum_neg_distrib]
  have hc : (∑ i : Fin 3, waveGradient (dirD u (1,0)) (t,x) i * waveGradient u (t,x) i) =
      ∑ i : Fin 3, waveGradient u (t,x) i * waveGradient (dirD u (1,0)) (t,x) i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hc]
  ring

lemma wave_local_energy {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec)
    (hw : deriv (deriv (fun r => u (r,x))) t = laplace (fun y => u (t,y)) x) :
    deriv (fun r => waveEnergy u (r,x)) t + divergence (fun y => waveFlux u (t,y)) x = 0 := by
  rw [waveEnergy_deriv hu,waveFlux_divergence hu,← deriv_deriv_slice_eq_dirD hu,hw]
  ring

lemma dirD_add {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F G : H → W}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (e : H) :
    dirD (fun p => F p+G p) e = fun p => dirD F e p+dirD G e p := by
  funext p
  simp only [dirD,fderiv_fun_add (hF p) (hG p),add_apply]

lemma dirD_sub {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F G : H → W}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (e : H) :
    dirD (fun p => F p-G p) e = fun p => dirD F e p-dirD G e p := by
  funext p
  simp only [dirD,fderiv_fun_sub (hF p) (hG p),sub_apply]

lemma dirD_sum {H W ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (S : Finset ι) {F : ι → H → W}
    (hF : ∀ i ∈ S, Differentiable ℝ (F i)) (e : H) :
    dirD (fun p => ∑ i ∈ S, F i p) e = fun p => ∑ i ∈ S, dirD (F i) e p := by
  funext p
  simp only [dirD,fderiv_fun_sum (fun i hi => hF i hi p),sum_apply]

lemma dirD_third_comm {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : H → W}
    (hF : ContDiff ℝ ∞ F) (e a p : H) :
    dirD (dirD (dirD F a) a) e p = dirD (dirD (dirD F e) a) a p := by
  rw [dirD_comm (contDiff_dirD hF a) a e]
  have hh : dirD (dirD F a) e = dirD (dirD F e) a :=
    funext (dirD_comm hF a e)
  rw [hh]

lemma waveBox_eq {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (t : ℝ) (x : Vec) :
    waveBox u (t,x) = deriv (deriv (fun r => u (r,x))) t -laplace (fun y => u (t,y)) x := by
  rw [deriv_deriv_slice_eq_dirD hu,laplace_slice_eq_dirD hu]
  rfl

lemma contDiff_waveBox {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (waveBox u) :=
  (contDiff_dirD (contDiff_dirD hu (1,0)) (1,0)).sub
    (ContDiff.sum (fun i _ => contDiff_dirD (contDiff_dirD hu (0,basis i)) (0,basis i)))

lemma waveBox_sub {u v : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    waveBox (fun p => u p-v p) = fun p => waveBox u p-waveBox v p := by
  have hdd (e a p : ℝ × Vec) :
      dirD (dirD (fun p => u p-v p) e) a p =
      dirD (dirD u e) a p-dirD (dirD v e) a p := by
    rw [dirD_sub (hu.differentiable (by simp)) (hv.differentiable (by simp)),
      dirD_sub ((contDiff_dirD hu e).differentiable (by simp))
        ((contDiff_dirD hv e).differentiable (by simp))]
  funext p
  simp only [waveBox,hdd,Finset.sum_sub_distrib]
  ring

lemma waveBox_add {u v : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    waveBox (fun p => u p+v p) = fun p => waveBox u p+waveBox v p := by
  have hdd (e a p : ℝ × Vec) :
      dirD (dirD (fun p => u p+v p) e) a p =
      dirD (dirD u e) a p+dirD (dirD v e) a p := by
    rw [dirD_add (hu.differentiable (by simp)) (hv.differentiable (by simp)),
      dirD_add ((contDiff_dirD hu e).differentiable (by simp))
        ((contDiff_dirD hv e).differentiable (by simp))]
  funext p
  simp only [waveBox,hdd,Finset.sum_add_distrib]
  ring

lemma waveBox_dirD {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (e : ℝ × Vec) (p : ℝ × Vec) :
    waveBox (dirD u e) p = dirD (waveBox u) e p := by
  have hf := (contDiff_dirD (contDiff_dirD hu (1,0)) (1,0)).differentiable (by simp)
  have hi (i : Fin 3) :=
    (contDiff_dirD (contDiff_dirD hu (0,basis i)) (0,basis i)).differentiable (by simp)
  have hs : Differentiable ℝ (fun p => ∑ i : Fin 3, dirD (dirD u (0,basis i)) (0,basis i) p) :=
    Differentiable.fun_sum (fun i _ => hi i)
  unfold waveBox
  rw [dirD_sub hf hs]
  dsimp only
  rw [dirD_sum Finset.univ (fun i _ => hi i)]
  simp only [dirD_third_comm hu]

lemma waveBox_timeDerivative_zero {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    (hw : ∀ t, 0<t → ∀ x, waveBox u (t,x)=0) {t : ℝ} (ht : 0<t) (x : Vec) :
    waveBox (dirD u (1,0)) (t,x)=0 := by
  rw [waveBox_dirD hu,← deriv_slice_eq_dirD ((contDiff_waveBox hu).differentiable (by simp))]
  have he : (fun r => waveBox u (r,x)) =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    filter_upwards [lt_mem_nhds ht] with r hr
    exact hw r hr x
  rw [he.deriv_eq,deriv_const]

lemma waveK_box {g : Vec → ℝ} (hg : ContDiff ℝ ∞ g) {t : ℝ} (ht : 0≤t) (x : Vec) :
    waveBox (waveK g) (t,x)=0 := by
  rw [waveBox_eq (contDiff_waveK hg),waveK_equation hg x ht,sub_self]

lemma contDiff_freeWave {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (freeWave g h) :=
  (contDiff_dirD (contDiff_waveK hg) (1,0)).add (contDiff_waveK hh)

lemma freeWave_initial {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) :
    freeWave g h (0,x)=g x := by
  rw [freeWave,← deriv_slice_eq_dirD ((contDiff_waveK hg).differentiable (by simp)),
    waveK_initial_velocity hg,waveK_zero,add_zero]

lemma freeWave_initial_velocity {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g)
    (hh : ContDiff ℝ ∞ h) (x : Vec) :
    deriv (fun t => freeWave g h (t,x)) 0 = h x := by
  rw [deriv_slice_eq_dirD ((contDiff_freeWave hg hh).differentiable (by simp))]
  change dirD (fun p => dirD (waveK g) (1,0) p+waveK h p) (1,0) (0,x)=_
  rw [dirD_add ((contDiff_dirD (contDiff_waveK hg) (1,0)).differentiable (by simp))
    ((contDiff_waveK hh).differentiable (by simp))]
  dsimp only
  rw [← deriv_deriv_slice_eq_dirD (contDiff_waveK hg),waveK_equation hg x (by norm_num),
    ← deriv_slice_eq_dirD ((contDiff_waveK hh).differentiable (by simp)),waveK_initial_velocity hh]
  simp only [waveK_zero]
  simp [laplace,divergence,gradient,spatialPartial]

lemma freeWave_box {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    {t : ℝ} (ht : 0<t) (x : Vec) : waveBox (freeWave g h) (t,x)=0 := by
  unfold freeWave
  rw [waveBox_add (contDiff_dirD (contDiff_waveK hg) (1,0)) (contDiff_waveK hh)]
  dsimp only
  rw [waveBox_timeDerivative_zero (contDiff_waveK hg) (fun _ hr y => waveK_box hg hr.le y) ht x,
    waveK_box hh ht.le,zero_add]

lemma sourceWave_box {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) {t : ℝ} (ht : 0≤t) (x : Vec) :
    waveBox (sourceWave ρ) (t,x)=ρ (t,x) := by
  rw [waveBox_eq (contDiff_sourceWave hρ),sourceWave_equation hρ x ht]
  ring

lemma waveGradient_initial_zero {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x, u (0,x)=0) (x : Vec) : waveGradient u (0,x)=0 := by
  rw [waveGradient_slice (hu.differentiable (by simp))]
  have hh : (fun y => u (0,y)) = fun _ => (0:ℝ) := funext h0
  rw [hh]
  ext i
  simp

lemma waveEnergy_initial_zero {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x, u (0,x)=0) (h1 : ∀ x, deriv (fun t => u (t,x)) 0=0) (x : Vec) :
    waveEnergy u (0,x)=0 := by
  rw [waveEnergy,waveGradient_initial_zero hu h0,
    ← deriv_slice_eq_dirD (hu.differentiable (by simp)),h1]
  norm_num

lemma wave_zero_on {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u)
    {T : ℝ} (hT : 0≤T)
    (hw : ∀ t ∈ Ioo 0 T, ∀ x, waveBox u (t,x)=0)
    (h0 : ∀ x, u (0,x)=0) (h1 : ∀ x, deriv (fun t => u (t,x)) 0=0)
    (x : Vec) : u (T,x)=0 := by
  have hezero (t : ℝ) (ht : t ∈ Icc 0 T) (y : Vec) : waveEnergy u (t,y)=0 := by
    apply causal_local_energy_vanishes ht.1
      ((contDiff_waveEnergy hu).of_le (by simp)).contDiffOn
      ((contDiff_waveFlux hu).of_le (by simp)).contDiffOn
      (contDiff_waveEnergy hu).continuous.continuousOn
      (fun _ _ z => waveEnergy_nonneg u (_,z))
      (fun _ _ z => waveFlux_bound u (_,z))
      _ (waveEnergy_initial_zero hu h0 h1)
    intro r hr z
    apply wave_local_energy hu
    have hh := hw r ⟨hr.1,hr.2.trans_le ht.2⟩ z
    rw [waveBox_eq hu] at hh
    linarith
  have htzero (t : ℝ) (ht : t ∈ Icc 0 T) : deriv (fun r => u (r,x)) t=0 := by
    rw [deriv_slice_eq_dirD (hu.differentiable (by simp))]
    have he := hezero t ht x
    unfold waveEnergy at he
    nlinarith [sq_nonneg (dirD u (1,0) (t,x)),sq_nonneg ‖waveGradient u (t,x)‖]
  have hdiff (t : ℝ) : DifferentiableAt ℝ (fun r => u (r,x)) t :=
    DifferentiableAt.comp (f:=fun r : ℝ => (r,x)) (g:=u) t
      (hu.differentiable (by simp) (t,x))
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hn := (convex_Icc (0:ℝ) T).norm_image_sub_le_of_norm_deriv_le
    (fun t (_ht : t ∈ Icc 0 T) => hdiff t)
    (C:=0) (fun t ht => by rw [htzero t ht]; simp) ⟨le_rfl,hT⟩ ⟨hT,le_rfl⟩
  simp only [zero_mul,h0,sub_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

lemma wave_unique_on {u v : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    {T : ℝ} (hT : 0≤T)
    (hw : ∀ t ∈ Ioo 0 T, ∀ x, waveBox u (t,x)=waveBox v (t,x))
    (h0 : ∀ x, u (0,x)=v (0,x))
    (h1 : ∀ x, deriv (fun t => u (t,x)) 0=deriv (fun t => v (t,x)) 0)
    (x : Vec) : u (T,x)=v (T,x) := by
  apply sub_eq_zero.mp
  apply wave_zero_on (hu.sub hv) hT _ _ _ x
  · intro t ht y
    rw [waveBox_sub hu hv]
    exact sub_eq_zero.mpr (hw t ht y)
  · intro y
    exact sub_eq_zero.mpr (h0 y)
  · intro y
    rw [deriv_slice_eq_dirD ((hu.sub hv).differentiable (by simp)),
      dirD_sub (hu.differentiable (by simp)) (hv.differentiable (by simp))]
    dsimp only
    rw [← deriv_slice_eq_dirD (hu.differentiable (by simp)),
      ← deriv_slice_eq_dirD (hv.differentiable (by simp)),h1,sub_self]

lemma spaceCurl_apply (F : Field) (p : ℝ × Vec) (i : Fin 3) :
    spaceCurl F p i = dirD F (0,basis (curlA i)) p (curlB i) -
      dirD F (0,basis (curlB i)) p (curlA i) := rfl

lemma contDiff_spaceCurl {F : Field} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (spaceCurl F) := by
  apply contDiff_euclidean.mpr
  intro i
  exact (contDiff_component (contDiff_dirD hF _) _).sub
    (contDiff_component (contDiff_dirD hF _) _)

lemma spaceCurl_slice {F : Field} (hF : Differentiable ℝ F) (t : ℝ) (x : Vec) :
    spaceCurl F (t,x) = curl (fun y => F (t,y)) x := by
  have hc (i : Fin 3) : Differentiable ℝ (fun p => F p i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiable.comp hF
  have hh (i j : Fin 3) : spatialPartial (fun y => F (t,y) i) x j =
      dirD F (0,basis j) (t,x) i := by
    rw [spatialPartial_time_slice (hc i (t,x))]
    exact dirD_component hF (t,x) (0,basis j) i
  ext i
  fin_cases i <;> simp [spaceCurl_apply,curl,curlA,curlB,hh]

lemma dirD_spaceCurl {F : Field} (hF : ContDiff ℝ ∞ F) (e p : ℝ × Vec) :
    dirD (spaceCurl F) e p = spaceCurl (dirD F e) p := by
  ext i
  rw [← dirD_component ((contDiff_spaceCurl hF).differentiable (by simp))]
  change dirD (fun q => dirD F (0,basis (curlA i)) q (curlB i) -
    dirD F (0,basis (curlB i)) q (curlA i)) e p = _
  rw [dirD_sub ((contDiff_component (contDiff_dirD hF _) _).differentiable (by simp))
    ((contDiff_component (contDiff_dirD hF _) _).differentiable (by simp))]
  dsimp only
  rw [dirD_component ((contDiff_dirD hF _).differentiable (by simp)),
    dirD_component ((contDiff_dirD hF _).differentiable (by simp)),
    dirD_comm hF (0,basis (curlA i)) e,dirD_comm hF (0,basis (curlB i)) e]
  rfl

lemma spaceCurl_sub {F G : Field} (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) :
    spaceCurl (fun p => F p-G p) = fun p => spaceCurl F p-spaceCurl G p := by
  funext p
  ext i
  simp only [spaceCurl_apply,dirD_sub hF hG,PiLp.sub_apply]
  ring

lemma contDiff_field_slice {F : Field} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => F (t,x)) := hF.comp (contDiff_const.prodMk contDiff_id)

lemma spaceCurl_spaceCurl_component {F : Field} (hF : ContDiff ℝ ∞ F)
    (t : ℝ) (x : Vec) (i : Fin 3) :
    spaceCurl (spaceCurl F) (t,x) i =
      spatialPartial (divergence (fun y => F (t,y))) x i-laplace (fun y => F (t,y) i) x := by
  rw [spaceCurl_slice ((contDiff_spaceCurl hF).differentiable (by simp))]
  have he : (fun y => spaceCurl F (t,y)) = curl (fun y => F (t,y)) :=
    funext (spaceCurl_slice (hF.differentiable (by simp)) t)
  rw [he,curl_curl_component (contDiff_field_slice hF t)]

lemma dirD_eq_of_eventuallyEq {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F G : H → W} {p : H}
    (h : F =ᶠ[𝓝 p] G) (e : H) : dirD F e p = dirD G e p := by
  unfold dirD
  rw [h.fderiv_eq]

lemma positive_time_eventuallyEq {W : Type*} {F G : ℝ × Vec → W}
    (h : ∀ t, 0<t → ∀ x, F (t,x)=G (t,x)) {t : ℝ} (ht : 0<t) (x : Vec) :
    F =ᶠ[𝓝 (t,x)] G := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds ht] with p hp
  exact h p.1 hp p.2

lemma spaceCurl_eq_of_eventuallyEq {F G : Field} {p : ℝ × Vec}
    (h : F =ᶠ[𝓝 p] G) : spaceCurl F p=spaceCurl G p := by
  ext i
  simp only [spaceCurl_apply,dirD_eq_of_eventuallyEq h]

lemma interval_time_eventuallyEq {W : Type*} {F G : ℝ × Vec → W} {a b t : ℝ}
    (h : ∀ r ∈ Ioo a b, ∀ x, F (r,x)=G (r,x)) (ht : t ∈ Ioo a b) (x : Vec) :
    F =ᶠ[𝓝 (t,x)] G := by
  filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds ht] with p hp
  exact h p.1 hp p.2

lemma dirD_dirD_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : ContDiff ℝ ∞ F) (e v p : H) (i : Fin 3) :
    dirD (dirD (fun q => F q i) e) v p = dirD (dirD F e) v p i := by
  have hh : dirD (fun q => F q i) e = fun q => dirD F e q i :=
    funext (fun q => dirD_component (hF.differentiable (by simp)) q e i)
  rw [hh,dirD_component ((contDiff_dirD hF e).differentiable (by simp))]

lemma waveBox_component_eq {F : Field} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : Vec) (i : Fin 3) :
    waveBox (fun p => F p i) (t,x) = dirD (dirD F (1,0)) (1,0) (t,x) i -
      laplace (fun y => F (t,y) i) x := by
  rw [waveBox_eq (contDiff_component hF i),
    deriv_deriv_slice_eq_dirD (contDiff_component hF i),dirD_dirD_component hF]

lemma maxwell_magnetic_wave {E B j : Field} {a b t : ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (hj : ContDiff ℝ ∞ j)
    (hEt : ∀ r ∈ Ioo a b, ∀ x, dirD E (1,0) (r,x)=spaceCurl B (r,x)-j (r,x))
    (hBt : ∀ r ∈ Ioo a b, ∀ x, dirD B (1,0) (r,x) = -spaceCurl E (r,x))
    (hDiv : ∀ r ∈ Ioo a b, ∀ x, divergence (fun y => B (r,y)) x=0)
    (ht : t ∈ Ioo a b) (x : Vec) (i : Fin 3) :
    waveBox (fun p => B p i) (t,x) = spaceCurl j (t,x) i := by
  have hdd := dirD_eq_of_eventuallyEq (interval_time_eventuallyEq (F:=dirD B (1,0)) (G:=fun p => -spaceCurl E p) hBt ht x) (1,0)
  have hn : dirD (fun p => -spaceCurl E p) (1,0) (t,x) = -dirD (spaceCurl E) (1,0) (t,x) := by
    simp [dirD,fderiv_fun_neg]
  rw [hn,dirD_spaceCurl hE] at hdd
  have hc := spaceCurl_eq_of_eventuallyEq (interval_time_eventuallyEq (F:=dirD E (1,0)) (G:=fun p => spaceCurl B p-j p) hEt ht x)
  rw [spaceCurl_sub ((contDiff_spaceCurl hB).differentiable (by simp))
    (hj.differentiable (by simp))] at hc
  dsimp only at hc
  rw [hc] at hdd
  rw [waveBox_component_eq hB,hdd,PiLp.neg_apply,PiLp.sub_apply,
    spaceCurl_spaceCurl_component hB]
  have hd : divergence (fun y => B (t,y)) = fun _ => (0:ℝ) := funext (hDiv t ht)
  rw [hd]
  simp [spatialPartial]
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

namespace RVM

lemma dirD_spatial_slice {F : ℝ × Vec → ℝ} (hF : Differentiable ℝ F)
    (t : ℝ) (x : Vec) (i : Fin 3) :
    dirD F (0,basis i) (t,x)=spatialPartial (fun y => F (t,y)) x i :=
  (spatialPartial_time_slice (hF (t,x)) i).symm

lemma waveBox_dirD_sourceWave {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {t : ℝ} (ht : 0<t) (x : Vec) (e : ℝ × Vec) :
    waveBox (dirD (sourceWave ρ) e) (t,x)=dirD ρ e (t,x) := by
  rw [waveBox_dirD (contDiff_sourceWave hρ)]
  apply dirD_eq_of_eventuallyEq
  exact positive_time_eventuallyEq (fun r hr y => sourceWave_box hρ hr.le y) ht x

lemma sourceWave_space_initial {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (x : Vec) (i : Fin 3) : dirD (sourceWave ρ) (0,basis i) (0,x)=0 := by
  rw [dirD_spatial_slice ((contDiff_sourceWave hρ).differentiable (by simp))]
  have hh : (fun y => sourceWave ρ (0,y)) = fun _ => (0:ℝ) :=
    funext (sourceWave_initial_value ρ)
  rw [hh]
  simp [spatialPartial]

lemma sourceWave_time_initial {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (x : Vec) : dirD (sourceWave ρ) (1,0) (0,x)=0 := by
  rw [← deriv_slice_eq_dirD ((contDiff_sourceWave hρ).differentiable (by simp)),
    sourceWave_initial_velocity hρ]

lemma sourceWave_space_time_initial {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (x : Vec) (i : Fin 3) :
    dirD (dirD (sourceWave ρ) (0,basis i)) (1,0) (0,x)=0 := by
  rw [dirD_comm (contDiff_sourceWave hρ),
    dirD_spatial_slice ((contDiff_dirD (contDiff_sourceWave hρ) _).differentiable (by simp))]
  have hh : (fun y => dirD (sourceWave ρ) (1,0) (0,y)) = fun _ => (0:ℝ) :=
    funext (sourceWave_time_initial hρ)
  rw [hh]
  simp [spatialPartial]

lemma contDiff_magneticPotentialComponent {j : Field} (hj : ContDiff ℝ ∞ j) (i : Fin 3) :
    ContDiff ℝ ∞ (magneticPotentialComponent j i) :=
  (contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _).sub
    (contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _)

lemma magneticPotentialComponent_initial {j : Field} (hj : ContDiff ℝ ∞ j) (x : Vec) (i : Fin 3) :
    magneticPotentialComponent j i (0,x)=0 := by
  simp only [magneticPotentialComponent,sourceWave_space_initial (contDiff_component hj _),sub_self]

lemma magneticPotentialComponent_initial_velocity {j : Field} (hj : ContDiff ℝ ∞ j)
    (x : Vec) (i : Fin 3) : deriv (fun t => magneticPotentialComponent j i (t,x)) 0 = 0 := by
  rw [deriv_slice_eq_dirD ((contDiff_magneticPotentialComponent hj i).differentiable (by simp))]
  unfold magneticPotentialComponent
  rw [dirD_sub ((contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _).differentiable (by simp))
    ((contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _).differentiable (by simp))]
  dsimp only
  rw [sourceWave_space_time_initial (contDiff_component hj _),
    sourceWave_space_time_initial (contDiff_component hj _),sub_self]

lemma magneticPotentialComponent_box {j : Field} (hj : ContDiff ℝ ∞ j)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    waveBox (magneticPotentialComponent j i) (t,x)=spaceCurl j (t,x) i := by
  unfold magneticPotentialComponent
  rw [waveBox_sub (contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _)
    (contDiff_dirD (contDiff_sourceWave (contDiff_component hj _)) _)]
  dsimp only
  rw [waveBox_dirD_sourceWave (contDiff_component hj _) ht,
    waveBox_dirD_sourceWave (contDiff_component hj _) ht,
    dirD_component (hj.differentiable (by simp)),dirD_component (hj.differentiable (by simp))]
  rfl

lemma maxwell_magnetic_potential_representation {E B j : Field} {T : ℝ}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) (hj : ContDiff ℝ ∞ j) (hT : 0≤T)
    (hEt : ∀ r ∈ Ioo 0 T, ∀ x, dirD E (1,0) (r,x)=spaceCurl B (r,x)-j (r,x))
    (hBt : ∀ r ∈ Icc 0 T, ∀ x, dirD B (1,0) (r,x) = -spaceCurl E (r,x))
    (hDiv : ∀ r ∈ Ioo 0 T, ∀ x, divergence (fun y => B (r,y)) x=0)
    (x : Vec) (i : Fin 3) :
    B (T,x) i = freeWave (fun y => B (0,y) i) (fun y => -spaceCurl E (0,y) i) (T,x) +
      magneticPotentialComponent j i (T,x) := by
  have hg := contDiff_component (contDiff_field_slice hB 0) i
  have hh := (contDiff_component (contDiff_field_slice (contDiff_spaceCurl hE) 0) i).neg
  have hfree := contDiff_freeWave hg hh
  have hpot := contDiff_magneticPotentialComponent hj i
  apply wave_unique_on (contDiff_component hB i) (hfree.add hpot) hT
  · intro r hr y
    rw [waveBox_add hfree hpot]
    dsimp only
    rw [freeWave_box hg hh hr.1,magneticPotentialComponent_box hj hr.1,zero_add]
    exact maxwell_magnetic_wave hE hB hj hEt
      (fun r hr => hBt r ⟨hr.1.le,hr.2.le⟩) hDiv hr y i
  · intro y
    rw [freeWave_initial hg,magneticPotentialComponent_initial hj,add_zero]
  · intro y
    have hfdy : DifferentiableAt ℝ (fun t => freeWave (fun z => B (0,z) i)
        (fun z => -spaceCurl E (0,z) i) (t,y)) 0 := by
      exact (((hfree.differentiable (by simp)).comp
        (differentiable_id.prodMk (differentiable_const y))) 0)
    have hpdy : DifferentiableAt ℝ (fun t => magneticPotentialComponent j i (t,y)) 0 := by
      exact (((hpot.differentiable (by simp)).comp
        (differentiable_id.prodMk (differentiable_const y))) 0)
    rw [deriv_fun_add hfdy hpdy,
      freeWave_initial_velocity hg hh,magneticPotentialComponent_initial_velocity hj,
      deriv_slice_eq_dirD ((contDiff_component hB i).differentiable (by simp)),
      dirD_component (hB.differentiable (by simp)),hBt 0 ⟨le_rfl,hT⟩]
    simp
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


lemma hasDerivAt_norm_nonzero {Y : ℝ → Vec} {u : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h0 : Y s≠0) :
    HasDerivAt (fun t => ‖Y t‖) (dot (Y s) u / ‖Y s‖) s := by
  have hn := (hY.differentiableAt.norm ℝ h0).hasDerivAt
  have he := (hn.pow 2).unique hY.norm_sq
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,← dot_eq_inner] at he
  have hr : ‖Y s‖≠0 := norm_ne_zero_iff.mpr h0
  have he' : deriv (fun t => ‖Y t‖) s = dot (Y s) u / ‖Y s‖ := by
    apply (eq_div_iff hr).mpr
    linarith
  rwa [he'] at hn

lemma dot_gradient_direction (g : Vec → ℝ) (y w : Vec) :
    dot (gradient g y) w=fderiv ℝ g y w := by
  rw [dot_comm,clm_sum_basis]
  simp only [dot,gradient_apply,spatialPartial]

lemma divergence_const_rvm (w y : Vec) : divergence (fun _ : Vec => w) y=0 := by
  simp [divergence,spatialPartial]

lemma contDiff_holeCutoff (ε : ℝ) {k : ℕ∞} : ContDiff ℝ k (holeCutoff ε) :=
  contDiff_const.sub (contDiff_ballCutoff _ _)

lemma holeCutoff_zero {ε : ℝ} (hε : 0<ε) {x : Vec} (hx : ‖x‖<ε/4) :
    holeCutoff ε x=0 := by
  rw [holeCutoff,ballCutoff,Real.smoothTransition.one_of_one_le,sub_self]
  apply (le_div_iff₀ (by positivity : 0<ε^2/8)).mpr
  nlinarith [sq_nonneg (ε/4-‖x‖),norm_nonneg x]

lemma holeCutoff_one {ε : ℝ} (hε : 0<ε) {x : Vec} (hx : ε/2≤‖x‖) :
    holeCutoff ε x=1 := by
  rw [holeCutoff,ballCutoff,Real.smoothTransition.zero_of_nonpos,sub_zero]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  nlinarith [sq_nonneg (‖x‖-ε/2)]

lemma holeCutoff_eventually_one {ε : ℝ} (hε : 0<ε) {x : Vec} (hx : ε/2<‖x‖) :
    holeCutoff ε =ᶠ[𝓝 x] (fun _ => 1) := by
  have hn : {y : Vec | ε/2<‖y‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  filter_upwards [hn] with y hy
  exact holeCutoff_one hε hy.le

lemma contDiff_holeCutoff_smul {ε : ℝ} {F : Vec → Vec} (hε : 0<ε)
    (hF : ∀ x≠0, ContDiffAt ℝ 1 F x) :
    ContDiff ℝ 1 (fun x => holeCutoff ε x • F x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : (fun x => holeCutoff ε x • F x) =ᶠ[𝓝 (0:Vec)] (fun _ => 0) := by
      filter_upwards [ball_mem_nhds (0:Vec) (by positivity : 0<ε/4)] with y hy
      rw [holeCutoff_zero hε (by simpa only [mem_ball_zero_iff] using hy),zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (contDiff_holeCutoff ε).contDiffAt.smul (hF x hx)

lemma divergence_congr_eventually {F G : Vec → Vec} {x : Vec} (h : F =ᶠ[𝓝 x] G) :
    divergence F x=divergence G x := by
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    ((h.fun_comp (fun w : Vec => w i)).fderiv_eq (𝕜:=ℝ))

lemma divergence_holeCutoff {ε : ℝ} {F : Vec → Vec} {x : Vec} (hε : 0<ε)
    (hx : ε/2<‖x‖) :
    divergence (fun z => holeCutoff ε z • F z) x = divergence F x := by
  apply divergence_congr_eventually
  filter_upwards [holeCutoff_eventually_one hε hx] with y hy
  rw [hy,one_smul]

lemma divergence_annulus {ε R : ℝ} (hε : 0<ε) (hεR : ε≤R) {F : Vec → Vec}
    (hF : ∀ x≠0, ContDiffAt ℝ 1 F x) :
    (∫ x in ball (0:Vec) R \ ball (0:Vec) ε, divergence F x) =
      (∫ n : Sphere, R^2*dot n.1 (F (R • n.1)) ∂sphereMeasure) -
      (∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure) := by
  let G : Vec → Vec := fun x => holeCutoff ε x • F x
  have hG := contDiff_holeCutoff_smul hε hF
  have hD : Continuous (divergence G) := continuous_divergence hG
  have hi : IntegrableOn (divergence G) (ball (0:Vec) R) :=
    (hD.continuousOn.integrableOn_compact (isCompact_closedBall (0:Vec) R)).mono_set ball_subset_closedBall
  have hd : (∫ x in ball (0:Vec) R \ ball (0:Vec) ε, divergence F x) =
      (∫ x in ball (0:Vec) R, divergence G x) - (∫ x in ball (0:Vec) ε, divergence G x) := by
    rw [← setIntegral_sdiff measurableSet_ball hi (ball_subset_ball hεR)]
    apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
    intro x hx
    apply (divergence_holeCutoff hε _).symm
    have hh : ε≤‖x‖ := by simpa only [mem_ball_zero_iff,not_lt] using hx.2
    linarith
  rw [hd,divergence_ball (hε.trans_le hεR) hG,divergence_ball hε hG]
  have hval (c : ℝ) (hc : ε ≤ c) (n : Sphere) : G (c • n.1)=F (c • n.1) := by
    dsimp [G]
    rw [holeCutoff_one hε,one_smul]
    have hn : ‖n.1‖=1 := sphere_norm n
    rw [norm_smul,Real.norm_of_nonneg (hε.le.trans hc),hn,mul_one]
    linarith
  congr 1 <;> apply integral_congr_ae <;> filter_upwards [] with n
  · change R^2*dot n.1 (G (R • n.1)) = _
    rw [hval R hεR]
  · change ε^2*dot n.1 (G (ε • n.1)) = _
    rw [hval ε le_rfl]



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


lemma dirD_integral_sphere {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [ProperSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : H × Vec → W} (hF : ContDiff ℝ 1 F) (e p : H) :
    dirD (fun x => ∫ n : Sphere, F (x,n.1) ∂sphereMeasure) e p =
      ∫ n : Sphere, dirD F (e,0) (p,n.1) ∂sphereMeasure := by
  have hc : Continuous (fun n : Sphere => (fderiv ℝ F (p,n.1)).comp
      (ContinuousLinearMap.inl ℝ H Vec)) :=
    ((hF.continuous_fderiv (by simp)).comp
      (continuous_const.prodMk continuous_subtype_val)).clm_comp continuous_const
  unfold dirD
  rw [(hasFDerivAt_integral_sphere hF p).fderiv,
    ContinuousLinearMap.integral_apply (hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) e]
  rfl

lemma sourceWave_eq_radius (ρ : ℝ × Vec → ℝ) : sourceWave ρ=volterra (radiusWaveKernel ρ) := by
  funext p
  have hh := intervalIntegral.integral_comp_sub_left (fun r => radiusWaveKernel ρ (p,r))
    (a:=0) (b:=p.1) p.1
  simpa only [sourceWave,volterra,sourceWaveKernel,waveK,sphereSum,radiusWaveKernel,
    sub_self,sub_zero,sub_sub_cancel,mul_assoc] using hh

lemma contDiff_radiusWaveKernel {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiff ℝ ∞ (radiusWaveKernel ρ) := by
  have hi : ContDiff ℝ ∞ (fun z : ((ℝ × Vec) × ℝ) × Vec =>
      ρ (z.1.1.1-z.1.2,z.1.1.2+z.1.2 • z.2)) := by
    apply hρ.comp
    exact ((contDiff_fst.comp (contDiff_fst.comp contDiff_fst)).sub
      (contDiff_snd.comp contDiff_fst)).prodMk
      ((contDiff_snd.comp (contDiff_fst.comp contDiff_fst)).add
        ((contDiff_snd.comp contDiff_fst).smul contDiff_snd))
  exact (contDiff_const.mul contDiff_snd).mul (contDiff_integral_sphere hi)

lemma dirD_radius_average {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (e p : ℝ × Vec) (r : ℝ) :
    dirD (fun z : ℝ × Vec => ∫ n : Sphere, ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure) e p =
      ∫ n : Sphere, dirD ρ e (p.1-r,p.2+r • n.1) ∂sphereMeasure := by
  let F : (ℝ × Vec) × Vec → ℝ := fun z => ρ (z.1.1-r,z.1.2+r • z.2)
  have hF : ContDiff ℝ 1 F := hρ.of_le (by simp) |>.comp
    (((contDiff_fst.comp contDiff_fst).sub contDiff_const).prodMk
      ((contDiff_snd.comp contDiff_fst).add (contDiff_snd.const_smul r)))
  rw [show (fun z : ℝ × Vec => ∫ n : Sphere, ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure)=
      (fun z => ∫ n : Sphere, F (z,n.1) ∂sphereMeasure) from rfl,dirD_integral_sphere hF]
  apply integral_congr_ae
  apply ae_of_all
  intro n
  have hi := ((hasFDerivAt_fst (𝕜:=ℝ) (p:=(p,n.1))).fst.sub_const r).prodMk
    (((hasFDerivAt_fst (𝕜:=ℝ) (p:=(p,n.1))).snd).add
      ((hasFDerivAt_snd (𝕜:=ℝ) (p:=(p,n.1))).const_smul r))
  have hd := (hρ.differentiable (by simp) (p.1-r,p.2+r • n.1)).hasFDerivAt.comp (p,n.1) hi
  change HasFDerivAt F _ (p,n.1) at hd
  change (fderiv ℝ F (p,n.1)) (e,0) = (fderiv ℝ ρ (p.1-r,p.2+r • n.1)) e
  rw [hd.fderiv]
  simp

lemma dirD_radiusWaveKernel {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (e p : ℝ × Vec) (r : ℝ) :
    dirD (radiusWaveKernel ρ) (e,0) (p,r)=radiusWaveKernel (dirD ρ e) (p,r) := by
  rw [← dirD_prod_left ((contDiff_radiusWaveKernel hρ).differentiable (by simp))]
  have hA : ContDiff ℝ ∞ (fun z : ℝ × Vec => ∫ n : Sphere,
      ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure) :=
    contDiff_integral_sphere (hρ.comp
      (((contDiff_fst.comp contDiff_fst).sub contDiff_const).prodMk
        ((contDiff_snd.comp contDiff_fst).add (contDiff_snd.const_smul r))))
  change dirD (fun z : ℝ × Vec => ((4*Real.pi)⁻¹*r)*
    (∫ n : Sphere, ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure)) e p = _
  unfold dirD
  rw [fderiv_const_mul (hA.differentiable (by simp) p)]
  change ((4*Real.pi)⁻¹*r)*dirD (fun z : ℝ × Vec =>
    ∫ n : Sphere, ρ (z.1-r,z.2+r • n.1) ∂sphereMeasure) e p = _
  rw [dirD_radius_average hρ]
  rfl

lemma dirD_sourceWave {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ) (e p : ℝ × Vec) :
    dirD (sourceWave ρ) e p = e.1*waveK (fun y => ρ (0,y)) p + sourceWave (dirD ρ e) p := by
  rw [sourceWave_eq_radius ρ,dirD_volterra (contDiff_radiusWaveKernel hρ)]
  have he : dirD (radiusWaveKernel ρ) (e,0)=radiusWaveKernel (dirD ρ e) := by
    funext z
    exact dirD_radiusWaveKernel hρ e z.1 z.2
  rw [he,← sourceWave_eq_radius]
  simp only [radiusWaveKernel,waveK,sphereSum,sub_self,mul_assoc]

lemma magneticPotentialComponent_source {j : Field} (hj : ContDiff ℝ ∞ j)
    (i : Fin 3) (p : ℝ × Vec) :
    magneticPotentialComponent j i p =
      sourceWave (dirD (fun z => j z (curlB i)) (0,basis (curlA i))) p -
      sourceWave (dirD (fun z => j z (curlA i)) (0,basis (curlB i))) p := by
  unfold magneticPotentialComponent
  rw [dirD_sourceWave (contDiff_component hj _),dirD_sourceWave (contDiff_component hj _)]
  simp

lemma ballCutoff_one {R ε : ℝ} (hε : 0<ε) {x : Vec}
    (hx : ε≤R^2-‖x‖^2) : ballCutoff R ε x=1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ hε).mpr (by simpa using hx)

lemma ballCutoff_eventually_one {R ε : ℝ} (hε : 0<ε) {x : Vec}
    (hx : ε<R^2-‖x‖^2) : ballCutoff R ε =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [(isOpen_lt continuous_const (continuous_const.sub (continuous_norm.pow 2))).mem_nhds hx]
    with y hy
  exact ballCutoff_one hε hy.le

lemma divergence_annulus_local {ε R T : ℝ} (hε : 0<ε) (hεR : ε≤R) (hRT : R<T)
    {F : Vec → Vec} (hF : ∀ x, 0<‖x‖ → ‖x‖<T → ContDiffAt ℝ 1 F x) :
    (∫ x in ball (0:Vec) R \ ball (0:Vec) ε, divergence F x) =
      (∫ n : Sphere, R^2*dot n.1 (F (R • n.1)) ∂sphereMeasure) -
      (∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure) := by
  let C := (R+T)/2
  let δ := C^2-R^2
  have hR : 0<R := hε.trans_le hεR
  have hRC : R<C := by dsimp [C]; linarith
  have hCT : C<T := by dsimp [C]; linarith
  have hC : 0<C := hR.trans hRC
  have hδ : 0<δ := by dsimp [δ]; nlinarith
  let G : Vec → Vec := fun x => ballCutoff C δ x • F x
  have hG : ∀ x≠0, ContDiffAt ℝ 1 G x := by
    intro x hx
    by_cases hxt : ‖x‖<T
    · exact (contDiff_ballCutoff C δ).contDiffAt.smul (hF x (norm_pos_iff.mpr hx) hxt)
    · have hcx : C<‖x‖ := hCT.trans_le (not_lt.mp hxt)
      have he : G =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hcx] with y hy
        dsimp [G]
        rw [ballCutoff_zero hC.le hδ (by simpa only [mem_closedBall_zero_iff,not_le] using hy),zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hD : ∀ x ∈ ball (0:Vec) R, divergence G x=divergence F x := by
    intro x hx
    have hxR : ‖x‖<R := by simpa only [mem_ball_zero_iff] using hx
    apply divergence_congr_eventually
    filter_upwards [ballCutoff_eventually_one hδ (show δ<C^2-‖x‖^2 by
      dsimp [δ]; nlinarith [norm_nonneg x])] with y hy
    dsimp [G]
    rw [hy,one_smul]
  have hV (c : ℝ) (hc : 0 ≤ c) (hcR : c≤R) (n : Sphere) : G (c • n.1)=F (c • n.1) := by
    have hn : ‖c • n.1‖=c := by rw [norm_smul,Real.norm_of_nonneg hc,sphere_norm,mul_one]
    dsimp [G]
    rw [ballCutoff_one hδ (by rw [hn]; dsimp [δ]; nlinarith),one_smul]
  rw [setIntegral_congr_fun (g:=divergence G) (measurableSet_ball.diff measurableSet_ball)
    (fun x hx => (hD x hx.1).symm),divergence_annulus hε hεR hG]
  congr 1 <;> apply integral_congr_ae <;> filter_upwards [] with n
  · rw [hV R hR.le le_rfl]
  · rw [hV ε hε.le hεR]

lemma integral_annulus_tendsto {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {R : ℝ} (hF : IntegrableOn F (ball (0:Vec) R)) :
    Tendsto (fun ε : ℝ => ∫ x in ball (0:Vec) R \ ball (0:Vec) ε, F x)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x in ball (0:Vec) R, F x)) := by
  have ht : Tendsto (fun ε : ℝ => ∫ x in ball (0:Vec) R,
      (ball (0:Vec) ε)ᶜ.indicator F x) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x in ball (0:Vec) R, F x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖F x‖)
    · exact Eventually.of_forall (fun ε => hF.aestronglyMeasurable.indicator measurableSet_ball.compl)
    · exact Eventually.of_forall (fun ε => ae_of_all _ (fun x => norm_indicator_le_norm_self _ _))
    · exact hF.norm
    · filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:Vec))] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (norm_pos_iff.mpr hx)] with ε hε
      symm
      exact indicator_of_mem (show x ∈ (ball (0:Vec) ε)ᶜ by
        simp only [mem_compl_iff,mem_ball_zero_iff]; exact not_lt_of_ge hε.2.le) F
  simpa only [setIntegral_indicator measurableSet_ball.compl,sdiff_eq_compl_inter,inter_comm] using ht

lemma divergence_ball_singular {R T : ℝ} (hR : 0<R) (hRT : R<T)
    {F : Vec → Vec} (hF : ∀ x, 0<‖x‖ → ‖x‖<T → ContDiffAt ℝ 1 F x)
    (hi : IntegrableOn (divergence F) (ball (0:Vec) R))
    (hzero : Tendsto (fun ε : ℝ => ∫ n : Sphere,
      ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure) (𝓝[>] (0:ℝ)) (𝓝 0)) :
    (∫ x in ball (0:Vec) R, divergence F x) =
      ∫ n : Sphere, R^2*dot n.1 (F (R • n.1)) ∂sphereMeasure := by
  have he : (fun ε : ℝ => ∫ x in ball (0:Vec) R \ ball (0:Vec) ε, divergence F x) =ᶠ[𝓝[>] 0]
      (fun ε => (∫ n : Sphere, R^2*dot n.1 (F (R • n.1)) ∂sphereMeasure) -
        (∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure)) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    exact divergence_annulus_local hε.1 hε.2.le hRT hF
  apply tendsto_nhds_unique (integral_annulus_tendsto hi)
  simpa only [sub_zero] using (tendsto_const_nhds.sub hzero).congr' he.symm

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SphericalFluxNorm
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

lemma spherical_flux_norm_le {F : Vec → Vec} {ε C : ℝ} (hε : 0<ε)
    (hF : ∀ z : Vec, ‖z‖=ε → ‖F z‖≤C/ε) :
    ‖∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure‖ ≤ C*ε*(4*Real.pi) := by
  have hb (n : Sphere) : ‖ε^2*dot n.1 (F (ε • n.1))‖≤C*ε := by
    have hn : ‖ε • n.1‖=ε := by rw [norm_smul,Real.norm_of_nonneg hε.le,sphere_norm,mul_one]
    have hd : ‖dot n.1 (F (ε • n.1))‖≤C/ε := by
      calc
        _ ≤ ‖n.1‖*‖F (ε • n.1)‖ := by
          simpa only [dot_eq_inner,Real.norm_eq_abs] using abs_real_inner_le_norm (n.1 : Vec) (F (ε • n.1))
        _ ≤ C/ε := by rw [sphere_norm,one_mul]; exact hF _ hn
    rw [norm_mul,Real.norm_of_nonneg (sq_nonneg ε)]
    calc
      ε^2*‖dot n.1 (F (ε • n.1))‖≤ε^2*(C/ε) := mul_le_mul_of_nonneg_left hd (sq_nonneg ε)
      _ = C*ε := by field_simp [hε.ne']
  simpa only [sphere_area] using (norm_integral_le_of_norm_le_const (μ := sphereMeasure) (ae_of_all _ hb))

lemma spherical_flux_tendsto_zero {F : Vec → Vec} {R C : ℝ} (hR : 0<R)
    (hF : ∀ z : Vec, 0<‖z‖ → ‖z‖<R → ‖F z‖≤C/‖z‖) :
    Tendsto (fun ε : ℝ => ∫ n : Sphere, ε^2*dot n.1 (F (ε • n.1)) ∂sphereMeasure)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm' (a:=fun ε => C*ε*(4*Real.pi))
  · filter_upwards [Ioo_mem_nhdsGT hR] with ε hε
    apply spherical_flux_norm_le hε.1
    intro z hz
    simpa only [hz] using hF z (by rw [hz]; exact hε.1) (by rw [hz]; exact hε.2)
  · simpa using ((tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds)).mul_const (4*Real.pi) :
      Tendsto (fun ε : ℝ => C*ε*(4*Real.pi)) (𝓝[>] (0:ℝ)) (𝓝 (C*0*(4*Real.pi))))

lemma fderiv_norm_apply_rvm {z : Vec} (hz : z≠0) (w : Vec) :
    fderiv ℝ (fun y : Vec => ‖y‖) z w=dot z w/‖z‖ := by
  have hc : HasDerivAt (fun r : ℝ => z+r • w) w 0 := by
    have hh := (hasDerivAt_const (0:ℝ) z).add ((hasDerivAt_id (0:ℝ)).smul_const w)
    change HasDerivAt (fun r : ℝ => z+r • w) (0+(1:ℝ) • w) 0 at hh
    simpa only [zero_add,one_smul] using hh
  have hd : HasFDerivAt (fun y : Vec => ‖y‖) (fderiv ℝ (fun y : Vec => ‖y‖) z) (z+(0:ℝ) • w) := by
    simpa using (differentiableAt_id.norm ℝ hz).hasFDerivAt
  have hn := hd.comp_hasDerivAt (0:ℝ) hc
  have hm := hasDerivAt_norm_nonzero hc (by simpa using hz)
  simpa using hn.unique hm

lemma fderiv_conePotential_apply {ρ : ℝ × Vec → ℝ} {t : ℝ} {x z : Vec}
    (hρ : DifferentiableAt ℝ ρ (t-‖z‖,x+z)) (hz : z≠0) (w : Vec) :
    fderiv ℝ (fun y : Vec => ρ (t-‖y‖,x+y)/‖y‖) z w =
      fderiv ℝ ρ (t-‖z‖,x+z) (0,w)/‖z‖ -
      dot z w/‖z‖^2 * dirD ρ (1,0) (t-‖z‖,x+z) -
      dot z w/‖z‖^3 * ρ (t-‖z‖,x+z) := by
  have hn : DifferentiableAt ℝ (fun y : Vec => ‖y‖) z := differentiableAt_id.norm ℝ hz
  have hi := ((hasFDerivAt_const t z).sub hn.hasFDerivAt).prodMk
    ((hasFDerivAt_const x z).add (hasFDerivAt_id z))
  have hp := hρ.hasFDerivAt.comp z hi
  have hh := hp.mul ((hasFDerivAt_inv (norm_ne_zero_iff.mpr hz)).comp z hn.hasFDerivAt)
  change HasFDerivAt (fun y : Vec => ρ (t-‖y‖,x+y)*‖y‖⁻¹) _ z at hh
  simp_rw [div_eq_mul_inv] at ⊢
  rw [hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    add_apply,ContinuousLinearMap.id_apply,
    smul_eq_mul,zero_sub,zero_add,neg_apply,fderiv_norm_apply_rvm hz,ContinuousLinearMap.toSpanSingleton_apply]
  have he : (- (dot z w/‖z‖),w) = ((0:ℝ),w)-(dot z w/‖z‖) • ((1:ℝ),(0:Vec)) := by ext <;> simp
  rw [he,map_sub,map_smul]
  unfold dirD
  simp only [smul_eq_mul,Function.comp_apply,Pi.add_apply,Pi.sub_apply,id_eq]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

lemma divergence_conePotential {ρ : ℝ × Vec → ℝ} {t : ℝ} {x z : Vec}
    (hρ : DifferentiableAt ℝ ρ (t-‖z‖,x+z)) (hz : z≠0) (i : Fin 3) :
    divergence (fun y : Vec => (ρ (t-‖y‖,x+y)/‖y‖) • basis i) z =
      dirD ρ (0,basis i) (t-‖z‖,x+z)/‖z‖ -
      z i/‖z‖^2 * dirD ρ (1,0) (t-‖z‖,x+z) -
      z i/‖z‖^3 * ρ (t-‖z‖,x+z) := by
  have hn : DifferentiableAt ℝ (fun y : Vec => ‖y‖) z := differentiableAt_id.norm ℝ hz
  have harg : DifferentiableAt ℝ (fun y : Vec => (t-‖y‖,x+y)) z :=
    ((differentiableAt_const t).sub hn).prodMk ((differentiableAt_const x).add differentiableAt_id)
  have hg : DifferentiableAt ℝ (fun y : Vec => ρ (t-‖y‖,x+y)/‖y‖) z :=
    by
      have hp : DifferentiableAt ℝ (fun y : Vec => ρ (t-‖y‖,x+y)) z := hρ.comp z harg
      exact (hp.hasFDerivAt.mul ((hasFDerivAt_inv (norm_ne_zero_iff.mpr hz)).comp z hn.hasFDerivAt)).differentiableAt
  rw [divergence_smul hg (differentiableAt_const _),divergence_const_rvm,mul_zero,add_zero,
    dot_gradient_direction,fderiv_conePotential_apply hρ hz]
  simp [dot,basis,dirD]

lemma integrableOn_ball_div_norm_pow {g : Vec → ℝ} (hg : Continuous g)
    (k : ℕ) (hk : k<3) (R : ℝ) :
    IntegrableOn (fun z : Vec => g z/‖z‖^k) (ball (0:Vec) R) := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0:Vec) R).image hg).isBounded.exists_norm_le
  apply integrableOn_ball_of_norm_le_rpow (by simp) (α:=(k:ℝ)) (C:=C) (by simpa using hk)
  · apply ae_restrict_of_forall_mem measurableSet_ball
    intro z hz
    have hh := hC _ ⟨z,ball_subset_closedBall hz,rfl⟩
    rw [norm_div,norm_pow,norm_norm,Real.rpow_neg (norm_nonneg z),Real.rpow_natCast,div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr (pow_nonneg (norm_nonneg z) k))
  · exact (hg.measurable.div (continuous_norm.pow k).measurable).aestronglyMeasurable

lemma norm_direction_coord_le (z : Vec) (i : Fin 3) : ‖z i/‖z‖‖≤1 := by
  by_cases hz : z=0
  · simp [hz]
  rw [norm_div,norm_norm,div_le_one (norm_pos_iff.mpr hz)]
  exact PiLp.norm_apply_le z i

lemma integrableOn_ball_direction_div_norm_pow {g : Vec → ℝ} (hg : Continuous g)
    (k : ℕ) (hk : k<3) (R : ℝ) (i : Fin 3) :
    IntegrableOn (fun z : Vec => z i/‖z‖^(k+1)*g z) (ball (0:Vec) R) := by
  have hm : Measurable (fun z : Vec => z i/‖z‖) := (PiLp.continuous_apply 2 _ i).measurable.div continuous_norm.measurable
  have hi := (integrableOn_ball_div_norm_pow hg k hk R).bdd_mul
    hm.aestronglyMeasurable (ae_of_all _ (fun z => norm_direction_coord_le z i))
  apply hi.congr
  filter_upwards [] with z
  simp only [pow_succ,div_eq_mul_inv,mul_inv_rev]
  ring

lemma contDiffAt_conePotential {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (t : ℝ) (x : Vec) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ ∞ (fun y : Vec => ρ (t-‖y‖,x+y)/‖y‖) z := by
  have hn : ContDiffAt ℝ ∞ (fun y : Vec => ‖y‖) z := contDiffAt_id.norm ℝ hz
  have hp : ContDiffAt ℝ ∞ (fun y : Vec => ρ (t-‖y‖,x+y)) z :=
    hρ.contDiffAt.comp z ((contDiffAt_const.sub hn).prodMk (contDiffAt_const.add contDiffAt_id))
  exact hp.div hn (norm_ne_zero_iff.mpr hz)

lemma integrable_conePotential_divergence {ρ : ℝ × Vec → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (t : ℝ) (x : Vec) (i : Fin 3) :
    IntegrableOn (divergence (fun y : Vec => (ρ (t-‖y‖,x+y)/‖y‖) • basis i))
      (ball (0:Vec) t) := by
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  have hi₁ := integrableOn_ball_div_norm_pow ((contDiff_dirD hρ (0,basis i)).continuous.comp harg)
    1 (by norm_num) t
  have hi₂ := integrableOn_ball_direction_div_norm_pow ((contDiff_dirD hρ (1,0)).continuous.comp harg)
    1 (by norm_num) t i
  have hi₃ := integrableOn_ball_direction_div_norm_pow (hρ.continuous.comp harg) 2 (by norm_num) t i
  apply ((hi₁.sub hi₂).sub hi₃).congr
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz
  simpa only [pow_one,Function.comp_apply,Pi.sub_apply] using
    (divergence_conePotential (hρ.differentiable (by simp) _) hz i).symm

lemma conePotential_tip_flux {ρ : ℝ × Vec → ℝ} (hρ : Continuous ρ)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    Tendsto (fun ε : ℝ => ∫ n : Sphere, ε^2*dot n.1
      ((ρ (t-‖ε • n.1‖,x+ε • n.1)/‖ε • n.1‖) • basis i) ∂sphereMeasure)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous (fun z : Vec => ρ (t-‖z‖,x+z)) :=
    hρ.comp ((continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id))
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0:Vec) t).image hc).isBounded.exists_norm_le
  apply spherical_flux_tendsto_zero (F:=fun z : Vec => (ρ (t-‖z‖,x+z)/‖z‖) • basis i)
    (C:=C*‖basis i‖) ht
  intro z hz hzt
  have hh := hC _ ⟨z,(by simpa only [mem_closedBall_zero_iff] using hzt.le),rfl⟩
  rw [norm_smul,norm_div,norm_norm]
  calc
    ‖ρ (t-‖z‖,x+z)‖/‖z‖*‖basis i‖ ≤ C/‖z‖*‖basis i‖ :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hh hz.le) (norm_nonneg _)
    _ = C*‖basis i‖/‖z‖ := by ring

lemma conePotential_spatial_ibp {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) t, dirD ρ (0,basis i) (t-‖z‖,x+z)/‖z‖) =
      (∫ z in ball (0:Vec) t,
        z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z) + z i/‖z‖^3*ρ (t-‖z‖,x+z)) +
      ∫ n : Sphere, t*n.1 i*ρ (0,x+t • n.1) ∂sphereMeasure := by
  have hg := divergence_ball_singular ht (show t<t+1 by linarith)
    (F:=fun z : Vec => (ρ (t-‖z‖,x+z)/‖z‖) • basis i)
    (fun z hz _ => ((contDiffAt_conePotential hρ t x (norm_ne_zero_iff.mp hz.ne')).of_le (by simp)).smul contDiffAt_const)
    (integrable_conePotential_divergence hρ t x i) (conePotential_tip_flux hρ.continuous ht x i)
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  have hi₁ := integrableOn_ball_div_norm_pow ((contDiff_dirD hρ (0,basis i)).continuous.comp harg)
    1 (by norm_num) t
  have hi₂ := integrableOn_ball_direction_div_norm_pow ((contDiff_dirD hρ (1,0)).continuous.comp harg)
    1 (by norm_num) t i
  have hi₃ := integrableOn_ball_direction_div_norm_pow (hρ.continuous.comp harg) 2 (by norm_num) t i
  have he : (∫ z in ball (0:Vec) t, divergence (fun y : Vec => (ρ (t-‖y‖,x+y)/‖y‖) • basis i) z) =
      (∫ z in ball (0:Vec) t, dirD ρ (0,basis i) (t-‖z‖,x+z)/‖z‖) -
      (∫ z in ball (0:Vec) t, z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z)) -
      (∫ z in ball (0:Vec) t, z i/‖z‖^3*ρ (t-‖z‖,x+z)) := by
    rw [← integral_sub (by simpa [IntegrableOn] using hi₁) (by simpa [IntegrableOn] using hi₂),
      ← integral_sub (by simpa [IntegrableOn] using Integrable.sub' hi₁ hi₂) (by simpa [IntegrableOn] using hi₃)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz
    exact divergence_conePotential (hρ.differentiable (by simp) _) hz i
  have hb : (∫ n : Sphere, t^2*dot n.1 ((ρ (t-‖t • n.1‖,x+t • n.1)/‖t • n.1‖) • basis i) ∂sphereMeasure) =
      ∫ n : Sphere, t*n.1 i*ρ (0,x+t • n.1) ∂sphereMeasure := by
    apply integral_congr_ae
    filter_upwards [] with n
    have hn : ‖t • n.1‖=t := by rw [norm_smul,Real.norm_of_nonneg ht.le,sphere_norm,mul_one]
    rw [hn,sub_self,dot_smul_right]
    have hd : dot n.1 (basis i)=n.1 i := by simp [dot,basis]
    rw [hd]
    field_simp
  rw [he,hb] at hg
  rw [integral_add (by simpa [IntegrableOn] using hi₂) (by simpa [IntegrableOn] using hi₃)]
  linarith
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

lemma sourceWave_spatial_ibp {ρ : ℝ × Vec → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    sourceWave (dirD ρ (0,basis i)) (t,x) = (4*Real.pi)⁻¹ *
      ((∫ z in ball (0:Vec) t,
        z i/‖z‖^2*dirD ρ (1,0) (t-‖z‖,x+z) + z i/‖z‖^3*ρ (t-‖z‖,x+z)) +
      ∫ n : Sphere, t*n.1 i*ρ (0,x+t • n.1) ∂sphereMeasure) := by
  rw [sourceWave_ball (contDiff_dirD hρ _).continuous ht.le x,conePotential_spatial_ibp hρ ht]

lemma magneticPotentialComponent_ball {j : Field} (hj : ContDiff ℝ ∞ j)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticPotentialComponent j i (t,x) =
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) t,
        z (curlA i)/‖z‖^2*dirD (fun p => j p (curlB i)) (1,0) (t-‖z‖,x+z) +
        z (curlA i)/‖z‖^3*j (t-‖z‖,x+z) (curlB i) -
        (z (curlB i)/‖z‖^2*dirD (fun p => j p (curlA i)) (1,0) (t-‖z‖,x+z) +
        z (curlB i)/‖z‖^3*j (t-‖z‖,x+z) (curlA i))) +
      (4*Real.pi)⁻¹ * (∫ n : Sphere,
        t*n.1 (curlA i)*j (0,x+t • n.1) (curlB i) -
        t*n.1 (curlB i)*j (0,x+t • n.1) (curlA i) ∂sphereMeasure) := by
  rw [magneticPotentialComponent_source hj,
    sourceWave_spatial_ibp (contDiff_component hj _) ht,
    sourceWave_spatial_ibp (contDiff_component hj _) ht]
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  have hi (a b : Fin 3) : IntegrableOn (fun z : Vec =>
      z a/‖z‖^2*dirD (fun p => j p b) (1,0) (t-‖z‖,x+z) +
      z a/‖z‖^3*j (t-‖z‖,x+z) b) (ball (0:Vec) t) :=
    Integrable.add (integrableOn_ball_direction_div_norm_pow
      ((contDiff_dirD (contDiff_component hj b) _).continuous.comp harg) 1 (by norm_num) t a)
      (integrableOn_ball_direction_div_norm_pow
        ((contDiff_component hj b).continuous.comp harg) 2 (by norm_num) t a)
  have hb (a b : Fin 3) : Integrable (fun n : Sphere => t*n.1 a*j (0,x+t • n.1) b) sphereMeasure := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (continuous_const.mul ((PiLp.continuous_apply 2 _ a).comp continuous_subtype_val)).mul
        ((contDiff_component hj b).continuous.comp
          ((continuous_const : Continuous (fun _ : Sphere => (0:ℝ))).prodMk
            (continuous_const.add ((continuous_const : Continuous (fun _ : Sphere => t)).smul
              (continuous_subtype_val : Continuous (fun n : Sphere => (n.1 : Vec)))))))
    · exact HasCompactSupport.of_compactSpace _
  rw [integral_sub (hi _ _) (hi _ _),integral_sub (hb _ _) (hb _ _)]
  ring

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PositiveExtension
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

section PositiveExtension
variable {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma contDiff_positiveTimeCut (a : ℝ) : ContDiff ℝ ∞ (positiveTimeCut a) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (a/4))
lemma positiveTimeCut_zero {a t : ℝ} (ha : 0<a) (ht : t≤a/4) : positiveTimeCut a t=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (by positivity))
lemma positiveTimeCut_one {a t : ℝ} (ha : 0<a) (ht : a/2≤t) : positiveTimeCut a t=1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ (by positivity : 0<a/4)).mpr
  linarith

lemma contDiff_positiveTimeExtend {a : ℝ} (ha : 0<a) {F : ℝ × H → W}
    (hF : ∀ p, 0<p.1 → ContDiffAt ℝ ∞ F p) : ContDiff ℝ ∞ (positiveTimeExtend a F) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0<p.1
  · exact ((contDiff_positiveTimeCut a).comp contDiff_fst).contDiffAt.smul (hF p hp)
  · have he : positiveTimeExtend a F =ᶠ[𝓝 p] (fun _ => 0) := by
      have hnh : {q : ℝ × H | q.1<a/4} ∈ 𝓝 p :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds (show p.1<a/4 by linarith)
      filter_upwards [hnh] with q hq
      simp only [positiveTimeExtend,positiveTimeCut_zero ha hq.le,zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq he

omit [NormedSpace ℝ H] in
lemma positiveTimeExtend_eventually_eq {a : ℝ} (ha : 0<a) (F : ℝ × H → W)
    {p : ℝ × H} (hp : a/2<p.1) : positiveTimeExtend a F =ᶠ[𝓝 p] F := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
  simp only [positiveTimeExtend,positiveTimeCut_one ha hq.le,one_smul]

lemma contDiff_positiveTimeShift {a : ℝ} (ha : 0<a) {F : ℝ × H → W}
    (hF : ∀ p, 0<p.1 → ContDiffAt ℝ ∞ F p) : ContDiff ℝ ∞ (positiveTimeShift a F) :=
  (contDiff_positiveTimeExtend ha hF).comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
lemma positiveTimeShift_eq {a t : ℝ} (ha : 0<a) (ht : 0≤t) (F : ℝ × H → W) (x : H) :
    positiveTimeShift a F (t,x)=F (a+t,x) := by
  change positiveTimeCut a (a+t) • F (a+t,x)=_
  rw [positiveTimeCut_one ha (by linarith),one_smul]

lemma fderiv_positiveTimeShift {a t : ℝ} (ha : 0<a) (ht : 0≤t) {F : ℝ × H → W} (x : H)
    (hF : DifferentiableAt ℝ F (a+t,x)) :
    fderiv ℝ (positiveTimeShift a F) (t,x)=fderiv ℝ F (a+t,x) := by
  have he := positiveTimeExtend_eventually_eq ha F (show a/2<(a+t,x).1 by dsimp; linarith)
  have hD : HasFDerivAt (fun p : ℝ × H => (a+p.1,p.2)) (ContinuousLinearMap.id ℝ (ℝ × H)) (t,x) := by
    simpa only [Prod.add_def,zero_add,id_eq] using
      (hasFDerivAt_id (𝕜:=ℝ) (t,x)).const_add (a,0)
  have hP : DifferentiableAt ℝ (positiveTimeExtend a F) (a+t,x) := hF.congr_of_eventuallyEq he
  have h := hP.hasFDerivAt.comp (t,x) hD
  change HasFDerivAt (positiveTimeShift a F) _ (t,x) at h
  rw [h.fderiv,he.fderiv_eq]
  simp

end PositiveExtension

lemma SmoothOnFiniteHorizons.field_positive {s : Solution} (hs : SmoothOnFiniteHorizons s)
    {p : ℝ × Vec} (hp : 0<p.1) : ContDiffAt ℝ ∞ s.E p ∧ ContDiffAt ℝ ∞ s.B p := by
  have hT : 0≤p.1+1 := by linarith
  have hn : fieldSlab (p.1+1) ∈ 𝓝 p := by
    have hnh : {q : ℝ × Vec | q.1 ∈ Ioo 0 (p.1+1)} ∈ 𝓝 p :=
      (isOpen_Ioo.preimage continuous_fst).mem_nhds ⟨hp,by linarith⟩
    exact mem_of_superset hnh (fun q hq => ⟨hq.1.le,hq.2.le⟩)
  exact ⟨(hs _ hT).2.1.contDiffAt hn,(hs _ hT).2.2.contDiffAt hn⟩

lemma SmoothOnFiniteHorizons.particle_positive {s : Solution} (hs : SmoothOnFiniteHorizons s)
    {p : ℝ × Phase} (hp : 0<p.1) : ContDiffAt ℝ ∞ s.f p := by
  have hT : 0≤p.1+1 := by linarith
  apply (hs _ hT).1.contDiffAt
  exact mem_of_superset ((isOpen_Ioo.preimage (continuous_fst : Continuous (Prod.fst : ℝ × Phase → ℝ))).mem_nhds
    (show p.1 ∈ Ioo 0 (p.1+1) from ⟨hp,by linarith⟩)) (fun q hq => ⟨hq.1.le,hq.2.le⟩)

lemma SmoothOnFiniteHorizons.moments_positive {s : Solution} (hs : SmoothOnFiniteHorizons s)
    (hc : CompactOnFiniteHorizons s) {p : ℝ × Vec} (hp : 0<p.1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × Vec => rho (fun z => s.f (q.1,z)) q.2) p ∧
    ContDiffAt ℝ ∞ (fun q : ℝ × Vec => current (fun z => s.f (q.1,z)) q.2) p := by
  let U : Set (ℝ × Vec) := {q | q.1 ∈ Ioo 0 (p.1+1)}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
  have hpU : p ∈ U := ⟨hp,by linarith⟩
  have hT : 0≤p.1+1 := by linarith
  obtain ⟨K,hK,hz⟩ := hc _ hT
  have hF : ContDiffOn ℝ ∞ (particleBySpacetime s.f) (U ×ˢ (univ : Set Vec)) := by
    intro z hz'
    apply (hs.particle_positive hz'.1.1).comp (f:=fun w : (ℝ × Vec) × Vec => (w.1.1,w.1.2,w.2)) z
      ((contDiff_reassociate).contDiffAt) |>.contDiffWithinAt
  have hzero : ∀ q ∈ U, ∀ v ∉ Prod.snd '' K, particleBySpacetime s.f (q,v)=0 := by
    intro q hq v hv
    by_contra hne
    exact hv ⟨(q.2,v),hz q.1 ⟨hq.1.le,hq.2.le⟩ (subset_tsupport _ hne),rfl⟩
  have hr := contDiffOn_integral_uniform_support hU (hK.image continuous_snd) hF hzero
  have hJ : ContDiffOn ℝ ∞ (fun z : (ℝ × Vec) × Vec => particleBySpacetime s.f z • velocity z.2)
      (U ×ˢ univ) := hF.smul ((contDiff_velocity.comp contDiff_snd).contDiffOn)
  have hzeroJ : ∀ q ∈ U, ∀ v ∉ Prod.snd '' K, particleBySpacetime s.f (q,v) • velocity v=0 := by
    intro q hq v hv
    rw [hzero q hq v hv,zero_smul]
  have hj := contDiffOn_integral_uniform_support hU (hK.image continuous_snd) hJ hzeroJ
  exact ⟨hr.contDiffAt (hU.mem_nhds hpU),hj.contDiffAt (hU.mem_nhds hpU)⟩

lemma spaceCurl_positiveTimeShift {a t : ℝ} (ha : 0<a) (ht : 0≤t) {F : Field}
    (hF : ∀ p, 0<p.1 → ContDiffAt ℝ ∞ F p) (x : Vec) :
    spaceCurl (positiveTimeShift a F) (t,x)=curl (fun y => F (a+t,y)) x := by
  rw [spaceCurl_slice ((contDiff_positiveTimeShift ha hF).differentiable (by simp))]
  congr 1
  funext y
  exact positiveTimeShift_eq ha ht F y

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_EquationsBefore
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
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma classical_positiveTimeShift_maxwell_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a t : ℝ}
    (ha : 0<a) (ht : 0≤t) (hH : a+t < H) (x : Vec) :
    dirD (positiveTimeShift a s.E) (1,0) (t,x)=
      spaceCurl (positiveTimeShift a s.B) (t,x)-
        positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2) (t,x) ∧
    dirD (positiveTimeShift a s.B) (1,0) (t,x) =
      -spaceCurl (positiveTimeShift a s.E) (t,x) ∧
    divergence (fun y => positiveTimeShift a s.E (t,y)) x =
      positiveTimeShift a (fun p : ℝ × Vec => rho (fun z => s.f (p.1,z)) p.2) (t,x) ∧
    divergence (fun y => positiveTimeShift a s.B (t,y)) x = 0 := by
  have hat : 0<a+t := by linarith
  have heq := hs.2.2.2.2.2.2.2.1 (a+t) hat.le hH
  have hE := field_differentiableAt_positive hs.2.1 hat x
  have hB := field_differentiableAt_positive hs.2.2.1 hat x
  have he := heq.2.1 x
  have hb := heq.2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hat),deriv_time_slice hE] at he
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hat),deriv_time_slice hB] at hb
  have hcE := spaceCurl_positiveTimeShift ha ht (fun p hp => (hm.field_positive hp).1) x
  have hcB := spaceCurl_positiveTimeShift ha ht (fun p hp => (hm.field_positive hp).2) x
  have hsE : (fun y => positiveTimeShift a s.E (t,y))=(fun y => s.E (a+t,y)) :=
    funext (positiveTimeShift_eq ha ht s.E)
  have hsB : (fun y => positiveTimeShift a s.B (t,y))=(fun y => s.B (a+t,y)) :=
    funext (positiveTimeShift_eq ha ht s.B)
  refine ⟨?_,?_,?_,?_⟩
  · unfold dirD
    rw [fderiv_positiveTimeShift ha ht x hE,hcB,positiveTimeShift_eq ha ht]
    exact (sub_eq_iff_eq_add.mp he).trans (by abel)
  · unfold dirD
    rw [fderiv_positiveTimeShift ha ht x hB,hcE]
    exact eq_neg_of_add_eq_zero_left hb
  · rw [hsE,positiveTimeShift_eq ha ht]
    exact heq.2.2.2.1 x
  · rw [hsB]
    exact heq.2.2.2.2 x

lemma classical_shifted_magnetic_potential_representation_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0≤T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    s.B (a+T,x) i =
      freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T,x) +
      magneticPotentialComponent
        (positiveTimeShift a (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2)) i (T,x) := by
  have hE := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).1)
  have hB := contDiff_positiveTimeShift ha (fun p hp => (hm.field_positive hp).2)
  have hj := contDiff_positiveTimeShift ha (fun p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).2)
  have hh := maxwell_magnetic_potential_representation hE hB hj hT
    (fun r hr y => (classical_positiveTimeShift_maxwell_before hs hm ha hr.1.le (by linarith [hr.2]) y).1)
    (fun r hr y => (classical_positiveTimeShift_maxwell_before hs hm ha hr.1 (by linarith [hr.2]) y).2.1)
    (fun r hr y => (classical_positiveTimeShift_maxwell_before hs hm ha hr.1.le (by linarith [hr.2]) y).2.2.2) x i
  rw [positiveTimeShift_eq ha hT] at hh
  simpa only [positiveTimeShift_eq ha (le_refl 0),add_zero,
    spaceCurl_positiveTimeShift ha (le_refl 0) (fun p hp => (hm.field_positive hp).1)] using hh

lemma contDiff_shifted_moments_before {d : Datum} {s : Solution} {H : ℝ} (hs : ClassicalBefore d s H)
    (hm : SmoothOnFiniteHorizons s) {a : ℝ} (ha : 0<a) :
    ContDiff ℝ ∞ (shiftedRho s a) ∧ ContDiff ℝ ∞ (shiftedCurrent s a) :=
  ⟨contDiff_positiveTimeShift ha (fun _p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).1),
   contDiff_positiveTimeShift ha (fun _p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).2)⟩

lemma classical_shifted_magnetic_physical_representation_before_oai {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    s.B (a+T,x) i =
      freeWave (fun y => s.B (a,y) i) (fun y => -curl (fun z => s.E (a,z)) y i) (T,x) +
      (4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      (4*Real.pi)⁻¹ * (∫ n : Sphere, T^2*dot n.1
        (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure) +
      (4*Real.pi)⁻¹ * (∫ n : Sphere,
        T*n.1 (curlA i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlB i) -
        T*n.1 (curlB i)*current (fun z => s.f (a,z)) (x+T • n.1) (curlA i) ∂sphereMeasure) := by
  have hρj := contDiff_shifted_moments_before hs hm ha
  rw [classical_shifted_magnetic_potential_representation_before hs hm ha hT.le hH x i]
  change _ + magneticPotentialComponent (shiftedCurrent s a) i (T,x)=_
  rw [magneticPotentialComponent_ball hρj.2 hT]
  change _ + ((4*Real.pi)⁻¹ * (∫ z in ball (0:Vec) T,
      magneticMomentDensity (shiftedCurrent s a) T x i z) + _)=_
  rw [integrated_magneticMomentDensity_actual_before hs hm ha hT hH x i]
  have hj0 (y : Vec) : shiftedCurrent s a (0,y)=current (fun z => s.f (a,z)) y := by
    simp only [shiftedCurrent,positiveTimeShift_eq ha (le_refl 0),add_zero]
  simp_rw [hj0]
  ring

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.classical_shifted_magnetic_physical_representation_before_oai := @OAI.RVM.classical_shifted_magnetic_physical_representation_before_oai
