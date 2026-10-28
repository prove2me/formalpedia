-- Prove2me | solution 1 for OAI.RVM.electric_source_deriv_volterra_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:21:10.349773+00:00
-- url     : https://prove2.me/submissions/fa906478-71e7-49d6-9528-5799732a457a

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

lemma dot_add_left (a b c : Vec) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_add_right (a b c : Vec) : dot a (b + c) = dot a b + dot a c := by
  rw [dot_comm, dot_add_left, dot_comm b a, dot_comm c a]

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

lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma full_directional_derivative {f : Particle} {t : ℝ} {x v u K : Vec}
    (hf : DifferentiableAt ℝ f (t,x,v)) :
    fderiv ℝ f (t,x,v) (1,u,K) =
      deriv (fun t' => f (t',x,v)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,v)) x i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,x,v')) v i) := by
  let L := fderiv ℝ f (t,x,v)
  have hT := hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (x,v)))
  have hιX : HasFDerivAt (fun y : Vec => (t,y,v))
      ((0 : Vec →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Vec).prod 0)) x := by
    exact (hasFDerivAt_const t x).prodMk
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const v x))
  have hιV : HasFDerivAt (fun y : Vec => (t,x,y))
      ((0 : Vec →L[ℝ] ℝ).prod ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec))) v := by
    exact (hasFDerivAt_const t v).prodMk
      ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))
  have hX := hf.hasFDerivAt.comp x hιX
  have hV := hf.hasFDerivAt.comp v hιV
  have ht : deriv (fun t' => f (t',x,v)) t = L (1,0,0) := by
    convert hT.deriv using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hx : fderiv ℝ (fun y => f (t,y,v)) x u = L (0,u,0) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F u) hX.fderiv
    convert h using 1 <;> rfl
  have hv : fderiv ℝ (fun v' => f (t,x,v')) v K = L (0,0,K) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F K) hV.fderiv
    convert h using 1 <;> rfl
  change L (1,u,K) = deriv (fun t' => f (t',x,v)) t +
    (∑ i : Fin 3, u i * fderiv ℝ (fun y => f (t,y,v)) x (basis i)) +
    (∑ i : Fin 3, K i * fderiv ℝ (fun v' => f (t,x,v')) v (basis i))
  rw [← clm_sum_basis, ← clm_sum_basis, ht, hx, hv]
  rw [← map_add, ← map_add]
  congr 1
  ext <;> simp

lemma particle_differentiableAt_positive {s : Solution}
    (hreg : ContDiffOn ℝ 1 s.f particleHalfSpace) {t : ℝ} (ht : 0 < t) (x v : Vec) :
    DifferentiableAt ℝ s.f (t,x,v) := by
  have hnhds : particleHalfSpace ∈ nhds (t,x,v) := by
    have hopen : IsOpen {z : ℝ × Phase | 0 < z.1} :=
      isOpen_lt continuous_const continuous_fst
    apply Filter.mem_of_superset (hopen.mem_nhds ht)
    intro z hz
    change 0 ≤ z.1
    exact le_of_lt hz
  exact ((hreg (t,x,v) ht.le).contDiffAt hnhds).differentiableAt (by norm_num)

lemma spatialPartial_mul {f g : Vec → ℝ} {x : Vec}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    spatialPartial (fun y => f y*g y) x i =
      f x*spatialPartial g x i+g x*spatialPartial f x i := by
  change fderiv ℝ (f*g) x (basis i) = _
  rw [fderiv_mul hf hg]
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

lemma integral_directional_derivative_zero {g : Vec → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (v : Vec) :
    (∫ x, fderiv ℝ g x v) = 0 := by
  have hid : Integrable (fun x => fderiv ℝ g x v) :=
    ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Vec)) (f := fun _ => (1 : ℝ)) (g := g) (v := v)
    (by simp)
    (by simpa using hid)
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const 1)
    (fun x _ => hg.differentiable (by simp) x)
  simpa using h

lemma integral_divergence_zero {F : Vec → Vec}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    (∫ x, divergence F x) = 0 := by
  have hfi (i : Fin 3) : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  have hci (i : Fin 3) : HasCompactSupport (fun x => F x i) := by
    exact hc.comp_left (g := fun v : Vec => v i) (by simp)
  have hi (i : Fin 3) : Integrable (fun x => spatialPartial (fun y => F y i) x i) :=
    (((hfi i).continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      ((hci i).fderiv_apply ℝ (basis i))
  rw [show (fun x => divergence F x) =
    (fun x => ∑ i : Fin 3, spatialPartial (fun y => F y i) x i) from rfl,
    integral_finsetSum _ (fun i _ => hi i)]
  simp only [spatialPartial, integral_directional_derivative_zero (hfi _) (hci _),
    Finset.sum_const_zero]

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

lemma fderiv_particleBySpacetime {f : Particle} {t : ℝ} {x v u K : Vec}
    (hf : DifferentiableAt ℝ f (t,x,v)) :
    fderiv ℝ (particleBySpacetime f) ((t,x),v) ((1,u),K) =
      fderiv ℝ f (t,x,v) (1,u,K) := by
  let A : ((ℝ × Vec) × Vec) →L[ℝ] (ℝ × Phase) :=
    ((ContinuousLinearMap.fst ℝ ℝ Vec).comp
      (ContinuousLinearMap.fst ℝ (ℝ × Vec) Vec)).prod
      (((ContinuousLinearMap.snd ℝ ℝ Vec).comp
        (ContinuousLinearMap.fst ℝ (ℝ × Vec) Vec)).prod
          (ContinuousLinearMap.snd ℝ (ℝ × Vec) Vec))
  have hA : HasFDerivAt (fun z : (ℝ × Vec) × Vec => (z.1.1,z.1.2,z.2)) A
      ((t,x),v) :=
    hasFDerivAt_fst.fst.prodMk (hasFDerivAt_fst.snd.prodMk hasFDerivAt_snd)
  have he := congrArg (fun L : ((ℝ × Vec) × Vec) →L[ℝ] ℝ => L ((1,u),K))
    (hf.hasFDerivAt.comp ((t,x),v) hA).fderiv
  exact he

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

lemma integral_vec_apply {g : Vec → Vec} (hg : Integrable g) (i : Fin 3) :
    (∫ v : Vec, g v) i = ∫ v : Vec, g v i := by
  exact ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hg).symm

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

lemma deriv_transition_nonneg (u : ℝ) : 0 ≤ deriv Real.smoothTransition u :=
  Real.smoothTransition.monotone.deriv_nonneg

lemma deriv_transition_zero_neg {u : ℝ} (hu : u < 0) :
    deriv Real.smoothTransition u = 0 := by
  have he : Real.smoothTransition =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
    filter_upwards [gt_mem_nhds hu] with v hv
    exact Real.smoothTransition.zero_of_nonpos hv.le
  rw [he.deriv_eq,deriv_const]

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

lemma gradient_apply (g : Vec → ℝ) (x : Vec) (i : Fin 3) :
    gradient g x i = spatialPartial g x i := by
  have h := inner_gradient_left (𝕜:=ℝ) (f:=g) (x:=x) (y:=basis i)
  rw [← dot_eq_inner] at h
  simpa [dot,basis,spatialPartial] using h

lemma sphere_area : sphereMeasure.real univ = 4*Real.pi := by
  rw [sphereMeasure,Measure.toSphere_real_apply_univ]
  simp only [Vec,finrank_euclideanSpace,Measure.real,EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  norm_num
  ring

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


lemma integrableOn_norm_rpow_neg {α R : ℝ} (hα : α<3) :
    IntegrableOn (fun z : Vec => ‖z‖ ^ (-α)) (ball (0:Vec) R) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp) (C:=1) (α:=α) (by simpa using hα)
  · exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]; simp)
  · exact (continuous_norm.measurable.pow measurable_const).aestronglyMeasurable

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

lemma coneDirection_norm {x y : Vec} (h : x≠y) : ‖coneDirection x y‖=1 := by
  have hr : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  simp [coneDirection,coneRadius,norm_smul,hr.ne']

lemma hasDerivAt_coneRadius {Y : ℝ → Vec} {u x : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h : x≠Y s) :
    HasDerivAt (coneRadius x ∘ Y) (-dot (coneDirection x (Y s)) u) s := by
  have hh := hasDerivAt_norm_nonzero ((hasDerivAt_const s x).sub hY)
    (sub_ne_zero.mpr h)
  convert hh using 1
  · rfl
  · simp only [coneDirection,coneRadius,dot_smul_left,zero_sub,Pi.sub_apply]
    simp only [dot,PiLp.neg_apply,mul_neg,Finset.sum_neg_distrib]
    ring

lemma retarded_transport_chain {f : Particle} {x y v u K : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y) :
    fderiv ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v) (u,K) =
      fderiv ℝ f (t-coneRadius x y,y,v) (dot (coneDirection x y) u,u,K) := by
  let Y : ℝ → Vec := fun s => y+s • u
  let V : ℝ → Vec := fun s => v+s • K
  have hY : HasDerivAt Y u 0 := by
    have hh := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const u)
    change HasDerivAt Y (0+(1:ℝ) • u) 0 at hh
    simpa only [zero_add,one_smul] using hh
  have hV : HasDerivAt V K 0 := by
    have hh := (hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const K)
    change HasDerivAt V (0+(1:ℝ) • K) 0 at hh
    simpa only [zero_add,one_smul] using hh
  have hr := hasDerivAt_coneRadius hY (by simpa [Y] using hxy)
  have hc := ((hasDerivAt_const (0:ℝ) t).sub hr).prodMk (hY.prodMk hV)
  have hf' : HasFDerivAt f (fderiv ℝ f (t-coneRadius x y,y,v))
      (t-coneRadius x (Y 0),Y 0,V 0) := by simpa only [Y,V,zero_smul,add_zero] using hf.hasFDerivAt
  have hh := hf'.comp_hasDerivAt (0:ℝ) hc
  have hinner : DifferentiableAt ℝ (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) := by
    refine ((differentiableAt_const t).sub ?_).prodMk differentiableAt_id
    exact ((differentiableAt_const x).sub differentiableAt_fst).norm ℝ (sub_ne_zero.mpr hxy)
  have houter := hf.comp (f := fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hinner
  have ho' : HasFDerivAt (fun z : Phase => f (t-coneRadius x z.1,z))
      (fderiv ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v)) (Y 0,V 0) := by
    convert houter.hasFDerivAt using 1 <;> try rfl
    simp only [Y,V,zero_smul,add_zero]
  have hh' := ho'.comp_hasDerivAt (0:ℝ) (hY.prodMk hV)
  have he := hh'.unique hh
  simpa only [Y,V,zero_smul,add_zero,zero_sub,neg_neg] using he

lemma dot_gradient_direction (g : Vec → ℝ) (y w : Vec) :
    dot (gradient g y) w=fderiv ℝ g y w := by
  rw [dot_comm,clm_sum_basis]
  simp only [dot,gradient_apply,spatialPartial]

lemma fderiv_phase_split {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : Phase → H} {y v u K : Vec} (hg : DifferentiableAt ℝ g (y,v)) :
    fderiv ℝ (fun z => g (z,v)) y u+fderiv ℝ (fun w => g (y,w)) v K =
      fderiv ℝ g (y,v) (u,K) := by
  have hiy : HasFDerivAt (fun z : Vec => (z,v))
      ((ContinuousLinearMap.id ℝ Vec).prod (0 : Vec →L[ℝ] Vec)) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y)
  have hiv : HasFDerivAt (fun w : Vec => (y,w))
      ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec)) v :=
    (hasFDerivAt_const y v).prodMk (hasFDerivAt_id v)
  have hy := hg.hasFDerivAt.comp y hiy
  have hv := hg.hasFDerivAt.comp v hiv
  have hy' : fderiv ℝ (fun z => g (z,v)) y u=fderiv ℝ g (y,v) (u,0) := by
    convert congrArg (fun L : Vec →L[ℝ] H => L u) hy.fderiv using 1 <;> rfl
  have hv' : fderiv ℝ (fun w => g (y,w)) v K=fderiv ℝ g (y,v) (0,K) := by
    convert congrArg (fun L : Vec →L[ℝ] H => L K) hv.fderiv using 1 <;> rfl
  rw [hy',hv']
  rw [← map_add]
  congr 1
  ext <;> simp

lemma differentiableAt_coneRadius {x y : Vec} (h : x≠y) :
    DifferentiableAt ℝ (coneRadius x) y :=
  ((differentiableAt_const x).sub differentiableAt_id).norm ℝ (sub_ne_zero.mpr h)

lemma differentiableAt_coneDirection {x y : Vec} (h : x≠y) :
    DifferentiableAt ℝ (coneDirection x) y :=
  ((differentiableAt_coneRadius h).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))).smul
    ((differentiableAt_const x).sub differentiableAt_id)

lemma fderiv_vec_component_at {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : H → Vec} {z e : H} (hg : DifferentiableAt ℝ g z) (i : Fin 3) :
    fderiv ℝ (fun w => g w i) z e=(fderiv ℝ g z e) i := by
  have h := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp z hg.hasFDerivAt
  convert congrArg (fun L : H →L[ℝ] ℝ => L e) h.fderiv using 1 <;> rfl

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


lemma contDiff_dot_pair {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : Vec × Vec => dot z.1 z.2) := by
  unfold dot
  fun_prop

lemma integrable_divergence_compact {F : Vec → Vec}
    (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) : Integrable (divergence F) := by
  apply (continuous_divergence hF).integrable_of_hasCompactSupport
  change HasCompactSupport (∑ i : Fin 3, fun x => spatialPartial (fun y => F y i) x i)
  apply HasCompactSupport.finset_sum
  intro i _
  exact (hc.comp_left (g:=fun v : Vec => v i) (by simp)).fderiv_apply ℝ (basis i)

lemma divergence_integral_uniform_support
    {U : Set Vec} {K : Set Vec} {F : Phase → Vec} {y : Vec}
    (hU : IsOpen U) (hK : IsCompact K) (hy : y ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hz : ∀ x ∈ U, ∀ v ∉ K, F (x,v)=0) :
    divergence (fun z => ∫ v : Vec, F (z,v)) y =
      ∫ v : Vec, divergence (fun z => F (z,v)) y := by
  have hdiff (v : Vec) : DifferentiableAt ℝ F (y,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).differentiableAt (by simp)
  have hi := (hasFDerivAt_integral_uniform_support hU hK hy hF hz).differentiableAt
  have hc : Continuous (fun v : Vec => fderiv ℝ F (y,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hy,mem_univ _⟩)
  have hcs := compactSupport_param_fderiv hU hK hy hz
  have hint (i : Fin 3) : Integrable (fun v : Vec => fderiv ℝ F (y,v) (basis i,0)) :=
    (hc.clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcs.comp_left (g:=fun L : Phase →L[ℝ] Vec => L (basis i,0)) (by simp))
  have hinti (i : Fin 3) : Integrable (fun v : Vec => (fderiv ℝ F (y,v) (basis i,0)) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp (hint i)
  have hslice (v e : Vec) : fderiv ℝ (fun z => F (z,v)) y e = fderiv ℝ F (y,v) (e,0) := by
    have hm : HasFDerivAt (fun z : Vec => (z,v))
        ((ContinuousLinearMap.id ℝ Vec).prod 0) y :=
      (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y)
    have hh := (hdiff v).hasFDerivAt.comp (f:=fun z : Vec => (z,v)) y hm
    convert congrArg (fun L : Vec →L[ℝ] Vec => L e) hh.fderiv using 1 <;> rfl
  unfold divergence spatialPartial
  simp_rw [fderiv_vec_component_at hi]
  simp_rw [fderiv_integral_uniform_support_apply hU hK hy hF hz,
    integral_vec_apply (hint _)]
  rw [← integral_finsetSum _ (fun i _ => hinti i)]
  apply integral_congr_ae
  filter_upwards [] with v
  apply Finset.sum_congr rfl
  intro i _
  have hsliceD : DifferentiableAt ℝ (fun z => F (z,v)) y :=
    (hdiff v).comp y (differentiableAt_id.prodMk (differentiableAt_const v))
  rw [fderiv_vec_component_at hsliceD,hslice]

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

lemma integrable_spatial_divergence_uniform_support
    {U : Set Vec} {K : Set Vec} {F : Phase → Vec} {y : Vec}
    (hU : IsOpen U) (hK : IsCompact K) (hy : y ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hz : ∀ x ∈ U, ∀ v ∉ K, F (x,v)=0) :
    Integrable (fun v : Vec => divergence (fun z => F (z,v)) y) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (y,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hy,mem_univ _⟩)
  have hcs := compactSupport_param_fderiv hU hK hy hz
  have hint (i : Fin 3) : Integrable (fun v : Vec => (fderiv ℝ F (y,v) (basis i,0)) i) := by
    apply (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
    exact (hc.clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcs.comp_left (g:=fun L : Phase →L[ℝ] Vec => L (basis i,0)) (by simp))
  apply (integrable_finsetSum Finset.univ (fun i _ => hint i)).congr
  filter_upwards [] with v
  unfold divergence spatialPartial
  apply Finset.sum_congr rfl
  intro i _
  have hd : DifferentiableAt ℝ F (y,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).differentiableAt (by simp)
  have hm : HasFDerivAt (fun z : Vec => (z,v)) ((ContinuousLinearMap.id ℝ Vec).prod 0) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y)
  have hh := hd.hasFDerivAt.comp (f:=fun z : Vec => (z,v)) y hm
  have hslice : DifferentiableAt ℝ (fun z => F (z,v)) y := hh.differentiableAt
  rw [fderiv_vec_component_at hslice i]
  change (fderiv ℝ F (y,v) (basis i,0)) i = _
  rw [show fderiv ℝ (fun z => F (z,v)) y =
      (fderiv ℝ F (y,v)).comp ((ContinuousLinearMap.id ℝ Vec).prod 0) from hh.fderiv]
  rfl

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

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma coneSpatialCoefficient_identity {x y : Vec} (hxy : x≠y) (v e : Vec) :
    dot (coneDirection x y) (coneSpatialLift x y v e)=coneSpatialCoefficient x y v e := by
  have hd := (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'
  simp only [coneSpatialLift,dot_add_right,dot_smul_right,coneSpatialCoefficient]
  field_simp
  ring

lemma retarded_spatial_division {f : Particle} {x y v K e : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y)
    (heq : fderiv ℝ f (t-coneRadius x y,y,v) (1,velocity v,K)=0) :
    fderiv ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v)
      (coneSpatialLift x y v e,coneSpatialCoefficient x y v e • K)=
    fderiv ℝ f (t-coneRadius x y,y,v) (0,e,0) := by
  rw [retarded_transport_chain hf hxy,coneSpatialCoefficient_identity hxy]
  have hv : (coneSpatialCoefficient x y v e,coneSpatialLift x y v e,
      coneSpatialCoefficient x y v e • K) =
      ((0:ℝ),e,(0:Vec))+coneSpatialCoefficient x y v e • ((1:ℝ),velocity v,K) := by
    ext <;> simp [coneSpatialLift]
  rw [hv,map_add,map_smul,heq,smul_zero,add_zero]

lemma phase_divergence_split {g : Phase → ℝ} {W V : Phase → Vec} {y v : Vec}
    (hg : DifferentiableAt ℝ g (y,v))
    (hW : DifferentiableAt ℝ W (y,v)) (hV : DifferentiableAt ℝ V (y,v)) :
    divergence (fun z => g (z,v) • W (z,v)) y+
      divergence (fun w => g (y,w) • V (y,w)) v =
      fderiv ℝ g (y,v) (W (y,v),V (y,v))+
      g (y,v)*(divergence (fun z => W (z,v)) y+divergence (fun w => V (y,w)) v) := by
  have hy : DifferentiableAt ℝ (fun z : Vec => (z,v)) y :=
    differentiableAt_id.prodMk (differentiableAt_const v)
  have hv : DifferentiableAt ℝ (fun w : Vec => (y,w)) v :=
    (differentiableAt_const y).prodMk differentiableAt_id
  have hgy : DifferentiableAt ℝ (fun z => g (z,v)) y := hg.comp y hy
  have hWy : DifferentiableAt ℝ (fun z => W (z,v)) y := hW.comp y hy
  have hgv : DifferentiableAt ℝ (fun w => g (y,w)) v := hg.comp v hv
  have hVv : DifferentiableAt ℝ (fun w => V (y,w)) v := hV.comp v hv
  rw [divergence_smul hgy hWy,
    divergence_smul hgv hVv,
    dot_gradient_direction,dot_gradient_direction]
  rw [←fderiv_phase_split hg]
  ring

lemma differentiableAt_coneSpatialCoefficient {x y v e : Vec} (hxy : x≠y) :
    DifferentiableAt ℝ (fun z : Phase => coneSpatialCoefficient x z.1 z.2 e) (y,v) := by
  have hn : DifferentiableAt ℝ (fun z : Phase => coneDirection x z.1) (y,v) :=
    (differentiableAt_coneDirection hxy).comp (f:=fun z : Phase => z.1) (y,v) differentiableAt_fst
  have hu : DifferentiableAt ℝ (fun z : Phase => velocity z.2) (y,v) :=
    (contDiff_velocity.differentiable (by simp : (∞:ℕ∞ω)≠0) v).comp
      (f:=fun z : Phase => z.2) (y,v) differentiableAt_snd
  have he : DifferentiableAt ℝ (fun z : Phase => dot (coneDirection x z.1) e) (y,v) := by
    simpa only [dot_eq_inner] using hn.inner ℝ (differentiableAt_const e)
  have hd : DifferentiableAt ℝ (fun z : Phase => 1-dot (coneDirection x z.1) (velocity z.2)) (y,v) := by
    exact (differentiableAt_const (1:ℝ)).sub (by simpa only [dot_eq_inner] using hn.inner ℝ hu)
  change DifferentiableAt ℝ (fun z : Phase => dot (coneDirection x z.1) e /
    (1-dot (coneDirection x z.1) (velocity z.2))) (y,v)
  convert he.mul (hd.inv (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne') using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma retarded_spatial_divergence {f : Particle} {K : Phase → Vec} {k : Phase → ℝ}
    {x y v e : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y)
    (hK : DifferentiableAt ℝ K (y,v)) (hk : DifferentiableAt ℝ k (y,v))
    (heq : fderiv ℝ f (t-coneRadius x y,y,v) (1,velocity v,K (y,v))=0) :
    k (y,v)*fderiv ℝ f (t-coneRadius x y,y,v) (0,e,0)=
      divergence (fun z => (f (t-coneRadius x z,z,v)*k (z,v)) • coneSpatialLift x z v e) y+
      divergence (fun w => (f (t-coneRadius x y,y,w)*k (y,w)) •
        (coneSpatialCoefficient x y w e • K (y,w))) v-
      f (t-coneRadius x y,y,v)*
        (divergence (fun z => k (z,v) • coneSpatialLift x z v e) y+
          divergence (fun w => k (y,w) • (coneSpatialCoefficient x y w e • K (y,w))) v) := by
  have hi : DifferentiableAt ℝ (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) :=
    ((differentiableAt_const t).sub
      ((differentiableAt_coneRadius hxy).comp (f:=fun z : Phase => z.1) (y,v) differentiableAt_fst)).prodMk differentiableAt_id
  have hg : DifferentiableAt ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v) :=
    hf.comp (f:=fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hi
  have hc := differentiableAt_coneSpatialCoefficient (v:=v) (e:=e) hxy
  have hu : DifferentiableAt ℝ (fun z : Phase => velocity z.2) (y,v) :=
    (contDiff_velocity.differentiable (by simp : (∞:ℕ∞ω)≠0) v).comp
      (f:=fun z : Phase => z.2) (y,v) differentiableAt_snd
  have hW : DifferentiableAt ℝ (fun z : Phase => k z • coneSpatialLift x z.1 z.2 e) (y,v) :=
    hk.smul ((differentiableAt_const e).add (hc.smul hu))
  have hV : DifferentiableAt ℝ (fun z : Phase => k z •
      (coneSpatialCoefficient x z.1 z.2 e • K z)) (y,v) := hk.smul (hc.smul hK)
  have hh := phase_divergence_split hg hW hV
  dsimp only at hh
  have hp : (k (y,v) • coneSpatialLift x y v e,
      k (y,v) • (coneSpatialCoefficient x y v e • K (y,v))) =
      k (y,v) • (coneSpatialLift x y v e,coneSpatialCoefficient x y v e • K (y,v)) := rfl
  rw [hp,map_smul,retarded_spatial_division hf hxy heq] at hh
  simp only [smul_eq_mul] at hh
  simpa only [←smul_smul,smul_eq_mul] using (eq_sub_iff_add_eq.mpr hh.symm)

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

namespace RVM

lemma field_contDiffAt_positive {k : ℕ∞ω} {F : Field}
    (hF : ContDiffOn ℝ k F fieldHalfSpace) {t : ℝ} (ht : 0<t) (x : Vec) :
    ContDiffAt ℝ k F (t,x) := by
  have hn : fieldHalfSpace ∈ 𝓝 (t,x) :=
    mem_of_superset ((isOpen_lt continuous_const
      (continuous_fst : Continuous (Prod.fst : ℝ × Vec → ℝ))).mem_nhds ht)
      (fun p hp => show 0≤p.1 from hp.le)
  exact (hF _ ht.le).contDiffAt hn

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

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_HomogeneousCancellation
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

lemma coneRadius_zero_smul {r : ℝ} (hr : 0 < r) (z : Vec) :
    coneRadius 0 (r • z)=r*coneRadius 0 z := by
  simp only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr]

lemma coneDirection_zero_smul {r : ℝ} (hr : 0 < r) (z : Vec) :
    coneDirection 0 (r • z)=coneDirection 0 z := by
  rw [coneDirection,coneRadius_zero_smul hr,zero_sub,←smul_neg,
    mul_inv_rev,smul_smul]
  rw [mul_assoc,inv_mul_cancel₀ hr.ne',mul_one]
  simp only [coneDirection,zero_sub]

lemma contDiffAt_coneSpatialLift {k : ℕ∞ω} {x y v e : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (fun z : Vec => coneSpatialLift x z v e) y := by
  have hn := contDiffAt_coneDirection (k:=k) hxy
  have hde := contDiff_dot_pair.contDiffAt.comp y (hn.prodMk (contDiffAt_const (c:=e)))
  have hdu := contDiff_dot_pair.contDiffAt.comp y (hn.prodMk (contDiffAt_const (c:=velocity v)))
  have hc : ContDiffAt ℝ k (fun z : Vec => coneSpatialCoefficient x z v e) y :=
    hde.div (contDiffAt_const.sub hdu) (cone_denom_pos v _ (coneDirection_norm hxy)).ne'
  exact contDiffAt_const.add (hc.smul contDiffAt_const)

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

lemma particle_spacetime_vlasov_before {s : Solution} {H : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : EquationsBefore s H)
    {t : ℝ} (ht : 0 < t) (hth : t < H) (x v : Vec) :
    fderiv ℝ (particleBySpacetime s.f) ((t,x),v)
      ((1,velocity v),s.E (t,x) + cross (velocity v) (s.B (t,x))) = 0 := by
  have hd := particle_differentiableAt_positive hf ht x v
  rw [fderiv_particleBySpacetime hd, full_directional_derivative hd]
  have he := (heq t (le_of_lt ht) hth).1 x v
  rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_IntegralBallPolarFlip
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
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma integral_ball_polar_flip {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Vec→W} {R : ℝ} (hg : IntegrableOn g (ball (0:Vec) R)) :
    (∫z in ball (0:Vec) R,g z)=
      ∫n : Sphere,∫r in Ioo (0:ℝ) R,r^2 • g (-(r • n.1)) ∂volume ∂sphereMeasure := by
  classical
  let H := (ball (0:Vec) R).indicator g
  have hi : Integrable H := (integrable_indicator_iff measurableSet_ball).mpr hg
  rw [←integral_indicator measurableSet_ball]
  change (∫z,H z)=_
  rw [←integral_neg_eq_self H volume,integral_polar hi.comp_neg]
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    have he : ∀r∈Ioi (0:ℝ),r^2 • H (-(r • n.1))=
        (Iio R).indicator (fun r=>r^2 • g (-(r • n.1))) r := by
      intro r hr
      have hnorm : ‖-(r • n.1)‖=r := by
        rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr,sphere_norm,mul_one]
      by_cases h : r<R
      · rw [show H (-(r • n.1))=g (-(r • n.1)) from indicator_of_mem
          (show -(r • n.1)∈ball (0:Vec) R by simpa only [mem_ball_zero_iff,hnorm] using h) g,
          indicator_of_mem (show r∈Iio R from h)]
      · rw [show H (-(r • n.1))=0 from indicator_of_notMem
          (show -(r • n.1)∉ball (0:Vec) R by simpa only [mem_ball_zero_iff,hnorm] using h) g,
          smul_zero,indicator_of_notMem (show r∉Iio R from h)]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Iio]
    rfl)

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

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma integral_Icc_sub (H : ℝ → ℝ) {t : ℝ} (ht : 0≤t) :
    (∫ r in Icc (0:ℝ) t, H (t-r))=∫ r in Icc (0:ℝ) t, H r := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht,← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_comp_sub_left]
  simp only [sub_self,sub_zero]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalAngularBound
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

lemma divergence_phase_first {F : Phase → Vec} {p : Phase}
    (hF : DifferentiableAt ℝ F p) :
    divergence (fun z => F (z,p.2)) p.1 =
      ∑ j : Fin 3, (fderiv ℝ F p (basis j,0)) j := by
  have hP := (hasFDerivAt_id (𝕜:=ℝ) p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have hh := hF.hasFDerivAt.comp p.1 hP
  change HasFDerivAt (fun z : Vec => F (z,p.2)) _ p.1 at hh
  unfold divergence spatialPartial
  congr 1
  funext j
  rw [fderiv_vec_component_at hh.differentiableAt j,hh.fderiv]
  rfl

lemma divergence_phase_second {F : Phase → Vec} {p : Phase}
    (hF : DifferentiableAt ℝ F p) :
    divergence (fun z => F (p.1,z)) p.2 =
      ∑ j : Fin 3, (fderiv ℝ F p (0,basis j)) j := by
  have hP := (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id (𝕜:=ℝ) p.2)
  have hh := hF.hasFDerivAt.comp p.2 hP
  change HasFDerivAt (fun z : Vec => F (p.1,z)) _ p.2 at hh
  unfold divergence spatialPartial
  congr 1
  funext j
  rw [fderiv_vec_component_at hh.differentiableAt j,hh.fderiv]
  rfl

lemma continuous_divergence_phase_slices {U : Set Vec} {F : Phase → Vec} {y : Vec}
    (hU : IsOpen U) (hy : y∈U) (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) :
    Continuous (fun v => divergence (fun z => F (z,v)) y) ∧
    Continuous (fun v => divergence (fun z => F (y,z)) v) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (y,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hy,mem_univ _⟩)
  have hd (v : Vec) : DifferentiableAt ℝ F (y,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).differentiableAt (by simp)
  constructor
  · simp_rw [divergence_phase_first (hd _)]
    exact continuous_finsetSum _ (fun j _ =>
      (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp (hc.clm_apply continuous_const))
  · simp_rw [divergence_phase_second (hd _)]
    exact continuous_finsetSum _ (fun j _ =>
      (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp (hc.clm_apply continuous_const))

lemma phase_division_integral {U K : Set Vec} {g : Phase → ℝ} {W V : Phase → Vec}
    {y : Vec} {L : Vec → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hy : y∈U)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ univ))
    (hW : ContDiffOn ℝ 1 W (U ×ˢ univ))
    (hV : ContDiffOn ℝ 1 V (U ×ˢ univ))
    (hz : ∀ z∈U, ∀ v∉K, g (z,v)=0)
    (heq : ∀ v, L v = divergence (fun z => g (z,v) • W (z,v)) y+
      divergence (fun w => g (y,w) • V (y,w)) v-
      g (y,v)*(divergence (fun z => W (z,v)) y+divergence (fun w => V (y,w)) v)) :
    Integrable L ∧ (∫ v, L v) =
      divergence (fun z => ∫ v, g (z,v) • W (z,v)) y-
      ∫ v, g (y,v)*(divergence (fun z => W (z,v)) y+divergence (fun w => V (y,w)) v) := by
  have hgw := hg.smul hW
  have hgV := hg.smul hV
  have hzw : ∀ z∈U, ∀ v∉K, (g (z,v) • W (z,v))=0 := by
    intro z hu v hv
    rw [hz z hu v hv,zero_smul]
  have hsi := integrable_spatial_divergence_uniform_support hU hK hy hgw hzw
  have hse := divergence_integral_uniform_support hU hK hy hgw hzw
  change Integrable (fun v => divergence (fun z => g (z,v) • W (z,v)) y) at hsi
  change divergence (fun z => ∫ v, g (z,v) • W (z,v)) y =
    ∫ v, divergence (fun z => g (z,v) • W (z,v)) y at hse
  have hvc : ContDiff ℝ 1 (fun w => g (y,w) • V (y,w)) := by
    rw [contDiff_iff_contDiffAt]
    intro v
    exact (hgV.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hy,mem_univ _⟩)).comp v
      (contDiffAt_const.prodMk contDiffAt_id)
  have hgs : HasCompactSupport (fun v => g (y,v)) :=
    compactSupport_of_zero_off hK (hz y hy)
  have hvcp : HasCompactSupport (fun w => g (y,w) • V (y,w)) := hgs.smul_right
  have hvi := integrable_divergence_compact hvc hvcp
  have hgc : Continuous (fun v => g (y,v)) :=
    hg.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hy,mem_univ _⟩)
  have hci : Integrable (fun v => g (y,v)*(divergence (fun z => W (z,v)) y+
      divergence (fun w => V (y,w)) v)) :=
    (hgc.mul ((continuous_divergence_phase_slices hU hy hW).1.add
      (continuous_divergence_phase_slices hU hy hV).2)).integrable_of_hasCompactSupport hgs.mul_right
  have he : L = fun v => divergence (fun z => g (z,v) • W (z,v)) y+
      divergence (fun w => g (y,w) • V (y,w)) v-
      g (y,v)*(divergence (fun z => W (z,v)) y+divergence (fun w => V (y,w)) v) := funext heq
  rw [he]
  refine ⟨(hsi.add hvi).sub hci,?_⟩
  have hsub := integral_sub (hsi.add hvi) hci
  have hadd := integral_add hsi hvi
  simp only [Pi.add_apply] at hsub hadd hse
  rw [hsub,hadd,integral_divergence_zero hvc hvcp,add_zero,←hse]

lemma contDiffAt_coneSpatialCoefficient_phase {k : ℕ∞ω} {x y v e : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (fun z : Phase => coneSpatialCoefficient x z.1 z.2 e) (y,v) := by
  have hn := (contDiffAt_coneDirection (k:=k) hxy).comp (y,v) contDiffAt_fst
  have hu : ContDiffAt ℝ k (fun z : Phase => velocity z.2) (y,v) :=
    contDiff_velocity.contDiffAt.comp (y,v) contDiffAt_snd
  have hde := contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk (contDiffAt_const (c:=e)))
  have hdu := contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk hu)
  exact hde.div (contDiffAt_const.sub hdu) (cone_denom_pos v _ (coneDirection_norm hxy)).ne'

lemma continuousOn_phase_divergences {U : Set Vec} {F : Phase → Vec}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) :
    ContinuousOn (fun p : Phase => divergence (fun z => F (z,p.2)) p.1) (U ×ˢ univ) ∧
    ContinuousOn (fun p : Phase => divergence (fun z => F (p.1,z)) p.2) (U ×ˢ univ) := by
  have hc := hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl
  have hd (p : Phase) (hp : p∈U ×ˢ univ) : DifferentiableAt ℝ F p :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have hb (e : Phase) (j : Fin 3) :
      ContinuousOn (fun p => (fderiv ℝ F p e) j) (U ×ˢ univ) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp_continuousOn
      (hc.clm_apply continuousOn_const)
  constructor
  · apply ContinuousOn.congr (continuousOn_finsetSum _ (fun j _ => hb (basis j,0) j))
    intro p hp
    exact divergence_phase_first (hd p hp)
  · apply ContinuousOn.congr (continuousOn_finsetSum _ (fun j _ => hb (0,basis j) j))
    intro p hp
    exact divergence_phase_second (hd p hp)

lemma continuousOn_divergence_of_isOpen {U : Set Vec} {F : Vec → Vec}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 1 F U) : ContinuousOn (divergence F) U := by
  have hc := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hd (p : Vec) (hp : p∈U) : DifferentiableAt ℝ F p :=
    (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  apply ContinuousOn.congr (f:=fun p => ∑ j : Fin 3, (fderiv ℝ F p (basis j)) j)
  · apply continuousOn_finsetSum
    intro j _
    exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.comp_continuousOn
      (hc.clm_apply continuousOn_const)
  · intro p hp
    unfold divergence spatialPartial
    simp_rw [fderiv_vec_component_at (hd p hp)]

lemma phase_division_annulus {U K : Set Vec} {g : Phase → ℝ} {W V : Phase → Vec}
    {L : Phase → ℝ} {ε R T : ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hε : 0<ε) (hεR : ε≤R) (hRT : R<T)
    (hdom : ∀ z : Vec, 0<‖z‖ → ‖z‖<T → z∈U)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ univ))
    (hW : ContDiffOn ℝ 1 W (U ×ˢ univ))
    (hV : ContDiffOn ℝ 1 V (U ×ˢ univ))
    (hz : ∀ z∈U, ∀ v∉K, g (z,v)=0)
    (heq : ∀ z∈U, ∀ v, L (z,v)=divergence (fun y => g (y,v) • W (y,v)) z+
      divergence (fun w => g (z,w) • V (z,w)) v-
      g (z,v)*(divergence (fun y => W (y,v)) z+divergence (fun w => V (z,w)) v)) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, L (z,v)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v, g (R • n.1,v) • W (R • n.1,v)) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v, g (ε • n.1,v) • W (ε • n.1,v)) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        g (z,v)*(divergence (fun y => W (y,v)) z+divergence (fun w => V (z,w)) v) := by
  let F : Vec → Vec := fun z => ∫ v, g (z,v) • W (z,v)
  have hF : ContDiffOn ℝ 1 F U :=
    contDiffOn_integral_uniform_support hU hK (hg.smul hW) (by
      intro z hu v hv
      change g (z,v) • W (z,v)=0
      rw [hz z hu v hv,zero_smul])
  let A := ball (0:Vec) R \ ball (0:Vec) ε
  let C := closedBall (0:Vec) R \ ball (0:Vec) ε
  have hC : IsCompact C := (isCompact_closedBall _ _).diff isOpen_ball
  have hAU : A⊆C := fun z hz => ⟨ball_subset_closedBall hz.1,hz.2⟩
  have hCU : C⊆U := by
    intro z hz
    have hzr : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz.1
    have hze : ε≤‖z‖ := by simpa only [mem_ball_zero_iff,not_lt] using hz.2
    exact hdom z (hε.trans_le hze) (hzr.trans_lt hRT)
  have hDz : IntegrableOn (divergence F) A :=
    (((continuousOn_divergence_of_isOpen hU hF).mono hCU).integrableOn_compact hC).mono_set hAU
  let B : Phase → ℝ := fun p =>
    g p*(divergence (fun y => W (y,p.2)) p.1+divergence (fun w => V (p.1,w)) p.2)
  have hB : ContinuousOn B (U ×ˢ univ) := hg.continuousOn.mul
    ((continuousOn_phase_divergences hU hW).1.add (continuousOn_phase_divergences hU hV).2)
  have hBi : ContinuousOn (fun z => ∫ v, B (z,v)) U := by
    apply continuousOn_integral_of_compact_support (k:=K) hK hB
    intro z v hu hv
    dsimp [B]
    rw [hz z hu v hv,zero_mul]
  have hBint : IntegrableOn (fun z => ∫ v, B (z,v)) A :=
    (hBi.mono hCU).integrableOn_compact hC |>.mono_set hAU
  have hD := divergence_annulus_local hε hεR hRT (F:=F) (by
    intro z hz ht
    exact hF.contDiffAt (hU.mem_nhds (hdom z hz ht)))
  have he (z : Vec) (hzA : z∈A) : (∫ v, L (z,v))=divergence F z-∫ v, B (z,v) :=
    (phase_division_integral hU hK (hCU (hAU hzA)) hg hW hV hz (heq z (hCU (hAU hzA)))).2
  rw [setIntegral_congr_fun (g:=fun z => divergence F z-∫v,B (z,v))
    (measurableSet_ball.diff measurableSet_ball) he,integral_sub hDz hBint,hD]

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma spatialTranslateParticle_add (x : Vec) (f : Particle) :
    spatialTranslateParticle x f = fun p => f ((0,x,0)+p) := by
  funext p
  change f (p.1,x+p.2.1,p.2.2) = f (0+p.1,x+p.2.1,0+p.2.2)
  rw [zero_add,zero_add]

lemma fderiv_spatialTranslateParticle (x : Vec) (f : Particle) (p : ℝ × Phase) :
    fderiv ℝ (spatialTranslateParticle x f) p = fderiv ℝ f (p.1,x+p.2.1,p.2.2) := by
  rw [spatialTranslateParticle_add,fderiv_comp_add_left]
  change fderiv ℝ f (0+p.1,x+p.2.1,0+p.2.2)=_
  rw [zero_add,zero_add]

lemma shifted_retarded_local_data {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} (ht : 0≤t) (x : Vec) :
    ∃ K : Set Vec, IsCompact K ∧
      ContDiffOn ℝ 1 (retardedDensity (spatialTranslateParticle x s.f) t 0)
        (retardedSpaceDomain t 0 ×ˢ univ) ∧
      ∀ z∈retardedSpaceDomain t 0, ∀ v∉K,
        retardedDensity (spatialTranslateParticle x s.f) t 0 (z,v)=0 := by
  obtain ⟨K,hK,hg,hz⟩ := retarded_local_data hf hc ht x
  have hmap (z : Vec) (hz : z∈retardedSpaceDomain t 0) : x+z∈retardedSpaceDomain t x := by
    refine ⟨?_,?_⟩
    · intro he
      have hh : z=0 := add_left_cancel (show x+z=x+0 by simpa only [add_zero] using he.symm)
      exact hz.1 hh.symm
    · rw [coneRadius_add]
      simpa only [coneRadius,zero_sub,norm_neg] using hz.2
  refine ⟨K,hK,?_,?_⟩
  · have hshift : ContDiff ℝ 1 (fun p : Phase => (x+p.1,p.2)) :=
      ((contDiff_const (c:=x)).add contDiff_fst).prodMk contDiff_snd
    have hm : MapsTo (fun p : Phase => (x+p.1,p.2))
        (retardedSpaceDomain t 0 ×ˢ univ) (retardedSpaceDomain t x ×ˢ univ) :=
      fun p hp => ⟨hmap p.1 hp.1,hp.2⟩
    have hh := hg.comp hshift.contDiffOn hm
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp [retardedDensity,spatialTranslateParticle,coneRadius]
  · intro z hzu v hv
    have hh := hz (x+z) (hmap z hzu) v hv
    simpa [retardedDensity,spatialTranslateParticle,coneRadius] using hh

lemma shifted_retarded_spatial_divergence {f : Particle} {K : Phase → Vec} {k : Phase → ℝ}
    {x z v e : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius 0 z,x+z,v)) (hz : (0:Vec)≠z)
    (hK : DifferentiableAt ℝ K (z,v)) (hk : DifferentiableAt ℝ k (z,v))
    (heq : fderiv ℝ f (t-coneRadius 0 z,x+z,v) (1,velocity v,K (z,v))=0) :
    k (z,v)*fderiv ℝ f (t-coneRadius 0 z,x+z,v) (0,e,0)=
      divergence (fun y => (f (t-coneRadius 0 y,x+y,v)*k (y,v)) • coneSpatialLift 0 y v e) z+
      divergence (fun w => (f (t-coneRadius 0 z,x+z,w)*k (z,w)) •
        (coneSpatialCoefficient 0 z w e • K (z,w))) v-
      f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => k (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => k (z,w) • (coneSpatialCoefficient 0 z w e • K (z,w))) v) := by
  have hf' : DifferentiableAt ℝ (spatialTranslateParticle x f) (t-coneRadius 0 z,z,v) := by
    rw [spatialTranslateParticle_add]
    apply DifferentiableAt.comp (f:=fun p : ℝ × Phase => (0,x,0)+p) _ ?_
      ((differentiableAt_const _).add differentiableAt_id)
    change DifferentiableAt ℝ f (0+(t-coneRadius 0 z),x+z,0+v)
    simpa only [zero_add] using hf
  have heq' : fderiv ℝ (spatialTranslateParticle x f) (t-coneRadius 0 z,z,v)
      (1,velocity v,K (z,v))=0 := by
    rw [fderiv_spatialTranslateParticle]
    exact heq
  have hh := retarded_spatial_divergence (e:=e) hf' hz hK hk heq'
  simpa only [fderiv_spatialTranslateParticle,spatialTranslateParticle] using hh

lemma retarded_spatial_annulus {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x e : Vec} {t ε R : ℝ} (hε : 0<ε) (hεR : ε≤R) (hRt : R<t)
    {k : Phase → ℝ} {K : Phase → Vec}
    (hk : ContDiffOn ℝ 1 k (retardedSpaceDomain t 0 ×ˢ univ))
    (hK : ContDiffOn ℝ 1 K (retardedSpaceDomain t 0 ×ˢ univ))
    (heq : ∀ z∈retardedSpaceDomain t 0, ∀ v,
      fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (1,velocity v,K (z,v))=0) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,
      ∫ v, k (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v,
        (s.f (t-R,x+R • n.1,v)*k (R • n.1,v)) • coneSpatialLift 0 (R • n.1) v e) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v,
        (s.f (t-ε,x+ε • n.1,v)*k (ε • n.1,v)) • coneSpatialLift 0 (ε • n.1) v e) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => k (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => k (z,w) • (coneSpatialCoefficient 0 z w e • K (z,w))) v) := by
  have ht : 0<t := (hε.trans_le hεR).trans hRt
  obtain ⟨S,hS,hg,hzero⟩ := shifted_retarded_local_data hf hc ht.le x
  have hU := isOpen_retardedSpaceDomain t 0
  have hco : ContDiffOn ℝ 1 (fun z : Phase => coneSpatialCoefficient 0 z.1 z.2 e)
      (retardedSpaceDomain t 0 ×ˢ univ) := fun p hp =>
    (contDiffAt_coneSpatialCoefficient_phase hp.1.1).contDiffWithinAt
  have hu : ContDiffOn ℝ 1 (fun z : Phase => velocity z.2) (retardedSpaceDomain t 0 ×ˢ univ) :=
    (contDiff_velocity.comp contDiff_snd).contDiffOn
  have hW : ContDiffOn ℝ 1 (fun z : Phase => k z • coneSpatialLift 0 z.1 z.2 e)
      (retardedSpaceDomain t 0 ×ˢ univ) :=
    hk.smul ((contDiffOn_const (c:=e)).add (hco.smul hu))
  have hV : ContDiffOn ℝ 1 (fun z : Phase => k z • (coneSpatialCoefficient 0 z.1 z.2 e • K z))
      (retardedSpaceDomain t 0 ×ˢ univ) := hk.smul (hco.smul hK)
  have hh := phase_division_annulus
    (L:=fun p => k p*fderiv ℝ s.f (t-coneRadius 0 p.1,x+p.1,p.2) (0,e,0))
    hU hS hε hεR hRt (by
      intro z hz hzt
      refine ⟨(norm_pos_iff.mp hz).symm,?_⟩
      simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr hzt)
    hg hW hV hzero (by
      intro z hzu v
      have hp := shifted_retarded_spatial_divergence (e:=e)
        (particle_differentiableAt_positive hf hzu.2 (x+z) v) hzu.1
        ((hK.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hzu,mem_univ _⟩)).differentiableAt (by simp))
        ((hk.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hzu,mem_univ _⟩)).differentiableAt (by simp))
        (heq z hzu v)
      simpa only [retardedDensity,spatialTranslateParticle,smul_smul,smul_eq_mul,mul_assoc] using hp)
  have hrad (a : ℝ) (ha : 0≤a) (n : Sphere) : coneRadius 0 (a • n.1)=a := by
    simp only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg ha,sphere_norm,mul_one]
  simpa only [retardedDensity,spatialTranslateParticle,smul_smul,smul_eq_mul,mul_assoc,
    hrad R (hε.le.trans hεR),hrad ε hε.le] using hh

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_PhysicalDivision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coneLorentz_contDiffAt {s : Solution}
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} (x : Vec) {p : Phase} (hp : p.1≠0) (ht : 0<t-coneRadius 0 p.1) :
    ContDiffAt ℝ 1 (coneLorentz s t x) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hp.symm).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have ha : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius 0 z.1,x+z.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_const.add contDiffAt_fst)
  have he := (field_contDiffAt_positive hE ht (x+p.1)).comp p ha
  have hb := (field_contDiffAt_positive hB ht (x+p.1)).comp p ha
  exact he.add (contDiff_cross.contDiffAt.comp p (hu.prodMk hb))

lemma coneLorentz_vlasov_before {s : Solution} {H t : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : EquationsBefore s H)
    (htH : t≤H) (x : Vec) {z : Vec} (hz : z∈retardedSpaceDomain t 0) (v : Vec) :
    fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (1,velocity v,coneLorentz s t x (z,v))=0 := by
  have hr : 0 < coneRadius 0 z := norm_pos_iff.mpr (sub_ne_zero.mpr hz.1)
  have hh := particle_spacetime_vlasov_before hf heq hz.2 (by linarith : t-coneRadius 0 z<H) (x+z) v
  rw [fderiv_particleBySpacetime (particle_differentiableAt_positive hf hz.2 (x+z) v)] at hh
  exact hh

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_TransportDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma divergence_parameter_slice {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {F : U × Vec → Vec} {a : U} {v : Vec} (hF : DifferentiableAt ℝ F (a,v)) :
    divergence (fun w => F (a,w)) v=∑ j : Fin 3,(fderiv ℝ F (a,v) (0,basis j)) j := by
  have hP := (hasFDerivAt_const a v).prodMk (hasFDerivAt_id (𝕜:=ℝ) v)
  have hh := hF.hasFDerivAt.comp v hP
  change HasFDerivAt (fun w : Vec => F (a,w)) _ v at hh
  unfold divergence spatialPartial
  congr 1
  funext j
  rw [fderiv_vec_component_at hh.differentiableAt j,hh.fderiv]
  rfl

lemma divergence_real_const_smul {F : Vec → Vec} {v : Vec} (hF : DifferentiableAt ℝ F v) (a : ℝ) :
    divergence (fun w => a • F w) v=a*divergence F v := by
  rw [divergence_smul (differentiableAt_const a) hF]
  have hg : gradient (fun _ : Vec => a) v=0 := by
    ext j
    simp
  rw [hg]
  simp [dot]

lemma integral_symmetric_annulus_tendsto {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {t : ℝ} (ht : 0<t) (hF : IntegrableOn F (ball (0:Vec) t)) :
    Tendsto (fun a : ℝ => ∫ z in ball (0:Vec) (t-a) \ ball (0:Vec) a,F z) (𝓝[>] (0:ℝ))
      (𝓝 (∫ z in ball (0:Vec) t,F z)) := by
  have hh : Tendsto (fun a : ℝ => ∫ z in ball (0:Vec) t,
      (ball (0:Vec) (t-a) \ ball (0:Vec) a).indicator F z) (𝓝[>] (0:ℝ))
      (𝓝 (∫ z in ball (0:Vec) t,F z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖F z‖)
    · exact Eventually.of_forall (fun a => hF.aestronglyMeasurable.indicator (measurableSet_ball.diff measurableSet_ball))
    · exact Eventually.of_forall (fun a => ae_of_all _ (fun z => norm_indicator_le_norm_self _ _))
    · exact hF.norm
    · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
      have hn : ‖z‖<t := by simpa only [mem_ball_zero_iff] using hz
      have hn0 : 0<‖z‖ := norm_pos_iff.mpr hz0
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT (lt_min hn0 (show 0<t-‖z‖ by linarith))] with a ha
      symm
      apply indicator_of_mem
      simp only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt]
      exact ⟨by linarith [ha.2.trans_le (min_le_right _ _)],(ha.2.trans_le (min_le_left _ _)).le⟩
  apply hh.congr'
  filter_upwards [Ioo_mem_nhdsGT ht] with a ha
  rw [setIntegral_indicator (measurableSet_ball.diff measurableSet_ball),inter_eq_right.mpr]
  intro z hz
  exact ball_subset_ball (by linarith [ha.1] : t-a≤t) hz.1

lemma norm_integral_ball_of_annulus_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {t C : ℝ} (ht : 0<t) (hF : IntegrableOn F (ball (0:Vec) t))
    (hb : ∀ ε R : ℝ, 0<ε → ε≤R → R<t → ‖∫ z in ball (0:Vec) R \ ball (0:Vec) ε,F z‖≤C) :
    ‖∫ z in ball (0:Vec) t,F z‖≤C := by
  apply le_of_tendsto (integral_symmetric_annulus_tendsto ht hF).norm
  filter_upwards [Ioo_mem_nhdsGT (half_pos ht)] with a ha
  exact hb a (t-a) ha.1 (by linarith [ha.2]) (by linarith [ha.1])

lemma particle_spatial_fderiv {f : Particle} {u : ℝ} {y v : Vec}
    (hf : DifferentiableAt ℝ f (u,y,v)) (e : Vec) :
    fderiv ℝ (fun z => f (u,z,v)) y e=fderiv ℝ f (u,y,v) (0,e,0) := by
  have hm : HasFDerivAt (fun z : Vec => (u,z,v))
      ((0 : Vec →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Vec).prod 0)) y :=
    (hasFDerivAt_const u y).prodMk ((hasFDerivAt_id (𝕜:=ℝ) y).prodMk (hasFDerivAt_const v y))
  have hh := hf.hasFDerivAt.comp (f:=fun z : Vec => (u,z,v)) y hm
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PhysicalC0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma kernel_volterra_norm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {F : Vec → W} {t C : ℝ} (ht : 0≤t) (_ : 0≤C)
    (hF : IntegrableOn F (ball (0:Vec) t)) {g : ℝ → ℝ} (hg : Continuous g)
    (hb : ∀ z, 0<‖z‖ → ‖z‖≤t → ‖F z‖≤C*g (t-‖z‖)/‖z‖^2) :
    ‖∫ z in ball (0:Vec) t, F z‖≤(4*Real.pi)*C*(∫ u in Icc (0:ℝ) t, g u) := by
  rw [integral_ball_polar_flip hF]
  have hr : IntegrableOn (fun r => C*g (t-r)) (Ioo (0:ℝ) t) :=
    ((continuous_const.mul (hg.comp (continuous_const.sub continuous_id))).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hin (a : Sphere) : ‖∫ r in Ioo (0:ℝ) t, r^2 • F (-(r • a.1))‖ ≤
      C*(∫ u in Icc (0:ℝ) t, g u) := by
    have hh := norm_integral_le_of_norm_le hr (f:=fun r => r^2 • F (-(r • a.1))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have he : ‖-(r • a.1)‖=r := by
        rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,sphere_norm,mul_one]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)]
      have hh := hb (-(r • a.1)) (by simpa only [he] using hr.1) (by simpa only [he] using hr.2.le)
      rw [he] at hh
      exact (mul_le_mul_of_nonneg_left hh (sq_nonneg r)).trans_eq (by field_simp [ne_of_gt hr.1]))
    apply hh.trans_eq
    rw [←integral_Icc_eq_integral_Ioo,integral_const_mul,integral_Icc_sub g ht]
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (Filter.Eventually.of_forall hin)
  simpa only [sphere_area,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma norm_velocity_integral_bound {P C : ℝ} {g : Vec → ℝ}
    (hzero : ∀ v, P<‖v‖ → g v=0) (hb : ∀ v, ‖v‖≤P → |g v|≤C) :
    ‖∫ v,g v‖≤volume.real (closedBall (0:Vec) P)*C := by
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=closedBall (0:Vec) P)
    (f:=g) (fun v hv => hzero v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv))]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P)) (f:=g) (C:=C) (by
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
    simpa only [Real.norm_eq_abs] using hb v (by simpa only [mem_closedBall,dist_zero_right] using hv))
  simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh

lemma retarded_packet_integrable {F : Vec × Phase → ℝ} {t P C : ℝ} (x : Vec)
    (hc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (hb : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |F (x,z,v)|≤C/‖z‖) :
    IntegrableOn (fun z => ∫ v,F (x,z,v)) (ball (0:Vec) t) := by
  let A := ball (0:Vec) t \ ({0}:Set Vec)
  have hC : ContinuousOn (fun p : Phase => F (x,p)) (A ×ˢ univ) := by
    intro p hp
    exact ((hc (x,p) hp.1.2 (by simpa only [mem_ball,dist_zero_right] using hp.1.1)).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hzero (z : Vec) (hza : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (x,z,v)=0 :=
    hz x z v hza.2 (by simpa only [mem_ball,dist_zero_right] using hza.1)
      (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  apply integrableOn_ball_of_punctured_bound (α:=1) (C:=volume.real (closedBall (0:Vec) P)*C)
    (by norm_num) (continuousOn_integral_uniform_support (isCompact_closedBall _ _) hC hzero)
  intro z hz0 hzt
  have hzn := norm_pos_iff.mp hz0
  have hh := norm_velocity_integral_bound (hz x z · hzn hzt) (hb x z · hzn hzt)
  simpa only [Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv,mul_assoc] using hh

lemma retarded_packet_spatial_fderiv {F : Vec × Phase → ℝ} {x z v : Vec}
    (hF : DifferentiableAt ℝ F (x,z,v)) (e : Vec) :
    fderiv ℝ (fun y => F (y,z,v)) x e=fderiv ℝ F (x,z,v) (e,0,0) := by
  have hh := hF.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (z,v) x))
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma retarded_packet_derivative_zero {F : Vec × Phase → ℝ} {P t : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z v e : Vec) (hz0 : z≠0) (hzt : ‖z‖<t) (hv : P<‖v‖) :
    fderiv ℝ F (x,z,v) (e,0,0)=0 := by
  rw [←retarded_packet_spatial_fderiv ((hF (x,z,v) hz0 hzt).differentiableAt (by simp)) e]
  have he : (fun y => F (y,z,v))=fun _ => (0:ℝ) := funext (fun y => hz y z v hz0 hzt hv)
  rw [he]
  simp

lemma hasDerivAt_retarded_packet_line {F : Vec × Phase → ℝ} {t P : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z e : Vec) (a : ℝ) (hz0 : z≠0) (hzt : ‖z‖<t) :
    HasDerivAt (fun q : ℝ => ∫ v,F (x+q • e,z,v))
      (∫ v,fderiv ℝ F (x+a • e,z,v) (e,0,0)) a := by
  let G : ℝ × Vec → ℝ := fun p => F (x+p.1 • e,z,p.2)
  have hG : ContDiff ℝ 1 G := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (hF (x+p.1 • e,z,p.2) hz0 hzt).comp p
      ((contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const)).prodMk
        (contDiffAt_const.prodMk contDiffAt_snd))
  have hzero (q : ℝ) (_ : q∈(univ : Set ℝ)) (v : Vec) (hv : v∉closedBall (0:Vec) P) : G (q,v)=0 :=
    hz _ z v hz0 hzt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  have hd := (hasFDerivAt_integral_uniform_support isOpen_univ (isCompact_closedBall (0:Vec) P)
    (mem_univ a) hG.contDiffOn hzero).differentiableAt.hasDerivAt
  rw [show deriv (fun q => ∫ v,G (q,v)) a = fderiv ℝ (fun q => ∫ v,G (q,v)) a 1 from rfl,
    fderiv_integral_uniform_support_apply isOpen_univ (isCompact_closedBall (0:Vec) P)
      (mem_univ a) hG.contDiffOn hzero] at hd
  apply hd.congr_deriv
  apply integral_congr_ae
  apply ae_of_all
  intro v
  have hm := ((hasFDerivAt_const x (a,v)).add ((hasFDerivAt_fst (𝕜:=ℝ)).smul_const e)).prodMk
    ((hasFDerivAt_const z (a,v)).prodMk (hasFDerivAt_snd (𝕜:=ℝ)))
  have hh := ((hF (x+a • e,z,v) hz0 hzt).differentiableAt (by simp)).hasFDerivAt.comp (a,v) hm
  change HasFDerivAt G _ (a,v) at hh
  simpa using congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L (1,0)) hh.fderiv

lemma hasDerivAt_retarded_packet_integral {F : Vec × Phase → ℝ} {t P C D : ℝ}
    (hF : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (hb : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |F (x,z,v)|≤C/‖z‖)
    (x e : Vec) (a : ℝ)
    (hD : ∀ x z v : Vec, z≠0 → ‖z‖<t → ‖v‖≤P → |fderiv ℝ F (x,z,v) (e,0,0)|≤D/‖z‖) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,F (x+q • e,z,v))
      (∫ z in ball (0:Vec) t,∫ v,fderiv ℝ F (x+a • e,z,v) (e,0,0)) a := by
  let V := volume.real (closedBall (0:Vec) P)
  have hfc := fun p hp ht => (hF p hp ht).continuousAt
  have hdc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t →
      ContinuousAt (fun p => fderiv ℝ F p (e,0,0)) p := by
    intro p hp ht
    exact ((hF p hp ht).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hdz := fun x z v hz0 hzt hv => retarded_packet_derivative_zero hF hz x z v e hz0 hzt hv
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:=fun z : Vec => V*D*‖z‖^(-(1:ℝ))) (by simp)
    (Eventually.of_forall (fun q => (retarded_packet_integrable (x+q • e) hfc hz hb).aestronglyMeasurable))
    (retarded_packet_integrable (x+a • e) hfc hz hb)
    (retarded_packet_integrable (x+a • e) hdc hdz hD).aestronglyMeasurable
    ?_ ((integrableOn_norm_rpow_neg (R:=t) (show (1:ℝ)<3 by norm_num)).const_mul (V*D)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzball hz0
    intro q _
    have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hzball
    have hh := norm_velocity_integral_bound (hdz (x+q • e) z · hz0 hzt) (hD (x+q • e) z · hz0 hzt)
    simpa only [V,Real.rpow_neg (norm_nonneg z),Real.rpow_one,div_eq_mul_inv,mul_assoc] using hh
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hzball hz0
    intro q _
    exact hasDerivAt_retarded_packet_line hF hz x z e q hz0 (by simpa only [mem_ball,dist_zero_right] using hzball)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceKernels
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

lemma contDiffAt_sourceAngularCore {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n u b : U → Vec} {z : U} {k : ℕ∞ω}
    (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z) (hb : ContDiffAt ℝ k b z)
    (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun w => sourceAngularCore (n w) (u w) (b w)) z := by
  have hnb := contDiff_dot_pair.contDiffAt.comp z (hn.prodMk hb)
  have hnu := contDiff_dot_pair.contDiffAt.comp z (hn.prodMk hu)
  exact (((contDiffAt_const.sub hnu).pow 2).inv (pow_ne_zero 2 hd)).smul
    ((hnb.smul (hn.sub hu)).sub ((contDiffAt_const.sub hnu).smul hb))

lemma sourceAngularProfile_contDiffAt (i : Fin 3) {p : (Vec × Vec × Vec) × Vec}
    (hd : 1-dot p.1.1 (velocity p.2)≠0) :
    ContDiffAt ℝ 1 (sourceAngularProfile i) p := by
  have hn : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => z.1.1) p := contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hforce : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec =>
      z.1.2.1+cross (velocity z.2) z.1.2.2) p :=
    contDiffAt_fst.snd.fst.add
      (contDiff_cross.contDiffAt.comp p (hu.prodMk contDiffAt_fst.snd.snd))
  have hdv : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => fderiv ℝ velocity z.2) p :=
    ((contDiff_velocity (k:=2)).fderiv_right (by norm_num)).contDiffAt.comp p contDiffAt_snd
  exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p
    (contDiffAt_sourceAngularCore hn hu (hdv.clm_apply hforce) hd)

lemma sourceFixedCoefficient_contDiffAt (v E B : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ 1 (sourceFixedCoefficient v E B i) z := by
  have hn := contDiffAt_coneDirection (k:=1) hz.symm
  have hc := (sourceAngularProfile_contDiffAt i (p:=((coneDirection 0 z,E,B),v))
    (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').comp z
      ((hn.prodMk (contDiffAt_const.prodMk contDiffAt_const)).prodMk contDiffAt_const)
  exact ((contDiffAt_coneRadius hz.symm).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.symm))).mul hc

lemma sourceFixedFlux_contDiffAt (v E B e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ 1 (sourceFixedFlux v E B e i) z :=
  (sourceFixedCoefficient_contDiffAt v E B i hz).smul (contDiffAt_coneSpatialLift hz.symm)

lemma sourceFixedFlux_homogeneous (v E B e : Vec) (i : Fin 3) {r : ℝ} (hr : 0 < r) (z : Vec) :
    sourceFixedFlux v E B e i (r • z)=r⁻¹ • sourceFixedFlux v E B e i z := by
  simp only [sourceFixedFlux,sourceFixedCoefficient,coneSpatialLift,coneSpatialCoefficient,
    coneRadius_zero_smul hr,coneDirection_zero_smul hr,smul_smul]
  congr 1
  field_simp

lemma fderiv_degree_neg_one {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0 < r → ∀ z, F (r • z)=r⁻¹ • F z)
    {r : ℝ} (hr : 0 < r) {z : Vec}
    (hz : DifferentiableAt ℝ F z) (hrz : DifferentiableAt ℝ F (r • z)) (e : Vec) :
    fderiv ℝ F (r • z) e=(r^2)⁻¹ • fderiv ℝ F z e := by
  have hm : HasFDerivAt (fun y : Vec => r • y) (r • ContinuousLinearMap.id ℝ Vec) z :=
    (hasFDerivAt_id z).const_smul r
  have h₁ := hrz.hasFDerivAt.comp z hm
  have h₂ := hz.hasFDerivAt.const_smul r⁻¹
  have heq : (fun y : Vec => F (r • y))=(fun y : Vec => r⁻¹ • F y) := funext (hh r hr)
  change HasFDerivAt (fun y : Vec => F (r • y)) _ _ at h₁
  rw [heq] at h₁
  have hv := congrArg (fun L : Vec →L[ℝ] Vec => L e) (h₁.unique h₂)
  change fderiv ℝ F (r • z) (r • e)=r⁻¹ • fderiv ℝ F z e at hv
  rw [map_smul] at hv
  have hv' := congrArg (fun a : Vec => r⁻¹ • a) hv
  simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul,
    show r⁻¹*r⁻¹=(r^2)⁻¹ by ring] using hv'

lemma divergence_degree_neg_one {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0 < r → ∀ z, F (r • z)=r⁻¹ • F z)
    (hF : ∀ z≠0, DifferentiableAt ℝ F z) {r : ℝ} (hr : 0 < r) {z : Vec} (hz : z≠0) :
    divergence F (r • z)=(r^2)⁻¹*divergence F z := by
  have hrz : r • z≠0 := smul_ne_zero hr.ne' hz
  have hc (y : Vec) (hy : y≠0) (i : Fin 3) :
      fderiv ℝ (fun x => F x i) y = (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F y) := by
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp y (hF y hy).hasFDerivAt).fderiv
  unfold divergence spatialPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc _ hrz i,hc _ hz i]
  change (fderiv ℝ F (r • z) (basis i)) i = (r^2)⁻¹*(fderiv ℝ F z (basis i)) i
  rw [fderiv_degree_neg_one hh hr (hF _ hz) (hF _ hrz)]
  rfl

lemma sourceConeCoefficient_contDiffAt {s : Solution}
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} (x : Vec) (i : Fin 3) {p : Phase} (hp : p.1≠0) (ht : 0<t-coneRadius 0 p.1) :
    ContDiffAt ℝ 1 (sourceConeCoefficient s t x i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hp.symm).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hp.symm).comp p contDiffAt_fst
  have ha : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius 0 z.1,x+z.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_const.add contDiffAt_fst)
  have he := (field_contDiffAt_positive hE ht (x+p.1)).comp p ha
  have hb := (field_contDiffAt_positive hB ht (x+p.1)).comp p ha
  have hc := (sourceAngularProfile_contDiffAt i (p:=((coneDirection 0 p.1,
      s.E (t-coneRadius 0 p.1,x+p.1),s.B (t-coneRadius 0 p.1,x+p.1)),p.2))
    (cone_denom_pos p.2 _ (coneDirection_norm hp.symm)).ne').comp p
      ((hn.prodMk (he.prodMk hb)).prodMk contDiffAt_snd)
  exact (hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.symm))).mul hc

lemma electric_source_division_annulus {s : Solution} {H t ε R : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (heq : EquationsBefore s H)
    (htH : t≤H) (hε : 0<ε) (hεR : ε≤R) (hRt : R<t) (x e : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
      sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v, s.f (t-R,x+R • n.1,v) •
        (sourceConeCoefficient s t x i (R • n.1,v) • coneSpatialLift 0 (R • n.1) v e)) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v, s.f (t-ε,x+ε • n.1,v) •
        (sourceConeCoefficient s t x i (ε • n.1,v) • coneSpatialLift 0 (ε • n.1) v e)) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => sourceConeCoefficient s t x i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v) := by
  have hk : ContDiffOn ℝ 1 (sourceConeCoefficient s t x i) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (sourceConeCoefficient_contDiffAt hE hB x i hp.1.1.symm hp.1.2).contDiffWithinAt
  have hK : ContDiffOn ℝ 1 (coneLorentz s t x) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (coneLorentz_contDiffAt hE hB x hp.1.1.symm hp.1.2).contDiffWithinAt
  simpa only [smul_smul] using retarded_spatial_annulus (e:=e) hf hc hε hεR hRt hk hK
    (fun z hz v => coneLorentz_vlasov_before hf heq htH x hz v)

lemma sourceJointFlux_contDiffAt (e : Vec) (i : Fin 3) {p : Phase × Phase}
    (hp : p.1.1≠0) : ContDiffAt ℝ 1 (sourceJointFlux e i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hp.symm).comp p contDiffAt_fst.fst
  have hn := (contDiffAt_coneDirection (k:=1) hp.symm).comp p contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase × Phase => velocity z.1.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_fst.snd
  have he := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk (contDiffAt_const (c:=e)))
  have hd := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk hu)
  have hne := (cone_denom_pos p.1.2 _ (coneDirection_norm hp.symm)).ne'
  have hW : ContDiffAt ℝ 1 (fun z : Phase × Phase => coneSpatialLift 0 z.1.1 z.1.2 e) p :=
    contDiffAt_const.add ((he.div (contDiffAt_const.sub hd) hne).smul hu)
  have hc := (sourceAngularProfile_contDiffAt i (p:=((coneDirection 0 p.1.1,p.2.1,p.2.2),p.1.2)) hne).comp p
    ((hn.prodMk (contDiffAt_snd.fst.prodMk contDiffAt_snd.snd)).prodMk contDiffAt_fst.snd)
  exact ((hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.symm))).mul hc).smul hW

lemma sourceJointFlux_derivative_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec), ‖v‖≤P → ‖E‖≤M → ‖B‖≤M →
      ‖fderiv ℝ (sourceJointFlux e i) ((n.1,v),(E,B))‖≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P) ×ˢ
    (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)
  have hK : IsCompact K := ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : ContinuousOn (fderiv ℝ (sourceJointFlux e i)) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    have hz : p.1.1≠0 := by intro hh; simp only [hh,norm_zero] at hn; norm_num at hn
    exact ((sourceJointFlux_contDiffAt e i hz).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n v E B hv hE hB
  apply (hC ((n.1,v),(E,B)) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_closedBall,dist_zero_right] using hv⟩,
    by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩

lemma sourceFixedFlux_spatial_derivative (v E B e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (a : Vec) :
    fderiv ℝ (sourceFixedFlux v E B e i) z a=
      fderiv ℝ (sourceJointFlux e i) ((z,v),(E,B)) ((a,0),(0,0)) := by
  have hm := ((hasFDerivAt_id (𝕜:=ℝ) z).prodMk (hasFDerivAt_const v z)).prodMk
    (hasFDerivAt_const (E,B) z)
  have hh := ((sourceJointFlux_contDiffAt e i (p:=((z,v),(E,B))) hz).differentiableAt (by simp)).hasFDerivAt.comp z hm
  exact congrArg (fun L : Vec →L[ℝ] Vec => L a) hh.fderiv

lemma sourceFixedFlux_field_derivative (v E B e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (a : Phase) :
    fderiv ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i z) (E,B) a=
      fderiv ℝ (sourceJointFlux e i) ((z,v),(E,B)) ((0,0),a) := by
  have hm := (hasFDerivAt_const (z,v) (E,B)).prodMk (hasFDerivAt_id (𝕜:=ℝ) (E,B))
  have hh := ((sourceJointFlux_contDiffAt e i (p:=((z,v),(E,B))) hz).differentiableAt (by simp)).hasFDerivAt.comp (E,B) hm
  exact congrArg (fun L : Phase →L[ℝ] Vec => L a) hh.fderiv

lemma sourceFixedFlux_field_differentiable (v e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (w : Phase) :
    DifferentiableAt ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i z) w :=
  ((sourceJointFlux_contDiffAt e i (p:=((z,v),w)) hz).differentiableAt (by simp)).comp w
    ((differentiableAt_const (z,v)).prodMk differentiableAt_id)

lemma sourceFixedFlux_field_rescale (v E B e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0)
    {r : ℝ} (hr : 0 < r) (a : Phase) :
    fderiv ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i (r • z)) (E,B) a=
      r⁻¹ • fderiv ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i z) (E,B) a := by
  have heq : (fun w : Phase => sourceFixedFlux v w.1 w.2 e i (r • z))=
      fun w : Phase => r⁻¹ • sourceFixedFlux v w.1 w.2 e i z :=
    funext (fun w => sourceFixedFlux_homogeneous v w.1 w.2 e i hr z)
  rw [heq]
  have hh := (sourceFixedFlux_field_differentiable v e i hz (E,B)).hasFDerivAt.const_smul r⁻¹
  change HasFDerivAt (fun w : Phase => r⁻¹ • sourceFixedFlux v w.1 w.2 e i z) _ _ at hh
  exact congrArg (fun L : Phase →L[ℝ] Vec => L a) hh.fderiv

lemma sourceFixedFlux_bounds (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec) (r : ℝ),
      ‖v‖≤P → ‖E‖≤M → ‖B‖≤M → 0 < r →
      |divergence (sourceFixedFlux v E B e i) (r • n.1)|≤3*C/r^2 ∧
      ∀ a : Phase, ‖fderiv ℝ (fun w : Phase => sourceFixedFlux v w.1 w.2 e i (r • n.1)) (E,B) a‖≤C/r*‖a‖ := by
  obtain ⟨C,hC,hb⟩ := sourceJointFlux_derivative_bound P M e i
  refine ⟨C,hC,?_⟩
  intro n v E B r hv hE hB hr
  have hn : n.1≠(0:Vec) := by intro hh; have hn := sphere_norm n; rw [hh,norm_zero] at hn; norm_num at hn
  have hder := hb n v E B hv hE hB
  have hF (z : Vec) (hz : z≠0) := (sourceFixedFlux_contDiffAt v E B e i hz).differentiableAt (by simp)
  constructor
  · rw [divergence_degree_neg_one (fun r hr z => sourceFixedFlux_homogeneous v E B e i hr z) hF hr hn,
      abs_mul,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
    have hb0 : |divergence (sourceFixedFlux v E B e i) n.1|≤3*C := by
      unfold divergence spatialPartial
      calc
        |∑ j : Fin 3,fderiv ℝ (fun z => sourceFixedFlux v E B e i z j) n.1 (basis j)|
            ≤ ∑ j : Fin 3,|fderiv ℝ (fun z => sourceFixedFlux v E B e i z j) n.1 (basis j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin 3,C := by
          apply Finset.sum_le_sum
          intro j hj
          rw [fderiv_vec_component_at (hF n.1 hn) j]
          change |(fderiv ℝ (sourceFixedFlux v E B e i) n.1 (basis j)) j|≤C
          apply (norm_coordinate_le _ j).trans
          rw [sourceFixedFlux_spatial_derivative v E B e i hn]
          have ht := (ContinuousLinearMap.le_opNorm _ ((basis j,0),(0,0))).trans
            (mul_le_mul_of_nonneg_right hder (norm_nonneg _))
          simpa [Prod.norm_mk,basis,PiLp.norm_single] using ht
        _ = 3*C := by simp
    exact (mul_le_mul_of_nonneg_left hb0 (inv_nonneg.mpr (sq_nonneg _))).trans_eq (by ring)
  · intro a
    rw [sourceFixedFlux_field_rescale v E B e i hn hr a,norm_smul,Real.norm_eq_abs,
      abs_inv,abs_of_pos hr,sourceFixedFlux_field_derivative v E B e i hn]
    have ht := (ContinuousLinearMap.le_opNorm _ ((0,0),a)).trans
      (mul_le_mul_of_nonneg_right hder (norm_nonneg _))
    have ht' : ‖fderiv ℝ (sourceJointFlux e i) ((n.1,v),(E,B)) ((0,0),a)‖≤C*‖a‖ := by
      simpa only [Prod.norm_mk,norm_zero,max_self,max_eq_right (norm_nonneg a)] using ht
    exact (mul_le_mul_of_nonneg_left ht' (inv_nonneg.mpr hr.le)).trans_eq (by ring)

lemma divergence_parameter_chain {F : Vec × Phase → Vec} {g : Vec → Phase} {z : Vec}
    (hF : DifferentiableAt ℝ F (z,g z)) (hg : DifferentiableAt ℝ g z) :
    divergence (fun y => F (y,g y)) z=
      divergence (fun y => F (y,g z)) z+
      ∑ j : Fin 3,(fderiv ℝ (fun w : Phase => F (z,w)) (g z) (fderiv ℝ g z (basis j))) j := by
  have hd := hF.hasFDerivAt.comp z ((hasFDerivAt_id (𝕜:=ℝ) z).prodMk hg.hasFDerivAt)
  have hs := hF.hasFDerivAt.comp z ((hasFDerivAt_id (𝕜:=ℝ) z).prodMk (hasFDerivAt_const (g z) z))
  have hp := hF.hasFDerivAt.comp (g z) ((hasFDerivAt_const z (g z)).prodMk (hasFDerivAt_id (𝕜:=ℝ) (g z)))
  change HasFDerivAt (fun y => F (y,g y)) _ z at hd
  change HasFDerivAt (fun y => F (y,g z)) _ z at hs
  change HasFDerivAt (fun w : Phase => F (z,w)) _ (g z) at hp
  unfold divergence spatialPartial
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fderiv_vec_component_at hd.differentiableAt j,fderiv_vec_component_at hs.differentiableAt j,
    hd.fderiv,hs.fderiv,hp.fderiv]
  change (fderiv ℝ F (z,g z) (basis j,fderiv ℝ g z (basis j))) j=
    (fderiv ℝ F (z,g z) (basis j,0)) j+(fderiv ℝ F (z,g z) (0,fderiv ℝ g z (basis j))) j
  rw [show (basis j,fderiv ℝ g z (basis j))=(basis j,0)+(0,fderiv ℝ g z (basis j)) by simp,map_add]
  rfl

lemma source_dynamic_spatial_divergence_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (g : Vec → Phase) (n : Sphere) (v : Vec) (r : ℝ),
      ‖v‖≤P → ‖(g (r • n.1)).1‖≤M → ‖(g (r • n.1)).2‖≤M → 0 < r →
      DifferentiableAt ℝ g (r • n.1) →
      |divergence (fun z => sourceFixedFlux v (g z).1 (g z).2 e i z) (r • n.1)|≤
        3*C/r^2+(3*C/r)*‖fderiv ℝ g (r • n.1)‖ := by
  obtain ⟨C,hC,hb⟩ := sourceFixedFlux_bounds P M e i
  refine ⟨C,hC,?_⟩
  intro g n v r hv hE hB hr hg
  have hn : n.1≠(0:Vec) := by intro hh; have hh' := sphere_norm n; rw [hh,norm_zero] at hh'; norm_num at hh'
  have hrn : r • (n.1 : Vec)≠0 := smul_ne_zero hr.ne' hn
  let z := r • (n.1 : Vec)
  let F : Vec × Phase → Vec := fun p => sourceFixedFlux v p.2.1 p.2.2 e i p.1
  have hF : DifferentiableAt ℝ F (z,g z) :=
    ((sourceJointFlux_contDiffAt e i (p:=((z,v),g z)) hrn).differentiableAt (by simp)).comp (f:=fun p : Vec × Phase => ((p.1,v),p.2)) (z,g z)
      ((differentiableAt_fst.prodMk (differentiableAt_const v)).prodMk differentiableAt_snd)
  have hchain := divergence_parameter_chain hF hg
  change divergence (fun y => F (y,g y)) z=_ at hchain
  change |divergence (fun y => F (y,g y)) z|≤_
  rw [hchain]
  obtain ⟨hsp,hparam⟩ := hb n v (g z).1 (g z).2 r hv hE hB hr
  have hcor : |∑ j : Fin 3, (fderiv ℝ (fun w : Phase => F (z,w)) (g z) (fderiv ℝ g z (basis j))) j|≤
      (3*C/r)*‖fderiv ℝ g z‖ := by
    calc
      _ ≤ ∑ j : Fin 3,|(fderiv ℝ (fun w : Phase => F (z,w)) (g z) (fderiv ℝ g z (basis j))) j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3,(C/r)*‖fderiv ℝ g z‖ := by
        apply Finset.sum_le_sum
        intro j hj
        apply (norm_coordinate_le _ j).trans
        refine (hparam (fderiv ℝ g z (basis j))).trans ?_
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hC hr.le)
        simpa only [show ‖basis j‖=1 by simp [basis,PiLp.norm_single],mul_one] using
          ContinuousLinearMap.le_opNorm (fderiv ℝ g z) (basis j)
      _ = _ := by simp; ring
  exact (abs_add_le _ _).trans (add_le_add hsp hcor)

lemma retarded_spacetime_lipschitz (t : ℝ) (x : Vec) :
    LipschitzWith 1 (fun z : Vec => (t-coneRadius 0 z,x+z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  simp only [NNReal.coe_one,one_mul,Prod.dist_eq,coneRadius,zero_sub,norm_neg]
  apply max_le
  · rw [Real.dist_eq,show (t-‖y‖)-(t-‖z‖)=‖z‖-‖y‖ by ring,abs_sub_comm,dist_eq_norm]
    exact abs_norm_sub_norm_le y z
  · rw [dist_add_left]

lemma norm_fderiv_retarded_fields {s : Solution} {t : ℝ} (x : Vec) {z : Vec}
    (hz : z≠0) (ht : 0<t-coneRadius 0 z)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace) :
    ‖fderiv ℝ (fun y : Vec => (s.E (t-coneRadius 0 y,x+y),s.B (t-coneRadius 0 y,x+y))) z‖≤
      max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖ := by
  let a : Vec → (ℝ × Vec) := fun y => (t-coneRadius 0 y,x+y)
  have ha : DifferentiableAt ℝ a z :=
    ((differentiableAt_const t).sub (differentiableAt_coneRadius hz.symm)).prodMk
      ((differentiableAt_const x).add differentiableAt_id)
  have he := (field_contDiffAt_positive hE ht (x+z)).differentiableAt (by simp)
  have hb := (field_contDiffAt_positive hB ht (x+z)).differentiableAt (by simp)
  have hh := (he.hasFDerivAt.prodMk hb.hasFDerivAt).comp z ha.hasFDerivAt
  change HasFDerivAt (fun y : Vec => (s.E (a y),s.B (a y))) _ z at hh
  rw [hh.fderiv]
  have hn : ‖fderiv ℝ a z‖≤1 := norm_fderiv_le_of_lipschitz ℝ (retarded_spacetime_lipschitz t x)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq
  simp only [mul_one,ContinuousLinearMap.opNorm_prod,Prod.norm_mk]

lemma physical_source_spatial_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t r : ℝ) (x v : Vec) (n : Sphere),
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      0 < r → r<t → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 (r • n.1),x+r • n.1)‖≤M →
      ‖s.B (t-coneRadius 0 (r • n.1),x+r • n.1)‖≤M →
      |divergence (fun z => sourceConeCoefficient s t x i (z,v) • coneSpatialLift 0 z v e) (r • n.1)|≤
        3*C/r^2+(3*C/r)*max
          ‖fderiv ℝ s.E (t-coneRadius 0 (r • n.1),x+r • n.1)‖
          ‖fderiv ℝ s.B (t-coneRadius 0 (r • n.1),x+r • n.1)‖ := by
  obtain ⟨C,hC,hb⟩ := source_dynamic_spatial_divergence_bound P M e i
  refine ⟨C,hC,?_⟩
  intro s t r x v n hE hB hr hrt hv he hb'
  have hn : n.1≠(0:Vec) := by intro hh; have hn := sphere_norm n; rw [hh,norm_zero] at hn; norm_num at hn
  have hz : r • (n.1 : Vec)≠0 := smul_ne_zero hr.ne' hn
  have ht : 0<t-coneRadius 0 (r • n.1) := by
    simpa only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hr.le,sphere_norm,mul_one] using sub_pos.mpr hrt
  let g : Vec → Phase := fun y => (s.E (t-coneRadius 0 y,x+y),s.B (t-coneRadius 0 y,x+y))
  have ha : DifferentiableAt ℝ (fun y : Vec => (t-coneRadius 0 y,x+y)) (r • n.1) :=
    ((differentiableAt_const t).sub (differentiableAt_coneRadius hz.symm)).prodMk
      ((differentiableAt_const x).add differentiableAt_id)
  have hg : DifferentiableAt ℝ g (r • n.1) :=
    (((field_contDiffAt_positive hE ht (x+r • n.1)).differentiableAt (by simp)).comp (r • n.1) ha).prodMk
      (((field_contDiffAt_positive hB ht (x+r • n.1)).differentiableAt (by simp)).comp (r • n.1) ha)
  exact (hb g n v r hv he hb' hr hg).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (norm_fderiv_retarded_fields x hz ht hE hB)
      (div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤3) hC) hr.le)))

lemma sourceVelocityProfile_contDiffAt (e : Vec) (i : Fin 3)
    {p : (Vec × Vec × Vec) × Vec} (hd : 1-dot p.1.1 (velocity p.2)≠0) :
    ContDiffAt ℝ 1 (sourceVelocityProfile e i) p := by
  have hn : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => z.1.1) p := contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hi := sourceAngularProfile_contDiffAt i hd
  have hm := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk (contDiffAt_const (c:=e)))
  have hdu := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk hu)
  have hforce : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec =>
      z.1.2.1+cross (velocity z.2) z.1.2.2) p :=
    contDiffAt_fst.snd.fst.add
      (contDiff_cross.contDiffAt.comp p (hu.prodMk contDiffAt_fst.snd.snd))
  exact (hi.mul (hm.div (contDiffAt_const.sub hdu) hd)).smul hforce

lemma continuousOn_sourceVelocityDivergence (e : Vec) (i : Fin 3) :
    ContinuousOn (fun p : (Vec × Vec × Vec) × Vec =>
      divergence (fun w => sourceVelocityProfile e i (p.1,w)) p.2)
      {p | 1-dot p.1.1 (velocity p.2)≠0} := by
  apply ContinuousOn.congr (f:=fun p : (Vec × Vec × Vec) × Vec =>
    ∑ j : Fin 3,(fderiv ℝ (sourceVelocityProfile e i) p (0,basis j)) j)
  · apply continuousOn_finsetSum
    intro j _ p hp
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.continuousAt.comp
      (((sourceVelocityProfile_contDiffAt e i hp).continuousAt_fderiv (by simp)).clm_apply
        continuousAt_const)).continuousWithinAt
  · intro p hp
    exact divergence_parameter_slice ((sourceVelocityProfile_contDiffAt e i hp).differentiableAt (by simp))

lemma sourceVelocityDivergence_uniform_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (E B v : Vec), ‖E‖≤M → ‖B‖≤M → ‖v‖≤P →
      |divergence (fun w => sourceVelocityProfile e i ((n.1,E,B),w)) v|≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : (Vec × Vec × Vec) × Vec =>
      divergence (fun w => sourceVelocityProfile e i (p.1,w)) p.2) K :=
    (continuousOn_sourceVelocityDivergence e i).mono (by
      intro p hp
      have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
      exact (cone_denom_pos p.2 p.1.1 hn).ne')
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n E B v hE hB hv
  apply (hC ((n.1,E,B),v) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩

lemma source_velocity_divergence_rescale (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3)
    {z : Vec} (hz : z≠0) (v : Vec) :
    divergence (fun w => sourceConeCoefficient s t x i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v =
      (coneRadius 0 z)⁻¹*
        divergence (fun w => sourceVelocityProfile e i
          ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),w)) v := by
  let a := (coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z))
  have ha : DifferentiableAt ℝ (fun w => sourceVelocityProfile e i (a,w)) v :=
    ((sourceVelocityProfile_contDiffAt e i (p:=(a,v))
      (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').differentiableAt (by simp)).comp v
      ((differentiableAt_const a).prodMk differentiableAt_id)
  have he : (fun w => sourceConeCoefficient s t x i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) =
      fun w => (coneRadius 0 z)⁻¹ • sourceVelocityProfile e i (a,w) := by
    funext w
    simp only [sourceConeCoefficient,sourceFixedCoefficient,coneSpatialCoefficient,coneLorentz,sourceVelocityProfile,a,smul_smul,mul_assoc]
  rw [he,divergence_real_const_smul ha]

lemma physical_source_velocity_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v : Vec), z≠0 → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |divergence (fun w => sourceConeCoefficient s t x i (z,w) •
        (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v|≤C/(coneRadius 0 z) := by
  obtain ⟨C,hC,hb⟩ := sourceVelocityDivergence_uniform_bound P M e i
  refine ⟨C,hC,?_⟩
  intro s t x z v hz hv hE hB
  rw [source_velocity_divergence_rescale s t x e i hz v,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))]
  have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
  exact (mul_le_mul_of_nonneg_left
    (hb ⟨coneDirection 0 z,hn⟩ _ _ v hE hB hv) (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))).trans_eq (by ring)

lemma sourceFixedFlux_uniform_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec), ‖v‖≤P → ‖E‖≤M → ‖B‖≤M →
      ‖sourceFixedFlux v E B e i n.1‖≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P) ×ˢ
    (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)
  have hK : IsCompact K := ((isCompact_sphere _ _).prod (isCompact_closedBall _ _)).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : ContinuousOn (sourceJointFlux e i) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    have hz : p.1.1≠0 := by intro hh; simp only [hh,norm_zero] at hn; norm_num at hn
    exact (sourceJointFlux_contDiffAt e i hz).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n v E B hv hE hB
  apply (hC ((n.1,v),(E,B)) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_closedBall,dist_zero_right] using hv⟩,
    by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩

lemma source_sphere_rescale (P : ℝ) (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3)
    {r : ℝ} (hr : 0 < r) (n : Sphere) :
    r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1)) =
    r*dot n.1 (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1) := by
  have he : (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1))=
      r⁻¹ • ∫ v in closedBall (0:Vec) P,
        s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
          (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1 := by
    rw [←integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      dsimp only
      rw [sourceFixedFlux_homogeneous v _ _ e i hr]
      simp only [smul_smul,mul_comm])
  rw [he,dot_smul_right]
  field_simp

lemma source_sphere_boundary_bound (P M A : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t U r : ℝ) (x : Vec),
      0 < r → r≤t → t≤U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      |∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
        s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
          (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1)) ∂sphereMeasure|≤C*r := by
  obtain ⟨K,hK,hkb⟩ := sourceFixedFlux_uniform_bound P M e i
  let C := volume.real (closedBall (0:Vec) P)*A*K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨(4*Real.pi)*C,mul_nonneg (by positivity) hC,?_⟩
  intro s t U r x hr hrt htU hf hEB
  simp_rw [source_sphere_rescale P s t x e i hr]
  have hs : t-r∈Icc (0:ℝ) U := ⟨by linarith,by linarith⟩
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (n : Sphere) : ‖r*dot n.1 (∫ v in closedBall (0:Vec) P,
      s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1)‖ ≤ r*C := by
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1) (C:=A*K) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hf _ hs _ v)
          (hkb n v _ _ (by simpa only [mem_closedBall,dist_zero_right] using hv)
            (hEB _ hs _).1 (hEB _ hs _).2) (norm_nonneg _) hA)
    have hd := abs_real_inner_le_norm n.1
      (∫ v in closedBall (0:Vec) P,s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
        (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i n.1)
    rw [sphere_norm,one_mul] at hd
    rw [norm_mul,Real.norm_of_nonneg hr.le,dot_eq_inner,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hd.trans (by
      simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,C,mul_assoc,mul_comm,mul_left_comm] using hh)) hr.le
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)
  simpa only [Real.norm_eq_abs,sphere_area,smul_eq_mul,mul_comm,mul_assoc,mul_left_comm] using hh

lemma inverse_source_majorant {a b Q r H : ℝ} (ha : 0≤a) (hb : 0≤b) (hQ : 0≤Q)
    (hr : 0 < r) (hrH : r≤H) :
    a/r^2+(a/r)*Q+b/r≤(a+(a*Q+b)*H)/r^2 := by
  calc
    _ = (a+(a*Q+b)*r)/r^2 := by field_simp; ring
    _ ≤ _ := by gcongr

lemma source_sphere_support {s : Solution} {t U P r : ℝ} (x e : Vec) (i : Fin 3)
    (hr : 0 ≤ r) (hrt : r≤t) (htU : t≤U)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ n : Sphere,r^2*dot n.1 (∫ v,s.f (t-r,x+r • n.1,v) •
      (sourceConeCoefficient s t x i (r • n.1,v) • coneSpatialLift 0 (r • n.1) v e)) ∂sphereMeasure) =
    (∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,s.f (t-r,x+r • n.1,v) •
      sourceFixedFlux v (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1)) ∂sphereMeasure) := by
  apply integral_congr_ae
  apply ae_of_all
  intro n
  have hrad : coneRadius 0 (r • n.1)=r := by
    simp only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hr,sphere_norm,mul_one]
  simp only [sourceConeCoefficient,hrad]
  change r^2*dot n.1 (∫ v,s.f (t-r,x+r • n.1,v) • sourceFixedFlux v
      (s.E (t-r,x+r • n.1)) (s.B (t-r,x+r • n.1)) e i (r • n.1))=_
  congr 2
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro v hv
  rw [hP _ ⟨by linarith,by linarith⟩ _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),zero_smul]

lemma source_bulk_support {s : Solution} {t U P ε R : ℝ} (x e : Vec) (i : Fin 3)
    (hRt : R≤t) (htU : t≤U)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,∫ v,s.f (t-coneRadius 0 z,x+z,v)*
      (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
        divergence (fun w => sourceConeCoefficient s t x i (z,w) •
          (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)) =
    ∫ z in ball (0:Vec) R \ ball (0:Vec) ε,sourceDivisionBulk P s t x e i z := by
  apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
  intro z hz
  have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    have hzR : ‖z‖<R := by simpa only [mem_ball,dist_zero_right] using hz.1
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro v hv
  rw [hP _ hu _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),zero_mul]

lemma sourceConeCoefficient_uniform_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v : Vec), z≠0 → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |sourceConeCoefficient s t x i (z,v)|≤C/‖z‖ := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (sourceAngularProfile i) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    exact (sourceAngularProfile_contDiffAt i (cone_denom_pos p.2 p.1.1 hn).ne').continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro s t x z v hz hv hE hB
  have hb := hC ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v) (by
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
    · simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB
    · simpa only [mem_closedBall,dist_zero_right] using hv)
  unfold sourceConeCoefficient sourceFixedCoefficient
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))]
  apply (mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _))
    (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg]
  ring

lemma source_particle_derivative_integrable {s : Solution} {U t P M N : ℝ} (x e : Vec) (i : Fin 3)
    (_ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (_hN : 0≤N)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    IntegrableOn (fun z => ∫ v,sourceConeCoefficient s t x i (z,v)*
      fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => sourceConeCoefficient s t x i p*
    fderiv ℝ s.f (t-coneRadius 0 p.1,x+p.1,p.2) (0,e,0)
  let A := ball (0:Vec) t \ ({0} : Set Vec)
  have hzprop {z : Vec} (hz : z∈A) : z≠0 ∧ 0<t-coneRadius 0 z ∧ t-coneRadius 0 z≤U := by
    have hzr : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz.1
    exact ⟨hz.2,by simpa [coneRadius] using sub_pos.mpr hzr,by dsimp [coneRadius]; linarith [norm_nonneg ((0:Vec)-z)]⟩
  have hfc : ContinuousOn F (A ×ˢ univ) := by
    intro p hp
    have hh := hzprop hp.1
    have hr := (contDiffAt_coneRadius (k:=1) hh.1.symm).comp p contDiffAt_fst
    have hm : ContinuousAt (fun p : Phase => (t-coneRadius 0 p.1,x+p.1,p.2)) p :=
      ((contDiffAt_const.sub hr).prodMk ((contDiffAt_const.add contDiffAt_fst).prodMk contDiffAt_snd)).continuousAt
    have hdf : ContinuousAt (fun q : Phase => fderiv ℝ s.f (t-coneRadius 0 q.1,x+q.1,q.2)) p :=
      ((particle_contDiffAt_positive hf hh.2.1 (x+p.1) p.2).continuousAt_fderiv (by simp)).comp (f:=fun q : Phase => (t-coneRadius 0 q.1,x+q.1,q.2)) hm
    exact ((sourceConeCoefficient_contDiffAt hE hB x i hh.1 hh.2.1).continuousAt.mul
      (hdf.clm_apply continuousAt_const)).continuousWithinAt
  have hzero (z : Vec) (hz : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    have hh := hzprop hz
    have hvP : P<‖v‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hv
    have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
      funext (fun y => hP _ ⟨hh.2.1.le,hh.2.2⟩ y v hvP)
    dsimp [F]
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e,he]
    simp
  obtain ⟨C,hC,hcb⟩ := sourceConeCoefficient_uniform_bound P M i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have hK : IsCompact (closedBall (0:Vec) P) := isCompact_closedBall _ _
  apply integrableOn_ball_of_punctured_bound (α:=1) (C:=D) (by norm_num)
    (continuousOn_integral_uniform_support hK hfc hzero)
  intro z hz hzt
  have hza : z∈A := ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hh := hzprop hza
  have heq : (∫ v,F (z,v))=∫ v in closedBall (0:Vec) P,F (z,v) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero z hza)).symm
  change ‖∫ v,F (z,v)‖≤_
  rw [heq,Real.rpow_neg (norm_nonneg z),Real.rpow_one]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => F (z,v)) (C:=(C/‖z‖)*(N*‖e‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      dsimp [F]
      rw [abs_mul,←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e]
      apply mul_le_mul (hcb s t x z v hh.1 (by simpa only [mem_closedBall,dist_zero_right] using hv)
        (hEB _ ⟨hh.2.1.le,hh.2.2⟩ _).1 (hEB _ ⟨hh.2.1.le,hh.2.2⟩ _).2)
      · simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans (mul_le_mul_of_nonneg_right (hfN _ ⟨hh.2.1.le,hh.2.2⟩ _ v) (norm_nonneg e))
      · exact abs_nonneg _
      · positivity)
  exact hb.trans_eq (by simp only [D,Measure.real,Measure.restrict_apply_univ]; ring)

lemma sourceAngularProfile_derivative_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (v E B : Vec), ‖v‖≤P → ‖E‖≤M → ‖B‖≤M →
      ‖fderiv ℝ (sourceAngularProfile i) ((n.1,E,B),v)‖≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fderiv ℝ (sourceAngularProfile i)) K := by
    intro p hp
    have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
    exact ((sourceAngularProfile_contDiffAt i (cone_denom_pos p.2 p.1.1 hn).ne').continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n v E B hv hE hB
  apply (hC ((n.1,E,B),v) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩

lemma sourceReceiverKernel_contDiffAt {s : Solution} {t : ℝ} (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : 0<t-coneRadius 0 p.2.1) :
    ContDiffAt ℝ 1 (sourceReceiverKernel s t i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hn := (contDiffAt_coneDirection (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hm : ContDiffAt ℝ 1 (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1)) p :=
    (contDiffAt_const.sub hr).prodMk (contDiffAt_fst.add contDiffAt_snd.fst)
  have he := (field_contDiffAt_positive hE ht (p.1+p.2.1)).comp p hm
  have hb := (field_contDiffAt_positive hB ht (p.1+p.2.1)).comp p hm
  have hprof := (sourceAngularProfile_contDiffAt i
    (p:=((coneDirection 0 p.2.1,s.E (t-coneRadius 0 p.2.1,p.1+p.2.1),s.B (t-coneRadius 0 p.2.1,p.1+p.2.1)),p.2.2))
    (cone_denom_pos p.2.2 _ (coneDirection_norm hz.symm)).ne').comp p
      ((hn.prodMk (he.prodMk hb)).prodMk contDiffAt_snd.snd)
  exact (hr.inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz.symm))).mul hprof

lemma source_receiver_fderiv_formula {s : Solution} {t : ℝ} (x z v e : Vec) (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hz : z≠0) (ht : 0<t-coneRadius 0 z) :
    fderiv ℝ (fun y => sourceConeCoefficient s t y i (z,v)) x e =
      (coneRadius 0 z)⁻¹*fderiv ℝ (sourceAngularProfile i)
        ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v)
        ((0,fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e),fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)),0) := by
  have hm := (hasFDerivAt_const (t-coneRadius 0 z) x).prodMk ((hasFDerivAt_id (𝕜:=ℝ) x).add_const z)
  have he := ((field_contDiffAt_positive hE ht (x+z)).differentiableAt (by simp)).hasFDerivAt.comp x hm
  have hb := ((field_contDiffAt_positive hB ht (x+z)).differentiableAt (by simp)).hasFDerivAt.comp x hm
  have hp := ((sourceAngularProfile_contDiffAt i
    (p:=((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),v))
    (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').differentiableAt (by simp)).hasFDerivAt.comp x
      (((hasFDerivAt_const (coneDirection 0 z) x).prodMk (he.prodMk hb)).prodMk (hasFDerivAt_const v x))
  have hh := hp.const_mul ((coneRadius 0 z)⁻¹)
  change HasFDerivAt (fun y => sourceConeCoefficient s t y i (z,v)) _ x at hh
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L e) hh.fderiv

lemma physical_source_receiver_bound (P M : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v e : Vec),
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      z≠0 → 0<t-coneRadius 0 z → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |fderiv ℝ (fun y => sourceConeCoefficient s t y i (z,v)) x e|≤
        C/‖z‖*max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖
          ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖*‖e‖ := by
  obtain ⟨C,hC,hcb⟩ := sourceAngularProfile_derivative_bound P M i
  refine ⟨C,hC,?_⟩
  intro s t x z v e hE hB hz ht hv he hb
  rw [source_receiver_fderiv_formula x z v e i hE hB hz ht,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))]
  let Q := max ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖
  have hQ : 0≤Q := (norm_nonneg _).trans (le_max_left _ _)
  have he' : ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e)‖≤Q*‖e‖ := by
    exact (ContinuousLinearMap.le_opNorm _ (0,e)).trans (by
      simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg e)] using mul_le_mul_of_nonneg_right
        (le_max_left ‖fderiv ℝ s.E (t-coneRadius 0 z,x+z)‖ _) (norm_nonneg ((0:ℝ),e)))
  have hb' : ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)‖≤Q*‖e‖ := by
    exact (ContinuousLinearMap.le_opNorm _ (0,e)).trans (by
      simpa only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg e)] using mul_le_mul_of_nonneg_right
        (le_max_right _ ‖fderiv ℝ s.B (t-coneRadius 0 z,x+z)‖) (norm_nonneg ((0:ℝ),e)))
  have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
  have hd := hcb ⟨coneDirection 0 z,hn⟩ v _ _ hv he hb
  have harg : ‖(((0:Vec),fderiv ℝ s.E (t-coneRadius 0 z,x+z) (0,e),
      fderiv ℝ s.B (t-coneRadius 0 z,x+z) (0,e)),(0:Vec))‖≤Q*‖e‖ := by
    simp only [Prod.norm_mk,norm_zero]
    exact max_le (max_le (by positivity) (max_le he' hb')) (by positivity)
  have hh := (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hd harg (norm_nonneg _) hC)
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (show 0 ≤ coneRadius 0 z from norm_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg,Q]
  ring

lemma sourceWeightedPacket_contDiffAt {s : Solution} {t : ℝ} (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : 0<t-coneRadius 0 p.2.1) :
    ContDiffAt ℝ 1 (sourceWeightedPacket s t i) p := by
  have hr := (contDiffAt_coneRadius (k:=1) hz.symm).comp p contDiffAt_snd.fst
  have hm : ContDiffAt ℝ 1 (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) p :=
    (contDiffAt_const.sub hr).prodMk ((contDiffAt_fst.add contDiffAt_snd.fst).prodMk contDiffAt_snd.snd)
  exact (sourceReceiverKernel_contDiffAt i hE hB hz ht).mul
    ((particle_contDiffAt_positive hf ht (p.1+p.2.1) p.2.2).comp p hm)

lemma sourceWeightedPacket_fderiv {s : Solution} {t : ℝ} (x z v e : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hz : z≠0) (ht : 0<t-coneRadius 0 z) :
    fderiv ℝ (sourceWeightedPacket s t i) (x,z,v) (e,0,0)=
      fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)*s.f (t-coneRadius 0 z,x+z,v)+
      sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0) := by
  have hk := (sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz ht).differentiableAt (by simp)
  have hF := (sourceWeightedPacket_contDiffAt i hf hE hB (p:=(x,z,v)) hz ht).differentiableAt (by simp)
  rw [←retarded_packet_spatial_fderiv hF e,←retarded_packet_spatial_fderiv hk e]
  have hkp := hk.hasFDerivAt.comp x ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (z,v) x))
  have hm := (hasFDerivAt_const (t-coneRadius 0 z) x).prodMk
    (((hasFDerivAt_id (𝕜:=ℝ) x).add_const z).prodMk (hasFDerivAt_const v x))
  have hfp := (particle_differentiableAt_positive hf ht (x+z) v).hasFDerivAt.comp x hm
  have hh := hkp.mul hfp
  change HasFDerivAt (fun y => sourceWeightedPacket s t i (y,z,v)) _ x at hh
  change HasFDerivAt (fun y => sourceReceiverKernel s t i (y,z,v)) _ x at hkp
  rw [hh.fderiv,hkp.fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,
    zero_apply,smul_eq_mul,Function.comp_apply,id_eq,sourceReceiverKernel]
  ring

lemma source_packet_estimates (P A M N Q : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hN : 0≤N) (hQ : 0≤Q) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧ ∀ (s : Solution) (U t : ℝ), t≤U →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceWeightedPacket s t i (x,z,v)|≤C/‖z‖ ∧
      |fderiv ℝ (sourceWeightedPacket s t i) (x,z,v) (e,0,0)|≤D/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := sourceConeCoefficient_uniform_bound P M i
  obtain ⟨L,hL,hlb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*A,L*Q*‖e‖*A+K*N*‖e‖,by positivity,by positivity,?_⟩
  intro s U t htU hf hE hB hfA hEB hDF hfN x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    have hr : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    rw [hr]
    constructor <;> linarith [norm_nonneg z]
  have hc := hkb s t x z v hz hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd := hlb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤L/‖z‖*Q*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  have hfd : |fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤N*‖e‖ := by
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hu.1 _ _) e]
    exact (ContinuousLinearMap.le_opNorm _ e).trans
      (mul_le_mul_of_nonneg_right (hfN _ ⟨hu.1.le,hu.2⟩ _ v) (norm_nonneg e))
  constructor
  · change |sourceConeCoefficient s t x i (z,v)*s.f (t-coneRadius 0 z,x+z,v)|≤_
    rw [abs_mul]
    exact (mul_le_mul hc (hfA _ ⟨hu.1.le,hu.2⟩ _ v) (abs_nonneg _) (by positivity)).trans_eq (by ring)
  · rw [sourceWeightedPacket_fderiv x z v e i hf hE hB hz hu.1]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    exact (add_le_add (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ v) (abs_nonneg _) (by positivity))
      (mul_le_mul hc hfd (abs_nonneg _) (by positivity))).trans_eq (by ring)

lemma hasDerivAt_electric_source_integral {s : Solution} {U t P A M N Q : ℝ}
    (x e : Vec) (i : Fin 3) (a : ℝ) (htU : t≤U)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hA : 0≤A) (hN : 0≤N) (hQ : 0≤Q)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hEB : ∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M)
    (hDF : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,
      sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))
      (∫ z in ball (0:Vec) t,∫ v,fderiv ℝ (sourceWeightedPacket s t i) (x+a • e,z,v) (e,0,0)) a := by
  obtain ⟨C,D,hC,hD,hb⟩ := source_packet_estimates P A M N Q e i hA hN hQ
  have hbc := hb s U t htU hf hE hB hfA hEB hDF hfN
  apply hasDerivAt_retarded_packet_integral (F:=sourceWeightedPacket s t i) (P:=P) (C:=C) (D:=D) ?_ ?_
    (fun x z v hz hzt hv => (hbc x z v hz hzt hv).1) x e a (fun x z v hz hzt hv => (hbc x z v hz hzt hv).2)
  · intro p hp ht
    apply sourceWeightedPacket_contDiffAt i hf hE hB hp
    simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr ht
  · intro x z v hz hzt hv
    have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
      simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
      constructor <;> linarith [norm_nonneg z]
    simp only [sourceWeightedPacket,hP _ hu _ v hv,mul_zero]

lemma retarded_packet_inner_integrable {F : Vec × Phase → ℝ} {t P : ℝ}
    (hc : ∀ p : Vec × Phase, p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p)
    (hz : ∀ x z v : Vec, z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0)
    (x z : Vec) (hz0 : z≠0) (hzt : ‖z‖<t) : Integrable (fun v => F (x,z,v)) := by
  have hcont : Continuous (fun v => F (x,z,v)) := continuous_iff_continuousAt.mpr (fun v =>
    (hc (x,z,v) hz0 hzt).comp (f:=fun w : Vec => (x,z,w)) (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall (0:Vec) P)
    (fun v hv => hz x z v hz0 hzt (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)))

lemma sourceReceiverParticlePacket_continuousAt {s : Solution} {t : ℝ} (e : Vec) (i : Fin 3)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {p : Vec × Phase} (hz : p.2.1≠0) (ht : ‖p.2.1‖<t) :
    ContinuousAt (sourceReceiverParticlePacket s t e i) p := by
  have hu : 0<t-coneRadius 0 p.2.1 := by simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr ht
  have hm : ContinuousAt (fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) p := (continuousAt_const.sub ((contDiffAt_coneRadius (k:=1) hz.symm).continuousAt.comp (f:=fun q : Vec × Phase => q.2.1) continuousAt_snd.fst)).prodMk
    ((continuousAt_fst.add continuousAt_snd.fst).prodMk continuousAt_snd.snd)
  exact (((sourceReceiverKernel_contDiffAt i hE hB hz hu).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).mul
    ((particle_contDiffAt_positive hf hu (p.1+p.2.1) p.2.2).continuousAt.comp (f:=fun q : Vec × Phase => (t-coneRadius 0 q.2.1,q.1+q.2.1,q.2.2)) hm)

lemma source_receiver_packet_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t Q : ℝ),t≤U → 0≤Q →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceReceiverParticlePacket s t e i (x,z,v)|≤C*Q/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*‖e‖*A,by positivity,?_⟩
  intro s U t Q htU hQ hE hB hfA hEB hDF x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  have hd := hkb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤K/‖z‖*Q*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  exact (by
    dsimp [sourceReceiverParticlePacket]
    rw [abs_mul]
    exact (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ _) (abs_nonneg _) (by positivity)).trans_eq (by ring))

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_VolterraKernels
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

lemma radial_volterra_majorant_integrable {t C : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn (fun z : Vec => C*g (t-‖z‖)/‖z‖^2) (ball (0:Vec) t) := by
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0:Vec) t).exists_bound_of_continuousOn
    (f:=fun z : Vec => C*g (t-‖z‖)) (by fun_prop)
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=D) (by norm_num)
  · intro z hz
    have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz.2
    exact ((continuous_const.mul (hg.comp (continuous_const.sub continuous_norm))).continuousAt.div
      (continuous_norm.pow 2).continuousAt (pow_ne_zero 2 hn)).continuousWithinAt
  · intro z hz hzt
    rw [norm_div,norm_pow,norm_norm,Real.rpow_neg (norm_nonneg z),Real.rpow_two]
    exact (div_le_div_of_nonneg_right (hD z (by
      simpa only [mem_closedBall,dist_zero_right] using hzt.le)) (sq_nonneg _)).trans_eq (by ring)

lemma kernel_volterra_norm_subset {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {F : Vec → W} {t C : ℝ} {S : Set Vec}
    (ht : 0≤t) (hC : 0≤C) (hS : MeasurableSet S) (hsub : S⊆ball (0:Vec) t)
    {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ u∈Icc (0:ℝ) t,0≤g u)
    (hb : ∀ z∈S,z≠0 → ‖F z‖≤C*g (t-‖z‖)/‖z‖^2) :
    ‖∫ z in S,F z‖≤(4*Real.pi)*C*(∫ u in Icc (0:ℝ) t,g u) := by
  let G : Vec → ℝ := fun z => C*g (t-‖z‖)/‖z‖^2
  have hG : IntegrableOn G (ball (0:Vec) t) := radial_volterra_majorant_integrable hg
  have hgball (z : Vec) (hz : z∈ball (0:Vec) t) : 0≤g (t-‖z‖) :=
    hg0 _ ⟨by
      have hh : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
      exact sub_nonneg.mpr hh.le,
      sub_le_self _ (norm_nonneg z)⟩
  have hGb (z : Vec) (hz : z∈ball (0:Vec) t) : 0≤G z := by
    have hh := hgball z hz
    dsimp [G]; positivity
  have hh := norm_integral_le_of_norm_le (hG.mono_set hsub) (f:=F) (by
    filter_upwards [ae_restrict_mem hS,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    exact hb z hz hz0)
  apply hh.trans
  apply (setIntegral_mono_set hG (by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact hGb z hz) (ae_of_all _ (fun z hz => hsub hz))).trans
  apply (le_abs_self _).trans
  change ‖∫ z in ball (0:Vec) t,G z‖≤_
  apply kernel_volterra_norm ht hC hG hg
  intro z hz hzt
  dsimp [G]
  have hgzt := hg0 (t-‖z‖) ⟨sub_nonneg.mpr hzt,sub_le_self _ (norm_nonneg z)⟩
  rw [abs_of_nonneg (by positivity)]

lemma source_volterra_factor {a b q H : ℝ} (ha : 0≤a) (hb : 0≤b) (hq : 0≤q) (hH : 0≤H) :
    a+(a*q+b)*H≤(a+b)*(1+H)*(1+q) := by
  have hh : a*q+b≤(a+b)*(1+q) := by nlinarith [mul_nonneg hb hq]
  have hh' := mul_le_mul_of_nonneg_right hh hH
  nlinarith [mul_nonneg (add_nonneg ha hb) hq]

lemma source_division_bulk_annulus_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H ε R : ℝ) (x : Vec) (g : ℝ → ℝ),
      0≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) → 0<ε → ε≤R → R<t → t≤U → U≤H →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,sourceDivisionBulk P s t x e i z|≤
        C*(1+H)*(∫ u in Icc (0:ℝ) t,1+g u) := by
  obtain ⟨Ks,hKs,hks⟩ := physical_source_spatial_bound P M e i
  obtain ⟨Kv,hKv,hkv⟩ := physical_source_velocity_bound P M e i
  let V := volume.real (closedBall (0:Vec) P)*A
  have hV : 0≤V := by dsimp [V]; positivity
  let C := 4*Real.pi*V*(3*Ks+Kv)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s U t H ε R x g hH hg hg0 hε hεR hRt htU hUH hE hB hf hEB hDF
  let L := V*(3*Ks+Kv)*(1+H)
  have hL : 0≤L := by dsimp [L]; positivity
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (z : Vec) (hz : z∈ball (0:Vec) R \ ball (0:Vec) ε) :
      ‖sourceDivisionBulk P s t x e i z‖≤L*(1+g (t-‖z‖))/‖z‖^2 := by
    have hzr : ‖z‖<R ∧ ε≤‖z‖ := by simpa only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt] using hz
    have hzn : z≠0 := norm_pos_iff.mp (hε.trans_le hzr.2)
    have hzpos : 0<‖z‖ := norm_pos_iff.mpr hzn
    have hrad : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
      rw [hrad]
      exact ⟨by linarith,by linarith [norm_nonneg z]⟩
    have hgpos : 0≤g (t-‖z‖) := by
      rw [←hrad]; exact hg0 _ ⟨hu.1.le,hu.2⟩
    let n : Sphere := ⟨‖z‖⁻¹ • z,by
      simp only [mem_sphere,dist_zero_right,norm_smul,norm_inv,norm_norm,
        inv_mul_cancel₀ hzpos.ne']⟩
    have hn : ‖z‖ • (n.1 : Vec)=z := by simp only [n,smul_smul,mul_inv_cancel₀ hzpos.ne',one_smul]
    have hs (v : Vec) (hv : ‖v‖≤P) :
        |divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z|≤
        3*Ks/‖z‖^2+(3*Ks/‖z‖)*g (t-‖z‖) := by
      have hh := hks s t ‖z‖ x v n hE hB hzpos (hzr.1.trans hRt) hv
      rw [hn] at hh
      apply (hh (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2).trans
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (by simpa only [hrad] using max_le (hDF _ hu _).1 (hDF _ hu _).2) (by positivity))
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (fun y => sourceConeCoefficient s t x i (y,v) • coneSpatialLift 0 y v e) z+
          divergence (fun w => sourceConeCoefficient s t x i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v))
      (C:=A*(((3*Ks+Kv)*(1+H)*(1+g (t-‖z‖)))/‖z‖^2)) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        have hvP : ‖v‖≤P := by simpa only [mem_closedBall,dist_zero_right] using hv
        have hvb := hkv s t x z v hzn hvP (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
        rw [hrad] at hvb
        rw [Real.norm_eq_abs,abs_mul]
        apply mul_le_mul (hf _ ⟨hu.1.le,hu.2⟩ _ v) _ (abs_nonneg _) hA
        exact ((abs_add_le _ _).trans (add_le_add (hs v hvP) hvb)).trans
          ((inverse_source_majorant (by positivity) hKv hgpos hzpos (hzr.1.le.trans (hRt.le.trans (htU.trans hUH)))).trans
            (div_le_div_of_nonneg_right (source_volterra_factor (by positivity) hKv hgpos hH) (sq_nonneg _))))
    exact hh.trans_eq (by simp only [Measure.real,Measure.restrict_apply_univ,L,V]; ring)
  have hh := kernel_volterra_norm_subset (hε.le.trans (hεR.trans hRt.le)) hL
    (measurableSet_ball.diff measurableSet_ball)
    (show ball (0:Vec) R \ ball (0:Vec) ε ⊆ ball (0:Vec) t from fun z hz => ball_subset_ball hRt.le hz.1)
    (g:=fun u => 1+g u) (continuous_const.add hg)
    (fun u hu => by have hh := hg0 u ⟨hu.1,hu.2.trans htU⟩; positivity)
    (fun z hz _ => hb z hz)
  rw [Real.norm_eq_abs] at hh
  exact hh.trans_eq (by dsimp [C,L]; ring)

lemma electric_source_annulus_gradient_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H ε R : ℝ) (x : Vec) (g : ℝ → ℝ),
      0≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) → 0<ε → ε≤R → R<t → t≤U → U≤H →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤
        C*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
  obtain ⟨C,hC,hb⟩ := source_division_bulk_annulus_volterra_bound P A M e i hA
  obtain ⟨B,hB,hbd⟩ := source_sphere_boundary_bound P M A e i hA
  refine ⟨C+2*B,by positivity,?_⟩
  intro s U t H ε R x g hH hg hg0 hε hεR hRt htU hUH hf hE hB' hc heq hfA hfP hEB hDF
  have hid := electric_source_division_annulus hf hE hB' hc heq htU hε hεR hRt x e i
  rw [hid,source_sphere_support x e i (hε.le.trans hεR) hRt.le htU hfP,
    source_sphere_support x e i hε.le (hεR.trans hRt.le) htU hfP,
    source_bulk_support x e i hRt.le htU hfP]
  have hout := hbd s t U R x (hε.trans_le hεR) hRt.le htU hfA hEB
  have hin := hbd s t U ε x hε (hεR.trans hRt.le) htU hfA hEB
  have hbulk := hb s U t H ε R x g hH hg hg0 hε hεR hRt htU hUH hE hB' hfA hEB hDF
  apply (abs_sub _ _).trans
  apply (add_le_add ((abs_sub _ _).trans (add_le_add hout hin)) hbulk).trans
  have hRH : R≤H := hRt.le.trans (htU.trans hUH)
  have heH : ε≤H := hεR.trans hRH
  have hW : 0≤(1+H)*(∫ u in Icc (0:ℝ) t,1+g u) := mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_Icc (fun u hu => by have hh := hg0 u ⟨hu.1,hu.2.trans htU⟩; positivity))
  have hBR : B*R≤B*H := mul_le_mul_of_nonneg_left hRH hB
  have hBe : B*ε≤B*H := mul_le_mul_of_nonneg_left heH hB
  have hBW : 0≤B*((1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := mul_nonneg hB hW
  have hCH := mul_nonneg hC hH
  nlinarith

lemma electric_source_particle_gradient_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t H N : ℝ) (x : Vec) (g : ℝ → ℝ),
      0<t → t≤U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤C*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
  obtain ⟨C,hC,hb⟩ := electric_source_annulus_gradient_volterra_bound P A M e i hA
  refine ⟨C,hC,?_⟩
  intro s U t H N x g ht htU hUH hg hg0 hN hf hE hB hc heq hfA hP hEB hDF hfN
  apply norm_integral_ball_of_annulus_bound ht
    (source_particle_derivative_integrable x e i ht htU hf hN hE hB hEB hP hfN)
  intro ε R hε hεR hRt
  exact hb s U t H ε R x g (ht.le.trans (htU.trans hUH)) hg hg0 hε hεR hRt htU hUH
    hf hE hB hc heq hfA hP hEB hDF

lemma source_receiver_packet_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t : ℝ) (g : ℝ → ℝ),t≤U → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      ∀ x z v : Vec,z≠0 → ‖z‖<t → ‖v‖≤P →
      |sourceReceiverParticlePacket s t e i (x,z,v)|≤C*g (t-‖z‖)/‖z‖ := by
  obtain ⟨K,hK,hkb⟩ := physical_source_receiver_bound P M i
  refine ⟨K*‖e‖*A,by positivity,?_⟩
  intro s U t g htU hg0 hE hB hfA hEB hDF x z v hz hzt hv
  have hu : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  have hQ : 0≤g (t-coneRadius 0 z) := hg0 _ ⟨hu.1.le,hu.2⟩
  have hd := hkb s t x z v e hE hB hz hu.1 hv (hEB _ ⟨hu.1.le,hu.2⟩ _).1 (hEB _ ⟨hu.1.le,hu.2⟩ _).2
  have hd' : |fderiv ℝ (sourceReceiverKernel s t i) (x,z,v) (e,0,0)|≤K/‖z‖*g (t-coneRadius 0 z)*‖e‖ := by
    rw [←retarded_packet_spatial_fderiv
      ((sourceReceiverKernel_contDiffAt i hE hB (p:=(x,z,v)) hz hu.1).differentiableAt (by simp)) e]
    exact hd.trans (by gcongr; exact max_le (hDF _ hu _).1 (hDF _ hu _).2)
  exact (by
    dsimp [sourceReceiverParticlePacket]
    rw [abs_mul]
    exact (mul_le_mul hd' (hfA _ ⟨hu.1.le,hu.2⟩ _ _) (abs_nonneg _) (by positivity)).trans_eq (by simp only [coneRadius,zero_sub,norm_neg]; ring))

lemma electric_source_receiver_integral_volterra_bound (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t H : ℝ) (x : Vec) (g : ℝ → ℝ),
      0≤t → t≤U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      |∫ z in ball (0:Vec) t,∫ v,sourceReceiverParticlePacket s t e i (x,z,v)|≤
        C*H*(∫ u in Icc (0:ℝ) t,g u) := by
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_volterra_bound P A M e i hA
  let V := volume.real (closedBall (0:Vec) P)
  have hV : 0≤V := by dsimp [V]; positivity
  refine ⟨4*Real.pi*V*K,by positivity,?_⟩
  intro s U t H x g ht htU hUH hg hg0 hE hB hfA hP hEB hDF
  have hH : 0≤H := ht.trans (htU.trans hUH)
  rw [←Real.norm_eq_abs]
  apply (kernel_volterra_norm_subset ht (C:=V*K*H) (by positivity) measurableSet_ball
    (Subset.rfl) hg (fun u hu => hg0 u ⟨hu.1,hu.2.trans htU⟩) ?_).trans_eq (by ring)
  intro z hz hz0
  have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
  have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Icc]
    constructor <;> linarith [norm_nonneg z]
  have hgu : 0≤g (t-‖z‖) := by simpa only [coneRadius,zero_sub,norm_neg] using hg0 _ hu
  have hh := norm_velocity_integral_bound (P:=P) (g:=fun v => sourceReceiverParticlePacket s t e i (x,z,v))
    (fun v hv => by simp only [sourceReceiverParticlePacket,hP _ hu _ v hv,mul_zero])
    (hkb s U t g htU hg0 hE hB hfA hEB hDF x z · hz0 hzt)
  apply hh.trans
  change V*(K*g (t-‖z‖)/‖z‖)≤_
  have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz0
  calc
    _ = (V*K*g (t-‖z‖)*‖z‖)/‖z‖^2 := by field_simp
    _ ≤ (V*K*g (t-‖z‖)*H)/‖z‖^2 := by gcongr; exact hzt.le.trans (htU.trans hUH)
    _ = _ := by ring

lemma electric_source_deriv_volterra_bound_oai (P A M : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (U t H N : ℝ) (x : Vec) (g : ℝ → ℝ),
      0<t → t≤U → U≤H → Continuous g → (∀ u∈Icc (0:ℝ) U,0≤g u) → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤g u ∧ ‖fderiv ℝ s.B (u,y)‖≤g u) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => ∫ z in ball (0:Vec) t,∫ v,
        sourceConeCoefficient s t (x+q • e) i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)) 0|≤
        C*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
  obtain ⟨C₁,hC₁,hb₁⟩ := electric_source_particle_gradient_volterra_bound P A M e i hA
  obtain ⟨C₂,hC₂,hb₂⟩ := electric_source_receiver_integral_volterra_bound P A M e i hA
  obtain ⟨K,hK,hkb⟩ := source_receiver_packet_bound P A M e i hA
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro s U t H N x g ht htU hUH hg hg0 hN hf hE hB hc heq hfA hP hEB hDF hfN
  obtain ⟨Q₀,hQ₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (f:=g) hg.continuousOn
  let Q := max Q₀ 0
  have hQ : 0≤Q := le_max_right _ _
  have hDFconst : ∀ u∈Ioc (0:ℝ) U, ∀ y, ‖fderiv ℝ s.E (u,y)‖≤Q ∧ ‖fderiv ℝ s.B (u,y)‖≤Q := by
    intro u hu y
    have hh : g u≤Q := (le_abs_self _).trans ((hQ₀ u ⟨hu.1.le,hu.2⟩).trans (le_max_left _ _))
    exact ⟨(hDF u hu y).1.trans hh,(hDF u hu y).2.trans hh⟩
  have hH : 0≤H := ht.le.trans (htU.trans hUH)
  have hprop (z : Vec) (hz : ‖z‖<t) : t-coneRadius 0 z∈Ioc (0:ℝ) U := by
    simp only [coneRadius,zero_sub,norm_neg,mem_Ioc]
    constructor <;> linarith [norm_nonneg z]
  let R := sourceReceiverParticlePacket s t e i
  let F := fun p : Vec × Phase => fderiv ℝ (sourceWeightedPacket s t i) p (e,0,0)
  have hRc : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt R p :=
    fun p hp hpt => sourceReceiverParticlePacket_continuousAt e i hf hE hB hp hpt
  have hRz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → R (x,z,v)=0 := by
    intro x z v hz hzt hv
    simp only [R,sourceReceiverParticlePacket,hP _ ⟨(hprop z hzt).1.le,(hprop z hzt).2⟩ _ v hv,mul_zero]
  have hweighted : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContDiffAt ℝ 1 (sourceWeightedPacket s t i) p :=
    fun p hp hpt => sourceWeightedPacket_contDiffAt i hf hE hB hp (hprop p.2.1 hpt).1
  have hWz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → sourceWeightedPacket s t i (x,z,v)=0 := by
    intro x z v hz hzt hv
    simp only [sourceWeightedPacket,hP _ ⟨(hprop z hzt).1.le,(hprop z hzt).2⟩ _ v hv,mul_zero]
  have hFc : ∀ p : Vec × Phase,p.2.1≠0 → ‖p.2.1‖<t → ContinuousAt F p := by
    intro p hp hpt
    exact ((hweighted p hp hpt).continuousAt_fderiv (by simp)).clm_apply continuousAt_const
  have hFz : ∀ x z v : Vec,z≠0 → ‖z‖<t → P<‖v‖ → F (x,z,v)=0 :=
    fun x z v hz hzt hv => retarded_packet_derivative_zero hweighted hWz x z v e hz hzt hv
  have hRi := retarded_packet_integrable x hRc hRz (hkb s U t Q htU hQ hE hB hfA hEB hDFconst)
  have hPi := source_particle_derivative_integrable x e i ht htU hf hN hE hB hEB hP hfN
  have hsplit : (∫ z in ball (0:Vec) t,∫ v,F (x,z,v))=
      (∫ z in ball (0:Vec) t,∫ v,R (x,z,v))+
      (∫ z in ball (0:Vec) t,∫ v,sourceConeCoefficient s t x i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) := by
    rw [←integral_add hRi hPi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hzt : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
    have hFi := retarded_packet_inner_integrable hFc hFz x z hz0 hzt
    have hRi' := retarded_packet_inner_integrable hRc hRz x z hz0 hzt
    have hh : (∫ v,F (x,z,v))-(∫ v,R (x,z,v))=
        ∫ v,sourceConeCoefficient s t x i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0) := by
      rw [←integral_sub hFi hRi']
      apply integral_congr_ae
      exact ae_of_all _ (fun v => by
        dsimp [F,R,sourceReceiverParticlePacket]
        rw [sourceWeightedPacket_fderiv x z v e i hf hE hB hz0 (hprop z hzt).1]
        ring)
    linarith
  rw [(hasDerivAt_electric_source_integral x e i 0 htU hf hE hB hA hN hQ hP hfA hEB hDFconst hfN).deriv]
  simp only [zero_smul,add_zero]
  change |∫ z in ball (0:Vec) t,∫ v,F (x,z,v)|≤_
  rw [hsplit]
  apply (abs_add_le _ _).trans
  apply (add_le_add (hb₂ s U t H x g ht.le htU hUH hg hg0 hE hB hfA hP hEB hDF)
    (hb₁ s U t H N x g ht htU hUH hg hg0 hN hf hE hB hc heq hfA hP hEB hDF hfN)).trans
  have hJ : 0≤∫ u in Icc (0:ℝ) t,1+g u := setIntegral_nonneg measurableSet_Icc
    (fun u hu => by have hh := hg0 u ⟨hu.1,hu.2.trans htU⟩; positivity)
  have hG : 0≤∫ u in Icc (0:ℝ) t,g u := setIntegral_nonneg measurableSet_Icc
    (fun u hu => hg0 u ⟨hu.1,hu.2.trans htU⟩)
  have hGJ : (∫ u in Icc (0:ℝ) t,g u)≤∫ u in Icc (0:ℝ) t,1+g u :=
    integral_mono hg.integrableOn_Icc (continuous_const.add hg).integrableOn_Icc (fun u => by linarith)
  have hh : C₂*H*(∫ u in Icc (0:ℝ) t,g u)≤C₂*(H+(1+H)*(∫ u in Icc (0:ℝ) t,1+g u)) := by
    have hmul : H*(∫ u in Icc (0:ℝ) t,g u)≤(1+H)*(∫ u in Icc (0:ℝ) t,1+g u) := by
      gcongr; linarith
    have hh' := mul_le_mul_of_nonneg_left (hmul.trans (le_add_of_nonneg_left hH)) hC₂
    nlinarith
  nlinarith

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.electric_source_deriv_volterra_bound_oai := @OAI.RVM.electric_source_deriv_volterra_bound_oai
