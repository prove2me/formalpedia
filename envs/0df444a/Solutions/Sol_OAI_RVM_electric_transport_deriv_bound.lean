-- Prove2me | solution 1 for OAI.RVM.electric_transport_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:21:34.769108+00:00
-- url     : https://prove2.me/submissions/3fe8195c-9c59-40ae-b58b-547ff6933574

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

lemma fderiv_weighted_param {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H × Vec → ℝ} {w : Vec → ℝ} {p : H} {v : Vec}
    (hF : DifferentiableAt ℝ F (p,v)) (hw : DifferentiableAt ℝ w v) (b : H) :
    fderiv ℝ (fun z : H × Vec => w z.2 * F z) (p,v) (b,0) =
      w v * fderiv ℝ F (p,v) (b,0) := by
  have hdw := hw.hasFDerivAt.comp (p,v) (hasFDerivAt_snd (𝕜 := ℝ) (p := (p,v)))
  have he := congrArg (fun L : (H × Vec) →L[ℝ] ℝ => L (b,0)) (hdw.mul hF.hasFDerivAt).fderiv
  change fderiv ℝ (fun z : H × Vec => w z.2 * F z) (p,v) (b,0) =
    w v * fderiv ℝ F (p,v) (b,0) + F (p,v) * fderiv ℝ w v 0 at he
  simpa only [map_zero, mul_zero, add_zero] using he

lemma fderiv_weighted_integral_uniform_support_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set H} {K : Set Vec} {F : H × Vec → ℝ} {p : H} {w : Vec → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) (hw : ContDiff ℝ 1 w)
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (b : H) :
    fderiv ℝ (fun x => ∫ v : Vec, w v * F (x,v)) p b =
      ∫ v : Vec, w v * fderiv ℝ F (p,v) (b,0) := by
  have hG : ContDiffOn ℝ 1 (fun z : H × Vec => w z.2 * F z) (U ×ˢ univ) :=
    (hw.comp contDiff_snd).contDiffOn.mul hF
  rw [fderiv_integral_uniform_support_apply hU hK hp hG
    (fun x hx v hv => by simp only [hzero x hx v hv, mul_zero])]
  apply integral_congr_ae
  filter_upwards [] with v
  exact fderiv_weighted_param
    (((hF (p,v) ⟨hp,mem_univ _⟩).contDiffAt
      ((hU.prod isOpen_univ).mem_nhds ⟨hp,mem_univ _⟩)).differentiableAt (by simp))
    (hw.differentiable (by simp) v) b

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

end SphereJets

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

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma integral_annulus_polar {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Vec→W} {ε R : ℝ} (hε : 0<ε)
    (hg : IntegrableOn g (ball (0:Vec) R \ ball (0:Vec) ε)) :
    (∫z in ball (0:Vec) R \ ball (0:Vec) ε,g z)=
      ∫n : Sphere,∫r in Ico ε R,r^2 • g (r • n.1) ∂volume ∂sphereMeasure := by
  classical
  let H := (ball (0:Vec) R \ ball (0:Vec) ε).indicator g
  have hm : MeasurableSet (ball (0:Vec) R \ ball (0:Vec) ε) := measurableSet_ball.diff measurableSet_ball
  have hi : Integrable H := (integrable_indicator_iff hm).mpr hg
  rw [←integral_indicator hm]
  change (∫z,H z)=_
  rw [integral_polar hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun n=>by
    dsimp only
    have he : ∀r∈Ioi (0:ℝ),r^2 • H (r • n.1)=
        (Ico ε R).indicator (fun r=>r^2 • g (r • n.1)) r := by
      intro r hr
      have hnorm : ‖r • n.1‖=r := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,sphere_norm,mul_one]
      have hmem : r • n.1∈ball (0:Vec) R \ ball (0:Vec) ε ↔ r∈Ico ε R := by
        simp only [Set.mem_sdiff,mem_ball_zero_iff,hnorm,mem_Ico,not_lt]
        exact and_comm
      by_cases h : r∈Ico ε R
      · rw [show H (r • n.1)=g (r • n.1) from indicator_of_mem (hmem.mpr h) g,
          indicator_of_mem h]
      · rw [show H (r • n.1)=0 from indicator_of_notMem (fun hh => h (hmem.mp hh)) g,
          smul_zero,indicator_of_notMem h]
    rw [setIntegral_congr_fun measurableSet_Ioi he,setIntegral_indicator measurableSet_Ico]
    have hset : Ioi (0:ℝ) ∩ Ico ε R=Ico ε R := by
      ext r
      simp only [mem_inter_iff,mem_Ioi,mem_Ico]
      exact ⟨fun h => h.2,fun h => ⟨hε.trans_le h.1,h⟩⟩
    rw [hset])

lemma fderiv_degree_neg_two {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0 < r → ∀ z, F (r • z)=(r^2)⁻¹ • F z)
    {r : ℝ} (hr : 0 < r) {z : Vec}
    (hz : DifferentiableAt ℝ F z) (hrz : DifferentiableAt ℝ F (r • z)) (e : Vec) :
    fderiv ℝ F (r • z) e=(r^3)⁻¹ • fderiv ℝ F z e := by
  have hm : HasFDerivAt (fun y : Vec => r • y) (r • ContinuousLinearMap.id ℝ Vec) z :=
    (hasFDerivAt_id z).const_smul r
  have h₁ := hrz.hasFDerivAt.comp z hm
  have h₂ := hz.hasFDerivAt.const_smul ((r^2)⁻¹)
  have heq : (fun y : Vec => F (r • y))=(fun y : Vec => (r^2)⁻¹ • F y) := funext (hh r hr)
  change HasFDerivAt (fun y : Vec => F (r • y)) _ _ at h₁
  rw [heq] at h₁
  have hv := congrArg (fun L : Vec →L[ℝ] Vec => L e) (h₁.unique h₂)
  change fderiv ℝ F (r • z) (r • e)=(r^2)⁻¹ • fderiv ℝ F z e at hv
  rw [map_smul] at hv
  have hv' := congrArg (fun a : Vec => r⁻¹ • a) hv
  simpa only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul,
    show r⁻¹*(r^2)⁻¹=(r^3)⁻¹ by field_simp] using hv'

lemma divergence_degree_neg_two {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0 < r → ∀ z, F (r • z)=(r^2)⁻¹ • F z)
    (hF : ∀ z≠0, DifferentiableAt ℝ F z) {r : ℝ} (hr : 0 < r) {z : Vec} (hz : z≠0) :
    divergence F (r • z)=(r^3)⁻¹*divergence F z := by
  have hrz : r • z≠0 := smul_ne_zero hr.ne' hz
  have hc (y : Vec) (hy : y≠0) (i : Fin 3) :
      fderiv ℝ (fun x => F x i) y = (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).comp (fderiv ℝ F y) := by
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp y (hF y hy).hasFDerivAt).fderiv
  unfold divergence spatialPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hc _ hrz i,hc _ hz i]
  change (fderiv ℝ F (r • z) (basis i)) i = (r^3)⁻¹*(fderiv ℝ F z (basis i)) i
  rw [fderiv_degree_neg_two hh hr (hF _ hz) (hF _ hrz)]
  rfl

lemma angular_mean_divergence_degree_neg_two {F : Vec → Vec}
    (hh : ∀ r : ℝ, 0 < r → ∀ z, F (r • z)=(r^2)⁻¹ • F z)
    (hF : ∀ z≠0, ContDiffAt ℝ 1 F z) :
    (∫ n : Sphere, divergence F n.1 ∂sphereMeasure)=0 := by
  have hd : ∀ z≠0, DifferentiableAt ℝ F z := fun z hz => (hF z hz).differentiableAt (by simp)
  have hz (n : Sphere) : n.1≠0 := by
    intro h
    have := sphere_norm n
    rw [h,norm_zero] at this
    norm_num at this
  have hG := contDiff_holeCutoff_smul (F:=F) (by norm_num : (0:ℝ)<1) hF
  have hc := continuous_divergence hG
  have hi : IntegrableOn (divergence F) (ball (0:Vec) 2 \ ball (0:Vec) 1) := by
    apply ((hc.continuousOn.integrableOn_compact (isCompact_closedBall (0:Vec) 2)).mono_set
      (s:=ball (0:Vec) 2 \ ball (0:Vec) 1) (fun z hz => ball_subset_closedBall hz.1)).congr_fun
    · intro z hz
      apply divergence_holeCutoff (by norm_num : (0:ℝ)<1)
      have hn : 1≤‖z‖ := by simpa only [mem_ball_zero_iff,not_lt] using hz.2
      linarith
    · exact measurableSet_ball.diff measurableSet_ball
  have ha := divergence_annulus (F:=F) (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)≤2) hF
  have hflux (n : Sphere) : (2:ℝ)^2*dot n.1 (F ((2:ℝ) • n.1))=
      (1:ℝ)^2*dot n.1 (F ((1:ℝ) • n.1)) := by
    rw [hh 2 (by norm_num),one_smul,dot_smul_right]
    ring
  have ha0 : (∫z in ball (0:Vec) 2 \ ball (0:Vec) 1,divergence F z)=0 := by
    rw [ha,show (∫n : Sphere,(2:ℝ)^2*dot n.1 (F ((2:ℝ) • n.1)) ∂sphereMeasure)=
      (∫n : Sphere,(1:ℝ)^2*dot n.1 (F ((1:ℝ) • n.1)) ∂sphereMeasure) from integral_congr_ae (ae_of_all _ hflux),sub_self]
  rw [integral_annulus_polar (by norm_num : (0:ℝ)<1) hi] at ha0
  have hir (n : Sphere) : (∫r in Ico (1:ℝ) 2,r^2 • divergence F (r • n.1))=
      Real.log 2*divergence F n.1 := by
    rw [setIntegral_congr_fun measurableSet_Ico (g:=fun r => r⁻¹*divergence F n.1)]
    · rw [integral_mul_const,integral_Ico_eq_integral_Ioc,←intervalIntegral.integral_of_le (by norm_num : (1:ℝ)≤2),
        integral_inv_of_pos (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<2)]
      simp
    · intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hr.1
      dsimp only
      rw [divergence_degree_neg_two (r:=r) (z:=n.1) hh hd hr0 (hz n),smul_eq_mul]
      field_simp
  simp_rw [hir] at ha0
  rw [integral_const_mul] at ha0
  exact (mul_eq_zero.mp ha0).resolve_left (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))

end RVM
end

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

lemma contDiffAt_transportAngularCore {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    {n u : U → Vec} {z : U} {k : ℕ∞ω}
    (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hd : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun w => transportAngularCore (n w) (u w)) z := by
  have hdu := contDiff_dot_pair.contDiffAt.comp z (hu.prodMk hu)
  have hdn := contDiff_dot_pair.contDiffAt.comp z (hn.prodMk hu)
  exact ((contDiffAt_const.sub hdu).div ((contDiffAt_const.sub hdn).pow 2)
    (pow_ne_zero 2 hd)).smul (hn.sub hu)

lemma contDiffAt_coneSpatialLift {k : ℕ∞ω} {x y v e : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (fun z : Vec => coneSpatialLift x z v e) y := by
  have hn := contDiffAt_coneDirection (k:=k) hxy
  have hde := contDiff_dot_pair.contDiffAt.comp y (hn.prodMk (contDiffAt_const (c:=e)))
  have hdu := contDiff_dot_pair.contDiffAt.comp y (hn.prodMk (contDiffAt_const (c:=velocity v)))
  have hc : ContDiffAt ℝ k (fun z : Vec => coneSpatialCoefficient x z v e) y :=
    hde.div (contDiffAt_const.sub hdu) (cone_denom_pos v _ (coneDirection_norm hxy)).ne'
  exact contDiffAt_const.add (hc.smul contDiffAt_const)

lemma transportSpatialFlux_contDiffAt (v e : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiffAt ℝ 1 (transportSpatialFlux v e i) z := by
  have h0z : (0:Vec)≠z := Ne.symm hz
  have hr := contDiffAt_coneRadius (k:=1) h0z
  have hn := contDiffAt_coneDirection (k:=1) h0z
  have hu : ContDiffAt ℝ 1 (fun _ : Vec => velocity v) z := contDiffAt_const
  have hc := contDiffAt_transportAngularCore hn hu
    (cone_denom_pos v _ (coneDirection_norm h0z)).ne'
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp z hc
  exact (((hr.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h0z)))).mul hi).smul
    (contDiffAt_coneSpatialLift (v:=v) (e:=e) h0z)

lemma transportSpatialFlux_homogeneous (v e : Vec) (i : Fin 3) {r : ℝ} (hr : 0 < r) (z : Vec) :
    transportSpatialFlux v e i (r • z)=(r^2)⁻¹ • transportSpatialFlux v e i z := by
  simp only [transportSpatialFlux,coneSpatialLift,coneSpatialCoefficient,
    coneRadius_zero_smul hr,coneDirection_zero_smul hr,smul_smul]
  congr 1
  ring

lemma transportSpatialFlux_angular_mean_zero (v e : Vec) (i : Fin 3) :
    (∫ n : Sphere, divergence (transportSpatialFlux v e i) n.1 ∂sphereMeasure)=0 := by
  exact angular_mean_divergence_degree_neg_two
    (fun r hr z => transportSpatialFlux_homogeneous v e i hr z)
    (fun z hz => transportSpatialFlux_contDiffAt v e i hz)

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

lemma transportSpatialFlux_joint_contDiffAt (e : Vec) (i : Fin 3) {p : Phase}
    (hp : p.1 ≠ 0) :
    ContDiffAt ℝ 1 (fun z : Phase => transportSpatialFlux z.2 e i z.1) p := by
  have hz : (0:Vec) ≠ p.1 := hp.symm
  have hr := (contDiffAt_coneRadius (k:=1) hz).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hz).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have he := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk (contDiffAt_const (c:=e)))
  have hd := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk hu)
  have hne := (cone_denom_pos p.2 _ (coneDirection_norm hz)).ne'
  have hc := he.div (contDiffAt_const.sub hd) hne
  have hW : ContDiffAt ℝ 1 (fun z : Phase => coneSpatialLift 0 z.1 z.2 e) p :=
    contDiffAt_const.add (hc.smul hu)
  have hA := contDiffAt_transportAngularCore hn hu hne
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p hA
  exact (((hr.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))).mul hi).smul hW

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

lemma continuousOn_transportSpatialDivergence (e : Vec) (i : Fin 3) :
    ContinuousOn (fun p : Phase => divergence (transportSpatialFlux p.2 e i) p.1)
      {p | p.1≠0} := by
  have he (p : Phase) (hp : p.1≠0) :=
    divergence_phase_first ((transportSpatialFlux_joint_contDiffAt e i hp).differentiableAt (by simp))
  apply ContinuousOn.congr (f:=fun p : Phase => ∑ j : Fin 3,
    (fderiv ℝ (fun z : Phase => transportSpatialFlux z.2 e i z.1) p (basis j,0)) j)
  · apply continuousOn_finsetSum
    intro j _ p hp
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.continuousAt.comp
      (((transportSpatialFlux_joint_contDiffAt e i hp).continuousAt_fderiv (by simp)).clm_apply
        continuousAt_const)).continuousWithinAt
  · intro p hp
    exact he p hp

lemma transportSpatialDivergence_uniform_bound (P : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ v∈closedBall (0:Vec) P, ∀ n : Sphere,
      |divergence (transportSpatialFlux v e i) n.1|≤C := by
  let K := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : Phase => divergence (transportSpatialFlux p.2 e i) p.1) K :=
    (continuousOn_transportSpatialDivergence e i).mono (by
      intro p hp
      have hn : ‖p.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1
      intro hz
      simp only [hz,norm_zero] at hn
      norm_num at hn)
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro v hv n
  exact (hC (n.1,v) ⟨n.2,hv⟩).trans (le_max_left _ _)

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

lemma transportConeCoefficient_contDiffAt (i : Fin 3) {p : Phase} (hp : p.1≠0) :
    ContDiffAt ℝ 1 (transportConeCoefficient i) p := by
  have hz : (0:Vec)≠p.1 := hp.symm
  have hr := (contDiffAt_coneRadius (k:=1) hz).comp p contDiffAt_fst
  have hn := (contDiffAt_coneDirection (k:=1) hz).comp p contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have hA := contDiffAt_transportAngularCore hn hu (cone_denom_pos p.2 _ (coneDirection_norm hz)).ne'
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p hA
  exact ((hr.pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)))).mul hi

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

lemma electric_transport_division_annulus {s : Solution} {H t ε R : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) (heq : EquationsBefore s H)
    (htH : t≤H) (hε : 0<ε) (hεR : ε≤R) (hRt : R<t) (x e : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
      transportConeCoefficient i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) =
      (∫ n : Sphere, R^2*dot n.1 (∫ v, s.f (t-R,x+R • n.1,v) •
        transportSpatialFlux v e i (R • n.1)) ∂sphereMeasure)-
      (∫ n : Sphere, ε^2*dot n.1 (∫ v, s.f (t-ε,x+ε • n.1,v) •
        transportSpatialFlux v e i (ε • n.1)) ∂sphereMeasure)-
      ∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, s.f (t-coneRadius 0 z,x+z,v)*
        (divergence (transportSpatialFlux v e i) z+
          divergence (fun w => transportConeCoefficient i (z,w) •
            (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v) := by
  have hk : ContDiffOn ℝ 1 (transportConeCoefficient i) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (transportConeCoefficient_contDiffAt i hp.1.1.symm).contDiffWithinAt
  have hK : ContDiffOn ℝ 1 (coneLorentz s t x) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (coneLorentz_contDiffAt hE hB x hp.1.1.symm hp.1.2).contDiffWithinAt
  have hh := retarded_spatial_annulus (e:=e) hf hc hε hεR hRt hk hK
    (fun z hz v => coneLorentz_vlasov_before hf heq htH x hz v)
  unfold transportSpatialFlux transportConeCoefficient at *
  simpa only [smul_smul,smul_eq_mul,mul_assoc] using hh

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_LogSingularBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma singular_radial_split_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : ℝ → W} {t θ A N : ℝ} (hθ : 0<θ) (hθt : θ≤t)
    (hg : ContinuousOn g (Ioc (0:ℝ) t))
    (hn : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤N)
    (ha : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤A/r) :
    IntegrableOn g (Ioc (0:ℝ) t) ∧
      ‖∫r in Ioc (0:ℝ) t,g r‖≤N*θ+A*Real.log (t/θ) := by
  have ht : 0<t := hθ.trans_le hθt
  have hi : IntegrableOn g (Ioc (0:ℝ) t) :=
    (integrableOn_const (μ:=volume) (s:=Ioc (0:ℝ) t) (C:=N) measure_Ioc_lt_top.ne).mono'
      (hg.aestronglyMeasurable measurableSet_Ioc) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hn r hr)
  have hi₁ : IntervalIntegrable g volume 0 θ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hθ.le).mpr
      (hi.mono_set (Ioc_subset_Ioc_right hθt))
  have hi₂ : IntervalIntegrable g volume θ t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hθt).mpr
      (hi.mono_set (Ioc_subset_Ioc_left hθ.le))
  have h₁ : ‖∫r in (0:ℝ)..θ,g r‖≤N*θ := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (f:=g) (a:=0) (b:=θ) (C:=N) (by
      rw [uIoc_of_le hθ.le]
      intro r hr
      exact hn r ⟨hr.1,hr.2.trans hθt⟩)
    simpa only [sub_zero,abs_of_pos hθ] using hh
  have hci : IntervalIntegrable (fun r : ℝ => A/r) volume θ t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hθt]
    exact continuousOn_const.div continuousOn_id (fun r hr => (hθ.trans_le hr.1).ne')
  have h₂ : ‖∫r in θ..t,g r‖≤A*Real.log (t/θ) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le (f:=g) hθt (by
      filter_upwards [] with r hr
      exact ha r ⟨hθ.trans hr.1,hr.2⟩) hci
    apply hh.trans_eq
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul,integral_inv_of_pos hθ ht]
    simp only [div_eq_mul_inv]
  refine ⟨hi,?_⟩
  rw [←intervalIntegral.integral_of_le ht.le,←intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

lemma singular_radial_log_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : ℝ → W} {t H A N : ℝ} (ht : 0<t) (htH : t≤H) (hA : 0≤A) (hN : 0≤N)
    (hg : ContinuousOn g (Ioc (0:ℝ) t))
    (hn : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤N)
    (ha : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤A/r) :
    IntegrableOn g (Ioc (0:ℝ) t) ∧
      ‖∫r in Ioc (0:ℝ) t,g r‖≤1+A*(Real.log (max 1 H)+Real.log (1+N)) := by
  let θ := min t (1+N)⁻¹
  have hp : 0<1+N := by linarith
  have hθ : 0<θ := lt_min ht (inv_pos.mpr hp)
  obtain ⟨hi,hb⟩ := singular_radial_split_bound hθ (min_le_left _ _) hg hn ha
  refine ⟨hi,hb.trans ?_⟩
  have hnear : N*θ≤1 := by
    calc
      N*θ≤N*(1+N)⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hN
      _ ≤ 1 := by rw [←div_eq_mul_inv]; exact (div_le_one hp).mpr (by linarith)
  have hratio : t/θ≤(max 1 H)*(1+N) := by
    by_cases hh : t≤(1+N)⁻¹
    · simp only [θ,min_eq_left hh,div_self ht.ne']
      exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (by linarith)
    · rw [show θ=(1+N)⁻¹ from min_eq_right (le_of_not_ge hh),div_inv_eq_mul]
      exact mul_le_mul_of_nonneg_right (htH.trans (le_max_right _ _)) hp.le
  have hl : Real.log (t/θ)≤Real.log (max 1 H)+Real.log (1+N) := by
    calc
      Real.log (t/θ)≤Real.log (max 1 H*(1+N)) := Real.log_le_log (div_pos ht hθ) hratio
      _ = _ := Real.log_mul (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _))) hp.ne'
  exact add_le_add hnear (mul_le_mul_of_nonneg_left hl hA)

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


section

local instance localInst_r26dc03_1 : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
lemma sphere_mean_zero_lipschitz_bound {a : Sphere → ℝ} {F : Vec → ℝ} {x : Vec}
    {r C N : ℝ} (ha : Continuous a) (hF : Continuous F)
    (hmean : (∫n : Sphere,a n ∂sphereMeasure)=0)
    (hC : 0≤C) (hab : ∀ n, |a n|≤C) (hr : 0 ≤ r)
    (_hN : 0≤N) (hLip : ∀ y, |F y-F x|≤N*‖y-x‖) :
    |∫ n : Sphere, a n*F (x+r • n.1) ∂sphereMeasure|≤(4*Real.pi)*C*N*r := by
  have hc : Continuous (fun n : Sphere => a n*F (x+r • n.1)) :=
    by fun_prop
  have hi := hc.integrable_of_hasCompactSupport (μ:=sphereMeasure) (HasCompactSupport.of_compactSpace _)
  have hai := ha.integrable_of_hasCompactSupport (μ:=sphereMeasure) (HasCompactSupport.of_compactSpace _)
  have he : (∫ n : Sphere,a n*(F (x+r • n.1)-F x) ∂sphereMeasure)=
      ∫ n : Sphere,a n*F (x+r • n.1) ∂sphereMeasure := by
    simp_rw [mul_sub]
    rw [integral_sub hi (hai.mul_const _),integral_mul_const,hmean,zero_mul,sub_zero]
  rw [←he]
  have hb : ∀ n : Sphere, ‖a n*(F (x+r • n.1)-F x)‖≤C*N*r := by
    intro n
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    have hh := hLip (x+r • n.1)
    simp only [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr,sphere_norm,mul_one] at hh
    exact (mul_le_mul (hab n) hh (abs_nonneg _) hC).trans_eq (by ring)
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)
  simpa only [Real.norm_eq_abs,sphere_area,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh

lemma transport_divergence_sphere_continuous (v e : Vec) (i : Fin 3) :
    Continuous (fun n : Sphere => divergence (transportSpatialFlux v e i) n.1) := by
  apply (continuousOn_transportSpatialDivergence e i).comp_continuous
    (continuous_subtype_val.prodMk continuous_const)
  intro n
  have hn := sphere_norm n
  intro hz
  change (n : Vec)=0 at hz
  rw [hz,norm_zero] at hn
  norm_num at hn

lemma transportSingularShell_near_far {P t U A N : ℝ} {f : Particle} {x e : Vec} {i : Fin 3}
    (_hA : 0≤A) (hN : 0≤N)
    (hf : ∀ s∈Icc (0:ℝ) U, ∀ v, Differentiable ℝ (fun y => f (s,y,v)))
    (hfA : ∀ s∈Icc (0:ℝ) U, ∀ y v, |f (s,y,v)|≤A)
    (hfN : ∀ s∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => f (s,z,v)) y‖≤N)
    {C : ℝ} (hC : 0≤C)
    (hc : ∀ v∈closedBall (0:Vec) P, ∀ n : Sphere,
      |divergence (transportSpatialFlux v e i) n.1|≤C)
    (ht : t∈Icc (0:ℝ) U) {r : ℝ} (hr : 0 < r) (hrt : r≤t) :
    |transportSingularShell P f t x e i r|≤volume.real (closedBall (0:Vec) P)*(4*Real.pi)*C*N ∧
    |transportSingularShell P f t x e i r|≤
      (volume.real (closedBall (0:Vec) P)*(4*Real.pi)*C*A)/r := by
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hs : t-r∈Icc (0:ℝ) U := ⟨by linarith,by linarith [ht.2]⟩
  have hnear (v : Vec) (hv : v∈closedBall (0:Vec) P) :
      ‖∫ n : Sphere,divergence (transportSpatialFlux v e i) n.1 *
        f (t-r,x+r • n.1,v) ∂sphereMeasure‖≤(4*Real.pi)*C*N*r := by
    apply sphere_mean_zero_lipschitz_bound (transport_divergence_sphere_continuous v e i)
      (hf _ hs v).continuous (transportSpatialFlux_angular_mean_zero v e i) hC (hc v hv) hr.le hN
    intro y
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf _ hs v z)
      (fun z _ => hfN _ hs z v) convex_univ (mem_univ x) (mem_univ y)
  have hfar (v : Vec) (hv : v∈closedBall (0:Vec) P) :
      ‖∫ n : Sphere,divergence (transportSpatialFlux v e i) n.1 *
        f (t-r,x+r • n.1,v) ∂sphereMeasure‖≤(4*Real.pi)*C*A := by
    have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (f:=fun n : Sphere =>
      divergence (transportSpatialFlux v e i) n.1 * f (t-r,x+r • n.1,v)) (C:=C*A) (ae_of_all _ (fun n : Sphere => by
      rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact mul_le_mul (hc v hv n) (hfA _ hs _ v) (abs_nonneg _) hC))
    simpa only [sphere_area,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  have hnear' := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv; exact hnear v hv)
  have hfar' := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv; exact hfar v hv)
  simp only [Measure.restrict_apply_univ,measureReal_def,Real.norm_eq_abs] at hnear' hfar'
  unfold transportSingularShell
  rw [abs_mul,abs_of_pos (inv_pos.mpr hr)]
  constructor
  · exact (mul_le_mul_of_nonneg_left hnear' (inv_nonneg.mpr hr.le)).trans_eq (by simp only [measureReal_def]; field_simp)
  · exact (mul_le_mul_of_nonneg_left hfar' (inv_nonneg.mpr hr.le)).trans_eq (by simp only [measureReal_def]; ring)

attribute [local instance] Measure.Subtype.measureSpace

lemma transportSingularShell_continuousOn {P t U : ℝ} {f : Particle} (x e : Vec) (i : Fin 3)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) (ht : t∈Icc (0:ℝ) U) :
    ContinuousOn (transportSingularShell P f t x e i) (Ioc (0:ℝ) t) := by
  let K := closedBall (0:Vec) P
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  let α := K × Sphere
  let μ : Measure α := volume.prod sphereMeasure
  let G : ℝ × α → ℝ := fun q => divergence (transportSpatialFlux q.2.1.1 e i) q.2.2.1 *
    f (t-q.1,x+q.1 • q.2.2.1,q.2.1.1)
  have hc : Continuous (fun a : α => divergence (transportSpatialFlux a.1.1 e i) a.2.1) := by
    apply (continuousOn_transportSpatialDivergence e i).comp_continuous
      ((continuous_subtype_val.comp continuous_snd).prodMk (continuous_subtype_val.comp continuous_fst))
    intro a hz
    change (a.2 : Vec)=0 at hz
    have hh := sphere_norm a.2
    rw [hz,norm_zero] at hh
    norm_num at hh
  have hn : Continuous (fun q : ℝ × α => (q.2.2:Vec)) := continuous_subtype_val.comp continuous_snd.snd
  have hv : Continuous (fun q : ℝ × α => (q.2.1:Vec)) := continuous_subtype_val.comp continuous_snd.fst
  have hmap : Continuous (fun q : ℝ × α => (t-q.1,x+q.1 • (q.2.2:Vec),(q.2.1:Vec))) :=
    (continuous_const.sub continuous_fst).prodMk ((continuous_const.add (continuous_fst.smul hn)).prodMk hv)
  have hG : ContinuousOn G (Ioc (0:ℝ) t ×ˢ univ) := by
    exact (hc.comp continuous_snd).continuousOn.mul (hf.comp hmap.continuousOn (by
      intro q hq
      exact ⟨by linarith [hq.1.2],by linarith [ht.2,hq.1.1]⟩))
  have hi (r : ℝ) (hr : r∈Ioc (0:ℝ) t) : Integrable (fun a : α => G (r,a)) μ :=
    (hG.comp_continuous (continuous_const.prodMk continuous_id) (fun a => ⟨hr,mem_univ a⟩)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : ContinuousOn (fun r => ∫ a, G (r,a) ∂μ) (Ioc (0:ℝ) t) := by
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hG
    intro r a _ ha
    exact (ha (mem_univ a)).elim
  have he (r : ℝ) (hr : r∈Ioc (0:ℝ) t) :
      (∫ a, G (r,a) ∂μ)=∫ v in K,∫ n : Sphere,
        divergence (transportSpatialFlux v e i) n.1*f (t-r,x+r • n.1,v) ∂sphereMeasure := by
    rw [show μ=(volume : Measure K).prod sphereMeasure from rfl,integral_prod _ (hi r hr)]
    exact integral_subtype measurableSet_closedBall
      (fun v : Vec => ∫ n : Sphere,divergence (transportSpatialFlux v e i) n.1 *
        f (t-r,x+r • n.1,v) ∂sphereMeasure)
  apply ContinuousOn.congr (f:=fun r : ℝ => r⁻¹*(∫ a, G (r,a) ∂μ))
  · exact (continuousOn_id.inv₀ (fun r hr => hr.1.ne')).mul hg
  · intro r hr
    change r⁻¹*(∫ v in K,∫ n : Sphere,divergence (transportSpatialFlux v e i) n.1 *
      f (t-r,x+r • n.1,v) ∂sphereMeasure) = r⁻¹*(∫ a, G (r,a) ∂μ)
    rw [he r hr]

end

section
attribute [local instance] Measure.Subtype.measureSpace
local instance instCompactSpaceElemVecSphere_2 : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

lemma singular_radial_log_bound_norm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : ℝ → W} {t H A N : ℝ} (ht : 0<t) (htH : t≤H) (hA : 0≤A) (hN : 0≤N)
    (hg : ContinuousOn g (Ioc (0:ℝ) t))
    (hn : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤N)
    (ha : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤A/r) :
    IntegrableOn g (Ioc (0:ℝ) t) ∧
      (∫r in Ioc (0:ℝ) t,‖g r‖)≤1+A*(Real.log (max 1 H)+Real.log (1+N)) := by
  have hh := singular_radial_log_bound ht htH hA hN hg.norm
    (fun r hr => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hn r hr)
    (fun r hr => by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using ha r hr)
  exact ⟨(singular_radial_log_bound ht htH hA hN hg hn ha).1,
    (le_abs_self _).trans hh.2⟩

lemma integral_annulus_polar_radial {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : Vec → W} {ε R : ℝ} (hε : 0<ε)
    (hg : ContinuousOn g {z | ε≤‖z‖ ∧ ‖z‖≤R}) :
    (∫z in ball (0:Vec) R \ ball (0:Vec) ε,g z)=
      ∫r in Ico ε R, ∫n : Sphere,r^2 • g (r • n.1) ∂sphereMeasure := by
  have hclosed : {z : Vec | ε≤‖z‖ ∧ ‖z‖≤R}=closedBall (0:Vec) R \ ball (0:Vec) ε := by
    ext z
    simp only [mem_ofPred_eq,Set.mem_sdiff,mem_closedBall,mem_ball,dist_zero_right,not_lt]
    exact and_comm
  have hgi : IntegrableOn g (ball (0:Vec) R \ ball (0:Vec) ε) := by
    have hcomp : IsCompact {z : Vec | ε≤‖z‖ ∧ ‖z‖≤R} := by
      rw [hclosed]
      exact (isCompact_closedBall _ _).diff isOpen_ball
    exact (hg.integrableOn_compact hcomp).mono_set (by
      intro z hz
      simp only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt] at hz
      exact ⟨hz.2,hz.1.le⟩)
  have hfun : ContinuousOn (fun p : ℝ × Sphere => p.1^2 • g (p.1 • p.2.1)) (Icc ε R ×ˢ univ) := by
    apply (continuous_fst.pow 2).continuousOn.smul
    apply hg.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).continuousOn
    intro p hp
    have hr : 0≤p.1 := hε.le.trans hp.1.1
    change ε≤‖p.1 • p.2.1‖ ∧ ‖p.1 • p.2.1‖≤R
    simpa only [mem_Icc,norm_smul,Real.norm_of_nonneg hr,sphere_norm,mul_one] using hp.1
  have hi : Integrable (fun p : ℝ × Sphere => p.1^2 • g (p.1 • p.2.1))
      ((volume.restrict (Ico ε R)).prod sphereMeasure) := by
    let : IsFiniteMeasure sphereMeasure := inferInstance
    let : IsFiniteMeasureOnCompacts ((volume : Measure ℝ).prod sphereMeasure) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    rw [Measure.restrict_prod_eq_prod_univ]
    exact (hfun.integrableOn_compact (μ := (volume : Measure ℝ).prod sphereMeasure)
      (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono_left Ico_subset_Icc_self)
  rw [integral_annulus_polar hε hgi]
  exact (integral_integral_swap hi).symm

lemma transportSingularBulk_continuousOn {P t U ε R : ℝ} {f : Particle}
    (x e : Vec) (i : Fin 3) (hε : 0<ε) (hRt : R≤t) (htU : t≤U)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) :
    ContinuousOn (transportSingularBulk P f t x e i) {z | ε≤‖z‖ ∧ ‖z‖≤R} := by
  let K := closedBall (0:Vec) P
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  let G : Vec × K → ℝ := fun p => divergence (transportSpatialFlux p.2.1 e i) p.1 *
    f (t-coneRadius 0 p.1,x+p.1,p.2.1)
  have hdiv : ContinuousOn (fun p : Vec × K => divergence (transportSpatialFlux p.2.1 e i) p.1)
      ({z | ε≤‖z‖ ∧ ‖z‖≤R} ×ˢ univ) := by
    apply (continuousOn_transportSpatialDivergence e i).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
    intro p hp
    change p.1≠0
    exact norm_pos_iff.mp (hε.trans_le hp.1.1)
  have hm : Continuous (fun p : Vec × K => (t-coneRadius 0 p.1,x+p.1,p.2.1)) := by
    unfold coneRadius
    fun_prop
  have hG : ContinuousOn G ({z | ε≤‖z‖ ∧ ‖z‖≤R} ×ˢ univ) := by
    apply hdiv.mul (hf.comp hm.continuousOn ?_)
    intro p hp
    change t-coneRadius 0 p.1∈Icc (0:ℝ) U
    simp only [coneRadius,zero_sub,norm_neg]
    exact ⟨by linarith [hp.1.2],by linarith [norm_nonneg p.1]⟩
  have hh : ContinuousOn (fun z => ∫ v : K, G (z,v)) {z | ε≤‖z‖ ∧ ‖z‖≤R} := by
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hG
    intro z v _ hv
    exact (hv (mem_univ v)).elim
  apply hh.congr
  intro z hz
  exact (integral_subtype measurableSet_closedBall
    (fun v : Vec => divergence (transportSpatialFlux v e i) z * f (t-coneRadius 0 z,x+z,v))).symm

lemma transportSingularBulk_shell {P t U r : ℝ} {f : Particle} (x e : Vec) (i : Fin 3)
    (hr : 0 < r) (hrt : r≤t) (htU : t≤U)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) :
    (∫ n : Sphere,r^2 • transportSingularBulk P f t x e i (r • n.1) ∂sphereMeasure)=
      transportSingularShell P f t x e i r := by
  let K := closedBall (0:Vec) P
  have he (n : Sphere) : r^2 • transportSingularBulk P f t x e i (r • n.1)=
      r⁻¹*(∫ v in K, divergence (transportSpatialFlux v e i) n.1 * f (t-r,x+r • n.1,v)) := by
    have hn : (n:Vec)≠0 := by
      intro h
      have := sphere_norm n
      rw [h,norm_zero] at this
      norm_num at this
    have hd (v : Vec) := divergence_degree_neg_two
      (fun a ha z => transportSpatialFlux_homogeneous v e i ha z)
      (fun z hz => (transportSpatialFlux_contDiffAt v e i hz).differentiableAt (by simp)) hr hn
    have hrad : coneRadius 0 (r • n.1)=r := by
      simp only [coneRadius,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hr.le,sphere_norm,mul_one]
    simp only [transportSingularBulk,hd,hrad,smul_eq_mul,mul_assoc,integral_const_mul]
    rw [←mul_assoc]
    congr 1
    field_simp
  simp_rw [he]
  rw [integral_const_mul]
  congr 1
  have hfun : ContinuousOn (fun p : Sphere × Vec => divergence (transportSpatialFlux p.2 e i) p.1.1 *
      f (t-r,x+r • p.1.1,p.2)) (univ ×ˢ K) := by
    have hc : ContinuousOn (fun p : Sphere × Vec => divergence (transportSpatialFlux p.2 e i) p.1.1)
        (univ ×ˢ K) := by
      apply (continuousOn_transportSpatialDivergence e i).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      intro p hp
      change (p.1:Vec)≠0
      intro hh
      have := sphere_norm p.1
      rw [hh,norm_zero] at this
      norm_num at this
    apply hc.mul
    apply hf.comp (by fun_prop : Continuous (fun p : Sphere × Vec => (t-r,x+r • p.1.1,p.2))).continuousOn
    intro p hp
    exact ⟨by linarith,by linarith⟩
  have hi : Integrable (fun p : Sphere × Vec => divergence (transportSpatialFlux p.2 e i) p.1.1 *
      f (t-r,x+r • p.1.1,p.2)) (sphereMeasure.prod (volume.restrict K)) := by
    rw [←Measure.restrict_univ (μ:=sphereMeasure),Measure.prod_restrict]
    exact hfun.integrableOn_compact (isCompact_univ.prod (isCompact_closedBall _ _))
  exact integral_integral_swap hi

lemma transportSingularBulk_annulus {P t U ε R : ℝ} {f : Particle}
    (x e : Vec) (i : Fin 3) (hε : 0<ε) (hRt : R≤t) (htU : t≤U)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportSingularBulk P f t x e i z)=
      ∫ r in Ico ε R,transportSingularShell P f t x e i r := by
  rw [integral_annulus_polar_radial hε (transportSingularBulk_continuousOn x e i hε hRt htU hf)]
  apply setIntegral_congr_fun measurableSet_Ico
  intro r hr
  exact transportSingularBulk_shell x e i (hε.trans_le hr.1) (hr.2.le.trans hRt) htU hf

lemma physical_transport_annulus_log_bound (P H A : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧ ∀ (U t N ε R : ℝ) (f : Particle),
      0<t → t≤U → U≤H → 0≤N → 0<ε → R≤t →
      ContinuousOn f {p | p.1∈Icc (0:ℝ) U} →
      (∀ s∈Icc (0:ℝ) U, ∀ v, Differentiable ℝ (fun y => f (s,y,v))) →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, |f (s,y,v)|≤A) →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => f (s,z,v)) y‖≤N) →
      ∀ x, |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportSingularBulk P f t x e i z|≤
        1+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨K,hK,hkb⟩ := transportSpatialDivergence_uniform_bound P e i
  let C := volume.real (closedBall (0:Vec) P)*(4*Real.pi)*K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,C*A,hC,mul_nonneg hC hA,?_⟩
  intro U t N ε R f ht htU hUH hN hε hRt hfc hfd hfA hfN x
  have htt : t∈Icc (0:ℝ) U := ⟨ht.le,htU⟩
  have hh := singular_radial_log_bound_norm ht (htU.trans hUH) (mul_nonneg hC hA) (mul_nonneg hC hN)
    (transportSingularShell_continuousOn x e i hfc htt)
    (fun r hr => (transportSingularShell_near_far hA hN hfd hfA hfN hK hkb htt hr.1 hr.2).1)
    (fun r hr => (transportSingularShell_near_far hA hN hfd hfA hfN hK hkb htt hr.1 hr.2).2)
  rw [transportSingularBulk_annulus x e i hε hRt htU hfc]
  rw [←Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply le_trans _ hh.2
  exact integral_mono_measure (Measure.restrict_mono_set volume (by
    intro r hr
    exact ⟨hε.trans_le hr.1,hr.2.le.trans hRt⟩))
    (Filter.Eventually.of_forall (fun r => norm_nonneg _)) hh.1.norm

end

section

lemma transportSpatialFlux_uniform_bound (P : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ v∈closedBall (0:Vec) P, ∀ n : Sphere,
      ‖transportSpatialFlux v e i n.1‖≤C := by
  let K := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : Phase => transportSpatialFlux p.2 e i p.1) K := by
    intro p hp
    have hn : ‖p.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1
    have hz : p.1≠0 := by intro hh; simp only [hh,norm_zero] at hn; norm_num at hn
    exact (transportSpatialFlux_joint_contDiffAt e i hz).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro v hv n
  exact (hC (n.1,v) ⟨n.2,hv⟩).trans (le_max_left _ _)

lemma transport_sphere_rescale (P : ℝ) (f : Particle) (t : ℝ) (x e : Vec) (i : Fin 3)
    {r : ℝ} (hr : 0 < r) (n : Sphere) :
    r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
      f (t-r,x+r • n.1,v) • transportSpatialFlux v e i (r • n.1)) =
    dot n.1 (∫ v in closedBall (0:Vec) P,
      f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1) := by
  have he : (∫ v in closedBall (0:Vec) P,
      f (t-r,x+r • n.1,v) • transportSpatialFlux v e i (r • n.1))=
      (r^2)⁻¹ • ∫ v in closedBall (0:Vec) P,
        f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1 := by
    rw [←integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ (fun v => by
      dsimp only
      rw [transportSpatialFlux_homogeneous v e i hr]
      simp only [smul_smul,mul_comm])
  rw [he,dot_smul_right,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero 2 hr.ne'),one_mul]

lemma transport_sphere_boundary_bound (P A : ℝ) (e : Vec) (i : Fin 3) (hA : 0≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (f : Particle) (t U r : ℝ) (x : Vec),
      0 < r → r≤t → t≤U →
      (∀ s∈Icc (0:ℝ) U, ∀ y v, |f (s,y,v)|≤A) →
      |∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,
        f (t-r,x+r • n.1,v) • transportSpatialFlux v e i (r • n.1)) ∂sphereMeasure|≤C := by
  obtain ⟨K,hK,hkb⟩ := transportSpatialFlux_uniform_bound P e i
  let C := volume.real (closedBall (0:Vec) P)*A*K
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨(4*Real.pi)*C,mul_nonneg (by positivity) hC,?_⟩
  intro f t U r x hr hrt htU hf
  simp_rw [transport_sphere_rescale P f t x e i hr]
  have hs : t-r∈Icc (0:ℝ) U := ⟨by linarith,by linarith⟩
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (n : Sphere) : ‖dot n.1 (∫ v in closedBall (0:Vec) P,
      f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1)‖≤C := by
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1) (C:=A*K) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul (hf _ hs _ v) (hkb v hv n) (norm_nonneg _) hA)
    have hd := abs_real_inner_le_norm n.1
      (∫ v in closedBall (0:Vec) P,f (t-r,x+r • n.1,v) • transportSpatialFlux v e i n.1)
    rw [sphere_norm,one_mul] at hd
    rw [dot_eq_inner,Real.norm_eq_abs]
    exact hd.trans (by simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,C,mul_assoc,mul_comm,mul_left_comm] using hh)
  have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hb)
  simpa only [Real.norm_eq_abs,sphere_area,smul_eq_mul,mul_comm] using hh

end

lemma transportVelocityProfile_contDiffAt (e : Vec) (i : Fin 3)
    {p : (Vec × Vec × Vec) × Vec} (hd : 1-dot p.1.1 (velocity p.2)≠0) :
    ContDiffAt ℝ 1 (transportVelocityProfile e i) p := by
  have hn : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => z.1.1) p := contDiffAt_fst.fst
  have hu : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec => velocity z.2) p :=
    contDiff_velocity.contDiffAt.comp p contDiffAt_snd
  have ha := contDiffAt_transportAngularCore hn hu hd
  have hi := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp p ha
  have hm := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk (contDiffAt_const (c:=e)))
  have hdu := contDiff_dot_pair.contDiffAt.comp p (hn.prodMk hu)
  have hforce : ContDiffAt ℝ 1 (fun z : (Vec × Vec × Vec) × Vec =>
      z.1.2.1+cross (velocity z.2) z.1.2.2) p :=
    contDiffAt_fst.snd.fst.add
      (contDiff_cross.contDiffAt.comp p (hu.prodMk contDiffAt_fst.snd.snd))
  exact (hi.mul (hm.div (contDiffAt_const.sub hdu) hd)).smul hforce

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

lemma continuousOn_transportVelocityDivergence (e : Vec) (i : Fin 3) :
    ContinuousOn (fun p : (Vec × Vec × Vec) × Vec =>
      divergence (fun w => transportVelocityProfile e i (p.1,w)) p.2)
      {p | 1-dot p.1.1 (velocity p.2)≠0} := by
  apply ContinuousOn.congr (f:=fun p : (Vec × Vec × Vec) × Vec =>
    ∑ j : Fin 3,(fderiv ℝ (transportVelocityProfile e i) p (0,basis j)) j)
  · apply continuousOn_finsetSum
    intro j _ p hp
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) j).continuous.continuousAt.comp
      (((transportVelocityProfile_contDiffAt e i hp).continuousAt_fderiv (by simp)).clm_apply
        continuousAt_const)).continuousWithinAt
  · intro p hp
    exact divergence_parameter_slice ((transportVelocityProfile_contDiffAt e i hp).differentiableAt (by simp))

lemma transportVelocityDivergence_uniform_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : Sphere) (E B v : Vec), ‖E‖≤M → ‖B‖≤M → ‖v‖≤P →
      |divergence (fun w => transportVelocityProfile e i ((n.1,E,B),w)) v|≤C := by
  let K := (sphere (0:Vec) 1 ×ˢ (closedBall (0:Vec) M ×ˢ closedBall (0:Vec) M)) ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := ((isCompact_sphere _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : (Vec × Vec × Vec) × Vec =>
      divergence (fun w => transportVelocityProfile e i (p.1,w)) p.2) K :=
    (continuousOn_transportVelocityDivergence e i).mono (by
      intro p hp
      have hn : ‖p.1.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1.1
      exact (cone_denom_pos p.2 p.1.1 hn).ne')
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro n E B v hE hB hv
  apply (hC ((n.1,E,B),v) ?_).trans (le_max_left _ _)
  exact ⟨⟨n.2,by simpa only [mem_prod,mem_closedBall,dist_zero_right] using And.intro hE hB⟩,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩

lemma divergence_real_const_smul {F : Vec → Vec} {v : Vec} (hF : DifferentiableAt ℝ F v) (a : ℝ) :
    divergence (fun w => a • F w) v=a*divergence F v := by
  rw [divergence_smul (differentiableAt_const a) hF]
  have hg : gradient (fun _ : Vec => a) v=0 := by
    ext j
    simp
  rw [hg]
  simp [dot]

lemma transport_velocity_divergence_rescale (s : Solution) (t : ℝ) (x e : Vec) (i : Fin 3)
    {z : Vec} (hz : z≠0) (v : Vec) :
    divergence (fun w => transportConeCoefficient i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v =
      ((coneRadius 0 z)^2)⁻¹*
        divergence (fun w => transportVelocityProfile e i
          ((coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z)),w)) v := by
  let a := (coneDirection 0 z,s.E (t-coneRadius 0 z,x+z),s.B (t-coneRadius 0 z,x+z))
  have ha : DifferentiableAt ℝ (fun w => transportVelocityProfile e i (a,w)) v :=
    ((transportVelocityProfile_contDiffAt e i (p:=(a,v))
      (cone_denom_pos v _ (coneDirection_norm hz.symm)).ne').differentiableAt (by simp)).comp v
      ((differentiableAt_const a).prodMk differentiableAt_id)
  have he : (fun w => transportConeCoefficient i (z,w) •
      (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) =
      fun w => ((coneRadius 0 z)^2)⁻¹ • transportVelocityProfile e i (a,w) := by
    funext w
    simp only [transportConeCoefficient,coneSpatialCoefficient,coneLorentz,transportVelocityProfile,a,smul_smul,mul_assoc]
  rw [he,divergence_real_const_smul ha]

lemma physical_transport_velocity_bound (P M : ℝ) (e : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (t : ℝ) (x z v : Vec), z≠0 → ‖v‖≤P →
      ‖s.E (t-coneRadius 0 z,x+z)‖≤M → ‖s.B (t-coneRadius 0 z,x+z)‖≤M →
      |divergence (fun w => transportConeCoefficient i (z,w) •
        (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v|≤C/(coneRadius 0 z)^2 := by
  obtain ⟨C,hC,hb⟩ := transportVelocityDivergence_uniform_bound P M e i
  refine ⟨C,hC,?_⟩
  intro s t x z v hz hv hE hB
  rw [transport_velocity_divergence_rescale s t x e i hz v,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  have hn : coneDirection 0 z∈sphere (0:Vec) 1 := by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm
  exact (mul_le_mul_of_nonneg_left
    (hb ⟨coneDirection 0 z,hn⟩ _ _ v hE hB hv) (inv_nonneg.mpr (sq_nonneg _))).trans_eq (by ring)

lemma norm_integral_annulus_inverse_sq_le {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {F : Vec → W} {ε R C : ℝ} (hε : 0<ε) (hεR : ε≤R)
    (hC : 0≤C) (hF : ∀ z∈ball (0:Vec) R \ ball (0:Vec) ε, ‖F z‖≤C/‖z‖^2) :
    ‖∫ z in ball (0:Vec) R \ ball (0:Vec) ε,F z‖≤4*Real.pi*C*R := by
  have hR : 0≤R := hε.le.trans hεR
  by_cases hi : IntegrableOn F (ball (0:Vec) R \ ball (0:Vec) ε)
  · rw [integral_annulus_polar hε hi]
    have hn (n : Sphere) : ‖∫ r in Ico ε R,r^2 • F (r • n.1)‖≤C*R := by
      have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (Ico ε R))
        (f:=fun r => r^2 • F (r • n.1)) (C:=C) (by
          filter_upwards [ae_restrict_mem measurableSet_Ico] with r hr
          have hr0 : 0 < r := hε.trans_le hr.1
          have hnorm : ‖r • n.1‖=r := by
            simp only [norm_smul,Real.norm_of_nonneg hr0.le,sphere_norm,mul_one]
          have hb := hF (r • n.1) (by
            simp only [Set.mem_sdiff,mem_ball,dist_zero_right,hnorm,not_lt]
            exact ⟨hr.2,hr.1⟩)
          rw [hnorm] at hb
          rw [norm_smul,Real.norm_of_nonneg (sq_nonneg r)]
          exact (mul_le_mul_of_nonneg_left hb (sq_nonneg r)).trans_eq (by field_simp))
      simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ico,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hεR)] at hh
      exact hh.trans (by nlinarith)
    have hh := norm_integral_le_of_norm_le_const (μ:=sphereMeasure) (ae_of_all _ hn)
    simpa only [sphere_area,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hh
  · rw [integral_undef hi,norm_zero]
    positivity

lemma transport_velocity_annulus_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hH : 0≤H) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (U t ε R : ℝ) (x : Vec),
      0<ε → ε≤R → R≤t → t≤U → U≤H →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportVelocityBulk P s t x e i z|≤C := by
  obtain ⟨K,hK,hkb⟩ := physical_transport_velocity_bound P M e i
  let D := volume.real (closedBall (0:Vec) P)*A*K
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨4*Real.pi*D*H,by positivity,?_⟩
  intro s U t ε R x hε hεR hRt htU hUH hf hEB
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb (z : Vec) (hz : z∈ball (0:Vec) R \ ball (0:Vec) ε) :
      ‖transportVelocityBulk P s t x e i z‖≤D/‖z‖^2 := by
    have hzr : ‖z‖<R ∧ ε≤‖z‖ := by simpa only [Set.mem_sdiff,mem_ball,dist_zero_right,not_lt] using hz
    have hzn : z≠0 := norm_pos_iff.mp (hε.trans_le hzr.2)
    have hrad : coneRadius 0 z=‖z‖ := by simp [coneRadius]
    have hu : t-coneRadius 0 z∈Icc (0:ℝ) U := by
      rw [hrad]
      exact ⟨by linarith,by linarith [norm_nonneg z]⟩
    have hh := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
      (f:=fun v => s.f (t-coneRadius 0 z,x+z,v)*
        divergence (fun w => transportConeCoefficient i (z,w) •
          (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)
      (C:=A*(K/‖z‖^2)) (by
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
        have hvP : ‖v‖≤P := by simpa only [mem_closedBall,dist_zero_right] using hv
        have hh := hkb s t x z v hzn hvP (hEB _ hu _).1 (hEB _ hu _).2
        rw [hrad] at hh
        rw [Real.norm_eq_abs,abs_mul]
        exact mul_le_mul (hf _ hu _ v) hh (abs_nonneg _) hA)
    exact hh.trans_eq (by simp only [Measure.real,Measure.restrict_apply_univ,D]; ring)
  rw [←Real.norm_eq_abs]
  exact (norm_integral_annulus_inverse_sq_le hε hεR hD hb).trans
    (mul_le_mul_of_nonneg_left (hRt.trans (htU.trans hUH)) (by positivity))

lemma transport_velocity_divergence_continuousOn {s : Solution} {t : ℝ} (x e : Vec) (i : Fin 3)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace) :
    ContinuousOn (fun p : Phase => divergence (fun w => transportConeCoefficient i (p.1,w) •
      (coneSpatialCoefficient 0 p.1 w e • coneLorentz s t x (p.1,w))) p.2)
      (retardedSpaceDomain t 0 ×ˢ univ) := by
  have hk : ContDiffOn ℝ 1 (transportConeCoefficient i) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (transportConeCoefficient_contDiffAt i hp.1.1.symm).contDiffWithinAt
  have hco : ContDiffOn ℝ 1 (fun z : Phase => coneSpatialCoefficient 0 z.1 z.2 e)
      (retardedSpaceDomain t 0 ×ˢ univ) := fun p hp =>
    (contDiffAt_coneSpatialCoefficient_phase hp.1.1).contDiffWithinAt
  have hK : ContDiffOn ℝ 1 (coneLorentz s t x) (retardedSpaceDomain t 0 ×ˢ univ) :=
    fun p hp => (coneLorentz_contDiffAt hE hB x hp.1.1.symm hp.1.2).contDiffWithinAt
  exact (continuousOn_phase_divergences (isOpen_retardedSpaceDomain t 0) (hk.smul (hco.smul hK))).2

lemma shifted_particle_continuousOn {f : Particle} {t U : ℝ} (x : Vec) (htU : t≤U)
    (hf : ContinuousOn f {p | p.1∈Icc (0:ℝ) U}) :
    ContinuousOn (fun p : Phase => f (t-coneRadius 0 p.1,x+p.1,p.2))
      (retardedSpaceDomain t 0 ×ˢ univ) := by
  apply hf.comp (by unfold coneRadius; fun_prop : Continuous
    (fun p : Phase => (t-coneRadius 0 p.1,x+p.1,p.2))).continuousOn
  intro p hp
  exact ⟨hp.1.2.le,by dsimp [coneRadius]; linarith [norm_nonneg ((0:Vec)-p.1)]⟩

lemma transport_bulk_split {s : Solution} {t U P ε R : ℝ} (x e : Vec) (i : Fin 3)
    (htU : t≤U) (hε : 0<ε) (hRt : R<t)
    (hf : ContinuousOn s.f {p | p.1∈Icc (0:ℝ) U})
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v, s.f (t-coneRadius 0 z,x+z,v)*
      (divergence (transportSpatialFlux v e i) z+
        divergence (fun w => transportConeCoefficient i (z,w) •
          (coneSpatialCoefficient 0 z w e • coneLorentz s t x (z,w))) v)) =
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportSingularBulk P s.f t x e i z)+
    (∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportVelocityBulk P s t x e i z) := by
  let A := ball (0:Vec) R \ ball (0:Vec) ε
  let C := closedBall (0:Vec) R \ ball (0:Vec) ε
  let U₀ := retardedSpaceDomain t 0
  let F : Phase → ℝ := fun p => s.f (t-coneRadius 0 p.1,x+p.1,p.2)
  let D : Phase → ℝ := fun p => divergence (transportSpatialFlux p.2 e i) p.1
  let V : Phase → ℝ := fun p => divergence (fun w => transportConeCoefficient i (p.1,w) •
    (coneSpatialCoefficient 0 p.1 w e • coneLorentz s t x (p.1,w))) p.2
  have hfC : ContinuousOn F (U₀ ×ˢ univ) := shifted_particle_continuousOn x htU hf
  have hDC : ContinuousOn D (U₀ ×ˢ univ) := (continuousOn_transportSpatialDivergence e i).mono
    (by intro p hp; exact hp.1.1.symm)
  have hVC : ContinuousOn V (U₀ ×ˢ univ) := transport_velocity_divergence_continuousOn x e i hE hB
  have hzero (z : Vec) (hz : z∈U₀) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    apply hP _ ⟨hz.2.le,?_⟩ _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
    dsimp [coneRadius]
    linarith [norm_nonneg ((0:Vec)-z)]
  have hAU : A⊆C := fun z hz => ⟨ball_subset_closedBall hz.1,hz.2⟩
  have hCU : C⊆U₀ := by
    intro z hz
    have hrz : ‖z‖≤R ∧ ε≤‖z‖ := by simpa only [C,Set.mem_sdiff,mem_closedBall,mem_ball,dist_zero_right,not_lt] using hz
    exact ⟨(norm_pos_iff.mp (hε.trans_le hrz.2)).symm,by simpa [coneRadius] using sub_pos.mpr (hrz.1.trans_lt hRt)⟩
  have hcompact : IsCompact C := (isCompact_closedBall _ _).diff isOpen_ball
  have hdI : IntegrableOn (fun z => ∫ v, F (z,v)*D (z,v)) A :=
    ((continuousOn_integral_uniform_support (isCompact_closedBall (0:Vec) P) (hfC.mul hDC)
      (by intro z hz v hv; dsimp only [Pi.mul_apply]; rw [hzero z hz v hv,zero_mul])).mono hCU).integrableOn_compact hcompact |>.mono_set hAU
  have hvI : IntegrableOn (fun z => ∫ v, F (z,v)*V (z,v)) A :=
    ((continuousOn_integral_uniform_support (isCompact_closedBall (0:Vec) P) (hfC.mul hVC)
      (by intro z hz v hv; dsimp only [Pi.mul_apply]; rw [hzero z hz v hv,zero_mul])).mono hCU).integrableOn_compact hcompact |>.mono_set hAU
  have hdi (z : Vec) (hz : z∈U₀) : Integrable (fun v => F (z,v)*D (z,v)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hfC.mul hDC).comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hz,mem_univ _⟩)
    · exact compactSupport_of_zero_off (isCompact_closedBall (0:Vec) P) (fun v hv => by rw [hzero z hz v hv,zero_mul])
  have hvi (z : Vec) (hz : z∈U₀) : Integrable (fun v => F (z,v)*V (z,v)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hfC.mul hVC).comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨hz,mem_univ _⟩)
    · exact compactSupport_of_zero_off (isCompact_closedBall (0:Vec) P) (fun v hv => by rw [hzero z hz v hv,zero_mul])
  calc
    _ = ∫ z in A, (∫ v,F (z,v)*D (z,v))+(∫ v,F (z,v)*V (z,v)) := by
      apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
      intro z hz
      simp only [mul_add]
      exact integral_add (hdi z (hCU (hAU hz))) (hvi z (hCU (hAU hz)))
    _ = (∫ z in A,∫ v,F (z,v)*D (z,v))+(∫ z in A,∫ v,F (z,v)*V (z,v)) := integral_add hdI hvI
    _ = _ := by
      congr 1
      · apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
        intro z hz
        rw [transportSingularBulk]
        simpa only [F,D,mul_comm] using
          (setIntegral_eq_integral_of_forall_compl_eq_zero (μ:=volume) (f:=fun v => F (z,v)*D (z,v)) (fun v hv => by
            change F (z,v)*D (z,v)=0
            rw [hzero z (hCU (hAU hz)) v hv,zero_mul])).symm
      · apply setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball)
        intro z hz
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => by
          change F (z,v)*V (z,v)=0
          rw [hzero z (hCU (hAU hz)) v hv,zero_mul])).symm

lemma transport_sphere_support {s : Solution} {t U P r : ℝ} (x e : Vec) (i : Fin 3)
    (hr : 0 ≤ r) (hrt : r≤t) (htU : t≤U)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) :
    (∫ n : Sphere,r^2*dot n.1 (∫ v,s.f (t-r,x+r • n.1,v) •
      transportSpatialFlux v e i (r • n.1)) ∂sphereMeasure) =
    (∫ n : Sphere,r^2*dot n.1 (∫ v in closedBall (0:Vec) P,s.f (t-r,x+r • n.1,v) •
      transportSpatialFlux v e i (r • n.1)) ∂sphereMeasure) := by
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    dsimp only
    congr 2
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
    intro v hv
    rw [hP _ ⟨by linarith,by linarith⟩ _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),zero_smul])

lemma abs_sub_sub_add_le (a b c d : ℝ) :
    |a-b-(c+d)|≤|a|+|b|+|c|+|d| := by
  linarith [abs_sub a b,abs_sub (a-b) (c+d),abs_add_le c d]

lemma electric_transport_annulus_gradient_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧
    ∀ (s : Solution) (U t N ε R : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤N → 0<ε → ε≤R → R<t →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε, ∫ v,
        transportConeCoefficient i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤
        B+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨Cb,hCb,hcb⟩ := transport_sphere_boundary_bound P A e i hA
  obtain ⟨Cv,hCv,hcv⟩ := transport_velocity_annulus_bound P A M H e i hA hH
  obtain ⟨C,D,hC,hD,hcd⟩ := physical_transport_annulus_log_bound P H A e i hA
  refine ⟨2*Cb+Cv+1,C,D,by positivity,hC,hD,?_⟩
  intro s U t N ε R x ht htU hUH hN hε hεR hRt hf hE hB hc heq hfA hP hEB hfN
  have hfc : ContinuousOn s.f {p | p.1∈Icc (0:ℝ) U} := hf.continuousOn.mono (fun p hp => hp.1)
  have hfd (u : ℝ) (hu : u∈Icc (0:ℝ) U) (v : Vec) : Differentiable ℝ (fun y => s.f (u,y,v)) := by
    have hh : ContDiff ℝ 1 (fun y => s.f (u,y,v)) := by
      apply contDiffOn_univ.mp
      exact hf.comp ((contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)).contDiffOn)
        (fun _ _ => hu.1)
    exact hh.differentiable (by simp)
  have hbR := hcb s.f t U R x (hε.trans_le hεR) hRt.le htU hfA
  have hbε := hcb s.f t U ε x hε (hεR.trans hRt.le) htU hfA
  have hbv := hcv s U t ε R x hε hεR hRt.le htU hUH hfA hEB
  have hbs := hcd U t N ε R s.f ht htU hUH hN hε hRt.le hfc hfd hfA hfN x
  rw [electric_transport_division_annulus hf hE hB hc heq htU hε hεR hRt x e i,
    transport_sphere_support x e i (hε.le.trans hεR) hRt.le htU hP,
    transport_sphere_support x e i hε.le (hεR.trans hRt.le) htU hP,
    transport_bulk_split x e i htU hε hRt hfc hE hB hP]
  calc
    _ ≤ |∫ n : Sphere,R^2*dot n.1 (∫ v in closedBall (0:Vec) P,s.f (t-R,x+R • n.1,v) •
        transportSpatialFlux v e i (R • n.1)) ∂sphereMeasure|+
      |∫ n : Sphere,ε^2*dot n.1 (∫ v in closedBall (0:Vec) P,s.f (t-ε,x+ε • n.1,v) •
        transportSpatialFlux v e i (ε • n.1)) ∂sphereMeasure|+
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportSingularBulk P s.f t x e i z|+
      |∫ z in ball (0:Vec) R \ ball (0:Vec) ε,transportVelocityBulk P s t x e i z| := by
        exact abs_sub_sub_add_le _ _ _ _
    _ ≤ _ := by linarith

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

lemma transportConeCoefficient_uniform_bound (P : ℝ) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ z v : Vec, z≠0 → ‖v‖≤P →
      |transportConeCoefficient i (z,v)|≤C/‖z‖^2 := by
  let K := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  have hc : ContinuousOn (fun p : Phase => transportAngularCore p.1 (velocity p.2) i) K := by
    intro p hp
    have hn : ‖p.1‖=1 := by simpa only [mem_sphere,dist_zero_right] using hp.1
    have hh := contDiffAt_transportAngularCore (k:=1) (z:=p) contDiffAt_fst
      (contDiff_velocity.contDiffAt.comp p contDiffAt_snd) (cone_denom_pos p.2 p.1 hn).ne'
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.continuousAt.comp hh.continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z v hz hv
  have hb := hC (coneDirection 0 z,v) ⟨by
    simpa only [mem_sphere,dist_zero_right] using coneDirection_norm hz.symm,
    by simpa only [mem_closedBall,dist_zero_right] using hv⟩
  unfold transportConeCoefficient
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
  apply (mul_le_mul_of_nonneg_left (hb.trans (le_max_left _ _)) (inv_nonneg.mpr (sq_nonneg _))).trans_eq
  simp only [coneRadius,zero_sub,norm_neg]
  ring

lemma transport_derivative_integrable {s : Solution} {U t P N : ℝ} (x e : Vec) (i : Fin 3)
    (_ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (_hN : 0≤N)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    IntegrableOn (fun z => ∫ v,transportConeCoefficient i (z,v)*
      fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)) (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => transportConeCoefficient i p*
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
    exact ((transportConeCoefficient_contDiffAt i hh.1).continuousAt.mul
      (hdf.clm_apply continuousAt_const)).continuousWithinAt
  have hzero (z : Vec) (hz : z∈A) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    have hh := hzprop hz
    have hvP : P<‖v‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hv
    have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
      funext (fun y => hP _ ⟨hh.2.1.le,hh.2.2⟩ y v hvP)
    dsimp [F]
    rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e,he]
    simp
  obtain ⟨C,hC,hcb⟩ := transportConeCoefficient_uniform_bound P i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have hK : IsCompact (closedBall (0:Vec) P) := isCompact_closedBall _ _
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=D) (by norm_num)
    (continuousOn_integral_uniform_support hK hfc hzero)
  intro z hz hzt
  have hza : z∈A := ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hh := hzprop hza
  have heq : (∫ v,F (z,v))=∫ v in closedBall (0:Vec) P,F (z,v) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzero z hza)).symm
  change ‖∫ v,F (z,v)‖≤_
  rw [heq,Real.rpow_neg (norm_nonneg z),Real.rpow_two]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => F (z,v)) (C:=(C/‖z‖^2)*(N*‖e‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      dsimp [F]
      rw [abs_mul,←particle_spatial_fderiv (particle_differentiableAt_positive hf hh.2.1 _ _) e]
      apply mul_le_mul (hcb z v hh.1 (by simpa only [mem_closedBall,dist_zero_right] using hv))
      · simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans (mul_le_mul_of_nonneg_right (hfN _ ⟨hh.2.1.le,hh.2.2⟩ _ v) (norm_nonneg e))
      · exact abs_nonneg _
      · positivity)
  exact hb.trans_eq (by simp only [D,Measure.real,Measure.restrict_apply_univ]; ring)

lemma electric_transport_gradient_bound (P A M H : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧
    ∀ (s : Solution) (U t N : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |∫ z in ball (0:Vec) t, ∫ v,
        transportConeCoefficient i (z,v)*fderiv ℝ s.f (t-coneRadius 0 z,x+z,v) (0,e,0)|≤
        B+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨B,C,D,hB,hC,hD,hbound⟩ := electric_transport_annulus_gradient_bound P A M H e i hA hH
  refine ⟨B,C,D,hB,hC,hD,?_⟩
  intro s U t N x ht htU hUH hN hf hE hB hc heq hfA hP hEB hfN
  apply norm_integral_ball_of_annulus_bound ht (transport_derivative_integrable x e i ht htU hf hN hP hfN)
  intro ε R hε hεR hRt
  exact hbound s U t N ε R x ht htU hUH hN hε hεR hRt hf hE hB hc heq hfA hP hEB hfN


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma particle_fixed_time_contDiff {s : Solution} {k : ℕ∞ω} {u : ℝ}
    (hf : ContDiffOn ℝ k s.f particleHalfSpace) (hu : 0≤u) :
    ContDiff ℝ k (fun p : Phase => s.f (u,p)) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => hu)

lemma transport_kernel_velocity_contDiff (i : Fin 3) {z : Vec} (hz : z≠0) :
    ContDiff ℝ 1 (fun v => transportConeCoefficient i (z,v)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  exact (transportConeCoefficient_contDiffAt i hz).comp v (contDiffAt_const.prodMk contDiffAt_id)

lemma hasDerivAt_transport_particle_line {s : Solution} {u P : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hu : 0<u)
    (hP : ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (x e z : Vec) (hz : z≠0) (i : Fin 3) (a : ℝ) :
    HasDerivAt (fun q : ℝ => ∫ v,transportConeCoefficient i (z,v)*s.f (u,x+q • e,v))
      (∫ v,transportConeCoefficient i (z,v)*fderiv ℝ s.f (u,x+a • e,v) (0,e,0)) a := by
  let F : ℝ × Vec → ℝ := fun p => s.f (u,x+p.1 • e,p.2)
  let w : Vec → ℝ := fun v => transportConeCoefficient i (z,v)
  have hF : ContDiff ℝ 1 F := (particle_fixed_time_contDiff hf hu.le).comp
    ((contDiff_const.add (contDiff_fst.smul contDiff_const)).prodMk contDiff_snd)
  have hw : ContDiff ℝ 1 w := transport_kernel_velocity_contDiff i hz
  have hzero (a : ℝ) (_ : a∈(univ : Set ℝ)) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (a,v)=0 :=
    hP _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv)
  have hG : ContDiffOn ℝ 1 (fun p : ℝ × Vec => w p.2*F p) (univ ×ˢ univ) :=
    ((hw.comp contDiff_snd).mul hF).contDiffOn
  have hd := (hasFDerivAt_integral_uniform_support isOpen_univ (isCompact_closedBall (0:Vec) P)
    (mem_univ a) hG (by intro q hq v hv; rw [hzero q hq v hv,mul_zero])).differentiableAt.hasDerivAt
  rw [show deriv (fun x => ∫ v, w v*F (x,v)) a = fderiv ℝ (fun x => ∫ v,w v*F (x,v)) a 1 from rfl,fderiv_weighted_integral_uniform_support_apply isOpen_univ
    (isCompact_closedBall (0:Vec) P) (mem_univ a) hF.contDiffOn hw hzero] at hd
  apply hd.congr_deriv
  apply integral_congr_ae
  exact ae_of_all _ (fun v => by
    apply congrArg (fun r : ℝ => w v*r)
    have hm : HasFDerivAt (fun p : ℝ × Vec => (u,x+p.1 • e,p.2))
        ((0 : (ℝ × Vec) →L[ℝ] ℝ).prod
          (((ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ Vec) e)).prod
            (ContinuousLinearMap.snd ℝ ℝ Vec))) (a,v) := by
      convert (hasFDerivAt_const u (a,v)).prodMk
        (((hasFDerivAt_const x (a,v)).add ((hasFDerivAt_fst (𝕜:=ℝ)).smul_const e)).prodMk
          (hasFDerivAt_snd (𝕜:=ℝ))) using 1
      all_goals try with_reducible_and_instances rfl
      first | rfl | simp
    have hh := (particle_differentiableAt_positive hf hu _ v).hasFDerivAt.comp
      (f:=fun p : ℝ × Vec => (u,x+p.1 • e,p.2)) (a,v) hm
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      zero_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',one_smul,F,Function.comp_def] using
      congrArg (fun L : (ℝ × Vec) →L[ℝ] ℝ => L (1,0)) hh.fderiv)

lemma norm_transport_velocity_integral_le {P C A : ℝ} {z : Vec} {i : Fin 3}
    {g : Vec → ℝ} (_hA : 0≤A)
    (hk : ∀ v, ‖v‖≤P → |transportConeCoefficient i (z,v)|≤C/‖z‖^2)
    (hzero : ∀ v, P<‖v‖ → g v=0) (hg : ∀ v, |g v|≤A) :
    ‖∫ v,transportConeCoefficient i (z,v)*g v‖≤volume.real (closedBall (0:Vec) P)*C*A/‖z‖^2 := by
  have heq : (∫ v,transportConeCoefficient i (z,v)*g v)=
      ∫ v in closedBall (0:Vec) P,transportConeCoefficient i (z,v)*g v := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hzero v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),mul_zero]
  rw [heq]
  let : IsFiniteMeasure (volume.restrict (closedBall (0:Vec) P)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact (isCompact_closedBall _ _).measure_lt_top⟩
  have hb := norm_integral_le_of_norm_le_const (μ:=volume.restrict (closedBall (0:Vec) P))
    (f:=fun v => transportConeCoefficient i (z,v)*g v) (C:=(C/‖z‖^2)*A) (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with v hv
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hk v (by simpa only [mem_closedBall,dist_zero_right] using hv)) (hg v)
        (abs_nonneg _) (le_trans (abs_nonneg _) (hk v (by simpa only [mem_closedBall,dist_zero_right] using hv))))
  exact hb.trans_eq (by simp only [Measure.real,Measure.restrict_apply_univ]; ring)

lemma transport_density_integrable {s : Solution} {U t P A : ℝ} (x : Vec) (i : Fin 3)
    (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hA : 0≤A)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) :
    IntegrableOn (fun z => ∫ v,transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,x+z,v))
      (ball (0:Vec) t) := by
  let F : Phase → ℝ := fun p => transportConeCoefficient i p*s.f (t-coneRadius 0 p.1,x+p.1,p.2)
  let U₀ := retardedSpaceDomain t 0
  have htime {z : Vec} (hz : z∈U₀) : t-coneRadius 0 z∈Icc (0:ℝ) U :=
    ⟨hz.2.le,(sub_le_self _ (norm_nonneg _)).trans htU⟩
  have hk : ContinuousOn (transportConeCoefficient i) (U₀ ×ˢ univ) := by
    intro p hp
    exact (transportConeCoefficient_contDiffAt i hp.1.1.symm).continuousAt.continuousWithinAt
  have hfc : ContinuousOn F (U₀ ×ˢ univ) := hk.mul
      (shifted_particle_continuousOn x htU (hf.continuousOn.mono (fun p hp => hp.1)))
  have hzero (z : Vec) (hz : z∈U₀) (v : Vec) (hv : v∉closedBall (0:Vec) P) : F (z,v)=0 := by
    dsimp [F]
    rw [hP _ (htime hz) _ v (by simpa only [mem_closedBall,dist_zero_right,not_le] using hv),mul_zero]
  have hsub : ball (0:Vec) t \ ({0} : Set Vec)⊆U₀ := by
    intro z hz
    exact ⟨(show z≠0 from hz.2).symm,by simpa only [coneRadius,zero_sub,norm_neg] using
      (sub_pos.mpr (show ‖z‖<t by simpa only [mem_ball,dist_zero_right] using hz.1))⟩
  obtain ⟨C,hC,hcb⟩ := transportConeCoefficient_uniform_bound P i
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=volume.real (closedBall (0:Vec) P)*C*A)
    (by norm_num) ((continuousOn_integral_uniform_support (isCompact_closedBall _ _) hfc hzero).mono hsub)
  intro z hz hzt
  have hzu : z∈U₀ := hsub ⟨by simpa only [mem_ball,dist_zero_right] using hzt,norm_pos_iff.mp hz⟩
  have hb := norm_transport_velocity_integral_le hA (fun v hv => hcb z v (norm_pos_iff.mp hz) hv)
    (hP _ (htime hzu) (x+z)) (hfA _ (htime hzu) (x+z))
  simpa only [Real.rpow_neg (norm_nonneg z),Real.rpow_two,div_eq_mul_inv] using hb

lemma hasDerivAt_electric_transport_integral {s : Solution} {U t P A N : ℝ}
    (x e : Vec) (i : Fin 3) (a : ℝ)
    (ht : 0<t) (htU : t≤U) (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hA : 0≤A) (hN : 0≤N)
    (hP : ∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0)
    (hfA : ∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A)
    (hfN : ∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) :
    HasDerivAt (fun q : ℝ => ∫ z in ball (0:Vec) t, ∫ v,
      transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v))
      (∫ z in ball (0:Vec) t, ∫ v,transportConeCoefficient i (z,v)*
        fderiv ℝ s.f (t-coneRadius 0 z,(x+a • e)+z,v) (0,e,0)) a := by
  obtain ⟨C,hC,hcb⟩ := transportConeCoefficient_uniform_bound P i
  let D := volume.real (closedBall (0:Vec) P)*C*N*‖e‖
  have htime {z : Vec} (hz : z∈ball (0:Vec) t) :
      0<t-coneRadius 0 z ∧ t-coneRadius 0 z≤U := by
    have hr : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
    exact ⟨by simpa only [coneRadius,zero_sub,norm_neg] using sub_pos.mpr hr,
      (sub_le_self _ (norm_nonneg _)).trans htU⟩
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s:=univ)
    (bound:=fun z : Vec => D*‖z‖^(-(2:ℝ))) (by simp)
    (Eventually.of_forall (fun q => (transport_density_integrable (x+q • e) i htU hf hA hP hfA).aestronglyMeasurable))
    (transport_density_integrable (x+a • e) i htU hf hA hP hfA)
    (transport_derivative_integrable (x+a • e) e i ht htU hf hN hP hfN).aestronglyMeasurable
    ?_ ((integrableOn_norm_rpow_neg (R:=t) (show (2:ℝ)<3 by norm_num)).const_mul D) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    intro q _
    have htz := htime hz
    refine (norm_transport_velocity_integral_le (mul_nonneg hN (norm_nonneg e))
      (fun v hv => hcb z v hz0 hv) ?_ ?_).trans_eq ?_
    · intro v hv
      rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf htz.1 _ _) e]
      have he : (fun y => s.f (t-coneRadius 0 z,y,v))=fun _ => (0:ℝ) :=
        funext (fun y => hP _ ⟨htz.1.le,htz.2⟩ y v hv)
      rw [he]
      simp
    · intro v
      rw [←particle_spatial_fderiv (particle_differentiableAt_positive hf htz.1 _ _) e]
      simpa only [Real.norm_eq_abs] using (ContinuousLinearMap.le_opNorm _ e).trans
        (mul_le_mul_of_nonneg_right (hfN _ ⟨htz.1.le,htz.2⟩ _ v) (norm_nonneg e))
    · simp only [D,Real.rpow_neg (norm_nonneg z),Real.rpow_two]
      ring
  · filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    intro q _
    have htz := htime hz
    simpa only [add_right_comm] using hasDerivAt_transport_particle_line hf htz.1
      (hP _ ⟨htz.1.le,htz.2⟩) (x+z) e z hz0 i q

lemma electric_transport_deriv_bound_oai (P A M H : ℝ) (e : Vec) (i : Fin 3)
    (hA : 0≤A) (hH : 0≤H) :
    ∃ B C D : ℝ, 0≤B ∧ 0≤C ∧ 0≤D ∧
    ∀ (s : Solution) (U t N : ℝ) (x : Vec),
      0<t → t≤U → U≤H → 0≤N →
      ContDiffOn ℝ 1 s.f particleHalfSpace →
      ContDiffOn ℝ 1 s.E fieldHalfSpace → ContDiffOn ℝ 1 s.B fieldHalfSpace →
      CompactOnFiniteHorizons s → EquationsBefore s U →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, |s.f (u,y,v)|≤A) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, P<‖v‖ → s.f (u,y,v)=0) →
      (∀ u∈Icc (0:ℝ) U, ∀ y, ‖s.E (u,y)‖≤M ∧ ‖s.B (u,y)‖≤M) →
      (∀ u∈Icc (0:ℝ) U, ∀ y v, ‖fderiv ℝ (fun z => s.f (u,z,v)) y‖≤N) →
      |deriv (fun q : ℝ => ∫ z in ball (0:Vec) t, ∫ v,
        transportConeCoefficient i (z,v)*s.f (t-coneRadius 0 z,(x+q • e)+z,v)) 0|≤
        B+D*(Real.log (max 1 H)+Real.log (1+C*N)) := by
  obtain ⟨B,C,D,hB,hC,hD,hb⟩ := electric_transport_gradient_bound P A M H e i hA hH
  refine ⟨B,C,D,hB,hC,hD,?_⟩
  intro s U t N x ht htU hUH hN hf hE hBB hc heq hfA hP hEB hfN
  rw [(hasDerivAt_electric_transport_integral x e i 0 ht htU hf hA hN hP hfA hfN).deriv]
  simpa only [zero_smul,add_zero] using hb s U t N x ht htU hUH hN hf hE hBB hc heq hfA hP hEB hfN

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.electric_transport_deriv_bound_oai := @OAI.RVM.electric_transport_deriv_bound_oai
