-- Prove2me | solution 1 for OAI.RVM.integrated_magneticMomentDensity_actual_before
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:32:43.432905+00:00
-- url     : https://prove2.me/submissions/b7d27649-4199-4970-8cb8-7fa9d9b6d0e3

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

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

lemma hasDerivAt_dot {f g : ℝ → Vec} {f' g' : Vec} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => dot (f t) (g t))
      (dot (f s) g' + dot f' (g s)) s := by
  simpa only [dot_eq_inner] using hf.inner ℝ hg

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

lemma hasDerivAt_particle_energy {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => q (V t)) (dot (velocity (V s)) K) s := by
  have hp : 1+‖V s‖^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hV.norm_sq).const_add 1).sqrt hp
  convert h using 1 <;> try rfl
  rw [velocity, dot_smul_left, dot_eq_inner]
  dsimp [q]
  have hq : Real.sqrt (1+‖V s‖^2) ≠ 0 := ne_of_gt (q_pos (V s))
  field_simp

lemma hasDerivAt_particle_velocity {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => velocity (V t))
      ((q (V s))⁻¹ • (K-dot (velocity (V s)) K • velocity (V s))) s := by
  have hq := hasDerivAt_particle_energy hV
  have h := (hq.inv (ne_of_gt (q_pos (V s)))).smul hV
  convert h using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply, velocity, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

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

lemma fderiv_velocity_apply (v h : Vec) :
    fderiv ℝ velocity v h = (q v)⁻¹ • (h-dot (velocity v) h • velocity v) := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt velocity (fderiv ℝ velocity v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_velocity hc
  have he := h₁.unique h₂
  simpa using he

lemma spatialPartial_velocity (v : Vec) (i j : Fin 3) :
    spatialPartial (fun w => velocity w j) v i =
      (q v)⁻¹ * ((if i=j then 1 else 0)-velocity v i*velocity v j) := by
  have hv : DifferentiableAt ℝ velocity v := contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v
  have hj := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp v hv.hasFDerivAt
  have hp := congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i)) hj.fderiv
  have h : spatialPartial (fun w => velocity w j) v i =
      (fderiv ℝ velocity v (basis i)) j := by
    convert hp using 1 <;> rfl
  rw [h, fderiv_velocity_apply]
  simp [basis, dot, eq_comm]

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

lemma divergence_magnetic_force (v B : Vec) :
    divergence (fun w => cross (velocity w) B) v = 0 := by
  have hd (j : Fin 3) : DifferentiableAt ℝ (fun w : Vec => velocity w j) v :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) j).differentiableAt.comp v
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v)
  simp only [divergence, Fin.sum_univ_succ]
  change spatialPartial (fun w => velocity w 1 * B 2 - velocity w 2 * B 1) v 0 +
    (spatialPartial (fun w => velocity w 2 * B 0 - velocity w 0 * B 2) v 1 +
    (spatialPartial (fun w => velocity w 0 * B 1 - velocity w 1 * B 0) v 2 + 0)) = 0
  simp only [spatialPartial_sub ((hd _).mul_const _) ((hd _).mul_const _),
    spatialPartial_mul (hd _) (differentiableAt_const _), spatialPartial_velocity]
  simp [spatialPartial]
  ring

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

lemma contDiff_lorentz (E B : Vec) {k : ℕ∞ω} :
    ContDiff ℝ k (fun v => E+cross (velocity v) B) := by
  exact contDiff_const.add (contDiff_cross.comp (contDiff_velocity.prodMk contDiff_const))

lemma divergence_lorentz (v E B : Vec) :
    divergence (fun w => E+cross (velocity w) B) v = 0 := by
  have hh (i : Fin 3) : spatialPartial (fun w => (E+cross (velocity w) B) i) v i =
      spatialPartial (fun w => cross (velocity w) B i) v i := by
    simp only [PiLp.add_apply, spatialPartial]
    rw [fderiv_const_add]
  simpa only [divergence, hh] using divergence_magnetic_force v B

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

lemma integrable_param_fderiv_apply_weight
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {U : Set H} {K : Set Vec} {F : H × Vec → ℝ} {p : H} {w : Vec → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ)) (hw : Continuous w)
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (b : H × Vec) :
    Integrable (fun v => w v * fderiv ℝ F (p,v) b) := by
  have hc : Continuous (fun v : Vec => fderiv ℝ F (p,v)) :=
    (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hp, mem_univ _⟩)
  apply (hw.mul (hc.clm_apply continuous_const)).integrable_of_hasCompactSupport
  apply (compactSupport_param_fderiv hU hK hp hzero).comp_left
    (g := fun L : (H × Vec) →L[ℝ] ℝ => L b) (by simp) |>.mul_left

lemma contDiff_reassociate {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : (ℝ × Vec) × Vec => (z.1.1,z.1.2,z.2)) :=
  contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)

lemma particle_spacetime_local_data {s : Solution} {t : ℝ} (x : Vec)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) (ht : 0 < t) :
    ∃ (U : Set (ℝ × Vec)) (K : Set Vec),
      IsOpen U ∧ IsCompact K ∧ (t,x) ∈ U ∧
      ContDiffOn ℝ 1 (particleBySpacetime s.f) (U ×ˢ univ) ∧
      ∀ p ∈ U, ∀ v ∉ K, particleBySpacetime s.f (p,v) = 0 := by
  obtain ⟨K₀,hK₀,hzero⟩ := hc (t+1) (by linarith)
  let U : Set (ℝ × Vec) := {p | p.1 ∈ Ioo 0 (t+1)}
  refine ⟨U, Prod.snd '' K₀, isOpen_Ioo.preimage continuous_fst,
    hK₀.image continuous_snd, ⟨ht,by linarith⟩, ?_, ?_⟩
  · exact hf.comp contDiff_reassociate.contDiffOn (fun z hz => le_of_lt hz.1.1)
  · intro p hp v hv
    change s.f (p.1,p.2,v) = 0
    by_contra hn
    have hh : (p.2,v) ∈ tsupport (fun z => s.f (p.1,z)) := subset_tsupport _ hn
    have hm := hzero p.1 ⟨le_of_lt hp.1, le_of_lt hp.2⟩ hh
    exact hv ⟨(p.2,v),hm,rfl⟩

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

lemma RegularParticle.local_data {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 < t) (x : Vec) :
    ∃ (U : Set (ℝ × Vec)) (K : Set Vec),
      IsOpen U ∧ IsCompact K ∧ (t,x) ∈ U ∧
      ContDiffOn ℝ 1 (particleBySpacetime f) (U ×ˢ univ) ∧
      ∀ p ∈ U, ∀ v ∉ K, particleBySpacetime f (p,v) = 0 :=
  particle_spacetime_local_data (s := ⟨f,0,0⟩) x hf.1 hf.2 ht

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

lemma RegularParticle.moment_integrable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    Integrable (fun v : Vec => f (t,x,v) • w v) := by
  obtain ⟨hs,hc⟩ := hf.slice ht x
  exact (hs.continuous.smul hw).integrable_of_hasCompactSupport hc.smul_right

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

lemma dot_zero_right_rvm (a : Vec) : dot a 0=0 := by simp [dot]
lemma dot_zero_left_rvm (a : Vec) : dot 0 a=0 := by simp [dot]

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

lemma hasDerivAt_eulerian_direction {Y : ℝ → Vec} {u x : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h : x≠Y s) :
    HasDerivAt (coneDirection x ∘ Y)
      ((coneRadius x (Y s))⁻¹ •
        (dot (coneDirection x (Y s)) u • coneDirection x (Y s)-u)) s := by
  have hr := hasDerivAt_coneRadius hY h
  have hr0 : coneRadius x (Y s)≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have hh := (hr.inv hr0).smul ((hasDerivAt_const s x).sub hY)
  convert hh using 1 <;> try rfl
  ext i
  simp only [coneDirection,coneRadius,Function.comp_apply,Pi.inv_apply,Pi.sub_apply,PiLp.neg_apply,PiLp.add_apply,
      PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,zero_sub,dot_smul_left]
  ring

lemma hasDerivAt_eulerianG_space {r : ℝ → ℝ} {n : ℝ → Vec} {u : Vec} {s : ℝ}
    (hr : HasDerivAt r (-dot (n s) u) s)
    (hn : HasDerivAt n ((r s)⁻¹ • (dot (n s) u • n s-u)) s)
    (hr0 : r s≠0) (hd : 1-dot (n s) u≠0) :
    HasDerivAt (fun t => eulerianG (r t) (n t) u)
      (((1-dot u u)/((r s)^2*(1-dot (n s) u)^2)) • (n s-u) -
        ((r s)^2)⁻¹ • n s) s := by
  have hd' := (hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_dot hn (hasDerivAt_const s u))
  have hh := ((hr.mul hd').inv (mul_ne_zero hr0 hd)).smul
    (hn.sub (hasDerivAt_const s u))
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply,Pi.mul_apply,Pi.sub_apply,PiLp.add_apply,PiLp.sub_apply,
      PiLp.smul_apply,smul_eq_mul,dot_smul_left,dot_sub_left,
      dot_zero_right_rvm,zero_add,sub_zero,zero_sub]
  field_simp
  ring

lemma hasDerivAt_eulerianG_velocity {u : ℝ → Vec} {b n : Vec} {r s : ℝ}
    (hu : HasDerivAt u b s) (hr : r≠0) (hd : 1-dot n (u s)≠0) :
    HasDerivAt (fun t => eulerianG r n (u t))
      ((r*(1-dot n (u s))^2)⁻¹ •
        ((dot n b) • (n-u s)-(1-dot n (u s)) • b)) s := by
  have hd' := (hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_dot (hasDerivAt_const s n) hu)
  have hh := (((hasDerivAt_const s r).mul hd').inv (mul_ne_zero hr hd)).smul
    ((hasDerivAt_const s n).sub hu)
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply,Pi.mul_apply,Pi.sub_apply,PiLp.neg_apply,PiLp.add_apply,PiLp.sub_apply,
      PiLp.smul_apply,smul_eq_mul,dot_zero_left_rvm,zero_add,zero_mul,zero_sub]
  field_simp
  ring

lemma eulerian_kernel_decomposition (r : ℝ) (n u b : Vec)
    (hr : r≠0) (hd : 1-dot n u≠0) :
    (r^2)⁻¹ • n +
      (((1-dot u u)/(r^2*(1-dot n u)^2)) • (n-u)-(r^2)⁻¹ • n) +
      (r*(1-dot n u)^2)⁻¹ • ((dot n b) • (n-u)-(1-dot n u) • b) =
      (1-dot n u) • physicalElectricKernel r n u b := by
  ext i
  simp only [physicalElectricKernel,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp
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

lemma retarded_transport_identity {f : Particle} {x y v u K : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y)
    (heq : fderiv ℝ f (t-coneRadius x y,y,v) (1,u,K)=0) :
    fderiv ℝ (fun z : Phase => f (t-coneRadius x z.1,z)) (y,v) (u,K) =
      -(1-dot (coneDirection x y) u)*fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0) := by
  rw [retarded_transport_chain hf hxy]
  have hv : (dot (coneDirection x y) u,u,K) =
      (1,u,K)-(1-dot (coneDirection x y) u) • ((1:ℝ),(0:Vec),(0:Vec)) := by
    ext <;> simp
  rw [hv,map_sub,map_smul,heq]
  simp only [smul_eq_mul,zero_sub,neg_mul]

lemma dot_gradient_direction (g : Vec → ℝ) (y w : Vec) :
    dot (gradient g y) w=fderiv ℝ g y w := by
  rw [dot_comm,clm_sum_basis]
  simp only [dot,gradient_apply,spatialPartial]

lemma divergence_const_rvm (w y : Vec) : divergence (fun _ : Vec => w) y=0 := by
  simp [divergence,spatialPartial]

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

lemma phase_divergence_transport {g : Phase → ℝ} {K : Vec → Vec} {y v u : Vec}
    (hg : DifferentiableAt ℝ g (y,v)) (hK : DifferentiableAt ℝ K v) :
    divergence (fun z => g (z,v) • u) y+divergence (fun w => g (y,w) • K w) v =
      fderiv ℝ g (y,v) (u,K v)+g (y,v)*divergence K v := by
  have hy : DifferentiableAt ℝ (fun z => g (z,v)) y :=
    hg.comp (f := fun z => (z,v)) y (differentiableAt_id.prodMk (differentiableAt_const v))
  have hv : DifferentiableAt ℝ (fun w => g (y,w)) v :=
    hg.comp (f := fun w => (y,w)) v ((differentiableAt_const y).prodMk differentiableAt_id)
  rw [divergence_smul hy (differentiableAt_const u),divergence_smul hv hK,
    divergence_const_rvm,mul_zero,add_zero,dot_gradient_direction,dot_gradient_direction,
    ← add_assoc,fderiv_phase_split hg]

lemma hasDerivAt_line_rvm (y u : Vec) :
    HasDerivAt (fun s : ℝ => y+s • u) u 0 := by
  have hh := (hasDerivAt_const (0:ℝ) y).add ((hasDerivAt_id (0:ℝ)).smul_const u)
  change HasDerivAt (fun s : ℝ => y+s • u) (0+(1:ℝ) • u) 0 at hh
  simpa only [zero_add,one_smul] using hh

lemma fderiv_of_line_rvm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : Vec → H} {y u : Vec} {w : H} (hg : DifferentiableAt ℝ g y)
    (hc : HasDerivAt (fun s : ℝ => g (y+s • u)) w 0) : fderiv ℝ g y u=w := by
  have h : HasFDerivAt g (fderiv ℝ g y) (y+(0:ℝ) • u) := by
    simpa only [zero_smul,add_zero] using hg.hasFDerivAt
  exact (h.comp_hasDerivAt 0 (hasDerivAt_line_rvm y u)).unique hc

lemma differentiableAt_coneRadius {x y : Vec} (h : x≠y) :
    DifferentiableAt ℝ (coneRadius x) y :=
  ((differentiableAt_const x).sub differentiableAt_id).norm ℝ (sub_ne_zero.mpr h)

lemma differentiableAt_coneDirection {x y : Vec} (h : x≠y) :
    DifferentiableAt ℝ (coneDirection x) y :=
  ((differentiableAt_coneRadius h).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))).smul
    ((differentiableAt_const x).sub differentiableAt_id)

lemma differentiableAt_eulerianG {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {r : H → ℝ} {n u : H → Vec} {s : H}
    (hr : DifferentiableAt ℝ r s) (hn : DifferentiableAt ℝ n s)
    (hu : DifferentiableAt ℝ u s) (hr0 : r s≠0) (hd : 1-dot (n s) (u s)≠0) :
    DifferentiableAt ℝ (fun z => eulerianG (r z) (n z) (u z)) s := by
  have hdot : DifferentiableAt ℝ (fun z => dot (n z) (u z)) s := by
    simpa only [dot_eq_inner] using hn.inner ℝ hu
  exact ((hr.mul ((differentiableAt_const (1:ℝ)).sub hdot)).inv
    (mul_ne_zero hr0 hd)).smul (hn.sub hu)

lemma fderiv_eulerianG_space {x y u : Vec} (hxy : x≠y)
    (hd : 1-dot (coneDirection x y) u≠0) :
    fderiv ℝ (fun z => eulerianG (coneRadius x z) (coneDirection x z) u) y u =
      ((1-dot u u)/((coneRadius x y)^2*(1-dot (coneDirection x y) u)^2)) •
        (coneDirection x y-u) - ((coneRadius x y)^2)⁻¹ • coneDirection x y := by
  have hr0 : coneRadius x y≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hg := differentiableAt_eulerianG (differentiableAt_coneRadius hxy)
    (differentiableAt_coneDirection hxy) (differentiableAt_const u) hr0 hd
  apply fderiv_of_line_rvm hg
  have hc := hasDerivAt_line_rvm y u
  have hxy' : x≠y+(0:ℝ) • u := by simpa only [zero_smul,add_zero] using hxy
  have hh := hasDerivAt_eulerianG_space
    (r := fun s => coneRadius x (y+s • u)) (n := fun s => coneDirection x (y+s • u))
    (u := u) (s := 0) (hasDerivAt_coneRadius hc hxy')
    (hasDerivAt_eulerian_direction hc hxy')
    (by simpa only [zero_smul,add_zero] using hr0)
    (by simpa only [zero_smul,add_zero] using hd)
  simpa only [Function.comp_apply,zero_smul,add_zero] using hh

lemma fderiv_eulerianG_velocity {r : ℝ} {n v K : Vec} (hr : r≠0)
    (hd : 1-dot n (velocity v)≠0) :
    fderiv ℝ (fun w => eulerianG r n (velocity w)) v K =
      (r*(1-dot n (velocity v))^2)⁻¹ •
        ((dot n (fderiv ℝ velocity v K)) • (n-velocity v)-
          (1-dot n (velocity v)) • (fderiv ℝ velocity v K)) := by
  have hv := (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω)≠0)) v
  apply fderiv_of_line_rvm (differentiableAt_eulerianG
    (differentiableAt_const r) (differentiableAt_const n) hv hr hd)
  have hvel := hasDerivAt_particle_velocity (hasDerivAt_line_rvm v K)
  have hh := hasDerivAt_eulerianG_velocity hvel hr
    (by simpa only [zero_smul,add_zero] using hd)
  simpa only [zero_smul,add_zero,fderiv_velocity_apply] using hh

lemma differentiableAt_retardedG {x y v : Vec} (hxy : x≠y) :
    DifferentiableAt ℝ (retardedG x) (y,v) := by
  apply differentiableAt_eulerianG (r := fun z : Phase => coneRadius x z.1)
    (n := fun z : Phase => coneDirection x z.1) (u := fun z : Phase => velocity z.2)
  · exact (differentiableAt_coneRadius hxy).comp (f:=Prod.fst) (y,v) differentiableAt_fst
  · exact (differentiableAt_coneDirection hxy).comp (f:=Prod.fst) (y,v) differentiableAt_fst
  · exact ((contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω)≠0)) v).comp
      (f:=Prod.snd) (y,v) differentiableAt_snd
  · exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  · exact (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'

lemma fderiv_retardedG {x y v K : Vec} (hxy : x≠y) :
    fderiv ℝ (retardedG x) (y,v) (velocity v,K) =
      (1-dot (coneDirection x y) (velocity v)) •
        physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v K) - ((coneRadius x y)^2)⁻¹ • coneDirection x y := by
  have hd := (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'
  have hr : coneRadius x y≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  rw [← fderiv_phase_split (differentiableAt_retardedG hxy)]
  change fderiv ℝ (fun z => eulerianG (coneRadius x z) (coneDirection x z) (velocity v)) y
    (velocity v)+fderiv ℝ (fun w => eulerianG (coneRadius x y) (coneDirection x y) (velocity w)) v K = _
  rw [fderiv_eulerianG_space hxy hd,fderiv_eulerianG_velocity hr hd]
  have he := eulerian_kernel_decomposition (coneRadius x y) (coneDirection x y)
    (velocity v) (fderiv ℝ velocity v K) hr hd
  exact eq_sub_of_add_eq (by simpa only [add_assoc,add_left_comm,add_comm] using he)

lemma differentiableAt_retardedDensity {f : Particle} {x y v : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y) :
    DifferentiableAt ℝ (retardedDensity f t x) (y,v) := by
  have hi : DifferentiableAt ℝ (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) :=
    ((differentiableAt_const t).sub ((differentiableAt_coneRadius hxy).comp
      (f:=Prod.fst) (y,v) differentiableAt_fst)).prodMk differentiableAt_id
  exact hf.comp (f := fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hi

lemma fderiv_vec_component_at {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : H → Vec} {z e : H} (hg : DifferentiableAt ℝ g z) (i : Fin 3) :
    fderiv ℝ (fun w => g w i) z e=(fderiv ℝ g z e) i := by
  have h := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp z hg.hasFDerivAt
  convert congrArg (fun L : H →L[ℝ] ℝ => L e) h.fderiv using 1 <;> rfl

lemma fderiv_cross_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F G : H → Vec} {z e : H} (hF : DifferentiableAt ℝ F z)
    (hG : DifferentiableAt ℝ G z) :
    fderiv ℝ (fun w => cross (F w) (G w)) z e =
      cross (fderiv ℝ F z e) (G z)+cross (F z) (fderiv ℝ G z e) := by
  have hi (A : H → Vec) (hA : DifferentiableAt ℝ A z) (i : Fin 3) :
      DifferentiableAt ℝ (fun w => A w i) z :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp z hA
  have hcross : DifferentiableAt ℝ (fun w => cross (F w) (G w)) z :=
    (contDiff_cross (k:=1)).differentiable (by simp) _ |>.comp z (hF.prodMk hG)
  have hmul (i j : Fin 3) : DifferentiableAt ℝ (fun w => F w i*G w j) z :=
    (hi F hF i).mul (hi G hG j)
  have hp (i j : Fin 3) : fderiv ℝ (fun w => F w i*G w j-F w j*G w i) z e =
      (fderiv ℝ F z e) i*G z j-(fderiv ℝ F z e) j*G z i +
      (F z i*(fderiv ℝ G z e) j-F z j*(fderiv ℝ G z e) i) := by
    rw [fderiv_fun_sub (hmul i j) (hmul j i),
      fderiv_fun_mul (hi F hF i) (hi G hG j),fderiv_fun_mul (hi F hF j) (hi G hG i)]
    simp only [sub_apply,add_apply,smul_apply,smul_eq_mul,fderiv_vec_component_at hF,
      fderiv_vec_component_at hG]
    ring
  ext i
  rw [← fderiv_vec_component_at hcross i]
  fin_cases i
  · exact hp 1 2
  · exact hp 2 0
  · exact hp 0 1

lemma fderiv_coneDirection_apply {x y u : Vec} (hxy : x≠y) :
    fderiv ℝ (coneDirection x) y u = (coneRadius x y)⁻¹ •
      (dot (coneDirection x y) u • coneDirection x y-u) := by
  apply fderiv_of_line_rvm (differentiableAt_coneDirection hxy)
  have hh := hasDerivAt_eulerian_direction (hasDerivAt_line_rvm y u)
    (by simpa only [zero_smul,add_zero] using hxy)
  convert hh using 1 <;> first | rfl | simp only [zero_smul,add_zero]

lemma eulerian_cross_direction {r : ℝ} {n u : Vec} (hr : r≠0)
    (hd : 1-dot n u≠0) :
    cross (r⁻¹ • (dot n u • n-u)) (eulerianG r n u) = (r^2)⁻¹ • cross n u := by
  ext i
  fin_cases i <;> dsimp [cross,eulerianG] <;> field_simp <;> ring

lemma differentiableAt_retardedH {x y v : Vec} (hxy : x≠y) :
    DifferentiableAt ℝ (retardedH x) (y,v) := by
  exact (contDiff_cross (k:=1)).differentiable (by simp) _ |>.comp
    (f:=fun z : Phase => (coneDirection x z.1,retardedG x z)) (y,v)
    (((differentiableAt_coneDirection hxy).comp (f:=Prod.fst) (y,v)
      differentiableAt_fst).prodMk (differentiableAt_retardedG hxy))

lemma fderiv_retardedH {x y v K : Vec} (hxy : x≠y) :
    fderiv ℝ (retardedH x) (y,v) (velocity v,K) =
      (1-dot (coneDirection x y) (velocity v)) • cross (coneDirection x y)
        (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v K)) +
      ((coneRadius x y)^2)⁻¹ • cross (coneDirection x y) (velocity v) := by
  have hn : DifferentiableAt ℝ (fun z : Phase => coneDirection x z.1) (y,v) :=
    (differentiableAt_coneDirection hxy).comp (f:=Prod.fst) (y,v) differentiableAt_fst
  have he : fderiv ℝ (fun z : Phase => coneDirection x z.1) (y,v) (velocity v,K) =
      (coneRadius x y)⁻¹ • (dot (coneDirection x y) (velocity v) • coneDirection x y-velocity v) := by
    have hfst : HasFDerivAt (Prod.fst : Phase → Vec) (ContinuousLinearMap.fst ℝ Vec Vec) (y,v) :=
      hasFDerivAt_fst
    have hd := (differentiableAt_coneDirection hxy).hasFDerivAt.comp (y,v) hfst
    have hh : fderiv ℝ (fun z : Phase => coneDirection x z.1) (y,v) (velocity v,K) =
        fderiv ℝ (coneDirection x) y (velocity v) := by
      convert congrArg (fun L : Phase →L[ℝ] Vec => L (velocity v,K)) hd.fderiv using 1 <;> rfl
    rw [hh,fderiv_coneDirection_apply hxy]
  change fderiv ℝ (fun z : Phase => cross (coneDirection x z.1) (retardedG x z)) (y,v) _ = _
  rw [fderiv_cross_apply hn (differentiableAt_retardedG hxy),he,
    fderiv_retardedG hxy]
  have hc := eulerian_cross_direction
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
    (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'
  change cross _ (eulerianG _ _ _)+_=_
  change cross _ (eulerianG (coneRadius x y) (coneDirection x y) (velocity v))+_=_
  change cross ((coneRadius x y)⁻¹ • _) (eulerianG (coneRadius x y) _ _) = _ at hc
  rw [hc]
  ext i
  fin_cases i <;> dsimp [cross,coneRadius] <;> ring

lemma retardedH_deficit_component {x y v : Vec} (hxy : x≠y) (i : Fin 3) :
    (1-dot (coneDirection x y) (velocity v))*retardedH x (y,v) i =
      -(cross (coneDirection x y) (velocity v)) i/coneRadius x y := by
  have hr : coneRadius x y≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hd := (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne'
  fin_cases i <;> dsimp [retardedH,retardedG,eulerianG,cross] <;> field_simp <;> ring

lemma retarded_magnetic_density_identity {f : Particle} {x y v E B : Vec} {t : ℝ}
    (hf : DifferentiableAt ℝ f (t-coneRadius x y,y,v)) (hxy : x≠y)
    (heq : fderiv ℝ f (t-coneRadius x y,y,v)
      (1,velocity v,E+cross (velocity v) B)=0) (i : Fin 3) :
    -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0) =
      f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        cross (coneDirection x y)
          (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
            (fderiv ℝ velocity v (E+cross (velocity v) B))) i -
      divergence (fun z => (retardedDensity f t x (z,v)*retardedH x (z,v) i) • velocity v) y -
      divergence (fun w => (retardedDensity f t x (y,w)*retardedH x (y,w) i) •
        (E+cross (velocity w) B)) v := by
  have hR := differentiableAt_retardedDensity hf hxy
  have hH := differentiableAt_retardedH (v:=v) hxy
  have hHi : DifferentiableAt ℝ (fun z : Phase => retardedH x z i) (y,v) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (y,v) hH
  have hK := (contDiff_lorentz (k:=1) E B).differentiable (by simp) v
  have hdiv := phase_divergence_transport (u:=velocity v) (hR.mul hHi) hK
  rw [divergence_lorentz,mul_zero,add_zero,fderiv_mul hR hHi] at hdiv
  simp only [add_apply,smul_apply,smul_eq_mul] at hdiv
  rw [fderiv_vec_component_at hH i,fderiv_retardedH hxy] at hdiv
  have htr : fderiv ℝ (retardedDensity f t x) (y,v) (velocity v,E+cross (velocity v) B) =
      -(1-dot (coneDirection x y) (velocity v))*fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0) :=
    retarded_transport_identity hf hxy heq
  rw [htr] at hdiv
  simp only [retardedDensity,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at hdiv
  have hhd := retardedH_deficit_component (v:=v) hxy i
  linear_combination hdiv - (fderiv ℝ f (t-coneRadius x y,y,v) (1,0,0))*hhd

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

lemma contDiff_eulerianG_velocity {k : ℕ∞ω} {r : ℝ} {n : Vec}
    (hr : r≠0) (hn : ‖n‖=1) :
    ContDiff ℝ k (fun v => eulerianG r n (velocity v)) := by
  have hd : ContDiff ℝ k (fun v => 1-dot n (velocity v)) :=
    contDiff_const.sub (contDiff_dot_pair.comp (contDiff_const.prodMk contDiff_velocity))
  exact ((contDiff_const.mul hd).inv (fun v => mul_ne_zero hr (cone_denom_pos v n hn).ne')).smul
    (contDiff_const.sub contDiff_velocity)

lemma contDiff_retardedG_velocity {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiff ℝ k (fun v => retardedG x (y,v)) := by
  change ContDiff ℝ k (fun v => eulerianG (coneRadius x y) (coneDirection x y) (velocity v))
  have hr : coneRadius x y≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  exact contDiff_eulerianG_velocity hr (coneDirection_norm hxy)

lemma contDiff_particle_velocity_profile {s : Solution} {t : ℝ} (ht : 0≤t) (x : Vec)
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) :
    ContDiff ℝ 1 (fun v => s.f (t,x,v)) := by
  apply contDiffOn_univ.mp
  exact hf.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
    (fun _ _ => ht)

lemma compactSupport_particle_velocity_profile {s : Solution} {t : ℝ} (ht : 0≤t) (x : Vec)
    (hc : CompactOnFiniteHorizons s) :
    HasCompactSupport (fun v => s.f (t,x,v)) := by
  obtain ⟨K,hK,hz⟩ := hc t ht
  apply compactSupport_of_zero_off (hK.image continuous_snd)
  intro v hv
  by_contra hne
  exact hv ⟨(x,v),hz t ⟨ht,le_rfl⟩ (subset_tsupport _ hne),rfl⟩

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

lemma contDiffAt_retardedG {k : ℕ∞ω} {x y v : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (retardedG x) (y,v) := by
  have hr : ContDiffAt ℝ k (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hn : ContDiffAt ℝ k (fun z : Phase => coneDirection x z.1) (y,v) :=
    (contDiffAt_coneDirection (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hu : ContDiffAt ℝ k (fun z : Phase => velocity z.2) (y,v) :=
    contDiff_velocity.contDiffAt.comp (y,v) contDiffAt_snd
  have hd : ContDiffAt ℝ k (fun z : Phase => 1-dot (coneDirection x z.1) (velocity z.2)) (y,v) :=
    contDiffAt_const.sub (contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk hu))
  exact ((hr.mul hd).inv (mul_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
    (cone_denom_pos v (coneDirection x y) (coneDirection_norm hxy)).ne')).smul (hn.sub hu)

lemma contDiffAt_retardedH {k : ℕ∞ω} {x y v : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (retardedH x) (y,v) :=
  contDiff_cross.contDiffAt.comp (y,v)
    (((contDiffAt_coneDirection (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst).prodMk
      (contDiffAt_retardedG hxy))

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

lemma classical_retarded_flux_calculus {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0<t-coneRadius x y)
    {G : Phase → ℝ}
    (hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v, ContDiffAt ℝ 1 G (z,v)) :
    Integrable (fun v : Vec => divergence
      (fun z => (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y) ∧
    divergence (fun z => ∫ v : Vec, (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y =
      ∫ v : Vec, divergence (fun z => (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y := by
  have ht0 : 0≤t := by have hr := norm_nonneg (x-y); change 0<t-‖x-y‖ at ht; linarith
  obtain ⟨K,hK,hF,hz⟩ := retarded_local_data hf hc ht0 x
  have hG' : ContDiffOn ℝ 1 G (retardedSpaceDomain t x ×ˢ univ) :=
    fun z hz => (hG z.1 hz.1 z.2).contDiffWithinAt
  have hcF : ContDiffOn ℝ 1
      (fun z : Phase => (retardedDensity s.f t x z*G z) • velocity z.2)
      (retardedSpaceDomain t x ×ˢ univ) :=
    (hF.mul hG').smul ((contDiff_velocity.comp contDiff_snd).contDiffOn)
  have hzero : ∀ z ∈ retardedSpaceDomain t x, ∀ v ∉ K,
      (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v=0 := by
    intro z hz' v hv
    rw [hz z hz' v hv,zero_mul,zero_smul]
  have hU := isOpen_retardedSpaceDomain t x
  have hy : y ∈ retardedSpaceDomain t x := ⟨hxy,ht⟩
  have hi := integrable_spatial_divergence_uniform_support
    (F := fun z : Phase => (retardedDensity s.f t x z*G z) • velocity z.2)
    hU hK hy hcF hzero
  have he := divergence_integral_uniform_support
    (F := fun z : Phase => (retardedDensity s.f t x z*G z) • velocity z.2)
    hU hK hy hcF hzero
  exact ⟨hi,he⟩

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

lemma classical_retarded_integral_identity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0<t-coneRadius x y)
    {G : Phase → ℝ} {C L : Vec → ℝ}
    (hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v, ContDiffAt ℝ 1 G (z,v))
    (hC : Continuous C)
    (heq : ∀ v, L v = retardedDensity s.f t x (y,v)*C v -
      divergence (fun z => (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y -
      divergence (fun w => (retardedDensity s.f t x (y,w)*G (y,w)) •
        (s.E (t-coneRadius x y,y)+cross (velocity w) (s.B (t-coneRadius x y,y)))) v) :
    (∫ v : Vec, L v) = (∫ v : Vec, retardedDensity s.f t x (y,v)*C v) -
      divergence (fun z => ∫ v : Vec, (retardedDensity s.f t x (z,v)*G (z,v)) • velocity v) y := by
  have hfp := contDiff_particle_velocity_profile ht.le y hf
  have hfcp := compactSupport_particle_velocity_profile ht.le y hc
  have hGp : ContDiff ℝ 1 (fun v => G (y,v)) := by
    rw [contDiff_iff_contDiffAt]
    intro v
    exact (hG y ⟨hxy,ht⟩ v).comp (f:=fun w : Vec => (y,w)) v
      (contDiffAt_const.prodMk contDiffAt_id)
  have hcv : Integrable (fun v : Vec => retardedDensity s.f t x (y,v)*C v) :=
    (hfp.continuous.mul hC).integrable_of_hasCompactSupport hfcp.mul_right
  obtain ⟨hsi,hse⟩ := classical_retarded_flux_calculus hf hc hxy ht hG
  have hvg : ContDiff ℝ 1 (fun w => (retardedDensity s.f t x (y,w)*G (y,w)) •
      (s.E (t-coneRadius x y,y)+cross (velocity w) (s.B (t-coneRadius x y,y)))) :=
    (hfp.mul hGp).smul (contDiff_lorentz _ _)
  have hvcp : HasCompactSupport (fun w => (retardedDensity s.f t x (y,w)*G (y,w)) •
      (s.E (t-coneRadius x y,y)+cross (velocity w) (s.B (t-coneRadius x y,y)))) :=
    hfcp.mul_right.smul_right
  have hsub := integral_sub (hcv.sub hsi) (integrable_divergence_compact hvg hvcp)
  have hsub' := integral_sub hcv hsi
  simp only [Pi.sub_apply] at hsub hsub'
  simp_rw [heq]
  rw [hsub,hsub',integral_divergence_zero hvg hvcp,sub_zero,hse]

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

lemma divergence_add_right {F : Vec → Vec} (x z : Vec) :
    divergence (fun y => F (x+y)) z=divergence F (x+z) := by
  unfold divergence spatialPartial
  congr 1
  funext i
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i)) (fderiv_comp_add_left (f:=fun y => F y i) (x:=z) x)

lemma coneRadius_add (x z : Vec) : coneRadius x (x+z)=‖z‖ := by
  unfold coneRadius
  rw [show x-(x+z) = -z by abel,norm_neg]

lemma retarded_flux_norm_bound {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, 0<‖z‖ → ‖z‖≤R →
      ‖∫ v : Vec, (retardedDensity s.f t x (x+z,v)*retardedG x (x+z,v) i) • velocity v‖≤C/‖z‖ := by
  have ht : 0≤t := le_trans hR hRt.le
  obtain ⟨K,hK,hz⟩ := hc t ht
  let K' : Set Vec := Prod.snd '' K
  have hK' : IsCompact K' := hK.image continuous_snd
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  have hP : IsCompact P := (isCompact_closedBall (0:Vec) R).prod (isCompact_sphere (0:Vec) 1)
  let F : (Vec × Vec) × Vec → Vec := fun p =>
    (s.f (t-‖p.1.1‖,x+p.1.1,p.2)*(1-dot p.1.2 (velocity p.2))⁻¹*
      (p.1.2 i-velocity p.2 i)) • velocity p.2
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1,p.2)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk
      ((continuous_const.add continuous_fst.fst).prodMk continuous_snd)
  have htime (z : Vec) (hz' : z ∈ closedBall (0:Vec) R) : t-‖z‖ ∈ Icc 0 t := by
    have hn : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz'
    exact ⟨by linarith,sub_le_self _ (norm_nonneg _)⟩
  have hcf : ContinuousOn (fun p : (Vec × Vec) × Vec => s.f (t-‖p.1.1‖,x+p.1.1,p.2)) (P ×ˢ univ) :=
    hf.continuousOn.comp harg.continuousOn (fun p hp => (htime p.1.1 hp.1.1).1)
  have hu : Continuous (fun p : (Vec × Vec) × Vec => velocity p.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hd : Continuous (fun p : (Vec × Vec) × Vec => 1-dot p.1.2 (velocity p.2)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_fst.snd.prodMk hu))
  have hd0 (p : (Vec × Vec) × Vec) (hp : p ∈ P ×ˢ univ) : 1-dot p.1.2 (velocity p.2)≠0 := by
    apply (cone_denom_pos _ _ ?_).ne'
    simpa only [mem_sphere,dist_zero_right] using hp.1.2
  have hcn : Continuous (fun p : (Vec × Vec) × Vec => p.1.2 i-velocity p.2 i) :=
    ((PiLp.continuous_apply 2 _ i).comp continuous_fst.snd).sub
      ((PiLp.continuous_apply 2 _ i).comp hu)
  have hF : ContinuousOn F (P ×ˢ univ) :=
    ((hcf.mul (hd.continuousOn.inv₀ hd0)).mul hcn.continuousOn).smul hu.continuousOn
  have hzero : ∀ p ∈ P, ∀ v ∉ K', F (p,v)=0 := by
    intro p hp v hv
    have hsf : s.f (t-‖p.1‖,x+p.1,v)=0 := by
      by_contra hne
      exact hv ⟨(x+p.1,v),hz _ (htime p.1 hp.1) (subset_tsupport _ hne),rfl⟩
    simp only [F,hsf,zero_mul,zero_smul]
  obtain ⟨C,hC,hbound⟩ := uniform_integral_bound_compact hP hK' hF hzero
  refine ⟨C,hC,?_⟩
  intro z hz0 hzR
  have hxy : x≠x+z := by
    intro h
    apply (norm_pos_iff.mp hz0)
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  let n := coneDirection x (x+z)
  have hn : ‖n‖=1 := coneDirection_norm hxy
  have hp : (z,n) ∈ P := ⟨by simpa only [mem_closedBall_zero_iff] using hzR,
    by simpa only [mem_sphere,dist_zero_right] using hn⟩
  have he : (∫ v : Vec, (retardedDensity s.f t x (x+z,v)*retardedG x (x+z,v) i) • velocity v) =
      ‖z‖⁻¹ • ∫ v : Vec, F ((z,n),v) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with v
    simp only [retardedDensity,retardedG,eulerianG,coneRadius_add,PiLp.smul_apply,smul_eq_mul,
      mul_inv_rev,PiLp.sub_apply,F,smul_smul]
    congr 1
    ring
  rw [he,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hz0.le)]
  calc
    ‖z‖⁻¹*‖∫ v : Vec, F ((z,n),v)‖ ≤ ‖z‖⁻¹*C :=
      mul_le_mul_of_nonneg_left (hbound (z,n) hp) (inv_nonneg.mpr hz0.le)
    _ = C/‖z‖ := by ring

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
lemma retarded_weighted_integral_bound {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec)
    {A : (Vec × Vec) × Vec → W}
    (hA : ContinuousOn A ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, ‖z‖≤R → ∀ n : Vec, ‖n‖=1 →
      ‖∫ v : Vec, s.f (t-‖z‖,x+z,v) • A ((z,n),v)‖≤C := by
  have ht : 0≤t := le_trans hR hRt.le
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

lemma retarded_electric_kernel_norm_bound {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec) :
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
  obtain ⟨C,hC,hbound⟩ := retarded_weighted_integral_bound hf hc hR hRt x (hD.continuousOn.smul hN)
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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CrossCLM
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

lemma cross_apply_cyclic (n v : Vec) (i : Fin 3) :
    cross n v i=n (curlA i)*v (curlB i)-n (curlB i)*v (curlA i) := by
  fin_cases i <;> simp [cross,curlA,curlB]

lemma crossCLM_apply (n v : Vec) : crossCLM n v=cross n v := rfl

lemma integral_cross_left {F : Vec → Vec} (hF : Integrable F) (n : Vec) :
    (∫ v : Vec, cross n (F v))=cross n (∫ v : Vec, F v) :=
  (crossCLM n).integral_comp_comm hF

lemma integrable_retardedElectricDensity_integrand {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) :
    Integrable (fun v : Vec =>
      (s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))) •
        physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))))) := by
  obtain ⟨hreg,hcomp⟩ := (show RegularParticle s.f from ⟨hf,hc⟩).slice ht y
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp
      (continuous_const.prodMk (contDiff_velocity (k:=1)).continuous))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  exact ((hreg.continuous.mul hd).smul hk).integrable_of_hasCompactSupport (hcomp.mul_right.smul_right)

lemma retardedMagneticDensity_component {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    retardedMagneticDensity s t x y i =
    ∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
      cross (coneDirection x y) (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y))))) i := by
  have hi := integrable_retardedElectricDensity_integrand hf hc hxy ht
  have hcross := (crossCLM (coneDirection x y)).integrable_comp hi
  unfold retardedMagneticDensity retardedElectricDensity
  rw [← integral_cross_left hi]
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hcross
  simpa only [crossCLM_apply,PiLp.proj_apply,cross_smul_right,PiLp.smul_apply,smul_eq_mul] using he.symm

lemma integrable_retarded_flux_integrand {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    Integrable (fun v : Vec => (retardedDensity s.f t x (y,v)*retardedG x (y,v) i) • velocity v) := by
  obtain ⟨hreg,hcomp⟩ := (show RegularParticle s.f from ⟨hf,hc⟩).slice ht y
  have hG : Continuous (fun v : Vec => retardedG x (y,v) i) :=
    (PiLp.continuous_apply 2 _ i).comp (contDiff_retardedG_velocity (k:=1) hxy).continuous
  exact ((hreg.continuous.mul hG).smul (contDiff_velocity (k:=1)).continuous).integrable_of_hasCompactSupport
    (hcomp.mul_right.smul_right)

lemma retardedMagneticFlux_components {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {x y : Vec} {t : ℝ} (hxy : x≠y) (ht : 0≤t-coneRadius x y) (i : Fin 3) :
    retardedMagneticFlux s t x i y =
      coneDirection x y (curlA i) • retardedElectricFlux s t x (curlB i) y -
      coneDirection x y (curlB i) • retardedElectricFlux s t x (curlA i) y := by
  have hA : Integrable (fun v : Vec => coneDirection x y (curlA i) •
      ((retardedDensity s.f t x (y,v)*retardedG x (y,v) (curlB i)) • velocity v)) :=
    (integrable_retarded_flux_integrand hf hc hxy ht (curlB i)).fun_smul (coneDirection x y (curlA i))
  have hB : Integrable (fun v : Vec => coneDirection x y (curlB i) •
      ((retardedDensity s.f t x (y,v)*retardedG x (y,v) (curlA i)) • velocity v)) :=
    (integrable_retarded_flux_integrand hf hc hxy ht (curlA i)).fun_smul (coneDirection x y (curlB i))
  unfold retardedMagneticFlux retardedElectricFlux
  rw [← integral_smul,← integral_smul,← integral_sub hA hB]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [retardedH,cross_apply_cyclic]
  simp only [smul_smul,← sub_smul]
  congr 1
  ring

lemma contDiffOn_retardedMagnetic_flux {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} (ht : 0≤t) (x : Vec) (i : Fin 3) :
    ContDiffOn ℝ 1 (retardedMagneticFlux s t x i) (retardedSpaceDomain t x) := by
  obtain ⟨K,hK,hF,hz⟩ := retarded_local_data hf hc ht x
  have hG : ContDiffOn ℝ 1 (fun z => retardedH x z i) (retardedSpaceDomain t x ×ˢ univ) := by
    intro z hz
    exact ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp z
      (contDiffAt_retardedH hz.1.1)).contDiffWithinAt
  apply contDiffOn_integral_uniform_support (isOpen_retardedSpaceDomain t x) hK
    ((hF.mul hG).smul (contDiff_velocity.comp contDiff_snd).contDiffOn)
  intro y hy v hv
  change (retardedDensity s.f t x (y,v)*retardedH x (y,v) i) • velocity v=0
  rw [hz y hy v hv,zero_mul,zero_smul]

lemma retarded_magnetic_flux_norm_bound {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec) (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, 0<‖z‖ → ‖z‖≤R →
      ‖retardedMagneticFlux s t x i (x+z)‖≤C/‖z‖ := by
  obtain ⟨CA,hCA,hA⟩ := retarded_flux_norm_bound hf hc hR hRt x (curlA i)
  obtain ⟨CB,hCB,hB⟩ := retarded_flux_norm_bound hf hc hR hRt x (curlB i)
  refine ⟨CA+CB,add_nonneg hCA hCB,?_⟩
  intro z hz hzR
  have hxy : x≠x+z := by
    intro h
    apply (norm_pos_iff.mp hz)
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have ht : 0≤t-coneRadius x (x+z) := by rw [coneRadius_add]; linarith
  have hn (j : Fin 3) : ‖coneDirection x (x+z) j‖≤1 :=
    (PiLp.norm_apply_le _ j).trans_eq (coneDirection_norm hxy)
  rw [retardedMagneticFlux_components hf hc hxy ht i]
  calc
    _ ≤ ‖coneDirection x (x+z) (curlA i) • retardedElectricFlux s t x (curlB i) (x+z)‖ +
        ‖coneDirection x (x+z) (curlB i) • retardedElectricFlux s t x (curlA i) (x+z)‖ := norm_sub_le _ _
    _ ≤ CB/‖z‖+CA/‖z‖ := by
      apply add_le_add
      · rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hn _)).trans (hB z hz hzR)
      · rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hn _)).trans (hA z hz hzR)
    _ = (CA+CB)/‖z‖ := by ring

lemma retarded_magnetic_flux_tip {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    Tendsto (fun ε : ℝ => ∫ n : Sphere, ε^2*dot n.1
      (retardedMagneticFlux s t x i (x+ε • n.1)) ∂sphereMeasure)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C,_,hbound⟩ := retarded_magnetic_flux_norm_bound hf hc (show 0≤t/2 by linarith)
    (show t/2<t by linarith) x i
  apply spherical_flux_tendsto_zero (C:=C) (R:=t/2)
    (F:=fun z => retardedMagneticFlux s t x i (x+z)) (show 0<t/2 by linarith)
  intro z hz hzR
  exact hbound z hz hzR.le
end RVM

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

lemma RegularParticle.time_moment_derivative {f : Particle} (hf : RegularParticle f)
    {w : Vec → ℝ} (hw : ContDiff ℝ 1 w) {t : ℝ} (ht : 0<t) (x : Vec) :
    dirD (fun p : ℝ × Vec => ∫ v : Vec, w v*f (p.1,p.2,v)) (1,0) (t,x) =
      ∫ v : Vec, w v*fderiv ℝ f (t,x,v) (1,0,0) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ := hf.local_data ht x
  change fderiv ℝ (fun p => ∫ v : Vec, w v*particleBySpacetime f (p,v)) (t,x) (1,0)=_
  rw [fderiv_weighted_integral_uniform_support_apply hU hK hp hF hw hzero]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [fderiv_particleBySpacetime (particle_differentiableAt_positive (s:=⟨f,0,0⟩) hf.1 ht x v)]

lemma RegularParticle.time_moment_integrable {f : Particle} (hf : RegularParticle f)
    {w : Vec → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0<t) (x : Vec) :
    Integrable (fun v : Vec => w v*fderiv ℝ f (t,x,v) (1,0,0)) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ := hf.local_data ht x
  have hi := integrable_param_fderiv_apply_weight hU hK hp hF hw hzero (((1:ℝ),(0:Vec)),(0:Vec))
  simpa only [fderiv_particleBySpacetime (particle_differentiableAt_positive (s:=⟨f,0,0⟩) hf.1 ht x _)] using hi

lemma RegularParticle.scalar_moment_integrable {f : Particle} (hf : RegularParticle f)
    {w : Vec → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0≤t) (x : Vec) :
    Integrable (fun v : Vec => w v*f (t,x,v)) := by
  simpa only [smul_eq_mul,mul_comm] using hf.moment_integrable hw ht x

lemma current_eq_integral_component {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0≤t) (x : Vec) (i : Fin 3) :
    current (fun z => f (t,z)) x i = ∫ v : Vec, velocity v i*f (t,x,v) := by
  have hi := hf.moment_integrable (contDiff_velocity (k:=1)).continuous ht x
  have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi
  simpa only [current,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul,mul_comm] using he.symm

lemma dirD_current_component {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    dirD (fun p : ℝ × Vec => current (fun z => f (p.1,z)) p.2 i) (1,0) (t,x) =
      ∫ v : Vec, velocity v i*fderiv ℝ f (t,x,v) (1,0,0) := by
  have he : (fun p : ℝ × Vec => current (fun z => f (p.1,z)) p.2 i) =ᶠ[𝓝 (t,x)]
      (fun p : ℝ × Vec => ∫ v : Vec, velocity v i*f (p.1,p.2,v)) := by
    filter_upwards [((isOpen_lt continuous_const (continuous_fst : Continuous (Prod.fst : ℝ × Vec → ℝ))).mem_nhds ht)] with p hp
    exact current_eq_integral_component hf hp.le p.2 i
  unfold dirD
  rw [he.fderiv_eq]
  exact hf.time_moment_derivative ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp contDiff_velocity) ht x

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

lemma integrableOn_retardedMagneticDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R<t) (x : Vec) :
    IntegrableOn (fun z => retardedMagneticDensity s t x (x+z)) (ball (0:Vec) R) := by
  have ht : 0≤t := le_trans hR hRt.le
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
  obtain ⟨C,_,hbound⟩ := retarded_electric_kernel_norm_bound hf hE.continuousOn hB.continuousOn hc hR hRt x
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=C) (by norm_num) hcont
  intro z hz hzR
  have hxy : x≠x+z := (hm ⟨by simpa only [mem_ball_zero_iff] using hzR,by simpa only [mem_singleton_iff] using norm_pos_iff.mp hz⟩).1
  calc
    ‖retardedMagneticDensity s t x (x+z)‖ ≤ ‖coneDirection x (x+z)‖*‖retardedElectricDensity s t x (x+z)‖ := norm_cross_le _ _
    _ = ‖retardedElectricDensity s t x (x+z)‖ := by rw [coneDirection_norm hxy,one_mul]
    _ ≤ C/‖z‖^2 := hbound z hz hzR.le
    _ = C*‖z‖^(-(2:ℝ)) := by rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two]; rfl

lemma integrableOn_magneticMomentDensity {j : Field} (hj : ContDiff ℝ ∞ j)
    (t : ℝ) (x : Vec) (i : Fin 3) :
    IntegrableOn (magneticMomentDensity j t x i) (ball (0:Vec) t) := by
  have harg : Continuous (fun z : Vec => (t-‖z‖,x+z)) :=
    (continuous_const.sub continuous_norm).prodMk (continuous_const.add continuous_id)
  have hi (a b : Fin 3) : IntegrableOn (fun z : Vec =>
      z a/‖z‖^2*dirD (fun p => j p b) (1,0) (t-‖z‖,x+z) +
      z a/‖z‖^3*j (t-‖z‖,x+z) b) (ball (0:Vec) t) :=
    Integrable.add (integrableOn_ball_direction_div_norm_pow
      ((contDiff_dirD (contDiff_component hj b) _).continuous.comp harg) 1 (by norm_num) t a)
      (integrableOn_ball_direction_div_norm_pow
        ((contDiff_component hj b).continuous.comp harg) 2 (by norm_num) t a)
  exact (hi _ _).sub (hi _ _)

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

lemma classical_retarded_magnetic_integral_identity_before {s : Solution} {H : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : EquationsBefore s H) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (hth : t < H) (i : Fin 3) :
    (∫ v : Vec, -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) =
      (∫ v : Vec, s.f (t-coneRadius x y,y,v)*(1-dot (coneDirection x y) (velocity v))*
        cross (coneDirection x y) (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
            cross (velocity v) (s.B (t-coneRadius x y,y))))) i) -
      divergence (fun z => ∫ v : Vec,
        (retardedDensity s.f t x (z,v)*retardedH x (z,v) i) • velocity v) y := by
  have hG : ∀ z ∈ retardedSpaceDomain t x, ∀ v,
      ContDiffAt ℝ 1 (fun z => retardedH x z i) (z,v) := by
    intro z hz v
    exact (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.contDiffAt.comp (z,v)
      (contDiffAt_retardedH hz.1)
  have hu : Continuous velocity := (contDiff_velocity (k:=1)).continuous
  have hd : Continuous (fun v => 1-dot (coneDirection x y) (velocity v)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_const.prodMk hu))
  have hk := continuous_physicalElectricKernel_velocity
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) (coneDirection_norm hxy)
    (s.E (t-coneRadius x y,y)) (s.B (t-coneRadius x y,y))
  have hkc : Continuous (fun v => cross (coneDirection x y)
      (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
          cross (velocity v) (s.B (t-coneRadius x y,y)))))) :=
    (contDiff_cross (k:=1)).continuous.comp (continuous_const.prodMk hk)
  have hki : Continuous (fun v => cross (coneDirection x y)
      (physicalElectricKernel (coneRadius x y) (coneDirection x y) (velocity v)
        (fderiv ℝ velocity v (s.E (t-coneRadius x y,y)+
          cross (velocity v) (s.B (t-coneRadius x y,y))))) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).continuous.comp hkc
  have hid := classical_retarded_integral_identity
    (L := fun v => -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) -
      cross (coneDirection x y) (velocity v) i/coneRadius x y *
        fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) hf hc hxy ht hG (hd.mul hki)
  simp only [retardedDensity,mul_assoc,Pi.mul_apply] at hid ⊢
  apply hid
  intro v
  have hf' := particle_differentiableAt_positive hf ht y v
  have hv : fderiv ℝ s.f (t-coneRadius x y,y,v)
      (1,velocity v,s.E (t-coneRadius x y,y)+cross (velocity v) (s.B (t-coneRadius x y,y)))=0 := by
    simpa only [fderiv_particleBySpacetime hf'] using particle_spacetime_vlasov_before hf heq ht
      ((sub_le_self t (norm_nonneg (x-y))).trans_lt hth) y v
  simpa only [retardedDensity,mul_assoc] using retarded_magnetic_density_identity hf' hxy hv i

lemma classical_retarded_magnetic_moment_identity_before {s : Solution} {H : ℝ}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (hc : CompactOnFiniteHorizons s)
    (heq : EquationsBefore s H) {x y : Vec} {t : ℝ}
    (hxy : x≠y) (ht : 0<t-coneRadius x y) (hth : t < H) (i : Fin 3) :
    -((coneRadius x y)^2)⁻¹*cross (coneDirection x y) (current (fun z => s.f (t-coneRadius x y,z)) y) i -
      (coneRadius x y)⁻¹*(coneDirection x y (curlA i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlB i)) (1,0) (t-coneRadius x y,y) -
        coneDirection x y (curlB i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlA i)) (1,0) (t-coneRadius x y,y)) =
      retardedMagneticDensity s t x y i - divergence (retardedMagneticFlux s t x i) y := by
  have hr : RegularParticle s.f := ⟨hf,hc⟩
  have hcv : ContDiff ℝ 1 (fun v : Vec => cross (coneDirection x y) (velocity v) i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp
      (contDiff_cross.comp (contDiff_const.prodMk contDiff_velocity))
  have hi := hr.moment_integrable (contDiff_velocity (k:=1)).continuous ht.le y
  have hcross : cross (coneDirection x y) (current (fun z => s.f (t-coneRadius x y,z)) y) i =
      ∫ v : Vec, cross (coneDirection x y) (velocity v) i*s.f (t-coneRadius x y,y,v) := by
    have hi' := (crossCLM (coneDirection x y)).integrable_comp hi
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi'
    unfold current
    rw [← integral_cross_left hi]
    simpa only [crossCLM_apply,PiLp.proj_apply,cross_smul_right,PiLp.smul_apply,smul_eq_mul,mul_comm] using he.symm
  have hdt : coneDirection x y (curlA i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlB i)) (1,0) (t-coneRadius x y,y) -
        coneDirection x y (curlB i)*
        dirD (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2 (curlA i)) (1,0) (t-coneRadius x y,y) =
      ∫ v : Vec, cross (coneDirection x y) (velocity v) i*fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0) := by
    have hInt (k : Fin 3) : Integrable (fun v : Vec => velocity v k*fderiv ℝ s.f (t-coneRadius x y,y,v) (1,0,0)) := hr.time_moment_integrable
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) k).continuous.comp (contDiff_velocity (k:=1)).continuous) ht y
    rw [dirD_current_component hr ht y,dirD_current_component hr ht y,
      ← integral_const_mul,← integral_const_mul,← integral_sub ((hInt _).const_mul _) ((hInt _).const_mul _)]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [cross_apply_cyclic]
    ring
  rw [hcross,hdt,retardedMagneticDensity_component hf hc hxy ht.le i,
    ← integral_const_mul,← integral_const_mul,
    ← integral_sub ((hr.scalar_moment_integrable hcv.continuous ht.le y).const_mul _)
      ((hr.time_moment_integrable hcv.continuous ht y).const_mul _)]
  unfold retardedMagneticFlux
  convert classical_retarded_magnetic_integral_identity_before hf hc heq hxy ht hth i using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext v
  dsimp only
  ring

lemma contDiff_shifted_moments_before {d : Datum} {s : Solution} {H : ℝ} (hs : ClassicalBefore d s H)
    (hm : SmoothOnFiniteHorizons s) {a : ℝ} (ha : 0<a) :
    ContDiff ℝ ∞ (shiftedRho s a) ∧ ContDiff ℝ ∞ (shiftedCurrent s a) :=
  ⟨contDiff_positiveTimeShift ha (fun _p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).1),
   contDiff_positiveTimeShift ha (fun _p hp => (hm.moments_positive hs.2.2.2.2.2.2.1 hp).2)⟩

lemma magneticMomentDensity_actual_before {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ} (ha : 0<a) (hH : a+T < H)
    (x : Vec) (i : Fin 3) {z : Vec} (hz : z≠0) (hzt : ‖z‖<T) :
    magneticMomentDensity (shiftedCurrent s a) T x i z =
      retardedMagneticDensity s (a+T) x (x+z) i -
      divergence (retardedMagneticFlux s (a+T) x i) (x+z) := by
  have hc := hs.2.2.2.2.2.2.1
  have hxy : x≠x+z := by
    intro h
    apply hz
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have ht : 0<a+T-coneRadius x (x+z) := by rw [coneRadius_add]; linarith
  have hp : 0<a+(T-‖z‖) := by linarith
  have hj := (hm.moments_positive hc (p:=(a+(T-‖z‖),x+z)) hp).2
  have hji (k : Fin 3) : DifferentiableAt ℝ
      (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 k) (a+(T-‖z‖),x+z) :=
    ((PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) k).contDiff.contDiffAt.comp _ hj).differentiableAt (by simp)
  have herr (k : Fin 3) : (fun p => shiftedCurrent s a p k)=
      positiveTimeShift a (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 k) := by
    funext p
    simp only [shiftedCurrent,positiveTimeShift,positiveTimeExtend,PiLp.smul_apply,smul_eq_mul]
  have hjder (k : Fin 3) : dirD (fun p => shiftedCurrent s a p k) (1,0) (T-‖z‖,x+z) =
      dirD (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2 k) (1,0) (a+(T-‖z‖),x+z) := by
    rw [herr]
    unfold dirD
    rw [fderiv_positiveTimeShift ha (sub_nonneg.mpr hzt.le) _ (hji k)]
  have hjval : shiftedCurrent s a (T-‖z‖,x+z)=current (fun q => s.f (a+(T-‖z‖),q)) (x+z) :=
    positiveTimeShift_eq ha (sub_nonneg.mpr hzt.le) _ _
  unfold magneticMomentDensity
  rw [hjder,hjder,hjval]
  have he := classical_retarded_magnetic_moment_identity_before hs.1 hc hs.2.2.2.2.2.2.2.1 hxy ht hH i
  rw [← he,cross_apply_cyclic]
  simp only [coneRadius_add,coneDirection_add,PiLp.neg_apply,PiLp.smul_apply,smul_eq_mul,
    show a+T-‖z‖=a+(T-‖z‖) by ring]
  field_simp [norm_ne_zero_iff.mpr hz]
  ring

lemma integrated_magneticMomentDensity_actual_before_oai {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) (hm : SmoothOnFiniteHorizons s) {a T : ℝ}
    (ha : 0<a) (hT : 0<T) (hH : a+T < H) (x : Vec) (i : Fin 3) :
    (∫ z in ball (0:Vec) T, magneticMomentDensity (shiftedCurrent s a) T x i z) =
      (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      ∫ n : Sphere, T^2*dot n.1 (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure := by
  have hc := hs.2.2.2.2.2.2.1
  have hρj := contDiff_shifted_moments_before hs hm ha
  have hM := integrableOn_magneticMomentDensity hρj.2 T x i
  have hD : IntegrableOn (fun z : Vec => retardedMagneticDensity s (a+T) x (x+z) i) (ball (0:Vec) T) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integrable_comp
      (integrableOn_retardedMagneticDensity hs.1 hs.2.1 hs.2.2.1 hc hT.le (show T<a+T by linarith) x)
  let F : Vec → Vec := fun z => retardedMagneticFlux s (a+T) x i (x+z)
  have he : (fun z => divergence F z) =ᵐ[volume.restrict (ball (0:Vec) T)]
      (fun z => retardedMagneticDensity s (a+T) x (x+z) i -
        magneticMomentDensity (shiftedCurrent s a) T x i z) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
    have hh := magneticMomentDensity_actual_before hs hm ha hH x i hz0 (by simpa only [mem_ball_zero_iff] using hz)
    dsimp only [F]
    rw [divergence_add_right]
    linarith
  have hF : ∀ z : Vec, 0<‖z‖ → ‖z‖<a+T → ContDiffAt ℝ 1 F z := by
    intro z hz hzT
    have hxy : x≠x+z := by
      intro h
      apply (norm_pos_iff.mp hz)
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    have hp : x+z ∈ retardedSpaceDomain (a+T) x := ⟨hxy,by rw [coneRadius_add]; linarith⟩
    exact ((contDiffOn_retardedMagnetic_flux hs.1 hc (by linarith) x i).contDiffAt
      ((isOpen_retardedSpaceDomain (a+T) x).mem_nhds hp)).comp z
        (contDiffAt_const.add contDiffAt_id)
  have hi : IntegrableOn (divergence F) (ball (0:Vec) T) := (hD.sub hM).congr he.symm
  have hg := divergence_ball_singular hT (show T<a+T by linarith) hF hi
    (retarded_magnetic_flux_tip hs.1 hc (show 0<a+T by linarith) x i)
  have hh : (∫ z in ball (0:Vec) T, divergence F z) =
      (∫ z in ball (0:Vec) T, retardedMagneticDensity s (a+T) x (x+z) i) -
      (∫ z in ball (0:Vec) T, magneticMomentDensity (shiftedCurrent s a) T x i z) := by
    rw [integral_congr_ae he,integral_sub hD hM]
  change _ = ∫ n : Sphere, T^2*dot n.1 (retardedMagneticFlux s (a+T) x i (x+T • n.1)) ∂sphereMeasure at hg
  linarith

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.integrated_magneticMomentDensity_actual_before_oai := @OAI.RVM.integrated_magneticMomentDensity_actual_before_oai
