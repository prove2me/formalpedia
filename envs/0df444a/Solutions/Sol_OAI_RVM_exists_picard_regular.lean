-- Prove2me | solution 1 for OAI.RVM.exists_picard_regular
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:25:01.891968+00:00
-- url     : https://prove2.me/submissions/efb66f8a-5ca1-497b-a9ed-b930408c9576

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_constructed_maxwell_equations
import Theorems.Thm_OAI_RVM_exists_smoothLorentzFlow
import Theorems.Thm_OAI_RVM_maxwell_timeContinuousL2

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

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

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

lemma clm_spacetime_velocity_split (L : ((ℝ × Vec) × Vec) →L[ℝ] ℝ)
    (u K : Vec) :
    L ((1,u),K) = L ((1,0),0) +
      ∑ i : Fin 3, u i * L ((0,basis i),0) +
      ∑ i : Fin 3, K i * L ((0,0),basis i) := by
  let A : Vec →L[ℝ] ((ℝ × Vec) × Vec) :=
    ((0 : Vec →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec)).prod 0
  let B : Vec →L[ℝ] ((ℝ × Vec) × Vec) :=
    (0 : Vec →L[ℝ] (ℝ × Vec)).prod (ContinuousLinearMap.id ℝ Vec)
  have hu := clm_sum_basis (L.comp A) u
  have hK := clm_sum_basis (L.comp B) K
  change L ((0,u),0) = ∑ i : Fin 3, u i * L ((0,basis i),0) at hu
  change L ((0,0),K) = ∑ i : Fin 3, K i * L ((0,0),basis i) at hK
  rw [← hu, ← hK, ← map_add, ← map_add]
  congr 1
  ext <;> simp

lemma fderiv_velocity_slice {F : (ℝ × Vec) × Vec → ℝ} {p : ℝ × Vec} {v : Vec}
    (hF : DifferentiableAt ℝ F (p,v)) (b : Vec) :
    fderiv ℝ (fun w => F (p,w)) v b = fderiv ℝ F (p,v) ((0,0),b) := by
  have he := hF.hasFDerivAt.comp v
    ((hasFDerivAt_const p v).prodMk (hasFDerivAt_id v))
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L b) he.fderiv

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

lemma spatialPartial_time_slice {G : ℝ × Vec → ℝ} {t : ℝ} {x : Vec}
    (hG : DifferentiableAt ℝ G (t,x)) (i : Fin 3) :
    spatialPartial (fun y => G (t,y)) x i = fderiv ℝ G (t,x) (0,basis i) := by
  exact congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    (hG.hasFDerivAt.comp x ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))).fderiv

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

lemma integral_lorentz_derivative_zero {g : Vec → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (E B : Vec) :
    (∫ v : Vec, fderiv ℝ g v (E + cross (velocity v) B)) = 0 := by
  have h := integral_mul_divergence (contDiff_lorentz E B) hg hc
  simp only [divergence_lorentz,mul_zero,integral_zero] at h
  linarith

lemma particle_number_balance_param
    {U : Set (ℝ × Vec)} {K : Set Vec} {F : (ℝ × Vec) × Vec → ℝ}
    {p : ℝ × Vec} (E B : Vec)
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    fderiv ℝ (fun y => ∫ v : Vec, F (y,v)) p (1,0) +
      ∑ i : Fin 3, fderiv ℝ (fun y => ∫ v : Vec, velocity v i * F (y,v)) p (0,basis i) =
      ∫ v : Vec, fderiv ℝ F (p,v) ((1,velocity v), E + cross (velocity v) B) := by
  have hdiff (v : Vec) : DifferentiableAt ℝ F (p,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).differentiableAt (by simp)
  have hs : ContDiff ℝ 1 (fun v : Vec => F (p,v)) := by
    apply contDiffOn_univ.mp
    exact hF.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
      (fun v _ => ⟨hp,mem_univ v⟩)
  have hc : HasCompactSupport (fun v : Vec => F (p,v)) :=
    compactSupport_of_zero_off hK (hzero p hp)
  have hvel (i : Fin 3) : ContDiff ℝ 1 (fun v => velocity v i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp contDiff_velocity
  have hint : Integrable (fun v : Vec => fderiv ℝ F (p,v) ((1,0),0)) := by
    simpa only [one_mul] using integrable_param_fderiv_apply_weight hU hK hp hF
      (continuous_const (y := (1:ℝ))) hzero (((1:ℝ),(0:Vec)),(0:Vec))
  have hint' (i : Fin 3) := integrable_param_fderiv_apply_weight hU hK hp hF
    (hvel i).continuous hzero (((0:ℝ),basis i),(0:Vec))
  have hintK : Integrable (fun v : Vec => fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B)) := by
    have hd : Continuous (fun v : Vec => fderiv ℝ F (p,v)) :=
      (hF.continuousOn_fderiv_of_isOpen (hU.prod isOpen_univ) le_rfl).comp_continuous
        (continuous_const.prodMk continuous_id) (fun _ => ⟨hp,mem_univ _⟩)
    apply (hd.clm_apply (continuous_const.prodMk (contDiff_lorentz (k := 1) E B).continuous)).integrable_of_hasCompactSupport
    apply compactSupport_of_zero_off (compactSupport_param_fderiv hU hK hp hzero)
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport hv,zero_apply]
  have hK0 : (∫ v : Vec, fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B)) = 0 := by
    simpa only [fderiv_velocity_slice (hdiff _)] using integral_lorentz_derivative_zero hs hc E B
  have he (v : Vec) : fderiv ℝ F (p,v) ((1,velocity v),E + cross (velocity v) B) =
      fderiv ℝ F (p,v) ((1,0),0) +
        (∑ i : Fin 3, velocity v i * fderiv ℝ F (p,v) ((0,basis i),0)) +
        fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B) := by
    rw [clm_spacetime_velocity_split]
    congr 1
    symm
    have h := clm_spacetime_velocity_split (fderiv ℝ F (p,v)) (0:Vec) (E + cross (velocity v) B)
    have h' : fderiv ℝ F (p,v) ((1,0),E + cross (velocity v) B) =
        fderiv ℝ F (p,v) ((1,0),0) + fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B) := by
      rw [← map_add]; congr 1; ext <;> simp
    simp only [PiLp.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] at h
    linarith
  rw [fderiv_integral_uniform_support_apply hU hK hp hF hzero]
  simp_rw [fderiv_weighted_integral_uniform_support_apply hU hK hp hF (hvel _) hzero]
  rw [← integral_finsetSum _ (fun i _ => hint' i), ← integral_add hint
    (integrable_finsetSum Finset.univ (fun i _ => hint' i))]
  calc
    _ = (∫ v : Vec, fderiv ℝ F (p,v) ((1,0),0) +
      ∑ i : Fin 3, velocity v i * fderiv ℝ F (p,v) ((0,basis i),0)) +
       (∫ v : Vec, fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B)) := by rw [hK0,add_zero]
    _ = _ := by
      calc
        _ = ∫ v : Vec, (fderiv ℝ F (p,v) ((1,0),0) +
          ∑ i : Fin 3, velocity v i * fderiv ℝ F (p,v) ((0,basis i),0)) +
            fderiv ℝ F (p,v) ((0,0),E + cross (velocity v) B) :=
          (integral_add (hint.add (integrable_finsetSum Finset.univ (fun i _ => hint' i))) hintK).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with v
          exact (he v).symm

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

lemma contDiff_volterra {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
    {F : (ℝ × H) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (volterra F) :=
  (contDiff_paramPrimitive hF).comp (contDiff_fst.prodMk contDiff_id)

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

lemma sourceWave_initial_value (ρ : ℝ × Vec → ℝ) (x : Vec) :
    sourceWave ρ (0,x) = 0 := by simp [sourceWave,volterra]

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

lemma dirD_component {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : H → Vec} (hF : Differentiable ℝ F) (p e : H) (i : Fin 3) :
    dirD (fun z => F z i) e p = dirD F e p i := by
  have h := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp p (hF p).hasFDerivAt
  change HasFDerivAt (fun z => F z i) _ p at h
  unfold dirD
  rw [h.fderiv]
  rfl

lemma contDiff_waveGradient {u : ℝ × Vec → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (waveGradient u) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_dirD hu (0,basis i)

lemma contDiff_freeWave {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (freeWave g h) :=
  (contDiff_dirD (contDiff_waveK hg) (1,0)).add (contDiff_waveK hh)

lemma freeWave_initial {g h : Vec → ℝ} (hg : ContDiff ℝ ∞ g) (x : Vec) :
    freeWave g h (0,x)=g x := by
  rw [freeWave,← deriv_slice_eq_dirD ((contDiff_waveK hg).differentiable (by simp)),
    waveK_initial_velocity hg,waveK_zero,add_zero]

lemma contDiff_spaceCurl {F : Field} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (spaceCurl F) := by
  apply contDiff_euclidean.mpr
  intro i
  exact (contDiff_component (contDiff_dirD hF _) _).sub
    (contDiff_component (contDiff_dirD hF _) _)

lemma contDiff_field_slice {F : Field} (hF : ContDiff ℝ ∞ F) (t : ℝ) :
    ContDiff ℝ ∞ (fun x => F (t,x)) := hF.comp (contDiff_const.prodMk contDiff_id)

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_SpaceDiv
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma spaceDiv_slice {F : Field} (hF : Differentiable ℝ F) (t : ℝ) (x : Vec) :
    spaceDiv F (t,x) = divergence (fun y => F (t,y)) x := by
  unfold spaceDiv divergence
  apply Finset.sum_congr rfl
  intro i _
  have hc : Differentiable ℝ (fun p => F p i) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiable.comp hF
  rw [spatialPartial_time_slice (hc (t,x))]
  exact (dirD_component hF (t,x) (0,basis i) i).symm

lemma contDiff_freeField {G H : Vec → Vec}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (freeField G H) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_freeWave (contDiff_component hG i) (contDiff_component hH i)

lemma freeField_initial {G H : Vec → Vec} (hG : ContDiff ℝ ∞ G) (x : Vec) :
    freeField G H (0,x)=G x := by
  ext i
  exact freeWave_initial (contDiff_component hG i) x

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceField
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma contDiff_sourceField {J : Field} (hJ : ContDiff ℝ ∞ J) :
    ContDiff ℝ ∞ (sourceField J) := by
  apply contDiff_euclidean.mpr
  intro i
  exact contDiff_sourceWave (contDiff_component hJ i)

lemma sourceField_initial (J : Field) (x : Vec) : sourceField J (0,x)=0 := by
  ext i
  exact sourceWave_initial_value (fun p => J p i) x

lemma contDiff_maxwellElectric {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀)
    (hρ : ContDiff ℝ ∞ ρ) (hj : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (maxwellElectric E₀ B₀ ρ j) :=
  (contDiff_freeField hE ((contDiff_curl hB).sub (contDiff_field_slice hj 0))).add
    (contDiff_sourceField ((contDiff_waveGradient hρ).neg.sub (contDiff_dirD hj _)))

lemma contDiff_maxwellMagnetic {E₀ B₀ : Vec → Vec} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (hB : ContDiff ℝ ∞ B₀) (hj : ContDiff ℝ ∞ j) :
    ContDiff ℝ ∞ (maxwellMagnetic E₀ B₀ j) :=
  (contDiff_freeField hB (contDiff_curl hE).neg).add
    (contDiff_sourceField (contDiff_spaceCurl hj))

lemma maxwellElectric_initial {E₀ B₀ : Vec → Vec} {ρ : ℝ × Vec → ℝ} {j : Field}
    (hE : ContDiff ℝ ∞ E₀) (x : Vec) : maxwellElectric E₀ B₀ ρ j (0,x)=E₀ x := by
  simp only [maxwellElectric,freeField_initial hE,sourceField_initial,add_zero]

lemma maxwellMagnetic_initial {E₀ B₀ : Vec → Vec} {j : Field}
    (hB : ContDiff ℝ ∞ B₀) (x : Vec) : maxwellMagnetic E₀ B₀ j (0,x)=B₀ x := by
  simp only [maxwellMagnetic,freeField_initial hB,sourceField_initial,add_zero]

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_VlasovConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff

namespace RVM

universe u

namespace SmoothLorentzFlow

variable {E B : Field} (F : SmoothLorentzFlow E B)

lemma contDiff_particle {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) :
    ContDiff ℝ ∞ (F.particle f₀) := hf.comp F.smooth_backward

lemma particle_along (f₀ : Phase → ℝ) (t : ℝ) (z : Phase) :
    F.particle f₀ (t,F.forward z t) = f₀ z := by
  simp only [particle,F.left_inverse]

lemma backward_initial (z : Phase) : F.backward (0,z) = z := by
  simpa only [F.initial] using F.left_inverse 0 z

lemma particle_initial (f₀ : Phase → ℝ) (z : Phase) : F.particle f₀ (0,z) = f₀ z := by
  simp only [particle,F.backward_initial]

lemma particle_nonneg {f₀ : Phase → ℝ} (hf : ∀ z, 0 ≤ f₀ z) (w : ℝ × Phase) :
    0 ≤ F.particle f₀ w := hf _

lemma particle_compact {f₀ : Phase → ℝ} (hf : HasCompactSupport f₀) (a b : ℝ) :
    ∃ K : Set Phase, IsCompact K ∧
      ∀ t ∈ Icc a b, tsupport (fun z => F.particle f₀ (t,z)) ⊆ K := by
  let K := (fun w : ℝ × Phase => F.forward w.2 w.1) '' (Icc a b ×ˢ tsupport f₀)
  have hK : IsCompact K := (isCompact_Icc.prod hf).image F.smooth_forward.continuous
  refine ⟨K,hK,?_⟩
  intro t ht
  apply closure_minimal _ hK.isClosed
  intro z hz
  exact ⟨(t,F.backward (t,z)),⟨ht,subset_tsupport _ hz⟩,F.right_inverse t z⟩

lemma particle_vlasov_direction {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (t : ℝ) (z : Phase) :
    fderiv ℝ (F.particle f₀) (t,z) (1,lorentzField E B (t,z)) = 0 := by
  let y := F.backward (t,z)
  have hy : F.forward y t = z := F.right_inverse t z
  have hd := ((F.contDiff_particle hf).differentiable (by simp) (t,F.forward y t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (F.ode y t))
  have heq : (fun r => F.particle f₀ (r,F.forward y r)) = fun _ => f₀ y := by
    funext r
    exact F.particle_along f₀ r y
  change HasDerivAt (fun r => F.particle f₀ (r,F.forward y r)) _ t at hd
  rw [heq] at hd
  have hh := hd.unique (hasDerivAt_const t (f₀ y))
  simpa only [hy] using hh

lemma particle_local_data {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport f₀) (t : ℝ) (x : Vec) :
    ∃ (U : Set (ℝ × Vec)) (K : Set Vec),
      IsOpen U ∧ IsCompact K ∧ (t,x) ∈ U ∧
      ContDiffOn ℝ ∞ (particleBySpacetime (F.particle f₀)) (U ×ˢ univ) ∧
      ∀ p ∈ U, ∀ v ∉ K, particleBySpacetime (F.particle f₀) (p,v) = 0 := by
  obtain ⟨K,hK,hzero⟩ := F.particle_compact hc (t-1) (t+1)
  let U : Set (ℝ × Vec) := {p | p.1 ∈ Ioo (t-1) (t+1)}
  refine ⟨U,Prod.snd '' K,isOpen_Ioo.preimage continuous_fst,hK.image continuous_snd,
    ⟨by linarith,by linarith⟩,((F.contDiff_particle hf).comp contDiff_reassociate).contDiffOn,?_⟩
  intro p hp v hv
  by_contra hn
  exact hv ⟨(p.2,v),hzero p.1 (Ioo_subset_Icc_self hp) (subset_tsupport _ hn),rfl⟩

lemma moment_smooth {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) (hc : HasCompactSupport f₀)
    {w : Vec → W} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (particleMoment (F.particle f₀) w) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  obtain ⟨U,K,hU,hK,hp,hf',hz⟩ := F.particle_local_data hf hc p.1 p.2
  have hs := contDiffOn_integral_uniform_support (n:=⊤) hU hK
    (hf'.smul (hw.comp contDiff_snd).contDiffOn)
    (fun p hp v hv => by
      change particleBySpacetime (F.particle f₀) (p,v) • w v = 0
      rw [hz p hp v hv,zero_smul])
  exact hs.contDiffAt (hU.mem_nhds hp)

lemma rho_smooth {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) (hc : HasCompactSupport f₀) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun z => F.particle f₀ (p.1,z)) p.2) := by
  convert F.moment_smooth hf hc (contDiff_const (c:=(1:ℝ))) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp [particleMoment,rho]

lemma current_smooth {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) (hc : HasCompactSupport f₀) :
    ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun z => F.particle f₀ (p.1,z)) p.2) :=
  F.moment_smooth hf hc contDiff_velocity

lemma particle_moment_integrable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀) (hc : HasCompactSupport f₀)
    {w : Vec → W} (hw : Continuous w) (p : ℝ × Vec) :
    Integrable (fun v => F.particle f₀ (p.1,p.2,v) • w v) := by
  obtain ⟨U,K,hU,hK,hp,hs,hz⟩ := F.particle_local_data hf hc p.1 p.2
  have hcont : Continuous (fun v : Vec => F.particle f₀ (p.1,p.2,v)) :=
    (F.contDiff_particle hf).continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  exact (hcont.smul hw).integrable_of_hasCompactSupport
    (compactSupport_of_zero_off hK (hz p hp)).smul_right

lemma current_component {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport f₀) (p : ℝ × Vec) (i : Fin 3) :
    current (fun z => F.particle f₀ (p.1,z)) p.2 i =
      ∫ v : Vec, velocity v i * F.particle f₀ (p.1,p.2,v) := by
  rw [current,integral_vec_apply (F.particle_moment_integrable hf hc
    (contDiff_velocity (k:=1)).continuous p)]
  simp only [PiLp.smul_apply,smul_eq_mul,mul_comm]

lemma source_conservation {f₀ : Phase → ℝ} (hf : ContDiff ℝ ∞ f₀)
    (hc : HasCompactSupport f₀) (t : ℝ) (x : Vec) :
    dirD (fun p : ℝ × Vec => rho (fun z => F.particle f₀ (p.1,z)) p.2) (1,0) (t,x) +
      divergence (fun y => current (fun z => F.particle f₀ (t,z)) y) x = 0 := by
  obtain ⟨U,K,hU,hK,hp,hs,hz⟩ := F.particle_local_data hf hc t x
  have he := particle_number_balance_param (E (t,x)) (B (t,x)) hU hK hp
    (hs.of_le (by simp)) hz
  have hv (v : Vec) : fderiv ℝ (particleBySpacetime (F.particle f₀)) ((t,x),v)
      ((1,velocity v),E (t,x)+cross (velocity v) (B (t,x))) = 0 := by
    rw [fderiv_particleBySpacetime ((F.contDiff_particle hf).differentiable (by simp) _)]
    exact F.particle_vlasov_direction hf t (x,v)
  simp only [hv,integral_zero] at he
  apply Eq.trans _ he
  congr 1
  unfold divergence
  apply Finset.sum_congr rfl
  intro i _
  have hj : DifferentiableAt ℝ (fun p : ℝ × Vec =>
      current (fun z => F.particle f₀ (p.1,z)) p.2 i) (t,x) :=
    (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (t,x)
      ((F.current_smooth hf hc).differentiable (by simp) _)
  rw [spatialPartial_time_slice hj]
  have heq : (fun p : ℝ × Vec => current (fun z => F.particle f₀ (p.1,z)) p.2 i) =
      (fun p => ∫ v : Vec, velocity v i * particleBySpacetime (F.particle f₀) (p,v)) :=
    funext (fun p => F.current_component hf hc p i)
  rw [heq]

end SmoothLorentzFlow

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

namespace SmoothLorentzFlow

lemma source_spatial_support {E B : Field} (F : SmoothLorentzFlow E B)
    {f₀ : Phase → ℝ} (hc : HasCompactSupport f₀) (a b : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t∈Icc a b, ∀ x : Vec, R<‖x‖ →
      rho (fun z => F.particle f₀ (t,z)) x=0 ∧
      current (fun z => F.particle f₀ (t,z)) x=0 := by
  obtain ⟨K,hK,hz⟩ := F.particle_compact hc a b
  obtain ⟨R,hR⟩ := (hK.image continuous_fst).isBounded.exists_norm_le
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro t ht x hx
  have he (v : Vec) : F.particle f₀ (t,x,v)=0 := by
    by_contra hn
    have hh := hR x ⟨(x,v),hz t ht (subset_tsupport _ hn),rfl⟩
    exact (not_lt_of_ge (hh.trans (le_max_left _ _))) hx
  simp [rho,current,he]

end SmoothLorentzFlow

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

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

theorem exists_picard_regular_oai {d : Datum} (hd : Admissible d) {E B : Field}
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B) :
    ∃ s : Solution, PicardRegular d s ∧ TransportFor s E B := by
  obtain ⟨hf,hc,hn,hE0,hB0,hEL,hBL,hDE,hDB⟩ := hd
  obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
  let f := F.particle d.f₀
  let ρ : ℝ × Vec → ℝ := fun p => rho (fun z => f (p.1,z)) p.2
  let j : Field := fun p => current (fun z => f (p.1,z)) p.2
  have hρ : ContDiff ℝ ∞ ρ := F.rho_smooth hf hc
  have hj : ContDiff ℝ ∞ j := F.current_smooth hf hc
  have hρ0 (x : Vec) : divergence d.E₀ x=ρ (0,x) := by
    simpa only [ρ,f,F.particle_initial] using hDE x
  let s : Solution := ⟨f,maxwellElectric d.E₀ d.B₀ ρ j,maxwellMagnetic d.E₀ d.B₀ j⟩
  have hsc : ∀ t, 0<t → ∀ x, dirD ρ (1,0) (t,x)+spaceDiv j (t,x)=0 := by
    intro t ht x
    rw [spaceDiv_slice (hj.differentiable (by simp))]
    exact F.source_conservation hf hc t x
  obtain ⟨hLe,hLb⟩ := maxwell_timeContinuousL2 hE0.1 hB0.1 hρ hj hEL hBL hρ0 hDB (by
    intro T hT
    obtain ⟨R,hR,hz⟩ := F.source_spatial_support hc (-1) (T+1)
    exact ⟨R,hz⟩)
  refine ⟨s,?_,F.particle_vlasov_direction hf⟩
  exact ⟨F.contDiff_particle hf,contDiff_maxwellElectric hE0.1 hB0.1 hρ hj,
    contDiff_maxwellMagnetic hE0.1 hB0.1 hj,F.particle_nonneg hn,
    fun T _ => F.particle_compact hc 0 T,hLe,hLb,F.particle_initial d.f₀,
    maxwellElectric_initial hE0.1,maxwellMagnetic_initial hB0.1,
    fun t ht x => constructed_maxwell_equations hE0.1 hB0.1 hρ hj hsc hρ0 hDB ht x,
    hρ,hj⟩

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.exists_picard_regular_oai := @OAI.RVM.exists_picard_regular_oai
