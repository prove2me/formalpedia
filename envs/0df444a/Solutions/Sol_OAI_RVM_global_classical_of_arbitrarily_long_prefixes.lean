-- Prove2me | solution 1 for OAI.RVM.global_classical_of_arbitrarily_long_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:28:55.116597+00:00
-- url     : https://prove2.me/submissions/ad1cefaa-8ffe-4b09-8420-96c12c0272ec

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

lemma divergence_cross {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => cross (F y) (G y)) x =
      dot (G x) (curl F x) - dot (F x) (curl G x) := by
  have hf (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF
  have hg (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG
  simp only [divergence, Fin.sum_univ_succ]
  change spatialPartial (fun y => F y 1 * G y 2 - F y 2 * G y 1) x 0 +
    (spatialPartial (fun y => F y 2 * G y 0 - F y 0 * G y 2) x 1 +
    (spatialPartial (fun y => F y 0 * G y 1 - F y 1 * G y 0) x 2+0)) = _
  have hm (i j k : Fin 3) :
      spatialPartial ((fun y => F y i) * (fun y => G y j)) x k =
        F x i * spatialPartial (fun y => G y j) x k +
        G x j * spatialPartial (fun y => F y i) x k :=
    spatialPartial_mul (hf i) (hg j) k
  have hs (i j k l r : Fin 3) := spatialPartial_sub ((hf i).mul (hg j)) ((hf k).mul (hg l)) r
  simp only [Pi.mul_apply] at hs
  simp only [hs, hm]
  simp [dot, curl, Fin.sum_univ_succ]
  ring

lemma hasDerivAt_field_energy {E B : ℝ → Vec} {e b : Vec} {t : ℝ}
    (he : HasDerivAt E e t) (hb : HasDerivAt B b t) :
    HasDerivAt (fun s => (‖E s‖^2+‖B s‖^2)/2)
      (dot (E t) e + dot (B t) b) t := by
  convert (he.norm_sq.add hb.norm_sq).div_const 2 using 1
  all_goals try with_reducible_and_instances rfl
  rw [← dot_eq_inner, ← dot_eq_inner]
  ring

lemma maxwell_energy_balance {E B : Field} {j : Vec} {t : ℝ} {x : Vec}
    (hE : DifferentiableAt ℝ E (t,x)) (hB : DifferentiableAt ℝ B (t,x))
    (he : deriv (fun s => E (s,x)) t - curl (fun y => B (t,y)) x = -j)
    (hb : deriv (fun s => B (s,x)) t + curl (fun y => E (t,y)) x = 0) :
    deriv (fun s => (‖E (s,x)‖^2+‖B (s,x)‖^2)/2) t +
      divergence (fun y => cross (E (t,y)) (B (t,y))) x = -dot (E (t,x)) j := by
  have heT : DifferentiableAt ℝ (fun s => E (s,x)) t :=
    hE.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hbT : DifferentiableAt ℝ (fun s => B (s,x)) t :=
    hB.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have heX : DifferentiableAt ℝ (fun y => E (t,y)) x :=
    hE.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hbX : DifferentiableAt ℝ (fun y => B (t,y)) x :=
    hB.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  rw [(hasDerivAt_field_energy heT.hasDerivAt hbT.hasDerivAt).deriv,
    divergence_cross heX hbX]
  have he' : deriv (fun s => E (s,x)) t = curl (fun y => B (t,y)) x-j := by
    apply sub_eq_iff_eq_add.mp at he
    simpa only [sub_eq_add_neg, add_comm] using he
  have hb' : deriv (fun s => B (s,x)) t = -curl (fun y => E (t,y)) x :=
    eq_neg_of_add_eq_zero_left hb
  rw [he', hb']
  simp only [dot, PiLp.sub_apply, PiLp.neg_apply, mul_sub, mul_neg,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
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

lemma particle_spacetime_vlasov {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace) (heq : Equations s)
    {t : ℝ} (ht : 0 < t) (x v : Vec) :
    fderiv ℝ (particleBySpacetime s.f) ((t,x),v)
      ((1,velocity v),s.E (t,x) + cross (velocity v) (s.B (t,x))) = 0 := by
  have hd := particle_differentiableAt_positive hf ht x v
  rw [fderiv_particleBySpacetime hd, full_directional_derivative hd]
  have he := (heq t (le_of_lt ht)).1 x v
  rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he

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

lemma divergence_add {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    divergence (fun y => F y+G y) x = divergence F x + divergence G x := by
  have hf (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF
  have hg (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG
  have ha (i : Fin 3) := congrArg (fun L : Vec →L[ℝ] ℝ => L (basis i))
    (fderiv_add (hf i) (hg i))
  change ∀ i : Fin 3, fderiv ℝ (fun y => F y i + G y i) x (basis i) =
    fderiv ℝ (fun y => F y i) x (basis i) + fderiv ℝ (fun y => G y i) x (basis i) at ha
  simp only [divergence, PiLp.add_apply, spatialPartial, ha, Finset.sum_add_distrib]

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

lemma TimeContinuousL2.memLp {F : Field} (hF : TimeContinuousL2 F)
    {t : ℝ} (ht : 0 ≤ t) : MemLp (fun x => F (t,x)) 2 volume := by
  obtain ⟨F₂,hc,heq⟩ := hF
  exact (Lp.memLp (F₂ t)).ae_eq (heq t ht)

lemma TimeContinuousL2.integrable_norm_sq {F : Field} (hF : TimeContinuousL2 F)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x => ‖F (t,x)‖^2) := by
  have hm := hF.memLp ht
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

lemma TimeContinuousL2.continuous_integral_norm_sq {F : Field} (hF : TimeContinuousL2 F) :
    ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Ici 0) := by
  obtain ⟨F₂,hc,heq⟩ := hF
  have hh : ∀ t ∈ Ici (0:ℝ), (∫ x : Vec, ‖F (t,x)‖^2) = ‖F₂ t‖^2 := by
    intro t ht
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [heq t ht] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  exact (hc.norm.pow 2).congr (fun t ht => hh t ht)

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

lemma energyCutoff_smooth (n : ℕ) : ContDiff ℝ 1 (energyCutoff n) :=
  energyBump.contDiff.comp ((contDiff_const : ContDiff ℝ 1 (fun _ : Vec => ((n:ℝ)+1)⁻¹)).smul
    (contDiff_id : ContDiff ℝ 1 (fun x : Vec => x)))

lemma energyCutoff_compact (n : ℕ) : HasCompactSupport (energyCutoff n) := by
  apply compactSupport_of_zero_off (isCompact_closedBall (0:Vec) (2*((n:ℝ)+1)))
  intro x hx
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hnX : 2 * ((n:ℝ)+1) < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
  have hnx : (((n:ℝ)+1)⁻¹ • x) ∉ Function.support energyBump := by
    rw [energyBump.support_eq]
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), energyBump]
    have hh : 2 < ((n:ℝ)+1)⁻¹ * ‖x‖ := by
      rw [← div_eq_inv_mul, lt_div_iff₀ hn]
      exact hnX
    exact not_lt.mpr hh.le
  exact Function.notMem_support.mp hnx

lemma energyCutoff_bounds (n : ℕ) (x : Vec) : 0 ≤ energyCutoff n x ∧ energyCutoff n x ≤ 1 :=
  ⟨energyBump.nonneg,energyBump.le_one⟩

lemma energyCutoff_deriv_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, ∀ x : Vec, ‖fderiv ℝ (energyCutoff n) x‖ ≤ C / ((n:ℝ)+1) := by
  have hd : ContDiff ℝ 1 (energyBump : Vec → ℝ) := energyBump.contDiff
  obtain ⟨C,hC⟩ := (hd.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (energyBump.hasCompactSupport.fderiv ℝ)
  have hCp : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨C,hCp,?_⟩
  intro n x
  have hn : 0 < (n:ℝ)+1 := by positivity
  have hh := (hd.differentiable (by simp) (((n:ℝ)+1)⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (((n:ℝ)+1)⁻¹))
  have heq := hh.fderiv
  change fderiv ℝ (energyCutoff n) x = _ at heq
  rw [heq]
  calc
    _ ≤ ‖fderiv ℝ (energyBump : Vec → ℝ) (((n:ℝ)+1)⁻¹ • x)‖ *
        ‖((n:ℝ)+1)⁻¹ • ContinuousLinearMap.id ℝ Vec‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖fderiv ℝ (energyBump : Vec → ℝ) (((n:ℝ)+1)⁻¹ • x)‖ * ((n:ℝ)+1)⁻¹ := by
      simp [norm_smul, abs_of_pos hn]
    _ ≤ C * ((n:ℝ)+1)⁻¹ := mul_le_mul_of_nonneg_right (hC _) (inv_pos.mpr hn).le
    _ = _ := div_eq_mul_inv _ _ |>.symm

lemma energyCutoff_tendsto (x : Vec) : Filter.Tendsto (fun n => energyCutoff n x) Filter.atTop (𝓝 1) := by
  have hi : Filter.Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) Filter.atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hzero : energyBump (0:Vec) = 1 := energyBump.one_of_mem_closedBall (by simp [energyBump])
  simpa only [energyCutoff, zero_smul,hzero,Function.comp_def] using! energyBump.continuous.continuousAt.tendsto.comp (hi.smul_const x)

lemma energyCutoff_integral_tendsto {F : Vec → ℝ} (hF : Integrable F) :
    Filter.Tendsto (fun n => ∫ x : Vec, energyCutoff n x * F x) Filter.atTop (𝓝 (∫ x : Vec, F x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
  · intro n
    exact (energyCutoff_smooth n).continuous.aestronglyMeasurable.mul hF.aestronglyMeasurable
  · exact hF.norm
  · intro n
    filter_upwards [] with x
    rw [norm_mul, Real.norm_of_nonneg (energyCutoff_bounds n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (energyCutoff_bounds n x).2
  · filter_upwards [] with x
    simpa only [one_mul] using (energyCutoff_tendsto x).mul_const (F x)

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM

lemma scalar_gronwall_interior {f : ℝ → ℝ} {K ε T : ℝ}
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hT : 0 ≤ T)
    (hc : ContinuousOn f (Icc 0 T)) (h0 : f 0 = 0)
    (hd : ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ f t)
    (hb : ∀ t ∈ Ioo 0 T, deriv f t ≤ K*f t+ε) :
    f T ≤ ε*T*Real.exp (K*T) := by
  rcases eq_or_lt_of_le hT with he | ht
  · subst T; simp [h0]
  let g : ℝ → ℝ := fun t => f t * Real.exp (-K*t)
  have hgc : ContinuousOn g (Icc 0 T) := hc.mul (by fun_prop)
  have hgd (t : ℝ) (htt : t ∈ Ioo 0 T) :
      HasDerivAt g ((deriv f t-K*f t)*Real.exp (-K*t)) t := by
    convert (hd t htt).hasDerivAt.mul (((hasDerivAt_id t).const_mul (-K)).exp) using 1 <;> try rfl
    simp only [id_eq]
    ring
  obtain ⟨c,hc',heq⟩ := exists_deriv_eq_slope g ht hgc
    (fun t ht => (hgd t ht).differentiableAt.differentiableWithinAt)
  have he' : Real.exp (-K*c) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hc'.1])
  have hg' : deriv g c ≤ ε := by
    rw [(hgd c hc').deriv]
    calc
      _ ≤ ε*Real.exp (-K*c) := mul_le_mul_of_nonneg_right (by linarith [hb c hc']) (Real.exp_pos _).le
      _ ≤ ε := mul_le_of_le_one_right hε he'
  rw [heq,sub_zero,show g 0=0 by simp [g,h0],sub_zero] at hg'
  have hlast := (div_le_iff₀ ht).mp hg'
  have hx := mul_le_mul_of_nonneg_right hlast (Real.exp_pos (K*T)).le
  simpa only [g,mul_assoc,← Real.exp_add,neg_mul,neg_add_cancel,Real.exp_zero,mul_one] using hx

lemma weighted_density_hasDerivAt
    {e : ℝ × Vec → ℝ} {g : Vec → ℝ} {t : ℝ}
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (ht : 0 < t) :
    HasDerivAt (fun r => ∫ x : Vec, g x*e (r,x))
      (∫ x : Vec, g x*fderiv ℝ e (t,x) (1,0)) t := by
  have hF : ContDiffOn ℝ 1 (fun p : ℝ × Vec => g p.2*e p)
      (Ioi 0 ×ˢ (univ : Set Vec)) := (hg.comp contDiff_snd).contDiffOn.mul he
  have hz : ∀ r ∈ Ioi (0:ℝ), ∀ x ∉ tsupport g, g x*e (r,x)=0 := by
    intro r _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hi := fderiv_integral_uniform_support_apply isOpen_Ioi hc ht hF hz (1:ℝ)
  have hd := hasFDerivAt_integral_uniform_support isOpen_Ioi hc ht hF hz
  have heq (x : Vec) : fderiv ℝ (fun p : ℝ × Vec => g p.2*e p) (t,x) (1,0) =
      g x*fderiv ℝ e (t,x) (1,0) := by
    have he' := he.contDiffAt (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
    have heT : DifferentiableAt ℝ (fun r => e (r,x)) t :=
      DifferentiableAt.comp t (f := fun r : ℝ => (r,x)) (g := e)
        (he'.differentiableAt (by simp))
        (differentiableAt_id.prodMk (differentiableAt_const x))
    have hgT := heT.hasDerivAt.const_mul (g x)
    have hf := hF.contDiffAt (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
    rw [← deriv_time_slice (hf.differentiableAt (by simp)), hgT.deriv,
      deriv_time_slice (he'.differentiableAt (by simp))]
  have hid : deriv (fun r => ∫ x : Vec, g x*e (r,x)) t =
      ∫ x : Vec, g x*fderiv ℝ e (t,x) (1,0) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g x*e (r,x)) t 1 = _
    rw [hi]
    simp only [heq]
  exact hid ▸ hd.differentiableAt.hasDerivAt

lemma continuous_divergence {F : Vec → Vec} (hF : ContDiff ℝ 1 F) :
    Continuous (divergence F) := by
  unfold divergence spatialPartial
  apply continuous_finsetSum
  intro i _
  have hi : ContDiff ℝ 1 (fun x => F x i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  exact (hi.continuous_fderiv (by simp)).clm_apply continuous_const

lemma weighted_density_deriv_le
    {e : ℝ × Vec → ℝ} {F : ℝ × Vec → Vec} {g : Vec → ℝ} {t K C : ℝ}
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hF : ContDiffOn ℝ 1 F (Ioi 0 ×ˢ (univ : Set Vec)))
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (ht : 0 < t)
    (hg0 : ∀ x, 0 ≤ g x) (hC : 0 ≤ C) (hgb : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (heI : Integrable (fun x : Vec => e (t,x)))
    (hflux : ∀ x : Vec, ‖F (t,x)‖ ≤ e (t,x))
    (hineq : ∀ x : Vec, fderiv ℝ e (t,x) (1,0) + divergence (fun y => F (t,y)) x ≤ K*e (t,x)) :
    deriv (fun r => ∫ x : Vec, g x*e (r,x)) t ≤
      K*(∫ x : Vec, g x*e (t,x))+C*(∫ x : Vec, e (t,x)) := by
  have hes : Continuous (fun x : Vec => e (t,x)) := he.continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨ht,mem_univ _⟩)
  have hfs : ContDiff ℝ 1 (fun x : Vec => F (t,x)) := by
    apply contDiffOn_univ.mp
    exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨ht,mem_univ _⟩)
  have hedc : Continuous (fun x : Vec => fderiv ℝ e (t,x) (1,0)) :=
    ((he.continuousOn_fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨ht,mem_univ _⟩)).clm_apply continuous_const
  have hi₁ : Integrable (fun x : Vec => g x*fderiv ℝ e (t,x) (1,0)) :=
    (hg.continuous.mul hedc).integrable_of_hasCompactSupport hc.mul_right
  have hi₂ : Integrable (fun x : Vec => g x*e (t,x)) :=
    (hg.continuous.mul hes).integrable_of_hasCompactSupport hc.mul_right
  have hi₃ : Integrable (fun x : Vec => g x*divergence (fun y => F (t,y)) x) :=
    (hg.continuous.mul (continuous_divergence hfs)).integrable_of_hasCompactSupport hc.mul_right
  have hi₄ : Integrable (fun x : Vec => fderiv ℝ g x (F (t,x))) :=
    ((hg.continuous_fderiv (by simp)).clm_apply hfs.continuous).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hc.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx, zero_apply]))
  rw [(weighted_density_hasDerivAt he hg hc ht).deriv]
  calc
    _ ≤ ∫ x : Vec, K*(g x*e (t,x))-g x*divergence (fun y => F (t,y)) x := by
      apply integral_mono hi₁ ((hi₂.const_mul K).sub hi₃)
      intro x
      change g x * fderiv ℝ e (t,x) (1,0) ≤ K*(g x*e (t,x))-g x*divergence (fun y => F (t,y)) x
      nlinarith [mul_le_mul_of_nonneg_left (hineq x) (hg0 x)]
    _ = K*(∫ x : Vec, g x*e (t,x))+(∫ x : Vec, fderiv ℝ g x (F (t,x))) := by
      rw [integral_sub (hi₂.const_mul K) hi₃, integral_const_mul, integral_mul_divergence hfs hg hc]
      ring
    _ ≤ _ := by
      apply add_le_add_right
      calc
        _ ≤ ∫ x : Vec, C*e (t,x) := by
          apply integral_mono hi₄ (heI.const_mul C)
          intro x
          exact (le_abs_self _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul (hgb x) (hflux x) (norm_nonneg _) hC))
        _ = _ := integral_const_mul _ _

theorem local_energy_inequality_vanishes
    {e : ℝ × Vec → ℝ} {F : ℝ × Vec → Vec} {K T : ℝ}
    (hK : 0 ≤ K) (hT : 0 ≤ T)
    (he : ContDiffOn ℝ 1 e (Ioi 0 ×ˢ (univ : Set Vec)))
    (hF : ContDiffOn ℝ 1 F (Ioi 0 ×ˢ (univ : Set Vec)))
    (hec : ContinuousOn e (Icc 0 T ×ˢ (univ : Set Vec)))
    (he0 : ∀ t ∈ Icc 0 T, ∀ x : Vec, 0 ≤ e (t,x))
    (heI : ∀ t ∈ Icc 0 T, Integrable (fun x : Vec => e (t,x)))
    (hcont : ContinuousOn (fun t => ∫ x : Vec, e (t,x)) (Icc 0 T))
    (hflux : ∀ t ∈ Ioo 0 T, ∀ x : Vec, ‖F (t,x)‖ ≤ e (t,x))
    (hineq : ∀ t ∈ Ioo 0 T, ∀ x : Vec,
      fderiv ℝ e (t,x) (1,0)+divergence (fun y => F (t,y)) x ≤ K*e (t,x))
    (hinit : ∀ x : Vec, e (0,x)=0) :
    ∀ x : Vec, e (T,x)=0 := by
  obtain ⟨C,hC,hCb⟩ := energyCutoff_deriv_bound
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).bddAbove_image hcont
  have hB' : ∀ t ∈ Icc 0 T, (∫ x : Vec, e (t,x)) ≤ B := fun t ht => hB ⟨t,ht,rfl⟩
  have hBn : 0 ≤ B := by
    have ht0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl,hT⟩
    exact (integral_nonneg (he0 0 ht0)).trans (hB' 0 ht0)
  have hbound (n : ℕ) : (∫ x : Vec, energyCutoff n x*e (T,x)) ≤
      ((C/((n:ℝ)+1))*B)*T*Real.exp (K*T) := by
    let f : ℝ → ℝ := fun t => ∫ x : Vec, energyCutoff n x*e (t,x)
    have hfc : ContinuousOn f (Icc 0 T) := by
      apply continuousOn_integral_uniform_support (energyCutoff_compact n)
        (((energyCutoff_smooth n).continuous.comp continuous_snd).continuousOn.mul hec)
      intro t _ x hx
      change energyCutoff n x * e (t,x) = 0
      rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
    apply scalar_gronwall_interior hK (mul_nonneg (div_nonneg hC (by positivity)) hBn) hT hfc
    · simp only [f,hinit,mul_zero,integral_zero]
    · intro t ht
      exact (weighted_density_hasDerivAt he (energyCutoff_smooth n) (energyCutoff_compact n) ht.1).differentiableAt
    · intro t ht
      have hder := weighted_density_deriv_le he hF (energyCutoff_smooth n)
        (energyCutoff_compact n) ht.1 (fun x => (energyCutoff_bounds n x).1)
        (div_nonneg hC (by positivity)) (hCb n) (heI t ⟨ht.1.le,ht.2.le⟩)
        (hflux t ht) (hineq t ht)
      exact hder.trans (add_le_add_right
        (mul_le_mul_of_nonneg_left (hB' t ⟨ht.1.le,ht.2.le⟩) (div_nonneg hC (by positivity))) _)
  have hl := energyCutoff_integral_tendsto (heI T ⟨hT,le_rfl⟩)
  have hr : Tendsto (fun n : ℕ => ((C/((n:ℝ)+1))*B)*T*Real.exp (K*T)) atTop (nhds 0) := by
    have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [div_eq_mul_inv,mul_zero,zero_mul] using (((hi.const_mul C).mul_const B).mul_const T).mul_const (Real.exp (K*T))
  have hz : (∫ x : Vec, e (T,x))=0 := le_antisymm
    (le_of_tendsto_of_tendsto' hl hr hbound) (integral_nonneg (he0 T ⟨hT,le_rfl⟩))
  have hae := (integral_eq_zero_iff_of_nonneg (he0 T ⟨hT,le_rfl⟩) (heI T ⟨hT,le_rfl⟩)).mp hz
  have hes : Continuous (fun x : Vec => e (T,x)) := hec.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨⟨hT,le_rfl⟩,mem_univ _⟩)
  exact fun x => congrFun (Measure.eq_of_ae_eq (μ := volume) hae hes continuous_const) x

lemma Classical.regularParticle {d : Datum} {s : Solution} (hs : Classical d s) :
    RegularParticle s.f := ⟨hs.1,hs.2.2.2.2.2.2.1⟩

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

lemma RegularParticle.moment_regular {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {f : Particle} (hf : RegularParticle f)
    {w : Vec → W} (hw : ContDiff ℝ 1 w) :
    ContDiffOn ℝ 1 (particleMoment f w) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  intro p hp
  obtain ⟨U,K,hU,hK,hp',hF,hzero⟩ := hf.local_data hp.1 p.2
  have hs := contDiffOn_integral_uniform_support (n := 1) hU hK
    (hF.smul (hw.comp contDiff_snd).contDiffOn)
    (fun p hp v hv => by
      change particleBySpacetime f (p,v) • w v = 0
      rw [hzero p hp v hv,zero_smul])
  exact (hs.contDiffAt (hU.mem_nhds hp')).contDiffWithinAt

lemma RegularParticle.moment_continuous_slab {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (particleMoment f w) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hf.2 T hT
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, f (p.1,p.2,v) • w v) _
  apply continuousOn_integral_uniform_support
    (F := fun z : (ℝ × Vec) × Vec => f (z.1.1,z.1.2,z.2) • w z.2) (hK.image continuous_snd)
  · apply ContinuousOn.smul ?_ (hw.comp continuous_snd).continuousOn
    exact hf.1.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
      (fun z hz => hz.1.1.1)
  · intro p hp v hv
    have hz : f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hz,zero_smul]

lemma RegularParticle.moment_compact {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Particle} (hf : RegularParticle f) (w : Vec → W) {T : ℝ} (hT : 0 ≤ T) :
    ∃ K : Set Vec, IsCompact K ∧ ∀ t ∈ Icc 0 T, ∀ x ∉ K, particleMoment f w (t,x) = 0 := by
  obtain ⟨K,hK,hzero⟩ := hf.2 T hT
  refine ⟨Prod.fst '' K,hK.image continuous_fst,?_⟩
  intro t ht x hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  have hz : f (t,x,v) = 0 := by
    by_contra hn
    exact hx ⟨(x,v),hzero t ht (subset_tsupport _ hn),rfl⟩
  simp only [hz,zero_smul,Pi.zero_apply]

lemma RegularParticle.spatial_moment_integrable {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun x : Vec => particleMoment f w (t,x)) := by
  obtain ⟨K,hK,hz⟩ := hf.moment_compact w ht
  have hc := (hf.moment_continuous_slab hw ht).comp_continuous
    (continuous_const.prodMk continuous_id)
    (fun x : Vec => show (t,x) ∈ Icc 0 t ×ˢ (univ : Set Vec) from ⟨⟨ht,le_rfl⟩,mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz t ⟨ht,le_rfl⟩))

lemma RegularParticle.integrated_moment_continuous {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Particle} (hf : RegularParticle f) {w : Vec → W} (hw : Continuous w)
    {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x : Vec, particleMoment f w (t,x)) (Icc 0 T) := by
  obtain ⟨K,hK,hz⟩ := hf.moment_compact w hT
  exact continuousOn_integral_uniform_support hK (hf.moment_continuous_slab hw hT) hz

lemma RegularParticle.velocity_flux_bound {f : Particle} (hf : RegularParticle f)
    {t : ℝ} (ht : 0 ≤ t) (x : Vec) (hpos : ∀ v, 0 ≤ f (t,x,v)) :
    ‖particleMoment f velocity (t,x)‖ ≤ particleMoment f (fun _ => (1:ℝ)) (t,x) := by
  dsimp [particleMoment]
  simp only [mul_one]
  calc
    _ ≤ ∫ v : Vec, ‖f (t,x,v) • velocity v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : Vec, f (t,x,v) := by
      have hi := hf.moment_integrable (contDiff_velocity (k := 1)).continuous ht x
      have hfI : Integrable (fun v : Vec => f (t,x,v)) :=
        (hf.slice ht x).1.continuous.integrable_of_hasCompactSupport (hf.slice ht x).2
      apply integral_mono hi.norm hfI
      intro v
      change ‖f (t,x,v) • velocity v‖ ≤ f (t,x,v)
      rw [norm_smul,Real.norm_of_nonneg (hpos v)]
      exact mul_le_of_le_one_right (hpos v) (norm_velocity_lt_one v).le

lemma TimeContinuousL2.sub {E F : Field} (hE : TimeContinuousL2 E) (hF : TimeContinuousL2 F) :
    TimeContinuousL2 (E-F) := by
  obtain ⟨E₂,hEc,hEe⟩ := hE
  obtain ⟨F₂,hFc,hFe⟩ := hF
  refine ⟨E₂-F₂,hEc.sub hFc,?_⟩
  intro t ht
  filter_upwards [Lp.coeFn_sub (E₂ t) (F₂ t),hEe t ht,hFe t ht] with x hsub he hf
  exact hsub.trans (by simp only [he,hf,Pi.sub_apply])

lemma uniqueDiffOn_particleHalfSpace : UniqueDiffOn ℝ particleHalfSpace := by
  have he : particleHalfSpace = Ici (0:ℝ) ×ˢ (univ : Set Phase) := by
    ext p; simp [particleHalfSpace]
  rw [he]
  exact (uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ

lemma RegularParticle.velocity_derivative_bound {f : Particle} (hf : RegularParticle f)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t ∈ Ioo 0 T, ∀ x v : Vec,
      ‖fderiv ℝ (fun w => f (t,x,w)) v‖ ≤ L := by
  obtain ⟨K,hK,hz⟩ := hf.2 T hT
  have hfullc := (hf.1.continuousOn_fderivWithin uniqueDiffOn_particleHalfSpace le_rfl).norm
  have hsub : Icc 0 T ×ˢ K ⊆ particleHalfSpace := fun p hp => hp.1.1
  obtain ⟨B,hB⟩ := ((isCompact_Icc : IsCompact (Icc (0:ℝ) T)).prod hK).bddAbove_image
    (hfullc.mono hsub)
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro t ht x v
  by_cases hmem : (x,v) ∈ K
  · have hd := particle_differentiableAt_positive (s := ⟨f,0,0⟩) hf.1 ht.1 x v
    have hnhds : particleHalfSpace ∈ nhds (t,x,v) :=
      mem_of_superset ((isOpen_Ioi.preimage (continuous_fst : Continuous (Prod.fst : ℝ × Phase → ℝ))).mem_nhds ht.1)
        (fun p hp => show p.1 ≥ 0 from le_of_lt hp)
    have hb : ‖fderiv ℝ f (t,x,v)‖ ≤ max 0 B := by
      rw [← fderivWithin_of_mem_nhds hnhds]
      exact (hB ⟨(t,x,v),⟨⟨ht.1.le,ht.2.le⟩,hmem⟩,rfl⟩).trans (le_max_right _ _)
    have hinj : HasFDerivAt (fun w : Vec => (t,x,w))
        ((0 : Vec →L[ℝ] ℝ).prod ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec))) v := by
      fun_prop
    have hs := hd.hasFDerivAt.comp v hinj
    apply ContinuousLinearMap.opNorm_le_bound _ (le_max_left 0 B)
    intro w
    have he : fderiv ℝ (fun w => f (t,x,w)) v w = fderiv ℝ f (t,x,v) (0,0,w) := by
      exact congrArg (fun A : Vec →L[ℝ] ℝ => A w) hs.fderiv
    rw [he]
    calc
      _ ≤ ‖fderiv ℝ f (t,x,v)‖ * ‖((0,0,w) : ℝ × Phase)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg w)
  · have hzero : (fun w : Vec => f (t,x,w)) =ᶠ[nhds v] (fun _ => 0) := by
      have hn := (hK.isClosed.isOpen_compl.preimage (continuous_const.prodMk continuous_id)).mem_nhds hmem
      filter_upwards [hn] with w hw
      by_contra hne
      exact hw (hz t ⟨ht.1.le,ht.2.le⟩ (subset_tsupport _ hne))
    rw [hzero.fderiv_eq (𝕜 := ℝ)]
    simp

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

lemma fderiv_square_half {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : H → ℝ} {p b : H} (hg : DifferentiableAt ℝ g p) :
    fderiv ℝ (fun z => (g z)^2/2) p b = g p * fderiv ℝ g p b := by
  have h := (hg.hasFDerivAt.pow 2).mul_const (2:ℝ)⁻¹
  simp only [div_eq_mul_inv]
  rw [h.fderiv]
  simp only [smul_apply,smul_eq_mul]
  norm_num
  ring

lemma squareDifference_nonneg (s₁ s₂ : Solution) (z : ℝ × Phase) :
    0 ≤ squareDifference s₁ s₂ z := div_nonneg (sq_nonneg _) (by norm_num)

lemma squareDifference_zero_iff (s₁ s₂ : Solution) (z : ℝ × Phase) :
    squareDifference s₁ s₂ z = 0 ↔ s₁.f z=s₂.f z := by
  simp [squareDifference,sub_eq_zero]

lemma particle_difference_direction {d : Datum} {s₁ s₂ : Solution}
    (hs₁ : Classical d s₁) (hs₂ : Classical d s₂) {t : ℝ} (ht : 0 < t) (x v : Vec) :
    fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hd₁ := particle_differentiableAt_positive hs₁.1 ht x v
  have hd₂ := particle_differentiableAt_positive hs₂.1 ht x v
  have hsp₁ : DifferentiableAt ℝ (particleBySpacetime s₁.f) ((t,x),v) :=
    (hd₁.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have hsp₂ : DifferentiableAt ℝ (particleBySpacetime s₂.f) ((t,x),v) :=
    (hd₂.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have he₁ := particle_spacetime_vlasov hs₁.1 hs₁.2.2.2.2.2.2.2.1 ht x v
  have he₂ := particle_spacetime_vlasov hs₂.1 hs₂.2.2.2.2.2.2.2.1 ht x v
  change fderiv ℝ (fun z => ((particleBySpacetime s₁.f-particleBySpacetime s₂.f) z)^2/2)
     ((t,x),v) _ = _
  rw [fderiv_square_half (hsp₁.sub hsp₂), fderiv_sub hsp₁ hsp₂]
  simp only [sub_apply,Pi.sub_apply,he₁,zero_sub]
  have hcross : cross (velocity v) (s₁.B (t,x)-s₂.B (t,x)) =
      cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)) := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [hcross]
  have hh : (((1:ℝ),velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      ((1,velocity v),s₂.E (t,x)+cross (velocity v) (s₂.B (t,x))) +
        ((0,0),(s₁.E (t,x)-s₂.E (t,x))+(cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)))) := by
    apply Prod.ext
    · simp
    · dsimp
      abel
  rw [hh,map_add,he₂,zero_add]
  have hv := fderiv_velocity_slice hsp₂
  change ∀ b, fderiv ℝ (fun v => s₂.f (t,x,v)) v b =
    fderiv ℝ (particleBySpacetime s₂.f) ((t,x),v) ((0,0),b) at hv
  rw [← hv]
  simp only [particleBySpacetime]
  ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_DifferenceFieldEnergy
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
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace RVM
lemma difference_source_pointwise {g L : ℝ} {D : Vec →L[ℝ] ℝ} {E B : Vec}
    (hL : 0 ≤ L) (hD : ‖D‖ ≤ L) (v : Vec) :
    -g*D (E+cross (velocity v) B)-dot E (g • velocity v) ≤
      (2*L+2)*(g^2/2+(‖E‖^2+‖B‖^2)/2) := by
  have hu := (norm_velocity_lt_one v).le
  have hK : ‖E+cross (velocity v) B‖ ≤ ‖E‖+‖B‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl
      ((norm_cross_le _ _).trans (mul_le_of_le_one_left (norm_nonneg B) hu)))
  have hd : |D (E+cross (velocity v) B)| ≤ L*(‖E‖+‖B‖) :=
    (D.le_opNorm _).trans (mul_le_mul hD hK (norm_nonneg _) hL)
  have hdot : |dot E (g • velocity v)| ≤ ‖E‖*|g| := by
    rw [dot_eq_inner]
    apply (abs_real_inner_le_norm _ _).trans
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg g) hu) (norm_nonneg E)
  have hab : |g| *(‖E‖+‖B‖) ≤ g^2+(‖E‖^2+‖B‖^2)/2 := by
    nlinarith [sq_nonneg (|g|-‖E‖),sq_nonneg (|g|-‖B‖),sq_abs g]
  calc
    _ ≤ |g| *|D (E+cross (velocity v) B)|+|dot E (g • velocity v)| := by
      have hh := neg_le_abs (g*D (E+cross (velocity v) B))
      rw [abs_mul] at hh
      linarith [neg_le_abs (dot E (g • velocity v))]
    _ ≤ |g| *(L*(‖E‖+‖B‖))+‖E‖*|g| :=
      add_le_add (mul_le_mul_of_nonneg_left hd (abs_nonneg g)) hdot
    _ ≤ (L+1)* (|g| *(‖E‖+‖B‖)) := by
      nlinarith [mul_nonneg (abs_nonneg g) (norm_nonneg B)]
    _ ≤ (L+1)*(g^2+(‖E‖^2+‖B‖^2)/2) :=
      mul_le_mul_of_nonneg_left hab (by linarith)
    _ ≤ _ := by nlinarith [sq_nonneg ‖E‖,sq_nonneg ‖B‖]

lemma compact_difference_source_bound
    {g : Vec → ℝ} {D : Vec → (Vec →L[ℝ] ℝ)} {K : Set Vec} {L : ℝ} (E B : Vec)
    (hg : Continuous g) (hD : Continuous D) (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v=0) (hL : 0 ≤ L) (hDb : ∀ v, ‖D v‖ ≤ L) :
    (∫ v : Vec, -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v)) ≤
      ((2*L+2)*(1+(volume K).toReal))*
        ((‖E‖^2+‖B‖^2)/2+(∫ v : Vec, (g v)^2/2)) := by
  let c : ℝ := (‖E‖^2+‖B‖^2)/2
  have hc : 0 ≤ c := div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
  have hgI : Integrable (fun v : Vec => (g v)^2/2) :=
    ((hg.pow 2).div_const 2).integrable_of_hasCompactSupport (by
      apply compactSupport_of_zero_off hK
      intro v hv
      simp [hz v hv])
  have hsC : Continuous (fun v : Vec => -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v)) := by
    apply Continuous.sub ((hg.neg).mul (hD.clm_apply (contDiff_lorentz (k := 1) E B).continuous))
    simp_rw [dot_eq_inner]
    exact continuous_const.inner (hg.smul (contDiff_velocity (k := 1)).continuous)
  have hs0 : ∀ v ∉ K, -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v) = 0 := by
    intro v hv
    simp [hz v hv,dot]
  have hsI : Integrable (fun v : Vec => -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v)) := hsC.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK hs0)
  have hcI : IntegrableOn (fun _ : Vec => c) K volume :=
    integrableOn_const hK.measure_lt_top.ne
  have hm : (∫ v : Vec, (g v)^2/2) ≥ 0 := integral_nonneg (fun v => by positivity)
  calc
    _ = ∫ v in K, -g v * D v (E+cross (velocity v) B)-dot E (g v • velocity v) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hs0).symm
    _ ≤ ∫ v in K, (2*L+2)*((g v)^2/2+c) := by
      apply integral_mono hsI.integrableOn ((hgI.integrableOn.add hcI).const_mul _)
      intro v
      exact difference_source_pointwise hL (hDb v) v
    _ = (2*L+2)*((∫ v : Vec, (g v)^2/2)+(volume K).toReal*c) := by
      rw [integral_const_mul,integral_add hgI.integrableOn hcI,
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun v hv => by simp [hz v hv]),
        integral_const]
      simp [measureReal_def]
    _ ≤ _ := by
      have hv := ENNReal.toReal_nonneg (a := volume K)
      dsimp [c] at *
      nlinarith [mul_nonneg hv hm,mul_nonneg (by linarith : 0 ≤ 2*L+2)
        (add_nonneg (mul_nonneg hv hm) hc)]

lemma squareDifference_regular {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) :
    RegularParticle (squareDifference s₁ s₂) := by
  refine ⟨((h₁.1.sub h₂.1).pow 2).div_const 2,?_⟩
  intro T hT
  obtain ⟨K₁,hK₁,hz₁⟩ := h₁.regularParticle.2 T hT
  obtain ⟨K₂,hK₂,hz₂⟩ := h₂.regularParticle.2 T hT
  refine ⟨K₁ ∪ K₂,hK₁.union hK₂,?_⟩
  intro t ht
  apply closure_minimal ?_ (hK₁.union hK₂).isClosed
  intro z hz
  by_contra hn
  have hf₁ : s₁.f (t,z)=0 := image_eq_zero_of_notMem_tsupport (f := fun z => s₁.f (t,z))
    (fun hh => hn (Or.inl (hz₁ t ht hh)))
  have hf₂ : s₂.f (t,z)=0 := image_eq_zero_of_notMem_tsupport (f := fun z => s₂.f (t,z))
    (fun hh => hn (Or.inr (hz₂ t ht hh)))
  exact hz (by simp [squareDifference,hf₁,hf₂])

lemma particleMoment_one (f : Particle) (p : ℝ × Vec) :
    particleMoment f (fun _ => (1:ℝ)) p = ∫ v : Vec, f (p.1,p.2,v) := by
  simp [particleMoment]

lemma RegularParticle.moment_component {f : Particle} (hf : RegularParticle f)
    {w : Vec → Vec} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) (x : Vec) (i : Fin 3) :
    particleMoment f w (t,x) i = ∫ v : Vec, w v i * f (t,x,v) := by
  have hi := hf.moment_integrable hw ht x
  have he := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hi
  simpa [particleMoment,mul_comm] using he.symm

lemma particle_difference_local {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 < t) (x : Vec) :
    deriv (fun r => particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (r,x)) t +
      divergence (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x =
      ∫ v : Vec, -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hf := squareDifference_regular h₁ h₂
  obtain ⟨U,K,hU,hK,hp,hF,hz⟩ := hf.local_data ht x
  have he := particle_number_balance_param (s₁.E (t,x)) (s₁.B (t,x)) hU hK hp hF hz
  have he' : (∫ v : Vec, fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x)))) = _ :=
    integral_congr_ae (Filter.Eventually.of_forall (particle_difference_direction h₁ h₂ ht x))
  rw [he'] at he
  have hn := (hf.moment_regular (w := fun _ => (1:ℝ)) contDiff_const).contDiffAt (x := (t,x))
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  rw [deriv_time_slice (hn.differentiableAt (by simp))]
  apply Eq.trans ?_ he
  congr 1
  · congr 2
    ext p
    exact particleMoment_one _ p
  · apply Finset.sum_congr rfl
    intro i _
    have hflux := (hf.moment_regular contDiff_velocity).contDiffAt (x := (t,x))
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
    have hc : DifferentiableAt ℝ (fun p => particleMoment (squareDifference s₁ s₂) velocity p i) (t,x) :=
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (t,x)
        (hflux.differentiableAt (by simp))
    rw [spatialPartial_time_slice hc]
    have heq : (fun p : ℝ × Vec => particleMoment (squareDifference s₁ s₂) velocity p i) =ᶠ[nhds (t,x)]
        (fun p => ∫ v : Vec, velocity v i * particleBySpacetime (squareDifference s₁ s₂) (p,v)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds ht] with p hp
      exact hf.moment_component (contDiff_velocity (k := 1)).continuous hp.le p.2 i
    rw [heq.fderiv_eq (𝕜 := ℝ)]

lemma curl_sub {F G : Vec → Vec} {x : Vec}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) :
    curl (F-G) x = curl F x - curl G x := by
  have h (i : Fin 3) : fderiv ℝ (fun y => F y i-G y i) x =
      fderiv ℝ (fun y => F y i) x - fderiv ℝ (fun y => G y i) x := by
    exact fderiv_sub
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hF)
      ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp x hG)
  ext i
  fin_cases i <;> simp [curl,spatialPartial,h] <;> ring

lemma difference_maxwell_local {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 < t) (x : Vec) :
    deriv (fun r => (‖s₁.E (r,x)-s₂.E (r,x)‖^2+‖s₁.B (r,x)-s₂.B (r,x)‖^2)/2) t +
      divergence (fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y))) x =
        -dot (s₁.E (t,x)-s₂.E (t,x))
          (current (fun z => s₁.f (t,z)) x-current (fun z => s₂.f (t,z)) x) := by
  have hE₁ := field_differentiableAt_positive h₁.2.1 ht x
  have hB₁ := field_differentiableAt_positive h₁.2.2.1 ht x
  have hE₂ := field_differentiableAt_positive h₂.2.1 ht x
  have hB₂ := field_differentiableAt_positive h₂.2.2.1 ht x
  have hE₁t : DifferentiableAt ℝ (fun r : ℝ => s₁.E (r,x)) t := hE₁.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hB₁t : DifferentiableAt ℝ (fun r : ℝ => s₁.B (r,x)) t := hB₁.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hE₂t : DifferentiableAt ℝ (fun r : ℝ => s₂.E (r,x)) t := hE₂.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hB₂t : DifferentiableAt ℝ (fun r : ℝ => s₂.B (r,x)) t := hB₂.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hE₁x : DifferentiableAt ℝ (fun y : Vec => s₁.E (t,y)) x := hE₁.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hB₁x : DifferentiableAt ℝ (fun y : Vec => s₁.B (t,y)) x := hB₁.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hE₂x : DifferentiableAt ℝ (fun y : Vec => s₂.E (t,y)) x := hE₂.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hB₂x : DifferentiableAt ℝ (fun y : Vec => s₂.B (t,y)) x := hB₂.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have he₁ := (h₁.2.2.2.2.2.2.2.1 t ht.le).2.1 x
  have hb₁ := (h₁.2.2.2.2.2.2.2.1 t ht.le).2.2.1 x
  have he₂ := (h₂.2.2.2.2.2.2.2.1 t ht.le).2.1 x
  have hb₂ := (h₂.2.2.2.2.2.2.2.1 t ht.le).2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he₁ hb₁ he₂ hb₂
  apply maxwell_energy_balance (E := s₁.E-s₂.E) (B := s₁.B-s₂.B) (hE₁.sub hE₂) (hB₁.sub hB₂)
  · change deriv ((fun r => s₁.E (r,x))-(fun r => s₂.E (r,x))) t -
      curl ((fun y => s₁.B (t,y))-(fun y => s₂.B (t,y))) x = _
    rw [deriv_sub hE₁t hE₂t,curl_sub hB₁x hB₂x]
    calc
      _ = (deriv (fun r => s₁.E (r,x)) t-curl (fun y => s₁.B (t,y)) x)-
        (deriv (fun r => s₂.E (r,x)) t-curl (fun y => s₂.B (t,y)) x) := by abel
      _ = _ := by rw [he₁,he₂]; abel
  · change deriv ((fun r => s₁.B (r,x))-(fun r => s₂.B (r,x))) t +
      curl ((fun y => s₁.E (t,y))-(fun y => s₂.E (t,y))) x = _
    rw [deriv_sub hB₁t hB₂t,curl_sub hE₁x hE₂x]
    calc
      _ = (deriv (fun r => s₁.B (r,x)) t+curl (fun y => s₁.E (t,y)) x)-
        (deriv (fun r => s₂.B (r,x)) t+curl (fun y => s₂.E (t,y)) x) := by abel
      _ = _ := by rw [hb₁,hb₂]; simp

lemma differenceFieldEnergy_nonneg (s₁ s₂ : Solution) (p : ℝ × Vec) :
    0 ≤ differenceFieldEnergy s₁ s₂ p := by
  exact div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)

lemma differenceEnergy_nonneg (s₁ s₂ : Solution) (p : ℝ × Vec) :
    0 ≤ differenceEnergy s₁ s₂ p := by
  apply add_nonneg (differenceFieldEnergy_nonneg _ _ _)
  rw [particleMoment_one]
  exact integral_nonneg (fun v => squareDifference_nonneg _ _ _)

lemma differenceEnergy_regular {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) :
    ContDiffOn ℝ 1 (differenceEnergy s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.sub h₂.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  have hb := (h₁.2.2.1.sub h₂.2.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  exact ((he.norm_sq ℝ).add (hb.norm_sq ℝ)).div_const 2 |>.add
    ((squareDifference_regular h₁ h₂).moment_regular contDiff_const)

lemma differenceFlux_regular {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) :
    ContDiffOn ℝ 1 (differenceFlux s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.sub h₂.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  have hb := (h₁.2.2.1.sub h₂.2.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  exact ((contDiff_cross (k := 1)).contDiffOn.comp (he.prodMk hb)
    (fun _ _ => mem_univ _)).add
      ((squareDifference_regular h₁ h₂).moment_regular contDiff_velocity)

lemma differenceEnergy_continuous_slab {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (differenceEnergy s₁ s₂) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.continuousOn.sub h₂.2.1.continuousOn).mono
    (show Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => hp.1.1)
  have hb := (h₁.2.2.1.continuousOn.sub h₂.2.2.1.continuousOn).mono
    (show Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => hp.1.1)
  exact ((he.norm.pow 2).add (hb.norm.pow 2)).div_const 2 |>.add
    ((squareDifference_regular h₁ h₂).moment_continuous_slab continuous_const hT)

lemma differenceEnergy_integrable {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Vec => differenceEnergy s₁ s₂ (t,x)) := by
  exact (((h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).integrable_norm_sq ht).add
    ((h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).integrable_norm_sq ht)).div_const 2 |>.add
      ((squareDifference_regular h₁ h₂).spatial_moment_integrable continuous_const ht)

lemma differenceEnergy_integrated_continuous {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x : Vec, differenceEnergy s₁ s₂ (t,x)) (Icc 0 T) := by
  have he := (h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).continuous_integral_norm_sq.mono
    (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  have hb := (h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).continuous_integral_norm_sq.mono
    (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  have hp := (squareDifference_regular h₁ h₂).integrated_moment_continuous
    (w := fun _ => (1:ℝ)) continuous_const hT
  apply ((he.add hb).div_const 2 |>.add hp).congr
  intro t ht
  change (∫ x : Vec, (‖(s₁.E-s₂.E) (t,x)‖^2+‖(s₁.B-s₂.B) (t,x)‖^2)/2+
    particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)) = _
  have hiE := (h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).integrable_norm_sq ht.1
  have hiB := (h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).integrable_norm_sq ht.1
  have hiP := (squareDifference_regular h₁ h₂).spatial_moment_integrable
    (w := fun _ => (1:ℝ)) continuous_const ht.1
  calc
    _ = (∫ x : Vec, (‖(s₁.E-s₂.E) (t,x)‖^2+‖(s₁.B-s₂.B) (t,x)‖^2)/2)+
      (∫ x : Vec, particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)) :=
        integral_add ((hiE.add hiB).div_const 2) hiP
    _ = _ := by rw [integral_div,integral_add hiE hiB]; rfl

lemma differenceFlux_bound {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ‖differenceFlux s₁ s₂ (t,x)‖ ≤ differenceEnergy s₁ s₂ (t,x) := by
  apply (norm_add_le _ _).trans
  apply add_le_add ?_ ((squareDifference_regular h₁ h₂).velocity_flux_bound ht x
    (fun v => squareDifference_nonneg _ _ _))
  apply (norm_cross_le _ _).trans
  dsimp [differenceFieldEnergy]
  nlinarith [sq_nonneg (‖s₁.E (t,x)-s₂.E (t,x)‖-‖s₁.B (t,x)-s₂.B (t,x)‖)]

lemma differenceEnergy_initial {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) (x : Vec) :
    differenceEnergy s₁ s₂ (0,x) = 0 := by
  have hf (v : Vec) : squareDifference s₁ s₂ (0,x,v)=0 := by
    rw [squareDifference_zero_iff,h₁.2.2.2.2.2.2.2.2.1,h₂.2.2.2.2.2.2.2.2.1]
  simp [differenceEnergy,differenceFieldEnergy,particleMoment_one,hf,
    h₁.2.2.2.2.2.2.2.2.2.1,h₁.2.2.2.2.2.2.2.2.2.2,
    h₂.2.2.2.2.2.2.2.2.2.1,h₂.2.2.2.2.2.2.2.2.2.2]

lemma differenceEnergy_local {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 < t) (x : Vec) :
    fderiv ℝ (differenceEnergy s₁ s₂) (t,x) (1,0)+
      divergence (fun y => differenceFlux s₁ s₂ (t,y)) x =
      ∫ v : Vec, -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) -
        dot (s₁.E (t,x)-s₂.E (t,x)) ((s₁.f (t,x,v)-s₂.f (t,x,v)) • velocity v) := by
  have hE := (field_differentiableAt_positive h₁.2.1 ht x).sub
    (field_differentiableAt_positive h₂.2.1 ht x)
  have hB := (field_differentiableAt_positive h₁.2.2.1 ht x).sub
    (field_differentiableAt_positive h₂.2.2.1 ht x)
  have hfield : DifferentiableAt ℝ (differenceFieldEnergy s₁ s₂) (t,x) := by
    unfold differenceFieldEnergy
    convert ((hE.norm_sq (𝕜 := ℝ)).add (hB.norm_sq (𝕜 := ℝ))).mul_const (2 : ℝ)⁻¹ using 1 <;> try rfl
  have hpart := ((squareDifference_regular h₁ h₂).moment_regular
    (w := fun _ => (1:ℝ)) contDiff_const).contDiffAt (x := (t,x))
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  have hflux := ((squareDifference_regular h₁ h₂).moment_regular contDiff_velocity).contDiffAt
    (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  have hcross : DifferentiableAt ℝ (fun p => cross (s₁.E p-s₂.E p) (s₁.B p-s₂.B p)) (t,x) :=
    (contDiff_cross (k := 1)).differentiable (by simp) _ |>.comp (t,x) (hE.prodMk hB)
  have hp := particle_difference_local h₁ h₂ ht x
  have hm := difference_maxwell_local h₁ h₂ ht x
  rw [deriv_time_slice (hpart.differentiableAt (by simp))] at hp
  change deriv (fun r => differenceFieldEnergy s₁ s₂ (r,x)) t + _ = _ at hm
  rw [deriv_time_slice hfield] at hm
  have hs₁ := h₁.regularParticle.slice ht.le x
  have hs₂ := h₂.regularParticle.slice ht.le x
  let g : Vec → ℝ := fun v => s₁.f (t,x,v)-s₂.f (t,x,v)
  have hgc : Continuous g := hs₁.1.continuous.sub hs₂.1.continuous
  have hgK : HasCompactSupport g := hs₁.2.sub hs₂.2
  have hdc : Continuous (fun v => fderiv ℝ (fun w => s₂.f (t,x,w)) v) :=
    hs₂.1.continuous_fderiv (by simp)
  have hi : Integrable (fun v => -g v * fderiv ℝ (fun w => s₂.f (t,x,w)) v
      ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x)))) :=
    (hgc.neg.mul (hdc.clm_apply (contDiff_lorentz (k := 1) _ _).continuous)).integrable_of_hasCompactSupport
      hgK.neg.mul_right
  have hjI : Integrable (fun v => g v • velocity v) :=
    (hgc.smul (contDiff_velocity (k := 1)).continuous).integrable_of_hasCompactSupport hgK.smul_right
  have hjdI : Integrable (fun v => dot (s₁.E (t,x)-s₂.E (t,x)) (g v • velocity v)) := by
    simp only [dot_eq_inner]
    exact hjI.const_inner _
  have hj : (∫ v : Vec, g v • velocity v) =
      current (fun z => s₁.f (t,z)) x-current (fun z => s₂.f (t,z)) x := by
    simp only [g,sub_smul,current]
    exact integral_sub
      (h₁.regularParticle.moment_integrable (contDiff_velocity (k := 1)).continuous ht.le x)
      (h₂.regularParticle.moment_integrable (contDiff_velocity (k := 1)).continuous ht.le x)
  have hdot : (∫ v : Vec, dot (s₁.E (t,x)-s₂.E (t,x)) (g v • velocity v)) =
      dot (s₁.E (t,x)-s₂.E (t,x))
        (current (fun z => s₁.f (t,z)) x-current (fun z => s₂.f (t,z)) x) := by
    simp only [dot_eq_inner]
    rw [integral_inner hjI,hj]
  change (fderiv ℝ (differenceFieldEnergy s₁ s₂+
    particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ))) (t,x)) (1,0) +
    divergence ((fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y)))+
      fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x = _
  have hxs : DifferentiableAt ℝ (fun y => cross (s₁.E (t,y)-s₂.E (t,y))
      (s₁.B (t,y)-s₂.B (t,y))) x :=
    hcross.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hvs : DifferentiableAt ℝ (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x :=
    (hflux.differentiableAt (by simp)).comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  rw [fderiv_add hfield (hpart.differentiableAt (by simp)),add_apply]
  have hvdiv : divergence ((fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y)))+
      fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x =
        divergence (fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y))) x+
        divergence (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x := by
    exact divergence_add hxs hvs
  rw [hvdiv]
  change _ = ∫ v : Vec, -g v * fderiv ℝ (fun w => s₂.f (t,x,w)) v
    ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) -
      dot (s₁.E (t,x)-s₂.E (t,x)) (g v • velocity v)
  rw [integral_sub hi hjdI,hdot]
  dsimp [g] at *
  linarith

lemma differenceEnergy_zero {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {t : ℝ} (ht : 0 ≤ t) (x : Vec)
    (hz : differenceEnergy s₁ s₂ (t,x)=0) :
    s₁.E (t,x)=s₂.E (t,x) ∧ s₁.B (t,x)=s₂.B (t,x) ∧ ∀ v, s₁.f (t,x,v)=s₂.f (t,x,v) := by
  have hp : 0 ≤ (∫ v : Vec, squareDifference s₁ s₂ (t,x,v)) :=
    integral_nonneg (fun v => squareDifference_nonneg _ _ _)
  have he := differenceFieldEnergy_nonneg s₁ s₂ (t,x)
  change differenceFieldEnergy s₁ s₂ (t,x)+particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)=0 at hz
  rw [particleMoment_one] at hz
  have hp0 : (∫ v : Vec, squareDifference s₁ s₂ (t,x,v))=0 := by linarith
  have he0 : differenceFieldEnergy s₁ s₂ (t,x)=0 := by linarith
  have heq : s₁.E (t,x)=s₂.E (t,x) := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    dsimp [differenceFieldEnergy] at he0
    nlinarith [sq_nonneg ‖s₁.B (t,x)-s₂.B (t,x)‖,norm_nonneg (s₁.E (t,x)-s₂.E (t,x))]
  have hbq : s₁.B (t,x)=s₂.B (t,x) := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    dsimp [differenceFieldEnergy] at he0
    nlinarith [sq_nonneg ‖s₁.E (t,x)-s₂.E (t,x)‖,norm_nonneg (s₁.B (t,x)-s₂.B (t,x))]
  refine ⟨heq,hbq,?_⟩
  have hs := (squareDifference_regular h₁ h₂).slice ht x
  have hi : Integrable (fun v : Vec => squareDifference s₁ s₂ (t,x,v)) :=
    hs.1.continuous.integrable_of_hasCompactSupport hs.2
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => squareDifference_nonneg s₁ s₂ (t,x,v)) hi).mp hp0
  have hevery := Measure.eq_of_ae_eq (μ := volume) hae hs.1.continuous continuous_const
  intro v
  exact (squareDifference_zero_iff _ _ _).mp (congrFun hevery v)

lemma differenceEnergy_differential_bound {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo 0 T, ∀ x : Vec,
      fderiv ℝ (differenceEnergy s₁ s₂) (t,x) (1,0)+
        divergence (fun y => differenceFlux s₁ s₂ (t,y)) x ≤
          C*differenceEnergy s₁ s₂ (t,x) := by
  obtain ⟨K₁,hK₁,hs₁⟩ := h₁.regularParticle.2 T hT
  obtain ⟨K₂,hK₂,hs₂⟩ := h₂.regularParticle.2 T hT
  let K : Set Vec := Prod.snd '' (K₁ ∪ K₂)
  have hK : IsCompact K := (hK₁.union hK₂).image continuous_snd
  obtain ⟨L,hL,hLb⟩ := h₂.regularParticle.velocity_derivative_bound hT
  refine ⟨(2*L+2)*(1+(volume K).toReal),by positivity,?_⟩
  intro t ht x
  rw [differenceEnergy_local h₁ h₂ ht.1 x]
  have hf₁ := h₁.regularParticle.slice ht.1.le x
  have hf₂ := h₂.regularParticle.slice ht.1.le x
  have hz : ∀ v ∉ K, s₁.f (t,x,v)-s₂.f (t,x,v)=0 := by
    intro v hv
    have hnot₁ : (x,v) ∉ tsupport (fun z => s₁.f (t,z)) := by
      intro hh
      exact hv ⟨(x,v),Or.inl (hs₁ t ⟨ht.1.le,ht.2.le⟩ hh),rfl⟩
    have hnot₂ : (x,v) ∉ tsupport (fun z => s₂.f (t,z)) := by
      intro hh
      exact hv ⟨(x,v),Or.inr (hs₂ t ⟨ht.1.le,ht.2.le⟩ hh),rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hnot₁,image_eq_zero_of_notMem_tsupport hnot₂,sub_self]
  have hb := compact_difference_source_bound (s₁.E (t,x)-s₂.E (t,x))
    (s₁.B (t,x)-s₂.B (t,x)) (hf₁.1.continuous.sub hf₂.1.continuous)
    (hf₂.1.continuous_fderiv (by simp)) hK hz hL (hLb t ht x)
  simpa only [differenceEnergy,differenceFieldEnergy,particleMoment_one,squareDifference,Pi.sub_apply] using hb

theorem classical_unique {d : Datum} {s₁ s₂ : Solution}
    (h₁ : Classical d s₁) (h₂ : Classical d s₂) : SameNonnegativeTime s₁ s₂ := by
  intro T hT
  obtain ⟨C,hC,hbound⟩ := differenceEnergy_differential_bound h₁ h₂ hT
  have hz := local_energy_inequality_vanishes hC hT
    (differenceEnergy_regular h₁ h₂) (differenceFlux_regular h₁ h₂)
    (differenceEnergy_continuous_slab h₁ h₂ hT)
    (fun _ _ _ => differenceEnergy_nonneg _ _ _)
    (fun _ ht => differenceEnergy_integrable h₁ h₂ ht.1)
    (differenceEnergy_integrated_continuous h₁ h₂ hT)
    (fun _ ht => differenceFlux_bound h₁ h₂ ht.1.le)
    hbound (differenceEnergy_initial h₁ h₂)
  have heq (x : Vec) := differenceEnergy_zero h₁ h₂ hT x (hz x)
  exact ⟨fun z => (heq z.1).2.2 z.2,fun x => (heq x).1,fun x => (heq x).2.1⟩

end RVM

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PositiveExtension
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

end PositiveExtension

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

lemma ClassicalBefore.regularParticle {d : Datum} {s : Solution} {H : ℝ}
    (hs : ClassicalBefore d s H) : RegularParticle s.f := ⟨hs.1,hs.2.2.2.2.2.2.1⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_UpperTimeCut
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

lemma contDiff_upperTimeCut (τ H : ℝ) : ContDiff ℝ ∞ (upperTimeCut τ H) :=
  (contDiff_positiveTimeCut _).comp (contDiff_const.sub contDiff_id)

lemma upperTimeCut_nonneg (τ H t : ℝ) : 0 ≤ upperTimeCut τ H t :=
  Real.smoothTransition.nonneg _

lemma upperTimeCut_one {τ H t : ℝ} (hτ : τ < H) (ht : t ≤ τ) :
    upperTimeCut τ H t = 1 := by
  apply positiveTimeCut_one (by linarith)
  linarith

lemma upperTimeCut_zero {τ H t : ℝ} (hτ : τ < H) (ht : (τ+H)/2 ≤ t) :
    upperTimeCut τ H t = 0 := by
  apply positiveTimeCut_zero (by linarith)
  linarith

section Generic
variable {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma upperTimeExtend_eq {τ H t : ℝ} (hτ : τ < H) (ht : t ≤ τ)
    (F : ℝ × X → W) (x : X) : upperTimeExtend τ H F (t,x)=F (t,x) := by
  simp only [upperTimeExtend,upperTimeCut_one hτ ht,one_smul]

omit [NormedSpace ℝ X] in
lemma upperTimeExtend_eventually_zero {τ H : ℝ} (hτ : τ < H)
    (F : ℝ × X → W) {p : ℝ × X} (hp : (τ+H)/2 < p.1) :
    upperTimeExtend τ H F =ᶠ[𝓝 p] (fun _ => 0) := by
  filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
  simp only [upperTimeExtend,upperTimeCut_zero hτ hq.le,zero_smul]

lemma contDiffOn_upperTimeExtend {τ H : ℝ} (hτ : τ < H) {F : ℝ × X → W}
    (hF : ContDiffOn ℝ ∞ F {p | p.1 ∈ Icc 0 H}) :
    ContDiffOn ℝ ∞ (upperTimeExtend τ H F) {p | 0 ≤ p.1} := by
  intro p hp
  by_cases hpt : p.1 < H
  · have hlocal : {q : ℝ × X | q.1 ∈ Icc 0 H} ∈ 𝓝[{q | 0 ≤ q.1}] p := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_fst continuous_const).mem_nhds hpt),
        self_mem_nhdsWithin] with q hq hq0
      exact ⟨hq0,hq.le⟩
    exact (((contDiff_upperTimeCut τ H).comp contDiff_fst).contDiffAt.contDiffWithinAt).smul
      ((hF p ⟨hp,hpt.le⟩).mono_of_mem_nhdsWithin hlocal)
  · exact (contDiffAt_const.congr_of_eventuallyEq
      (upperTimeExtend_eventually_zero hτ F (show (τ+H)/2 < p.1 by linarith))).contDiffWithinAt

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma derivWithin_upperTimeExtend {τ H t : ℝ} (hτ : τ < H) (ht : t < τ)
    (F : ℝ × X → W) (x : X) (S : Set ℝ) :
    derivWithin (fun r => upperTimeExtend τ H F (r,x)) S t =
      derivWithin (fun r => F (r,x)) S t := by
  have he : (fun r => upperTimeExtend τ H F (r,x)) =ᶠ[𝓝 t] (fun r => F (r,x)) := by
    filter_upwards [Iio_mem_nhds ht] with r hr
    exact upperTimeExtend_eq hτ hr.le F x
  exact he.filter_mono nhdsWithin_le_nhds |>.derivWithin_eq (upperTimeExtend_eq hτ ht.le F x)
end Generic

lemma timeContinuousL2_upperTimeExtend {τ H : ℝ} (hτ : τ < H) (hH : 0 ≤ H)
    {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec),
      ContinuousOn F₂ (Icc 0 H) ∧ ∀ t ∈ Icc 0 H,
        (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x))) :
    TimeContinuousL2 (upperTimeExtend τ H F) := by
  obtain ⟨F₂,hc,he⟩ := hF
  refine ⟨fun t => upperTimeCut τ H t • F₂ (min t H),?_,?_⟩
  · exact (contDiff_upperTimeCut τ H).continuous.continuousOn.smul
      (hc.comp (continuous_id.min continuous_const).continuousOn
        (fun t ht => ⟨le_min ht hH,min_le_right _ _⟩))
  · intro t ht
    have hl := Lp.coeFn_smul (upperTimeCut τ H t) (F₂ (min t H))
    by_cases htH : t ≤ H
    · rw [min_eq_left htH] at hl
      filter_upwards [hl,he t ⟨ht,htH⟩] with x hx hx'
      simpa only [min_eq_left htH,upperTimeExtend,Pi.smul_apply,hx'] using hx
    · have hz := upperTimeCut_zero hτ (show (τ+H)/2 ≤ t by linarith)
      filter_upwards [hl] with x hx
      simpa only [hz,upperTimeExtend,zero_smul,Pi.zero_apply,Pi.smul_apply] using hx

lemma cutoffPrefix_eq {τ H t : ℝ} (hτH : τ < H) (ht : t ≤ τ) (s : Solution) :
    (∀ z, (cutoffPrefix τ H s).f (t,z)=s.f (t,z)) ∧
    (∀ x, (cutoffPrefix τ H s).E (t,x)=s.E (t,x)) ∧
    (∀ x, (cutoffPrefix τ H s).B (t,x)=s.B (t,x)) :=
  ⟨upperTimeExtend_eq hτH ht s.f,upperTimeExtend_eq hτH ht s.E,
    upperTimeExtend_eq hτH ht s.B⟩

lemma cutoffPrefix_equations {s : Solution} {τ H : ℝ} (hτH : τ < H)
    (hs : EquationsBefore s H) : EquationsBefore (cutoffPrefix τ H s) τ := by
  intro t ht htτ
  have hh := hs t ht (htτ.trans hτH)
  have hf (x v : Vec) := derivWithin_upperTimeExtend hτH htτ s.f (x,v) (Ici 0)
  have hE (x : Vec) := derivWithin_upperTimeExtend hτH htτ s.E x (Ici 0)
  have hB (x : Vec) := derivWithin_upperTimeExtend hτH htτ s.B x (Ici 0)
  change (∀ x v, derivWithin (fun r => upperTimeExtend τ H s.f (r,x,v)) (Ici 0) t + _ + _ = 0) ∧ _
  simp only [cutoffPrefix]
  simp only [hf,hE,hB]
  simpa only [upperTimeExtend,upperTimeCut_one hτH htτ.le,one_smul] using hh

lemma SmoothClassicalPrefix.cutoff_classical_before {d : Datum} {s : Solution} {τ H : ℝ}
    (hs : SmoothClassicalPrefix d s H) (hτ : 0 ≤ τ) (hτH : τ < H) :
    ClassicalBefore d (cutoffPrefix τ H s) τ := by
  have hH : 0 ≤ H := hτ.trans hτH.le
  refine ⟨(contDiffOn_upperTimeExtend hτH hs.f_smooth).of_le (by decide),
    (contDiffOn_upperTimeExtend hτH hs.E_smooth).of_le (by decide),
    (contDiffOn_upperTimeExtend hτH hs.B_smooth).of_le (by decide),?_,
    timeContinuousL2_upperTimeExtend hτH hH hs.E_L2,
    timeContinuousL2_upperTimeExtend hτH hH hs.B_L2,?_,
    cutoffPrefix_equations hτH hs.equations,?_,?_,?_⟩
  · intro t ht z
    by_cases htH : t ≤ H
    · exact mul_nonneg (upperTimeCut_nonneg τ H t) (hs.nonnegative t ⟨ht,htH⟩ z)
    · simp only [cutoffPrefix,upperTimeExtend,
        upperTimeCut_zero hτH (show (τ+H)/2 ≤ t by linarith),zero_smul,le_refl]
  · obtain ⟨K,hK,hk⟩ := hs.compact
    intro T _hT
    refine ⟨K,hK,?_⟩
    intro t ht
    by_cases htH : t ≤ H
    · exact (tsupport_smul_subset_right (fun _ : Phase => upperTimeCut τ H t)
        (fun z => s.f (t,z))).trans (hk t ⟨ht.1,htH⟩)
    · simp only [cutoffPrefix,upperTimeExtend,
        upperTimeCut_zero hτH (show (τ+H)/2 ≤ t by linarith),zero_smul]
      change tsupport (0 : Phase → ℝ) ⊆ K
      simp only [tsupport_zero,empty_subset]
  · intro z
    exact (cutoffPrefix_eq hτH hτ s).1 z |>.trans (hs.initial_f z)
  · intro x
    exact (cutoffPrefix_eq hτH hτ s).2.1 x |>.trans (hs.initial_E x)
  · intro x
    exact (cutoffPrefix_eq hτH hτ s).2.2 x |>.trans (hs.initial_B x)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_FiniteUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma particle_difference_direction_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (hs₁ : ClassicalBefore d s₁ H) (hs₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x v : Vec) :
    fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hd₁ := particle_differentiableAt_positive hs₁.1 ht x v
  have hd₂ := particle_differentiableAt_positive hs₂.1 ht x v
  have hsp₁ : DifferentiableAt ℝ (particleBySpacetime s₁.f) ((t,x),v) :=
    (hd₁.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have hsp₂ : DifferentiableAt ℝ (particleBySpacetime s₂.f) ((t,x),v) :=
    (hd₂.comp ((t,x),v) ((contDiff_reassociate (k := 1)).differentiable (by simp) _))
  have he₁ := particle_spacetime_vlasov_before hs₁.1 hs₁.2.2.2.2.2.2.2.1 ht hth x v
  have he₂ := particle_spacetime_vlasov_before hs₂.1 hs₂.2.2.2.2.2.2.2.1 ht hth x v
  change fderiv ℝ (fun z => ((particleBySpacetime s₁.f-particleBySpacetime s₂.f) z)^2/2)
     ((t,x),v) _ = _
  rw [fderiv_square_half (hsp₁.sub hsp₂), fderiv_sub hsp₁ hsp₂]
  simp only [sub_apply,Pi.sub_apply,he₁,zero_sub]
  have hcross : cross (velocity v) (s₁.B (t,x)-s₂.B (t,x)) =
      cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)) := by
    ext i; fin_cases i <;> simp [cross] <;> ring
  rw [hcross]
  have hh : (((1:ℝ),velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x))) =
      ((1,velocity v),s₂.E (t,x)+cross (velocity v) (s₂.B (t,x))) +
        ((0,0),(s₁.E (t,x)-s₂.E (t,x))+(cross (velocity v) (s₁.B (t,x))-cross (velocity v) (s₂.B (t,x)))) := by
    apply Prod.ext
    · simp
    · dsimp
      abel
  rw [hh,map_add,he₂,zero_add]
  have hv := fderiv_velocity_slice hsp₂
  change ∀ b, fderiv ℝ (fun v => s₂.f (t,x,v)) v b =
    fderiv ℝ (particleBySpacetime s₂.f) ((t,x),v) ((0,0),b) at hv
  rw [← hv]
  simp only [particleBySpacetime]
  ring

lemma squareDifference_regular_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) :
    RegularParticle (squareDifference s₁ s₂) := by
  refine ⟨((h₁.1.sub h₂.1).pow 2).div_const 2,?_⟩
  intro T hT
  obtain ⟨K₁,hK₁,hz₁⟩ := h₁.regularParticle.2 T hT
  obtain ⟨K₂,hK₂,hz₂⟩ := h₂.regularParticle.2 T hT
  refine ⟨K₁ ∪ K₂,hK₁.union hK₂,?_⟩
  intro t ht
  apply closure_minimal ?_ (hK₁.union hK₂).isClosed
  intro z hz
  by_contra hn
  have hf₁ : s₁.f (t,z)=0 := image_eq_zero_of_notMem_tsupport (f := fun z => s₁.f (t,z))
    (fun hh => hn (Or.inl (hz₁ t ht hh)))
  have hf₂ : s₂.f (t,z)=0 := image_eq_zero_of_notMem_tsupport (f := fun z => s₂.f (t,z))
    (fun hh => hn (Or.inr (hz₂ t ht hh)))
  exact hz (by simp [squareDifference,hf₁,hf₂])

lemma particle_difference_local_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x : Vec) :
    deriv (fun r => particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (r,x)) t +
      divergence (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x =
      ∫ v : Vec, -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) := by
  have hf := squareDifference_regular_before h₁ h₂
  obtain ⟨U,K,hU,hK,hp,hF,hz⟩ := hf.local_data ht x
  have he := particle_number_balance_param (s₁.E (t,x)) (s₁.B (t,x)) hU hK hp hF hz
  have he' : (∫ v : Vec, fderiv ℝ (particleBySpacetime (squareDifference s₁ s₂)) ((t,x),v)
      ((1,velocity v),s₁.E (t,x)+cross (velocity v) (s₁.B (t,x)))) = _ :=
    integral_congr_ae (Filter.Eventually.of_forall (particle_difference_direction_before h₁ h₂ ht hth x))
  rw [he'] at he
  have hn := (hf.moment_regular (w := fun _ => (1:ℝ)) contDiff_const).contDiffAt (x := (t,x))
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  rw [deriv_time_slice (hn.differentiableAt (by simp))]
  apply Eq.trans ?_ he
  congr 1
  · congr 2
    ext p
    exact particleMoment_one _ p
  · apply Finset.sum_congr rfl
    intro i _
    have hflux := (hf.moment_regular contDiff_velocity).contDiffAt (x := (t,x))
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
    have hc : DifferentiableAt ℝ (fun p => particleMoment (squareDifference s₁ s₂) velocity p i) (t,x) :=
      (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (t,x)
        (hflux.differentiableAt (by simp))
    rw [spatialPartial_time_slice hc]
    have heq : (fun p : ℝ × Vec => particleMoment (squareDifference s₁ s₂) velocity p i) =ᶠ[nhds (t,x)]
        (fun p => ∫ v : Vec, velocity v i * particleBySpacetime (squareDifference s₁ s₂) (p,v)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds ht] with p hp
      exact hf.moment_component (contDiff_velocity (k := 1)).continuous hp.le p.2 i
    rw [heq.fderiv_eq (𝕜 := ℝ)]

lemma difference_maxwell_local_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x : Vec) :
    deriv (fun r => (‖s₁.E (r,x)-s₂.E (r,x)‖^2+‖s₁.B (r,x)-s₂.B (r,x)‖^2)/2) t +
      divergence (fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y))) x =
        -dot (s₁.E (t,x)-s₂.E (t,x))
          (current (fun z => s₁.f (t,z)) x-current (fun z => s₂.f (t,z)) x) := by
  have hE₁ := field_differentiableAt_positive h₁.2.1 ht x
  have hB₁ := field_differentiableAt_positive h₁.2.2.1 ht x
  have hE₂ := field_differentiableAt_positive h₂.2.1 ht x
  have hB₂ := field_differentiableAt_positive h₂.2.2.1 ht x
  have hE₁t : DifferentiableAt ℝ (fun r : ℝ => s₁.E (r,x)) t := hE₁.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hB₁t : DifferentiableAt ℝ (fun r : ℝ => s₁.B (r,x)) t := hB₁.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hE₂t : DifferentiableAt ℝ (fun r : ℝ => s₂.E (r,x)) t := hE₂.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hB₂t : DifferentiableAt ℝ (fun r : ℝ => s₂.B (r,x)) t := hB₂.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hE₁x : DifferentiableAt ℝ (fun y : Vec => s₁.E (t,y)) x := hE₁.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hB₁x : DifferentiableAt ℝ (fun y : Vec => s₁.B (t,y)) x := hB₁.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hE₂x : DifferentiableAt ℝ (fun y : Vec => s₂.E (t,y)) x := hE₂.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hB₂x : DifferentiableAt ℝ (fun y : Vec => s₂.B (t,y)) x := hB₂.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have he₁ := (h₁.2.2.2.2.2.2.2.1 t ht.le hth).2.1 x
  have hb₁ := (h₁.2.2.2.2.2.2.2.1 t ht.le hth).2.2.1 x
  have he₂ := (h₂.2.2.2.2.2.2.2.1 t ht.le hth).2.1 x
  have hb₂ := (h₂.2.2.2.2.2.2.2.1 t ht.le hth).2.2.1 x
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)] at he₁ hb₁ he₂ hb₂
  apply maxwell_energy_balance (E := s₁.E-s₂.E) (B := s₁.B-s₂.B) (hE₁.sub hE₂) (hB₁.sub hB₂)
  · change deriv ((fun r => s₁.E (r,x))-(fun r => s₂.E (r,x))) t -
      curl ((fun y => s₁.B (t,y))-(fun y => s₂.B (t,y))) x = _
    rw [deriv_sub hE₁t hE₂t,curl_sub hB₁x hB₂x]
    calc
      _ = (deriv (fun r => s₁.E (r,x)) t-curl (fun y => s₁.B (t,y)) x)-
        (deriv (fun r => s₂.E (r,x)) t-curl (fun y => s₂.B (t,y)) x) := by abel
      _ = _ := by rw [he₁,he₂]; abel
  · change deriv ((fun r => s₁.B (r,x))-(fun r => s₂.B (r,x))) t +
      curl ((fun y => s₁.E (t,y))-(fun y => s₂.E (t,y))) x = _
    rw [deriv_sub hB₁t hB₂t,curl_sub hE₁x hE₂x]
    calc
      _ = (deriv (fun r => s₁.B (r,x)) t+curl (fun y => s₁.E (t,y)) x)-
        (deriv (fun r => s₂.B (r,x)) t+curl (fun y => s₂.E (t,y)) x) := by abel
      _ = _ := by rw [hb₁,hb₂]; simp

lemma differenceEnergy_regular_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) :
    ContDiffOn ℝ 1 (differenceEnergy s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.sub h₂.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  have hb := (h₁.2.2.1.sub h₂.2.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  exact ((he.norm_sq ℝ).add (hb.norm_sq ℝ)).div_const 2 |>.add
    ((squareDifference_regular_before h₁ h₂).moment_regular contDiff_const)

lemma differenceFlux_regular_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) :
    ContDiffOn ℝ 1 (differenceFlux s₁ s₂) (Ioi 0 ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.sub h₂.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  have hb := (h₁.2.2.1.sub h₂.2.2.1).mono (show Ioi 0 ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from
    fun p hp => show 0 ≤ p.1 from hp.1.le)
  exact ((contDiff_cross (k := 1)).contDiffOn.comp (he.prodMk hb)
    (fun _ _ => mem_univ _)).add
      ((squareDifference_regular_before h₁ h₂).moment_regular contDiff_velocity)

lemma differenceEnergy_continuous_slab_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (differenceEnergy s₁ s₂) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have he := (h₁.2.1.continuousOn.sub h₂.2.1.continuousOn).mono
    (show Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => hp.1.1)
  have hb := (h₁.2.2.1.continuousOn.sub h₂.2.2.1.continuousOn).mono
    (show Icc 0 T ×ˢ (univ : Set Vec) ⊆ fieldHalfSpace from fun p hp => hp.1.1)
  exact ((he.norm.pow 2).add (hb.norm.pow 2)).div_const 2 |>.add
    ((squareDifference_regular_before h₁ h₂).moment_continuous_slab continuous_const hT)

lemma differenceEnergy_integrable_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Vec => differenceEnergy s₁ s₂ (t,x)) := by
  exact (((h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).integrable_norm_sq ht).add
    ((h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).integrable_norm_sq ht)).div_const 2 |>.add
      ((squareDifference_regular_before h₁ h₂).spatial_moment_integrable continuous_const ht)

lemma differenceEnergy_integrated_continuous_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (fun t => ∫ x : Vec, differenceEnergy s₁ s₂ (t,x)) (Icc 0 T) := by
  have he := (h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).continuous_integral_norm_sq.mono
    (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  have hb := (h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).continuous_integral_norm_sq.mono
    (Icc_subset_Ici_self : Icc 0 T ⊆ Ici (0:ℝ))
  have hp := (squareDifference_regular_before h₁ h₂).integrated_moment_continuous
    (w := fun _ => (1:ℝ)) continuous_const hT
  apply ((he.add hb).div_const 2 |>.add hp).congr
  intro t ht
  change (∫ x : Vec, (‖(s₁.E-s₂.E) (t,x)‖^2+‖(s₁.B-s₂.B) (t,x)‖^2)/2+
    particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)) = _
  have hiE := (h₁.2.2.2.2.1.sub h₂.2.2.2.2.1).integrable_norm_sq ht.1
  have hiB := (h₁.2.2.2.2.2.1.sub h₂.2.2.2.2.2.1).integrable_norm_sq ht.1
  have hiP := (squareDifference_regular_before h₁ h₂).spatial_moment_integrable
    (w := fun _ => (1:ℝ)) continuous_const ht.1
  calc
    _ = (∫ x : Vec, (‖(s₁.E-s₂.E) (t,x)‖^2+‖(s₁.B-s₂.B) (t,x)‖^2)/2)+
      (∫ x : Vec, particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)) :=
        integral_add ((hiE.add hiB).div_const 2) hiP
    _ = _ := by rw [integral_div,integral_add hiE hiB]; rfl

lemma differenceFlux_bound_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 ≤ t) (x : Vec) :
    ‖differenceFlux s₁ s₂ (t,x)‖ ≤ differenceEnergy s₁ s₂ (t,x) := by
  apply (norm_add_le _ _).trans
  apply add_le_add ?_ ((squareDifference_regular_before h₁ h₂).velocity_flux_bound ht x
    (fun v => squareDifference_nonneg _ _ _))
  apply (norm_cross_le _ _).trans
  dsimp [differenceFieldEnergy]
  nlinarith [sq_nonneg (‖s₁.E (t,x)-s₂.E (t,x)‖-‖s₁.B (t,x)-s₂.B (t,x)‖)]

lemma differenceEnergy_initial_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) (x : Vec) :
    differenceEnergy s₁ s₂ (0,x) = 0 := by
  have hf (v : Vec) : squareDifference s₁ s₂ (0,x,v)=0 := by
    rw [squareDifference_zero_iff,h₁.2.2.2.2.2.2.2.2.1,h₂.2.2.2.2.2.2.2.2.1]
  simp [differenceEnergy,differenceFieldEnergy,particleMoment_one,hf,
    h₁.2.2.2.2.2.2.2.2.2.1,h₁.2.2.2.2.2.2.2.2.2.2,
    h₂.2.2.2.2.2.2.2.2.2.1,h₂.2.2.2.2.2.2.2.2.2.2]

lemma differenceEnergy_local_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 < t) (hth : t < H) (x : Vec) :
    fderiv ℝ (differenceEnergy s₁ s₂) (t,x) (1,0)+
      divergence (fun y => differenceFlux s₁ s₂ (t,y)) x =
      ∫ v : Vec, -(s₁.f (t,x,v)-s₂.f (t,x,v)) *
        fderiv ℝ (fun w => s₂.f (t,x,w)) v
          ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) -
        dot (s₁.E (t,x)-s₂.E (t,x)) ((s₁.f (t,x,v)-s₂.f (t,x,v)) • velocity v) := by
  have hE := (field_differentiableAt_positive h₁.2.1 ht x).sub
    (field_differentiableAt_positive h₂.2.1 ht x)
  have hB := (field_differentiableAt_positive h₁.2.2.1 ht x).sub
    (field_differentiableAt_positive h₂.2.2.1 ht x)
  have hfield : DifferentiableAt ℝ (differenceFieldEnergy s₁ s₂) (t,x) := by
    unfold differenceFieldEnergy
    convert ((hE.norm_sq (𝕜 := ℝ)).add (hB.norm_sq (𝕜 := ℝ))).mul_const (2 : ℝ)⁻¹ using 1 <;> try rfl
  have hpart := ((squareDifference_regular_before h₁ h₂).moment_regular
    (w := fun _ => (1:ℝ)) contDiff_const).contDiffAt (x := (t,x))
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  have hflux := ((squareDifference_regular_before h₁ h₂).moment_regular contDiff_velocity).contDiffAt
    (x := (t,x)) ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht,mem_univ _⟩)
  have hcross : DifferentiableAt ℝ (fun p => cross (s₁.E p-s₂.E p) (s₁.B p-s₂.B p)) (t,x) :=
    (contDiff_cross (k := 1)).differentiable (by simp) _ |>.comp (t,x) (hE.prodMk hB)
  have hp := particle_difference_local_before h₁ h₂ ht hth x
  have hm := difference_maxwell_local_before h₁ h₂ ht hth x
  rw [deriv_time_slice (hpart.differentiableAt (by simp))] at hp
  change deriv (fun r => differenceFieldEnergy s₁ s₂ (r,x)) t + _ = _ at hm
  rw [deriv_time_slice hfield] at hm
  have hs₁ := h₁.regularParticle.slice ht.le x
  have hs₂ := h₂.regularParticle.slice ht.le x
  let g : Vec → ℝ := fun v => s₁.f (t,x,v)-s₂.f (t,x,v)
  have hgc : Continuous g := hs₁.1.continuous.sub hs₂.1.continuous
  have hgK : HasCompactSupport g := hs₁.2.sub hs₂.2
  have hdc : Continuous (fun v => fderiv ℝ (fun w => s₂.f (t,x,w)) v) :=
    hs₂.1.continuous_fderiv (by simp)
  have hi : Integrable (fun v => -g v * fderiv ℝ (fun w => s₂.f (t,x,w)) v
      ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x)))) :=
    (hgc.neg.mul (hdc.clm_apply (contDiff_lorentz (k := 1) _ _).continuous)).integrable_of_hasCompactSupport
      hgK.neg.mul_right
  have hjI : Integrable (fun v => g v • velocity v) :=
    (hgc.smul (contDiff_velocity (k := 1)).continuous).integrable_of_hasCompactSupport hgK.smul_right
  have hjdI : Integrable (fun v => dot (s₁.E (t,x)-s₂.E (t,x)) (g v • velocity v)) := by
    simp only [dot_eq_inner]
    exact hjI.const_inner _
  have hj : (∫ v : Vec, g v • velocity v) =
      current (fun z => s₁.f (t,z)) x-current (fun z => s₂.f (t,z)) x := by
    simp only [g,sub_smul,current]
    exact integral_sub
      (h₁.regularParticle.moment_integrable (contDiff_velocity (k := 1)).continuous ht.le x)
      (h₂.regularParticle.moment_integrable (contDiff_velocity (k := 1)).continuous ht.le x)
  have hdot : (∫ v : Vec, dot (s₁.E (t,x)-s₂.E (t,x)) (g v • velocity v)) =
      dot (s₁.E (t,x)-s₂.E (t,x))
        (current (fun z => s₁.f (t,z)) x-current (fun z => s₂.f (t,z)) x) := by
    simp only [dot_eq_inner]
    rw [integral_inner hjI,hj]
  change (fderiv ℝ (differenceFieldEnergy s₁ s₂+
    particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ))) (t,x)) (1,0) +
    divergence ((fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y)))+
      fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x = _
  have hxs : DifferentiableAt ℝ (fun y => cross (s₁.E (t,y)-s₂.E (t,y))
      (s₁.B (t,y)-s₂.B (t,y))) x :=
    hcross.comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  have hvs : DifferentiableAt ℝ (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x :=
    (hflux.differentiableAt (by simp)).comp x ((differentiableAt_const t).prodMk differentiableAt_id)
  rw [fderiv_add hfield (hpart.differentiableAt (by simp)),add_apply]
  have hvdiv : divergence ((fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y)))+
      fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x =
        divergence (fun y => cross (s₁.E (t,y)-s₂.E (t,y)) (s₁.B (t,y)-s₂.B (t,y))) x+
        divergence (fun y => particleMoment (squareDifference s₁ s₂) velocity (t,y)) x := by
    exact divergence_add hxs hvs
  rw [hvdiv]
  change _ = ∫ v : Vec, -g v * fderiv ℝ (fun w => s₂.f (t,x,w)) v
    ((s₁.E (t,x)-s₂.E (t,x))+cross (velocity v) (s₁.B (t,x)-s₂.B (t,x))) -
      dot (s₁.E (t,x)-s₂.E (t,x)) (g v • velocity v)
  rw [integral_sub hi hjdI,hdot]
  dsimp [g] at *
  linarith

lemma differenceEnergy_zero_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {t : ℝ} (ht : 0 ≤ t) (x : Vec)
    (hz : differenceEnergy s₁ s₂ (t,x)=0) :
    s₁.E (t,x)=s₂.E (t,x) ∧ s₁.B (t,x)=s₂.B (t,x) ∧ ∀ v, s₁.f (t,x,v)=s₂.f (t,x,v) := by
  have hp : 0 ≤ (∫ v : Vec, squareDifference s₁ s₂ (t,x,v)) :=
    integral_nonneg (fun v => squareDifference_nonneg _ _ _)
  have he := differenceFieldEnergy_nonneg s₁ s₂ (t,x)
  change differenceFieldEnergy s₁ s₂ (t,x)+particleMoment (squareDifference s₁ s₂) (fun _ => (1:ℝ)) (t,x)=0 at hz
  rw [particleMoment_one] at hz
  have hp0 : (∫ v : Vec, squareDifference s₁ s₂ (t,x,v))=0 := by linarith
  have he0 : differenceFieldEnergy s₁ s₂ (t,x)=0 := by linarith
  have heq : s₁.E (t,x)=s₂.E (t,x) := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    dsimp [differenceFieldEnergy] at he0
    nlinarith [sq_nonneg ‖s₁.B (t,x)-s₂.B (t,x)‖,norm_nonneg (s₁.E (t,x)-s₂.E (t,x))]
  have hbq : s₁.B (t,x)=s₂.B (t,x) := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    dsimp [differenceFieldEnergy] at he0
    nlinarith [sq_nonneg ‖s₁.E (t,x)-s₂.E (t,x)‖,norm_nonneg (s₁.B (t,x)-s₂.B (t,x))]
  refine ⟨heq,hbq,?_⟩
  have hs := (squareDifference_regular_before h₁ h₂).slice ht x
  have hi : Integrable (fun v : Vec => squareDifference s₁ s₂ (t,x,v)) :=
    hs.1.continuous.integrable_of_hasCompactSupport hs.2
  have hae := (integral_eq_zero_iff_of_nonneg (fun v => squareDifference_nonneg s₁ s₂ (t,x,v)) hi).mp hp0
  have hevery := Measure.eq_of_ae_eq (μ := volume) hae hs.1.continuous continuous_const
  intro v
  exact (squareDifference_zero_iff _ _ _).mp (congrFun hevery v)

lemma differenceEnergy_differential_bound_before {d : Datum} {H : ℝ} {s₁ s₂ : Solution}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H) {T : ℝ} (hT : 0 ≤ T) (hTH : T ≤ H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo 0 T, ∀ x : Vec,
      fderiv ℝ (differenceEnergy s₁ s₂) (t,x) (1,0)+
        divergence (fun y => differenceFlux s₁ s₂ (t,y)) x ≤
          C*differenceEnergy s₁ s₂ (t,x) := by
  obtain ⟨K₁,hK₁,hs₁⟩ := h₁.regularParticle.2 T hT
  obtain ⟨K₂,hK₂,hs₂⟩ := h₂.regularParticle.2 T hT
  let K : Set Vec := Prod.snd '' (K₁ ∪ K₂)
  have hK : IsCompact K := (hK₁.union hK₂).image continuous_snd
  obtain ⟨L,hL,hLb⟩ := h₂.regularParticle.velocity_derivative_bound hT
  refine ⟨(2*L+2)*(1+(volume K).toReal),by positivity,?_⟩
  intro t ht x
  rw [differenceEnergy_local_before h₁ h₂ ht.1 (ht.2.trans_le hTH) x]
  have hf₁ := h₁.regularParticle.slice ht.1.le x
  have hf₂ := h₂.regularParticle.slice ht.1.le x
  have hz : ∀ v ∉ K, s₁.f (t,x,v)-s₂.f (t,x,v)=0 := by
    intro v hv
    have hnot₁ : (x,v) ∉ tsupport (fun z => s₁.f (t,z)) := by
      intro hh
      exact hv ⟨(x,v),Or.inl (hs₁ t ⟨ht.1.le,ht.2.le⟩ hh),rfl⟩
    have hnot₂ : (x,v) ∉ tsupport (fun z => s₂.f (t,z)) := by
      intro hh
      exact hv ⟨(x,v),Or.inr (hs₂ t ⟨ht.1.le,ht.2.le⟩ hh),rfl⟩
    rw [image_eq_zero_of_notMem_tsupport hnot₁,image_eq_zero_of_notMem_tsupport hnot₂,sub_self]
  have hb := compact_difference_source_bound (s₁.E (t,x)-s₂.E (t,x))
    (s₁.B (t,x)-s₂.B (t,x)) (hf₁.1.continuous.sub hf₂.1.continuous)
    (hf₂.1.continuous_fderiv (by simp)) hK hz hL (hLb t ht x)
  simpa only [differenceEnergy,differenceFieldEnergy,particleMoment_one,squareDifference,Pi.sub_apply] using hb

theorem classical_unique_before {d : Datum} {s₁ s₂ : Solution} {H : ℝ}
    (h₁ : ClassicalBefore d s₁ H) (h₂ : ClassicalBefore d s₂ H)
    {T : ℝ} (hT : 0 ≤ T) (hTH : T ≤ H) :
    (∀ z, s₁.f (T,z)=s₂.f (T,z)) ∧
    (∀ x, s₁.E (T,x)=s₂.E (T,x)) ∧ (∀ x, s₁.B (T,x)=s₂.B (T,x)) := by
  obtain ⟨C,hC,hbound⟩ := differenceEnergy_differential_bound_before h₁ h₂ hT hTH
  have hz := local_energy_inequality_vanishes hC hT
    (differenceEnergy_regular_before h₁ h₂) (differenceFlux_regular_before h₁ h₂)
    (differenceEnergy_continuous_slab_before h₁ h₂ hT)
    (fun _ _ _ => differenceEnergy_nonneg _ _ _)
    (fun _ ht => differenceEnergy_integrable_before h₁ h₂ ht.1)
    (differenceEnergy_integrated_continuous_before h₁ h₂ hT)
    (fun _ ht => differenceFlux_bound_before h₁ h₂ ht.1.le)
    hbound (differenceEnergy_initial_before h₁ h₂)
  have heq (x : Vec) := differenceEnergy_zero_before h₁ h₂ hT x (hz x)
  exact ⟨fun z => (heq z.1).2.2 z.2,fun x => (heq x).1,fun x => (heq x).2.1⟩

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma SmoothClassicalPrefix.mono {d : Datum} {s : Solution} {T H : ℝ}
    (hs : SmoothClassicalPrefix d s H) (hTH : T ≤ H) : SmoothClassicalPrefix d s T := by
  have hsub : Icc (0:ℝ) T ⊆ Icc 0 H := Icc_subset_Icc_right hTH
  refine ⟨hs.f_smooth.mono (fun p hp => hsub hp),hs.E_smooth.mono (fun p hp => hsub hp),
    hs.B_smooth.mono (fun p hp => hsub hp),fun t ht => hs.nonnegative t (hsub ht),?_,?_,?_,
    fun t ht htT => hs.equations t ht (htT.trans_le hTH),hs.initial_f,hs.initial_E,hs.initial_B⟩
  · obtain ⟨F,hc,he⟩ := hs.E_L2
    exact ⟨F,hc.mono hsub,fun t ht => he t (hsub ht)⟩
  · obtain ⟨F,hc,he⟩ := hs.B_L2
    exact ⟨F,hc.mono hsub,fun t ht => he t (hsub ht)⟩
  · obtain ⟨K,hK,hk⟩ := hs.compact
    exact ⟨K,hK,fun t ht => hk t (hsub ht)⟩

lemma SmoothClassicalPrefix.unique_lt {d : Datum} {s₁ s₂ : Solution} {H₁ H₂ t : ℝ}
    (h₁ : SmoothClassicalPrefix d s₁ H₁) (h₂ : SmoothClassicalPrefix d s₂ H₂)
    (ht : 0 ≤ t) (ht₁ : t < H₁) (ht₂ : t < H₂) :
    (∀ z, s₁.f (t,z)=s₂.f (t,z)) ∧ (∀ x, s₁.E (t,x)=s₂.E (t,x)) ∧
      (∀ x, s₁.B (t,x)=s₂.B (t,x)) := by
  obtain ⟨τ,htτ,hτ⟩ := exists_between (lt_min ht₁ ht₂)
  have hτ₁ := hτ.trans_le (min_le_left _ _)
  have hτ₂ := hτ.trans_le (min_le_right _ _)
  have he := classical_unique_before
    (h₁.cutoff_classical_before (ht.trans htτ.le) hτ₁)
    (h₂.cutoff_classical_before (ht.trans htτ.le) hτ₂) ht htτ.le
  have he₁ := cutoffPrefix_eq hτ₁ htτ.le s₁
  have he₂ := cutoffPrefix_eq hτ₂ htτ.le s₂
  exact ⟨fun z => (he₁.1 z).symm.trans ((he.1 z).trans (he₂.1 z)),
    fun x => (he₁.2.1 x).symm.trans ((he.2.1 x).trans (he₂.2.1 x)),
    fun x => (he₁.2.2 x).symm.trans ((he.2.2 x).trans (he₂.2.2 x))⟩

theorem SmoothClassicalPrefix.unique {d : Datum} {s₁ s₂ : Solution} {H₁ H₂ t : ℝ}
    (h₁ : SmoothClassicalPrefix d s₁ H₁) (h₂ : SmoothClassicalPrefix d s₂ H₂)
    (ht : 0 ≤ t) (ht₁ : t ≤ H₁) (ht₂ : t ≤ H₂) :
    (∀ z, s₁.f (t,z)=s₂.f (t,z)) ∧ (∀ x, s₁.E (t,x)=s₂.E (t,x)) ∧
      (∀ x, s₁.B (t,x)=s₂.B (t,x)) := by
  rcases ht.eq_or_lt with rfl | ht
  · exact ⟨fun z => (h₁.initial_f z).trans (h₂.initial_f z).symm,
      fun x => (h₁.initial_E x).trans (h₂.initial_E x).symm,
      fun x => (h₁.initial_B x).trans (h₂.initial_B x).symm⟩
  have hp : ∀ r∈Ico (0:ℝ) t,
      (∀ z, s₁.f (r,z)=s₂.f (r,z)) ∧ (∀ x, s₁.E (r,x)=s₂.E (r,x)) ∧
        (∀ x, s₁.B (r,x)=s₂.B (r,x)) :=
    fun r hr => h₁.unique_lt h₂ hr.1 (hr.2.trans_le ht₁) (hr.2.trans_le ht₂)
  have hcl : Icc (0:ℝ) t ⊆ closure (Ico 0 t) := by rw [closure_Ico ht.ne]
  have h₁r := h₁.mono ht₁
  have h₂r := h₂.mono ht₂
  refine ⟨?_,?_,?_⟩
  · intro z
    exact (Set.EqOn.of_subset_closure (fun r hr => (hp r hr).1 z)
      (h₁r.f_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      (h₂r.f_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      Ico_subset_Icc_self hcl) ⟨ht.le,le_rfl⟩
  · intro x
    exact (Set.EqOn.of_subset_closure (fun r hr => (hp r hr).2.1 x)
      (h₁r.E_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      (h₂r.E_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      Ico_subset_Icc_self hcl) ⟨ht.le,le_rfl⟩
  · intro x
    exact (Set.EqOn.of_subset_closure (fun r hr => (hp r hr).2.2 x)
      (h₁r.B_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      (h₂r.B_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun r hr => hr))
      Ico_subset_Icc_self hcl) ⟨ht.le,le_rfl⟩

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

lemma time_slab_mem_nhdsWithin {X : Type*} [TopologicalSpace X]
    {p : ℝ × X} {H : ℝ} (hp : p.1<H) :
    {z : ℝ × X | z.1∈Icc (0:ℝ) H} ∈ 𝓝[{z : ℝ × X | 0 ≤ z.1}] p := by
  have hh : {z : ℝ × X | z.1<H} ∈ 𝓝 p :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds hp
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hh] with z hz hzH
  exact ⟨hz,hzH.le⟩

lemma contDiffOn_halfspace_of_slabs {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {f : ℝ × X → Y} {k : ℕ∞ω}
    (hf : ∀ T : ℝ, 0 ≤ T → ContDiffOn ℝ k f {z : ℝ × X | z.1∈Icc (0:ℝ) T}) :
    ContDiffOn ℝ k f {z : ℝ × X | 0 ≤ z.1} := by
  intro p hp
  change 0 ≤ p.1 at hp
  exact (hf (p.1+1) (by linarith) p ⟨hp,by linarith⟩).mono_of_mem_nhdsWithin
    (time_slab_mem_nhdsWithin (by linarith))

lemma timeContinuousL2_of_slabs {F : Field}
    (hF : ∀ H : ℝ, 0 ≤ H → ∃ G : ℝ → Lp Vec 2 (volume : Measure Vec),
      ContinuousOn G (Icc (0:ℝ) H) ∧
      ∀ t∈Icc (0:ℝ) H, (G t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x))) :
    TimeContinuousL2 F := by
  choose G hG he using fun H : ℝ => hF (max H 0) (le_max_right H 0)
  let g : ℝ → Lp Vec 2 (volume : Measure Vec) := fun t => G t t
  have hself (t : ℝ) (ht : 0 ≤ t) : (g t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x)) :=
    he t t ⟨ht,le_max_left t 0⟩
  have heq (H t : ℝ) (ht : t∈Icc (0:ℝ) H) : g t=G H t := by
    apply Lp.ext
    exact (hself t ht.1).trans (he H t ⟨ht.1,ht.2.trans (le_max_left H 0)⟩).symm
  refine ⟨g,?_,hself⟩
  intro t ht
  have hmem : Icc (0:ℝ) (max (t+1) 0) ∈ 𝓝[Ici 0] t := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<t+1 by linarith))] with r hr hrH
    exact ⟨hr,hrH.le.trans (le_max_left (t+1) 0)⟩
  have hc := (hG (t+1) t ⟨ht,by linarith [le_max_left (t+1) 0]⟩).mono_of_mem_nhdsWithin hmem
  apply hc.congr_of_eventuallyEq_of_mem ?_ ht
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<t+1 by linarith))] with r hr hrH
  exact heq (t+1) r ⟨hr,hrH.le⟩

theorem global_classical_of_arbitrarily_long_prefixes_oai {d : Datum}
    (hpre : ∀ H : ℝ, 0 ≤ H → ∃ U : ℝ, H<U ∧ ∃ a : Solution, SmoothClassicalPrefix d a U) :
    ∃ s : Solution, Classical d s ∧ SmoothOnFiniteHorizons s ∧
      ∀ s' : Solution, Classical d s' → SameNonnegativeTime s s' := by
  choose U hU a ha using fun H : ℝ => hpre (max H 0) (le_max_right H 0)
  let s : Solution := ⟨fun p => (a p.1).f p,fun p => (a p.1).E p,fun p => (a p.1).B p⟩
  have heq (H t : ℝ) (ht : t∈Icc (0:ℝ) H) :
      (∀ z, s.f (t,z)=(a H).f (t,z)) ∧
      (∀ x, s.E (t,x)=(a H).E (t,x)) ∧ (∀ x, s.B (t,x)=(a H).B (t,x)) := by
    exact (ha t).unique (ha H) ht.1 ((le_max_left t 0).trans (hU t).le)
      (ht.2.trans ((le_max_left H 0).trans (hU H).le))
  have hsm : SmoothOnFiniteHorizons s := by
    intro T hT
    have htU : T ≤ U T := (le_max_left T 0).trans (hU T).le
    have hh := (ha T).mono htU
    exact ⟨hh.f_smooth.congr (fun p hp => (heq T p.1 hp).1 p.2),
      hh.E_smooth.congr (fun p hp => (heq T p.1 hp).2.1 p.2),
      hh.B_smooth.congr (fun p hp => (heq T p.1 hp).2.2 p.2)⟩
  have hregf : ContDiffOn ℝ 1 s.f particleHalfSpace :=
    contDiffOn_halfspace_of_slabs (fun T ht => (hsm T ht).1.of_le (by simp))
  have hregE : ContDiffOn ℝ 1 s.E fieldHalfSpace :=
    contDiffOn_halfspace_of_slabs (fun T ht => (hsm T ht).2.1.of_le (by simp))
  have hregB : ContDiffOn ℝ 1 s.B fieldHalfSpace :=
    contDiffOn_halfspace_of_slabs (fun T ht => (hsm T ht).2.2.of_le (by simp))
  have hpos (t : ℝ) (ht : 0 ≤ t) (z : Phase) : 0 ≤ s.f (t,z) :=
    (ha t).nonnegative t ⟨ht,(le_max_left t 0).trans (hU t).le⟩ z
  have hL2E : TimeContinuousL2 s.E := by
    apply timeContinuousL2_of_slabs
    intro H hH
    obtain ⟨G,hG,hrep⟩ := (ha H).E_L2
    refine ⟨G,hG.mono (Icc_subset_Icc_right ((le_max_left H 0).trans (hU H).le)),?_⟩
    intro t ht
    exact (hrep t ⟨ht.1,ht.2.trans ((le_max_left H 0).trans (hU H).le)⟩).trans
      (Filter.Eventually.of_forall fun x => ((heq H t ht).2.1 x).symm)
  have hL2B : TimeContinuousL2 s.B := by
    apply timeContinuousL2_of_slabs
    intro H hH
    obtain ⟨G,hG,hrep⟩ := (ha H).B_L2
    refine ⟨G,hG.mono (Icc_subset_Icc_right ((le_max_left H 0).trans (hU H).le)),?_⟩
    intro t ht
    exact (hrep t ⟨ht.1,ht.2.trans ((le_max_left H 0).trans (hU H).le)⟩).trans
      (Filter.Eventually.of_forall fun x => ((heq H t ht).2.2 x).symm)
  have hcompact : CompactOnFiniteHorizons s := by
    intro H hH
    obtain ⟨K,hK,hk⟩ := (ha H).compact
    refine ⟨K,hK,?_⟩
    intro t ht
    rw [show (fun z => s.f (t,z))=(fun z => (a H).f (t,z)) from funext (heq H t ht).1]
    exact hk t ⟨ht.1,ht.2.trans ((le_max_left H 0).trans (hU H).le)⟩
  have hequations : Equations s := by
    intro t ht
    let H := t+1
    have htH : t ≤ H := by dsimp [H]; linarith
    have htU : t<U H := lt_of_le_of_lt (htH.trans (le_max_left H 0)) (hU H)
    have hh := (ha H).equations t ht htU
    have heqt := heq H t ⟨ht,htH⟩
    have hf (z : Phase) :
        derivWithin (fun r => s.f (r,z)) (Ici 0) t =
          derivWithin (fun r => (a H).f (r,z)) (Ici 0) t := by
      apply Filter.EventuallyEq.derivWithin_eq_of_mem (hx:=ht)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<H by dsimp [H]; linarith))] with r hr hrH
      exact (heq H r ⟨hr,hrH.le⟩).1 z
    have hE (x : Vec) :
        derivWithin (fun r => s.E (r,x)) (Ici 0) t =
          derivWithin (fun r => (a H).E (r,x)) (Ici 0) t := by
      apply Filter.EventuallyEq.derivWithin_eq_of_mem (hx:=ht)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<H by dsimp [H]; linarith))] with r hr hrH
      exact (heq H r ⟨hr,hrH.le⟩).2.1 x
    have hB (x : Vec) :
        derivWithin (fun r => s.B (r,x)) (Ici 0) t =
          derivWithin (fun r => (a H).B (r,x)) (Ici 0) t := by
      apply Filter.EventuallyEq.derivWithin_eq_of_mem (hx:=ht)
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show t<H by dsimp [H]; linarith))] with r hr hrH
      exact (heq H r ⟨hr,hrH.le⟩).2.2 x
    simpa only [hf,hE,hB,heqt.1,heqt.2.1,heqt.2.2] using hh
  have hc : Classical d s := ⟨hregf,hregE,hregB,hpos,hL2E,hL2B,hcompact,hequations,
    (ha 0).initial_f,(ha 0).initial_E,(ha 0).initial_B⟩
  exact ⟨s,hc,hsm,fun s' hs' => classical_unique hc hs'⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.global_classical_of_arbitrarily_long_prefixes_oai := @OAI.RVM.global_classical_of_arbitrarily_long_prefixes_oai
