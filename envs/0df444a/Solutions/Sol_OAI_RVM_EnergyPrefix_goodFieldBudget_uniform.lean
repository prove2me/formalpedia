-- Prove2me | solution 1 for OAI.RVM.EnergyPrefix.goodFieldBudget_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:36:54.464962+00:00
-- url     : https://prove2.me/submissions/92b31cf3-cc71-43b2-8777-3d19c94a6c5f

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

lemma dot_cross_self_left (a b : Vec) : dot a (cross a b) = 0 := by
  simp [dot, cross, Fin.sum_univ_succ]
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

lemma dot_cross_cycle (a b c : Vec) : dot a (cross b c) = dot b (cross c a) := by
  simp [dot, cross, Fin.sum_univ_succ]
  ring

lemma cross_antisymm (a b : Vec) : cross a b = -cross b a := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma poynting_norm_le_energy (E B : Vec) :
    ‖cross E B‖ ≤ (‖E‖^2+‖B‖^2)/2 := by
  have h := norm_cross_le E B
  nlinarith [sq_nonneg (‖E‖-‖B‖)]

lemma field_cone_energy_identity (E B n : Vec) (hn : ‖n‖ = 1) :
    (‖E‖^2+‖B‖^2)/2-dot n (cross E B) =
      (‖E+cross n B‖^2+(dot n B)^2)/2 := by
  have hcross := cross_dot_square n B
  rw [dot_self, dot_self, dot_self, hn] at hcross
  rw [norm_add_sq_real, ← dot_eq_inner]
  have he : dot E (cross n B) = -dot n (cross E B) := by
    rw [dot_cross_cycle, cross_antisymm B E]
    simp [dot, Finset.sum_neg_distrib]
  rw [he]
  nlinarith

lemma good_field_square_le_flux (E B n : Vec) (hn : ‖n‖ = 1) :
    (‖E+cross n B‖+|dot n B|)^2 ≤
      4*((‖E‖^2+‖B‖^2)/2-dot n (cross E B)) := by
  rw [field_cone_energy_identity E B n hn]
  nlinarith [sq_abs (dot n B), sq_nonneg (‖E+cross n B‖-|dot n B|)]

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

lemma fderiv_q_apply (v h : Vec) : fderiv ℝ q v h = dot (velocity v) h := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt q (fderiv ℝ q v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_q.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_energy hc
  have he := h₁.unique h₂
  simpa using he

lemma spatialPartial_q (v : Vec) (i : Fin 3) : spatialPartial q v i = velocity v i := by
  simp [spatialPartial, fderiv_q_apply, dot, basis]

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

lemma divergence_energy_lorentz (v E B : Vec) :
    divergence (fun w => q w • (E+cross (velocity w) B)) v = dot (velocity v) E := by
  let F : Vec → Vec := fun w => E+cross (velocity w) B
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun w => F w i) v :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp v
      ((contDiff_lorentz E B).differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v)
  have hh (i : Fin 3) : spatialPartial (fun w => (q w • F w) i) v i =
      q v*spatialPartial (fun w => F w i) v i+ F v i*velocity v i := by
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [spatialPartial_mul (contDiff_q.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v)
      (hd i), spatialPartial_q]
  change (∑ i : Fin 3, spatialPartial (fun w => (q w • F w) i) v i) = _
  simp only [hh, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [show (∑ i : Fin 3, spatialPartial (fun w => F w i) v i) = 0 from
    divergence_lorentz v E B, mul_zero, zero_add]
  change dot (F v) (velocity v) = _
  rw [dot_comm, show F v = E+cross (velocity v) B from rfl,
    dot_add_right, dot_cross_self_left, add_zero]

lemma integral_momentum_work {g : Vec → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (E B : Vec) :
    (∫ v, q v * ∑ i : Fin 3,
      (E+cross (velocity v) B) i * spatialPartial g v i) =
      -dot E (∫ v, g v • velocity v) := by
  let F : Vec → Vec := fun v => q v • (E+cross (velocity v) B)
  have hF : ContDiff ℝ 1 F := contDiff_q.smul (contDiff_lorentz E B)
  have hfi (i : Fin 3) : ContDiff ℝ 1 (fun v => F v i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff.comp hF
  have hi (i : Fin 3) : Integrable (fun v => F v i*spatialPartial g v i) :=
    ((hfi i).continuous.mul
      ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (basis i)).mul_left
  have hi' (i : Fin 3) : Integrable (fun v => spatialPartial (fun w => F w i) v i*g v) :=
    ((((hfi i).continuous_fderiv (by simp)).clm_apply continuous_const).mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hv : Integrable (fun v => g v • velocity v) :=
    (hg.continuous.smul (contDiff_velocity (k := 1)).continuous).integrable_of_hasCompactSupport hc.smul_right
  calc
    _ = ∫ v, ∑ i : Fin 3, F v i * spatialPartial g v i := by
      congr 1; funext v; simp only [F, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    _ = ∑ i : Fin 3, ∫ v, F v i * spatialPartial g v i := integral_finsetSum _ (fun i _ => hi i)
    _ = ∑ i : Fin 3, -(∫ v, spatialPartial (fun w => F w i) v i * g v) := by
      congr 1; funext i; exact integral_mul_spatialPartial (hfi i) hg hc i
    _ = -(∫ v, divergence F v * g v) := by
      rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hi' i)]
      congr 2; funext v; simp only [divergence, Finset.sum_mul]
    _ = -(∫ v, dot E (g v • velocity v)) := by
      congr 1; apply integral_congr_ae; filter_upwards [] with v
      rw [show divergence F v = dot (velocity v) E from divergence_energy_lorentz v E B,
        dot_smul_right, dot_comm]; ring
    _ = _ := by simp only [dot_eq_inner]; rw [integral_inner hv E]

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

lemma q_mul_velocity (v : Vec) (i : Fin 3) : q v * velocity v i = v i := by
  simp only [velocity, PiLp.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (q_pos v)), one_mul]

lemma particle_energy_balance_param
    {U : Set (ℝ × Vec)} {K : Set Vec} {F : (ℝ × Vec) × Vec → ℝ}
    {p : ℝ × Vec} (E B : Vec)
    (hU : IsOpen U) (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0)
    (hV : ∀ v, fderiv ℝ F (p,v) ((1,velocity v), E + cross (velocity v) B) = 0) :
    fderiv ℝ (fun y => ∫ v : Vec, q v * F (y,v)) p (1,0) +
      ∑ i : Fin 3, fderiv ℝ (fun y => ∫ v : Vec, v i * F (y,v)) p (0,basis i) =
      dot E (∫ v : Vec, F (p,v) • velocity v) := by
  have hdiff (v : Vec) : DifferentiableAt ℝ F (p,v) :=
    (hF.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)).differentiableAt (by simp)
  have hs : ContDiff ℝ 1 (fun v : Vec => F (p,v)) := by
    apply contDiffOn_univ.mp
    exact hF.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
      (fun v _ => ⟨hp,mem_univ v⟩)
  have hc : HasCompactSupport (fun v : Vec => F (p,v)) :=
    compactSupport_of_zero_off hK (hzero p hp)
  have hv (v : Vec) :
      q v * fderiv ℝ F (p,v) ((1,0),0) +
        ∑ i : Fin 3, v i * fderiv ℝ F (p,v) ((0,basis i),0) =
      -(q v * ∑ i : Fin 3, (E + cross (velocity v) B) i *
        spatialPartial (fun w => F (p,w)) v i) := by
    have he := congrArg (fun r : ℝ => q v * r) (hV v)
    rw [clm_spacetime_velocity_split] at he
    simp only [mul_add, Finset.mul_sum, ← mul_assoc, q_mul_velocity, mul_zero] at he
    simpa only [spatialPartial, fderiv_velocity_slice (hdiff v), Finset.mul_sum, ← mul_assoc] using
      (eq_neg_of_add_eq_zero_left he)
  have hproj (i : Fin 3) : ContDiff ℝ 1 (fun v : Vec => v i) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).contDiff
  have hint := integrable_param_fderiv_apply_weight hU hK hp hF
    (contDiff_q (k := 1)).continuous hzero (((1 : ℝ),(0 : Vec)),(0 : Vec))
  have hint' (i : Fin 3) := integrable_param_fderiv_apply_weight hU hK hp hF
    (hproj i).continuous hzero (((0 : ℝ),basis i),(0 : Vec))
  rw [fderiv_weighted_integral_uniform_support_apply hU hK hp hF contDiff_q hzero]
  simp_rw [fderiv_weighted_integral_uniform_support_apply hU hK hp hF (hproj _) hzero]
  rw [← integral_finsetSum _ (fun i _ => hint' i), ← integral_add hint
    (integrable_finsetSum _ (fun i _ => hint' i))]
  calc
    _ = ∫ v : Vec, -(q v * ∑ i : Fin 3, (E + cross (velocity v) B) i *
        spatialPartial (fun w => F (p,w)) v i) := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact hv v
    _ = _ := by rw [integral_neg, integral_momentum_work hs hc]; ring

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

lemma param_moment_component
    {U : Set (ℝ × Vec)} {K : Set Vec} {F : (ℝ × Vec) × Vec → ℝ}
    {p : ℝ × Vec} (hK : IsCompact K) (hp : p ∈ U)
    (hF : ContinuousOn F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) (i : Fin 3) :
    (∫ v : Vec, F (p,v) • v) i = ∫ v : Vec, v i * F (p,v) := by
  have hc := hF.comp_continuous (continuous_const.prodMk continuous_id)
    (fun v : Vec => show (p,v) ∈ U ×ˢ univ from ⟨hp,mem_univ _⟩)
  have hi : Integrable (fun v : Vec => F (p,v) • v) :=
    (hc.smul continuous_id).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off hK (hzero p hp)).smul_right
  rw [integral_vec_apply hi]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_comm]

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

lemma coneShellFlux_zero_outside (s : Solution) {T ε t : ℝ} (hε : 0 < ε)
    (ht : t ∈ Icc 0 T) {x x₀ : Vec} (hx : x ∉ closedBall x₀ T) :
    coneShellFlux s T ε x₀ (t,x) = 0 := by
  simp [coneShellFlux,deriv_transition_zero_neg (coneArgument_neg_outside hε ht hx)]

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

lemma coneShellFlux_polar_kernel (s : Solution) (T ε t r : ℝ) (x₀ : Vec) (n : Sphere) :
    r^2 • coneShellFlux s T ε x₀ (t,x₀+r • n.1) =
      radialConeWeight (T-t) ε r * radialConeProfile s t (T-t) x₀ r n := by
  have hn : ‖r • n.1‖^2 = r^2 := by simp [norm_smul,Real.norm_eq_abs,sq_abs]
  simp only [coneShellFlux,coneArgument,radialConeWeight,radialConeProfile,
    add_sub_cancel_left,hn,inner_smul_left,smul_eq_mul,starRingEnd_apply,star_trivial]
  ring

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

lemma integral_limit_nonneg_le {μ : Measure ℝ} {G : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    {C : ℝ} (hC : 0 ≤ C) (hGi : ∀ n, Integrable (G n) μ)
    (hGn : ∀ n, ∀ᵐ t ∂μ, 0 ≤ G n t)
    (hconv : ∀ᵐ t ∂μ, Filter.Tendsto (fun n => G n t) Filter.atTop (𝓝 (F t)))
    (hbound : ∀ n, (∫ t, G n t ∂μ) ≤ C) :
    Integrable F μ ∧ (∫ t, F t ∂μ) ≤ C := by
  have hFn : ∀ᵐ t ∂μ, 0 ≤ F t := by
    filter_upwards [hconv, ae_all_iff.mpr hGn] with t ht hp
    exact ge_of_tendsto' ht hp
  have hnormG (n : ℕ) : (∫ t, ‖G n t‖ ∂μ) = ∫ t, G n t ∂μ := by
    apply integral_congr_ae
    filter_upwards [hGn n] with t ht
    exact Real.norm_of_nonneg ht
  have hb : Filter.liminf (fun n => ∫⁻ t, ‖G n t‖ₑ ∂μ) Filter.atTop ≤ ENNReal.ofReal C := by
    apply Filter.liminf_le_of_frequently_le'
    apply Filter.Frequently.of_forall
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hGi n),hnormG]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hi := integrable_of_tendsto hconv (fun n => (hGi n).aestronglyMeasurable)
    (lt_of_le_of_lt hb ENNReal.ofReal_lt_top).ne
  refine ⟨hi, ?_⟩
  have hh := (lintegral_enorm_le_liminf_of_tendsto hconv
    (fun n => (hGi n).aestronglyMeasurable.aemeasurable.enorm)).trans hb
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi,
    ENNReal.ofReal_le_ofReal_iff hC] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [hFn] with t ht
  exact (Real.norm_of_nonneg ht).symm

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

lemma sphere_neg_preserving : MeasurePreserving (Neg.neg : Sphere → Sphere)
    sphereMeasure sphereMeasure := by
  refine ⟨continuous_neg.measurable, ?_⟩
  ext A hA
  rw [Measure.map_apply continuous_neg.measurable hA,
    Measure.toSphere_apply' _ (continuous_neg.measurable hA),
    Measure.toSphere_apply' _ hA]
  have he : (Subtype.val '' ((Neg.neg : Sphere → Sphere) ⁻¹' A) : Set Vec) =
      -(Subtype.val '' A) := by
    ext x
    constructor
    · rintro ⟨n,hn,rfl⟩
      exact ⟨-n,hn,rfl⟩
    · rintro ⟨n,hn,hnx⟩
      exact ⟨-n,by simpa using hn,by simpa using congrArg Neg.neg hnx⟩
  rw [he,Set.smul_neg,Measure.measure_neg]

lemma integral_sphere_neg {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : Sphere → W) :
    (∫ n : Sphere, f (-n) ∂sphereMeasure) = ∫ n : Sphere, f n ∂sphereMeasure :=
  sphere_neg_preserving.integral_comp (MeasurableEquiv.neg Sphere).measurableEmbedding f

lemma nullConeFlux_spherical_eq (s : Solution) (T t : ℝ) (x₀ : Vec) :
    (∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) =
      ∫ n : Sphere, radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure := by
  rw [← integral_sphere_neg (fun n => nullConeFlux s T x₀ t n)]
  apply integral_congr_ae
  apply ae_of_all
  intro n
  simp only [nullConeFlux,radialConeProfile,coe_neg_sphere,smul_neg,sub_neg_eq_add,
    dot_eq_inner,inner_neg_left]
  ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedPhaseDomain
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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

namespace EnergyPrefix
variable {s : Solution} {T : ℝ}

lemma differentiable_particle (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (z : Phase) :
    DifferentiableAt ℝ s.f (t,z) :=
  (hs.f_smooth.contDiffAt (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem)).differentiableAt (by simp)

lemma differentiable_field {F : Field} (hF : ContDiffOn ℝ 1 F (Icc 0 T ×ˢ (univ : Set Vec)))
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) : DifferentiableAt ℝ F (t,x) :=
  (hF.contDiffAt (prod_mem_nhds (Icc_mem_nhds ht.1 ht.2) univ_mem)).differentiableAt (by simp)

lemma local_data (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    ∃ (U : Set (ℝ × Vec)) (K : Set Vec), IsOpen U ∧ IsCompact K ∧ (t,x) ∈ U ∧
      ContDiffOn ℝ 1 (particleBySpacetime s.f) (U ×ˢ univ) ∧
      ∀ p ∈ U, ∀ v ∉ K, particleBySpacetime s.f (p,v)=0 := by
  obtain ⟨K,hK,hzero⟩ := hs.compact
  let U : Set (ℝ × Vec) := {p | p.1 ∈ Ioo 0 T}
  refine ⟨U,Prod.snd '' K,isOpen_Ioo.preimage continuous_fst,hK.image continuous_snd,ht,?_,?_⟩
  · exact hs.f_smooth.comp contDiff_reassociate.contDiffOn
      (fun p hp => ⟨Ioo_subset_Icc_self hp.1,mem_univ _⟩)
  · intro p hp v hv
    by_contra hn
    have hh : (p.2,v) ∈ tsupport (fun z => s.f (p.1,z)) := subset_tsupport _ hn
    exact hv ⟨(p.2,v),hzero p.1 (Ioo_subset_Icc_self hp) hh,rfl⟩

lemma spacetime_vlasov (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x v : Vec) :
    fderiv ℝ (particleBySpacetime s.f) ((t,x),v)
      ((1,velocity v),s.E (t,x)+cross (velocity v) (s.B (t,x)))=0 := by
  rw [fderiv_particleBySpacetime (hs.differentiable_particle ht (x,v)),
    full_directional_derivative (hs.differentiable_particle ht (x,v))]
  exact hs.vlasov t ht x v

lemma particle_energy_balance (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    fderiv ℝ (fun p : ℝ × Vec => ∫ v : Vec, q v * s.f (p.1,p.2,v)) (t,x) (1,0) +
      ∑ i : Fin 3, fderiv ℝ (fun p : ℝ × Vec => ∫ v : Vec, v i * s.f (p.1,p.2,v))
        (t,x) (0,basis i) = dot (s.E (t,x)) (current (fun z => s.f (t,z)) x) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ :=
    hs.local_data ht x
  exact particle_energy_balance_param (s.E (t,x)) (s.B (t,x)) hU hK hp hF hzero
    (hs.spacetime_vlasov ht x)

lemma particle_energy_flux_regular (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    ContDiffAt ℝ 1 (particleEnergy s) (t,x) ∧ ContDiffAt ℝ 1 (particleFlux s) (t,x) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ :=
    hs.local_data ht x
  constructor
  · apply (contDiffOn_integral_uniform_support (n := 1) hU hK
      ((contDiff_q.comp contDiff_snd).contDiffOn.mul hF)
      (fun p hp v hv => by simp only [hzero p hp v hv, mul_zero])).contDiffAt (hU.mem_nhds hp)
  · apply (contDiffOn_integral_uniform_support (n := 1) hU hK
      (hF.smul contDiff_snd.contDiffOn)
      (fun p hp v hv => by
        change particleBySpacetime s.f (p,v) • v = 0
        rw [hzero p hp v hv, zero_smul])).contDiffAt (hU.mem_nhds hp)

lemma particleFlux_component (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) (i : Fin 3) :
    particleFlux s (t,x) i = ∫ v : Vec, v i * s.f (t,x,v) := by
  obtain ⟨U,K,hU,hK,hp,hF,hzero⟩ :=
    hs.local_data ht x
  exact param_moment_component hK hp hF.continuousOn hzero i

lemma particle_energy_local (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    deriv (fun r => particleEnergy s (r,x)) t +
      divergence (fun y => particleFlux s (t,y)) x =
        dot (s.E (t,x)) (current (fun z => s.f (t,z)) x) := by
  obtain ⟨henergy,hflux⟩ := particle_energy_flux_regular hs ht x
  rw [deriv_time_slice (henergy.differentiableAt (by simp))]
  apply Eq.trans _ (particle_energy_balance hs ht x)
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hcomp : DifferentiableAt ℝ (fun p => particleFlux s p i) (t,x) :=
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).differentiableAt.comp (t,x)
      (hflux.differentiableAt (by simp))
  rw [spatialPartial_time_slice hcomp]
  have he : (fun p : ℝ × Vec => particleFlux s p i) =ᶠ[𝓝 (t,x)]
      (fun p => ∫ v : Vec, v i * s.f (p.1,p.2,v)) := by
    filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds ht] with p hp
    exact particleFlux_component hs hp p.2 i
  rw [he.fderiv_eq (𝕜 := ℝ)]

lemma local_energy_conservation (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Vec) :
    deriv (fun r => totalEnergy s (r,x)) t +
      divergence (fun y => totalFlux s (t,y)) x = 0 := by
  have hE := differentiable_field hs.E_smooth ht x
  have hB := differentiable_field hs.B_smooth ht x
  obtain ⟨henergy,hflux⟩ := particle_energy_flux_regular hs ht x
  obtain ⟨he,hb⟩ := hs.maxwell t ht x
  have hm := maxwell_energy_balance hE hB he hb
  have hp := particle_energy_local hs ht x
  have heT : DifferentiableAt ℝ (fun r => s.E (r,x)) t :=
    hE.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hbT : DifferentiableAt ℝ (fun r => s.B (r,x)) t :=
    hB.comp t (differentiableAt_id.prodMk (differentiableAt_const x))
  have hfluxX : DifferentiableAt ℝ (fun y => particleFlux s (t,y)) x :=
    (hflux.differentiableAt (by simp)).comp x
      ((differentiableAt_const t).prodMk differentiableAt_id)
  have hcrossX : DifferentiableAt ℝ (fun y => cross (s.E (t,y)) (s.B (t,y))) x :=
    (contDiff_cross (k := 1)).differentiable (by simp) _ |>.comp x
      ((hE.comp x ((differentiableAt_const t).prodMk differentiableAt_id)).prodMk
        (hB.comp x ((differentiableAt_const t).prodMk differentiableAt_id)))
  change deriv (fun r => (‖s.E (r,x)‖^2 + ‖s.B (r,x)‖^2)/2 + particleEnergy s (r,x)) t +
    divergence (fun y => cross (s.E (t,y)) (s.B (t,y)) + particleFlux s (t,y)) x = 0
  have hpT : DifferentiableAt ℝ (fun r => particleEnergy s (r,x)) t :=
    DifferentiableAt.comp t (f := fun r : ℝ => (r,x)) (g := particleEnergy s)
      (henergy.differentiableAt (by simp))
      (differentiableAt_id.prodMk (differentiableAt_const x))
  have hfT : DifferentiableAt ℝ (fun r => (‖s.E (r,x)‖^2 + ‖s.B (r,x)‖^2)/2) t :=
    ((heT.norm_sq (𝕜 := ℝ)).add (hbT.norm_sq (𝕜 := ℝ))).div_const 2
  have hd := deriv_add hfT hpT
  change deriv (fun r => (‖s.E (r,x)‖^2 + ‖s.B (r,x)‖^2)/2 + particleEnergy s (r,x)) t =
    deriv (fun r => (‖s.E (r,x)‖^2 + ‖s.B (r,x)‖^2)/2) t +
      deriv (fun r => particleEnergy s (r,x)) t at hd
  rw [hd, divergence_add hcrossX hfluxX]
  linarith

lemma velocity_slice (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    ContDiff ℝ 1 (fun v : Vec => s.f (t,x,v)) ∧
      HasCompactSupport (fun v : Vec => s.f (t,x,v)) := by
  constructor
  · apply contDiffOn_univ.mp
    exact hs.f_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
      (fun _ _ => ⟨ht,mem_univ _⟩)
  · obtain ⟨K,hK,hzero⟩ := hs.compact
    apply compactSupport_of_zero_off (hK.image continuous_snd)
    intro v hv
    by_contra hn
    exact hv ⟨(x,v),hzero t ht (subset_tsupport _ hn),rfl⟩

lemma particle_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ particleEnergy s (t,x) := by
  apply integral_nonneg
  intro v
  exact mul_nonneg (q_pos v).le (hs.nonnegative t ht (x,v))

lemma particle_flux_bound (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    ‖particleFlux s (t,x)‖ ≤ particleEnergy s (t,x) := by
  obtain ⟨hf,hc⟩ := velocity_slice hs ht x
  have hi : Integrable (fun v : Vec => s.f (t,x,v) • v) :=
    (hf.continuous.smul continuous_id).integrable_of_hasCompactSupport hc.smul_right
  have hqi : Integrable (fun v : Vec => q v * s.f (t,x,v)) :=
    ((contDiff_q (k := 1)).continuous.mul hf.continuous).integrable_of_hasCompactSupport hc.mul_left
  calc
    _ ≤ ∫ v : Vec, ‖s.f (t,x,v) • v‖ := norm_integral_le_integral_norm _
    _ ≤ _ := by
      apply integral_mono hi.norm hqi
      intro v
      have hp := hs.nonnegative t ht (x,v)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp]
      nlinarith [norm_lt_q v]

lemma total_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ totalEnergy s (t,x) := by
  dsimp [totalEnergy]
  have hp := particle_energy_nonneg hs ht x
  positivity

lemma total_flux_bound (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    ‖totalFlux s (t,x)‖ ≤ totalEnergy s (t,x) := by
  exact (norm_add_le _ _).trans
    (add_le_add (poynting_norm_le_energy (s.E (t,x)) (s.B (t,x)))
      (particle_flux_bound hs ht x))

lemma prefix_memLp {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : MemLp (fun x => F (t,x)) 2 volume := by
  obtain ⟨F₂,hc,heq⟩ := hF
  exact (Lp.memLp (F₂ t)).ae_eq (heq t ht)

lemma prefix_integrable_norm_sq {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : Integrable (fun x => ‖F (t,x)‖^2) := by
  have hm := prefix_memLp hF ht
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

lemma particle_energy_continuous_slab (hs : EnergyPrefix s T) :
    ContinuousOn (particleEnergy s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hs.compact
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, q v * s.f (p.1,p.2,v)) _
  apply continuousOn_integral_uniform_support (F := fun z : (ℝ × Vec) × Vec => q z.2 * s.f (z.1.1,z.1.2,z.2)) (hK.image continuous_snd)
  · apply ((contDiff_q (k := 1)).continuous.comp continuous_snd).continuousOn.mul
    apply hs.f_smooth.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
    intro z hz
    exact ⟨hz.1.1,mem_univ _⟩
  · intro p hp v hv
    have hf : s.f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hf,mul_zero]

lemma particle_energy_compact (hs : EnergyPrefix s T) :
    ∃ K : Set Vec, IsCompact K ∧ ∀ t ∈ Icc 0 T, ∀ x ∉ K, particleEnergy s (t,x) = 0 := by
  obtain ⟨K,hK,hzero⟩ := hs.compact
  refine ⟨Prod.fst '' K,hK.image continuous_fst,?_⟩
  intro t ht x hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  have hf : s.f (t,x,v) = 0 := by
    by_contra hn
    exact hx ⟨(x,v),hzero t ht (subset_tsupport _ hn),rfl⟩
  simp only [hf,mul_zero, Pi.zero_apply]

lemma particle_energy_integrable (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (fun x : Vec => particleEnergy s (t,x)) := by
  obtain ⟨K,hK,hz⟩ := particle_energy_compact hs
  have hc := (particle_energy_continuous_slab hs).comp_continuous
    (continuous_const.prodMk continuous_id)
    (fun x : Vec => show (t,x) ∈ Icc 0 T ×ˢ (univ : Set Vec) from ⟨ht,mem_univ _⟩)
  exact hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz t ht))

lemma total_energy_integrable (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable (fun x : Vec => totalEnergy s (t,x)) := by
  exact ((prefix_integrable_norm_sq hs.E_L2 ht).add
    (prefix_integrable_norm_sq hs.B_L2 ht)).div_const 2 |>.add
      (particle_energy_integrable hs ht)

lemma total_energy_regular (hs : EnergyPrefix s T) : ContDiffOn ℝ 1 (totalEnergy s) (Ioo 0 T ×ˢ (univ : Set Vec)) := by
  have hE := hs.E_smooth.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
  have hB := hs.B_smooth.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
  have hp : ContDiffOn ℝ 1 (particleEnergy s) (Ioo 0 T ×ˢ (univ : Set Vec)) := by
    intro p hp
    exact (particle_energy_flux_regular hs hp.1 p.2).1.contDiffWithinAt
  exact ((hE.norm_sq ℝ).add (hB.norm_sq ℝ)).div_const 2 |>.add hp

lemma total_flux_regular (hs : EnergyPrefix s T) : ContDiffOn ℝ 1 (totalFlux s) (Ioo 0 T ×ˢ (univ : Set Vec)) := by
  have hE := hs.E_smooth.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
  have hB := hs.B_smooth.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)
  have hp : ContDiffOn ℝ 1 (particleFlux s) (Ioo 0 T ×ˢ (univ : Set Vec)) := by
    intro p hp
    exact (particle_energy_flux_regular hs hp.1 p.2).2.contDiffWithinAt
  exact ((contDiff_cross (k := 1)).contDiffOn.comp (hE.prodMk hB)
    (fun _ _ => mem_univ _)).add hp

lemma total_energy_continuous_slab (hs : EnergyPrefix s T) :
    ContinuousOn (totalEnergy s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  exact ((hs.E_smooth.continuousOn.norm.pow 2).add
    (hs.B_smooth.continuousOn.norm.pow 2)).div_const 2 |>.add
      (particle_energy_continuous_slab hs)

end EnergyPrefix

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_DerivMovingEnergy
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
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace NNReal

namespace RVM.EnergyPrefix

lemma deriv_moving_energy {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {U : Set ℝ} (hU : IsOpen U) (hpos : U ⊆ Ioo 0 T)
    {g : ℝ × Vec → ℝ} {K : Set Vec} (hK : IsCompact K)
    (hg : ContDiffOn ℝ 1 g (U ×ˢ (univ : Set Vec)))
    (hz : ∀ r ∈ U, ∀ x ∉ K, g (r,x)=0)
    {t : ℝ} (ht : t ∈ U) :
    HasDerivAt (fun r => ∫ x : Vec, g (r,x) * totalEnergy s (r,x))
      (∫ x : Vec, fderiv ℝ g (t,x) (1,0) * totalEnergy s (t,x) +
        fderiv ℝ g (t,x) (0,totalFlux s (t,x))) t := by
  have hE := (total_energy_regular hs).mono (prod_mono_left hpos)
  have hF : ContDiffOn ℝ 1 (fun p => g p * totalEnergy s p)
      (U ×ˢ (univ : Set Vec)) := hg.mul hE
  have hzF : ∀ r ∈ U, ∀ x ∉ K, g (r,x)*totalEnergy s (r,x)=0 := by
    intro r hr x hx
    rw [hz r hr x hx,zero_mul]
  have hd := hasFDerivAt_integral_uniform_support hU hK ht hF hzF
  have hi := fderiv_integral_uniform_support_apply hU hK ht hF hzF (1:ℝ)
  have hgg : ContDiff ℝ 1 (fun x => g (t,x)) := by
    apply ContDiffOn.comp_contDiff hg (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hS : ContDiff ℝ 1 (fun x => totalFlux s (t,x)) := by
    apply ContDiffOn.comp_contDiff ((total_flux_regular hs).mono (prod_mono_left hpos))
      (contDiff_const.prodMk contDiff_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hEc : Continuous (fun x => totalEnergy s (t,x)) := by
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
  have hIt : Integrable (fun x => fderiv ℝ g (t,x) (1,0) * totalEnergy s (t,x)) :=
    ((hgD.clm_apply continuous_const).mul hEc).integrable_of_hasCompactSupport
      (hgDapply (1,0)).mul_right
  have hIa : Integrable (fun x => g (t,x) * divergence (fun y => totalFlux s (t,y)) x) :=
    (hgg.continuous.mul (continuous_divergence hS)).integrable_of_hasCompactSupport hgC.mul_right
  have hIs : Integrable (fun x => fderiv ℝ (fun y => g (t,y)) x (totalFlux s (t,x))) :=
    ((hgg.continuous_fderiv (by simp)).clm_apply hS.continuous).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hgC.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx,zero_apply]))
  have heq : ∀ x : Vec,
      fderiv ℝ (fun p => g p * totalEnergy s p) (t,x) (1,0) =
        fderiv ℝ g (t,x) (1,0) * totalEnergy s (t,x) -
          g (t,x) * divergence (fun y => totalFlux s (t,y)) x := by
    intro x
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hg' := (hg.contDiffAt hn).differentiableAt (by simp)
    have hE' := (hE.contDiffAt hn).differentiableAt (by simp)
    change fderiv ℝ (g * totalEnergy s) (t,x) (1,0) = _
    rw [fderiv_mul hg' hE',add_apply,
      smul_apply,smul_apply,
      smul_eq_mul,smul_eq_mul,← deriv_time_slice hE']
    have hl := local_energy_conservation hs (hpos ht) x
    rw [show deriv (fun r => totalEnergy s (r,x)) t =
      -divergence (fun y => totalFlux s (t,y)) x by linarith]
    ring
  have hxder (x v : Vec) : fderiv ℝ (fun y => g (t,y)) x v = fderiv ℝ g (t,x) (0,v) := by
    have hn : U ×ˢ (univ : Set Vec) ∈ 𝓝 (t,x) :=
      (hU.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩
    have hh := ((hg.contDiffAt hn).differentiableAt (by simp)).hasFDerivAt.comp x
      ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
    change HasFDerivAt (fun y => g (t,y)) _ x at hh
    rw [hh.fderiv]
    simp
  have hh : deriv (fun r => ∫ x : Vec, g (r,x) * totalEnergy s (r,x)) t =
      ∫ x : Vec, fderiv ℝ g (t,x) (1,0) * totalEnergy s (t,x) +
        fderiv ℝ g (t,x) (0,totalFlux s (t,x)) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g (r,x) * totalEnergy s (r,x)) t 1 = _
    rw [hi]
    simp only [heq]
    rw [integral_sub hIt hIa,integral_mul_divergence hS hgg hgC,sub_neg_eq_add]
    simp_rw [← hxder]
    exact (integral_add hIt hIs).symm
  exact hh ▸ hd.differentiableAt.hasDerivAt

lemma coneShellFlux_nonneg {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Icc 0 T) (x x₀ : Vec) :
    0 ≤ coneShellFlux s T ε x₀ (t,x) := by
  by_cases hr : ‖x-x₀‖ ≤ T-t
  · apply mul_nonneg (mul_nonneg (by positivity) (deriv_transition_nonneg _))
    have hb := total_flux_bound hs ht x
    have he := total_energy_nonneg hs ht x
    have hc := real_inner_le_norm (-(x-x₀)) (totalFlux s (t,x))
    simp only [inner_neg_left,norm_neg] at hc
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (x-x₀)),
      mul_le_mul_of_nonneg_right hr he]
  · have hn : coneArgument T ε x₀ (t,x) < 0 := by
      dsimp [coneArgument]
      apply div_neg_of_neg_of_pos _ hε
      have := norm_nonneg (x-x₀)
      push Not at hr
      have hR : 0 ≤ T-t := sub_nonneg.mpr ht.2
      nlinarith [sq_lt_sq₀ hR (norm_nonneg (x-x₀)) |>.mpr hr]
    simp [coneShellFlux,deriv_transition_zero_neg hn]

lemma deriv_cone_energy {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Ioo 0 T) (x₀ : Vec) :
    HasDerivAt (fun r => ∫ x : Vec, coneCutoff T ε x₀ (r,x)*totalEnergy s (r,x))
      (-(∫ x : Vec, coneShellFlux s T ε x₀ (t,x))) t := by
  have hh := deriv_moving_energy hs isOpen_Ioo Subset.rfl
    (isCompact_closedBall x₀ T) (contDiff_coneCutoff T ε x₀ (k := 1)).contDiffOn
    (fun r hr x hx => coneCutoff_zero_outside hε ⟨hr.1.le,hr.2.le⟩ hx) ht
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [← integral_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [coneCutoff_fderiv,coneCutoff_fderiv]
  simp only [inner_zero_right,mul_zero,mul_one,sub_zero,zero_sub]
  dsimp [coneShellFlux]
  ring

lemma particle_flux_continuous_slab {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (_hT : 0 ≤ T) :
    ContinuousOn (particleFlux s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  obtain ⟨K,hK,hzero⟩ := hs.compact
  change ContinuousOn (fun p : ℝ × Vec => ∫ v : Vec, s.f (p.1,p.2,v) • v) _
  apply continuousOn_integral_uniform_support
    (F := fun z : (ℝ × Vec) × Vec => s.f (z.1.1,z.1.2,z.2) • z.2) (hK.image continuous_snd)
  · have hf : ContinuousOn (fun z : (ℝ × Vec) × Vec => s.f (z.1.1,z.1.2,z.2))
        ((Icc 0 T ×ˢ univ) ×ˢ univ) := by
      apply hs.f_smooth.continuousOn.comp (contDiff_reassociate (k := 1)).continuous.continuousOn
      intro z hz
      exact ⟨hz.1.1,mem_univ _⟩
    exact hf.smul continuous_snd.continuousOn
  · intro p hp v hv
    have hf : s.f (p.1,p.2,v) = 0 := by
      by_contra hn
      exact hv ⟨(p.2,v),hzero p.1 hp.1 (subset_tsupport _ hn),rfl⟩
    simp only [hf,zero_smul]

lemma total_flux_continuous_slab {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) :
    ContinuousOn (totalFlux s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  exact ((contDiff_cross (k := 1)).continuous.comp_continuousOn
    (hs.E_smooth.continuousOn.prodMk hs.B_smooth.continuousOn)).add
      (particle_flux_continuous_slab hs hT)

lemma coneShellFlux_continuous_slab {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {ε : ℝ} (hT : 0 ≤ T) (x₀ : Vec) :
    ContinuousOn (coneShellFlux s T ε x₀) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  have hθ : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by simp)
  exact ((continuous_const.mul (hθ.comp (contDiff_coneArgument T ε x₀ (k := 1)).continuous)).continuousOn).mul
    (((continuous_const.sub continuous_fst).continuousOn.mul
      (total_energy_continuous_slab hs)).add
        ((continuous_snd.sub continuous_const).continuousOn.inner
          (total_flux_continuous_slab hs hT)))

lemma coneShellFlux_integral_continuous {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (x₀ : Vec) :
    ContinuousOn (fun t => ∫ x : Vec, coneShellFlux s T ε x₀ (t,x)) (Icc 0 T) := by
  apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ T)
    (coneShellFlux_continuous_slab hs hT x₀)
  intro t ht x hx
  exact coneShellFlux_zero_outside s hε ht hx

lemma cone_energy_continuous {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {ε : ℝ} (_hT : 0 ≤ T) (hε : 0 < ε) (x₀ : Vec) :
    ContinuousOn (fun t => ∫ x : Vec, coneCutoff T ε x₀ (t,x)*totalEnergy s (t,x)) (Icc 0 T) := by
  apply continuousOn_integral_uniform_support (isCompact_closedBall x₀ T)
    ((contDiff_coneCutoff T ε x₀ (k := 1)).continuous.continuousOn.mul
      (total_energy_continuous_slab hs))
  intro t ht x hx
  change coneCutoff T ε x₀ (t,x)*totalEnergy s (t,x)=0
  simp only [coneCutoff_zero_outside hε ht hx,zero_mul]

lemma coneShellFlux_bound {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {ε b : ℝ} (hb : 0 ≤ b) (hbT : b ≤ T) (hε : 0 < ε) (x₀ : Vec) :
    (∫ t in 0..b, ∫ x : Vec, coneShellFlux s T ε x₀ (t,x)) ≤
      ∫ x : Vec, totalEnergy s (0,x) := by
  have hT := hb.trans hbT
  have hsub : Icc (0:ℝ) b ⊆ Icc 0 T := Icc_subset_Icc_right hbT
  have hc := (cone_energy_continuous hs hT hε x₀).mono hsub
  have hi := ((coneShellFlux_integral_continuous hs hT hε x₀).mono hsub).intervalIntegrable_of_Icc (μ := volume) hb
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb hc
    (fun t ht => deriv_cone_energy hs hε ⟨ht.1,ht.2.trans_le hbT⟩ x₀) hi.neg
  rw [intervalIntegral.integral_neg] at hf
  have hbpos : 0 ≤ ∫ x : Vec, coneCutoff T ε x₀ (b,x)*totalEnergy s (b,x) := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (Real.smoothTransition.nonneg _) (total_energy_nonneg hs ⟨hb,hbT⟩ x)
  have hzero : (∫ x : Vec, coneCutoff T ε x₀ (0,x)*totalEnergy s (0,x)) ≤
      ∫ x : Vec, totalEnergy s (0,x) := by
    refine integral_mono ?_ (total_energy_integrable hs ⟨le_rfl,hT⟩) ?_
    · apply Continuous.integrable_of_hasCompactSupport
      · apply Continuous.mul ((contDiff_coneCutoff T ε x₀ (k := 1)).continuous.comp
          (continuous_const.prodMk continuous_id))
        apply (total_energy_continuous_slab hs).comp_continuous
          (continuous_const.prodMk continuous_id)
        intro x
        exact ⟨⟨le_rfl,hT⟩,mem_univ x⟩
      · apply HasCompactSupport.mul_right
        apply compactSupport_of_zero_off (isCompact_closedBall x₀ T)
        exact fun x hx => coneCutoff_zero_outside hε ⟨le_rfl,hT⟩ hx
    · intro x
      exact mul_le_of_le_one_left (total_energy_nonneg hs ⟨le_rfl,hT⟩ x)
        (Real.smoothTransition.le_one _)
  linarith

lemma continuous_radialConeProfile {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (R : ℝ) (x₀ : Vec) :
    Continuous (fun p : ℝ × Sphere => radialConeProfile s t R x₀ p.1 p.2) := by
  have hU : Continuous (fun x => totalEnergy s (t,x)) := by
    apply (total_energy_continuous_slab hs).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hS : Continuous (fun x => totalFlux s (t,x)) := by
    apply (total_flux_continuous_slab hs (ht.1.trans ht.2)).comp_continuous
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hx : Continuous (fun p : ℝ × Sphere => x₀ + p.1 • p.2.1) := by fun_prop
  exact continuous_fst.mul ((continuous_const.mul (hU.comp hx)).add
    (continuous_fst.mul ((continuous_subtype_val.comp continuous_snd).inner (hS.comp hx))))

lemma continuous_spherical_radialConeProfile {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (R : ℝ) (x₀ : Vec) :
    Continuous (fun r => ∫ n : Sphere, radialConeProfile s t R x₀ r n ∂sphereMeasure) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
    (continuous_radialConeProfile hs ht R x₀).continuousOn
  intro r n _ hn
  exact (hn (mem_univ n)).elim

lemma coneShellFlux_polar {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {ε t : ℝ} (ht : t ∈ Icc 0 T) (hε : 0 < ε) (x₀ : Vec) :
    (∫ x : Vec, coneShellFlux s T ε x₀ (t,x)) =
      ∫ r in 0..(T-t), radialConeWeight (T-t) ε r *
        (∫ n : Sphere, radialConeProfile s t (T-t) x₀ r n ∂sphereMeasure) := by
  have hR : 0 ≤ T-t := sub_nonneg.mpr ht.2
  have hC : Continuous (fun x => coneShellFlux s T ε x₀ (t,x₀+x)) := by
    apply (coneShellFlux_continuous_slab hs (ht.1.trans ht.2) x₀).comp_continuous
      (continuous_const.prodMk (continuous_const.add continuous_id))
    intro x
    exact ⟨ht,mem_univ _⟩
  have hK : HasCompactSupport (fun x => coneShellFlux s T ε x₀ (t,x₀+x)) := by
    apply compactSupport_of_zero_off (isCompact_closedBall (0:Vec) T)
    intro x hx
    apply coneShellFlux_zero_outside s hε ht
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx
  have htrans := integral_add_left_eq_self (μ := (volume : Measure Vec))
    (fun x => coneShellFlux s T ε x₀ (t,x)) x₀
  rw [← htrans,integral_polar (hC.integrable_of_hasCompactSupport hK)]
  simp_rw [coneShellFlux_polar_kernel,radialConeWeight_integral_Ioi hR hε]
  have hcont : Continuous (fun p : ℝ × Sphere =>
      radialConeWeight (T-t) ε p.1 * radialConeProfile s t (T-t) x₀ p.1 p.2) :=
    ((continuous_radialConeWeight (T-t) ε).comp continuous_fst).mul
      (continuous_radialConeProfile hs ht (T-t) x₀)
  have hi : Integrable (fun p : ℝ × Sphere => radialConeWeight (T-t) ε p.1 *
      radialConeProfile s t (T-t) x₀ p.1 p.2)
        ((volume.restrict (uIoc 0 (T-t))).prod sphereMeasure) := by
    let : IsFiniteMeasure sphereMeasure := inferInstance
    let : IsFiniteMeasureOnCompacts ((volume : Measure ℝ).prod sphereMeasure) :=
      Measure.prod.instIsFiniteMeasureOnCompacts _ _
    rw [uIoc_of_le hR,Measure.restrict_prod_eq_prod_univ]
    exact (hcont.continuousOn.integrableOn_compact
      (μ := (volume : Measure ℝ).prod sphereMeasure)
      (isCompact_Icc.prod isCompact_univ)).mono_set
      (prod_mono_left Ioc_subset_Icc_self)
  rw [← intervalIntegral_integral_swap hi]
  apply intervalIntegral.integral_congr
  intro r _
  exact integral_const_mul _ _

lemma coneShellFlux_tendsto {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (htT : t < T) (x₀ : Vec) :
    Filter.Tendsto (fun ε => ∫ x : Vec, coneShellFlux s T ε x₀ (t,x))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ n : Sphere, radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure)) := by
  have hh := radialConeWeight_tendsto (sub_pos.mpr htT)
    (continuous_spherical_radialConeProfile hs ht (T-t) x₀).continuousOn
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (coneShellFlux_polar hs ht hε x₀).symm

lemma light_cone_flux {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) (x₀ : Vec) :
    IntegrableOn (fun t => ∫ n : Sphere,
      radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure) (Ioo 0 T) ∧
    (∫ t in 0..T, ∫ n : Sphere,
      radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure) ≤
        ∫ x : Vec, totalEnergy s (0,x) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have heps : Filter.Tendsto ε Filter.atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Filter.Eventually.of_forall hε⟩
  let G : ℕ → ℝ → ℝ := fun n t => ∫ x : Vec, coneShellFlux s T (ε n) x₀ (t,x)
  have hGi (n : ℕ) : Integrable (G n) (volume.restrict (Ioo 0 T)) := by
    exact ((coneShellFlux_integral_continuous hs hT (hε n) x₀).integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hGn (n : ℕ) : ∀ᵐ t ∂volume.restrict (Ioo 0 T), 0 ≤ G n t := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    apply integral_nonneg
    intro x
    exact coneShellFlux_nonneg hs (hε n) ⟨ht.1.le,ht.2.le⟩ x x₀
  have hconv : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      Filter.Tendsto (fun n => G n t) Filter.atTop
        (𝓝 (∫ n : Sphere, radialConeProfile s t (T-t) x₀ (T-t) n ∂sphereMeasure)) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    exact (coneShellFlux_tendsto hs (Ioo_subset_Icc_self ht) ht.2 x₀).comp heps
  have hb (n : ℕ) : (∫ t in Ioo 0 T, G n t) ≤ ∫ x : Vec, totalEnergy s (0,x) := by
    rw [restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le hT]
    exact coneShellFlux_bound hs hT le_rfl (hε n) x₀
  obtain ⟨hi,hb⟩ := integral_limit_nonneg_le
    (integral_nonneg (total_energy_nonneg hs ⟨le_rfl,hT⟩)) hGi hGn hconv hb
  refine ⟨hi, ?_⟩
  rwa [restrict_Ioo_eq_restrict_Ioc,← intervalIntegral.integral_of_le hT] at hb

open scoped Pointwise

lemma null_cone_flux {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) (x₀ : Vec) :
    IntegrableOn (fun t => ∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) (Ioo 0 T) ∧
    (∫ t in 0..T, ∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) ≤
      ∫ x : Vec, totalEnergy s (0,x) := by
  simp_rw [nullConeFlux_spherical_eq]
  exact light_cone_flux hs hT x₀

lemma particle_cone_nonneg {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) {n : Vec} (hn : ‖n‖ = 1) :
    0 ≤ particleEnergy s (t,x) - dot n (particleFlux s (t,x)) := by
  have hh := dot_le_norm n (particleFlux s (t,x))
  rw [hn,one_mul] at hh
  linarith [particle_flux_bound hs ht x]

lemma goodConeDensity_bounds {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) {n : Vec} (hn : ‖n‖=1) :
    0 ≤ goodConeDensity s (t,x) n ∧
      goodConeDensity s (t,x) n ≤ 4*(totalEnergy s (t,x)-dot n (totalFlux s (t,x))) := by
  have hG := good_field_square_le_flux (s.E (t,x)) (s.B (t,x)) n hn
  have hP := particle_cone_nonneg hs ht x hn
  dsimp [goodConeDensity,totalEnergy,totalFlux]
  rw [dot_add_right]
  constructor
  · positivity
  · linarith

lemma goodConeDensity_continuousOn {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) :
    ContinuousOn (fun p : (ℝ × Vec) × Vec => goodConeDensity s p.1 p.2)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) := by
  have hE : ContinuousOn (fun p : (ℝ × Vec) × Vec => s.E p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    hs.E_smooth.continuousOn.comp continuous_fst.continuousOn (by
      intro p hp; exact hp.1)
  have hB : ContinuousOn (fun p : (ℝ × Vec) × Vec => s.B p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    hs.B_smooth.continuousOn.comp continuous_fst.continuousOn (by
      intro p hp; exact hp.1)
  have hF : ContinuousOn (fun p : (ℝ × Vec) × Vec => particleFlux s p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    (particle_flux_continuous_slab hs hT).comp
      continuous_fst.continuousOn (fun _ h => h.1)
  have hP : ContinuousOn (fun p : (ℝ × Vec) × Vec => particleEnergy s p.1)
      ((Icc 0 T ×ˢ (univ : Set Vec)) ×ˢ univ) :=
    (particle_energy_continuous_slab hs).comp
      continuous_fst.continuousOn (fun _ h => h.1)
  have hc := (contDiff_cross (k := 1)).continuous.comp_continuousOn
    (continuous_snd.continuousOn.prodMk hB)
  simp only [goodConeDensity,dot_eq_inner]
  exact (((hE.add hc).norm.add (continuous_snd.continuousOn.inner hB).abs).pow 2).add
    (hP.sub (continuous_snd.continuousOn.inner hF))

lemma goodConeDensity_cone_continuous {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) (x₀ : Vec) :
    ContinuousOn (fun p : ℝ × Sphere =>
      (T-p.1)^2 * goodConeDensity s (p.1,x₀-(T-p.1) • p.2.1) p.2.1) (Icc 0 T ×ˢ univ) := by
  have hn : Continuous (fun p : ℝ × Sphere => p.2.1) := continuous_subtype_val.comp continuous_snd
  have hx : Continuous (fun p : ℝ × Sphere => x₀-(T-p.1) • p.2.1) :=
    continuous_const.sub ((continuous_const.sub continuous_fst).smul hn)
  have hmap : Continuous (fun p : ℝ × Sphere => ((p.1,x₀-(T-p.1) • p.2.1),p.2.1)) :=
    (continuous_fst.prodMk hx).prodMk hn
  have hg : ContinuousOn (fun p : ℝ × Sphere =>
      goodConeDensity s (p.1,x₀-(T-p.1) • p.2.1) p.2.1) (Icc 0 T ×ˢ univ) := by
    apply (goodConeDensity_continuousOn hs hT).comp hmap.continuousOn
    intro p hp
    exact ⟨⟨hp.1,mem_univ _⟩,mem_univ _⟩
  have hw : Continuous (fun p : ℝ × Sphere => (T-p.1)^2) :=
    (continuous_const.sub continuous_fst).pow 2
  convert! hw.continuousOn.mul hg using 1
  all_goals try with_reducible_and_instances rfl

lemma nullConeFlux_sphere_continuous {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (R : ℝ) (x₀ : Vec) :
    Continuous (fun n : Sphere => nullConeFlux s R x₀ t n) := by
  have hc : Continuous (fun n : Sphere => radialConeProfile s t (R-t) x₀ (R-t) n) :=
    (continuous_radialConeProfile hs ht (R-t) x₀).comp
      (continuous_const.prodMk continuous_id)
  convert! hc.comp continuous_neg using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [Function.comp_apply,nullConeFlux,radialConeProfile,coe_neg_sphere,smul_neg,
    ← sub_eq_add_neg,dot_eq_inner,inner_neg_left]
  ring

lemma goodConeDensity_sphere_integral_bound {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x₀ : Vec) :
    (∫ n : Sphere, (T-t)^2 * goodConeDensity s (t,x₀-(T-t) • n.1) n.1 ∂sphereMeasure) ≤
      4*(∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) := by
  rw [← integral_const_mul]
  apply integral_mono
  · have hc := (goodConeDensity_cone_continuous hs (ht.1.trans ht.2) x₀).comp_continuous
      (continuous_const.prodMk continuous_id) (fun n => ⟨ht,mem_univ n⟩)
    exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  · exact integrableOn_univ.mp (((nullConeFlux_sphere_continuous hs ht T x₀).const_mul 4).continuousOn.integrableOn_compact isCompact_univ)
  · intro n
    have hn := (goodConeDensity_bounds hs ht (x₀-(T-t) • n.1) (sphere_norm n)).2
    dsimp [nullConeFlux]
    nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg (T-t))]

lemma goodConeDensity_time_integral_bound {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
     (hT : 0 ≤ T) (x₀ : Vec) :
    (∫ t in 0..T, ∫ n : Sphere,
      (T-t)^2 * goodConeDensity s (t,x₀-(T-t) • n.1) n.1 ∂sphereMeasure) ≤
        4*(∫ x : Vec, totalEnergy s (0,x)) := by
  let F : ℝ → ℝ := fun t => ∫ n : Sphere,
    (T-t)^2 * goodConeDensity s (t,x₀-(T-t) • n.1) n.1 ∂sphereMeasure
  have hFi : ContinuousOn F (Icc 0 T) := by
    apply continuousOn_integral_of_compact_support (k := univ) isCompact_univ
      (goodConeDensity_cone_continuous hs hT x₀)
    intro t n _ hn
    exact (hn (mem_univ n)).elim
  have hNi := (null_cone_flux hs hT x₀).1
  have hFint : IntegrableOn F (Ioo 0 T) :=
    (hFi.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hle : (∫ t in Ioo 0 T, F t) ≤
      ∫ t in Ioo 0 T, 4*(∫ n : Sphere, nullConeFlux s T x₀ t n ∂sphereMeasure) := by
    apply integral_mono_ae hFint (hNi.const_mul 4)
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro t ht
    exact goodConeDensity_sphere_integral_bound hs ⟨ht.1.le,ht.2.le⟩ x₀
  rw [integral_const_mul] at hle
  simp only [restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le hT] at hle
  have hbound := (null_cone_flux hs hT x₀).2
  exact le_trans hle (by linarith)

end RVM.EnergyPrefix

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ArrivalDomain
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
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM
namespace EnergyPrefix

lemma mono {s : Solution} {T U : ℝ} (hs : EnergyPrefix s T) (hU : U ≤ T) :
    EnergyPrefix s U := by
  have hc : Icc (0 : ℝ) U ⊆ Icc 0 T := Icc_subset_Icc_right hU
  have ho : Ioo (0 : ℝ) U ⊆ Ioo 0 T := Ioo_subset_Ioo_right hU
  refine ⟨hs.f_smooth.mono (prod_mono hc Subset.rfl),
    hs.E_smooth.mono (prod_mono hc Subset.rfl),
    hs.B_smooth.mono (prod_mono hc Subset.rfl),
    fun t ht => hs.nonnegative t (hc ht),?_,?_,?_,
    fun t ht => hs.vlasov t (ho ht),fun t ht => hs.maxwell t (ho ht)⟩
  · obtain ⟨F,hF,hrep⟩ := hs.E_L2
    exact ⟨F,hF.mono hc,fun t ht => hrep t (hc ht)⟩
  · obtain ⟨F,hF,hrep⟩ := hs.B_L2
    exact ⟨F,hF.mono hc,fun t ht => hrep t (hc ht)⟩
  · obtain ⟨K,hK,hrep⟩ := hs.compact
    exact ⟨K,hK,fun t ht => hrep t (hc ht)⟩

end EnergyPrefix

end RVM
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_PhaseAcceleration
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
open scoped Topology ContDiff NNReal ENNReal

namespace RVM

lemma dyadicWindow_index_le {k n m : ℕ} {x : ℝ}
    (hn : DyadicWindow k n x) (hm : DyadicWindow k m x) : m≤n+2*k := by
  have hpk : 0<(2:ℝ)^k := by positivity
  have hx : 0≤x := by
    by_contra hh
    have he := mul_neg_of_pos_of_neg (by positivity : 0<(2:ℝ)^n) (lt_of_not_ge hh)
    have hp : 0<1/(2:ℝ)^k := by positivity
    linarith [hn.1]
  by_contra hnm
  have hi : n+(2*k+1) ≤ m := by omega
  have he := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hi) hx
  have hlo : 2*(2:ℝ)^k ≤ (2:ℝ)^(n+(2*k+1))*x := by
    calc
      _ = (1/(2:ℝ)^k)*(2:ℝ)^(2*k+1) := by
        rw [pow_add,show 2*k=k*2 from Nat.mul_comm _ _,pow_mul]; norm_num; field_simp
      _ ≤ ((2:ℝ)^n*x)*(2:ℝ)^(2*k+1) :=
        mul_le_mul_of_nonneg_right hn.1 (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hh := hlo.trans (he.trans hm.2)
  linarith

lemma dyadicWindow_card_le (k : ℕ) (S : Finset ℕ) {x : ℝ}
    (hS : ∀ n∈S, DyadicWindow k n x) : S.card≤4*k+1 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨n,hn⟩ := hs
    have hsub : S⊆Finset.Icc (n-2*k) (n+2*k) := by
      intro m hm
      have hlo := dyadicWindow_index_le (hS m hm) (hS n hn)
      have hhi := dyadicWindow_index_le (hS n hn) (hS m hm)
      exact Finset.mem_Icc.mpr ⟨by omega,hhi⟩
    have hh := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hh
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceCellLast
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Set

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma EnergyPrefix.goodConeIntegrand_continuous {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    ContinuousOn (Function.uncurry (goodConeIntegrand s t x)) (Icc 0 t ×ˢ univ) :=
  EnergyPrefix.goodConeDensity_cone_continuous (hs.mono ht.2) ht.1 x

lemma EnergyPrefix.goodConeIntegrand_nonneg {s : Solution} {T t r : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (hr : r∈Icc 0 t) (x : Vec) (n : Sphere) :
    0≤goodConeIntegrand s t x r n :=
  mul_nonneg (sq_nonneg _) (EnergyPrefix.goodConeDensity_bounds (hs.mono ht.2) hr _ (sphere_norm n)).1

lemma EnergyPrefix.goodConeIntegrand_sphere_continuous {s : Solution} {T t r : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (hr : r∈Icc 0 t) (x : Vec) :
    Continuous (goodConeIntegrand s t x r) :=
  (hs.goodConeIntegrand_continuous ht x).comp_continuous
    (continuous_const.prodMk continuous_id) (fun n => ⟨hr,mem_univ n⟩)

lemma EnergyPrefix.goodConeIntegrand_sphere_integral_continuous {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    ContinuousOn (fun r => ∫ n : Sphere, goodConeIntegrand s t x r n ∂sphereMeasure) (Icc 0 t) := by
  apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ
    (hs.goodConeIntegrand_continuous ht x)
  exact fun r n _ hn => (hn (mem_univ n)).elim

lemma EnergyPrefix.goodConeIntegrand_lintegral_eq {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    (∫⁻ r in Icc 0 t, ∫⁻ n : Sphere, ENNReal.ofReal (goodConeIntegrand s t x r n) ∂sphereMeasure) =
      ENNReal.ofReal (∫ r in Icc 0 t, ∫ n : Sphere, goodConeIntegrand s t x r n ∂sphereMeasure) := by
  calc
    _ = ∫⁻ r in Icc 0 t, ENNReal.ofReal (∫ n : Sphere, goodConeIntegrand s t x r n ∂sphereMeasure) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro r hr
      exact (ofReal_integral_eq_lintegral_ofReal
        (integrableOn_univ.mp
          ((hs.goodConeIntegrand_sphere_continuous ht hr x).continuousOn.integrableOn_compact isCompact_univ))
        (ae_of_all _ (hs.goodConeIntegrand_nonneg ht hr x))).symm
    _ = _ := (ofReal_integral_eq_lintegral_ofReal
      ((hs.goodConeIntegrand_sphere_integral_continuous ht x).integrableOn_compact isCompact_Icc)
      (ae_restrict_of_forall_mem measurableSet_Icc
        (fun r hr => integral_nonneg (hs.goodConeIntegrand_nonneg ht hr x)))).symm

lemma EnergyPrefix.goodFieldConeMass_le_density {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    goodFieldConeMass s t x ≤
      ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere, ENNReal.ofReal (goodConeIntegrand s t x r n) ∂sphereMeasure := by
  apply setLIntegral_mono' measurableSet_Icc
  intro r hr
  apply lintegral_mono
  intro n
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hp := EnergyPrefix.particle_cone_nonneg (hs.mono ht.2) hr (x-(t-r) • n.1) (sphere_norm n)
  dsimp [goodConeDensity,goodField]
  linarith

lemma EnergyPrefix.goodFieldConeMass_bound {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t∈Icc 0 T) (x : Vec) :
    goodFieldConeMass s t x ≤ ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
  refine (hs.goodFieldConeMass_le_density ht x).trans ?_
  rw [hs.goodConeIntegrand_lintegral_eq ht x]
  apply ENNReal.ofReal_le_ofReal
  have hh := EnergyPrefix.goodConeDensity_time_integral_bound (hs.mono ht.2) ht.1 x
  simpa only [intervalIntegral.integral_of_le ht.1,integral_Icc_eq_integral_Ioc,goodConeIntegrand] using hh

lemma dyadicWindow_single_sum_indicator {α : Type*} (k : ℕ) (S : Finset ℕ)
    (G : ℕ → Set α) (p : α) (e : ℝ≥0∞) {x : ℝ}
    (hG : ∀ n∈S, p∈G n → DyadicWindow k n x) :
    (∑ n∈S, (G n).indicator (fun _ => e) p) ≤ (4*k+1 : ℕ)*e := by
  classical
  have hc : (S.filter (fun n => p∈G n)).card≤4*k+1 := by
    apply dyadicWindow_card_le
    intro n hn
    exact hG n (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
  have heq : (∑ n∈S, (G n).indicator (fun _ => e) p)=
      (S.filter (fun n => p∈G n)).card*e := by
    simp only [Set.indicator]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [heq]
  exact mul_le_mul' (by exact_mod_cast hc) le_rfl

lemma finset_sum_lintegral_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : Finset ι) (f : ι → α → ℝ≥0∞) :
    (∑ i∈S, ∫⁻ x, f i x ∂μ) ≤ ∫⁻ x, ∑ i∈S, f i x ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

lemma goodFieldBinConeMass_sum_le (s : Solution) (X a : ℝ → Vec)
    (k : ℕ) (S : Finset ℕ) (t : ℝ) :
    (∑ j∈S, goodFieldBinConeMass s X a k j t) ≤
      (4*k+1:ℕ)*goodFieldConeMass s t (X t) := by
  unfold goodFieldBinConeMass
  calc
    _ ≤ ∫⁻ r in Icc 0 t, ∑ j∈S, ∫⁻ n : Sphere,
        (receiverAngularSet a k j t).indicator (fun n =>
          ENNReal.ofReal ((t-r)^2 * goodField (s.E (r,X t-(t-r) • n.1))
            (s.B (r,X t-(t-r) • n.1)) n.1^2)) n ∂sphereMeasure :=
      finset_sum_lintegral_le _ _ _
    _ ≤ ∫⁻ r in Icc 0 t, ∫⁻ n : Sphere,
        (4*k+1:ℕ)*ENNReal.ofReal ((t-r)^2 * goodField (s.E (r,X t-(t-r) • n.1))
          (s.B (r,X t-(t-r) • n.1)) n.1^2) ∂sphereMeasure := by
      apply lintegral_mono
      intro r
      refine (finset_sum_lintegral_le _ _ _).trans (lintegral_mono (fun n => ?_))
      exact dyadicWindow_single_sum_indicator k S (receiverAngularSet a k · t) n _
        (fun j _ hj => hj)
    _ = _ := by
      simp only [goodFieldConeMass,lintegral_const_mul' _ _ (by finiteness : ((4*k+1:ℕ):ℝ≥0∞)≠⊤)]

lemma EnergyPrefix.goodFieldBudget_sum_bound {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (S : Finset ℕ) :
    (∑ j∈S, goodFieldBudget s X a k lo hi I j) ≤
      (ENNReal.ofReal I)⁻¹ * (4*k+1:ℕ) * ENNReal.ofReal (hi-lo) *
        ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
  unfold goodFieldBudget
  rw [← Finset.mul_sum]
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc lo hi,
        (4*k+1:ℕ)*ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
      apply mul_le_mul' le_rfl
      refine (finset_sum_lintegral_le _ _ _).trans ?_
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      exact (goodFieldBinConeMass_sum_le s X a k S t).trans
        (mul_le_mul' le_rfl (hs.goodFieldConeMass_bound (hJ ht) (X t)))
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      ac_rfl

lemma EnergyPrefix.goodFieldBudget_tsum_bound {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) :
    (∑' j : ℕ, goodFieldBudget s X a k lo hi I j) ≤
      (ENNReal.ofReal I)⁻¹ * (4*k+1:ℕ) * ENNReal.ofReal (hi-lo) *
        ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (hs.goodFieldBudget_sum_bound X a k hJ)

lemma EnergyPrefix.goodFieldBudget_uniform_oai {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (X a : ℝ → Vec) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (hI : 0<I) (hlen : hi-lo≤I) :
    (∑' j : ℕ, goodFieldBudget s X a k lo hi I j) ≤
      (4*k+1:ℕ)*ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by
  have hnorm : (ENNReal.ofReal I)⁻¹*ENNReal.ofReal (hi-lo)≤1 := by
    calc
      _ ≤ (ENNReal.ofReal I)⁻¹*ENNReal.ofReal I :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hlen)
      _ = 1 := ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hI).ne' ENNReal.ofReal_ne_top
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹ * (4*k+1:ℕ) * ENNReal.ofReal (hi-lo) *
        ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) :=
      hs.goodFieldBudget_tsum_bound X a k hJ
    _ = (4*k+1:ℕ)*((ENNReal.ofReal I)⁻¹*ENNReal.ofReal (hi-lo))*
        ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y))) := by ac_rfl
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul' (mul_le_mul' le_rfl hnorm)
        (le_refl (ENNReal.ofReal (4*(∫ y : Vec, totalEnergy s (0,y)))))

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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

end

end OAI
end

theorem solution : type_of% @OAI.RVM.EnergyPrefix.goodFieldBudget_uniform_oai := @OAI.RVM.EnergyPrefix.goodFieldBudget_uniform_oai
