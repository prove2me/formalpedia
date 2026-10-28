-- Prove2me | solution 1 for OAI.RVM.Admissible.direct_remaining_source_short_uniform_expanded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:39:10.225775+00:00
-- url     : https://prove2.me/submissions/d44fb72b-0604-40c5-8dfd-652350cc6573

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direct_source_shared_short_angles_expanded
import Theorems.Thm_OAI_RVM_EnergyPrefix_goodFieldBudget_uniform

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

lemma poynting_norm_le_energy (E B : Vec) :
    ‖cross E B‖ ≤ (‖E‖^2+‖B‖^2)/2 := by
  have h := norm_cross_le E B
  nlinarith [sq_nonneg (‖E‖-‖B‖)]

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

lemma prefix_continuous_integral_norm_sq {F : Field} (hF : ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec), ContinuousOn F₂ (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t,x))) :
    ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Icc 0 T) := by
  obtain ⟨F₂,hc,heq⟩ := hF
  have hh : ∀ t ∈ Icc (0:ℝ) T, (∫ x : Vec, ‖F (t,x)‖^2) = ‖F₂ t‖^2 := by
    intro t ht
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [heq t ht] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  exact (hc.norm.pow 2).congr (fun t ht => hh t ht)

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

lemma integrated_energy_continuous (hs : EnergyPrefix s T) :
    ContinuousOn (fun t => ∫ x : Vec, totalEnergy s (t,x)) (Icc 0 T) := by
  obtain ⟨K,hK,hz⟩ := particle_energy_compact hs
  have hp : ContinuousOn (fun t => ∫ x : Vec, particleEnergy s (t,x)) (Icc 0 T) :=
    continuousOn_integral_uniform_support hK
      (particle_energy_continuous_slab hs) hz
  have he := prefix_continuous_integral_norm_sq hs.E_L2
  have hb := prefix_continuous_integral_norm_sq hs.B_L2
  apply ((he.add hb).div_const 2 |>.add hp).congr
  intro t ht
  change (∫ x : Vec, (‖s.E (t,x)‖^2+‖s.B (t,x)‖^2)/2+particleEnergy s (t,x)) =
    ((∫ x : Vec, ‖s.E (t,x)‖^2)+(∫ x : Vec, ‖s.B (t,x)‖^2))/2+
      (∫ x : Vec, particleEnergy s (t,x))
  calc
    _ = (∫ x : Vec, (‖s.E (t,x)‖^2+‖s.B (t,x)‖^2)/2)+
        (∫ x : Vec, particleEnergy s (t,x)) :=
      integral_add (((prefix_integrable_norm_sq hs.E_L2 ht).add
        (prefix_integrable_norm_sq hs.B_L2 ht)).div_const 2)
        (particle_energy_integrable hs ht)
    _ = _ := by
      rw [integral_div, integral_add (prefix_integrable_norm_sq hs.E_L2 ht)
        (prefix_integrable_norm_sq hs.B_L2 ht)]

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

lemma deriv_weighted_energy (hs : EnergyPrefix s T) {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r => ∫ x : Vec, g x * totalEnergy s (r,x))
      (∫ x : Vec, fderiv ℝ g x (totalFlux s (t,x))) t := by
  have hE := total_energy_regular hs
  have hF : ContDiffOn ℝ 1 (fun p : ℝ × Vec => g p.2 * totalEnergy s p)
      (Ioo 0 T ×ˢ (univ : Set Vec)) := (hg.comp contDiff_snd).contDiffOn.mul hE
  have hz : ∀ r ∈ Ioo (0:ℝ) T, ∀ x ∉ tsupport g, g x * totalEnergy s (r,x) = 0 := by
    intro r _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
  have hd := hasFDerivAt_integral_uniform_support isOpen_Ioo hc ht hF hz
  have hi := fderiv_integral_uniform_support_apply isOpen_Ioo hc ht hF hz (1:ℝ)
  have heq : ∀ x : Vec,
      fderiv ℝ (fun p : ℝ × Vec => g p.2 * totalEnergy s p) (t,x) (1,0) =
        -g x * divergence (fun y => totalFlux s (t,y)) x := by
    intro x
    have he := hE.contDiffAt (x := (t,x)) (IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_univ) ⟨ht,mem_univ x⟩)
    have heT : DifferentiableAt ℝ (fun r => totalEnergy s (r,x)) t :=
      DifferentiableAt.comp t (f := fun r : ℝ => (r,x)) (g := totalEnergy s)
        (he.differentiableAt (by simp))
        (differentiableAt_id.prodMk (differentiableAt_const x))
    have hgT : HasDerivAt (fun r => g x * totalEnergy s (r,x))
        (g x * deriv (fun r => totalEnergy s (r,x)) t) t :=
      heT.hasDerivAt.const_mul (g x)
    have hf := hF.contDiffAt (x := (t,x)) (IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_univ) ⟨ht,mem_univ x⟩)
    rw [← deriv_time_slice (hf.differentiableAt (by simp)), hgT.deriv]
    have hl := local_energy_conservation hs ht x
    rw [show deriv (fun r => totalEnergy s (r,x)) t =
      -divergence (fun y => totalFlux s (t,y)) x by linarith]
    ring
  have hS : ContDiff ℝ 1 (fun x => totalFlux s (t,x)) := by
    apply contDiffOn_univ.mp
    exact (total_flux_regular hs).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht,mem_univ x⟩)
  have hh : deriv (fun r => ∫ x : Vec, g x * totalEnergy s (r,x)) t =
      ∫ x : Vec, fderiv ℝ g x (totalFlux s (t,x)) := by
    change fderiv ℝ (fun r => ∫ x : Vec, g x * totalEnergy s (r,x)) t 1 = _
    rw [hi]
    simp only [heq, neg_mul, integral_neg]
    rw [integral_mul_divergence hS hg hc, neg_neg]
  exact hh ▸ hd.differentiableAt.hasDerivAt

lemma total_energy_continuous_slab (hs : EnergyPrefix s T) :
    ContinuousOn (totalEnergy s) (Icc 0 T ×ˢ (univ : Set Vec)) := by
  exact ((hs.E_smooth.continuousOn.norm.pow 2).add
    (hs.B_smooth.continuousOn.norm.pow 2)).div_const 2 |>.add
      (particle_energy_continuous_slab hs)

lemma weighted_energy_continuous (hs : EnergyPrefix s T) {g : Vec → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    :
    ContinuousOn (fun t => ∫ x : Vec, g x * totalEnergy s (t,x)) (Icc 0 T) := by
  apply continuousOn_integral_uniform_support hc
    ((hg.comp continuous_snd).continuousOn.mul (total_energy_continuous_slab hs))
  intro t _ x hx
  change g x * totalEnergy s (t,x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]

lemma weighted_energy_deriv_bound (hs : EnergyPrefix s T) {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ‖deriv (fun r => ∫ x : Vec, g x * totalEnergy s (r,x)) t‖ ≤
      C * (∫ x : Vec, totalEnergy s (t,x)) := by
  rw [(deriv_weighted_energy hs hg hc ht).deriv]
  have hS : Continuous (fun x : Vec => totalFlux s (t,x)) := by
    apply ContinuousOn.comp_continuous (total_flux_regular hs).continuousOn
      (continuous_const.prodMk continuous_id)
    intro x
    exact ⟨ht,mem_univ x⟩
  have hi : Integrable (fun x => fderiv ℝ g x (totalFlux s (t,x))) :=
    ((hg.continuous_fderiv (by simp)).clm_apply hS).integrable_of_hasCompactSupport
      (compactSupport_of_zero_off (hc.fderiv ℝ) (by
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport hx, zero_apply]))
  calc
    _ ≤ ∫ x : Vec, ‖fderiv ℝ g x (totalFlux s (t,x))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : Vec, C * totalEnergy s (t,x) := by
      apply integral_mono hi.norm ((total_energy_integrable hs (Ioo_subset_Icc_self ht)).const_mul C)
      intro x
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hb x) (total_flux_bound hs (Ioo_subset_Icc_self ht) x) (norm_nonneg _) hC)
    _ = _ := integral_const_mul _ _

lemma weighted_energy_increment_bound (hs : EnergyPrefix s T) {g : Vec → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    {C B : ℝ} (hC : 0 ≤ C) (hb : ∀ x, ‖fderiv ℝ g x‖ ≤ C)
    (hT : 0 ≤ T) (hB : ∀ t ∈ Icc 0 T, (∫ x : Vec, totalEnergy s (t,x)) ≤ B) :
    ‖(∫ x : Vec, g x * totalEnergy s (T,x)) - (∫ x : Vec, g x * totalEnergy s (0,x))‖ ≤ C * B * T := by
  rcases eq_or_lt_of_le hT with he | ht
  · subst T; simp
  let F : ℝ → ℝ := fun t => ∫ x : Vec, g x * totalEnergy s (t,x)
  have hcont : ContinuousOn F (Icc 0 T) := weighted_energy_continuous hs hg.continuous hc
  have hdiff : DifferentiableOn ℝ F (Ioo 0 T) := fun t ht =>
    (deriv_weighted_energy hs hg hc ht).differentiableAt.differentiableWithinAt
  obtain ⟨c,hcT,heq⟩ := exists_deriv_eq_slope F ht hcont hdiff
  have hder : ‖deriv F c‖ ≤ C * B :=
    (weighted_energy_deriv_bound hs hg hc hC hb hcT).trans
      (mul_le_mul_of_nonneg_left (hB c ⟨hcT.1.le,hcT.2.le⟩) hC)
  rw [heq, sub_zero, norm_div, Real.norm_of_nonneg hT] at hder
  exact (div_le_iff₀ ht).mp hder

theorem energy_conservation (hs : EnergyPrefix s T) (hT : 0 ≤ T) :
    (∫ x : Vec, totalEnergy s (T,x)) = ∫ x : Vec, totalEnergy s (0,x) := by
  obtain ⟨C,hC,hb⟩ := energyCutoff_deriv_bound
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).bddAbove_image
    (integrated_energy_continuous hs)
  have hB' : ∀ t ∈ Icc 0 T, (∫ x : Vec, totalEnergy s (t,x)) ≤ B :=
    fun t ht => hB ⟨t,ht,rfl⟩
  have hinc (n : ℕ) :
      ‖(∫ x : Vec, energyCutoff n x * totalEnergy s (T,x)) -
        (∫ x : Vec, energyCutoff n x * totalEnergy s (0,x))‖ ≤
          (C / ((n:ℝ)+1)) * B * T :=
    weighted_energy_increment_bound hs (energyCutoff_smooth n) (energyCutoff_compact n)
      (div_nonneg hC (by positivity)) (hb n) hT hB'
  have hl := ((energyCutoff_integral_tendsto (total_energy_integrable hs ⟨hT,le_rfl⟩)).sub
    (energyCutoff_integral_tendsto (total_energy_integrable hs ⟨le_rfl,hT⟩))).norm
  have hr : Filter.Tendsto (fun n : ℕ => (C / ((n:ℝ)+1)) * B * T) Filter.atTop (𝓝 0) := by
    have hi : Filter.Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [div_eq_mul_inv,mul_zero,zero_mul] using ((hi.const_mul C).mul_const B).mul_const T
  have he := le_of_tendsto_of_tendsto' hl hr hinc
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm he (norm_nonneg _)))

end EnergyPrefix

end RVM

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

namespace RVM

lemma EnergyPrefix.magnetic_lintegral_bound {s : Solution} {T t : ℝ}
    (hs : EnergyPrefix s T) (ht : t ∈ Icc 0 T) :
    (∫⁻ x : Vec, ENNReal.ofReal (‖s.B (t,x)‖^2)) ≤
      ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (EnergyPrefix.prefix_integrable_norm_sq hs.B_L2 ht)
    (ae_of_all _ (fun x => sq_nonneg ‖s.B (t,x)‖))]
  apply ENNReal.ofReal_le_ofReal
  rw [← (hs.mono ht.2).energy_conservation ht.1,← integral_const_mul]
  apply integral_mono (EnergyPrefix.prefix_integrable_norm_sq hs.B_L2 ht)
    ((hs.total_energy_integrable ht).const_mul 2)
  intro x
  dsimp only [totalEnergy]
  nlinarith [hs.particle_energy_nonneg ht x,sq_nonneg ‖s.E (t,x)‖]

lemma arrivalAngularSet_sum_indicator (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ)
    (k : ℕ) (S : Finset ℕ) (p : ℝ × Vec) (e : ℝ≥0∞) :
    (∑ j∈S, (arrivalAngularSet α zX T k j).indicator (fun _ => e) p) ≤
      (2*(4*k+1):ℕ)*e := by
  classical
  let G₁ : ℕ → Set (ℝ × Vec) := fun j =>
    {r | r∈arrivalDomain α zX T ∧ DyadicWindow k j (Real.sqrt ((1-dot
      (arrivalDirection α zX T r) (arrivalVelocity α zX T r))/2))}
  let G₂ : ℕ → Set (ℝ × Vec) := fun j =>
    {r | r∈arrivalFinalDomain α zX T ∧ DyadicWindow k j (Real.sqrt ((1-dot
      ((T-r.1)⁻¹ • ((α zX T).1-r.2)) (velocity (α zX T).2))/2))}
  have h₁ := dyadicWindow_single_sum_indicator k S G₁ p e (fun _ _ h => h.2)
  have h₂ := dyadicWindow_single_sum_indicator k S G₂ p e (fun _ _ h => h.2)
  have hpart (j : ℕ) : (arrivalAngularSet α zX T k j).indicator (fun _ => e) p ≤
      (G₁ j).indicator (fun _ => e) p+(G₂ j).indicator (fun _ => e) p := by
    by_cases hp : p∈arrivalAngularSet α zX T k j
    · rw [indicator_of_mem hp]
      rcases hp with h|h
      · rw [indicator_of_mem (show p∈G₁ j from h)]
        exact le_add_right le_rfl
      · rw [indicator_of_mem (show p∈G₂ j from h)]
        exact le_add_left le_rfl
    · rw [indicator_of_notMem hp]; exact zero_le
  calc
    _ ≤ ∑ j∈S, ((G₁ j).indicator (fun _ => e) p+(G₂ j).indicator (fun _ => e) p) :=
      Finset.sum_le_sum (fun j _ => hpart j)
    _ ≤ (4*k+1:ℕ)*e+(4*k+1:ℕ)*e := by
      rw [Finset.sum_add_distrib]
      exact add_le_add h₁ h₂
    _ = _ := by push_cast; ring

lemma EnergyPrefix.magneticFieldBudget_sum_bound {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (α : Phase → ℝ → Phase) (zX : Phase) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (S : Finset ℕ) :
    (∑ j∈S, magneticFieldBudget s α zX T k lo hi I j) ≤
      (ENNReal.ofReal I)⁻¹*(2*(4*k+1):ℕ)*ENNReal.ofReal (hi-lo)*
        ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
  unfold magneticFieldBudget
  rw [← Finset.mul_sum]
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹ * ∫⁻ t in Icc lo hi, ∫⁻ x : Vec,
        (2*(4*k+1):ℕ)*ENNReal.ofReal (‖s.B (t,x)‖^2) := by
      apply mul_le_mul' le_rfl
      refine (finset_sum_lintegral_le _ _ _).trans ?_
      apply lintegral_mono
      intro t
      exact (finset_sum_lintegral_le _ _ _).trans
        (lintegral_mono (fun x => arrivalAngularSet_sum_indicator α zX T k S (t,x) _))
    _ ≤ (ENNReal.ofReal I)⁻¹ * ∫⁻ _t in Icc lo hi,
        (2*(4*k+1):ℕ)*ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [lintegral_const_mul' _ _ (by finiteness : ((2*(4*k+1):ℕ):ℝ≥0∞)≠⊤)]
      exact mul_le_mul' le_rfl (hs.magnetic_lintegral_bound (hJ ht))
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
      ac_rfl

lemma EnergyPrefix.magneticFieldBudget_tsum_bound {s : Solution} {T lo hi I : ℝ}
    (hs : EnergyPrefix s T) (α : Phase → ℝ → Phase) (zX : Phase) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) :
    (∑' j : ℕ, magneticFieldBudget s α zX T k lo hi I j) ≤
      (ENNReal.ofReal I)⁻¹*(2*(4*k+1):ℕ)*ENNReal.ofReal (hi-lo)*
        ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le (hs.magneticFieldBudget_sum_bound α zX k hJ)

lemma EnergyPrefix.magneticFieldBudget_uniform {s : Solution} {T lo hi I C : ℝ}
    (hs : EnergyPrefix s T) (α : Phase → ℝ → Phase) (zX : Phase) (k : ℕ)
    (hJ : Icc lo hi⊆Icc (0:ℝ) T) (hI : 0<I) (hC : 0≤C) (hlen : hi-lo≤C*I) :
    (∑' j : ℕ, magneticFieldBudget s α zX T k lo hi I j) ≤
      (2*(4*k+1):ℕ)*ENNReal.ofReal C*ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by
  have hnorm : (ENNReal.ofReal I)⁻¹*ENNReal.ofReal (hi-lo)≤ENNReal.ofReal C := by
    calc
      _ ≤ (ENNReal.ofReal I)⁻¹*ENNReal.ofReal (C*I) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hlen)
      _ = _ := by
        rw [ENNReal.ofReal_mul hC,mul_left_comm,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hI).ne' ENNReal.ofReal_ne_top,mul_one]
  calc
    _ ≤ (ENNReal.ofReal I)⁻¹*(2*(4*k+1):ℕ)*ENNReal.ofReal (hi-lo)*
        ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) :=
      hs.magneticFieldBudget_tsum_bound α zX k hJ
    _ = (2*(4*k+1):ℕ)*((ENNReal.ofReal I)⁻¹*ENNReal.ofReal (hi-lo))*
        ENNReal.ofReal (2*(∫ x : Vec, totalEnergy s (0,x))) := by ac_rfl
    _ ≤ _ := mul_le_mul' (mul_le_mul' le_rfl hnorm) le_rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_MomentumDirection
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
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff



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

open Set MeasureTheory
open scoped ENNReal

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

open scoped Topology ContDiff ENNReal

open scoped Topology ContDiff NNReal

open scoped Topology ContDiff

open Set

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma sourceRepresentative_sum_bound {x : ℝ} (hx : 0≤x) (S : Finset ℕ)
    (hS : ∀n∈S,sourceRepresentative n≤x) : ∑n∈S,sourceRepresentative n≤2*x := by
  classical
  have hgeom (N : ℕ) : ∑n∈Finset.range (N+1),sourceRepresentative n≤2*sourceRepresentative N := by
    induction N with
    | zero => norm_num [sourceRepresentative]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have he : sourceRepresentative (N+1)=2*sourceRepresentative N := by
        dsimp only [sourceRepresentative]
        rw [pow_succ]
        ring
      rw [he]
      linarith
  by_cases hne : S.Nonempty
  · let N := S.max' hne
    have hsub : S⊆Finset.range (N+1) := by
      intro n hn
      apply Finset.mem_range.mpr
      have hh := S.le_max' n hn
      change n≤N at hh
      omega
    have hs : (∑n∈S,sourceRepresentative n)≤∑n∈Finset.range (N+1),sourceRepresentative n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by dsimp only [sourceRepresentative]; positivity)
    exact hs.trans ((hgeom N).trans (mul_le_mul_of_nonneg_left (hS N (S.max'_mem hne)) (by norm_num)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DyadicBalanceConstant
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
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma dyadicBalanceConstant_pos {α β : ℝ} (hα : 0<α) (hβ : 0<β) :
    0<dyadicBalanceConstant α β := by
  have ha : 0<1-((2:ℝ)^α)⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hα))
  have hb : 0<1-((2:ℝ)^β)⁻¹ := sub_pos.mpr
    (inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num : (1:ℝ)<2) hβ))
  unfold dyadicBalanceConstant
  positivity

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_NormalisedPartialCutoff
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma product_le_min_scale {P p w : ℝ} (hp : 0≤p) (hw : 0≤w)
    (hpP : p≤P) (hwP : w≤P) : w*p≤P*min p w := by
  rcases le_total p w with h|h
  · rw [min_eq_left h]
    exact mul_le_mul_of_nonneg_right hwP hp
  · rw [min_eq_right h]
    calc w*p≤w*P := mul_le_mul_of_nonneg_left hpP hw
         _ = P*w := by ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CappedRepresentativePos
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma cappedRepresentative_pos (n : ℕ) : 0 < cappedRepresentative n := by
  dsimp [cappedRepresentative]
  positivity

lemma cappedRepresentative_le_one (n : ℕ) : cappedRepresentative n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ClosedEulerianTimeBudget
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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma capped_positive_power_sum {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤x) :
    ∑j∈S,(cappedRepresentative j/x)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  classical
  have hbase : 0<((2:ℝ)⁻¹)^α := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : ((2:ℝ)⁻¹)^α<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hnorm : ‖((2:ℝ)⁻¹)^α‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hbase]; exact hbase1
  by_cases hne : S.Nonempty
  · let j₀ := S.min' hne
    have hj₀ : j₀∈S := S.min'_mem hne
    have hjmin (j : ℕ) (hj : j∈S) : j₀≤j := S.min'_le j hj
    have hp (j : ℕ) (hj : j∈S) : cappedRepresentative j/x≤((2:ℝ)⁻¹)^(j-j₀) := by
      have he : cappedRepresentative j=cappedRepresentative j₀*((2:ℝ)⁻¹)^(j-j₀) := by
        dsimp only [cappedRepresentative]
        rw [←pow_add,Nat.add_sub_of_le (hjmin j hj)]
      rw [he]
      apply (div_le_iff₀ hx).mpr
      have hh := mul_le_mul_of_nonneg_right (hS j₀ hj₀)
        (pow_nonneg (by norm_num : (0:ℝ)≤2⁻¹) (j-j₀))
      simpa only [mul_comm] using hh
    have hpoint (j : ℕ) (hj : j∈S) : (cappedRepresentative j/x)^α≤(((2:ℝ)⁻¹)^α)^(j-j₀) := by
      rw [Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2⁻¹)]
      exact Real.rpow_le_rpow (div_nonneg (cappedRepresentative_pos j).le hx.le) (hp j hj) hα.le
    have hinj : Set.InjOn (fun j : ℕ=>j-j₀) S := by
      intro i hi j hj hij
      have hi' := hjmin i hi
      have hj' := hjmin j hj
      change i-j₀=j-j₀ at hij
      omega
    calc
      _ ≤ ∑j∈S,(((2:ℝ)⁻¹)^α)^(j-j₀) := Finset.sum_le_sum hpoint
      _ = ∑m∈S.image (fun j=>j-j₀),(((2:ℝ)⁻¹)^α)^m := (Finset.sum_image hinj).symm
      _ ≤ ∑'m : ℕ,(((2:ℝ)⁻¹)^α)^m :=
        (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum _ (fun _ _=>by positivity)
      _ = _ := tsum_geometric_of_norm_lt_one hnorm
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hbase1.le)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_IndexTwoPow
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma index_lt_of_two_pow_le {n N : ℕ} {B : ℝ}
    (hn : (2:ℝ)^n ≤ B) (hN : B < (2:ℝ)^N) : n<N := by
  by_contra hc
  have he := pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) (Nat.le_of_not_gt hc)
  exact (not_lt_of_ge (he.trans hn)) hN

lemma cappedRepresentative_mul_pow (n : ℕ) : cappedRepresentative n*(2:ℝ)^n=1 := by
  simp [cappedRepresentative,inv_pow]

end RVM

open Set

namespace RVM

lemma exists_dyadic_count_log {B : ℝ} (hB : 1 ≤ B) :
    ∃N : ℕ, B < (2:ℝ)^N ∧ (N:ℝ) ≤ 2+Real.log B/Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ Real.log B/Real.log 2 := div_nonneg (Real.log_nonneg hB) h2.le
  let n := ⌈Real.log B/Real.log 2⌉₊
  refine ⟨n+1,?_,?_⟩
  · apply (Real.log_lt_log_iff (zero_lt_one.trans_le hB) (by positivity)).mp
    rw [Real.log_pow,Nat.cast_add,Nat.cast_one]
    have hc : Real.log B/Real.log 2 < (n:ℝ)+1 := by
      have hh := Nat.le_ceil (Real.log B/Real.log 2)
      dsimp [n]
      linarith only [hh]
    exact (div_lt_iff₀ h2).mp hc
  · have hh : (n:ℝ) < Real.log B/Real.log 2+1 := Nat.ceil_lt_add_one h0
    push_cast
    linarith only [hh]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_RelativeCauchyConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relativeCauchyConstant_nonneg {C E Z : ℝ} (hC : 0≤C) :
    0 ≤ relativeCauchyConstant C E Z := by unfold relativeCauchyConstant; positivity

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RadialSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section
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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma capped_positive_power_sum_unscaled {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤x) :
    ∑j∈S,(cappedRepresentative j)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹*x^α := by
  have hh := capped_positive_power_sum hx hα S hS
  have he (j : ℕ) : (cappedRepresentative j/x)^α=(cappedRepresentative j)^α/x^α :=
    Real.div_rpow (cappedRepresentative_pos j).le hx.le α
  simp_rw [he] at hh
  rw [←Finset.sum_div] at hh
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hx α)).mp hh


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma Admissible.datumEnergyNumber_nonneg {d : Datum} (hd : Admissible d) :
    0≤datumEnergyNumber d := by
  apply integral_nonneg
  intro x
  apply add_nonneg (by positivity)
  exact integral_nonneg (fun v=>mul_nonneg (q_pos v).le (hd.2.2.1 _))

lemma SmoothClassicalPrefix.initial_energy_eq {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) :
    (∫x : Vec,totalEnergy s (0,x))=datumEnergyNumber d := by
  unfold totalEnergy particleEnergy datumEnergyNumber
  simp only [hs.initial_E,hs.initial_B,hs.initial_f]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionOverlap
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

lemma SmoothClassicalPrefix.energyPrefix {d : Datum} {s : Solution} {H : ℝ}
    (hs : SmoothClassicalPrefix d s H) : EnergyPrefix s H := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro t ht x v
    have hh := (hs.equations t ht.1.le ht.2).1 x v
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro t ht x
    have he := (hs.equations t ht.1.le ht.2).2.1 x
    have hb := (hs.equations t ht.1.le ht.2).2.2.1 x
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

end RVM

open Set MeasureTheory
open scoped ENNReal

end

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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_TransportRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma relativeAngularConstant_nonneg {K κ e : ℝ} (hK : 0≤K) (hκ : 0≤κ) (he : 1/4<e) :
    0 ≤ relativeAngularConstant K κ e := by
  have h0 : 0≤e := by linarith
  have h1 : 0≤e-1/4 := by linarith
  unfold relativeAngularConstant
  apply add_nonneg
  · exact mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) h0))) (Real.rpow_nonneg hK _)
  · exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) h1))) (Real.rpow_nonneg hK _)) (Real.rpow_nonneg hκ _)


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SharedBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relativeCauchyConstant_factor (C E Z : ℝ) :
    relativeCauchyConstant C E Z=relativeCauchyConstant C E 1*Real.sqrt Z := by
  simp only [relativeCauchyConstant,Real.sqrt_one,mul_one]
  ring

lemma SmoothClassicalPrefix.directReceiverGoodBudget_sum {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hd : Admissible d) (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {a b I : ℝ} (ha : 0≤a) (hb : b≤T) (hI : 0<I) (hJI : b-a≤I) :
    Summable (directReceiverGoodBudget s F zX a b I) ∧
    (∑'n,directReceiverGoodBudget s F zX a b I n)≤20*datumEnergyNumber d := by
  have hJ : Icc a b⊆Icc (0:ℝ) T := fun _ ht=>⟨ha.trans ht.1,ht.2.trans hb⟩
  have hh := hs.energyPrefix.goodFieldBudget_uniform (fun t=>(prefixFlow F.flow T zX t).1)
    (fun t=>velocity (prefixFlow F.flow T zX t).2) 1 hJ hI hJI
  rw [hs.initial_energy_eq] at hh
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hh
  have he : (5:ℝ≥0∞)*ENNReal.ofReal (4*datumEnergyNumber d)=ENNReal.ofReal (20*datumEnergyNumber d) := by
    rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5)]
    congr 1
    ring
  rw [he] at hh
  have hf := ne_of_lt (lt_of_le_of_lt hh ENNReal.ofReal_lt_top)
  have hn := ENNReal.ne_top_of_tsum_ne_top hf
  refine ⟨ENNReal.summable_toReal hf,?_⟩
  dsimp only [directReceiverGoodBudget]
  rw [←ENNReal.tsum_toReal_eq hn]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rwa [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg)] at h

lemma SmoothClassicalPrefix.directReceiverMagneticBudget_sum {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hd : Admissible d) (F : PhaseFlowOn s.E s.B T) (zX : Phase)
    {a b I : ℝ} (hI : 0<I) (hJI : b-a≤I) :
    Summable (directReceiverMagneticBudget s F zX a b I) ∧
    (∑'n,directReceiverMagneticBudget s F zX a b I n)≤120*datumEnergyNumber d := by
  have hJ : Icc (max 0 (a-2*I)) (min T b)⊆Icc (0:ℝ) T :=
    fun _ ht=>⟨(le_max_left _ _).trans ht.1,ht.2.trans (min_le_left _ _)⟩
  have hlen : min T b-max 0 (a-2*I)≤3*I := by
    have h1 := min_le_right T b
    have h2 := le_max_right 0 (a-2*I)
    linarith
  have hh := hs.energyPrefix.magneticFieldBudget_uniform F.flow zX 1 hJ hI
    (by norm_num : (0:ℝ)≤3) hlen
  rw [hs.initial_energy_eq] at hh
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.cast_ofNat] at hh
  have he : (10:ℝ≥0∞)*ENNReal.ofReal 3*ENNReal.ofReal (2*datumEnergyNumber d)=
      ENNReal.ofReal (60*datumEnergyNumber d) := by
    rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),
      ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10*3)]
    congr 1
    ring
  rw [he] at hh
  have hf := ne_of_lt (lt_of_le_of_lt hh ENNReal.ofReal_lt_top)
  have hn := ENNReal.ne_top_of_tsum_ne_top hf
  have hsum := ENNReal.summable_toReal hf
  refine ⟨hsum.mul_left 2,?_⟩
  dsimp only [directReceiverMagneticBudget]
  rw [tsum_mul_left,←ENNReal.tsum_toReal_eq hn]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hd.datumEnergyNumber_nonneg)] at h
  linarith

lemma budget_sqrt_weight_sum {ι : Type*} (S : Finset ι) (G W : ι→ℝ) {E N : ℝ}
    (hG : ∀i∈S,0≤G i) (hW : ∀i∈S,0≤W i) (hE : 0≤E) (hN : 0≤N)
    (hbudget : ∑i∈S,G i≤E) (hweight : ∑i∈S,W i≤N) :
    ∑i∈S,Real.sqrt (G i)*Real.sqrt (W i)≤Real.sqrt E*Real.sqrt N := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun i=>Real.sqrt (G i)) (fun i=>Real.sqrt (W i))
  have he : (∑i∈S,(Real.sqrt (G i))^2)=∑i∈S,G i := Finset.sum_congr rfl (fun i hi=>Real.sq_sqrt (hG i hi))
  have hn : (∑i∈S,(Real.sqrt (W i))^2)=∑i∈S,W i := Finset.sum_congr rfl (fun i hi=>Real.sq_sqrt (hW i hi))
  rw [he,hn] at hc
  have hu := mul_le_mul hbudget hweight (Finset.sum_nonneg hW) hE
  have hp : 0≤Real.sqrt E*Real.sqrt N := by positivity
  have hs : (Real.sqrt E*Real.sqrt N)^2=E*N := by rw [mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hN]
  nlinarith

lemma budget_sqrt_sum {ι : Type*} (S : Finset ι) (G : ι→ℝ) {E N : ℝ}
    (hG : ∀i∈S,0≤G i) (hE : 0≤E) (hN : 0≤N)
    (hbudget : ∑i∈S,G i≤E) (hcard : (S.card:ℝ)≤N) :
    ∑i∈S,Real.sqrt (G i)≤Real.sqrt E*Real.sqrt N := by
  have hh := budget_sqrt_weight_sum S G (fun _=>1) hG (by intros; norm_num) hE hN hbudget
    (by simpa using hcard)
  simpa only [Real.sqrt_one,mul_one] using hh

lemma source_sqrt_sum_bound {x : ℝ} (_hx : 0≤x) (S : Finset ℕ)
    (hS : ∀n∈S,sourceRepresentative n≤x) : ∑n∈S,Real.sqrt (sourceRepresentative n)≤4*Real.sqrt x := by
  have hp (n : ℕ) : 0 ≤ sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hgeom (N : ℕ) : ∑n∈Finset.range (N+1),Real.sqrt (sourceRepresentative n)≤4*Real.sqrt (sourceRepresentative N) := by
    induction N with
    | zero => norm_num [sourceRepresentative,Finset.sum_range_succ]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have he : sourceRepresentative (N+1)=2*sourceRepresentative N := by
        dsimp only [sourceRepresentative]
        rw [pow_succ]
        ring
      rw [he,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
      have hs : (4:ℝ)≤3*Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
      nlinarith [mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (sourceRepresentative N))]
  by_cases hne : S.Nonempty
  · let N := S.max' hne
    have hsub : S⊆Finset.range (N+1) := by
      intro n hn
      apply Finset.mem_range.mpr
      have hh := S.le_max' n hn
      change n≤N at hh
      omega
    have hs : (∑n∈S,Real.sqrt (sourceRepresentative n))≤∑n∈Finset.range (N+1),Real.sqrt (sourceRepresentative n) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>Real.sqrt_nonneg _)
    exact hs.trans ((hgeom N).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hS N (S.max'_mem hne))) (by norm_num)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

lemma receiver_scale_card {P w : ℝ} (hP : 1≤P) (hw : 0<w) (hwP : w≤P)
    (hL : 1≤Real.log (2+P)) (S : Finset ℕ)
    (hS : ∀n∈S,1/w ≤ cappedRepresentative n) :
    (S.card:ℝ)≤pairCountConstant*Real.log (2+P) := by
  obtain ⟨N,hN,hcard⟩ := exists_dyadic_count_log hP
  have hsub : S⊆Finset.range N := by
    intro n hn
    apply Finset.mem_range.mpr
    apply index_lt_of_two_pow_le _ hN
    have hh := mul_le_mul_of_nonneg_right (hS n hn) (show 0≤(2:ℝ)^n by positivity)
    rw [cappedRepresentative_mul_pow] at hh
    have hh' : (2:ℝ)^n≤w := by
      have he : (1/w)*(2:ℝ)^n=(2:ℝ)^n/w := by ring
      rw [he] at hh
      exact (div_le_iff₀ hw).mp hh |>.trans_eq (one_mul w)
    exact hh'.trans hwP
  have hc : (S.card:ℝ)≤(N:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range N)
  apply hc.trans (hcard.trans _)
  have hd := div_le_div_of_nonneg_right
    (Real.log_le_log (zero_lt_one.trans_le hP) (by linarith : P≤2+P))
    (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  unfold pairCountConstant
  simp only [div_eq_mul_inv,one_mul] at hd ⊢
  nlinarith

lemma receiver_good_sqrt_sum (S : Finset ℕ) (G : ℕ→ℝ) {E : ℝ}
    (hG : ∀n∈S,0≤G n) (hE : 0≤E) (hbudget : ∑n∈S,G n≤E) :
    ∑n∈S,Real.sqrt (G n)*Real.sqrt (cappedRepresentative n)≤Real.sqrt E*Real.sqrt 2 := by
  apply budget_sqrt_weight_sum S G cappedRepresentative hG
    (fun n _=>(cappedRepresentative_pos n).le) hE (by norm_num) hbudget
  have hh := capped_positive_power_sum_unscaled (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1) S (fun n _=>cappedRepresentative_le_one n)
  norm_num at hh
  exact hh

lemma source_stability_sqrt_sum_upper {P Q w : ℝ} (hP : 0<P) (hQ : 0<Q) (hw : 0<w) (hwQ : w≤Q)
    (S : Finset ℕ) (hS : ∀n∈S,sourceRepresentative n≤Q) :
    ∑n∈S,sourceRepresentative n*Real.sqrt (P/min (sourceRepresentative n) w)≤
      4*Q*Real.sqrt (P/w) := by
  have hp (n : ℕ) : 0 < sourceRepresentative n := by dsimp [sourceRepresentative]; positivity
  have hpoint (n : ℕ) (hn : n∈S) :
      sourceRepresentative n*Real.sqrt (P/min (sourceRepresentative n) w)≤
        Real.sqrt Q*Real.sqrt (P/w)*Real.sqrt (sourceRepresentative n) := by
    let p := sourceRepresentative n
    have hm : 0 < min p w := lt_min (hp n) hw
    have hprod := product_le_min_scale (hp n).le hw.le (hS n hn) hwQ
    have hratio : p/min p w≤Q/w := (div_le_div_iff₀ hm hw).mpr (by simpa only [p,mul_comm] using hprod)
    have hq : p^2*(P/min p w)≤Q*(P/w)*p := by
      calc
        _=(P*p)*(p/min p w) := by ring
        _≤(P*p)*(Q/w) := mul_le_mul_of_nonneg_left hratio (mul_nonneg hP.le (hp n).le)
        _=_ := by ring
    have heL : (p*Real.sqrt (P/min p w))^2=p^2*(P/min p w) := by
      rw [mul_pow,Real.sq_sqrt (div_nonneg hP.le hm.le)]
    have heR : (Real.sqrt Q*Real.sqrt (P/w)*Real.sqrt p)^2=Q*(P/w)*p := by
      simp only [mul_pow,Real.sq_sqrt hQ.le,Real.sq_sqrt (div_nonneg hP.le hw.le),Real.sq_sqrt (show 0≤p from (hp n).le)]
    have hpos : 0≤Real.sqrt Q*Real.sqrt (P/w)*Real.sqrt p := by positivity
    nlinarith
  calc
    _≤∑n∈S,Real.sqrt Q*Real.sqrt (P/w)*Real.sqrt (sourceRepresentative n) := Finset.sum_le_sum hpoint
    _=(Real.sqrt Q*Real.sqrt (P/w))*(∑n∈S,Real.sqrt (sourceRepresentative n)) := (Finset.mul_sum ..).symm
    _≤(Real.sqrt Q*Real.sqrt (P/w))*(4*Real.sqrt Q) :=
      mul_le_mul_of_nonneg_left (source_sqrt_sum_bound hQ.le S hS) (by positivity)
    _=4*(Real.sqrt Q)^2*Real.sqrt (P/w) := by ring
    _=4*Q*Real.sqrt (P/w) := by rw [Real.sq_sqrt hQ.le]

lemma rpow_three_quarters_le_sqrt {I : ℝ} (hI : 0<I) (hI1 : I≤1) :
    (I : ℝ)^(3/4:ℝ)≤Real.sqrt I := by
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_ge hI hI1 (by norm_num)

lemma plain_magnetic_three_quarters {I L : ℝ} (hI : 0<I) (hL : 0≤L) :
    (I : ℝ)^(3/4:ℝ)*Real.sqrt L≤Real.sqrt I+I*L := by
  have he : (I : ℝ)^(3/4:ℝ)=Real.sqrt I*(I : ℝ)^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hI]
    congr 1
    norm_num
  have he' : Real.sqrt I*((I : ℝ)^(1/4:ℝ)*Real.sqrt L)^2=I*L := by
    rw [mul_pow,Real.sq_sqrt hL,←Real.rpow_natCast,←Real.rpow_mul hI.le,
      Real.sqrt_eq_rpow]
    rw [←mul_assoc,←Real.rpow_add hI]
    norm_num
  have hx : (I : ℝ)^(1/4:ℝ)*Real.sqrt L≤1+((I : ℝ)^(1/4:ℝ)*Real.sqrt L)^2 := by
    nlinarith [sq_nonneg ((I : ℝ)^(1/4:ℝ)*Real.sqrt L-1/2)]
  have hh := mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg I)
  rw [mul_add,mul_one,he'] at hh
  calc
    _=Real.sqrt I*((I : ℝ)^(1/4:ℝ)*Real.sqrt L) := by rw [he]; ring
    _≤_ := hh

lemma source_parameter_scalar {M A L X : ℝ} (hM : 1≤M) (hA : 1≤A) (hL : 1≤L) (hX : 1≤X) :
    (Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*Real.sqrt X*Real.sqrt L≤
      (M+Real.sqrt A)*X*L := by
  have hM0 : 0≤M := zero_le_one.trans hM
  have hA0 : 0≤A := zero_le_one.trans hA
  have hL0 : 0≤L := zero_le_one.trans hL
  have hX0 : 0≤X := zero_le_one.trans hX
  have hrootM : Real.sqrt M≤M := Real.sqrt_le_self_iff.mpr (Or.inr hM)
  have hrootL : Real.sqrt L≤L := Real.sqrt_le_self_iff.mpr (Or.inr hL)
  have hrootX : Real.sqrt X≤X := Real.sqrt_le_self_iff.mpr (Or.inr hX)
  have hAL : 1≤A*L := one_le_mul_of_one_le_of_one_le hA hL
  have hrootAL : 1≤Real.sqrt (A*L) := by simpa using Real.sqrt_le_sqrt hAL
  have hdouble : Real.sqrt (Real.sqrt (A*L))≤Real.sqrt A*Real.sqrt L := by
    rw [←Real.sqrt_mul hA0]
    exact Real.sqrt_le_self_iff.mpr (Or.inr hrootAL)
  have hU : (Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*Real.sqrt L≤(M+Real.sqrt A)*L := by
    calc
      _≤(M+Real.sqrt A*Real.sqrt L)*Real.sqrt L :=
        mul_le_mul_of_nonneg_right (add_le_add hrootM hdouble) (Real.sqrt_nonneg L)
      _=M*Real.sqrt L+Real.sqrt A*L := by
        rw [add_mul]
        rw [mul_assoc,←pow_two,Real.sq_sqrt hL0]
      _≤M*L+Real.sqrt A*L := add_le_add (mul_le_mul_of_nonneg_left hrootL hM0) le_rfl
      _=_ := by ring
  calc
    _=((Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*Real.sqrt L)*Real.sqrt X := by ring
    _≤((M+Real.sqrt A)*L)*X := mul_le_mul hU hrootX (Real.sqrt_nonneg X) (by positivity)
    _=_ := by ring

lemma remaining_source_uniform_numerics {I P w M A L a b c : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hP : 0<P) (hw : 0<w) (hwP : w≤P)
    (hM : 1≤M) (hA : 1≤A) (hL : 1≤L) (ha : 0≤a) (hb : 0≤b) (hc : 0 ≤ c) :
    2*P*(I : ℝ)^(3/4:ℝ)*(a+b*Real.sqrt L)+
      4*I*P*Real.sqrt (P/w)*(Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*c*Real.sqrt L≤
      (2*a+2*b+4*c)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*L/w) := by
  let Q := P*Real.sqrt I
  let V := (M+Real.sqrt A)*I*P^2*L/w
  have hM0 : 0≤M := zero_le_one.trans hM
  have hA0 : 0≤A := zero_le_one.trans hA
  have hL0 : 0≤L := zero_le_one.trans hL
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hV : 0≤V := by dsimp [V]; positivity
  have hX : 1≤P/w := (le_div_iff₀ hw).mpr (by simpa using hwP)
  have hplain := rpow_three_quarters_le_sqrt hI hI1
  have hmag := plain_magnetic_three_quarters hI hL0
  have hPL : I*P*L≤V := by
    have hM1 : 1≤M+Real.sqrt A := by linarith [Real.sqrt_nonneg A]
    have hx : 1≤(M+Real.sqrt A)*(P/w) := one_le_mul_of_one_le_of_one_le hM1 hX
    have hh := mul_le_mul_of_nonneg_left hx (show 0≤I*P*L by positivity)
    calc
      _=(I*P*L)*1 := (mul_one _).symm
      _≤(I*P*L)*((M+Real.sqrt A)*(P/w)) := hh
      _=V := by dsimp [V]; ring
  have hg : 2*P*(I : ℝ)^(3/4:ℝ)*a≤2*a*Q := by
    have hh := mul_le_mul_of_nonneg_left hplain (show 0≤2*P*a by positivity)
    dsimp only [Q]
    nlinarith only [hh]
  have hb' : 2*P*(I : ℝ)^(3/4:ℝ)*b*Real.sqrt L≤2*b*(Q+V) := by
    have hh := mul_le_mul_of_nonneg_left hmag (show 0≤2*P*b by positivity)
    have hh' := mul_le_mul_of_nonneg_left hPL (show 0≤2*b by positivity)
    dsimp only [Q] at *
    nlinarith only [hh,hh']
  have hp' : 4*I*P*Real.sqrt (P/w)*(Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*c*Real.sqrt L≤4*c*V := by
    calc
      _=(4*I*P*c)*((Real.sqrt M+Real.sqrt (Real.sqrt (A*L)))*Real.sqrt (P/w)*Real.sqrt L) := by ring
      _≤(4*I*P*c)*((M+Real.sqrt A)*(P/w)*L) :=
        mul_le_mul_of_nonneg_left (source_parameter_scalar hM hA hL hX) (by positivity)
      _=4*c*V := by dsimp [V]; ring
  dsimp only [Q,V] at hg hb' hp' hQ hV ⊢
  nlinarith [mul_nonneg ha hV,mul_nonneg hc hQ]

lemma receiver_shared_two_budget_sum (S : Finset ℕ) (G B : ℕ→ℝ)
    {Eg Eb N g b g₀ g₁ b₀ b₁ x : ℝ}
    (hG : ∀n∈S,0≤G n) (hB : ∀n∈S,0≤B n)
    (hEg : 0≤Eg) (hEb : 0≤Eb) (hN : 0≤N)
    (hg : 0≤g) (hb : 0≤b) (hg₀ : 0≤g₀) (hg₁ : 0≤g₁)
    (hb₀ : 0≤b₀) (hb₁ : 0≤b₁) (hx : 0≤x)
    (hbudgetG : ∑n∈S,G n≤Eg) (hbudgetB : ∑n∈S,B n≤Eb) (hcard : (S.card:ℝ)≤N) :
    ∑n∈S,(g*Real.sqrt (G n)*(g₀*Real.sqrt (cappedRepresentative n)+x*g₁)+
      b*Real.sqrt (B n)*(b₀+x*b₁))≤
      g*g₀*Real.sqrt Eg*Real.sqrt 2+b*b₀*Real.sqrt Eb*Real.sqrt N+
        x*(g*g₁*Real.sqrt Eg+b*b₁*Real.sqrt Eb)*Real.sqrt N := by
  have hgw := receiver_good_sqrt_sum S G hG hEg hbudgetG
  have hgs := budget_sqrt_sum S G hG hEg hN hbudgetG hcard
  have hbs := budget_sqrt_sum S B hB hEb hN hbudgetB hcard
  calc
    _=(g*g₀)*(∑n∈S,Real.sqrt (G n)*Real.sqrt (cappedRepresentative n))+
        (b*b₀)*(∑n∈S,Real.sqrt (B n))+
        (x*g*g₁)*(∑n∈S,Real.sqrt (G n))+(x*b*b₁)*(∑n∈S,Real.sqrt (B n)) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤(g*g₀)*(Real.sqrt Eg*Real.sqrt 2)+(b*b₀)*(Real.sqrt Eb*Real.sqrt N)+
        (x*g*g₁)*(Real.sqrt Eg*Real.sqrt N)+(x*b*b₁)*(Real.sqrt Eb*Real.sqrt N) := by
      exact add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hgw (by positivity))
        (mul_le_mul_of_nonneg_left hbs (by positivity)))
        (mul_le_mul_of_nonneg_left hgs (by positivity)))
        (mul_le_mul_of_nonneg_left hbs (by positivity))
    _=_ := by ring

lemma momentum_affine_stability_sum_upper {P Q w a b : ℝ}
    (hP : 0<P) (hQ : 0<Q) (hw : 0<w) (hwQ : w≤Q)
    (ha : 0≤a) (hb : 0≤b) (S : Finset ℕ) (hS : ∀n∈S,sourceRepresentative n≤Q) :
    ∑n∈S,sourceRepresentative n*(a+b*Real.sqrt (P/min (sourceRepresentative n) w))≤
      2*Q*a+4*Q*Real.sqrt (P/w)*b := by
  calc
    _=(∑n∈S,sourceRepresentative n)*a+(∑n∈S,sourceRepresentative n*Real.sqrt (P/min (sourceRepresentative n) w))*b := by
      simp only [Finset.sum_mul,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _≤_ := add_le_add
      (mul_le_mul_of_nonneg_right (sourceRepresentative_sum_bound hQ.le S hS) ha)
      (mul_le_mul_of_nonneg_right (source_stability_sqrt_sum_upper hP hQ hw hwQ S hS) hb)

lemma remaining_source_budget_total (Sp Sφ : Finset ℕ) (G B : ℕ→ℝ)
    {I P w M A L Eg Eb N g b g₀ g₁ b₀ b₁ H : ℝ}
    (hI : 0<I) (hI1 : I≤1) (hP : 0<P) (hw : 0<w) (hwP : w≤P)
    (hM : 1≤M) (hA : 1≤A) (hL : 1≤L)
    (hG : ∀n∈Sφ,0≤G n) (hB : ∀n∈Sφ,0≤B n)
    (hEg : 0≤Eg) (hEb : 0≤Eb) (hN : 0≤N)
    (hg : 0≤g) (hb : 0≤b) (hg₀ : 0≤g₀) (hg₁ : 0≤g₁)
    (hb₀ : 0≤b₀) (hb₁ : 0≤b₁) (hH : 0≤H)
    (hbudgetG : ∑n∈Sφ,G n≤Eg) (hbudgetB : ∑n∈Sφ,B n≤Eb)
    (hcard : (Sφ.card:ℝ)≤N*L) (hp : ∀n∈Sp,sourceRepresentative n≤128*P) :
    let U := Real.sqrt M+Real.sqrt (Real.sqrt (A*L))
    let a := g*g₀*Real.sqrt Eg*Real.sqrt 2
    let b' := b*b₀*Real.sqrt Eb*Real.sqrt N
    let c := H*(g*g₁*Real.sqrt Eg+b*b₁*Real.sqrt Eb)*Real.sqrt N
    (∑np∈Sp,∑nf∈Sφ,(I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
      (g*Real.sqrt (G nf)*(g₀*Real.sqrt (cappedRepresentative nf)+
          H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*g₁)+
       b*Real.sqrt (B nf)*(b₀+
          H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*b₁)))≤
      128*(2*a+2*b'+4*c)*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*L/w) := by
  dsimp only
  let U := Real.sqrt M+Real.sqrt (Real.sqrt (A*L))
  let a := g*g₀*Real.sqrt Eg*Real.sqrt 2
  let b' := b*b₀*Real.sqrt Eb*Real.sqrt N
  let c := H*(g*g₁*Real.sqrt Eg+b*b₁*Real.sqrt Eb)*Real.sqrt N
  have hU : 0≤U := by dsimp [U]; positivity
  have ha : 0≤a := by dsimp [a]; positivity
  have hb' : 0≤b' := by dsimp [b']; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hL0 : 0≤L := zero_le_one.trans hL
  have hquarter : (I : ℝ)^(3/4:ℝ)*(I : ℝ)^(1/4:ℝ)=I := by
    rw [←Real.rpow_add hI]
    norm_num
  have hinner (np : ℕ) :
      (∑nf∈Sφ,(I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
        (g*Real.sqrt (G nf)*(g₀*Real.sqrt (cappedRepresentative nf)+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*g₁)+
         b*Real.sqrt (B nf)*(b₀+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*b₁)))≤
      (I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
        (a+b'*Real.sqrt L+((I : ℝ)^(1/4:ℝ)*U*c*Real.sqrt L)*Real.sqrt (P/min (sourceRepresentative np) w)) := by
    rw [←Finset.mul_sum]
    have hs := receiver_shared_two_budget_sum Sφ G B hG hB hEg hEb
      (mul_nonneg hN hL0) hg hb hg₀ hg₁ hb₀ hb₁
      (show 0≤H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U by positivity)
      hbudgetG hbudgetB hcard
    apply mul_le_mul_of_nonneg_left _ (by dsimp [sourceRepresentative]; positivity)
    calc
      _≤_ := hs
      _=_ := by rw [Real.sqrt_mul hN]; dsimp [a,b',c]; ring
  calc
    _≤∑np∈Sp,(I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
        (a+b'*Real.sqrt L+((I : ℝ)^(1/4:ℝ)*U*c*Real.sqrt L)*Real.sqrt (P/min (sourceRepresentative np) w)) :=
      Finset.sum_le_sum (fun np _=>hinner np)
    _=(I : ℝ)^(3/4:ℝ)*(∑np∈Sp,sourceRepresentative np*
        (a+b'*Real.sqrt L+((I : ℝ)^(1/4:ℝ)*U*c*Real.sqrt L)*Real.sqrt (P/min (sourceRepresentative np) w))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro np hnp
      ring
    _≤(I : ℝ)^(3/4:ℝ)*(2*(128*P)*(a+b'*Real.sqrt L)+
      4*(128*P)*Real.sqrt (P/w)*((I : ℝ)^(1/4:ℝ)*U*c*Real.sqrt L)) :=
      mul_le_mul_of_nonneg_left (momentum_affine_stability_sum_upper hP (by positivity) hw
        (by linarith : w≤128*P) (by positivity) (by positivity) Sp hp) (by positivity)
    _=128*(2*P*(I : ℝ)^(3/4:ℝ)*(a+b'*Real.sqrt L)+4*I*P*Real.sqrt (P/w)*U*c*Real.sqrt L) := by
      calc
        _=128*(2*P*(I : ℝ)^(3/4:ℝ)*(a+b'*Real.sqrt L)+
          4*((I : ℝ)^(3/4:ℝ)*(I : ℝ)^(1/4:ℝ))*P*Real.sqrt (P/w)*U*c*Real.sqrt L) := by ring
        _=_ := by rw [hquarter]
    _≤_ := by
      have hh := mul_le_mul_of_nonneg_left
        (remaining_source_uniform_numerics hI hI1 hP hw hwP hM hA hL ha hb' hc)
        (by norm_num : (0:ℝ)≤128)
      simpa only [U,a,b',c,mul_assoc] using hh

lemma receiver_scale_card_enlarged {P w : ℝ} (hP : 1≤P) (hw : 0<w) (hwP : w≤P)
    (hL : 1≤Real.log (2+P)) (S : Finset ℕ)
    (hS : ∀n∈S,1/(32*w) ≤ cappedRepresentative n) :
    (S.card:ℝ)≤(1+Real.log 32)*pairCountConstant*Real.log (2+P) := by
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hP' : 1≤32*P := by linarith
  have hlog : Real.log (2+P)≤Real.log (2+32*P) :=
    Real.log_le_log (by positivity) (by linarith)
  have hc := receiver_scale_card hP' (by positivity : 0<32*w)
    (mul_le_mul_of_nonneg_left hwP (by norm_num : (0:ℝ)≤32)) (hL.trans hlog) S hS
  have hl : Real.log (2+32*P)≤(1+Real.log 32)*Real.log (2+P) := by
    calc
      _≤Real.log (32*(2+P)) := Real.log_le_log (by positivity) (by linarith)
      _=Real.log 32+Real.log (2+P) := Real.log_mul (by norm_num) (by positivity)
      _≤_ := by nlinarith [Real.log_nonneg (by norm_num : (1:ℝ)≤32)]
  have hN : 0≤pairCountConstant := by unfold pairCountConstant; positivity
  exact hc.trans (by nlinarith [mul_le_mul_of_nonneg_left hl hN])

lemma remainingGoodConstant_nonneg {K κ β : ℝ} (hK : 0≤K) (hκ : 0≤κ)
    (hβ : 0≤β) (hβ1 : β≤1/2) : 0 ≤ remainingGoodConstant K κ β := by
  unfold remainingGoodConstant
  exact mul_nonneg (mul_nonneg (relativeAngularConstant_nonneg hK hκ (by linarith))
    (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)))))
    (Real.rpow_nonneg hκ _)

lemma remainingMagneticConstant_nonneg {K κ β : ℝ} (hK : 0≤K) (hκ : 0≤κ)
    (_hβ : 0≤β) (hβ1 : β≤1/2) : 0 ≤ remainingMagneticConstant K κ β := by
  unfold remainingMagneticConstant
  exact mul_nonneg (relativeAngularConstant_nonneg hK hκ (by linarith))
    (inv_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one (by norm_num) (by norm_num) (by linarith))))

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direct_remaining_source_short_uniform_expanded_oai {d : Datum} (hd : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T →
    ∀ (zX : Phase) (S : Set Phase) (a b I w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → a≤b → 0<I → I≤1 → b-a≤I →
      1≤M → 1≤A → 1≤P → 1≤Real.log (2+P) → 0<w → w≤P →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀ (Sp Sφ : Finset ℕ) (Sθ : ℕ→ℕ→Finset ℕ) (Sσ : ℕ→ℕ→ℕ→Finset ℕ),
      (∀np∈Sp,sourceRepresentative np≤128*P) →
      (∀nf∈Sφ,1/(32*w) ≤ cappedRepresentative nf) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,cappedRepresentative nf≤16384*cappedRepresentative nt) →
      (∀np∈Sp,∀nf∈Sφ,∀nt∈Sθ np nf,∀j∈Sσ np nf nt,
        cappedRepresentative j≤131080*cappedRepresentative nt ∧
        512 ≤ cappedRepresentative j*sourceRepresentative np ∧ 32 ≤ cappedRepresentative j*w) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun np nt nf j nr=>relativeRepresentativeClosedBin T w ![np,nt,nf,nr] j
      (∑np∈Sp,∑nf∈Sφ,∑nt∈Sθ np nf,∑j∈Sσ np nf nt,∑'nr : ℕ,
        if max 1 T*cappedRepresentative nr≤I then
          ∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B np nt nf j nr) z
            ∂physicalBinMeasure V (B np nt nf j nr) (Icc a b) else 0)≤
      ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hbin⟩ := hd.direct_source_shared_short_angles_expanded
  let E := datumEnergyNumber d
  let Eg := 20*E
  let Eb := 120*E
  let N := (1+Real.log 32)*pairCountConstant
  let g := relativeCauchyConstant Cg E 1
  let b' := relativeCauchyConstant Cb E 1
  let g₀ := 2*remainingGoodConstant 131080 16384 0
  let g₁ := remainingGoodConstant 131080 16384 (1/2)
  let b₀ := 2*remainingMagneticConstant 131080 16384 0
  let b₁ := remainingMagneticConstant 131080 16384 (1/2)
  let H := 2*Real.sqrt 16384
  let D := dyadicBalanceConstant (1/2) (1/2)
  let aa := g*g₀*Real.sqrt Eg*Real.sqrt 2
  let bb := b'*b₀*Real.sqrt Eb*Real.sqrt N
  let cc := H*(g*g₁*Real.sqrt Eg+b'*b₁*Real.sqrt Eb)*Real.sqrt N
  have hE : 0≤E := hd.datumEnergyNumber_nonneg
  have hEg : 0≤Eg := by dsimp [Eg]; positivity
  have hEb : 0≤Eb := by dsimp [Eb]; positivity
  have hN : 0≤N := by dsimp [N,pairCountConstant]; positivity
  have hg : 0≤g := relativeCauchyConstant_nonneg hCg
  have hb' : 0≤b' := relativeCauchyConstant_nonneg hCb
  have hg₀ : 0≤g₀ := mul_nonneg (by norm_num) (remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hg₁ : 0≤g₁ := remainingGoodConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hb₀ : 0≤b₀ := mul_nonneg (by norm_num) (remainingMagneticConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hb₁ : 0≤b₁ := remainingMagneticConstant_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hH : 0≤H := by dsimp [H]; positivity
  have hD : 0≤D := (dyadicBalanceConstant_pos (by norm_num) (by norm_num)).le
  have haa : 0≤aa := by dsimp [aa]; positivity
  have hbb : 0≤bb := by dsimp [bb]; positivity
  have hcc : 0 ≤ cc := by dsimp [cc]; positivity
  refine ⟨D*(128*(2*aa+2*bb+4*cc)),by positivity,?_⟩
  intro s T F hs hT zX S a b I w M A P hS hS0 ha hb hab hI hI1 hJI hM hA hP hL hw hwP HX HZ
    Sp Sφ Sθ Sσ hp hφ hθ hσ
  dsimp only
  let G := directReceiverGoodBudget s F zX a b I
  let B := directReceiverMagneticBudget s F zX a b I
  let U := Real.sqrt M+Real.sqrt (Real.sqrt (A*Real.log (2+P)))
  let f (np nf : ℕ) := (I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
    (g*Real.sqrt (G nf)*(g₀*Real.sqrt (cappedRepresentative nf)+
      H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*g₁)+
     b'*Real.sqrt (B nf)*(b₀+
      H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*b₁))
  have hG (nf : ℕ) : 0≤G nf := ENNReal.toReal_nonneg
  have hB (nf : ℕ) : 0≤B nf := by dsimp [B,directReceiverMagneticBudget]; positivity
  have hf (np nf : ℕ) : 0≤f np nf := by dsimp [f,U,sourceRepresentative]; positivity
  obtain ⟨hGs,hGt⟩ := hs.directReceiverGoodBudget_sum hd F zX ha hb hI hJI
  obtain ⟨hBs,hBt⟩ := hs.directReceiverMagneticBudget_sum hd F zX hI hJI
  have hGb : ∑nf∈Sφ,G nf≤Eg := (hGs.sum_le_tsum Sφ (fun n _=>hG n)).trans hGt
  have hBb : ∑nf∈Sφ,B nf≤Eb := (hBs.sum_le_tsum Sφ (fun n _=>hB n)).trans hBt
  have hi (np : ℕ) (hnp : np∈Sp) (nf : ℕ) (hnf : nf∈Sφ) :=
    hbin s T F hs.energyPrefix hT hs.initial_f zX S np nf a b I w M A P
      hS hS0 ha hb hab hI hJI (zero_lt_one.trans_le hM) (zero_le_one.trans hA)
      (zero_lt_one.trans_le hP) hw HX HZ (Sθ np nf) (Sσ np nf) (hθ np hnp nf hnf) (hσ np hnp nf hnf)
  have he (np nf : ℕ) :
      D*(I : ℝ)^(3/4:ℝ)*sourceRepresentative np*
        (relativeCauchyConstant Cg (∫x : Vec,totalEnergy s (0,x)) (G nf)*
          (2*remainingGoodConstant 131080 16384 0*Real.sqrt (cappedRepresentative nf)+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*remainingGoodConstant 131080 16384 (1/2))+
         relativeCauchyConstant Cb (∫x : Vec,totalEnergy s (0,x)) (B nf)*
          (2*remainingMagneticConstant 131080 16384 0+
            H*(I : ℝ)^(1/4:ℝ)*Real.sqrt (P/min (sourceRepresentative np) w)*U*remainingMagneticConstant 131080 16384 (1/2)))=
      D*f np nf := by
    rw [hs.initial_energy_eq,relativeCauchyConstant_factor Cg,relativeCauchyConstant_factor Cb]
    dsimp [f,g,b',E,g₀,g₁,b₀,b₁]
    ring
  calc
    _≤∑np∈Sp,∑nf∈Sφ,ENNReal.ofReal (D*f np nf) := by
      apply Finset.sum_le_sum
      intro np hnp
      apply Finset.sum_le_sum
      intro nf hnf
      have hh := hi np hnp nf hnf
      dsimp only at hh
      change _≤ENNReal.ofReal _ at hh
      rw [←he np nf]
      exact hh
    _=ENNReal.ofReal (D*(∑np∈Sp,∑nf∈Sφ,f np nf)) := by
      simp_rw [←ENNReal.ofReal_sum_of_nonneg (fun n _=>mul_nonneg hD (hf _ n)),
        ←ENNReal.ofReal_sum_of_nonneg (fun n _=>Finset.sum_nonneg (fun i _=>mul_nonneg hD (hf n i))),
        ←Finset.mul_sum]
    _≤_ := by
      apply ENNReal.ofReal_le_ofReal
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hD
      exact remaining_source_budget_total Sp Sφ G B hI hI1 (zero_lt_one.trans_le hP) hw hwP hM hA hL
        (fun n _=>hG n) (fun n _=>hB n) hEg hEb hN hg hb' hg₀ hg₁ hb₀ hb₁ hH hGb hBb
        (receiver_scale_card_enlarged hP hw hwP hL Sφ hφ) hp

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direct_remaining_source_short_uniform_expanded_oai := @OAI.RVM.Admissible.direct_remaining_source_short_uniform_expanded_oai
