-- Prove2me | solution 1 for OAI.RVM.Admissible.projected_source_baseline_far
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:09:51.820327+00:00
-- url     : https://prove2.me/submissions/2db3542e-96df-4732-a0f8-1fbd4d964987

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_projected_source_two_budget_bound
import Theorems.Thm_OAI_RVM_EnergyPrefix_goodFieldBudget_uniform
import Theorems.Thm_OAI_RVM_PhaseFlowOn_closedEulerian_baseline_budget

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixClamp
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
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma prefixClamp_eq {T t : ℝ} (ht : t∈Icc 0 T) : prefixClamp T t=t := by
  simp [prefixClamp,min_eq_right ht.2,max_eq_right ht.1]

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixParticle
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
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma dyadicWindow_one_sqrt {D : ℝ} (j : ℕ)
    (hlo : ((2:ℝ)^j)⁻¹^2/2≤D) (hhi : D≤8*((2:ℝ)^j)⁻¹^2) :
    DyadicWindow 1 j (Real.sqrt (D/2)) := by
  have hp : 0<(2:ℝ)^j := by positivity
  have hi : 0<((2:ℝ)^j)⁻¹ := inv_pos.mpr hp
  have hD0 : 0≤D := (by positivity : 0≤((2:ℝ)^j)⁻¹^2/2).trans hlo
  have hD : 0≤D/2 := by positivity
  have hsq := Real.sq_sqrt hD
  have hlo' : ((2:ℝ)^j)⁻¹/2≤Real.sqrt (D/2) := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  have hhi' : Real.sqrt (D/2)≤2*((2:ℝ)^j)⁻¹ := by
    nlinarith [Real.sqrt_nonneg (D/2)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hlo' hp.le
    simpa only [pow_one,← mul_div_assoc,mul_inv_cancel₀ hp.ne'] using hh
  · have hh := mul_le_mul_of_nonneg_left hhi' hp.le
    simpa only [pow_one,mul_left_comm,mul_inv_cancel₀ hp.ne',mul_one] using hh

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

lemma Admissible.projected_source_baseline_far_oai {d : Datum} (hd₀ : Admissible d) :
    ∃ Cg Cb c : ℝ,0 ≤ Cg ∧ 0 ≤ Cb ∧ 0 ≤ c ∧
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (k : Fin 4→ℕ)
        (a b I len w M A P L massScale Cs : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale → 0 < w → 128 ≤ Cs →
      massScale ≤ sourceRepresentative (k 0)/128 → massScale ≤ w/8 →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      32 ≤ cappedRepresentative (k 2)*w →
      2*len ≤ (Cs*(P/massScale)*(M/cappedRepresentative (k 2)+
        Real.sqrt (A*L/cappedRepresentative (k 2))))⁻¹^2 →
      (∀t∈Icc a b,w/16 ≤ ‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let r := max 1 T*cappedRepresentative (k 3)
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := representativeClosedBin T w k
      let E := ∫x : Vec,totalEnergy s (0,x)
      let mass := ENNReal.ofReal (568197120*E*(1+I/len)/(p*r*φ^2))
      (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V B T w Q z
        ∂physicalBinMeasure V B (Icc a b))  ≤
      ENNReal.ofReal (128*(3840+94080000*c)*φ^2/(p*θ^2))*
        ((ENNReal.ofReal (20*I*E))^(1/2:ℝ)*
          (ENNReal.ofReal (128*Cg*p^3*θ^2)*mass)^(1/2:ℝ))+
      ENNReal.ofReal (128*(3840+94080000*c)*φ/p)*
        ((ENNReal.ofReal (40*(I+2*r)*E))^(1/2:ℝ)*
          (ENNReal.ofReal (128*Cb*p^3*θ^2)*mass)^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,c,hCg,hCb,hc,hsource⟩ := hd₀.projected_source_two_budget_bound
  refine ⟨Cg,Cb,c,hCg,hCb,hc,?_⟩
  intro s T F hs hT h0 zX S Q k a b I len w M A P L massScale Cs hS hS0 ha hb hlen hlenI hab
    hM hA hP hL hm hw hCs hmq hmw hsmall hwφ hstable hband HX HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let r := max 1 T*cappedRepresentative (k 3)
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  have hp : 0 < p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0 < θ := cappedRepresentative_pos _
  have hφ : 0 < φ := cappedRepresentative_pos _
  have hr : 0 < r := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (cappedRepresentative_pos _)
  have hBmax : B.rmax=2*r := by dsimp [B,representativeClosedBin,r]; ring
  have hBmin : B.rmin=r/2 := rfl
  have hBDmin : B.Dmin=φ^2/2 := rfl
  have hI : 0 < I := hlen.trans_le hlenI
  have hE : 0 ≤ E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hdsmall : B.dmax ≤ φ^2/32 := by
    change 8*θ^2 ≤ φ^2/32
    have ht : θ ≤ φ/16 := hsmall
    nlinarith only [sq_le_sq₀ hθ.le (by positivity : 0 ≤ φ/16) |>.mpr ht]
  have hbudget := F.closedEulerian_baseline_budget hs hT zX B hS (k 0) (k 2)
    (by rfl : p=64*(2:ℝ)^(k 0)) (by rfl : φ=(2:ℝ)⁻¹^(k 2)) ha hb hlen hlenI hab
    hM hA hP hL hm hφ (cappedRepresentative_le_one _) hCs hstable le_rfl le_rfl hmq hmw
    (by change 0 < r/2; positivity) (by rw [hBmax]; positivity) hdsmall le_rfl le_rfl
    (by change 4 ≤ φ*(w/8); dsimp [φ] at *; nlinarith only [hwφ]) HX HZ
  have hmass : coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) /
      ENNReal.ofReal (B.rmin^2*B.Dmin)  ≤
      ENNReal.ofReal (568197120*E*(1+I/len)/(p*r*φ^2)) := by
    calc
      _  ≤  (ENNReal.ofReal (35512320*B.rmax/p*(1+I/len))*ENNReal.ofReal E)/
          ENNReal.ofReal (B.rmin^2*B.Dmin) := by gcongr
      _ = _ := by
        rw [hBmax,hBmin,hBDmin,←ENNReal.ofReal_mul (by positivity : 0 ≤ 35512320*(2*r)/p*(1+I/len)),
          ←ENNReal.ofReal_div_of_pos (by positivity : 0 < (r/2)^2*(φ^2/2))]
        congr 1
        field_simp [hp.ne',hr.ne',hφ.ne',hlen.ne']
        ring
  have hgood : ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) 1 a b I (k 2)  ≤
      ENNReal.ofReal (20*I*E) := by
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.goodFieldBudget_uniform X (fun t=>velocity (V t)) 1 hJ hI hab)
    calc
      _  ≤  ENNReal.ofReal I*((4*1+1:ℕ)*ENNReal.ofReal (4*E)) := mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal I*(5*ENNReal.ofReal (4*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=5),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5),
          ←ENNReal.ofReal_mul hI.le]
        congr 1
        ring
  have hmag : ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T 1
      (max 0 (a-B.rmax)) (min T (b-B.rmin)) I (k 2)  ≤
      ENNReal.ofReal (40*(I+2*r)*E) := by
    have hsub : Icc (max 0 (a-B.rmax)) (min T (b-B.rmin))⊆Icc 0 T :=
      Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
    have hh : min T (b-B.rmin)-max 0 (a-B.rmax)  ≤  (1+2*r/I)*I := by
      have hb' := min_le_right T (b-B.rmin)
      have ha' := le_max_right 0 (a-B.rmax)
      rw [hBmax] at ha'
      rw [hBmin] at hb'
      have he : (1+2*r/I)*I=I+2*r := by field_simp
      rw [hBmin,hBmax,he]
      linarith only [hab,hb',ha',hr]
    have hh := (ENNReal.le_tsum (k 2)).trans
      (hs.magneticFieldBudget_uniform F.flow zX 1 hsub hI (by positivity : 0 ≤ 1+2*r/I) hh)
    calc
      _  ≤  ENNReal.ofReal (2*I)*((2*(4*1+1):ℕ)*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E)) :=
        mul_le_mul' le_rfl hh
      _ = _ := by
        change ENNReal.ofReal (2*I)*(10*ENNReal.ofReal (1+2*r/I)*ENNReal.ofReal (2*E))=_
        rw [←ENNReal.ofReal_ofNat (n:=10),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 10),
          ←ENNReal.ofReal_mul (by positivity : 0 ≤ 10*(1+2*r/I)),
          ←ENNReal.ofReal_mul (by positivity : 0 ≤ 2*I)]
        congr 1
        field_simp [hI.ne']
        ring
  have hband' (t : ℝ) (ht : t∈Icc a b) : w/16 ≤ ‖V t‖ := by
    simpa only [V,prefixFlow,prefixClamp_eq (hJ ht)] using hband t ht
  have hangle (D : ℝ) (hD : D∈Icc B.Dmin B.Dmax) : DyadicWindow 1 (k 2) (Real.sqrt (D/2)) :=
    dyadicWindow_one_sqrt (k 2)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.1)
      (by simpa only [B,representativeClosedBin,cappedRepresentative,inv_pow] using hD.2)
  have hn := hsource s T F hs hT h0 zX B S Q a b I w (p/128) p θ φ 1 1 (k 2)
    hS hS0 hJ hI hw (by positivity) hp hθ hφ (by norm_num)
    (by change 0 < r/2; positivity) (by change 0 < φ^2/2; positivity)
    le_rfl (by change p/32 ≤ p; linarith only [hp]) le_rfl le_rfl le_rfl le_rfl
    (by norm_num [B,representativeClosedBin]) (hdsmall.trans (by change φ^2/32 ≤ φ^2/2; nlinarith only [sq_nonneg φ]))
    hangle hband'
  dsimp only at hn
  have hθ1 : θ ≤ 1 := cappedRepresentative_le_one _
  simp only [min_eq_left hθ1] at hn
  have heqG : (3840+94080000*c)*φ^2/(p/128*θ^2)=128*(3840+94080000*c)*φ^2/(p*θ^2) := by ring
  have heqB : (3840+94080000*c)*φ/(p/128)=128*(3840+94080000*c)*φ/p := by ring
  rw [heqG,heqB] at hn
  apply hn.trans
  apply add_le_add
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hgood (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact (min_le_right _ _).trans (mul_le_mul' le_rfl hmass)
  · apply mul_le_mul' le_rfl
    apply mul_le_mul' (ENNReal.rpow_le_rpow hmag (by norm_num))
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    exact (min_le_right _ _).trans (mul_le_mul' le_rfl hmass)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.projected_source_baseline_far_oai := @OAI.RVM.Admissible.projected_source_baseline_far_oai
