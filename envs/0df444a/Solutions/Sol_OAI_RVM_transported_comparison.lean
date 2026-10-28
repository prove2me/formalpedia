-- Prove2me | solution 1 for OAI.RVM.transported_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:45:19.327997+00:00
-- url     : https://prove2.me/submissions/e7535360-2580-46cb-97ba-c4a4a76b9f34

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_exists_smoothLorentzFlow

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

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_IncrementBootstrap
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

lemma norm_relativistic_projection_le (u h : Vec) (hu : ‖u‖ ≤ 1) :
    ‖h-dot u h • u‖ ≤ ‖h‖ := by
  have hsq : ‖h-dot u h • u‖^2 = ‖h‖^2-2*(dot u h)^2+(dot u h)^2*‖u‖^2 := by
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← dot_eq_inner,
      dot_smul_right,dot_comm h u]
    ring
  have hu2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hh := mul_le_mul_of_nonneg_left hu2 (sq_nonneg (dot u h))
  nlinarith [norm_nonneg (h-dot u h • u),norm_nonneg h,sq_nonneg (dot u h)]

lemma norm_fderiv_velocity_le (v : Vec) : ‖fderiv ℝ velocity v‖ ≤ (q v)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (q_pos v).le)
  intro h
  rw [fderiv_velocity_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (q_pos v))]
  exact mul_le_mul_of_nonneg_left
    (norm_relativistic_projection_le _ _ (norm_velocity_lt_one v).le)
    (inv_nonneg.mpr (q_pos v).le)

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

lemma cross_sub_left (a b c : Vec) : cross (a-b) c = cross a c-cross b c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

lemma cross_sub_right (a b c : Vec) : cross a (b-c) = cross a b-cross a c := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

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

namespace SmoothLorentzFlow

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

end SmoothLorentzFlow

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

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

lemma velocity_global_lipschitz (v w : Vec) : ‖velocity w-velocity v‖≤‖w-v‖ := by
  have hh := (convex_univ : Convex ℝ (univ : Set Vec)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (contDiff_velocity (k:=1)).differentiable (by norm_num) x)
    (C:=1) (fun x _ => (norm_fderiv_velocity_le x).trans ((inv_le_one₀ (q_pos x)).mpr (by
      have hq := q_sq x
      nlinarith [q_pos x,sq_nonneg ‖x‖]))) (mem_univ v) (mem_univ w)
  simpa only [one_mul] using hh

lemma lorentzField_difference_bound {E B E' B' : Field} {t L N D : ℝ}
    (hL : 0≤L) (hN : 0≤N) (hD : 0≤D)
    (hB : ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEd : ∀ x, ‖E (t,x)-E' (t,x)‖≤D)
    (hBd : ∀ x, ‖B (t,x)-B' (t,x)‖≤D) (z z' : Phase) :
    ‖lorentzField E B (t,z)-lorentzField E' B' (t,z')‖≤(1+2*N+L)*‖z-z'‖+2*D := by
  have hpos : ‖z.1-z'.1‖≤‖z-z'‖ := by simpa only [Prod.fst_sub] using norm_fst_le (z-z')
  have hvel : ‖z.2-z'.2‖≤‖z-z'‖ := by simpa only [Prod.snd_sub] using norm_snd_le (z-z')
  have hu : ‖velocity z.2‖≤1 := (norm_velocity_lt_one _).le
  have hu' : ‖velocity z'.2‖≤1 := (norm_velocity_lt_one _).le
  have hUd : ‖velocity z.2-velocity z'.2‖≤‖z-z'‖ := (velocity_global_lipschitz z'.2 z.2).trans hvel
  have hF : ‖E (t,z.1)+cross (velocity z.2) (B (t,z.1))-
      (E' (t,z'.1)+cross (velocity z'.2) (B' (t,z'.1)))‖≤(2*N+L)*‖z-z'‖+2*D := by
    have he : E (t,z.1)+cross (velocity z.2) (B (t,z.1))-
        (E' (t,z'.1)+cross (velocity z'.2) (B' (t,z'.1)))=
        (E (t,z.1)-E (t,z'.1))+(E (t,z'.1)-E' (t,z'.1))+
        cross (velocity z.2-velocity z'.2) (B (t,z.1))+
        cross (velocity z'.2) (B (t,z.1)-B (t,z'.1))+
        cross (velocity z'.2) (B (t,z'.1)-B' (t,z'.1)) := by
      rw [cross_sub_left,cross_sub_right,cross_sub_right]
      abel
    rw [he]
    have h₁ := (hEx z'.1 z.1).trans (mul_le_mul_of_nonneg_left hpos hN)
    have h₂ := hEd z'.1
    have h₃ := (norm_cross_le _ _).trans (mul_le_mul hUd (hB z.1) (norm_nonneg _) (norm_nonneg _))
    have h₄ := (norm_cross_le _ _).trans (mul_le_mul hu' ((hBx z'.1 z.1).trans
      (mul_le_mul_of_nonneg_left hpos hN)) (norm_nonneg _) zero_le_one)
    have h₅ := (norm_cross_le _ _).trans (mul_le_mul hu' (hBd z'.1) (norm_nonneg _) zero_le_one)
    have hh := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h₁ h₂)) h₃)) h₄)) h₅)
    exact hh.trans_eq (by ring)
  simp only [lorentzField]
  rw [Prod.norm_def]
  simp only [Prod.fst_sub,Prod.snd_sub]
  apply max_le
  · exact hUd.trans (by nlinarith [norm_nonneg (z-z')])
  · exact hF.trans (by nlinarith [norm_nonneg (z-z')])

lemma gronwallBound_le_exp_linear {δ K ε t : ℝ} (hK : 0<K) (hε : 0≤ε) (_ht : 0≤t) :
    gronwallBound δ K ε t≤(δ+ε*t)*Real.exp (K*t) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  have h := Real.add_one_le_exp (-(K*t))
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (K*t)).le
  rw [Real.exp_neg,inv_mul_cancel₀ (Real.exp_ne_zero (K*t))] at hmul
  have hx : Real.exp (K*t)-1≤K*t*Real.exp (K*t) := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hx (div_nonneg hε hK.le)
  have he : ε/K*(K*t*Real.exp (K*t))=ε*t*Real.exp (K*t) := by field_simp
  rw [he] at hh
  nlinarith

lemma SmoothLorentzFlow.backward_stability {E B E' B' : Field}
    (F : SmoothLorentzFlow E B) (G : SmoothLorentzFlow E' B') {T L N D : ℝ}
    (hL : 0≤L) (hN : 0≤N) (hD : 0≤D)
    (hB : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEd : ∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D)
    (hBd : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)-B' (t,x)‖≤D)
    {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
    ‖F.backward (t,z)-G.backward (t,z')‖≤
      (‖z-z'‖+2*D*t)*Real.exp ((1+2*N+L)*t) := by
  let α : ℝ → Phase := fun u => F.forward (F.backward (t,z)) (t-u)
  let β : ℝ → Phase := fun u => G.forward (G.backward (t,z')) (t-u)
  let K := 1+2*N+L
  have hK : 0<K := by dsimp [K]; linarith
  have hα (u : ℝ) : HasDerivAt α (-lorentzField E B (t-u,α u)) u := by
    have hh := (F.ode (F.backward (t,z)) (t-u)).scomp u ((hasDerivAt_id u).const_sub t)
    simpa only [α, Function.comp_def,one_smul,neg_smul] using hh
  have hβ (u : ℝ) : HasDerivAt β (-lorentzField E' B' (t-u,β u)) u := by
    have hh := (G.ode (G.backward (t,z')) (t-u)).scomp u ((hasDerivAt_id u).const_sub t)
    simpa only [β, Function.comp_def,one_smul,neg_smul] using hh
  have hfc : ContinuousOn (fun u => α u-β u) (Icc 0 t) :=
    (continuous_iff_continuousAt.mpr fun u => (hα u).continuousAt).continuousOn.sub
      (continuous_iff_continuousAt.mpr fun u => (hβ u).continuousAt).continuousOn
  have h₀ : ‖α 0-β 0‖≤‖z-z'‖ := by simp [α,β,F.right_inverse,G.right_inverse]
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le hfc
    (fun u _ => ((hα u).sub (hβ u)).hasDerivWithinAt) (K:=K) (ε:=2*D) h₀
    (fun u hu => by
      have htime : t-u∈Icc 0 T := ⟨by linarith [hu.2],by linarith [ht.2,hu.1]⟩
      simpa only [neg_sub_neg,norm_sub_rev] using
        lorentzField_difference_bound hL hN hD (hB _ htime) (hEx _ htime) (hBx _ htime)
          (hEd _ htime) (hBd _ htime) (α u) (β u)) t ⟨ht.1,le_rfl⟩
  simp only [α,β,sub_self,F.initial,G.initial,sub_zero] at hh
  exact hh.trans (gronwallBound_le_exp_linear hK (by positivity) ht.1)

lemma transported_comparison_oai {d : Datum} {s s' : Solution} {E B E' B' : Field}
    (hf : ContDiff ℝ ∞ s.f) (hg : ContDiff ℝ ∞ s'.f)
    (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ E') (hB' : ContDiff ℝ ∞ B')
    (hV : TransportFor s E B) (hV' : TransportFor s' E' B')
    (h₀ : ∀ z, s.f (0,z)=d.f₀ z) (h₀' : ∀ z, s'.f (0,z)=d.f₀ z)
    {T A L N D : ℝ} (hA : 0≤A) (hL : 0≤L) (hN : 0≤N) (hD : 0≤D)
    (ha : ∀ z w, |d.f₀ z-d.f₀ w|≤A*‖z-w‖)
    (hBb : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)‖≤L)
    (hEx : ∀ t∈Icc 0 T, ∀ x y, ‖E (t,y)-E (t,x)‖≤N*‖y-x‖)
    (hBx : ∀ t∈Icc 0 T, ∀ x y, ‖B (t,y)-B (t,x)‖≤N*‖y-x‖)
    (hEd : ∀ t∈Icc 0 T, ∀ x, ‖E (t,x)-E' (t,x)‖≤D)
    (hBd : ∀ t∈Icc 0 T, ∀ x, ‖B (t,x)-B' (t,x)‖≤D)
    {t : ℝ} (ht : t∈Icc 0 T) (z z' : Phase) :
    |s.f (t,z)-s'.f (t,z')|≤A*(‖z-z'‖+2*D*t)*Real.exp ((1+2*N+L)*t) := by
  obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
  obtain ⟨G⟩ := exists_smoothLorentzFlow hE' hB'
  rw [F.transport_for_inverse hf hV,G.transport_for_inverse hg hV',h₀,h₀']
  exact (ha _ _).trans ((mul_le_mul_of_nonneg_left
    (F.backward_stability G hL hN hD hBb hEx hBx hEd hBd ht z z') hA).trans_eq (by ring))

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.transported_comparison_oai := @OAI.RVM.transported_comparison_oai
