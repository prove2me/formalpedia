-- Prove2me | solution 1 for OAI.SKValueG.weak_profile_guerra_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:10:59.394252+00:00
-- url     : https://prove2.me/submissions/cfea6e4d-2d26-4614-812e-aeaf4607a625

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_SmoothTerminal_liftProfile_bound

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_JetAlgebra
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

namespace JetExpr

lemma uniform_bound {α : Type*} {R : ℕ → α → ℝ}
    (hR : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ a, |R j a|≤C) (e : JetExpr) :
    ∃ C : ℝ, 0≤C ∧ ∀ a, |eval (fun j ↦ R j a) e|≤C := by
  induction e with
  | const c => exact ⟨|c|,abs_nonneg c,fun _ ↦ le_rfl⟩
  | coord j => exact hR j
  | add e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A+B,add_nonneg hA hB,fun a ↦ (abs_add_le _ _).trans (add_le_add (he a) (hf a))⟩
  | mul e f he hf =>
    obtain ⟨A,hA,he⟩ := he
    obtain ⟨B,hB,hf⟩ := hf
    exact ⟨A*B,mul_nonneg hA hB,fun a ↦ by
      simpa only [eval,abs_mul] using mul_le_mul (he a) (hf a) (abs_nonneg _) hA⟩

end JetExpr
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_ColeHopfPDE
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma heat_log_pde {f f' f'' : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf'' : Continuous f'') (hfg : ExpGrowth f) (hf'g : ExpGrowth f')
    (hf''g : ExpGrowth f'') {c h : ℝ} (hc : c≠0) (hh : 0<h)
    (hp : ∀ x, heat h f x ≠ 0) (x : ℝ) :
    HasDerivAt (fun r ↦ Real.log (heat r f x)/c)
      ((1/2 : ℝ)*(deriv (deriv (fun y ↦ Real.log (heat h f y)/c)) x +
        c*(deriv (fun y ↦ Real.log (heat h f y)/c) x)^2)) h := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr (fun y ↦ (hf' y).continuousAt)
  have hd := ((heat_time_hasDerivAt hf hf' hf'' hfg hf'g hf''g x hh).log (hp x)).div_const c
  rw [heat_log_spatial_second hf hf' hf'' hfg hf'g hf''g c h hp,
    heat_log_spatial_deriv hf hf'c hfg hf'g c h hp]
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  field_simp [hp x,hc]
  ring

lemma coleHopf_pde_of_pos {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0 < c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  let f := fun x ↦ Real.exp (c*ψ x)
  let f' := fun x ↦ Real.exp (c*ψ x)*(c*deriv ψ x)
  let f'' := fun x ↦ Real.exp (c*ψ x)*((c*deriv ψ x)^2+c*deriv (deriv ψ) x)
  have hψd := hψs.differentiable (by norm_num)
  have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
  have hψ'd : Differentiable ℝ (deriv ψ) := hψ's.differentiable (by norm_num)
  have hψc := hψs.continuous
  have hψ'c := hψs.continuous_deriv (by norm_num)
  have hψ''c : Continuous (deriv (deriv ψ)) :=
    hψ's.continuous_deriv (by norm_num)
  have hfd (y : ℝ) : HasDerivAt f (f' y) y := ((hψd y).hasDerivAt.const_mul c).exp
  have hf'd (y : ℝ) : HasDerivAt f' (f'' y) y := by
    have hd := (hfd y).mul ((hψ'd y).hasDerivAt.const_mul c)
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [f,f',f'']
    ring
  have hfg : ExpGrowth f := ExpGrowth.exp_lipschitz hψ hc.le
  have hψ'b (y : ℝ) : |deriv ψ y|≤1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y)
  have hf'g : ExpGrowth f' := hfg.mul_bounded hc.le (fun y ↦ by
    simpa only [abs_mul,abs_of_pos hc,mul_one] using
      mul_le_mul_of_nonneg_left (hψ'b y) hc.le)
  have hf''g : ExpGrowth f'' := hfg.mul_bounded (R := c^2+c*K) (by positivity) (fun y ↦ by
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg _),abs_mul,abs_of_pos hc]
    have hsq : (c*deriv ψ y)^2 ≤ c^2 := by
      have h := sq_le_sq₀ (abs_nonneg (deriv ψ y)) zero_le_one |>.mpr (hψ'b y)
      rw [sq_abs] at h
      nlinarith [mul_nonneg (sq_nonneg c) (sub_nonneg.mpr h)]
    linarith [mul_le_mul_of_nonneg_left (hψ'' y) hc.le])
  have hp (y : ℝ) : heat h f y≠0 := (lipschitz_exp_integral_pos hψ hc.le y (Real.sqrt h)).ne'
  have hd := heat_log_pde hfd hf'd (by dsimp [f'']; fun_prop) hfg hf'g hf''g hc.ne' hh hp x
  have heq (r : ℝ) : coleHopf c r ψ = fun y ↦ Real.log (heat r f y)/c := by
    funext y
    simp only [coleHopf,ite_eq_right hc.ne',f]
  simp_rw [heq]
  exact hd

lemma coleHopf_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c h : ℝ} (hc : 0 ≤ c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ coleHopf c r ψ x)
      ((1/2 : ℝ)*(deriv (deriv (coleHopf c h ψ)) x+c*(deriv (coleHopf c h ψ) x)^2)) h := by
  rcases hc.eq_or_lt with rfl | hc
  · have hd (y : ℝ) := ((hψs.differentiable (by norm_num)) y).hasDerivAt
    have hψ's : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.mp hψs).2.2
    have hd' (y : ℝ) := ((hψ's.differentiable (by norm_num)) y).hasDerivAt
    have hψ'g : ExpGrowth (deriv ψ) := ExpGrowth.of_bound zero_le_one (fun y ↦ by
      simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hψ (x₀ := y))
    have hψ''g := ExpGrowth.of_bound hK hψ''
    have heq (r : ℝ) : coleHopf 0 r ψ = heat r ψ := by funext y; simp [coleHopf]
    have h1 : deriv (heat h ψ)=heat h (deriv ψ) := by
      funext y
      exact (heat_spatial_hasDerivAt hd hψ's.continuous (ExpGrowth.lipschitz hψ) hψ'g y h).deriv
    have h2 : deriv (heat h (deriv ψ))=heat h (deriv (deriv ψ)) := by
      funext y
      exact (heat_spatial_hasDerivAt hd' (hψ's.continuous_deriv (by norm_num)) hψ'g hψ''g y h).deriv
    simpa only [heq,h1,h2,zero_mul,add_zero] using
      heat_time_hasDerivAt hd hd' (hψ's.continuous_deriv (by norm_num))
        (ExpGrowth.lipschitz hψ) hψ'g hψ''g x hh
  · exact coleHopf_pde_of_pos hψ hψs hK hψ'' hc hh x

lemma coleHopf_backward_pde {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    (hψs : ContDiff ℝ 2 ψ) {K : ℝ} (hK : 0≤K)
    (hψ'' : ∀ x, |deriv (deriv ψ) x|≤K) {c b t : ℝ} (hc : 0 ≤ c) (ht : t<b) (x : ℝ) :
    HasDerivAt (fun s ↦ coleHopf c (b-s) ψ x)
      (-(1/2 : ℝ)*(deriv (deriv (coleHopf c (b-t) ψ)) x+
        c*(deriv (coleHopf c (b-t) ψ) x)^2)) t := by
  have hd := (coleHopf_pde hψ hψs hK hψ'' hc (sub_pos.mpr ht) x).comp t
    ((hasDerivAt_const t b).sub (hasDerivAt_id t))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [zero_sub]
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatContinuity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma coleHopf_continuous {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {c : ℝ} (hc : 0 ≤ c) :
    Continuous (fun p : ℝ×ℝ ↦ coleHopf c p.1 ψ p.2) := by
  by_cases hc0 : c=0
  · simpa [SKValue.coleHopf,hc0] using heat_continuous hψ.continuous (ExpGrowth.lipschitz hψ)
  · have hH := heat_continuous (Real.continuous_exp.comp (continuous_const.mul hψ.continuous)) (ExpGrowth.exp_lipschitz hψ hc)
    simpa only [coleHopf,ite_eq_right hc0,Function.comp_def,Pi.mul_apply] using
      (hH.log (fun p ↦ (lipschitz_exp_integral_pos hψ hc p.2 (Real.sqrt p.1)).ne')).div_const c

lemma SmoothTerminal.coleHopf_uniform_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {c : ℝ} (hc : 0 ≤ c) :
    ∀ n, ∃ C : ℝ, 0≤C ∧ ∀ h x, |iteratedDeriv n (deriv (coleHopf c h ψ)) x|≤C := by
  rcases hc.eq_or_lt with rfl | hc
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    refine ⟨C,hC,?_⟩
    intro h x
    rw [coleHopf_zero_coeff]
    rw [hψ.heat_deriv_jets]
    exact heat_bound hC hb h x
  · exact coleHopf_deriv_uniform_bounds_of_pos hψ.lipschitz hψ.smooth hψ.jets hc

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_LogHeatJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma nonneg_time_lipschitz {f g : ℝ → ℝ} {C : ℝ} (hC : 0≤C)
    (hf : Continuous f) (hg : Continuous g)
    (hd : ∀ h, 0<h → HasDerivAt f (g h) h)
    (hb : ∀ h, 0≤h → |g h|≤C) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |f s-f t|≤C* |s-t| := by
  wlog hst : s≤t generalizing s t
  · simpa only [abs_sub_comm] using this ht hs (le_of_not_ge hst)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hf.continuousOn
    (fun r hr ↦ hd r (hs.trans_lt hr.1)) (hg.intervalIntegrable _ _)
  have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := t) (f := g) (C := |C|) (fun r hr ↦ by
      rw [uIoc_of_le hst] at hr
      simpa only [Real.norm_eq_abs] using
        (hb r (hs.trans hr.1.le)).trans (le_abs_self C))
  rw [he,Real.norm_eq_abs] at hb'
  simpa only [abs_of_nonneg hC,abs_sub_comm,mul_comm] using hb'

lemma SmoothTerminal.coleHopf_time_jets {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ d : ℝ → ℝ → ℝ, Continuous (fun p : ℝ×ℝ ↦ d p.1 p.2) ∧
      (∃ C : ℝ, 0≤C ∧ ∀ h x, |d h x|≤C) ∧
      ∀ h x, 0<h → HasDerivAt (fun r ↦ iteratedDeriv n (deriv (coleHopf c r ψ)) x) (d h x) h := by
  rcases hc.eq_or_lt with rfl | hc
  · let d := fun h x ↦ (1/2 : ℝ)*iteratedDeriv (n+3) (heat h ψ) x
    refine ⟨d,continuous_const.mul (heat_jet_continuous hψ.smooth hψ.growth _),?_,?_⟩
    · obtain ⟨C,hC,hb⟩ := hψ.jets.bound (n+2)
      refine ⟨C/2,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2),
        heat_iteratedDeriv hψ.smooth hψ.growth,show n+3=(n+2)+1 from rfl,iteratedDeriv_succ']
      linarith [heat_bound hC hb h x]
    · intro h x hh
      simpa only [coleHopf_zero_coeff,←iteratedDeriv_succ'] using heat_jet_time hψ.smooth hψ.growth (n+1) x hh
  · let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
    let R := fun j (p : ℝ×ℝ) ↦ normalizedJet F j p.1 p.2
    let E := JetExpr.D JetExpr.σh (JetExpr.logGradientJet n)
    let d := fun h x ↦ c⁻¹*JetExpr.eval (fun j ↦ R j (h,x)) E
    have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    have hR : ∀ j, Continuous (R j) := fun j ↦ heat_normalizedJet_continuous hes hg hp j
    refine ⟨d,continuous_const.mul (JetExpr.continuous_eval hR E),?_,?_⟩
    · have hRb : ∀ j, ∃ C : ℝ, 0≤C ∧ ∀ p, |R j p|≤C := by
        intro j
        obtain ⟨C,hC,hb⟩ := exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc.le j
        exact ⟨C,hC,fun p ↦ hb p.1 p.2⟩
      obtain ⟨C,hC,hb⟩ := JetExpr.uniform_bound hRb E
      refine ⟨|c⁻¹| * C,by positivity,?_⟩
      intro h x
      dsimp only [d]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb (h,x)) (abs_nonneg _)
    · intro h x hh
      simp_rw [coleHopf_gradient_jet_expr hψ hc]
      apply HasDerivAt.const_mul
      apply JetExpr.hasDerivAt_eval
      intro j
      simpa only [JetExpr.eval_σh] using heat_normalizedJet_time hes hg hp j x hh

lemma SmoothTerminal.coleHopf_jets_time_lipschitz {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ s t x, 0 ≤ s → 0 ≤ t →
      |iteratedDeriv n (deriv (coleHopf c s ψ)) x-iteratedDeriv n (deriv (coleHopf c t ψ)) x|≤C* |s-t| := by
  obtain ⟨d,hdc,⟨C,hC,hb⟩,hd⟩ := hψ.coleHopf_time_jets hc n
  refine ⟨C,hC,?_⟩
  intro s t x hs ht
  exact nonneg_time_lipschitz hC
    ((hψ.coleHopf_joint_jets hc n).comp (continuous_id.prodMk continuous_const))
    (hdc.comp (continuous_id.prodMk continuous_const))
    (fun h hh ↦ hd h x hh) (fun h _ ↦ hb h x) hs ht

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_SmoothEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma coleHopf_gradient_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c h : ℝ} (hc : 0 ≤ c) (hh : 0<h) (x : ℝ) :
    HasDerivAt (fun r ↦ deriv (coleHopf c r ψ) x)
      ((1/2 : ℝ)*deriv (deriv (deriv (coleHopf c h ψ))) x+
        c*(deriv (coleHopf c h ψ) x*deriv (deriv (coleHopf c h ψ)) x)) h := by
  rcases hc.eq_or_lt with rfl | hc
  · simpa only [coleHopf_zero_coeff,zero_mul,add_zero,show (3 : ℕ)=1+1+1 from rfl,
      iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using heat_jet_time hψ.smooth hψ.growth 1 x hh
  · let F := fun r ↦ heat r (fun y ↦ Real.exp (c*ψ y))
    have hes : ContDiff ℝ ∞ (fun x ↦ Real.exp (c*ψ x)) := (contDiff_const.mul hψ.smooth).exp
    have hg := exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc.le
    have hp : ∀ r x, F r x≠0 := fun r x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc.le x (Real.sqrt r)).ne'
    have hd := (heat_normalizedJet_time hes hg hp 1 x hh).const_mul c⁻¹
    have hj0 := congrFun (coleHopf_gradient_jet_expr hψ hc 0 h) x
    have hj1 := congrFun (coleHopf_gradient_jet_expr hψ hc 1 h) x
    have hj2 := congrFun (coleHopf_gradient_jet_expr hψ hc 2 h) x
    simp only [iteratedDeriv_zero,show (2 : ℕ)=1+1 from rfl,
      iteratedDeriv_succ,JetExpr.logGradientJet,JetExpr.D,JetExpr.σx,JetExpr.eval] at hj0 hj1 hj2
    convert! hd using 1
    · funext r
      rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc r]
    · rw [hj0,hj1,hj2]
      field_simp [hc.ne']
      ring

lemma integral_from_deriv_on_strip {T : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hg : ContinuousOn g (Icc (0 : ℝ) T))
    (hd : ∀ r∈Ioo (0 : ℝ) T, HasDerivAt f (g r) r)
    {s t : ℝ} (hs : s∈Icc (0 : ℝ) T) (ht : t∈Icc (0 : ℝ) T) :
    f s-f t=∫ r in t..s, g r := by
  have hi {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) :
      IntervalIntegrable g volume a b :=
    (hg.mono (by
      intro r hr
      rcases mem_uIcc.mp hr with hr | hr
      · exact ⟨ha.1.trans hr.1,hr.2.trans hb.2⟩
      · exact ⟨hb.1.trans hr.1,hr.2.trans ha.2⟩)).intervalIntegrable
  have he {a : ℝ} (ha : a∈Icc (0 : ℝ) T) : ∫ r in (0 : ℝ)..a, g r=f a-f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.1
      (hf.mono (Icc_subset_Icc le_rfl ha.2))
      (fun r hr ↦ hd r ⟨hr.1,hr.2.trans_le ha.2⟩) (hi ⟨le_rfl,ha.1.trans ha.2⟩ ha)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi ⟨le_rfl,ht.1.trans ht.2⟩ ht) (hi ht hs)
  rw [he hs,he ht] at hadd
  linarith

lemma SmoothTerminal.backward_jet_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) (n : ℕ) (x : ℝ) :
    Continuous (fun t ↦ iteratedDeriv n (deriv (coleHopf c (T-t) ψ)) x) := by
  have hmap : Continuous (fun t : ℝ ↦ (T-t,x)) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hj : Continuous (fun p : ℝ×ℝ ↦ iteratedDeriv n (deriv (coleHopf c p.1 ψ)) p.2) :=
    hψ.coleHopf_joint_jets hc n
  convert hj.comp hmap using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma SmoothTerminal.backward_gradient_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (coleHopf c (T-t) ψ) x) := by
  simpa only [iteratedDeriv_zero] using hψ.backward_jet_continuous hc T 0 x

lemma SmoothTerminal.backward_curvature_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (deriv (coleHopf c (T-t) ψ)) x) := by
  simpa only [iteratedDeriv_one] using hψ.backward_jet_continuous hc T 1 x

lemma SmoothTerminal.backward_third_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ deriv (deriv (deriv (coleHopf c (T-t) ψ))) x) := by
  simpa only [show (2 : ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
    using hψ.backward_jet_continuous hc T 2 x

lemma SmoothTerminal.backward_value_continuous {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T x : ℝ) :
    Continuous (fun t ↦ coleHopf c (T-t) ψ x) :=
  (coleHopf_continuous hψ.lipschitz hc).comp ((continuous_const.sub continuous_id).prodMk continuous_const)

lemma SmoothTerminal.backward_value_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) {s t : ℝ}
    (ht : t∈Icc (0 : ℝ) T) (hs : s∈Icc (0 : ℝ) T) (x : ℝ) :
    coleHopf c (T-s) ψ x-coleHopf c (T-t) ψ x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (coleHopf c (T-r) ψ)) x+
      c*((1/2 : ℝ)*(deriv (coleHopf c (T-r) ψ) x)^2)) := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (coleHopf c (T-r) ψ)) x+
    c*((1/2 : ℝ)*(deriv (coleHopf c (T-r) ψ) x)^2)
  have hgc : Continuous g := by
    exact (continuous_const.mul (hψ.backward_curvature_continuous hc T x)).add
      (continuous_const.mul (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).pow 2)))
  have hd (r : ℝ) (hr : r∈Ioo (0 : ℝ) T) :
      HasDerivAt (fun r ↦ coleHopf c (T-r) ψ x) (-g r) r := by
    obtain ⟨K,hK,hb⟩ := hψ.jets.deriv.bound_zero
    have hd := coleHopf_backward_pde hψ.lipschitz
      (hψ.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hK hb hc hr.2 x
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [g]
    ring
  have he := integral_from_deriv_on_strip
    (hψ.backward_value_continuous hc T x).continuousOn hgc.neg.continuousOn hd hs ht
  change _ = ∫ r in t..s, -(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.backward_gradient_pde {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) {s t : ℝ}
    (ht : t∈Icc (0 : ℝ) T) (hs : s∈Icc (0 : ℝ) T) (x : ℝ) :
    deriv (coleHopf c (T-s) ψ) x-deriv (coleHopf c (T-t) ψ) x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (deriv (coleHopf c (T-r) ψ))) x+
      c*(deriv (coleHopf c (T-r) ψ) x*deriv (deriv (coleHopf c (T-r) ψ)) x)) := by
  let g := fun r ↦ (1/2 : ℝ)*deriv (deriv (deriv (coleHopf c (T-r) ψ))) x+
    c*(deriv (coleHopf c (T-r) ψ) x*deriv (deriv (coleHopf c (T-r) ψ)) x)
  have hgc : Continuous g := by
    exact (continuous_const.mul (hψ.backward_third_continuous hc T x)).add
      (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).mul (hψ.backward_curvature_continuous hc T x)))
  have hd (r : ℝ) (hr : r∈Ioo (0 : ℝ) T) :
      HasDerivAt (fun r ↦ deriv (coleHopf c (T-r) ψ) x) (-g r) r := by
    have hd := (coleHopf_gradient_pde hψ hc (sub_pos.mpr hr.2) x).comp r
      ((hasDerivAt_const r T).sub (hasDerivAt_id r))
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [g]
    ring
  have he := integral_from_deriv_on_strip (hψ.backward_gradient_continuous hc T x).continuousOn hgc.neg.continuousOn hd hs ht
  change _ = ∫ r in t..s, -(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.constant_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    SmoothEvolution T (fun _ ↦ c) (fun t ↦ coleHopf c (T-t) ψ) := by
  refine ⟨fun _ _ ↦ hψ.evolve hc _,fun x ↦ (hψ.backward_value_continuous hc T x).continuousOn,
    fun n x ↦ (hψ.backward_jet_continuous hc T n x).continuousOn,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.coleHopf_uniform_jets hc n
    exact ⟨C,hC,fun t _ x ↦ hb (T-t) x⟩
  · intro n
    obtain ⟨L,hL,hb⟩ := hψ.coleHopf_jets_time_lipschitz hc n
    refine ⟨L,hL,?_⟩
    intro s hs t ht x
    have he : |(T-s)-(T-t)|=|s-t| := by rw [sub_sub_sub_cancel_left,abs_sub_comm]
    simpa only [he] using hb (T-s) (T-t) x (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2)
  · intro t ht s hs x
    exact hψ.backward_value_pde hc T ht hs x
  · intro t ht s hs x
    exact hψ.backward_gradient_pde hc T ht hs x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TimePatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma patchTime_left {E : Type*} {a t : ℝ} (f g : ℝ → E) (ht : t≤a) :
    patchTime a f g t=f t := ite_eq_left ht
lemma patchTime_right {E : Type*} {a t : ℝ} (f g : ℝ → E) (ht : a<t) :
    patchTime a f g t=g (t-a) := ite_eq_right (not_le.mpr ht)

lemma patchTime_continuous {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) a)) (hg : ContinuousOn g (Icc (0 : ℝ) b))
    (hfg : f a=g 0) : ContinuousOn (patchTime a f g) (Icc (0 : ℝ) (a+b)) := by
  have hf' : ContinuousOn f (Icc (0 : ℝ) (a+b)∩closure (Iic a)) := by
    apply hf.mono
    simp only [closure_Iic]
    exact fun _ hx ↦ ⟨hx.1.1,hx.2⟩
  have hg' : ContinuousOn (fun t ↦ g (t-a)) (Icc (0 : ℝ) (a+b)∩closure (Iic a)ᶜ) := by
    apply hg.comp (continuous_id.sub continuous_const).continuousOn
    simp only [compl_Iic,closure_Ioi]
    intro t ht
    change 0≤t-a ∧ t-a≤b
    exact ⟨sub_nonneg.mpr ht.2,by linarith [ht.1.2]⟩
  have he : ∀ t∈Icc (0 : ℝ) (a+b)∩frontier (Iic a), f t=g (t-a) := by
    intro t ht
    have ht' : t=a := by simpa only [frontier_Iic,mem_singleton_iff] using ht.2
    subst t
    simpa only [sub_self] using hfg
  have hh := ContinuousOn.piecewise he hf' hg'
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  simp only [patchTime,Set.piecewise,mem_Iic]

lemma patchTime_bound {a b C D : ℝ} (hC : 0≤C) (hD : 0≤D) {f g : ℝ → ℝ}
    (hf : ∀ t∈Icc (0 : ℝ) a, |f t|≤C) (hg : ∀ t∈Icc (0 : ℝ) b, |g t|≤D) :
    ∀ t∈Icc (0 : ℝ) (a+b), |patchTime a f g t|≤C+D := by
  intro t ht
  by_cases hta : t≤a
  · rw [patchTime_left f g hta]
    exact (hf t ⟨ht.1,hta⟩).trans (le_add_of_nonneg_right hD)
  · rw [patchTime_right f g (lt_of_not_ge hta)]
    exact (hg (t-a) ⟨by linarith,by linarith [ht.2]⟩).trans (le_add_of_nonneg_left hC)

lemma patchTime_lipschitz {a b C D : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hC : 0≤C) (hD : 0≤D) {f g : ℝ → ℝ}
    (hf : ∀ s∈Icc (0 : ℝ) a, ∀ t∈Icc (0 : ℝ) a, |f s-f t|≤C*|s-t|)
    (hg : ∀ s∈Icc (0 : ℝ) b, ∀ t∈Icc (0 : ℝ) b, |g s-g t|≤D*|s-t|)
    (hfg : f a=g 0) :
    ∀ s∈Icc (0 : ℝ) (a+b), ∀ t∈Icc (0 : ℝ) (a+b),
      |patchTime a f g s-patchTime a f g t|≤(C+D)*|s-t| := by
  have hcross {s t : ℝ} (hs : s∈Icc (0 : ℝ) a) (ht : t∈Icc a (a+b)) :
      |f s-g (t-a)|≤(C+D)*|s-t| := by
    have h1 := hf s hs a ⟨ha,le_rfl⟩
    have h2 := hg 0 ⟨le_rfl,hb⟩ (t-a) ⟨sub_nonneg.mpr ht.1,by linarith [ht.2]⟩
    have hh := abs_sub_le (f s) (f a) (g (t-a))
    rw [hfg] at hh h1
    rw [abs_of_nonpos (sub_nonpos.mpr hs.2)] at h1
    rw [zero_sub,abs_neg,abs_of_nonneg (sub_nonneg.mpr ht.1)] at h2
    rw [abs_of_nonpos (sub_nonpos.mpr (hs.2.trans ht.1))]
    nlinarith [mul_nonneg hC (sub_nonneg.mpr ht.1),mul_nonneg hD (sub_nonneg.mpr hs.2)]
  intro s hs t ht
  by_cases hsa : s≤a <;> by_cases hta : t≤a
  · rw [patchTime_left f g hsa,patchTime_left f g hta]
    have hh := hf s ⟨hs.1,hsa⟩ t ⟨ht.1,hta⟩
    nlinarith [mul_nonneg hD (abs_nonneg (s-t))]
  · rw [patchTime_left f g hsa,patchTime_right f g (lt_of_not_ge hta)]
    exact hcross ⟨hs.1,hsa⟩ ⟨le_of_lt (lt_of_not_ge hta),ht.2⟩
  · rw [patchTime_right f g (lt_of_not_ge hsa),patchTime_left f g hta,abs_sub_comm,abs_sub_comm s t]
    exact hcross ⟨ht.1,hta⟩ ⟨le_of_lt (lt_of_not_ge hsa),hs.2⟩
  · rw [patchTime_right f g (lt_of_not_ge hsa),patchTime_right f g (lt_of_not_ge hta)]
    have hh := hg (s-a) ⟨by linarith,by linarith [hs.2]⟩ (t-a) ⟨by linarith,by linarith [ht.2]⟩
    rw [sub_sub_sub_cancel_right] at hh
    nlinarith [mul_nonneg hC (abs_nonneg (s-t))]

lemma patchTime_intervalIntegrable {a b : ℝ} (ha : 0≤a) (hb : 0≤b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 a) (hg : IntervalIntegrable g volume 0 b) :
    IntervalIntegrable (patchTime a f g) volume 0 (a+b) := by
  have hl : IntervalIntegrable (patchTime a f g) volume 0 a := by
    apply hf.congr_uIoo
    rw [uIoo_of_le ha]
    intro t ht
    exact (patchTime_left f g ht.2.le).symm
  have hr : IntervalIntegrable (fun t ↦ g (t-a)) volume a (a+b) := by
    simpa only [zero_add,add_comm b a] using hg.comp_sub_right a
  apply hl.trans
  apply hr.congr_uIoo
  rw [uIoo_of_le (le_add_of_nonneg_right hb)]
  intro t ht
  exact (patchTime_right f g ht.1).symm

lemma patchTime_integral_left {a s : ℝ} (hs : s∈Icc (0 : ℝ) a) (f g : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..s, patchTime a f g r)=∫ r in (0 : ℝ)..s, f r := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hs.1]
  exact fun r hr ↦ patchTime_left f g (hr.2.trans hs.2)

lemma patchTime_integral_right {a s : ℝ} (hs : a ≤ s) (f g : ℝ → ℝ) :
    (∫ r in a..s, patchTime a f g r)=∫ r in (0 : ℝ)..(s-a), g r := by
  calc
    _ = ∫ r in a..s, g (r-a) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hs
      exact fun r hr ↦ patchTime_right f g hr.1
    _ = _ := by rw [intervalIntegral.integral_comp_sub_right,sub_self]

lemma patchTime_primitive {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {f g p q : ℝ → ℝ} (hp : IntervalIntegrable p volume 0 a)
    (hq : IntervalIntegrable q volume 0 b)
    (hf : ∀ t∈Icc (0 : ℝ) a, f t-f 0=∫ r in (0 : ℝ)..t, p r)
    (hg : ∀ t∈Icc (0 : ℝ) b, g t-g 0=∫ r in (0 : ℝ)..t, q r)
    (hfg : f a=g 0) : ∀ t∈Icc (0 : ℝ) (a+b),
    patchTime a f g t-patchTime a f g 0=∫ r in (0 : ℝ)..t, patchTime a p q r := by
  intro t ht
  rw [patchTime_left f g ha]
  by_cases hta : t≤a
  · rw [patchTime_left f g hta,patchTime_integral_left ⟨ht.1,hta⟩]
    exact hf t ⟨ht.1,hta⟩
  · rw [patchTime_right f g (lt_of_not_ge hta)]
    have hi := patchTime_intervalIntegrable ha hb hp hq
    have hsub {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) :
        uIcc s t⊆uIcc (0 : ℝ) (a+b) := by
      rw [uIcc_of_le (add_nonneg ha hb)]
      exact uIcc_subset_Icc hs ht
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (hi.mono_set (hsub ⟨le_rfl,add_nonneg ha hb⟩ ⟨ha,le_add_of_nonneg_right hb⟩))
      (hi.mono_set (hsub ⟨ha,le_add_of_nonneg_right hb⟩ ht))
    rw [patchTime_integral_left ⟨ha,le_rfl⟩,patchTime_integral_right (le_of_lt (lt_of_not_ge hta))] at hh
    have h1 := hf a ⟨ha,le_rfl⟩
    have h2 := hg (t-a) ⟨by linarith,by linarith [ht.2]⟩
    linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolutionPatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue

lemma patchTime_apply {a t x : ℝ} (V W : ℝ → ℝ → ℝ) :
    patchTime a V W t x=patchTime a (fun t ↦ V t x) (fun t ↦ W t x) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma patchTime_gradient {a t : ℝ} (V W : ℝ → ℝ → ℝ) :
    deriv (patchTime a V W t)=patchTime a (fun t ↦ deriv (V t)) (fun t ↦ deriv (W t)) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma patchTime_jet {a t x : ℝ} (V W : ℝ → ℝ → ℝ) (n : ℕ) :
    iteratedDeriv n (deriv (patchTime a V W t)) x=
      patchTime a (fun t ↦ iteratedDeriv n (deriv (V t)) x) (fun t ↦ iteratedDeriv n (deriv (W t)) x) t := by
  by_cases ht : t≤a <;> simp [patchTime,ht]

lemma SmoothEvolution.value_rhs_integrable {T : ℝ} (hT : 0≤T)
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V)
    (hg : IntervalIntegrable γ volume 0 T) (x : ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2 : ℝ)*deriv (deriv (V r)) x+
      γ r*((1/2 : ℝ)*(deriv (V r) x)^2))) volume 0 T := by
  have hc1 : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have hc0 : ContinuousOn (fun t ↦ deriv (V t) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using h.continuous_jet 0 x
  apply IntervalIntegrable.neg
  apply IntervalIntegrable.add (hc1.intervalIntegrable.const_mul _)
  apply hg.mul_continuousOn
  convert! continuousOn_const.mul (hc0.pow 2) using 1
  all_goals try with_reducible_and_instances rfl

lemma SmoothEvolution.gradient_rhs_integrable {T : ℝ} (hT : 0≤T)
    {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : SmoothEvolution T γ V)
    (hg : IntervalIntegrable γ volume 0 T) (x : ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V r))) x+
      γ r*(deriv (V r) x*deriv (deriv (V r)) x))) volume 0 T := by
  have hc2 : ContinuousOn (fun t ↦ deriv (deriv (deriv (V t))) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero]
      using h.continuous_jet 2 x
  have hc1 : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have hc0 : ContinuousOn (fun t ↦ deriv (V t) x) (uIcc (0 : ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using h.continuous_jet 0 x
  apply IntervalIntegrable.neg
  apply IntervalIntegrable.add (hc2.intervalIntegrable.const_mul _)
  apply hg.mul_continuousOn
  convert! hc0.mul hc1 using 1
  all_goals try with_reducible_and_instances rfl

lemma primitive_to_integral {T : ℝ} (hT : 0≤T) {f p : ℝ → ℝ}
    (hp : IntervalIntegrable p volume 0 T)
    (hf : ∀ t∈Icc (0 : ℝ) T, f t-f 0=∫ r in (0 : ℝ)..t, p r)
    {s t : ℝ} (hs : s∈Icc (0 : ℝ) T) (ht : t∈Icc (0 : ℝ) T) :
    f s-f t=∫ r in t..s, p r := by
  have hi {a b : ℝ} (ha : a∈Icc (0 : ℝ) T) (hb : b∈Icc (0 : ℝ) T) :
      IntervalIntegrable p volume a b := hp.mono_set (by
    rw [uIcc_of_le hT]
    exact uIcc_subset_Icc ha hb)
  have hh := intervalIntegral.integral_add_adjacent_intervals (hi ⟨le_rfl,hT⟩ ht) (hi ht hs)
  rw [←hf s hs,←hf t ht] at hh
  linarith

lemma SmoothEvolution.patch_value_pde {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) (x : ℝ) :
    patchTime a V W s x-patchTime a V W t x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (patchTime a V W r)) x+
      patchTime a γ η r*((1/2 : ℝ)*(deriv (patchTime a V W r) x)^2)) := by
  let p := fun r ↦ -((1/2 : ℝ)*deriv (deriv (V r)) x+γ r*((1/2 : ℝ)*(deriv (V r) x)^2))
  let q := fun r ↦ -((1/2 : ℝ)*deriv (deriv (W r)) x+η r*((1/2 : ℝ)*(deriv (W r) x)^2))
  have hp := hV.value_rhs_integrable ha hγ x
  have hq := hW.value_rhs_integrable hb hη x
  have hv : ∀ t∈Icc (0 : ℝ) a, V t x-V 0 x=∫ r in (0 : ℝ)..t, p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.value_pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw : ∀ t∈Icc (0 : ℝ) b, W t x-W 0 x=∫ r in (0 : ℝ)..t, q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.value_pde 0 ⟨le_rfl,hb⟩ t ht x
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw (congrFun hjoin x)) hs ht
  rw [←patchTime_apply V W,←patchTime_apply V W] at he
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr : r≤a <;> simp [patchTime,hr]

lemma SmoothEvolution.patch_gradient_pde {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) {s t : ℝ} (hs : s∈Icc (0 : ℝ) (a+b)) (ht : t∈Icc (0 : ℝ) (a+b)) (x : ℝ) :
    deriv (patchTime a V W s) x-deriv (patchTime a V W t) x =
    -(∫ r in t..s, (1/2 : ℝ)*deriv (deriv (deriv (patchTime a V W r))) x+
      patchTime a γ η r*(deriv (patchTime a V W r) x*deriv (deriv (patchTime a V W r)) x)) := by
  let p := fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (V r))) x+γ r*(deriv (V r) x*deriv (deriv (V r)) x))
  let q := fun r ↦ -((1/2 : ℝ)*deriv (deriv (deriv (W r))) x+η r*(deriv (W r) x*deriv (deriv (W r)) x))
  have hp := hV.gradient_rhs_integrable ha hγ x
  have hq := hW.gradient_rhs_integrable hb hη x
  have hv : ∀ t∈Icc (0 : ℝ) a, deriv (V t) x-deriv (V 0) x=∫ r in (0 : ℝ)..t, p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.gradient_pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw : ∀ t∈Icc (0 : ℝ) b, deriv (W t) x-deriv (W 0) x=∫ r in (0 : ℝ)..t, q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.gradient_pde 0 ⟨le_rfl,hb⟩ t ht x
  have hj : deriv (V a) x=deriv (W 0) x := by rw [hjoin]
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw hj) hs ht
  simp_rw [patchTime_gradient,patchTime_apply]
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr : r≤a <;> simp [patchTime,hr]

lemma SmoothEvolution.patch {a b : ℝ} (ha : 0≤a) (hb : 0≤b)
    {γ η : ℝ → ℝ} {V W : ℝ → ℝ → ℝ}
    (hV : SmoothEvolution a γ V) (hW : SmoothEvolution b η W)
    (hγ : IntervalIntegrable γ volume 0 a) (hη : IntervalIntegrable η volume 0 b)
    (hjoin : V a=W 0) :
    SmoothEvolution (a+b) (patchTime a γ η) (patchTime a V W) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro t ht
    by_cases hta : t≤a
    · rw [patchTime_left V W hta]
      exact hV.slices t ⟨ht.1,hta⟩
    · rw [patchTime_right V W (lt_of_not_ge hta)]
      exact hW.slices (t-a) ⟨by linarith,by linarith [ht.2]⟩
  · intro x
    simp_rw [patchTime_apply]
    exact patchTime_continuous (hV.continuous_value x) (hW.continuous_value x) (congrFun hjoin x)
  · intro n x
    simp_rw [patchTime_jet]
    apply patchTime_continuous (hV.continuous_jet n x) (hW.continuous_jet n x)
    rw [hjoin]
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.bound n
    obtain ⟨D,hD,hw⟩ := hW.bound n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro t ht x
    rw [patchTime_jet]
    exact patchTime_bound hC hD (fun t ht ↦ hv t ht x) (fun t ht ↦ hw t ht x) t ht
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.temporal n
    obtain ⟨D,hD,hw⟩ := hW.temporal n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro s hs t ht x
    rw [patchTime_jet,patchTime_jet]
    apply patchTime_lipschitz ha hb hC hD (fun s hs t ht ↦ hv s hs t ht x)
      (fun s hs t ht ↦ hw s hs t ht x) _ s hs t ht
    rw [hjoin]
  · intro t ht s hs x
    exact hV.patch_value_pde ha hb hW hγ hη hjoin hs ht x
  · intro t ht s hs x
    exact hV.patch_gradient_pde ha hb hW hγ hη hjoin hs ht x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_FiniteStepEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma profileTime_nonneg (l : HeatProfile) : 0≤profileTime l := by
  induction l with
  | nil => exact le_rfl
  | cons p l ih => exact add_nonneg p.1.coe_nonneg ih

lemma profileCoeff_integrable (l : HeatProfile) :
    IntervalIntegrable (profileCoeff l) volume 0 (profileTime l) := by
  induction l with
  | nil => exact intervalIntegrable_const
  | cons p l ih =>
    exact patchTime_intervalIntegrable p.1.coe_nonneg (profileTime_nonneg l) intervalIntegrable_const ih

lemma SmoothTerminal.zero_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) :
    SmoothEvolution 0 (fun _ ↦ 0) (fun _ ↦ ψ) := by
  refine ⟨fun _ _ ↦ hψ,fun _ ↦ continuousOn_const,fun _ _ ↦ continuousOn_const,?_,?_,?_,?_⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := hψ.jets.bound n
    exact ⟨C,hC,fun _ _ ↦ hb⟩
  · intro n
    exact ⟨0,le_rfl,by intros; simp⟩
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp
  · intro t ht s hs x
    have ht0 : t=0 := le_antisymm ht.2 ht.1
    have hs0 : s=0 := le_antisymm hs.2 hs.1
    subst t; subst s; simp

lemma SmoothTerminal.profile_evolution {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) (l : HeatProfile) :
    SmoothEvolution (profileTime l) (profileCoeff l) (profileValue ψ l) := by
  induction l with
  | nil => exact hψ.zero_evolution
  | cons p l ih =>
    have hv : SmoothTerminal (profileValue ψ l 0) := ih.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hc := hv.constant_evolution p.2.coe_nonneg (p.1 : ℝ)
    apply hc.patch p.1.coe_nonneg (profileTime_nonneg l) ih intervalIntegrable_const (profileCoeff_integrable l)
    funext x
    simp only [sub_self,coleHopf_zero]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_StrictProfile
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma liftProfile_time (ε : ℝ≥0) (k : ℕ) (l : HeatProfile) :
    profileTime (liftProfile ε k l)=profileTime l := by
  induction l generalizing k with
  | nil => rfl
  | cons p l ih => simp only [liftProfile,profileTime,ih]

lemma liftProfile_lower (ε : ℝ≥0) (k : ℕ) {c : ℝ≥0} {l : HeatProfile}
    (h : ∀ p∈l,c≤p.2) : ∀ r∈liftProfile ε k l,c+ε*k ≤ r.2 := by
  induction l generalizing k with
  | nil => simp [liftProfile]
  | cons p l ih =>
    intro r hr
    simp only [liftProfile,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact add_le_add_left (h p (List.mem_cons_self ..)) _
    · exact (add_le_add_right (mul_le_mul_of_nonneg_left (show (k : ℝ≥0)≤(k+1 : ℕ) by exact_mod_cast (Nat.le_succ k)) (show 0≤ε from zero_le)) c).trans
        (ih (k+1) (fun p hp ↦ h p (List.mem_cons_of_mem _ hp)) r hr)

lemma liftProfile_strict {ε : ℝ≥0} (hε : 0<ε) (k : ℕ) {l : HeatProfile}
    (h : l.Pairwise (fun p r ↦ p.2 ≤ r.2)) :
    (liftProfile ε k l).Pairwise (fun p r ↦ p.2 < r.2) := by
  induction l generalizing k with
  | nil => exact List.Pairwise.nil
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp h
    apply List.pairwise_cons.mpr
    refine ⟨?_,ih (k+1) hl⟩
    intro r hr
    have hb := liftProfile_lower ε (k+1) hp r hr
    apply lt_of_lt_of_le _ hb
    apply add_lt_add_right
    exact mul_lt_mul_of_pos_left (by exact_mod_cast (Nat.lt_succ_self k)) hε

lemma liftProfile_positive {ε : ℝ≥0} (hε : 0<ε) {k : ℕ} (hk : 0<k) (l : HeatProfile) :
    ∀ r∈liftProfile ε k l,(0 : ℝ) < r.2 := by
  intro r hr
  have hh := liftProfile_lower ε k (c := 0) (fun p _ ↦ (show 0≤p.2 from zero_le)) r hr
  have hp : (0 : ℝ≥0)<ε*k := mul_pos hε (by exact_mod_cast hk)
  exact_mod_cast hp.trans_le (by simpa only [zero_add] using hh)

lemma liftProfile_coeff_lower (ε : ℝ≥0) (k : ℕ) (l : HeatProfile) (t : ℝ) :
    profileCoeff l t≤profileCoeff (liftProfile ε k l) t := by
  induction l generalizing k t with
  | nil => exact le_rfl
  | cons p l ih =>
    change patchTime _ _ _ t≤patchTime _ _ _ t
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht,patchTime_left _ _ ht]
      simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_natCast]
      exact le_add_of_nonneg_right (by positivity)
    · rw [patchTime_right _ _ (lt_of_not_ge ht),patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _ _

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_StandardGaussian
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x*gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun y : ℝ ↦ -y^2/2) (-x) x := by
    have hh := ((hasDerivAt_id x).pow 2).neg.div_const (2 : ℝ)
    simpa only [Pi.pow_def,Pi.neg_def,id_eq,pow_one,show (2 : ℕ)-1=1 from rfl,
      Nat.cast_ofNat,mul_one,neg_div,mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh
  have hd := h1.exp.const_mul ((Real.sqrt (2*Real.pi))⁻¹)
  convert hd using 1 <;> try rfl
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
  · simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    ring

lemma density_mul_integrable {f : ℝ → ℝ} (hf : Integrable f standardGaussian) :
    Integrable (fun x ↦ gaussianPDFReal 0 1 x*f x) := by
  rw [standardGaussian,gaussianReal_of_var_ne_zero _ (by norm_num)] at hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (Eventually.of_forall (fun x ↦ gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mp hf
  simpa only [toReal_gaussianPDF,smul_eq_mul] using hh

lemma standardGaussian_integrable_id : Integrable (fun x : ℝ ↦ x) standardGaussian := by
  have hh := (memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (1 : ℝ≥0∞) (by norm_num))
  exact hh.integrable (by norm_num)

lemma gaussian_stein_bounded {f f' : ℝ → ℝ} {C D : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hm : AEStronglyMeasurable f' standardGaussian)
    (hC : ∀ x, |f x|≤C) (hD : ∀ x, |f' x|≤D) :
    (∫ x, x*f x ∂standardGaussian) = ∫ x, f' x ∂standardGaussian := by
  have hfm : Continuous f := continuous_iff_continuousAt.mpr (fun x ↦ (hf x).continuousAt)
  have hfi : Integrable f standardGaussian := Integrable.of_bound hfm.aestronglyMeasurable C
    (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hC x)))
  have hf'i : Integrable f' standardGaussian := Integrable.of_bound hm D
    (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hD x)))
  have hxfi : Integrable (fun x ↦ x*f x) standardGaussian :=
    standardGaussian_integrable_id.mul_bdd hfm.aestronglyMeasurable
      (Eventually.of_forall (fun x ↦ (Real.norm_eq_abs _).trans_le (hC x)))
  have hi1 : Integrable (fun x ↦ f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert (density_mul_integrable hxfi).neg using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.neg_apply]
    ring
  have hi2 : Integrable (fun x ↦ f' x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hf'i
  have hi3 : Integrable (fun x ↦ f x*gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using density_mul_integrable hfi
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := gaussianPDFReal 0 1) (u' := f') (v' := fun x ↦ -x*gaussianPDFReal 0 1 x)
    (fun x _ ↦ hf x) (fun x _ ↦ density_hasDerivAt x) hi1 hi2 hi3
  have hb : (∫ x, f x*(-x*gaussianPDFReal 0 1 x)) =
      -(∫ x, gaussianPDFReal 0 1 x*(x*f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x ↦ by ring)
  rw [hb] at hibp
  have he : (∫ x, gaussianPDFReal 0 1 x*(x*f x)) =
      ∫ x, gaussianPDFReal 0 1 x*f' x := by
    exact neg_injective hibp |>.trans (by congr 1; funext x; ring)
  simpa only [standardGaussian,integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    smul_eq_mul] using he

lemma gaussian_coordinate_integrable {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun z : ι → ℝ ↦ z i) (gaussianProduct ι) := by
  exact ((measurePreserving_eval (fun _ : ι ↦ standardGaussian) i).integrable_comp
    standardGaussian_integrable_id.aestronglyMeasurable).mpr standardGaussian_integrable_id

lemma gaussian_pi_stein_bounded {n : ℕ} (i : Fin n) {f f' : (Fin n → ℝ) → ℝ} {C D : ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ z, HasDerivAt (fun x ↦ f (Function.update z i x)) (f' z) (z i))
    (hC : ∀ z, |f z| ≤ C) (hD : ∀ z, |f' z| ≤ D) :
    (∫ z, z i*f z ∂gaussianProduct (Fin n)) = ∫ z, f' z ∂gaussianProduct (Fin n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ ℝ) i
    have he : MeasurePreserving e.symm (standardGaussian.prod (gaussianProduct (Fin n)))
        (gaussianProduct (Fin (n+1))) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ standardGaussian) i).symm
    have hi : Integrable (fun z : Fin (n+1) → ℝ ↦ z i*f z) (gaussianProduct (Fin (n+1))) :=
      (gaussian_coordinate_integrable i).mul_bdd hf.aestronglyMeasurable
        (Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (hC z)))
    have hi' : Integrable f' (gaussianProduct (Fin (n+1))) :=
      Integrable.of_bound hf'.aestronglyMeasurable D
        (Eventually.of_forall (fun z ↦ (Real.norm_eq_abs _).trans_le (hD z)))
    have hip : Integrable (fun p ↦ e.symm p i * f (e.symm p))
        (standardGaussian.prod (gaussianProduct (Fin n))) := (he.integrable_comp hi.aestronglyMeasurable).mpr hi
    have hi'p : Integrable (fun p ↦ f' (e.symm p))
        (standardGaussian.prod (gaussianProduct (Fin n))) := (he.integrable_comp hi'.aestronglyMeasurable).mpr hi'
    rw [← he.integral_comp' (fun z ↦ z i*f z), ← he.integral_comp' f',
      integral_prod _ hip, integral_prod _ hi'p,
      integral_integral_swap (f := fun x y ↦ e.symm (x,y) i * f (e.symm (x,y))) hip,
      integral_integral_swap (f := fun x y ↦ f' (e.symm (x,y))) hi'p]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Equiv.coe_fn_mk,Fin.insertNth_apply_same]
    change (∫ x, x*f (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) ∂standardGaussian) =
      ∫ x, f' (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) ∂standardGaussian
    have hmeas : Measurable (fun x : ℝ ↦ i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y) := by
      exact e.symm.measurable.comp (measurable_id.prodMk measurable_const)
    apply gaussian_stein_bounded (f' := fun x ↦ f' (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y))
    · intro x
      simpa only [Fin.update_insertNth,Fin.insertNth_apply_same] using hd (i.insertNth (α := fun _ : Fin (n+1) ↦ ℝ) x y)
    · exact (hf'.measurable.comp hmeas).aestronglyMeasurable
    · exact fun x ↦ hC _
    · exact fun x ↦ hD _

lemma partition_pos {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) : 0 < partition x := by
  exact Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty

lemma gibbsWeight_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    0 ≤ gibbsWeight x i := le_of_lt (div_pos (Real.exp_pos _) (partition_pos x))

lemma sum_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∑ i, gibbsWeight x i = 1 := by
  simp only [gibbsWeight,← Finset.sum_div]
  change partition x / partition x = 1
  exact div_self (ne_of_gt (partition_pos x))

lemma gibbsWeight_le_one {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    gibbsWeight x i ≤ 1 := by
  calc
    _ ≤ ∑ j, gibbsWeight x j := Finset.single_le_sum (fun j _ ↦ gibbsWeight_nonneg x j) (Finset.mem_univ i)
    _ = 1 := sum_gibbsWeight x

lemma continuous_partition {ι : Type*} [Fintype ι] : Continuous (@partition ι _) := by
  unfold partition
  fun_prop

lemma continuous_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι] (i : ι) :
    Continuous (fun x : ι → ℝ ↦ gibbsWeight x i) := by
  exact (Real.continuous_exp.comp (continuous_apply i)).div continuous_partition (fun x ↦ ne_of_gt (partition_pos x))

lemma hasDerivAt_partition {ι : Type*} [Fintype ι] {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) :
    HasDerivAt (fun s ↦ partition (x s)) (∑ i, Real.exp (x t i)*v i) t := by
  simpa only [partition,Finset.sum_apply] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (h i).exp))

lemma hasDerivAt_logPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) :
    HasDerivAt (fun s ↦ logPartition (x s)) (∑ i, gibbsWeight (x t) i*v i) t := by
  convert (hasDerivAt_partition h).log (ne_of_gt (partition_pos _)) using 1 <;> try rfl
  simp only [gibbsWeight,Finset.sum_div,mul_div_assoc]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma hasDerivAt_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ℝ → ι → ℝ} {v : ι → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s ↦ x s i) (v i) t) (i : ι) :
    HasDerivAt (fun s ↦ gibbsWeight (x s) i)
      (gibbsWeight (x t) i*(v i-∑ j, gibbsWeight (x t) j*v j)) t := by
  convert (h i).exp.div (hasDerivAt_partition h) (ne_of_gt (partition_pos _)) using 1 <;> try rfl
  simp only [gibbsWeight]
  rw [show (∑ j, Real.exp (x t j)/partition (x t)*v j) =
      (∑ j, Real.exp (x t j)*v j)/partition (x t) by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro j _; ring]
  field_simp [ne_of_gt (partition_pos (x t))]

lemma abs_gibbsMean_le {ι : Type*} [Fintype ι] [Nonempty ι] (x v : ι → ℝ) {C : ℝ}
    (hC : ∀ i, |v i| ≤ C) : |∑ i, gibbsWeight x i*v i| ≤ C := by
  calc
    _ ≤ ∑ i, |gibbsWeight x i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, gibbsWeight x i*|v i| := by simp only [abs_mul,abs_of_nonneg (gibbsWeight_nonneg _ _)]
    _ ≤ ∑ i, gibbsWeight x i*C := Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (hC i) (gibbsWeight_nonneg _ _))
    _ = C := by rw [← Finset.sum_mul,sum_gibbsWeight,one_mul]

lemma continuous_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) :
    Continuous (linearProcess c) := by
  unfold linearProcess
  fun_prop

lemma hasDerivAt_linearProcess_update {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : ι → κ → ℝ) (z : κ → ℝ) (i : ι) (k : κ) :
    HasDerivAt (fun x ↦ linearProcess c (Function.update z k x) i) (c i k) (z k) := by
  have h : ∀ j, HasDerivAt (fun x ↦ c i j * Function.update z k x j)
      (if j=k then c i k else 0) (z k) := by
    intro j
    by_cases hj : j=k
    · subst j
      simpa only [Function.update_self,ite_true,mul_one,id_eq] using (hasDerivAt_id (z k)).const_mul (c i k)
    · simpa only [Function.update_of_ne hj,ite_eq_right hj] using hasDerivAt_const (z k) (c i j*z j)
  simpa only [linearProcess,Finset.sum_apply,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    using HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ h j)

lemma continuous_linear_gibbsWeight {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) : Continuous (fun z ↦ gibbsWeight (linearProcess c z) i) :=
  (continuous_gibbsWeight i).comp (continuous_linearProcess c)

lemma integrable_linear_gibbsWeight {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) : Integrable (fun z ↦ gibbsWeight (linearProcess c z) i) (gaussianProduct κ) := by
  apply Integrable.of_bound (continuous_linear_gibbsWeight c i).aestronglyMeasurable 1
  exact Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _)

lemma coordinate_gibbsWeight_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) (k : κ) :
    Integrable (fun z ↦ z k*gibbsWeight (linearProcess c z) i) (gaussianProduct κ) := by
  apply (gaussian_coordinate_integrable k).mul_bdd (continuous_linear_gibbsWeight c i).aestronglyMeasurable
  exact Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _)

lemma gaussian_coordinate_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c : ι → Fin n → ℝ) (i : ι) (k : Fin n) :
    (∫ z, z k*gibbsWeight (linearProcess c z) i ∂gaussianProduct (Fin n)) =
    ∫ z, gibbsWeight (linearProcess c z) i *
      (c i k - ∑ j, gibbsWeight (linearProcess c z) j*c j k) ∂gaussianProduct (Fin n) := by
  apply gaussian_pi_stein_bounded k (C := 1) (D := 2*∑ j, |c j k|)
  · exact continuous_linear_gibbsWeight c i
  · apply Continuous.mul (continuous_linear_gibbsWeight c i)
    apply continuous_const.sub
    exact continuous_finsetSum _ (fun j _ ↦ (continuous_linear_gibbsWeight c j).mul continuous_const)
  · intro z
    simpa only [Function.update_eq_self] using
      hasDerivAt_gibbsWeight (fun j ↦ hasDerivAt_linearProcess_update c z j k) i
  · intro z
    rw [abs_of_nonneg (gibbsWeight_nonneg _ _)]
    exact gibbsWeight_le_one _ _
  · intro z
    have hsum : ∀ j, |c j k| ≤ ∑ l, |c l k| := fun j ↦
      Finset.single_le_sum (f := fun l ↦ |c l k|) (fun l _ ↦ abs_nonneg _) (Finset.mem_univ j)
    calc
      _ = gibbsWeight (linearProcess c z) i * |c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k| := by
        rw [abs_mul,abs_of_nonneg (gibbsWeight_nonneg _ _)]
      _ ≤ |c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k| :=
        mul_le_of_le_one_left (abs_nonneg _) (gibbsWeight_le_one _ _)
      _ ≤ |c i k| + |∑ j, gibbsWeight (linearProcess c z) j*c j k| := abs_sub _ _
      _ ≤ (∑ j, |c j k|) + (∑ j, |c j k|) := add_le_add (hsum i) (abs_gibbsMean_le _ _ hsum)
      _ = _ := by ring

lemma le_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    x i ≤ logPartition x := by
  apply (Real.le_log_iff_exp_le (partition_pos x)).mpr
  exact Finset.single_le_sum (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i)

lemma logPartition_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) {C : ℝ}
    (h : ∀ i, x i ≤ C) : logPartition x ≤ Real.log (Fintype.card ι) + C := by
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  calc
    logPartition x ≤ Real.log ((Fintype.card ι : ℝ)*Real.exp C) := by
      apply Real.log_le_log (partition_pos x)
      calc
        partition x ≤ ∑ _ : ι, Real.exp C := Finset.sum_le_sum (fun i _ ↦ Real.exp_le_exp.mpr (h i))
        _ = _ := by simp
    _ = _ := by rw [Real.log_mul (ne_of_gt hc) (Real.exp_ne_zero _),Real.log_exp]

lemma abs_logPartition_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    |logPartition x| ≤ |Real.log (Fintype.card ι)| + ∑ i, |x i| := by
  have hsum : ∀ i, |x i| ≤ ∑ j, |x j| := fun i ↦
    Finset.single_le_sum (f := fun j ↦ |x j|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
  have hu := logPartition_le x (fun i ↦ (le_abs_self _).trans (hsum i))
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hl := le_logPartition x i
  have hx := neg_abs_le (x i)
  have hxi := hsum i
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log (Fintype.card ι)),abs_nonneg (Real.log (Fintype.card ι))]

lemma continuous_logPartition {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (@logPartition ι _) :=
  continuous_partition.log (fun x ↦ ne_of_gt (partition_pos x))

lemma linearProcess_integrable {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    Integrable (fun z ↦ linearProcess c z i) (gaussianProduct κ) :=
  integrable_finsetSum _ (fun k _ ↦ (gaussian_coordinate_integrable k).const_mul (c i k))

lemma logPartition_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) : Integrable (fun z ↦ logPartition (linearProcess c z)) (gaussianProduct κ) := by
  have hb := (integrable_const (|Real.log (Fintype.card ι)| : ℝ)).add
    (integrable_finsetSum Finset.univ (fun i _ ↦ (linearProcess_integrable c i).abs))
  apply hb.mono' ((continuous_logPartition.comp (continuous_linearProcess c)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_def,Pi.add_apply] using abs_logPartition_le (linearProcess c z))

lemma gibbsWeight_mul_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) (i : ι) {f : (κ → ℝ) → ℝ} (hi : Integrable f (gaussianProduct κ)) :
    Integrable (fun z ↦ gibbsWeight (linearProcess c z) i*f z) (gaussianProduct κ) := by
  simpa only [mul_comm] using hi.mul_bdd (continuous_linear_gibbsWeight c i).aestronglyMeasurable
    (Eventually.of_forall (fun z ↦ by rw [Real.norm_eq_abs,abs_of_nonneg (gibbsWeight_nonneg _ _)]; exact gibbsWeight_le_one _ _))

lemma gaussian_linear_gibbsWeight {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c d : ι → Fin n → ℝ) (i : ι) :
    (∫ z, gibbsWeight (linearProcess c z) i * linearProcess d z i ∂gaussianProduct (Fin n)) =
    ∫ z, gibbsWeight (linearProcess c z) i *
      ((∑ k, d i k*c i k) - ∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k))
        ∂gaussianProduct (Fin n) := by
  have hid : ∀ k, Integrable (fun z ↦ d i k * (z k*gibbsWeight (linearProcess c z) i))
      (gaussianProduct (Fin n)) := fun k ↦ (coordinate_gibbsWeight_integrable c i k).const_mul _
  have hic : ∀ k, Integrable (fun z ↦ d i k * (gibbsWeight (linearProcess c z) i *
      (c i k - ∑ j, gibbsWeight (linearProcess c z) j*c j k))) (gaussianProduct (Fin n)) := by
    intro k
    apply Integrable.const_mul
    apply gibbsWeight_mul_integrable
    exact (integrable_const _).sub (integrable_finsetSum Finset.univ
      (fun j _ ↦ (integrable_linear_gibbsWeight c j).mul_const _))
  calc
    _ = ∫ z, ∑ k, d i k*(z k*gibbsWeight (linearProcess c z) i) ∂gaussianProduct (Fin n) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z ↦ by simp only [linearProcess,Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring)
    _ = ∑ k, d i k * (∫ z, z k*gibbsWeight (linearProcess c z) i ∂gaussianProduct (Fin n)) := by
      rw [integral_finsetSum Finset.univ (fun k _ ↦ hid k)]
      simp only [integral_const_mul]
    _ = ∑ k, d i k * (∫ z, gibbsWeight (linearProcess c z) i *
        (c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k) ∂gaussianProduct (Fin n)) := by
      simp only [gaussian_coordinate_gibbsWeight]
    _ = ∫ z, ∑ k, d i k * (gibbsWeight (linearProcess c z) i *
        (c i k-∑ j, gibbsWeight (linearProcess c z) j*c j k)) ∂gaussianProduct (Fin n) := by
      rw [integral_finsetSum Finset.univ (fun k _ ↦ hic k)]
      simp only [integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl; intro k _; ring
      · rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro k _; ring

lemma weighted_covariance_pairs {ι : Type*} [Fintype ι] (p : ι → ℝ) (D : ι → ι → ℝ)
    (hp : ∑ i, p i = 1) :
    ∑ i, p i*(D i i-∑ j, p j*D i j) =
    (1/2 : ℝ)*∑ i, ∑ j, p i*p j*(D i i+D j j-D i j-D j i) := by
  have h1 : (∑ i, ∑ j, p i*p j*D i i) = ∑ i, p i*D i i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = p i*D i i*∑ j, p j := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ = _ := by rw [hp,mul_one]
  have h2 : (∑ i, ∑ j, p i*p j*D j j) = ∑ j, p j*D j j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (∑ i, p i)*(p j*D j j) := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      _ = _ := by rw [hp,one_mul]
  have h3 : (∑ i, ∑ j, p i*p j*D j i) = ∑ i, ∑ j, p i*p j*D i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  have hl : (∑ i, p i*(D i i-∑ j, p j*D i j)) =
      (∑ i, p i*D i i) - ∑ i, ∑ j, p i*p j*D i j := by
    simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc]
  have hr : (∑ i, ∑ j, p i*p j*(D i i+D j j-D i j-D j i)) =
      2*(∑ i, p i*D i i)-2*(∑ i, ∑ j, p i*p j*D i j) := by
    simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [h1,h2,h3]
    ring
  rw [hl,hr]
  ring

end SKValueG
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RotatedCoefficients
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma gaussian_gibbs_derivative_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (c d : ι → Fin n → ℝ)
    (h : ∀ i j, 0 ≤ ∑ k, (d i k-d j k)*(c i k-c j k)) :
    0 ≤ ∫ z, ∑ i, gibbsWeight (linearProcess c z) i*linearProcess d z i ∂gaussianProduct (Fin n) := by
  have hi : ∀ i, Integrable (fun z ↦ gibbsWeight (linearProcess c z) i*linearProcess d z i)
      (gaussianProduct (Fin n)) := fun i ↦ gibbsWeight_mul_integrable c i (linearProcess_integrable d i)
  have hi' : ∀ i, Integrable (fun z ↦ gibbsWeight (linearProcess c z) i *
      ((∑ k, d i k*c i k)-∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k)))
      (gaussianProduct (Fin n)) := by
    intro i
    apply gibbsWeight_mul_integrable
    exact (integrable_const _).sub (integrable_finsetSum _ (fun j _ ↦ (integrable_linear_gibbsWeight c j).mul_const _))
  rw [integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [gaussian_linear_gibbsWeight]
  rw [← integral_finsetSum _ (fun i _ ↦ hi' i)]
  apply integral_nonneg
  intro z
  change (0 : ℝ) ≤ ∑ i, gibbsWeight (linearProcess c z) i *
    ((∑ k, d i k*c i k)-∑ j, gibbsWeight (linearProcess c z) j*(∑ k, d i k*c j k))
  rw [weighted_covariance_pairs _ (fun i j ↦ ∑ k, d i k*c j k) (sum_gibbsWeight (linearProcess c z))]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (mul_nonneg (gibbsWeight_nonneg _ _) (gibbsWeight_nonneg _ _))
  have he : (∑ k, d i k*c i k)+(∑ k, d j k*c j k)-
      (∑ k, d i k*c j k)-(∑ k, d j k*c i k) = ∑ k, (d i k-d j k)*(c i k-c j k) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  exact h i j

lemma hasDerivAt_rotatedProcess {ι κ : Type*} [Fintype κ] (a b : ι → κ → ℝ)
    (t : ℝ) (z : κ → ℝ) (i : ι) :
    HasDerivAt (fun s ↦ linearProcess (rotatedCoefficients a b s) z i)
      (linearProcess (rotationVelocity a b t) z i) t := by
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun k _ ↦
    (((Real.hasDerivAt_cos t).mul_const (a i k)).add ((Real.hasDerivAt_sin t).mul_const (b i k))).mul_const (z k))

lemma abs_rotationVelocity_le {ι κ : Type*} (a b : ι → κ → ℝ) (t : ℝ) (i : ι) (k : κ) :
    |rotationVelocity a b t i k| ≤ |a i k|+|b i k| := by
  calc
    _ ≤ |-Real.sin t*a i k| + |Real.cos t*b i k| := abs_add_le _ _
    _ = |Real.sin t| *|a i k| + |Real.cos t| *|b i k| := by rw [abs_mul,abs_neg,abs_mul]
    _ ≤ 1*|a i k| + 1*|b i k| := add_le_add
      (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one t) (abs_nonneg _))
    _ = _ := by ring

lemma rotation_derivative_bound {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (a b : ι → κ → ℝ) (t : ℝ) (z : κ → ℝ) :
    |∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
        linearProcess (rotationVelocity a b t) z i| ≤
      ∑ i, ∑ k, (|a i k|+|b i k|)*|z k| := by
  apply abs_gibbsMean_le
  intro i
  calc
    _ ≤ ∑ k, |rotationVelocity a b t i k*z k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, (|a i k|+|b i k|)*|z k| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_rotationVelocity_le _ _ _ _ _) (abs_nonneg _)
    _ ≤ _ := Finset.single_le_sum (f := fun j ↦ ∑ k, (|a j k|+|b j k|)*|z k|) (fun j _ ↦ Finset.sum_nonneg (fun k _ ↦ mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))) (Finset.mem_univ i)

lemma hasDerivAt_expected_rotated_logPartition {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ ∫ z, logPartition (linearProcess (rotatedCoefficients a b s) z) ∂gaussianProduct (Fin n))
      (∫ z, ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
        linearProcess (rotationVelocity a b t) z i ∂gaussianProduct (Fin n)) t := by
  have hb : Integrable (fun z : Fin n → ℝ ↦ ∑ i, ∑ k, (|a i k|+|b i k|)*|z k|)
      (gaussianProduct (Fin n)) :=
    integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun k _ ↦
      (gaussian_coordinate_integrable k).abs.const_mul _))
  have hmc : Continuous (fun z : Fin n → ℝ ↦ ∑ i,
      gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
      linearProcess (rotationVelocity a b t) z i) := by
    apply continuous_finsetSum
    intro i _
    apply (continuous_linear_gibbsWeight _ _).mul
    exact (continuous_apply i).comp (continuous_linearProcess _)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ) (μ := gaussianProduct (Fin n))
    (F := fun s z ↦ logPartition (linearProcess (rotatedCoefficients a b s) z))
    (F' := fun s z ↦ ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b s) z) i *
      linearProcess (rotationVelocity a b s) z i)
    (bound := fun z ↦ ∑ i, ∑ k, (|a i k|+|b i k|)*|z k|)
    (Filter.univ_mem)
    (Eventually.of_forall (fun s ↦ (continuous_logPartition.comp (continuous_linearProcess _)).aestronglyMeasurable))
    (logPartition_integrable _) hmc.aestronglyMeasurable
    (Eventually.of_forall (fun z s _ ↦ by simpa only [Real.norm_eq_abs] using rotation_derivative_bound a b s z)) hb
    (Eventually.of_forall (fun z s _ ↦ hasDerivAt_logPartition (hasDerivAt_rotatedProcess a b s z)))).2

lemma rotation_pair_covariance {ι κ : Type*} [Fintype κ] (a b : ι → κ → ℝ) (t : ℝ) (i j : ι) :
    (∑ k, (rotationVelocity a b t i k-rotationVelocity a b t j k)*
      (rotatedCoefficients a b t i k-rotatedCoefficients a b t j k)) =
    Real.sin t*Real.cos t*((∑ k, (b i k-b j k)^2)-(∑ k, (a i k-a j k)^2)) +
      ((Real.cos t)^2-(Real.sin t)^2)*∑ k, (a i k-a j k)*(b i k-b j k) := by
  simp only [rotationVelocity,rotatedCoefficients,← Finset.sum_sub_distrib,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma expected_logPartition_le_of_pair_distances {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (a b : ι → Fin n → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct (Fin n)) ≤
    ∫ z, logPartition (linearProcess b z) ∂gaussianProduct (Fin n) := by
  let F := fun t ↦ ∫ z, logPartition (linearProcess (rotatedCoefficients a b t) z) ∂gaussianProduct (Fin n)
  have hd : ∀ t, HasDerivAt F (∫ z, ∑ i, gibbsWeight (linearProcess (rotatedCoefficients a b t) z) i *
      linearProcess (rotationVelocity a b t) z i ∂gaussianProduct (Fin n)) t :=
    hasDerivAt_expected_rotated_logPartition a b
  have hc : Continuous F := continuous_iff_continuousAt.mpr (fun t ↦ (hd t).continuousAt)
  have hm : MonotoneOn F (Icc (0 : ℝ) (Real.pi/2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc.continuousOn
      (fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (Real.pi/2) := interior_subset ht
    rw [(hd t).deriv]
    apply gaussian_gibbs_derivative_nonneg
    intro i j
    rw [rotation_pair_covariance,horth,mul_zero,add_zero]
    exact mul_nonneg (mul_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi ht'.1 (ht'.2.trans (by linarith [Real.pi_pos])))
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, ht'.1],ht'.2⟩)) (sub_nonneg.mpr (hdist i j))
  have hπ : (0 : ℝ) ≤ Real.pi/2 := by positivity
  have hh := hm ⟨le_rfl,hπ⟩ ⟨hπ,le_rfl⟩ hπ
  have ha0 : rotatedCoefficients a b 0 = a := by funext i k; simp [rotatedCoefficients]
  have hb0 : rotatedCoefficients a b (Real.pi/2) = b := by funext i k; simp [rotatedCoefficients]
  simpa only [F,ha0,hb0] using hh

lemma le_finiteMaximum {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : x i ≤ finiteMaximum x :=
  le_csSup (Set.finite_range x).bddAbove (Set.mem_range_self i)

lemma exists_finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∃ i, x i = finiteMaximum x := (Set.range_nonempty x).csSup_mem (Set.finite_range x)

lemma continuous_finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (@finiteMaximum ι) := by
  have he (x : ι → ℝ) : finiteMaximum x = Finset.univ.sup' Finset.univ_nonempty x := by
    rw [Finset.sup'_eq_csSup_image]
    simp only [Finset.coe_univ,Set.image_univ,finiteMaximum]
  simp_rw [funext he]
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ ↦ continuous_apply i)

lemma abs_finiteMaximum_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    |finiteMaximum x| ≤ ∑ i, |x i| := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  rw [← hi]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (x j)) (Finset.mem_univ i)

lemma finiteMaximum_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) : Integrable (fun z ↦ finiteMaximum (linearProcess c z)) (gaussianProduct κ) := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ (linearProcess_integrable c i).abs)).mono'
    ((continuous_finiteMaximum.comp (continuous_linearProcess c)).aestronglyMeasurable)
  exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs,Function.comp_def] using abs_finiteMaximum_le (linearProcess c z))

lemma linearProcess_scaled {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (β : ℝ) (z : κ → ℝ) :
    linearProcess (fun i k ↦ β*c i k) z = fun i ↦ β*linearProcess c z i := by
  funext i
  simp only [linearProcess,Finset.mul_sum,mul_assoc]

lemma gaussian_integral_reindex {κ ν : Type*} [Fintype κ] [Fintype ν] (e : κ ≃ ν)
    (f : (κ → ℝ) → ℝ) :
    (∫ z : ν → ℝ, f (fun k ↦ z (e k)) ∂gaussianProduct ν) = ∫ z, f z ∂gaussianProduct κ := by
  have he := measurePreserving_piCongrLeft (α := fun _ : κ ↦ ℝ)
    (fun _ : κ ↦ standardGaussian) e.symm
  have hf (z : ν → ℝ) : (MeasurableEquiv.piCongrLeft (π := fun _ : κ ↦ ℝ) e.symm) z = fun k ↦ z (e k) := by
    funext k
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simpa only [gaussianProduct,hf] using he.integral_comp' f

lemma linearProcess_reindex {ι κ ν : Type*} [Fintype κ] [Fintype ν]
    (c : ι → κ → ℝ) (e : κ ≃ ν) (z : ν → ℝ) :
    linearProcess c (fun k ↦ z (e k)) = linearProcess (fun i l ↦ c i (e.symm l)) z := by
  funext i
  simpa only [linearProcess, Equiv.symm_apply_apply] using e.sum_comp (fun l ↦ c i (e.symm l)*z l)

lemma spin_sq (b : Bool) : spin b ^ 2 = 1 := by cases b <;> norm_num [spin]
lemma abs_spin (b : Bool) : |spin b| = 1 := by cases b <;> norm_num [spin]

lemma twice_upper_sum {ι : Type*} [Fintype ι] [LinearOrder ι] (f : ι → ι → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    2*(∑ i, ∑ j, if i < j then f i j else 0) = ∑ i, ∑ j, f i j := by
  have hs : (∑ i, ∑ j, if j < i then f i j else 0) = ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have hsplit (i j : ι) : f i j = (if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_ge h.le]
    · subst j; simp [hdiag]
    · simp [h,not_lt_of_ge h.le]
  conv_rhs => arg 2; ext i; arg 2; ext j; rw [hsplit i j]
  simp only [Finset.sum_add_distrib,hs]
  ring

lemma spin_pair_difference {dimension : ℕ} (σ τ : Fin dimension → Bool) (i j : Fin dimension) :
    (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 =
      2-2*(spin (σ i)*spin (τ i))*(spin (σ j)*spin (τ j)) := by
  have h1 := spin_sq (σ i)
  have h2 := spin_sq (σ j)
  have h3 := spin_sq (τ i)
  have h4 := spin_sq (τ j)
  calc
    _ = (spin (σ i))^2*(spin (σ j))^2+(spin (τ i))^2*(spin (τ j))^2 -
      2*(spin (σ i)*spin (τ i))*(spin (σ j)*spin (τ j)) := by ring
    _ = _ := by rw [h1,h2,h3,h4]; ring

end SKValueG
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_BlockCoeff
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma hamCoeff_distance {n : ℕ} (hn : 0 < n) (σ τ : Fin n → Bool) :
    (∑ k, (hamCoeff n σ k-hamCoeff n τ k)^2) =
    (n : ℝ) - (∑ i, spin (σ i)*spin (τ i))^2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt := Real.sq_sqrt hn'.le
  have hn0 := ne_of_gt hn'
  have hs0 := Real.sqrt_ne_zero'.mpr hn'
  have hu := twice_upper_sum (fun i j ↦ (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2)
    (fun i j ↦ by ring) (fun i ↦ by rw [← sq,← sq,spin_sq,spin_sq]; norm_num)
  have he : (∑ i, ∑ j, (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2) =
      2*(n : ℝ)^2 - 2*(∑ i, spin (σ i)*spin (τ i))^2 := by
    simp_rw [spin_pair_difference,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum,← Finset.sum_mul]
    ring
  have hc : (∑ k, (hamCoeff n σ k-hamCoeff n τ k)^2) =
      (Real.sqrt (n : ℝ))⁻¹^2 *
      ∑ i, ∑ j, if i < j then (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 else 0 := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum,hamCoeff]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hc,inv_pow,hsqrt]
  rw [he] at hu
  have ht : (∑ i, ∑ j, if i < j then (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 else 0) =
      (n : ℝ)^2 - (∑ i, spin (σ i)*spin (τ i))^2 := by linarith
  rw [ht]
  field_simp

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_LogComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma expected_logPartition_reindex {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    [Fintype ν] (e : κ ≃ ν) (a : ι → κ → ℝ) :
    (∫ z, logPartition (linearProcess (fun i k ↦ a i (e.symm k)) z)
      ∂gaussianProduct ν) = ∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ := by
  simpa only [linearProcess_reindex] using gaussian_integral_reindex e
    (fun z ↦ logPartition (linearProcess a z))

lemma expected_logPartition_le_orthogonal {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ι → κ → ℝ)
    (horth : ∀ i j, (∑ k, (a i k-a j k)*(b i k-b j k)) = 0)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ) ≤
      ∫ z, logPartition (linearProcess b z) ∂gaussianProduct κ := by
  let e := Fintype.equivFin κ
  have h := expected_logPartition_le_of_pair_distances
    (fun i k ↦ a i (e.symm k)) (fun i k ↦ b i (e.symm k))
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)*(b i k-b j k))]
      exact horth i j)
    (fun i j ↦ by
      rw [e.symm.sum_comp (fun k ↦ (a i k-a j k)^2),
        e.symm.sum_comp (fun k ↦ (b i k-b j k)^2)]
      exact hdist i j)
  simpa only [expected_logPartition_reindex] using h

lemma expected_logPartition_embedLeft {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) :
    (∫ z, logPartition (linearProcess (embedLeft (ν := ν) a) z) ∂gaussianProduct (κ ⊕ ν)) =
      ∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, logPartition (linearProcess (embedLeft a) z)
    ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ logPartition (linearProcess (embedLeft a) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedLeft a) ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : κ ⊕ ν ↦ ℝ)).symm p) = linearProcess a p.1 := by
    funext i
    simp [linearProcess,embedLeft,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_fst (μ := gaussianProduct κ)
    (ν := gaussianProduct ν) (fun z ↦ logPartition (linearProcess a z))

lemma expected_logPartition_embedRight {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (b : ι → ν → ℝ) :
    (∫ z, logPartition (linearProcess (embedRight (κ := κ) b) z) ∂gaussianProduct (κ ⊕ ν)) =
      ∫ z, logPartition (linearProcess b z) ∂gaussianProduct ν := by
  have he := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ ν ↦ standardGaussian)
  change (∫ z, logPartition (linearProcess (embedRight b) z)
    ∂Measure.pi (fun _ : κ ⊕ ν ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun z ↦ logPartition (linearProcess (embedRight b) z))]
  have hlin (p : (κ → ℝ) × (ν → ℝ)) :
      linearProcess (embedRight b) ((MeasurableEquiv.sumPiEquivProdPi
        (fun _ : κ ⊕ ν ↦ ℝ)).symm p) = linearProcess b p.2 := by
    funext i
    simp [linearProcess,embedRight,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin]
  simpa [gaussianProduct] using integral_fun_snd (μ := gaussianProduct κ)
    (ν := gaussianProduct ν) (fun z ↦ logPartition (linearProcess b z))

lemma expected_logPartition_le {ι κ ν : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) (b : ι → ν → ℝ)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, logPartition (linearProcess a z) ∂gaussianProduct κ) ≤
      ∫ z, logPartition (linearProcess b z) ∂gaussianProduct ν := by
  have h := expected_logPartition_le_orthogonal
    (embedLeft (ν := ν) a) (embedRight (κ := κ) b)
    (fun i j ↦ by simp [embedLeft,embedRight,Fintype.sum_sum_type])
    (fun i j ↦ by simpa only [Fintype.sum_sum_type,embedLeft,embedRight,
      Sum.elim_inl,Sum.elim_inr,sub_self,zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero,zero_add,add_zero] using hdist i j)
  simpa only [expected_logPartition_embedLeft,expected_logPartition_embedRight] using h

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma finiteMaximum_add_const {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (c : ℝ) : finiteMaximum (fun i ↦ x i+c)=finiteMaximum x+c := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum x
  obtain ⟨j,hj⟩ := exists_finiteMaximum (fun i ↦ x i+c)
  apply le_antisymm
  · rw [← hj]
    linarith [le_finiteMaximum x j]
  · rw [← hi]
    exact le_finiteMaximum (fun i ↦ x i+c) i

lemma affineMaximum_integrable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (a : ι → κ → ℝ) (d : ι → ℝ) :
    Integrable (fun z ↦ finiteMaximum (fun i ↦ linearProcess a z i+d i)) (gaussianProduct κ) := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦
    ((linearProcess_integrable a i).add (integrable_const (d i))).abs)).mono'
  · exact (continuous_finiteMaximum.comp ((continuous_linearProcess a).add continuous_const)).aestronglyMeasurable
  · exact Eventually.of_forall (fun z ↦ by
      simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_finiteMaximum_le
        (fun i ↦ linearProcess a z i + d i))

lemma replicated_partition_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (x d : ι → ℝ) (β : ℝ) (hβ : 0≤β) (m : ι → ℕ)
    (hl : ∀ i, Real.exp (β*d i) ≤ (m i : ℝ))
    (hu : ∀ i, (m i : ℝ) ≤ 2*Real.exp (β*d i)) :
    β*finiteMaximum (fun i ↦ x i+d i) ≤
        logPartition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) ∧
      logPartition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) ≤
        β*finiteMaximum (fun i ↦ x i+d i)+Real.log (2*(Fintype.card ι : ℝ)) := by
  have hp : partition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) =
      ∑ i, (m i : ℝ)*Real.exp (β*x i) := by
    simp [partition,Fintype.sum_sigma]
  have hlo : Real.exp (β*finiteMaximum (fun i ↦ x i+d i)) ≤
      partition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) := by
    obtain ⟨i,hi⟩ := exists_finiteMaximum (fun i ↦ x i+d i)
    rw [← hi,hp]
    calc
      _ = Real.exp (β*d i)*Real.exp (β*x i) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ (m i : ℝ)*Real.exp (β*x i) := mul_le_mul_of_nonneg_right (hl i) (Real.exp_pos _).le
      _ ≤ _ := Finset.single_le_sum (f := fun j ↦ (m j : ℝ)*Real.exp (β*x j)) (fun j _ ↦ by positivity) (Finset.mem_univ i)
  have hup : partition (fun i : (Σ i, Fin (m i)) ↦ β*x i.1) ≤
      2*(Fintype.card ι : ℝ)*Real.exp (β*finiteMaximum (fun i ↦ x i+d i)) := by
    rw [hp]
    calc
      _ ≤ ∑ i : ι, 2*Real.exp (β*finiteMaximum (fun i ↦ x i+d i)) := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ 2*Real.exp (β*d i)*Real.exp (β*x i) :=
            mul_le_mul_of_nonneg_right (hu i) (Real.exp_pos _).le
          _ = 2*Real.exp (β*(x i+d i)) := by rw [mul_assoc,←Real.exp_add]; congr 2; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_finiteMaximum (fun i ↦ x i+d i) i) hβ)) (by norm_num)
      _ = _ := by simp; ring
  refine ⟨?_,?_⟩
  · simpa only [Real.log_exp,logPartition] using Real.log_le_log (Real.exp_pos _) hlo
  · have hc : 0<2*(Fintype.card ι : ℝ) := by positivity
    have hh := Real.log_le_log ((Real.exp_pos _).trans_le hlo) hup
    simpa only [logPartition,Real.log_mul hc.ne' (Real.exp_pos _).ne',
      Real.log_exp,add_comm] using hh

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_AffineComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

theorem expected_affine_max_le {ι κ ν : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype ν]
    (a : ι → κ → ℝ) (b : ι → ν → ℝ) (d : ι → ℝ)
    (hdist : ∀ i j, (∑ k, (a i k-a j k)^2) ≤ ∑ k, (b i k-b j k)^2) :
    (∫ z, finiteMaximum (fun i ↦ linearProcess a z i+d i) ∂gaussianProduct κ) ≤
      ∫ z, finiteMaximum (fun i ↦ linearProcess b z i+d i) ∂gaussianProduct ν := by
  classical
  let A := fun z ↦ finiteMaximum (fun i ↦ linearProcess a z i+d i)
  let B := fun z ↦ finiteMaximum (fun i ↦ linearProcess b z i+d i)
  have hiA : Integrable A (gaussianProduct κ) := affineMaximum_integrable a d
  have hiB : Integrable B (gaussianProduct ν) := affineMaximum_integrable b d
  let C := ∑ i, |d i|
  have hC (i : ι) : 0 ≤ d i+C := by
    have h := Finset.single_le_sum (fun j _ ↦ abs_nonneg (d j)) (Finset.mem_univ i)
    have hh := neg_abs_le (d i)
    dsimp [C]
    linarith
  let L := Real.log (2*(Fintype.card ι : ℝ))
  have hβbound (β : ℝ) (hβ : 0 ≤ β) :
      β*(∫ z, A z ∂gaussianProduct κ) ≤ β*(∫ z, B z ∂gaussianProduct ν)+L := by
    let m : ι → ℕ := fun i ↦ ⌈Real.exp (β*(d i+C))⌉₊
    have hm (i : ι) : 0 < m i := Nat.ceil_pos.mpr (Real.exp_pos _)
    let : Nonempty (Σ i, Fin (m i)) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty ι),⟨0,hm _⟩⟩⟩
    have hl (i : ι) : Real.exp (β*(d i+C)) ≤ (m i : ℝ) := Nat.le_ceil _
    have hu (i : ι) : (m i : ℝ) ≤ 2*Real.exp (β*(d i+C)) := by
      have he : 1 ≤ Real.exp (β*(d i+C)) := Real.one_le_exp_iff.mpr (mul_nonneg hβ (hC i))
      have hh := Nat.ceil_lt_add_one (Real.exp_pos (β*(d i+C))).le
      dsimp [m]
      linarith
    let a' : (Σ i, Fin (m i)) → κ → ℝ := fun i k ↦ β*a i.1 k
    let b' : (Σ i, Fin (m i)) → ν → ℝ := fun i k ↦ β*b i.1 k
    have hcomp := expected_logPartition_le a' b' (fun i j ↦ by
      have heA : (∑ k, (β*a i.1 k-β*a j.1 k)^2) =
          β^2*∑ k, (a i.1 k-a j.1 k)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      have heB : (∑ k, (β*b i.1 k-β*b j.1 k)^2) =
          β^2*∑ k, (b i.1 k-b j.1 k)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      dsimp [a',b']
      rw [heA,heB]
      exact mul_le_mul_of_nonneg_left (hdist i.1 j.1) (sq_nonneg β))
    have hAi := logPartition_integrable a'
    have hBi := logPartition_integrable b'
    have hlow (z : κ → ℝ) : β*(A z+C) ≤ logPartition (linearProcess a' z) := by
      have h := (replicated_partition_bounds (linearProcess a z)
        (fun i ↦ d i+C) β hβ m hl hu).1
      have he : (fun i ↦ linearProcess a z i+(d i+C)) =
          (fun i ↦ (linearProcess a z i+d i)+C) := by funext i; ring
      rw [he,finiteMaximum_add_const] at h
      simpa only [A,a',linearProcess_scaled,linearProcess] using h
    have hupp (z : ν → ℝ) : logPartition (linearProcess b' z) ≤ β*(B z+C)+L := by
      have h := (replicated_partition_bounds (linearProcess b z)
        (fun i ↦ d i+C) β hβ m hl hu).2
      have he : (fun i ↦ linearProcess b z i+(d i+C)) =
          (fun i ↦ (linearProcess b z i+d i)+C) := by funext i; ring
      rw [he,finiteMaximum_add_const] at h
      simpa only [B,b',linearProcess_scaled,linearProcess,L] using h
    have h1 := integral_mono ((hiA.add (integrable_const C)).const_mul β) hAi hlow
    have h2 := integral_mono hBi
      (((hiB.add (integrable_const C)).const_mul β).add (integrable_const L)) hupp
    have h := h1.trans (hcomp.trans h2)
    simp only [Pi.add_apply] at h
    rw [integral_const_mul,integral_add hiA (integrable_const C),integral_const] at h
    have hiB' : Integrable (fun z ↦ β*(B z+C)) (gaussianProduct ν) :=
      (hiB.add (integrable_const C)).const_mul β
    rw [integral_add hiB' (integrable_const L),
      integral_const_mul,integral_add hiB (integrable_const C),integral_const,integral_const] at h
    simp only [probReal_univ,one_smul] at h
    linarith
  by_contra hh
  have hΔ : 0 < (∫ z, A z ∂gaussianProduct κ)-(∫ z, B z ∂gaussianProduct ν) :=
    sub_pos.mpr (lt_of_not_ge hh)
  let Δ := (∫ z, A z ∂gaussianProduct κ)-(∫ z, B z ∂gaussianProduct ν)
  let β := (|L|+1)/Δ
  have hb : 0<β := div_pos (by positivity) hΔ
  have h := hβbound β hb.le
  have he : β*Δ=|L|+1 := div_mul_cancel₀ _ hΔ.ne'
  have hl := le_abs_self L
  dsimp [Δ] at he
  nlinarith

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma product_inner_sum {κ ν : Type*} [Fintype κ] [Fintype ν]
    (x y : κ → ℝ) (u v : ν → ℝ) :
    (∑ k : κ×ν, (x k.1*u k.2)*(y k.1*v k.2)) =
      (∑ k, x k*y k)*(∑ k, u k*v k) := by
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sq_distance_sum {κ : Type*} [Fintype κ] (x y : κ → ℝ) :
    (∑ k, (x k-y k)^2) = (∑ k, x k^2)+(∑ k, y k^2)-2*(∑ k, x k*y k) := by
  simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma leafField_inner {Λ κ : Type*} [Fintype κ] (n : ℕ) (v : Λ → κ → ℝ)
    (p q : (Fin n → Bool)×Λ) :
    (∑ k, leafFieldCoeff n v p k*leafFieldCoeff n v q k) =
      (∑ i, spin (p.1 i)*spin (q.1 i))*(∑ k, v p.2 k*v q.2 k) :=
  product_inner_sum (fun i ↦ spin (p.1 i)) (fun i ↦ spin (q.1 i)) (v p.2) (v q.2)

lemma leafField_sq {Λ κ : Type*} [Fintype κ] (n : ℕ) (v : Λ → κ → ℝ)
    (hv : ∀ α, ∑ k, (v α k)^2=1) (p : (Fin n → Bool)×Λ) :
    (∑ k, (leafFieldCoeff n v p k)^2)=(n : ℝ) := by
  simp_rw [sq]
  rw [leafField_inner]
  simp only [←sq,spin_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,hv]

lemma leafAux_inner {Λ κ : Type*} [Fintype κ] (n : ℕ) (v : Λ → κ → ℝ)
    (α β : Λ) :
    (∑ k, leafAuxCoeff n v α k*leafAuxCoeff n v β k) =
      ((n : ℝ)/2)*(∑ k, v α k*v β k)^2 := by
  have hp := product_inner_sum (v α) (v β) (v α) (v β)
  calc
    _ = (Real.sqrt ((n : ℝ)/2))^2 *
        (∑ k : κ×κ, (v α k.1*v α k.2)*(v β k.1*v β k.2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [leafAuxCoeff]
      ring
    _ = _ := by rw [Real.sq_sqrt (by positivity),hp]; ring

lemma leafAux_sq {Λ κ : Type*} [Fintype κ] (n : ℕ) (v : Λ → κ → ℝ)
    (hv : ∀ α, ∑ k, (v α k)^2=1) (α : Λ) :
    (∑ k, (leafAuxCoeff n v α k)^2)=(n : ℝ)/2 := by
  simp_rw [sq]
  rw [leafAux_inner]
  simp only [←sq,hv,one_pow,mul_one]

theorem guerra_metric_remainder {Λ κ : Type*} [Fintype κ] {n : ℕ}
    (hn : 0<n) (v : Λ → κ → ℝ) (hv : ∀ α, ∑ k, (v α k)^2=1)
    (p q : (Fin n → Bool)×Λ) :
    (∑ k, (leafFieldCoeff n v p k-leafFieldCoeff n v q k)^2)-
      (∑ k, (guerraCoeff n v p k-guerraCoeff n v q k)^2) =
      (n : ℝ)*((∑ i, spin (p.1 i)*spin (q.1 i))/(n : ℝ)-
        (∑ k, v p.2 k*v q.2 k))^2 := by
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  rw [Fintype.sum_sum_type]
  simp only [guerraCoeff,Sum.elim_inl,Sum.elim_inr]
  rw [hamCoeff_distance hn,sq_distance_sum (leafFieldCoeff n v p),
    leafField_sq n v hv,leafField_sq n v hv,leafField_inner,
    sq_distance_sum (leafAuxCoeff n v p.2),leafAux_sq n v hv,
    leafAux_sq n v hv,leafAux_inner]
  field_simp
  ring

lemma guerra_metric_le {Λ κ : Type*} [Fintype κ] {n : ℕ}
    (hn : 0<n) (v : Λ → κ → ℝ) (hv : ∀ α, ∑ k, (v α k)^2=1)
    (p q : (Fin n → Bool)×Λ) :
    (∑ k, (guerraCoeff n v p k-guerraCoeff n v q k)^2) ≤
      ∑ k, (leafFieldCoeff n v p k-leafFieldCoeff n v q k)^2 := by
  have h := guerra_metric_remainder hn v hv p q
  have hs : 0 ≤ (n : ℝ)*((∑ i, spin (p.1 i)*spin (q.1 i))/(n : ℝ)-
      (∑ k, v p.2 k*v q.2 k))^2 := by positivity
  linarith

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_ExponentialMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace SKValueG

lemma exp_one_density_real (x : ℝ) :
    (gammaPDF 1 1 x).toReal = if 0 ≤ x then Real.exp (-x) else 0 := by
  simp only [gammaPDF,gammaPDFReal,Real.Gamma_one,Real.one_rpow,div_one,
    sub_self,Real.rpow_zero,mul_one,one_mul]
  rw [ENNReal.toReal_ofReal]
  split_ifs <;> positivity

lemma exp_one_pos_ae : ∀ᵐ x ∂expMeasure 1, 0<x := by
  have h : (expMeasure 1) (Iic 0)=0 := by
    have hc := cdf_expMeasure_eq (show (0 : ℝ)<1 by norm_num) 0
    rw [cdf_eq_real] at hc
    simpa [measureReal_def,ENNReal.toReal_eq_zero_iff,measure_ne_top] using hc
  rw [ae_iff]
  simpa only [not_lt, Iic] using h

lemma exp_one_integrable_iff (f : ℝ → ℝ) :
    Integrable f (expMeasure 1) ↔
      IntegrableOn (fun x ↦ Real.exp (-x)*f x) (Ioi 0) := by
  unfold expMeasure gammaMeasure
  rw [integrable_withDensity_iff_integrable_smul'
    (by unfold gammaPDF; fun_prop) (Eventually.of_forall (fun x ↦ by simp [gammaPDF]))]
  simp only [exp_one_density_real,smul_eq_mul]
  have he : (fun x ↦ (if 0 ≤ x then Real.exp (-x) else 0)*f x)=
      (Ici 0).indicator (fun x ↦ Real.exp (-x)*f x) := by
    ext x; by_cases h : 0≤x <;> simp [h]
  rw [he,integrable_indicator_iff measurableSet_Ici]
  exact integrableOn_Ici_iff_integrableOn_Ioi

lemma exp_one_rpow_integrable {p : ℝ} (hp : -1<p) :
    Integrable (fun x : ℝ ↦ x^p) (expMeasure 1) := by
  apply (exp_one_integrable_iff _).mpr
  have h := Real.GammaIntegral_convergent (s := p+1) (by linarith)
  simpa only [add_sub_cancel_right] using h

lemma abs_log_le_two_rpow {x : ℝ} (hx : 0<x) :
    |Real.log x| ≤ 2*(x^(1/2 : ℝ)+x^(-1/2 : ℝ)) := by
  have h1 := Real.log_le_rpow_div hx.le (show (0 : ℝ)<1/2 by norm_num)
  have h2 := Real.log_le_rpow_div (inv_nonneg.mpr hx.le) (show (0 : ℝ)<1/2 by norm_num)
  rw [Real.log_inv,Real.inv_rpow hx.le] at h2
  have he : (x^(1/2 : ℝ))⁻¹=x^(-1/2 : ℝ) := by
    rw [show (-1/2 : ℝ)=-(1/2 : ℝ) by ring,Real.rpow_neg hx.le]
  rw [he] at h2
  have hp1 := Real.rpow_nonneg hx.le (1/2 : ℝ)
  have hp2 := Real.rpow_nonneg hx.le (-1/2 : ℝ)
  apply abs_le.mpr
  constructor <;> linarith

lemma exp_one_log_integrable : Integrable Real.log (expMeasure 1) := by
  have h := ((exp_one_rpow_integrable (p := (1/2 : ℝ)) (by norm_num)).add
    (exp_one_rpow_integrable (p := (-1/2 : ℝ)) (by norm_num))).const_mul 2
  apply h.mono' Real.measurable_log.aestronglyMeasurable
  exact exp_one_pos_ae.mono (fun x hx ↦ by simpa only [Real.norm_eq_abs,Pi.add_apply] using abs_log_le_two_rpow hx)

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace SKValueG

lemma gumbel_cdf (t : ℝ) : cdf gumbelLaw t=Real.exp (-Real.exp (-t)) := by
  rw [cdf_eq_real,gumbelLaw,measureReal_def,Measure.map_apply (by fun_prop) measurableSet_Iic]
  have he : (fun x ↦ -Real.log x) ⁻¹' Iic t =ᵐ[expMeasure 1] Ici (Real.exp (-t)) := by
    filter_upwards [exp_one_pos_ae] with x hx
    apply propext
    change -Real.log x ≤ t ↔ Real.exp (-t) ≤ x
    rw [←Real.le_log_iff_exp_le hx]
    constructor <;> intro h <;> linarith
  rw [measure_congr he,←measureReal_def,←compl_Iio,measureReal_compl measurableSet_Iio,
    measureReal_congr Iio_ae_eq_Iic,←cdf_eq_real,cdf_expMeasure_eq (by norm_num)]
  simp [Real.exp_nonneg,probReal_univ]

lemma gumbel_integrable : Integrable (fun x : ℝ ↦ x) gumbelLaw := by
  rw [gumbelLaw,integrable_map_measure (by fun_prop) (by fun_prop)]
  exact exp_one_log_integrable.neg

lemma gumbel_exp_integrable {p : ℝ} (hp : p<1) :
    Integrable (fun x : ℝ ↦ Real.exp (p*x)) gumbelLaw := by
  rw [gumbelLaw,integrable_map_measure (by fun_prop) (by fun_prop)]
  apply (exp_one_rpow_integrable (p := -p) (by linarith)).congr
  filter_upwards [exp_one_pos_ae] with x hx
  rw [Real.rpow_def_of_pos hx]
  congr 1
  ring

lemma prob_measure_eq_of_cdf {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ t, cdf μ t=cdf ν t) : μ=ν := by
  apply Measure.ext_of_Iic
  intro t
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  exact (cdf_eq_real μ t).symm.trans ((h t).trans (cdf_eq_real ν t))

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GumbelMax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma finiteMaximum_le_iff {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (t : ℝ) :
    finiteMaximum x ≤ t ↔ ∀ i, x i≤t := by
  constructor
  · intro h i; exact (le_finiteMaximum x i).trans h
  · intro h; obtain ⟨i,hi⟩ := exists_finiteMaximum x; simpa only [←hi] using h i

lemma exp_sum_pos {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) :
    0<∑ i, Real.exp (d i) := Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty

lemma gumbel_shift_cdf (d t : ℝ) :
    cdf (gumbelLaw.map (fun x ↦ x+d)) t=Real.exp (-Real.exp (-(t-d))) := by
  have : IsProbabilityMeasure (gumbelLaw.map (fun x ↦ x+d)) := Measure.isProbabilityMeasure_map (by fun_prop : Measurable fun x : ℝ ↦ x+d).aemeasurable
  rw [cdf_eq_real,measureReal_def,Measure.map_apply (by fun_prop) measurableSet_Iic]
  have he : (fun x : ℝ ↦ x+d) ⁻¹' Iic t=Iic (t-d) := by ext x; simp only [mem_preimage,mem_Iic]; constructor <;> intro h <;> linarith
  rw [he,←measureReal_def,←cdf_eq_real,gumbel_cdf]

lemma gumbel_max_cdf {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) (t : ℝ) :
    cdf ((Measure.pi (fun _ : ι ↦ gumbelLaw)).map
      (fun z ↦ finiteMaximum (fun i ↦ d i+z i))) t=
      Real.exp (-Real.exp (-(t-logSumExp d))) := by
  have hm : Measurable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i)) :=
    (continuous_finiteMaximum.comp (continuous_const.add continuous_id)).measurable
  have : IsProbabilityMeasure ((Measure.pi (fun _ : ι ↦ gumbelLaw)).map
      (fun z ↦ finiteMaximum (fun i ↦ d i+z i))) := Measure.isProbabilityMeasure_map hm.aemeasurable
  rw [cdf_eq_real,measureReal_def,Measure.map_apply hm measurableSet_Iic]
  have he : (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i)) ⁻¹' Iic t=
      univ.pi (fun i ↦ Iic (t-d i)) := by
    ext z
    simp only [mem_preimage,mem_Iic,finiteMaximum_le_iff,mem_univ_pi]
    exact forall_congr' (fun i ↦ by constructor <;> intro h <;> linarith)
  rw [he,Measure.pi_pi,ENNReal.toReal_prod]
  simp only [←measureReal_def,←cdf_eq_real,gumbel_cdf]
  rw [←Real.exp_sum]
  congr 1
  simp only [logSumExp]
  rw [show -(t-Real.log (∑ i, Real.exp (d i)))=-t+Real.log (∑ i, Real.exp (d i)) by ring,
    Real.exp_add,Real.exp_log (exp_sum_pos d)]
  simp_rw [show ∀ i, -(t-d i)=-t+d i by intro i; ring,Real.exp_add]
  rw [Finset.sum_neg_distrib,←Finset.mul_sum]

theorem gumbel_max_law {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) :
    (Measure.pi (fun _ : ι ↦ gumbelLaw)).map
      (fun z ↦ finiteMaximum (fun i ↦ d i+z i))=
      gumbelLaw.map (fun x ↦ x+logSumExp d) := by
  have hm : Measurable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i)) :=
    (continuous_finiteMaximum.comp (continuous_const.add continuous_id)).measurable
  have : IsProbabilityMeasure ((Measure.pi (fun _ : ι ↦ gumbelLaw)).map
      (fun z ↦ finiteMaximum (fun i ↦ d i+z i))) := Measure.isProbabilityMeasure_map hm.aemeasurable
  have : IsProbabilityMeasure (gumbelLaw.map (fun x ↦ x+logSumExp d)) := Measure.isProbabilityMeasure_map (by fun_prop : Measurable fun x : ℝ ↦ x+logSumExp d).aemeasurable
  apply prob_measure_eq_of_cdf
  intro t
  rw [gumbel_max_cdf,gumbel_shift_cdf]

lemma integral_gumbel_max {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → ℝ) :
    (∫ z, finiteMaximum (fun i ↦ d i+z i) ∂Measure.pi (fun _ : ι ↦ gumbelLaw))=
      gumbelMean+logSumExp d := by
  have hm : Measurable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ d i+z i)) :=
    (continuous_finiteMaximum.comp (continuous_const.add continuous_id)).measurable
  have h := congrArg (fun μ : Measure ℝ ↦ ∫ x, x ∂μ) (gumbel_max_law d)
  rw [integral_map hm.aemeasurable (by fun_prop),integral_map (by fun_prop) (by fun_prop)] at h
  rw [h,integral_add gumbel_integrable (integrable_const _)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,gumbelMean]

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal
namespace SKValueG

lemma log_tangent_bound {x m : ℝ} (hx : 0<x) (hm : 0 < m) :
    Real.log x ≤ x/m-1+Real.log m := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hm)
  rw [Real.log_div hx.ne' hm.ne'] at h
  linarith

lemma log_mean_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (hx : ∀ i, 0<x i) :
    (∑ i, Real.log (x i))/(Fintype.card ι : ℝ) ≤
      Real.log ((∑ i, x i)/(Fintype.card ι : ℝ)) := by
  let c : ℝ := Fintype.card ι
  have hc : 0 < c := by dsimp [c]; positivity
  let m : ℝ := (∑ i, x i)/c
  have hm : 0 < m := div_pos (Finset.sum_pos (fun i _ ↦ hx i) Finset.univ_nonempty) hc
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ log_tangent_bound (hx i) hm)
  have hs : (∑ i, x i) ≠ 0 := (Finset.sum_pos (fun i _ ↦ hx i) Finset.univ_nonempty).ne'
  have he : (∑ i, (x i/m-1+Real.log m))=c*Real.log m := by
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.sum_div]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    dsimp [m,c]
    field_simp [hs]
    ring
  rw [he] at h
  exact (div_le_iff₀ hc).mpr (by nlinarith)

lemma integral_log_le_log_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hl : Integrable (fun ω ↦ Real.log (f ω)) μ)
    (hp : ∀ᵐ ω ∂μ, 0<f ω) :
    (∫ ω, Real.log (f ω) ∂μ) ≤ Real.log (∫ ω, f ω ∂μ) := by
  have hm : 0<∫ ω, f ω ∂μ := integral_pos_iff_support_of_nonneg_ae (hp.mono (fun _ h ↦ h.le)) hf |>.mpr (by
    have hs : Function.support f =ᵐ[μ] univ := hp.mono (fun ω hω ↦ by apply propext; change (f ω≠0) ↔ True; simp [hω.ne'])
    rw [measure_congr hs]
    simp)
  have h := integral_mono_ae hl
    (((hf.div_const (∫ ω, f ω ∂μ)).sub (integrable_const 1)).add
      (integrable_const (Real.log (∫ ω, f ω ∂μ))))
    (hp.mono (fun ω hω ↦ log_tangent_bound hω hm))
  have he : (∫ ω, (f ω/(∫ ω, f ω ∂μ)-1)+Real.log (∫ ω, f ω ∂μ) ∂μ)=
      Real.log (∫ ω, f ω ∂μ) := by
    rw [integral_add (f := fun ω ↦ f ω/(∫ ω, f ω ∂μ)-1)
      (g := fun _ ↦ Real.log (∫ ω, f ω ∂μ))
      ((hf.div_const _).sub (integrable_const 1)) (integrable_const _),
      integral_sub (f := fun ω ↦ f ω/(∫ ω, f ω ∂μ)) (g := fun _ ↦ (1 : ℝ))
      (hf.div_const _) (integrable_const 1),integral_div]
    simp [hm.ne']
  exact h.trans_eq he

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_EmpiricalLog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal
namespace SKValueG

lemma empiricalMean_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} (hi : ∀ i, Integrable (X i) μ) (n : ℕ) :
    Integrable (empiricalMean X n) μ :=
  (integrable_finsetSum _ (fun i _ ↦ hi i)).div_const _

lemma integral_empiricalMean {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} (hi : ∀ i, Integrable (X i) μ)
    (he : ∀ i, (∫ ω, X i ω ∂μ)=∫ ω, X 0 ω ∂μ) (n : ℕ) :
    (∫ ω, empiricalMean X n ω ∂μ)=∫ ω, X 0 ω ∂μ := by
  simp only [empiricalMean]
  rw [integral_div,integral_finsetSum _ (fun i _ ↦ hi i)]
  simp only [he,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  have hn : (n : ℝ)+1≠0 := by positivity
  field_simp

lemma empirical_log_lower {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hp : ∀ i, 0<X i ω) :
    empiricalMean (fun i ω ↦ Real.log (X i ω)) n ω ≤ Real.log (empiricalMean X n ω) := by
  have h := log_mean_lower (fun i : Fin (n+1) ↦ X i ω) (fun i ↦ hp i)
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ Real.log (X i ω)),
    Fin.sum_univ_eq_sum_range (fun i ↦ X i ω)] at h
  simpa only [Fintype.card_fin,empiricalMean,Nat.cast_add,Nat.cast_one] using h

lemma empiricalMean_pos {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hp : ∀ i, 0<X i ω) : 0<empiricalMean X n ω := by
  apply div_pos
  · exact Finset.sum_pos (fun i _ ↦ hp i) (Finset.nonempty_range_iff.mpr (by omega))
  · positivity

theorem expected_log_empiricalMean_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hi : Integrable (X 0) μ) (hl : Integrable (fun ω ↦ Real.log (X 0 ω)) μ)
    (hp : ∀ i, ∀ᵐ ω ∂μ, 0<X i ω)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n ↦ ∫ ω, Real.log (empiricalMean X n ω) ∂μ)
      atTop (𝓝 (Real.log (∫ ω, X 0 ω ∂μ))) := by
  let Y := fun i ω ↦ Real.log (X i ω)
  have hiX (i) : Integrable (X i) μ := (hid i).integrable_iff.mpr hi
  have hidY (i) : IdentDistrib (Y i) (Y 0) μ μ := (hid i).comp Real.measurable_log
  have hiY (i) : Integrable (Y i) μ := (hidY i).integrable_iff.mpr hl
  have hpall : ∀ᵐ ω ∂μ, ∀ i, 0<X i ω := ae_all_iff.mpr hp
  have hiA (n) := empiricalMean_integrable hiX n
  have hiB (n) := empiricalMean_integrable hiY n
  have hpos : 0<∫ ω, X 0 ω ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae ((hp 0).mono (fun _ h ↦ h.le)) hi).mpr (by
      have hs : Function.support (X 0) =ᵐ[μ] univ := (hp 0).mono (fun ω hω ↦ by
        apply propext; change X 0 ω≠0 ↔ True; simp [hω.ne'])
      rw [measure_congr hs]; simp)
  have hlogmeas (n) : AEStronglyMeasurable (fun ω ↦ Real.log (empiricalMean X n ω)) μ :=
    (Real.measurable_log.comp_aemeasurable (hiA n).aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hilog (n) : Integrable (fun ω ↦ Real.log (empiricalMean X n ω)) μ := by
    apply (((hiA n).sub (integrable_const 1)).abs.add (hiB n).abs).mono' (hlogmeas n)
    filter_upwards [hpall] with ω hω
    have hpA := empiricalMean_pos X n ω hω
    have hlo := empirical_log_lower X n ω hω
    have hup := log_tangent_bound hpA (show (0 : ℝ)<1 by norm_num)
    simp only [div_one,Real.log_one,add_zero] at hup
    change |Real.log (empiricalMean X n ω)| ≤ |empiricalMean X n ω-1|+|empiricalMean Y n ω|
    apply abs_le.mpr
    constructor
    · have hh := neg_abs_le (empiricalMean Y n ω)
      have hh' := abs_nonneg (empiricalMean X n ω-1)
      change empiricalMean Y n ω ≤ _ at hlo
      linarith
    · have hh := le_abs_self (empiricalMean X n ω-1)
      have hh' := abs_nonneg (empiricalMean Y n ω)
      linarith
  let F := fun n ω ↦ Real.log (empiricalMean X n ω)-empiricalMean Y n ω
  have hiF (n) : Integrable (F n) μ := (hilog n).sub (hiB n)
  have hFnonneg (n) : ∀ᵐ ω ∂μ, 0≤F n ω :=
    hpall.mono (fun ω hω ↦ sub_nonneg.mpr (empirical_log_lower X n ω hω))
  let c := Real.log (∫ ω, X 0 ω ∂μ)-(∫ ω, Y 0 ω ∂μ)
  have hc : 0 ≤ c := sub_nonneg.mpr (integral_log_le_log_integral hi hl (hp 0))
  have hAX := strong_law_ae_real X hi hind hid
  have hBY := strong_law_ae_real Y hl
    (fun i j hij ↦ (hind hij).comp Real.measurable_log Real.measurable_log) hidY
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ F n ω) atTop (𝓝 c) := by
    filter_upwards [hAX,hBY] with ω hX hY
    have hx := (hX.comp (tendsto_add_atTop_nat 1)).log hpos.ne'
    have hy := hY.comp (tendsto_add_atTop_nat 1)
    simpa only [F,c,empiricalMean,Function.comp_def,Nat.cast_add,Nat.cast_one] using hx.sub hy
  have hiC (n) : Integrable (fun ω ↦ min (F n ω) c) μ := (hiF n).inf (integrable_const c)
  have htrunc := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ c)
    (fun n ↦ (hiC n).aestronglyMeasurable) (integrable_const c)
    (fun n ↦ (hFnonneg n).mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min hω hc)]
      exact min_le_right _ _))
    (hlim.mono (fun ω hω ↦ by simpa only [min_self] using hω.min (tendsto_const_nhds (x := c))))
  have htrunc' : Tendsto (fun n ↦ ∫ ω, min (F n ω) c ∂μ) atTop (𝓝 c) := by simpa using htrunc
  have hIntegral (n) : (∫ ω, F n ω ∂μ)=
      (∫ ω, Real.log (empiricalMean X n ω) ∂μ)-(∫ ω, Y 0 ω ∂μ) := by
    rw [integral_sub (hilog n) (hiB n),integral_empiricalMean hiY (fun i ↦ (hidY i).integral_eq)]
  have hUpper (n) : (∫ ω, F n ω ∂μ) ≤ c := by
    rw [hIntegral]
    apply sub_le_sub_right
    have h := integral_log_le_log_integral (hiA n) (hilog n)
      (hpall.mono (fun ω hω ↦ empiricalMean_pos X n ω hω))
    rwa [integral_empiricalMean hiX (fun i ↦ (hid i).integral_eq)] at h
  have hFin : Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) atTop (𝓝 c) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' htrunc' tendsto_const_nhds
      (Eventually.of_forall (fun n ↦ integral_mono (hiC n) (hiF n) (fun ω ↦ min_le_left _ _)))
      (Eventually.of_forall hUpper)
  have hfinal := hFin.add_const (∫ ω, Y 0 ω ∂μ)
  simpa only [hIntegral,c,sub_add_cancel] using hfinal

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_FiniteBranching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma finiteMaximum_div_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) :
    finiteMaximum (fun i ↦ d i/m)=finiteMaximum d/m := by
  apply le_antisymm
  · rw [finiteMaximum_le_iff]
    intro i
    exact div_le_div_of_nonneg_right (le_finiteMaximum d i) hm.le
  · obtain ⟨i,hi⟩ := exists_finiteMaximum d
    rw [←hi]
    exact le_finiteMaximum (fun i ↦ d i/m) i

lemma integral_scaled_gumbel_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) :
    (∫ z, finiteMaximum (fun i ↦ d i+z i/m) ∂Measure.pi (fun _ : ι ↦ gumbelLaw))=
      (gumbelMean+logSumExp (fun i ↦ m*d i))/m := by
  have he (z : ι → ℝ) : finiteMaximum (fun i ↦ d i+z i/m)=
      finiteMaximum (fun i ↦ m*d i+z i)/m := by
    rw [←finiteMaximum_div_pos _ hm]
    congr 1; ext i; field_simp
  simp_rw [he]
  rw [integral_div,integral_gumbel_max]

lemma centered_gumbel_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) :
    (∫ z, finiteMaximum (fun i ↦ d i+z i/m) ∂Measure.pi (fun _ : ι ↦ gumbelLaw))-
      (gumbelMean+Real.log (Fintype.card ι : ℝ))/m=
    Real.log ((∑ i, Real.exp (m*d i))/(Fintype.card ι : ℝ))/m := by
  rw [integral_scaled_gumbel_max d hm,Real.log_div (exp_sum_pos _).ne' (by positivity)]
  dsimp [logSumExp]
  ring

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma iid_empiricalMean_L1 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hi : Integrable (X 0) μ)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n ↦ ∫ ω, |empiricalMean X n ω-(∫ ω, X 0 ω ∂μ)| ∂μ)
      atTop (𝓝 0) := by
  have hh := strong_law_Lp (p := 1) le_rfl (by simp) X (memLp_one_iff_integrable.mpr hi) hind hid
  have h := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞)≠⊤)).tendsto.comp
    (hh.comp (tendsto_add_atTop_nat 1))
  have hiX (i) : Integrable (X i) μ := (hid i).integrable_iff.mpr hi
  have he (n : ℕ) :
      (∫ ω, |empiricalMean X n ω-(∫ ω, X 0 ω ∂μ)| ∂μ)=
      (eLpNorm (fun ω ↦ (n+1 : ℝ)⁻¹ • (∑ i ∈ Finset.range (n+1),X i ω)-
        (∫ ω, X 0 ω ∂μ)) 1 μ).toReal := by
    have hm := ((empiricalMean_integrable hiX n).sub (integrable_const (∫ ω,X 0 ω ∂μ))).aestronglyMeasurable
    change AEStronglyMeasurable (fun ω ↦ empiricalMean X n ω-(∫ ω,X 0 ω ∂μ)) μ at hm
    rw [eLpNorm_one_eq_lintegral_enorm]
    simpa only [empiricalMean,smul_eq_mul,div_eq_mul_inv,mul_comm,Pi.sub_apply,Real.norm_eq_abs]
      using integral_norm_eq_lintegral_enorm hm
  simpa only [he,Function.comp_def,Nat.cast_add,Nat.cast_one,ENNReal.toReal_zero] using h

lemma nonnegative_L1_of_ae_and_integrals {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → Ω → ℝ} {c : ℝ}
    (hi : ∀ n, Integrable (F n) μ) (hn : ∀ n, ∀ᵐ ω ∂μ, 0≤F n ω)
    (hc : 0 ≤ c) (hlim : ∀ᵐ ω ∂μ,Tendsto (fun n ↦ F n ω) atTop (𝓝 c))
    (hI : Tendsto (fun n ↦ ∫ ω,F n ω ∂μ) atTop (𝓝 c)) :
    Tendsto (fun n ↦ ∫ ω,|F n ω-c| ∂μ) atTop (𝓝 0) := by
  have hiC (n) : Integrable (fun ω ↦ min (F n ω) c) μ := (hi n).inf (integrable_const c)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ c)
    (fun n ↦ (hiC n).aestronglyMeasurable) (integrable_const c)
    (fun n ↦ (hn n).mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min hω hc)]
      exact min_le_right _ _))
    (hlim.mono (fun ω hω ↦ by simpa only [min_self] using hω.min (tendsto_const_nhds (x := c))))
  have ht' : Tendsto (fun n ↦ ∫ ω,min (F n ω) c ∂μ) atTop (𝓝 c) := by simpa using ht
  have he (n) : (∫ ω,|F n ω-c| ∂μ)=(∫ ω,F n ω ∂μ)+c-2*(∫ ω,min (F n ω) c ∂μ) := by
    have eq (ω) : |F n ω-c|=F n ω+c-2*min (F n ω) c := by
      rcases le_total (F n ω) c with h|h
      · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]; ring
    simp_rw [eq]
    rw [integral_sub (f := fun ω ↦ F n ω+c) (g := fun ω ↦ 2*min (F n ω) c)
      ((hi n).add (integrable_const c)) ((hiC n).const_mul 2),
      integral_add (f := F n) (g := fun _ ↦ c) (hi n) (integrable_const c),integral_const_mul,integral_const]
    simp
  have h := (hI.add_const c).sub (ht'.const_mul 2)
  simpa only [he,show c+c-2*c=0 by ring] using h

lemma empiricalMean_log_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hiX : ∀ i,Integrable (X i) μ)
    (hiY : ∀ i,Integrable (fun ω ↦ Real.log (X i ω)) μ)
    (hp : ∀ i,∀ᵐ ω ∂μ,0<X i ω) (n : ℕ) :
    Integrable (fun ω ↦ Real.log (empiricalMean X n ω)) μ := by
  let Y := fun i ω ↦ Real.log (X i ω)
  have hiA := empiricalMean_integrable hiX n
  have hiB := empiricalMean_integrable hiY n
  apply ((hiA.sub (integrable_const 1)).abs.add hiB.abs).mono'
    ((Real.measurable_log.comp_aemeasurable hiA.aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
  filter_upwards [ae_all_iff.mpr hp] with ω hω
  have hpA := empiricalMean_pos X n ω hω
  have hlo := empirical_log_lower X n ω hω
  have hup := log_tangent_bound hpA (show (0 : ℝ)<1 by norm_num)
  simp only [div_one,Real.log_one,add_zero] at hup
  change |Real.log (empiricalMean X n ω)|≤|empiricalMean X n ω-1|+|empiricalMean Y n ω|
  apply abs_le.mpr
  constructor
  · have hh := neg_abs_le (empiricalMean Y n ω)
    have hh' := abs_nonneg (empiricalMean X n ω-1)
    change empiricalMean Y n ω≤_ at hlo
    linarith
  · have hh := le_abs_self (empiricalMean X n ω-1)
    have hh' := abs_nonneg (empiricalMean Y n ω)
    linarith

theorem log_empiricalMean_L1 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hi : Integrable (X 0) μ) (hl : Integrable (fun ω ↦ Real.log (X 0 ω)) μ)
    (hp : ∀ i,∀ᵐ ω ∂μ,0<X i ω)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i,IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n ↦ ∫ ω,|Real.log (empiricalMean X n ω)-Real.log (∫ ω,X 0 ω ∂μ)| ∂μ)
      atTop (𝓝 0) := by
  let Y := fun i ω ↦ Real.log (X i ω)
  have hiX (i) : Integrable (X i) μ := (hid i).integrable_iff.mpr hi
  have hidY (i) : IdentDistrib (Y i) (Y 0) μ μ := (hid i).comp Real.measurable_log
  have hiY (i) : Integrable (Y i) μ := (hidY i).integrable_iff.mpr hl
  have hindY : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) Y) :=
    fun i j hij ↦ (hind hij).comp Real.measurable_log Real.measurable_log
  have hpos : 0<∫ ω,X 0 ω ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae ((hp 0).mono (fun _ h ↦ h.le)) hi).mpr (by
      have hs : Function.support (X 0)=ᵐ[μ] univ := (hp 0).mono (fun ω hω ↦ by
        apply propext; change X 0 ω≠0 ↔ True; simp [hω.ne'])
      rw [measure_congr hs]; simp)
  have hilog (n) := empiricalMean_log_integrable X hiX hiY hp n
  have hiB (n) := empiricalMean_integrable hiY n
  let c := Real.log (∫ ω,X 0 ω ∂μ)-(∫ ω,Y 0 ω ∂μ)
  let F := fun n ω ↦ Real.log (empiricalMean X n ω)-empiricalMean Y n ω
  have hiF (n) : Integrable (F n) μ := (hilog n).sub (hiB n)
  have hFpos (n) : ∀ᵐ ω ∂μ,0≤F n ω := (ae_all_iff.mpr hp).mono (fun ω hω ↦
    sub_nonneg.mpr (empirical_log_lower X n ω hω))
  have hc : 0 ≤ c := sub_nonneg.mpr (integral_log_le_log_integral hi hl (hp 0))
  have hlima : ∀ᵐ ω ∂μ,Tendsto (fun n ↦ F n ω) atTop (𝓝 c) := by
    filter_upwards [strong_law_ae_real X hi hind hid,strong_law_ae_real Y hl hindY hidY] with ω hX hY
    have hx := (hX.comp (tendsto_add_atTop_nat 1)).log hpos.ne'
    have hy := hY.comp (tendsto_add_atTop_nat 1)
    simpa only [F,c,empiricalMean,Function.comp_def,Nat.cast_add,Nat.cast_one] using hx.sub hy
  have hlimI : Tendsto (fun n ↦ ∫ ω,F n ω ∂μ) atTop (𝓝 c) := by
    have h := (expected_log_empiricalMean_tendsto X hi hl hp hind hid).sub_const (∫ ω,Y 0 ω ∂μ)
    have he (n) : (∫ ω,F n ω ∂μ)=(∫ ω,Real.log (empiricalMean X n ω) ∂μ)-(∫ ω,Y 0 ω ∂μ) := by
      rw [integral_sub (hilog n) (hiB n),integral_empiricalMean hiY (fun i ↦ (hidY i).integral_eq)]
    simpa only [he,c] using h
  have hF := nonnegative_L1_of_ae_and_integrals hiF hFpos hc hlima hlimI
  have hY := iid_empiricalMean_L1 Y hl hindY hidY
  have hlim : Tendsto (fun n ↦ (∫ ω,|F n ω-c| ∂μ)+
      (∫ ω,|empiricalMean Y n ω-(∫ ω,Y 0 ω ∂μ)| ∂μ)) atTop (𝓝 0) := by simpa using hF.add hY
  apply squeeze_zero (fun n ↦ integral_nonneg (fun ω ↦ abs_nonneg _)) _ hlim
  intro n
  rw [←integral_add (f := fun ω ↦ |F n ω-c|)
    (g := fun ω ↦ |empiricalMean Y n ω-(∫ ω,Y 0 ω ∂μ)|)
    ((hiF n).sub (integrable_const c)).abs
    ((hiB n).sub (integrable_const _)).abs]
  apply integral_mono ((hilog n).sub (integrable_const _)).abs
    (((hiF n).sub (integrable_const c)).abs.add ((hiB n).sub (integrable_const _)).abs)
  intro ω
  have he : Real.log (empiricalMean X n ω)-Real.log (∫ ω,X 0 ω ∂μ)=
      (F n ω-c)+(empiricalMean Y n ω-(∫ ω,Y 0 ω ∂μ)) := by dsimp [F,c]; ring
  change |Real.log (empiricalMean X n ω)-Real.log (∫ ω,X 0 ω ∂μ)| ≤
    |F n ω-c|+|empiricalMean Y n ω-(∫ ω,Y 0 ω ∂μ)|
  rw [he]
  exact abs_add_le _ _

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GumbelReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma lipschitz_integrable_comp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hi : Integrable f μ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) : Integrable (fun ω ↦ ψ (f ω)) μ := by
  apply ((hi.norm.const_mul (L : ℝ)).add (integrable_const ‖ψ 0‖)).mono'
    (hψ.continuous.comp_aestronglyMeasurable hi.aestronglyMeasurable)
  exact Eventually.of_forall (fun ω ↦ by
    have h : ‖ψ (f ω)-ψ 0‖ ≤ (L : ℝ)*‖f ω‖ := by simpa only [sub_zero] using hψ.norm_sub_le (f ω) 0
    have htri := norm_add_le (ψ (f ω)-ψ 0) (ψ 0)
    simp only [sub_add_cancel] at htri
    change ‖ψ (f ω)‖ ≤ (L : ℝ)*‖f ω‖+‖ψ 0‖
    linarith)

lemma gumbelSmooth_lipschitz {m : ℝ} {ψ : ℝ → ℝ} {L : ℝ≥0}
    (hψ : LipschitzWith L ψ) : LipschitzWith L (gumbelSmooth m ψ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hix := lipschitz_integrable_comp ((gumbel_integrable.div_const m).add (integrable_const x)) hψ
  have hiy := lipschitz_integrable_comp ((gumbel_integrable.div_const m).add (integrable_const y)) hψ
  change |(∫ g, ψ (g/m+x) ∂gumbelLaw)-(∫ g, ψ (g/m+y) ∂gumbelLaw)|≤L*|x-y|
  rw [←integral_sub (f := fun g ↦ ψ (g/m+x)) (g := fun g ↦ ψ (g/m+y)) hix hiy]
  have hbound (g : ℝ) : ‖ψ (g/m+x)-ψ (g/m+y)‖≤(L : ℝ)*|x-y| := by
    simpa only [Real.norm_eq_abs,add_sub_add_left_eq_sub] using hψ.norm_sub_le (g/m+x) (g/m+y)
  simpa using norm_integral_le_of_norm_le_const (μ := gumbelLaw) (Eventually.of_forall hbound)

lemma integral_comp_diff_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {s : Ω → ℝ} (hi : Integrable s μ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) (c : ℝ) :
    |(∫ ω,ψ (s ω) ∂μ)-ψ c|≤(L : ℝ)*(∫ ω,|s ω-c| ∂μ) := by
  have his := lipschitz_integrable_comp hi hψ
  have hie : Integrable (fun ω ↦ |s ω-c|) μ := (hi.sub (integrable_const c)).abs
  calc
    _ = |∫ ω,ψ (s ω)-ψ c ∂μ| := by rw [integral_sub his (integrable_const _)]; simp
    _ ≤ ∫ ω,|ψ (s ω)-ψ c| ∂μ := by simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (fun ω ↦ ψ (s ω)-ψ c)
    _ ≤ ∫ ω,(L : ℝ)*|s ω-c| ∂μ := integral_mono
      (his.sub (integrable_const _)).abs (hie.const_mul _)
      (fun ω ↦ by simpa only [Real.norm_eq_abs] using hψ.norm_sub_le (s ω) c)
    _ = _ := integral_const_mul _ _

lemma scaled_gumbel_test_integral {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    (∫ z,ψ (finiteMaximum (fun i ↦ d i+z i/m)-Real.log (Fintype.card ι : ℝ)/m)
      ∂Measure.pi (fun _ : ι ↦ gumbelLaw))=
      gumbelSmooth m ψ (Real.log ((∑ i,Real.exp (m*d i))/(Fintype.card ι : ℝ))/m) := by
  have hmmax : Measurable (fun z : ι → ℝ ↦ finiteMaximum (fun i ↦ m*d i+z i)) :=
    (continuous_finiteMaximum.comp (continuous_const.add continuous_id)).measurable
  have ht : Measurable (fun y : ℝ ↦ ψ (y/m-Real.log (Fintype.card ι : ℝ)/m)) := by fun_prop
  have h := congrArg (fun μ : Measure ℝ ↦ ∫ y,ψ (y/m-Real.log (Fintype.card ι : ℝ)/m) ∂μ)
    (gumbel_max_law (fun i ↦ m*d i))
  rw [integral_map hmmax.aemeasurable ht.aestronglyMeasurable,
    integral_map (by fun_prop) ht.aestronglyMeasurable] at h
  have he (z : ι → ℝ) : finiteMaximum (fun i ↦ d i+z i/m)=
      finiteMaximum (fun i ↦ m*d i+z i)/m := by
    rw [←finiteMaximum_div_pos _ hm]
    congr 1; ext i; field_simp
  simp_rw [he]
  rw [h]
  apply integral_congr_ae
  exact Eventually.of_forall (fun g ↦ by
    apply congrArg ψ
    rw [Real.log_div (exp_sum_pos _).ne' (by positivity)]
    dsimp [logSumExp]
    ring)

theorem marked_branching_limit {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    {m : ℝ} (hm : 0 < m) (hi : Integrable (X 0) μ)
    (he : Integrable (fun ω ↦ Real.exp (m*X 0 ω)) μ)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i,IdentDistrib (X i) (X 0) μ μ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) :
    Tendsto (fun n ↦ ∫ ω,
      (∫ z,ψ (finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-Real.log (n+1 : ℝ)/m)
        ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)
      atTop (𝓝 (gumbelSmooth m ψ (Real.log (∫ ω,Real.exp (m*X 0 ω) ∂μ)/m))) := by
  let Y := fun i ω ↦ Real.exp (m*X i ω)
  have hf : Measurable (fun x : ℝ ↦ Real.exp (m*x)) := by fun_prop
  have hl : Integrable (fun ω ↦ Real.log (Y 0 ω)) μ := by
    simpa only [Y,Real.log_exp] using hi.const_mul m
  have hiY (i) : Integrable (Y i) μ := ((hid i).comp hf).integrable_iff.mpr he
  have hilogY (i) : Integrable (fun ω ↦ Real.log (Y i ω)) μ :=
    (((hid i).comp hf).comp Real.measurable_log).integrable_iff.mpr hl
  have hpY (i) : ∀ᵐ ω ∂μ,0<Y i ω := Eventually.of_forall (fun ω ↦ Real.exp_pos _)
  have hlim := log_empiricalMean_L1 Y he hl hpY
    (fun i j hij ↦ (hind hij).comp hf hf) (fun i ↦ (hid i).comp hf)
  let c := Real.log (∫ ω,Y 0 ω ∂μ)/m
  let s := fun n ω ↦ Real.log (empiricalMean Y n ω)/m
  have his (n) : Integrable (s n) μ :=
    (empiricalMean_log_integrable Y hiY hilogY hpY n).div_const m
  have herr (n) : (∫ ω,|s n ω-c| ∂μ)=
      (∫ ω,|Real.log (empiricalMean Y n ω)-Real.log (∫ ω,Y 0 ω ∂μ)| ∂μ)/m := by
    rw [←integral_div]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω ↦ by dsimp [s,c]; rw [←sub_div,abs_div,abs_of_pos hm])
  have ht : Tendsto (fun n ↦ ∫ ω,|s n ω-c| ∂μ) atTop (𝓝 0) := by
    simpa only [herr,zero_div] using hlim.div_const m
  have hg := gumbelSmooth_lipschitz (m := m) hψ
  have hb (n) := integral_comp_diff_le (his n) hg c
  have hx : Tendsto (fun n ↦ |(∫ ω,gumbelSmooth m ψ (s n ω) ∂μ)-gumbelSmooth m ψ c|)
      atTop (𝓝 0) := squeeze_zero (fun n ↦ abs_nonneg _) hb (by simpa using ht.const_mul (L : ℝ))
  have hconv : Tendsto (fun n ↦ ∫ ω,gumbelSmooth m ψ (s n ω) ∂μ) atTop
      (𝓝 (gumbelSmooth m ψ c)) := tendsto_iff_norm_sub_tendsto_zero.mpr (by
        simpa only [Real.norm_eq_abs] using hx)
  have heq (n : ℕ) : (∫ ω,(∫ z,ψ (finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-
      Real.log (n+1 : ℝ)/m) ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)=
      ∫ ω,gumbelSmooth m ψ (s n ω) ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω ↦ by
      have hh := scaled_gumbel_test_integral (fun i : Fin (n+1) ↦ X i ω) hm ψ hψ.continuous.measurable
      rw [Fin.sum_univ_eq_sum_range (fun i ↦ Real.exp (m*X i ω))] at hh
      simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,empiricalMean,Y,s] using hh)
  simpa only [heq,c,Y] using hconv

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_EmpiricalPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma rpow_le_add_one {x p : ℝ} (hx : 0≤x) (hp : 0≤p) (hp1 : p≤1) :
    x^p ≤ x+1 := by
  by_cases h : x≤1
  · have hh := Real.rpow_le_one hx h hp
    linarith
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hp1
    rw [Real.rpow_one] at hh
    linarith

lemma integrable_rpow_le_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hi : Integrable X μ)
    (hn : ∀ᵐ ω ∂μ, 0≤X ω) {p : ℝ} (hp : 0≤p) (hp1 : p≤1) :
    Integrable (fun ω ↦ (X ω)^p) μ := by
  apply (hi.abs.add (integrable_const 1)).mono'
    ((Real.continuous_rpow_const hp).comp_aestronglyMeasurable hi.aestronglyMeasurable)
  filter_upwards [hn] with ω hω
  simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hω p),
    abs_of_nonneg hω] using rpow_le_add_one hω hp hp1

lemma integral_rpow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hi : Integrable X μ)
    (hn : ∀ᵐ ω ∂μ, 0≤X ω) {p : ℝ} (hp : 0≤p) (hp1 : p≤1) :
    (∫ ω, (X ω)^p ∂μ) ≤ (∫ ω, X ω ∂μ)^p :=
  (Real.concaveOn_rpow hp hp1).le_map_integral
    (Real.continuous_rpow_const hp).continuousOn isClosed_Ici hn hi
    (integrable_rpow_le_one hi hn hp hp1)

lemma nonneg_integrals_tendsto_of_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : ℕ → Ω → ℝ} {c : ℝ}
    (hi : ∀ n, Integrable (F n) μ) (hn : ∀ n, ∀ᵐ ω ∂μ, 0≤F n ω)
    (hc : 0 ≤ c) (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ F n ω) atTop (𝓝 c))
    (hup : ∀ n, (∫ ω, F n ω ∂μ) ≤ c) :
    Tendsto (fun n ↦ ∫ ω, F n ω ∂μ) atTop (𝓝 c) := by
  have hiC (n) : Integrable (fun ω ↦ min (F n ω) c) μ := (hi n).inf (integrable_const c)
  have ht := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ c)
    (fun n ↦ (hiC n).aestronglyMeasurable) (integrable_const c)
    (fun n ↦ (hn n).mono (fun ω hω ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min hω hc)]
      exact min_le_right _ _))
    (hlim.mono (fun ω hω ↦ by simpa only [min_self] using hω.min (tendsto_const_nhds (x := c))))
  have ht' : Tendsto (fun n ↦ ∫ ω, min (F n ω) c ∂μ) atTop (𝓝 c) := by simpa using ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ht' tendsto_const_nhds
    (Eventually.of_forall (fun n ↦ integral_mono (hiC n) (hi n) (fun ω ↦ min_le_left _ _)))
    (Eventually.of_forall hup)

theorem expected_rpow_empiricalMean_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hi : Integrable (X 0) μ) (hp : ∀ i, ∀ᵐ ω ∂μ, 0≤X i ω)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {p : ℝ} (hp0 : 0≤p) (hp1 : p≤1) :
    Tendsto (fun n ↦ ∫ ω, (empiricalMean X n ω)^p ∂μ)
      atTop (𝓝 ((∫ ω, X 0 ω ∂μ)^p)) := by
  have hiX (i) : Integrable (X i) μ := (hid i).integrable_iff.mpr hi
  have hiall (n) := empiricalMean_integrable hiX n
  have hpall := ae_all_iff.mpr hp
  have hpA (n) : ∀ᵐ ω ∂μ, 0≤empiricalMean X n ω := hpall.mono (fun ω hω ↦ by
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ ↦ hω i)
    · positivity)
  have hiA (n) := integrable_rpow_le_one (hiall n) (hpA n) hp0 hp1
  apply nonneg_integrals_tendsto_of_upper hiA
    (fun n ↦ (hpA n).mono (fun ω hω ↦ Real.rpow_nonneg hω p))
    (Real.rpow_nonneg (integral_nonneg_of_ae (hp 0)) p)
  · have hAX := strong_law_ae_real X hi hind hid
    exact hAX.mono (fun ω hω ↦ by
      have h := ((Real.continuous_rpow_const hp0).tendsto (∫ ω, X 0 ω ∂μ)).comp
        (hω.comp (tendsto_add_atTop_nat 1))
      simpa only [empiricalMean,Function.comp_def,Nat.cast_add,Nat.cast_one] using h)
  · intro n
    have h := integral_rpow_le (hiall n) (hpA n) hp0 hp1
    rwa [integral_empiricalMean hiX (fun i ↦ (hid i).integral_eq)] at h

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators
namespace SKValueG

lemma gumbelExpMoment_pos {p : ℝ} (hp : p<1) : 0<gumbelExpMoment p := by
  apply (integral_pos_iff_support_of_nonneg (fun g ↦ (Real.exp_pos (p*g)).le)
    (gumbel_exp_integrable hp)).mpr
  simp [Function.support,Real.exp_ne_zero]

lemma gumbelSmooth_exp (m a c : ℝ) :
    gumbelSmooth m (fun x ↦ Real.exp (a*x)) c=
      gumbelExpMoment (a/m)*Real.exp (a*c) := by
  have he (g : ℝ) : Real.exp (a*(g/m+c))=Real.exp ((a/m)*g)*Real.exp (a*c) := by
    rw [←Real.exp_add]; congr 1; ring
  simp only [gumbelSmooth,he,integral_mul_const,gumbelExpMoment]

lemma finite_centered_max_exp_moment {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) {m : ℝ} (hm : 0 < m) (a : ℝ) :
    (∫ z,Real.exp (a*(finiteMaximum (fun i ↦ d i+z i/m)-Real.log (Fintype.card ι : ℝ)/m))
      ∂Measure.pi (fun _ : ι ↦ gumbelLaw))=
    gumbelExpMoment (a/m)*((∑ i,Real.exp (m*d i))/(Fintype.card ι : ℝ))^(a/m) := by
  rw [scaled_gumbel_test_integral d hm (fun x ↦ Real.exp (a*x)) (by fun_prop),gumbelSmooth_exp]
  congr 1
  rw [Real.rpow_def_of_pos (div_pos (exp_sum_pos _) (by positivity))]
  congr 1
  ring

lemma empirical_branch_exp_identity {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : ℕ → Ω → ℝ) {m : ℝ} (hm : 0 < m) (a : ℝ) (n : ℕ) :
    (∫ ω,(∫ z,Real.exp (a*(finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-
        Real.log (n+1 : ℝ)/m)) ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)=
      gumbelExpMoment (a/m)*∫ ω,(empiricalMean (fun i ω ↦ Real.exp (m*X i ω)) n ω)^(a/m) ∂μ := by
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω ↦ by
    have h := finite_centered_max_exp_moment (fun i : Fin (n+1) ↦ X i ω) hm a
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ Real.exp (m*X i ω))] at h
    simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,empiricalMean] using h)

theorem marked_branching_exponential_limit {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    {m : ℝ} (hm : 0 < m) {a : ℝ} (ha : 0≤a) (ham : a < m)
    (he : Integrable (fun ω ↦ Real.exp (m*X 0 ω)) μ)
    (hind : Pairwise (Function.onFun (fun x1 x2 ↦ x1 ⟂ᵢ[μ] x2) X))
    (hid : ∀ i,IdentDistrib (X i) (X 0) μ μ) :
    Tendsto (fun n ↦ ∫ ω,(∫ z,Real.exp (a*(finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-
        Real.log (n+1 : ℝ)/m)) ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)
      atTop (𝓝 (gumbelExpMoment (a/m)*(∫ ω,Real.exp (m*X 0 ω) ∂μ)^(a/m))) := by
  let Y := fun i ω ↦ Real.exp (m*X i ω)
  have hf : Measurable (fun x : ℝ ↦ Real.exp (m*x)) := by fun_prop
  have hp : 0≤a/m := div_nonneg ha hm.le
  have hp1 : a/m≤1 := (div_le_one hm).mpr ham.le
  have h := expected_rpow_empiricalMean_tendsto Y he
    (fun i ↦ Eventually.of_forall (fun ω ↦ (Real.exp_pos _).le))
    (fun i j hij ↦ (hind hij).comp hf hf) (fun i ↦ (hid i).comp hf) hp hp1
  simpa only [empirical_branch_exp_identity X hm a,Y] using h.const_mul (gumbelExpMoment (a/m))

theorem marked_branching_exponential_upper {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    {m : ℝ} (hm : 0 < m) {a : ℝ} (ha : 0≤a) (ham : a < m)
    (he : Integrable (fun ω ↦ Real.exp (m*X 0 ω)) μ)
    (hid : ∀ i,IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    (∫ ω,(∫ z,Real.exp (a*(finiteMaximum (fun i : Fin (n+1) ↦ X i ω+z i/m)-
        Real.log (n+1 : ℝ)/m)) ∂Measure.pi (fun _ : Fin (n+1) ↦ gumbelLaw)) ∂μ)≤
      gumbelExpMoment (a/m)*(∫ ω,Real.exp (m*X 0 ω) ∂μ)^(a/m) := by
  rw [empirical_branch_exp_identity X hm a n]
  let Y := fun i ω ↦ Real.exp (m*X i ω)
  have hf : Measurable (fun x : ℝ ↦ Real.exp (m*x)) := by fun_prop
  have hiY (i) : Integrable (Y i) μ := ((hid i).comp hf).integrable_iff.mpr he
  have hpA : ∀ᵐ ω ∂μ,0≤empiricalMean Y n ω := Eventually.of_forall (fun ω ↦
    (empiricalMean_pos Y n ω (fun i ↦ Real.exp_pos _)).le)
  have h := integral_rpow_le (empiricalMean_integrable hiY n) hpA
    (div_nonneg ha hm.le) ((div_le_one hm).mpr ham.le)
  rw [integral_empiricalMean hiY (fun i ↦ ((hid i).comp hf).integral_eq)] at h
  exact mul_le_mul_of_nonneg_left h (gumbelExpMoment_pos ((div_lt_one hm).mpr ham)).le

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_BranchLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma continuous_branchMax (m : ℝ) (b : ℕ) : Continuous (branchMax m b) := by
  apply Continuous.sub _ continuous_const
  exact continuous_finiteMaximum.comp (by fun_prop)

instance branchLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) (b : ℕ) :
    IsProbabilityMeasure (branchLaw μ m b) := by
  unfold branchLaw
  exact Measure.isProbabilityMeasure_map (continuous_branchMax m b).measurable.aemeasurable

lemma integrable_finiteMaximum_of_integrable {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] {μ : Measure Ω} {f : ι → Ω → ℝ}
    (hf : ∀ i,Integrable (f i) μ) : Integrable (fun ω ↦ finiteMaximum (fun i ↦ f i ω)) μ := by
  apply (integrable_finsetSum Finset.univ (fun i _ ↦ (hf i).abs)).mono'
    (continuous_finiteMaximum.comp_aestronglyMeasurable ((integrable_pi_iff.mpr hf).aestronglyMeasurable))
  exact Eventually.of_forall (fun ω ↦ by simpa only [Real.norm_eq_abs] using abs_finiteMaximum_le (fun i ↦ f i ω))

lemma branchMax_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) (m : ℝ) (b : ℕ) :
    Integrable (branchMax m b)
      ((Measure.pi (fun _ : Fin (b+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))) := by
  apply Integrable.sub _ (integrable_const _)
  apply integrable_finiteMaximum_of_integrable
  intro i
  have hiX : Integrable (fun x : Fin (b+1) → ℝ ↦ x i) (Measure.pi (fun _ ↦ μ)) :=
    (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).integrable_comp (by fun_prop) |>.mpr hi
  have hiG : Integrable (fun z : Fin (b+1) → ℝ ↦ z i) (Measure.pi (fun _ ↦ gumbelLaw)) :=
    (measurePreserving_eval (fun _ : Fin (b+1) ↦ gumbelLaw) i).integrable_comp (by fun_prop) |>.mpr gumbel_integrable
  exact (hiX.comp_fst _).add ((hiG.div_const m).comp_snd _)

lemma branchLaw_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) (m : ℝ) (b : ℕ) :
    Integrable (fun x : ℝ ↦ x) (branchLaw μ m b) := by
  rw [branchLaw,integrable_map_measure (by fun_prop) (continuous_branchMax m b).measurable.aemeasurable]
  exact branchMax_integrable hi m b

lemma branchMax_exp_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a m : ℝ} (_ : 0≤a) (ham : a/m<1)
    (he : Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ) (b : ℕ) :
    Integrable (fun p ↦ Real.exp (a*branchMax m b p))
      ((Measure.pi (fun _ : Fin (b+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))) := by
  have hi (i : Fin (b+1)) : Integrable (fun p : (Fin (b+1) → ℝ) × (Fin (b+1) → ℝ) ↦
      Real.exp (a*p.1 i)*Real.exp ((a/m)*p.2 i))
      ((Measure.pi (fun _ : Fin (b+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))) := by
    apply Integrable.mul_prod (f := fun x : Fin (b+1) → ℝ ↦ Real.exp (a*x i))
      (g := fun z : Fin (b+1) → ℝ ↦ Real.exp ((a/m)*z i))
    · exact (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).integrable_comp (by fun_prop) |>.mpr he
    · exact (measurePreserving_eval (fun _ : Fin (b+1) ↦ gumbelLaw) i).integrable_comp (by fun_prop) |>.mpr (gumbel_exp_integrable ham)
  apply ((integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).mul_const
    (Real.exp (-a*Real.log (b+1 : ℝ)/m))).mono'
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_branchMax m b))).aestronglyMeasurable)
  apply Eventually.of_forall
  intro p
  simp only [Function.comp_def,Pi.mul_apply]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  obtain ⟨i,hi⟩ := exists_finiteMaximum (fun i : Fin (b+1) ↦ p.1 i+p.2 i/m)
  calc
    _ = (Real.exp (a*p.1 i)*Real.exp ((a/m)*p.2 i))*Real.exp (-a*Real.log (b+1 : ℝ)/m) := by
      simp only [branchMax,←hi,←Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun j : Fin (b+1) ↦ Real.exp (a*p.1 j)*Real.exp ((a/m)*p.2 j))
      (fun j _ ↦ by positivity) (Finset.mem_univ i)) (Real.exp_pos _).le

lemma branchLaw_exp_integral {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a m : ℝ} (ha : 0≤a) (ham : a/m<1)
    (he : Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ) (b : ℕ) :
    (∫ x,Real.exp (a*x) ∂branchLaw μ m b)=
      ∫ x,(∫ z,Real.exp (a*branchMax m b (x,z)) ∂Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))
        ∂Measure.pi (fun _ : Fin (b+1) ↦ μ) := by
  rw [branchLaw,integral_map (continuous_branchMax m b).measurable.aemeasurable (by fun_prop)]
  exact integral_prod _ (branchMax_exp_integrable ha ham he b)

lemma iid_sequence_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (i : ℕ) :
    HasLaw (fun x : ℕ → ℝ ↦ x i) μ (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) i).hasLaw

lemma iid_finite_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℕ) :
    HasLaw (fun x : ℕ → ℝ ↦ fun i : Fin (b+1) ↦ x i) (Measure.pi (fun _ : Fin (b+1) ↦ μ))
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  apply iIndepFun.hasLaw_pi (fun i : Fin (b+1) ↦ iid_sequence_law μ i.val)
  exact (iIndepFun_infinitePi (P := fun _ : ℕ ↦ μ) (X := fun _ x ↦ x)
    (fun _ ↦ measurable_id)).precomp Fin.val_injective

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma integrable_exp_smaller {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a m : ℝ} (ha : 0≤a) (ham : a ≤ m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) :
    Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ := by
  apply (he.add (integrable_const 1)).mono' (by fun_prop)
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  change Real.exp (a*x)≤Real.exp (m*x)+1
  by_cases hx : 0≤x
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ham hx)).trans (by linarith)
  · have h := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha (le_of_not_ge hx))
    linarith [Real.exp_pos (m*x)]

lemma iid_branchIntegral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) (b : ℕ) (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    (∫ x,(∫ z,ψ (branchMax m b (x,z)) ∂Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))
      ∂Measure.pi (fun _ : Fin (b+1) ↦ μ))=
    ∫ x : ℕ → ℝ,(∫ z,ψ (branchMax m b ((fun i ↦ x i),z))
      ∂Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw)) ∂Measure.infinitePi (fun _ : ℕ ↦ μ) := by
  exact ((iid_finite_law μ b).integral_comp
    ((hψ.comp (continuous_branchMax m b)).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)).symm

lemma branchLaw_test {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) (m : ℝ) (b : ℕ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) :
    (∫ x,ψ x ∂branchLaw μ m b)=
      ∫ x,(∫ z,ψ (branchMax m b (x,z)) ∂Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw))
        ∂Measure.pi (fun _ : Fin (b+1) ↦ μ) := by
  rw [branchLaw,integral_map (continuous_branchMax m b).measurable.aemeasurable
    hψ.continuous.aestronglyMeasurable]
  exact integral_prod _ (lipschitz_integrable_comp (branchMax_integrable hi m b) hψ)

lemma gumbelSmooth_id (m c : ℝ) : gumbelSmooth m id c=gumbelMean/m+c := by
  simp only [gumbelSmooth,id_eq]
  rw [integral_add (gumbel_integrable.div_const m) (integrable_const c),integral_div,integral_const]
  simp [gumbelMean]

theorem branchLaw_test_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) {m : ℝ} (hm : 0 < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ)
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψ : LipschitzWith L ψ) :
    Tendsto (fun b ↦ ∫ x,ψ x ∂branchLaw μ m b) atTop
      (𝓝 (gumbelSmooth m ψ (Real.log (∫ x,Real.exp (m*x) ∂μ)/m))) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let X := fun i (x : ℕ → ℝ) ↦ x i
  have hd : IdentDistrib (X 0) id P μ := (iid_sequence_law μ 0).identDistrib HasLaw.id
  have hex := (hd.comp (show Measurable (fun x : ℝ ↦ Real.exp (m*x)) by fun_prop))
  have hind : iIndepFun X P := iIndepFun_infinitePi (fun _ ↦ measurable_id)
  have h := marked_branching_limit X hm (hd.integrable_iff.mpr hi)
    (hex.integrable_iff.mpr he) (fun i j hij ↦ hind.indepFun hij)
    (fun i ↦ (iid_sequence_law μ i).identDistrib (iid_sequence_law μ 0)) hψ
  have heq := hex.integral_eq
  simp only [Function.comp_def,id_eq] at heq
  rw [heq] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext b
  exact (branchLaw_test hi m b hψ).trans (iid_branchIntegral μ m b ψ hψ.continuous)

theorem branchLaw_mean_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) {m : ℝ} (hm : 0 < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) :
    Tendsto (fun b ↦ ∫ x,x ∂branchLaw μ m b) atTop
      (𝓝 (gumbelMean/m+Real.log (∫ x,Real.exp (m*x) ∂μ)/m)) := by
  simpa only [gumbelSmooth_id,id_eq] using branchLaw_test_tendsto hi hm he LipschitzWith.id

theorem branchLaw_exp_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m) {a : ℝ} (ha : 0≤a) (ham : a < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) :
    Tendsto (fun b ↦ ∫ x,Real.exp (a*x) ∂branchLaw μ m b) atTop
      (𝓝 (gumbelExpMoment (a/m)*(∫ x,Real.exp (m*x) ∂μ)^(a/m))) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let X := fun i (x : ℕ → ℝ) ↦ x i
  have hd : IdentDistrib (X 0) id P μ := (iid_sequence_law μ 0).identDistrib HasLaw.id
  have hex := hd.comp (show Measurable (fun x : ℝ ↦ Real.exp (m*x)) by fun_prop)
  have hind : iIndepFun X P := iIndepFun_infinitePi (fun _ ↦ measurable_id)
  have h := marked_branching_exponential_limit X hm ha ham (hex.integrable_iff.mpr he)
    (fun i j hij ↦ hind.indepFun hij) (fun i ↦ (iid_sequence_law μ i).identDistrib (iid_sequence_law μ 0))
  have heq := hex.integral_eq
  simp only [Function.comp_def,id_eq] at heq
  rw [heq] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext b
  exact (branchLaw_exp_integral ha ((div_lt_one hm).mpr ham) (integrable_exp_smaller ha ham.le he) b).trans
    (iid_branchIntegral μ m b (fun x ↦ Real.exp (a*x)) (by fun_prop))

theorem branchLaw_exp_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {m : ℝ} (hm : 0 < m) {a : ℝ} (ha : 0≤a) (ham : a < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) (b : ℕ) :
    (∫ x,Real.exp (a*x) ∂branchLaw μ m b)≤
      gumbelExpMoment (a/m)*(∫ x,Real.exp (m*x) ∂μ)^(a/m) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ μ)
  let X := fun i (x : ℕ → ℝ) ↦ x i
  have hd : IdentDistrib (X 0) id P μ := (iid_sequence_law μ 0).identDistrib HasLaw.id
  have hex := hd.comp (show Measurable (fun x : ℝ ↦ Real.exp (m*x)) by fun_prop)
  have h := marked_branching_exponential_upper X hm ha ham (hex.integrable_iff.mpr he)
    (fun i ↦ (iid_sequence_law μ i).identDistrib (iid_sequence_law μ 0)) b
  have heq := hex.integral_eq
  simp only [Function.comp_def,id_eq] at heq
  rw [heq] at h
  have heqb := (branchLaw_exp_integral ha ((div_lt_one hm).mpr ham) (integrable_exp_smaller ha ham.le he) b).trans
    (iid_branchIntegral μ m b (fun x ↦ Real.exp (a*x)) (by fun_prop))
  rw [heqb]
  exact h

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_GaussianTree
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma treePath_inner_node (c : ℝ → TreeLevel → ℝ) (q : ℝ) (l : TreeLevel) (T : GaussianTree)
    (α β : TreeLeaves (l::T)) :
    (∑ e,treePathCoeff c q (l::T) α e*treePathCoeff c q (l::T) β e)=
    if α.1=β.1 then (c q l)^2+∑ e,treePathCoeff c l.endpoint T α.2 e*treePathCoeff c l.endpoint T β.2 e else 0 := by
  classical
  change (∑ e : Fin (l.branchExcess+1) ⊕ (Fin (l.branchExcess+1) × TreeEdges T),_)=_
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [treePathCoeff]
  by_cases h : α.1=β.1
  · simp only [h,ite_true]
    simp [←h,ite_mul,mul_ite,sq]
  · simp only [h,ite_false]
    have he (i : Fin (l.branchExcess+1)) : ¬(α.1=i ∧ β.1=i) := by
      rintro ⟨ha,hb⟩; exact h (ha.trans hb.symm)
    simp_rw [ite_mul,zero_mul]
    simp only [mul_ite,mul_zero]
    have hzero (i : Fin (l.branchExcess+1)) (r s : ℝ) :
        (if α.1=i then if β.1=i then r*s else 0 else 0)=0 := by
      split_ifs with ha hb <;> try rfl
      exact (he i ⟨ha,hb⟩).elim
    simp only [hzero,Finset.sum_const_zero,add_zero]

lemma treeField_inner (q : ℝ) (T : GaussianTree) (hT : ValidTreeGrid q T)
    (α β : TreeLeaves T) :
    (∑ e,treeFieldVector q T α e*treeFieldVector q T β e)=treeOverlap q T α β-q := by
  induction T generalizing q with
  | nil =>
    simp only [treeFieldVector,treePathCoeff,treeOverlap,sub_self]
    exact Finset.sum_eq_zero (by intro e he; exact PEmpty.elim e)
  | cons l T ih =>
    change q≤l.endpoint ∧ ValidTreeGrid l.endpoint T at hT
    rw [treeFieldVector,treePath_inner_node]
    dsimp [treeOverlap]
    split_ifs with h
    · rw [Real.sq_sqrt (sub_nonneg.mpr hT.1)]
      have hh := ih l.endpoint hT.2 α.2 β.2
      change (l.endpoint-q)+(∑ e,treeFieldVector l.endpoint T α.2 e*treeFieldVector l.endpoint T β.2 e)=_
      rw [hh]; ring
    · ring

lemma treeAux_inner (n : ℕ) (q : ℝ) (hq : 0≤q) (T : GaussianTree) (hT : ValidTreeGrid q T)
    (α β : TreeLeaves T) :
    (∑ e,treeAuxVector n q T α e*treeAuxVector n q T β e)=
      ((n : ℝ)/2)*((treeOverlap q T α β)^2-q^2) := by
  induction T generalizing q with
  | nil =>
    simp only [treeAuxVector,treePathCoeff,treeOverlap,sub_self,mul_zero]
    exact Finset.sum_eq_zero (by intro e he; exact PEmpty.elim e)
  | cons l T ih =>
    change q≤l.endpoint ∧ ValidTreeGrid l.endpoint T at hT
    rw [treeAuxVector,treePath_inner_node]
    dsimp [treeOverlap]
    split_ifs with h
    · rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by nlinarith [hT.1])]
      have hh := ih l.endpoint (hq.trans hT.1) hT.2 α.2 β.2
      change ((n : ℝ)/2)*(l.endpoint^2-q^2)+
        (∑ e,treeAuxVector n l.endpoint T α.2 e*treeAuxVector n l.endpoint T β.2 e)=_
      rw [hh]; ring
    · ring

lemma treeOverlap_self (q : ℝ) (T : GaussianTree) (hT : ValidTreeGrid q T) (α : TreeLeaves T) :
    treeOverlap q T α α=1 := by
  induction T generalizing q with
  | nil => exact hT
  | cons l T ih => simp only [treeOverlap,ite_true]; exact ih l.endpoint hT.2 α.2

lemma treeField_unit (T : GaussianTree) (hT : ValidTreeGrid 0 T) (α : TreeLeaves T) :
    (∑ e,(treeFieldVector 0 T α e)^2)=1 := by
  simp only [sq]
  rw [treeField_inner 0 T hT,treeOverlap_self 0 T hT]
  norm_num

lemma treeAux_distance (n : ℕ) (T : GaussianTree) (hT : ValidTreeGrid 0 T)
    (α β : TreeLeaves T) :
    (∑ e,(treeAuxVector n 0 T α e-treeAuxVector n 0 T β e)^2)=
      (n : ℝ)*(1-(treeOverlap 0 T α β)^2) := by
  rw [sq_distance_sum]
  simp only [sq]
  rw [treeAux_inner n 0 (by norm_num) T hT,
    treeAux_inner n 0 (by norm_num) T hT,
    treeAux_inner n 0 (by norm_num) T hT,
    treeOverlap_self 0 T hT,treeOverlap_self 0 T hT]
  ring

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_LiteralLower
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma finiteMaximum_prod_add {ι Λ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype Λ] [Nonempty Λ] (f : ι → ℝ) (g : Λ → ℝ) :
    finiteMaximum (fun p : ι×Λ ↦ f p.1+g p.2)=finiteMaximum f+finiteMaximum g := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := exists_finiteMaximum (fun p : ι×Λ ↦ f p.1+g p.2)
    rw [←hp]
    exact add_le_add (le_finiteMaximum f p.1) (le_finiteMaximum g p.2)
  · obtain ⟨i,hi⟩ := exists_finiteMaximum f
    obtain ⟨a,ha⟩ := exists_finiteMaximum g
    rw [←hi,←ha]
    exact le_finiteMaximum (fun p : ι×Λ ↦ f p.1+g p.2) (i,a)

lemma finiteMaximum_prod_curry {ι Λ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype Λ] [Nonempty Λ] (f : ι×Λ → ℝ) :
    finiteMaximum f=finiteMaximum (fun a ↦ finiteMaximum (fun i ↦ f (i,a))) := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := exists_finiteMaximum f
    rw [←hp]
    exact (le_finiteMaximum (fun i ↦ f (i,p.2)) p.1).trans
      (le_finiteMaximum (fun a ↦ finiteMaximum (fun i ↦ f (i,a))) p.2)
  · obtain ⟨a,ha⟩ := exists_finiteMaximum (fun a ↦ finiteMaximum (fun i ↦ f (i,a)))
    obtain ⟨i,hi⟩ := exists_finiteMaximum (fun i ↦ f (i,a))
    rw [←ha,←hi]
    exact le_finiteMaximum f (i,a)

lemma spinMaximum_eq_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    finiteMaximum (fun σ : ι → Bool ↦ ∑ i, spin (σ i)*x i)=∑ i, |x i| := by
  classical
  apply le_antisymm
  · obtain ⟨σ,hσ⟩ := exists_finiteMaximum (fun σ : ι → Bool ↦ ∑ i, spin (σ i)*x i)
    rw [←hσ]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |spin (σ i)*x i| := le_abs_self _
      _ = _ := by rw [abs_mul,abs_spin,one_mul]
  · let σ : ι → Bool := fun i ↦ decide (0≤x i)
    have he (i : ι) : spin (σ i)*x i=|x i| := by
      by_cases h : 0≤x i
      · simp [σ,spin,h,abs_of_nonneg h]
      · simp [σ,spin,h,abs_of_neg (lt_of_not_ge h)]
    simpa only [he] using le_finiteMaximum (fun σ : ι → Bool ↦ ∑ i, spin (σ i)*x i) σ

lemma linearProcess_leafField {Λ κ : Type*} [Fintype κ] (n : ℕ)
    (v : Λ → κ → ℝ) (z : Fin n×κ → ℝ) (p : (Fin n → Bool)×Λ) :
    linearProcess (leafFieldCoeff n v) z p=∑ i, spin (p.1 i)*leafField v z p.2 i := by
  simp only [linearProcess,leafFieldCoeff,Fintype.sum_prod_type,leafField,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma leafField_max {Λ κ : Type*} [Fintype Λ] [Nonempty Λ] [Fintype κ]
    (n : ℕ) (v : Λ → κ → ℝ) (d : Λ → ℝ) (z : Fin n×κ → ℝ) :
    finiteMaximum (fun p ↦ linearProcess (leafFieldCoeff n v) z p+d p.2)=
      finiteMaximum (fun α ↦ (∑ i, |leafField v z α i|)+d α) := by
  rw [finiteMaximum_prod_curry]
  simp only [linearProcess_leafField,finiteMaximum_add_const,spinMaximum_eq_sum_abs]

lemma expected_guerra_max {Λ κ : Type*} [Fintype Λ] [Nonempty Λ] [Fintype κ]
    (n : ℕ) (v : Λ → κ → ℝ) (d : Λ → ℝ) :
    (∫ z, finiteMaximum (fun p ↦ linearProcess (guerraCoeff n v) z p+d p.2)
      ∂gaussianProduct ((Fin n×Fin n)⊕(κ×κ))) = expectedMaximum n+
      ∫ z, finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z α+d α)
        ∂gaussianProduct (κ×κ) := by
  have he := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin n×Fin n)⊕(κ×κ) ↦ standardGaussian)
  change (∫ z, finiteMaximum (fun p ↦ linearProcess (guerraCoeff n v) z p+d p.2)
    ∂Measure.pi (fun _ : (Fin n×Fin n)⊕(κ×κ) ↦ standardGaussian)) = _
  rw [←he.integral_comp' (fun z ↦ finiteMaximum (fun p ↦ linearProcess (guerraCoeff n v) z p+d p.2))]
  have hlin (z : ((Fin n×Fin n) → ℝ)×((κ×κ) → ℝ)) :
      (fun p ↦ linearProcess (guerraCoeff n v)
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin n×Fin n)⊕(κ×κ) ↦ ℝ)).symm z) p+d p.2) =
      (fun p ↦ linearProcess (hamCoeff n) z.1 p.1+(linearProcess (leafAuxCoeff n v) z.2 p.2+d p.2)) := by
    funext p
    simp [linearProcess,guerraCoeff,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm,add_assoc]
  have hm (z : ((Fin n×Fin n) → ℝ)×((κ×κ) → ℝ)) :
      finiteMaximum (fun p : (Fin n → Bool)×Λ ↦ linearProcess (hamCoeff n) z.1 p.1+
        (linearProcess (leafAuxCoeff n v) z.2 p.2+d p.2)) =
      finiteMaximum (linearProcess (hamCoeff n) z.1)+
        finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z.2 α+d α) :=
    finiteMaximum_prod_add (linearProcess (hamCoeff n) z.1)
      (fun α ↦ linearProcess (leafAuxCoeff n v) z.2 α+d α)
  simp only [hlin,hm]
  change (∫ z, finiteMaximum (linearProcess (hamCoeff n) z.1)+
    finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z.2 α+d α)
      ∂(gaussianProduct (Fin n×Fin n)).prod (gaussianProduct (κ×κ))) = _
  rw [integral_add ((finiteMaximum_integrable (hamCoeff n)).comp_fst _)
    ((affineMaximum_integrable (leafAuxCoeff n v) d).comp_snd _),
    integral_fun_fst (fun z ↦ finiteMaximum (linearProcess (hamCoeff n) z)),
    integral_fun_snd (fun z ↦ finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z α+d α))]
  simp [expectedMaximum]

theorem finite_guerra_upper {Λ κ : Type*} [Fintype Λ] [Nonempty Λ] [Fintype κ]
    {n : ℕ} (hn : 0<n) (v : Λ → κ → ℝ)
    (hv : ∀ α, ∑ k, (v α k)^2=1) (d : Λ → ℝ) :
    expectedMaximum n+
      (∫ z, finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z α+d α)
        ∂gaussianProduct (κ×κ)) ≤
      ∫ z, finiteMaximum (fun α ↦ (∑ i, |leafField v z α i|)+d α)
        ∂gaussianProduct (Fin n×κ) := by
  have h := expected_affine_max_le (guerraCoeff n v) (leafFieldCoeff n v)
    (fun p ↦ d p.2) (guerra_metric_le hn v hv)
  simpa only [expected_guerra_max,leafField_max] using h

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_TreeGuerra
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma treeAux_tensor_distance (n : ℕ) (T : GaussianTree) (hT : ValidTreeGrid 0 T)
    (α β : TreeLeaves T) :
    (∑ e,(leafAuxCoeff n (treeFieldVector 0 T) α e-leafAuxCoeff n (treeFieldVector 0 T) β e)^2)=
      ∑ e,(treeAuxVector n 0 T α e-treeAuxVector n 0 T β e)^2 := by
  rw [sq_distance_sum,leafAux_sq n _ (treeField_unit T hT),
    leafAux_sq n _ (treeField_unit T hT),leafAux_inner,treeField_inner 0 T hT,
    treeAux_distance n T hT]
  ring

lemma expected_treeAux_eq_tensor (n : ℕ) (T : GaussianTree) (hT : ValidTreeGrid 0 T)
    (d : TreeLeaves T → ℝ) :
    (∫ z,finiteMaximum (fun α ↦ linearProcess (treeAuxVector n 0 T) z α+d α)
      ∂gaussianProduct (TreeEdges T))=
    ∫ z,finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n (treeFieldVector 0 T)) z α+d α)
      ∂gaussianProduct (TreeEdges T × TreeEdges T) := by
  apply le_antisymm
  · exact expected_affine_max_le _ _ d (fun α β ↦ (treeAux_tensor_distance n T hT α β).symm.le)
  · exact expected_affine_max_le _ _ d (fun α β ↦ (treeAux_tensor_distance n T hT α β).le)

theorem finite_tree_guerra_upper {n : ℕ} (hn : 0 < n)
    (T : GaussianTree) (hT : ValidTreeGrid 0 T) (d : TreeLeaves T → ℝ) :
    expectedMaximum n+
      (∫ z,finiteMaximum (fun α ↦ linearProcess (treeAuxVector n 0 T) z α+d α)
        ∂gaussianProduct (TreeEdges T))≤
      ∫ z,finiteMaximum (fun α ↦ (∑ i,|leafField (treeFieldVector 0 T) z α i|)+d α)
        ∂gaussianProduct (Fin n × TreeEdges T) := by
  rw [expected_treeAux_eq_tensor n T hT d]
  exact finite_guerra_upper hn (treeFieldVector 0 T) (treeField_unit T hT) d

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma finiteMaximum_prod_curry_left {ι κ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype κ] [Nonempty κ] (f : ι×κ → ℝ) :
    finiteMaximum f=finiteMaximum (fun i ↦ finiteMaximum (fun j ↦ f (i,j))) := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := exists_finiteMaximum f
    rw [←hp]
    exact (le_finiteMaximum (fun j ↦ f (p.1,j)) p.2).trans
      (le_finiteMaximum (fun i ↦ finiteMaximum (fun j ↦ f (i,j))) p.1)
  · obtain ⟨i,hi⟩ := exists_finiteMaximum (fun i ↦ finiteMaximum (fun j ↦ f (i,j)))
    obtain ⟨j,hj⟩ := exists_finiteMaximum (fun j ↦ f (i,j))
    rw [←hi,←hj]
    exact le_finiteMaximum f (i,j)

lemma treeLinear_step (c : ℝ → TreeLevel → ℝ) (q : ℝ) (l : TreeLevel) (T : GaussianTree)
    (z : TreeEdges (l::T) → ℝ) (α : TreeLeaves (l::T)) :
    linearProcess (treePathCoeff c q (l::T)) z α=
      c q l*z (Sum.inl α.1)+linearProcess (treePathCoeff c l.endpoint T)
        (fun e ↦ z (Sum.inr (α.1,e))) α.2 := by
  classical
  change (∑ e : Fin (l.branchExcess+1) ⊕ (Fin (l.branchExcess+1) × TreeEdges T),_)=_
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [treePathCoeff,ite_mul,zero_mul]
  simp [linearProcess]

lemma treePathCoeff_const_q (c : TreeLevel → ℝ) (q r : ℝ) (T : GaussianTree) :
    treePathCoeff (fun _ l ↦ c l) q T=treePathCoeff (fun _ l ↦ c l) r T := by
  induction T with
  | nil => rfl
  | cons l T ih => funext α e; cases e <;> rfl

lemma treeOffset_step (l : TreeLevel) (T : GaussianTree)
    (g : TreeEdges (l::T) → ℝ) (α : TreeLeaves (l::T)) :
    treeOffset (l::T) g α=(g (Sum.inl α.1)-Real.log (l.branchExcess+1 : ℝ))/l.height+
      treeOffset T (fun e ↦ g (Sum.inr (α.1,e))) α.2 := by
  rw [treeOffset,treeLinear_step,treeCenter]
  rw [treePathCoeff_const_q (fun l ↦ 1/l.height) l.endpoint 0 T]
  simp only [treeOffset]
  ring

lemma scalarTreeValue_step (c : ℝ → TreeLevel → ℝ) (q : ℝ) (l : TreeLevel) (T : GaussianTree)
    (z g : TreeEdges (l::T) → ℝ) :
    scalarTreeValue c q (l::T) z g=finiteMaximum (fun i : Fin (l.branchExcess+1) ↦
      c q l*z (Sum.inl i)+scalarTreeValue c l.endpoint T
        (fun e ↦ z (Sum.inr (i,e))) (fun e ↦ g (Sum.inr (i,e)))+
      (g (Sum.inl i)-Real.log (l.branchExcess+1 : ℝ))/l.height) := by
  unfold scalarTreeValue
  change finiteMaximum (fun α : Fin (l.branchExcess+1) × TreeLeaves T ↦ _)=_
  rw [finiteMaximum_prod_curry_left]
  congr 1; funext i
  conv_lhs =>
    arg 1
    ext α
    rw [treeLinear_step c q l T z (i,α),treeOffset_step l T g (i,α)]
  have he (a b d e : ℝ) : a+b+(d+e)=(b+e)+(a+d) := by ring
  conv_lhs =>
    arg 1
    ext α
    rw [he]
  dsimp only
  rw [finiteMaximum_add_const]
  ring

lemma fieldTreeValue_step (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ)
    (z : Fin n × TreeEdges (l::T) → ℝ) (g : TreeEdges (l::T) → ℝ) :
    fieldTreeValue n q (l::T) x z g=finiteMaximum (fun j : Fin (l.branchExcess+1) ↦
      fieldTreeValue n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*z (i,Sum.inl j))
        (fun p ↦ z (p.1,Sum.inr (j,p.2))) (fun e ↦ g (Sum.inr (j,e)))+
      (g (Sum.inl j)-Real.log (l.branchExcess+1 : ℝ))/l.height) := by
  have hh (α : TreeLeaves (l::T)) (i : Fin n) :
      leafField (treeFieldVector q (l::T)) z α i=
      Real.sqrt (l.endpoint-q)*z (i,Sum.inl α.1)+
        leafField (treeFieldVector l.endpoint T) (fun p ↦ z (p.1,Sum.inr (α.1,p.2))) α.2 i := by
    exact treeLinear_step (fun q l ↦ Real.sqrt (l.endpoint-q)) q l T (fun e ↦ z (i,e)) α
  unfold fieldTreeValue
  change finiteMaximum (fun α : Fin (l.branchExcess+1) × TreeLeaves T ↦ _)=_
  rw [finiteMaximum_prod_curry_left]
  congr 1; funext j
  conv_lhs =>
    arg 1
    ext α
    rw [treeOffset_step l T g (j,α)]
    simp only [hh (j,α),←add_assoc]
  dsimp only
  have he (a b d : ℝ) : a+b+d=(a+d)+b := by ring
  conv_lhs =>
    arg 1
    ext α
    rw [he]
  rw [finiteMaximum_add_const]

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_TreeProductLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma measurePreserving_finite_curry {I E A : Type*} [Fintype I] [Fintype E]
    [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun z : I×E → A ↦ fun i e ↦ z (i,e))
      (Measure.pi (fun _ ↦ μ)) (Measure.pi (fun _ : I ↦ Measure.pi (fun _ : E ↦ μ))) := by
  refine ⟨by fun_prop,?_⟩
  have h := Measure.infinitePi_map_curry (fun (_ : I) (_ : E) ↦ μ)
  simp only [Measure.infinitePi_eq_pi,MeasurableEquiv.coe_curry] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rfl

lemma measurePreserving_nodeBlocks {I E A : Type*} [Fintype I] [Fintype E]
    [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun z : I⊕(I×E) → A ↦ fun i ↦ (z (Sum.inl i),fun e ↦ z (Sum.inr (i,e))))
      (Measure.pi (fun _ ↦ μ))
      (Measure.pi (fun _ : I ↦ μ.prod (Measure.pi (fun _ : E ↦ μ)))) := by
  have hsum := measurePreserving_sumPiEquivProdPi (fun _ : I⊕(I×E) ↦ μ)
  have hc := (MeasurePreserving.id (Measure.pi (fun _ : I ↦ μ))).prod
    (measurePreserving_finite_curry (I := I) (E := E) μ)
  have hp := (measurePreserving_arrowProdEquivProdArrow A (E → A) I
    (fun _ ↦ μ) (fun _ ↦ Measure.pi (fun _ : E ↦ μ))).symm
  exact hp.comp (hc.comp hsum)

lemma measurePreserving_midSwap {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (σ : Measure C)
    [SFinite μ] [SFinite ν] [SFinite σ] :
    MeasurePreserving (fun p : (A×B)×C ↦ ((p.1.1,p.2),p.1.2))
      ((μ.prod ν).prod σ) ((μ.prod σ).prod ν) := by
  have h1 := measurePreserving_prodAssoc μ ν σ
  have h2 := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := σ))
  have h3 := (measurePreserving_prodAssoc μ σ ν).symm
  exact h3.comp (h2.comp h1)

lemma gaussianAddLaw_integrable (c : ℝ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) :
    Integrable (fun x : ℝ ↦ x) (gaussianAddLaw c μ) := by
  rw [gaussianAddLaw,integrable_map_measure (by fun_prop) (by fun_prop)]
  exact ((standardGaussian_integrable_id.const_mul c).comp_fst μ).add (hi.comp_snd _)

lemma gaussianAddLaw_exp_integrable (c a : ℝ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ) :
    Integrable (fun x : ℝ ↦ Real.exp (a*x)) (gaussianAddLaw c μ) := by
  rw [gaussianAddLaw,integrable_map_measure (by fun_prop) (by fun_prop)]
  have hg : Integrable (fun z : ℝ ↦ Real.exp ((a*c)*z)) standardGaussian :=
    integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (a*c)
  convert hg.mul_prod hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  dsimp only [Function.comp_def]
  rw [←Real.exp_add]
  congr 1
  ring

lemma gaussianAddLaw_exp (c a : ℝ) {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    (∫ x,Real.exp (a*x) ∂gaussianAddLaw c μ)=
      Real.exp ((a*c)^2/2)*(∫ x,Real.exp (a*x) ∂μ) := by
  rw [gaussianAddLaw,integral_map (by fun_prop) (by fun_prop)]
  have he (p : ℝ×ℝ) : Real.exp (a*(c*p.1+p.2))=
      Real.exp ((a*c)*p.1)*Real.exp (a*p.2) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [integral_prod_mul (fun z : ℝ ↦ Real.exp ((a*c)*z)) (fun x : ℝ ↦ Real.exp (a*x))]
  have heq := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) (a*c)
  simpa [mgf,standardGaussian] using congrArg (fun x ↦ x*(∫ x,Real.exp (a*x) ∂μ)) heq

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

instance scalarTreeLaw_probability (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    IsProbabilityMeasure (scalarTreeLaw c q T) := by
  induction T generalizing q with
  | nil => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | cons l T ih =>
    have := ih l.endpoint
    exact inferInstanceAs (IsProbabilityMeasure
      (branchLaw (gaussianAddLaw (c q l) (scalarTreeLaw c l.endpoint T)) l.height l.branchExcess))

lemma finiteMaximum_const {I : Type*} [Fintype I] [Nonempty I] (a : ℝ) :
    finiteMaximum (fun _ : I ↦ a)=a := by
  obtain ⟨i,hi⟩ := exists_finiteMaximum (fun _ : I ↦ a)
  exact hi.symm

lemma scalarTreeEval_nil (c : ℝ → TreeLevel → ℝ) (q : ℝ) (w : TreeEdges [] → ℝ×ℝ) :
    scalarTreeEval c q [] w=0 := by
  simp only [scalarTreeEval,scalarTreeValue,treeOffset,treeCenter,linearProcess]
  simp only [show ∀ f : PEmpty → ℝ, (∑ e,f e)=0 from fun f ↦ Fintype.sum_empty f,
    sub_self,zero_add,finiteMaximum_const]

lemma continuous_scalarTreeEval (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    Continuous (scalarTreeEval c q T) := by
  unfold scalarTreeEval scalarTreeValue treeOffset
  apply continuous_finiteMaximum.comp
  apply continuous_pi
  intro α
  unfold linearProcess
  fun_prop

lemma marked_gaussianAddLaw {S : Type*} [MeasurableSpace S] (σ : Measure S) [IsProbabilityMeasure σ]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : S → ℝ}
    (hf : MeasurePreserving f σ μ) (c : ℝ) :
    MeasurePreserving (fun p : (ℝ×ℝ)×S ↦ (c*p.1.1+f p.2,p.1.2))
      (edgeNoiseLaw.prod σ) ((gaussianAddLaw c μ).prod gumbelLaw) := by
  have hadd : MeasurePreserving (fun p : ℝ×ℝ ↦ c*p.1+p.2)
      (standardGaussian.prod μ) (gaussianAddLaw c μ) := ⟨by fun_prop,rfl⟩
  exact ((hadd.prod (MeasurePreserving.id gumbelLaw)).comp
    (((MeasurePreserving.id standardGaussian).prod hf).prod (MeasurePreserving.id gumbelLaw))).comp
    (measurePreserving_midSwap standardGaussian gumbelLaw σ)

lemma scalarTreeEval_step (c : ℝ → TreeLevel → ℝ) (q : ℝ) (l : TreeLevel) (T : GaussianTree)
    (w : TreeEdges (l::T) → ℝ×ℝ) :
    scalarTreeEval c q (l::T) w=branchMax l.height l.branchExcess
      ((fun i ↦ c q l*(w (Sum.inl i)).1+
        scalarTreeEval c l.endpoint T (fun e ↦ w (Sum.inr (i,e)))),
       fun i ↦ (w (Sum.inl i)).2) := by
  rw [scalarTreeEval,scalarTreeValue_step]
  unfold branchMax
  have he (i : Fin (l.branchExcess+1)) :
      c q l*(w (Sum.inl i)).1+scalarTreeEval c l.endpoint T (fun e ↦ w (Sum.inr (i,e)))+
        ((w (Sum.inl i)).2-Real.log (l.branchExcess+1 : ℝ))/l.height=
      (c q l*(w (Sum.inl i)).1+scalarTreeEval c l.endpoint T (fun e ↦ w (Sum.inr (i,e)))+
        (w (Sum.inl i)).2/l.height)+(-Real.log (l.branchExcess+1 : ℝ)/l.height) := by ring
  change finiteMaximum (fun i ↦ c q l*(w (Sum.inl i)).1+
    scalarTreeEval c l.endpoint T (fun e ↦ w (Sum.inr (i,e)))+
      ((w (Sum.inl i)).2-Real.log (l.branchExcess+1 : ℝ))/l.height)=_
  conv_lhs => arg 1; ext i; rw [he i]
  rw [finiteMaximum_add_const]
  ring

theorem scalarTreeEval_law (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    MeasurePreserving (scalarTreeEval c q T) (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw))
      (scalarTreeLaw c q T) := by
  induction T generalizing q with
  | nil =>
    have he : scalarTreeEval c q []=fun _ ↦ (0 : ℝ) := funext (scalarTreeEval_nil c q)
    rw [he,scalarTreeLaw]
    exact ⟨measurable_const,by simp⟩
  | cons l T ih =>
    let ν := gaussianAddLaw (c q l) (scalarTreeLaw c l.endpoint T)
    have hblock := measurePreserving_nodeBlocks (I := Fin (l.branchExcess+1)) (E := TreeEdges T) edgeNoiseLaw
    have hchild := marked_gaussianAddLaw (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw)) (ih l.endpoint) (c q l)
    have hchildren := measurePreserving_pi (fun _ : Fin (l.branchExcess+1) ↦
      edgeNoiseLaw.prod (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw)))
      (fun _ ↦ ν.prod gumbelLaw) (fun _ ↦ hchild)
    have hpair := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (l.branchExcess+1))
      (fun _ ↦ ν) (fun _ ↦ gumbelLaw)
    have hmax : MeasurePreserving (branchMax l.height l.branchExcess)
        ((Measure.pi (fun _ : Fin (l.branchExcess+1) ↦ ν)).prod
          (Measure.pi (fun _ : Fin (l.branchExcess+1) ↦ gumbelLaw)))
        (scalarTreeLaw c q (l::T)) := ⟨(continuous_branchMax _ _).measurable,rfl⟩
    have hall := hmax.comp (hpair.comp (hchildren.comp hblock))
    convert hall using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    exact scalarTreeEval_step c q l T w

lemma scalarTreeLaw_integrable (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    Integrable (fun x : ℝ ↦ x) (scalarTreeLaw c q T) := by
  induction T generalizing q with
  | nil =>
    change Integrable (fun x : ℝ ↦ x) (Measure.dirac (0 : ℝ))
    exact integrable_dirac (by simp)
  | cons l T ih => exact branchLaw_integrable (gaussianAddLaw_integrable _ (ih l.endpoint)) _ _

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_CascadeMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

instance cascadeLaw_probability (L : CascadeShape) (w : CascadeWidths L) :
    IsProbabilityMeasure (cascadeLaw L w) := by
  induction L with
  | nil => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : ℝ)))
  | cons p L ih =>
    have := ih w.2
    exact inferInstanceAs (IsProbabilityMeasure (branchLaw (gaussianAddLaw p.1 (cascadeLaw L w.2)) p.2 w.1))

lemma branchLaw_exp_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a m : ℝ} (ha : 0 ≤ a) (ham : a/m < 1)
    (he : Integrable (fun x : ℝ ↦ Real.exp (a*x)) μ) (b : ℕ) :
    Integrable (fun x : ℝ ↦ Real.exp (a*x)) (branchLaw μ m b) := by
  rw [branchLaw,integrable_map_measure (by fun_prop) (continuous_branchMax m b).measurable.aemeasurable]
  exact branchMax_exp_integrable ha ham he b

lemma cascadeMoment_pos {L : CascadeShape} {a : ℝ} (h : CascadeScale a L) :
    0 < cascadeMoment a L := by
  induction L generalizing a with
  | nil => exact zero_lt_one
  | cons p L ih =>
    obtain ⟨ha,ham,hL⟩ := h
    have hm : 0 < p.2 := ha.trans_lt ham
    exact mul_pos (gumbelExpMoment_pos ((div_lt_one hm).mpr ham))
      (Real.rpow_pos_of_pos (mul_pos (Real.exp_pos _) (ih hL)) _)

lemma cascadeLaw_integrable (L : CascadeShape) (w : CascadeWidths L) :
    Integrable (fun x : ℝ ↦ x) (cascadeLaw L w) := by
  induction L with
  | nil =>
    apply integrable_dirac
    simp
  | cons p L ih => exact branchLaw_integrable (gaussianAddLaw_integrable _ (ih w.2)) _ _

lemma cascadeLaw_exp_integrable {L : CascadeShape} {a : ℝ} (h : CascadeScale a L)
    (w : CascadeWidths L) : Integrable (fun x : ℝ ↦ Real.exp (a*x)) (cascadeLaw L w) := by
  induction L generalizing a with
  | nil =>
    apply integrable_dirac
    simp
  | cons p L ih =>
    obtain ⟨ha,ham,hL⟩ := h
    have hm : 0 < p.2 := ha.trans_lt ham
    have he := gaussianAddLaw_exp_integrable p.1 p.2 (ih hL w.2)
    exact branchLaw_exp_integrable ha ((div_lt_one hm).mpr ham)
      (integrable_exp_smaller ha ham.le he) w.1

theorem cascadeMoment_mem_closure {L : CascadeShape} {a : ℝ} (h : CascadeScale a L) :
    cascadeMoment a L ∈ closure (range (fun w : CascadeWidths L ↦
      ∫ x,Real.exp (a*x) ∂cascadeLaw L w)) := by
  induction L generalizing a with
  | nil =>
    apply subset_closure
    exact ⟨PUnit.unit,by simp [cascadeLaw,cascadeMoment]⟩
  | cons p L ih =>
    obtain ⟨ha,ham,hL⟩ := h
    have hm : 0 < p.2 := ha.trans_lt ham
    let f : ℝ → ℝ := fun y ↦ gumbelExpMoment (a/p.2)*(Real.exp ((p.2*p.1)^2/2)*y)^(a/p.2)
    have hf : ContinuousAt f (cascadeMoment p.2 L) :=
      continuousAt_const.mul ((continuousAt_const.mul continuousAt_id).rpow_const (Or.inr (div_nonneg ha hm.le)))
    have hh := mem_closure_image hf (ih hL)
    apply (closure_minimal (t := closure (range (fun w : CascadeWidths (p::L) ↦
      ∫ x,Real.exp (a*x) ∂cascadeLaw (p::L) w))) ?_ isClosed_closure) hh
    rintro y ⟨z,⟨w,rfl⟩,rfl⟩
    have he := gaussianAddLaw_exp_integrable p.1 p.2 (cascadeLaw_exp_integrable hL w)
    have ht := branchLaw_exp_tendsto hm ha ham he
    rw [gaussianAddLaw_exp] at ht
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun b ↦ ⟨(b,w),rfl⟩))

theorem cascadeMean_mem_closure {L : CascadeShape} (h : CascadeScale 0 L) :
    cascadeMean L ∈ closure (range (fun w : CascadeWidths L ↦ ∫ x,x ∂cascadeLaw L w)) := by
  cases L with
  | nil =>
    apply subset_closure
    exact ⟨PUnit.unit,by simp [cascadeLaw,cascadeMean]⟩
  | cons p L =>
    obtain ⟨_,hm,hL⟩ := h
    let f : ℝ → ℝ := fun y ↦ gumbelMean/p.2+Real.log (Real.exp ((p.2*p.1)^2/2)*y)/p.2
    have hf : ContinuousAt f (cascadeMoment p.2 L) := by
      apply continuousAt_const.add
      apply ContinuousAt.div_const
      apply ContinuousAt.log (continuousAt_const.mul continuousAt_id)
      exact (mul_pos (Real.exp_pos _) (cascadeMoment_pos hL)).ne'
    have hh := mem_closure_image hf (cascadeMoment_mem_closure hL)
    apply (closure_minimal (t := closure (range (fun w : CascadeWidths (p::L) ↦
      ∫ x,x ∂cascadeLaw (p::L) w))) ?_ isClosed_closure) hh
    rintro y ⟨z,⟨w,rfl⟩,rfl⟩
    have he := gaussianAddLaw_exp_integrable p.1 p.2 (cascadeLaw_exp_integrable hL w)
    have ht := branchLaw_mean_tendsto (gaussianAddLaw_integrable _ (cascadeLaw_integrable L w)) hm he
    rw [gaussianAddLaw_exp] at ht
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun b ↦ ⟨(b,w),rfl⟩))

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_FieldTreeLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma continuous_fieldTreeEval (n : ℕ) (q : ℝ) (T : GaussianTree) :
    Continuous (fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦ fieldTreeEval n q T p.1 p.2) := by
  unfold fieldTreeEval fieldTreeValue treeOffset leafField linearProcess
  apply continuous_finiteMaximum.comp
  apply continuous_pi
  intro α
  fun_prop

lemma fieldTreeEval_nil (n : ℕ) (q : ℝ) (x : Fin n → ℝ) (w : TreeEdges [] → (Fin n → ℝ)×ℝ) :
    fieldTreeEval n q [] x w=∑ i,|x i| := by
  simp only [fieldTreeEval,fieldTreeValue,treeOffset,treeCenter,linearProcess,leafField]
  simp only [show ∀ f : PEmpty → ℝ, (∑ e,f e)=0 from fun f ↦ Fintype.sum_empty f,
    sub_self,add_zero,finiteMaximum_const]

lemma continuous_fieldChild (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) :
    Continuous (fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦
      fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i) p.2) := by
  have hc : Continuous (fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦
      ((fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i),p.2)) := by
    apply Continuous.prodMk _ continuous_snd
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_const.mul ((continuous_apply i).comp continuous_fst))
  exact (continuous_fieldTreeEval n l.endpoint T).comp hc

instance fieldChildLaw_probability (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) :
    IsProbabilityMeasure (fieldChildLaw n q l T x) := by
  unfold fieldChildLaw
  exact Measure.isProbabilityMeasure_map (continuous_fieldChild n q l T x).measurable.aemeasurable

lemma fieldTreeEval_step (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ)
    (w : TreeEdges (l::T) → (Fin n → ℝ)×ℝ) :
    fieldTreeEval n q (l::T) x w=branchMax l.height l.branchExcess
      ((fun j ↦ fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*(w (Sum.inl j)).1 i)
        (fun e ↦ w (Sum.inr (j,e)))),fun j ↦ (w (Sum.inl j)).2) := by
  rw [fieldTreeEval,fieldTreeValue_step]
  unfold branchMax
  have he (a b : ℝ) : a+(b-Real.log (l.branchExcess+1 : ℝ))/l.height=
      (a+b/l.height)+(-Real.log (l.branchExcess+1 : ℝ)/l.height) := by ring
  conv_lhs => arg 1; ext j; rw [he]
  rw [finiteMaximum_add_const]
  simp only [fieldTreeEval,sub_eq_add_neg,neg_div]

lemma fieldTreeEval_law_step (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) :
    MeasurePreserving (fieldTreeEval n q (l::T) x)
      (Measure.pi (fun _ : TreeEdges (l::T) ↦ fieldNoiseLaw n))
      (branchLaw (fieldChildLaw n q l T x) l.height l.branchExcess) := by
  let σ := Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)
  have hc : MeasurePreserving (fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦
      fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i) p.2)
      ((gaussianProduct (Fin n)).prod σ) (fieldChildLaw n q l T x) :=
    ⟨(continuous_fieldChild n q l T x).measurable,rfl⟩
  have hb := (hc.prod (MeasurePreserving.id gumbelLaw)).comp
    (measurePreserving_midSwap (gaussianProduct (Fin n)) gumbelLaw σ)
  have hblocks := measurePreserving_nodeBlocks (I := Fin (l.branchExcess+1)) (E := TreeEdges T) (fieldNoiseLaw n)
  have hchildren := measurePreserving_pi (fun _ : Fin (l.branchExcess+1) ↦
    (fieldNoiseLaw n).prod σ) (fun _ ↦ (fieldChildLaw n q l T x).prod gumbelLaw) (fun _ ↦ hb)
  have hp := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (l.branchExcess+1))
    (fun _ ↦ fieldChildLaw n q l T x) (fun _ ↦ gumbelLaw)
  have hmax : MeasurePreserving (branchMax l.height l.branchExcess)
      ((Measure.pi (fun _ : Fin (l.branchExcess+1) ↦ fieldChildLaw n q l T x)).prod
        (Measure.pi (fun _ : Fin (l.branchExcess+1) ↦ gumbelLaw)))
      (branchLaw (fieldChildLaw n q l T x) l.height l.branchExcess) :=
    ⟨(continuous_branchMax _ _).measurable,rfl⟩
  have hall := hmax.comp (hp.comp (hchildren.comp hblocks))
  convert hall using 1
  all_goals try with_reducible_and_instances rfl
  funext w
  exact fieldTreeEval_step n q l T x w

lemma fieldTreeEval_integrable (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ) :
    Integrable (fieldTreeEval n q T x) (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) := by
  have hz (e : TreeEdges T) (i : Fin n) : Integrable (fun w : TreeEdges T → (Fin n → ℝ)×ℝ ↦ (w e).1 i)
      (Measure.pi (fun _ ↦ fieldNoiseLaw n)) := by
    have h := ((measurePreserving_eval (fun _ : Fin n ↦ standardGaussian) i).integrable_comp (by fun_prop)).mpr
      standardGaussian_integrable_id
    exact (measurePreserving_eval (fun _ : TreeEdges T ↦ fieldNoiseLaw n) e).integrable_comp (by fun_prop)
      |>.mpr (h.comp_fst gumbelLaw)
  have hg (e : TreeEdges T) : Integrable (fun w : TreeEdges T → (Fin n → ℝ)×ℝ ↦ (w e).2)
      (Measure.pi (fun _ ↦ fieldNoiseLaw n)) :=
    (measurePreserving_eval (fun _ : TreeEdges T ↦ fieldNoiseLaw n) e).integrable_comp (by fun_prop)
      |>.mpr (gumbel_integrable.comp_snd (gaussianProduct (Fin n)))
  unfold fieldTreeEval fieldTreeValue
  apply integrable_finiteMaximum_of_integrable
  intro α
  apply Integrable.add
  · apply integrable_finsetSum
    intro i _
    apply Integrable.abs
    apply Integrable.add (integrable_const _)
    unfold leafField
    apply integrable_finsetSum
    intro e _
    exact (hz e i).const_mul _
  · unfold treeOffset linearProcess
    apply Integrable.sub _ (integrable_const _)
    apply integrable_finsetSum
    intro e _
    exact (hg e).const_mul _

lemma fieldTreeEval_comp_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] (n : ℕ) (q : ℝ) (T : GaussianTree)
    (x : Ω → Fin n → ℝ) (w : Ω → TreeEdges T → (Fin n → ℝ)×ℝ)
    (hx : ∀ i,Integrable (fun ω ↦ x ω i) μ)
    (hz : ∀ e i,Integrable (fun ω ↦ (w ω e).1 i) μ)
    (hg : ∀ e,Integrable (fun ω ↦ (w ω e).2) μ) :
    Integrable (fun ω ↦ fieldTreeEval n q T (x ω) (w ω)) μ := by
  unfold fieldTreeEval fieldTreeValue
  apply integrable_finiteMaximum_of_integrable
  intro α
  apply Integrable.add
  · apply integrable_finsetSum
    intro i _
    apply Integrable.abs
    apply Integrable.add (hx i)
    unfold leafField
    apply integrable_finsetSum
    intro e _
    exact (hz e i).const_mul _
  · unfold treeOffset linearProcess
    apply Integrable.sub _ (integrable_const _)
    apply integrable_finsetSum
    intro e _
    exact (hg e).const_mul _

lemma fieldChildLaw_integrable (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ) :
    Integrable (fun y : ℝ ↦ y) (fieldChildLaw n q l T x) := by
  rw [fieldChildLaw,integrable_map_measure (by fun_prop) (continuous_fieldChild n q l T x).measurable.aemeasurable]
  apply fieldTreeEval_comp_integrable
  · intro i
    apply Integrable.add (integrable_const _)
    exact ((integrable_comp_eval (μ := fun _ : Fin n ↦ standardGaussian) standardGaussian_integrable_id).const_mul _).comp_fst _
  · intro e i
    have h : Integrable (fun w : TreeEdges T → (Fin n → ℝ)×ℝ ↦ (w e).1 i)
        (Measure.pi (fun _ ↦ fieldNoiseLaw n)) :=
      (integrable_comp_eval (μ := fun _ : TreeEdges T ↦ fieldNoiseLaw n)
        ((integrable_comp_eval (μ := fun _ : Fin n ↦ standardGaussian) (i := i) standardGaussian_integrable_id).comp_fst gumbelLaw))
    exact h.comp_snd _
  · intro e
    have h : Integrable (fun w : TreeEdges T → (Fin n → ℝ)×ℝ ↦ (w e).2)
        (Measure.pi (fun _ ↦ fieldNoiseLaw n)) :=
      integrable_comp_eval (gumbel_integrable.comp_snd (gaussianProduct (Fin n)))
    exact h.comp_snd _

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_RandomGuerra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma scalar_pairing_law (T : GaussianTree) :
    MeasurePreserving (fun p : (TreeEdges T → ℝ)×(TreeEdges T → ℝ) ↦ fun e ↦ (p.1 e,p.2 e))
      ((gaussianProduct (TreeEdges T)).prod (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw)))
      (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw)) :=
  (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (TreeEdges T)
    (fun _ ↦ standardGaussian) (fun _ ↦ gumbelLaw)).symm

lemma field_pairing_law (n : ℕ) (T : GaussianTree) :
    MeasurePreserving (fun p : (Fin n×TreeEdges T → ℝ)×(TreeEdges T → ℝ) ↦ fun e ↦ ((fun i ↦ p.1 (i,e)),p.2 e))
      ((gaussianProduct (Fin n×TreeEdges T)).prod (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw)))
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) := by
  have hs := measurePreserving_piCongrLeft (fun _ : TreeEdges T×Fin n ↦ standardGaussian)
    (Equiv.prodComm (Fin n) (TreeEdges T))
  have hc := (measurePreserving_finite_curry (I := TreeEdges T) (E := Fin n) standardGaussian).comp hs
  have hp := (measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) ℝ (TreeEdges T)
    (fun _ ↦ gaussianProduct (Fin n)) (fun _ ↦ gumbelLaw)).symm
  exact hp.comp (hc.prod (MeasurePreserving.id (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))))

lemma scalarTreeEval_integrable (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    Integrable (scalarTreeEval c q T) (Measure.pi (fun _ : TreeEdges T ↦ edgeNoiseLaw)) :=
  (scalarTreeEval_law c q T).integrable_comp aestronglyMeasurable_id |>.mpr (scalarTreeLaw_integrable c q T)

lemma scalarTreeValue_integrable_prod (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    Integrable (fun p : (TreeEdges T → ℝ)×(TreeEdges T → ℝ) ↦ scalarTreeValue c q T p.1 p.2)
      ((gaussianProduct (TreeEdges T)).prod (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))) := by
  exact (scalar_pairing_law T).integrable_comp (continuous_scalarTreeEval c q T).aestronglyMeasurable
    |>.mpr (scalarTreeEval_integrable c q T)

lemma fieldTreeValue_integrable_prod (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ) :
    Integrable (fun p : (Fin n×TreeEdges T → ℝ)×(TreeEdges T → ℝ) ↦ fieldTreeValue n q T x p.1 p.2)
      ((gaussianProduct (Fin n×TreeEdges T)).prod (Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))) := by
  have hc : Continuous (fieldTreeEval n q T x) :=
    (continuous_fieldTreeEval n q T).comp (continuous_const.prodMk continuous_id)
  exact (field_pairing_law n T).integrable_comp hc.aestronglyMeasurable
    |>.mpr (fieldTreeEval_integrable n q T x)

lemma scalarTreeValue_mean (c : ℝ → TreeLevel → ℝ) (q : ℝ) (T : GaussianTree) :
    (∫ g,∫ z,scalarTreeValue c q T z g ∂gaussianProduct (TreeEdges T)
      ∂Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))=∫ y,y ∂scalarTreeLaw c q T := by
  rw [←integral_prod_symm _ (scalarTreeValue_integrable_prod c q T)]
  have hcomp := (scalarTreeEval_law c q T).comp (scalar_pairing_law T)
  have he := hcomp.hasLaw.integral_comp aestronglyMeasurable_id
  exact he

lemma fieldTreeValue_mean (n : ℕ) (q : ℝ) (T : GaussianTree) (x : Fin n → ℝ) :
    (∫ g,∫ z,fieldTreeValue n q T x z g ∂gaussianProduct (Fin n×TreeEdges T)
      ∂Measure.pi (fun _ : TreeEdges T ↦ gumbelLaw))=
      ∫ w,fieldTreeEval n q T x w ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n) := by
  rw [←integral_prod_symm _ (fieldTreeValue_integrable_prod n q T x)]
  have hc : Continuous (fieldTreeEval n q T x) :=
    (continuous_fieldTreeEval n q T).comp (continuous_const.prodMk continuous_id)
  exact (field_pairing_law n T).hasLaw.integral_comp hc.aestronglyMeasurable

theorem randomized_tree_guerra_upper {n : ℕ} (hn : 0 < n) (T : GaussianTree) (hT : ValidTreeGrid 0 T) :
    expectedMaximum n+(∫ y,y ∂scalarTreeLaw (fun q l ↦ Real.sqrt ((n : ℝ)/2)*Real.sqrt (l.endpoint^2-q^2)) 0 T) ≤
      ∫ w,fieldTreeEval n 0 T (fun _ ↦ 0) w ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n) := by
  let c : ℝ → TreeLevel → ℝ := fun q l ↦ Real.sqrt ((n : ℝ)/2)*Real.sqrt (l.endpoint^2-q^2)
  have hiA := scalarTreeValue_integrable_prod c 0 T
  have hiF := fieldTreeValue_integrable_prod n 0 T (fun _ ↦ 0)
  have hg : ∀ g : TreeEdges T → ℝ, expectedMaximum n+
      (∫ z,scalarTreeValue c 0 T z g ∂gaussianProduct (TreeEdges T)) ≤
      ∫ z,fieldTreeValue n 0 T (fun _ ↦ 0) z g ∂gaussianProduct (Fin n×TreeEdges T) := by
    intro g
    simpa only [scalarTreeValue,fieldTreeValue,zero_add,treeAuxVector,c] using
      finite_tree_guerra_upper hn T hT (treeOffset T g)
  have hu := integral_mono ((integrable_const (expectedMaximum n)).add hiA.integral_prod_right)
    hiF.integral_prod_right hg
  simp only [Pi.add_apply] at hu
  rw [integral_add (integrable_const _) hiA.integral_prod_right,integral_const,probReal_univ,one_smul,
    scalarTreeValue_mean,fieldTreeValue_mean] at hu
  exact hu

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma coleHopf_one_sided {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {m : ℝ} (hm : 0 < m)
    (h x y : ℝ) : SKValue.coleHopf m h ψ x ≤ SKValue.coleHopf m h ψ y+|x-y| := by
  have hiX := SKValue.lipschitz_exp_integrable hψ hm.le x (Real.sqrt h)
  have hiY := SKValue.lipschitz_exp_integrable hψ hm.le y (Real.sqrt h)
  have hpX := SKValue.lipschitz_exp_integral_pos hψ hm.le x (Real.sqrt h)
  have hpY := SKValue.lipschitz_exp_integral_pos hψ hm.le y (Real.sqrt h)
  have e : SKValue.standardGaussian=standardGaussian := rfl
  rw [e] at hiX hiY hpX hpY
  have hbound : (∫ z,Real.exp (m*ψ (x+Real.sqrt h*z)) ∂standardGaussian) ≤
      Real.exp (m*|x-y|)*(∫ z,Real.exp (m*ψ (y+Real.sqrt h*z)) ∂standardGaussian) := by
    rw [←integral_const_mul]
    apply integral_mono hiX (hiY.const_mul _)
    intro z
    have hl := hψ.dist_le_mul (x+Real.sqrt h*z) (y+Real.sqrt h*z)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hl
    rw [show x+Real.sqrt h*z-(y+Real.sqrt h*z)=x-y by ring] at hl
    dsimp only
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := le_abs_self (ψ (x+Real.sqrt h*z)-ψ (y+Real.sqrt h*z))
    nlinarith
  have hh := Real.log_le_log hpX hbound
  rw [Real.log_mul (Real.exp_pos _).ne' hpY.ne',Real.log_exp] at hh
  simp only [SKValue.coleHopf,ite_eq_right hm.ne',SKValue.heat,e]
  apply (div_le_iff₀ hm).mpr
  have he : (Real.log (∫ z,Real.exp (m*ψ (y+Real.sqrt h*z)) ∂standardGaussian)/m+|x-y|)*m=
      m*|x-y|+Real.log (∫ z,Real.exp (m*ψ (y+Real.sqrt h*z)) ∂standardGaussian) := by field_simp; ring
  rw [he]
  exact hh

lemma coleHopf_lipschitz {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {m : ℝ} (hm : 0 < m)
    (h : ℝ) : LipschitzWith 1 (SKValue.coleHopf m h ψ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul,Real.dist_eq]
  have hxy := coleHopf_one_sided hψ hm h x y
  have hyx := coleHopf_one_sided hψ hm h y x
  rw [abs_sub_comm y x] at hyx
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma fieldProfile_lipschitz {T : GaussianTree} {a : ℝ} (h : TreeScale a T) (q : ℝ) :
    LipschitzWith 1 (fieldProfile q T) := by
  induction T generalizing a q with
  | nil =>
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [fieldProfile,NNReal.coe_one,one_mul,Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y
  | cons l T ih =>
    obtain ⟨ha,ham,hT⟩ := h
    exact coleHopf_lipschitz (ih hT _) (ha.trans_lt ham) _

lemma gaussian_exp_sum_profile_integrable {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {m : ℝ} (hm : 0 ≤ m) (n : ℕ) (x : Fin n → ℝ) (s : ℝ) :
    Integrable (fun z : Fin n → ℝ ↦ Real.exp (m*∑ i,ψ (x i+s*z i))) (gaussianProduct (Fin n)) := by
  have hi := Integrable.fintype_prod (fun i : Fin n ↦ SKValue.lipschitz_exp_integrable hψ hm (x i) s)
  convert hi using 1
  · funext z
    simp only [Finset.mul_sum,Real.exp_sum]
  · rfl

lemma gaussian_exp_sum_coleHopf {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ)
    {m : ℝ} (hm : 0 < m) (n : ℕ) (x : Fin n → ℝ) (h : ℝ) :
    (∫ z : Fin n → ℝ,Real.exp (m*∑ i,ψ (x i+Real.sqrt h*z i)) ∂gaussianProduct (Fin n))=
      Real.exp (m*∑ i,SKValue.coleHopf m h ψ (x i)) := by
  simp only [Finset.mul_sum,Real.exp_sum]
  rw [gaussianProduct,integral_fintype_prod_eq_prod (fun i : Fin n ↦ fun z : ℝ ↦ Real.exp (m*ψ (x i+Real.sqrt h*z)))]
  apply Finset.prod_congr rfl
  intro i _
  simp only [SKValue.coleHopf,ite_eq_right hm.ne',SKValue.heat]
  rw [mul_div_cancel₀ _ hm.ne',Real.exp_log (SKValue.lipschitz_exp_integral_pos hψ hm.le (x i) (Real.sqrt h))]
  rfl

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_BranchMeanUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma branchMax_gumbelMean {branchExcess : ℕ} (x : Fin (branchExcess+1) → ℝ)
    {m : ℝ} (hm : 0 < m) :
    (∫ z,branchMax m branchExcess (x,z) ∂Measure.pi (fun _ : Fin (branchExcess+1) ↦ gumbelLaw))=
      gumbelMean/m+Real.log ((∑ i,Real.exp (m*x i))/(branchExcess+1 : ℝ))/m := by
  have hi : Integrable (fun z : Fin (branchExcess+1) → ℝ ↦ finiteMaximum (fun i ↦ x i+z i/m))
      (Measure.pi (fun _ : Fin (branchExcess+1) ↦ gumbelLaw)) := by
    apply integrable_finiteMaximum_of_integrable
    intro i
    exact (integrable_const _).add (((measurePreserving_eval (fun _ : Fin (branchExcess+1) ↦ gumbelLaw) i).integrable_comp
      (by fun_prop) |>.mpr gumbel_integrable).div_const m)
  unfold branchMax
  rw [integral_sub hi (integrable_const _)]
  simp only [integral_const,probReal_univ,one_smul]
  have h := centered_gumbel_max x hm
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at h
  rw [add_div] at h
  linarith

theorem branchLaw_mean_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ ↦ x) μ) {m : ℝ} (hm : 0 < m)
    (he : Integrable (fun x : ℝ ↦ Real.exp (m*x)) μ) (b : ℕ) :
    (∫ x,x ∂branchLaw μ m b) ≤ gumbelMean/m+Real.log (∫ x,Real.exp (m*x) ∂μ)/m := by
  let ν := Measure.pi (fun _ : Fin (b+1) ↦ μ)
  let G := Measure.pi (fun _ : Fin (b+1) ↦ gumbelLaw)
  let V := fun x : Fin (b+1) → ℝ ↦ (∑ i,Real.exp (m*x i))/(b+1 : ℝ)
  have hiv : Integrable V ν := by
    apply Integrable.div_const
    apply integrable_finsetSum
    intro i _
    exact (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).integrable_comp (by fun_prop) |>.mpr he
  have hif : Integrable (fun x ↦ ∫ z,branchMax m b (x,z) ∂G) ν :=
    (branchMax_integrable hi m b).integral_prod_left
  have hil : Integrable (fun x ↦ Real.log (V x)) ν := by
    convert (hif.const_mul m).sub (integrable_const gumbelMean) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    dsimp only [G,V,Pi.sub_apply,Pi.mul_apply]
    rw [branchMax_gumbelMean x hm]
    field_simp
    ring
  have hp (x : Fin (b+1) → ℝ) : 0<V x := div_pos (exp_sum_pos _) (by positivity)
  have hv : (∫ x,V x ∂ν)=∫ x,Real.exp (m*x) ∂μ := by
    dsimp only [V]
    rw [integral_div,integral_finsetSum]
    · have hh (i : Fin (b+1)) : (∫ x : Fin (b+1) → ℝ,Real.exp (m*x i) ∂ν)=
          ∫ x,Real.exp (m*x) ∂μ :=
        (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).hasLaw.integral_comp (show AEStronglyMeasurable (fun x : ℝ ↦ Real.exp (m*x)) μ by fun_prop)
      simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      push_cast
      field_simp
    · intro i _
      exact (measurePreserving_eval (fun _ : Fin (b+1) ↦ μ) i).integrable_comp (by fun_prop) |>.mpr he
  have hj := integral_log_le_log_integral hiv hil (Eventually.of_forall hp)
  rw [hv] at hj
  have hid := branchLaw_test hi m b LipschitzWith.id
  simp only [id_eq] at hid
  rw [hid]
  simp_rw [branchMax_gumbelMean _ hm]
  rw [integral_add (integrable_const _) (hil.div_const m), integral_const,integral_div]
  simp only [probReal_univ,one_smul]
  linarith [div_le_div_of_nonneg_right hj hm.le]

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma gumbelTreeMoment_pos {T : GaussianTree} {a : ℝ} (h : TreeScale a T) :
    0 < gumbelTreeMoment a T := by
  induction T generalizing a with
  | nil => exact zero_lt_one
  | cons l T ih =>
    obtain ⟨ha,ham,hT⟩ := h
    have hm : 0 < l.height := ha.trans_lt ham
    exact mul_pos (gumbelExpMoment_pos ((div_lt_one hm).mpr ham)) (Real.rpow_pos_of_pos (ih hT) _)

lemma exp_prod_integrable_of_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν] {f : A×B → ℝ} {H : A → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hpos : ∀ p,0 ≤ f p)
    (hi : ∀ x,Integrable (fun y ↦ f (x,y)) ν) (hH : Integrable H μ)
    (hb : ∀ x,(∫ y,f (x,y) ∂ν) ≤ H x) : Integrable f (μ.prod ν) := by
  apply (integrable_prod_iff hf).mpr
  refine ⟨Eventually.of_forall hi,?_⟩
  have he : (fun x ↦ ∫ y,‖f (x,y)‖ ∂ν)=(fun x ↦ ∫ y,f (x,y) ∂ν) := by
    funext x
    apply integral_congr_ae
    exact Eventually.of_forall (fun y ↦ Real.norm_of_nonneg (hpos (x,y)))
  rw [he]
  apply hH.mono' hf.integral_prod_right'
  exact Eventually.of_forall (fun x ↦ by
    rw [Real.norm_of_nonneg (integral_nonneg (fun y ↦ hpos (x,y)))]
    exact hb x)

lemma fieldChildLaw_exp_bound (n : ℕ) (q : ℝ) (l : TreeLevel) (T : GaussianTree) (x : Fin n → ℝ)
    {ψ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) {m K : ℝ} (hm : 0 < m)
    (hi : ∀ y,Integrable (fun w ↦ Real.exp (m*fieldTreeEval n l.endpoint T y w))
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)))
    (hb : ∀ y,(∫ w,Real.exp (m*fieldTreeEval n l.endpoint T y w)
      ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) ≤ K*Real.exp (m*∑ i,ψ (y i))) :
    Integrable (fun y : ℝ ↦ Real.exp (m*y)) (fieldChildLaw n q l T x) ∧
      (∫ y,Real.exp (m*y) ∂fieldChildLaw n q l T x) ≤ K*Real.exp (m*∑ i,SKValue.coleHopf m (l.endpoint-q) ψ (x i)) := by
  let f := fun p : (Fin n → ℝ)×(TreeEdges T → (Fin n → ℝ)×ℝ) ↦
    Real.exp (m*fieldTreeEval n l.endpoint T (fun i ↦ x i+Real.sqrt (l.endpoint-q)*p.1 i) p.2)
  have hmeas : AEStronglyMeasurable f ((gaussianProduct (Fin n)).prod
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n))) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_fieldChild n q l T x))).aestronglyMeasurable
  have hH := (gaussian_exp_sum_profile_integrable hψ hm.le n x (Real.sqrt (l.endpoint-q))).const_mul K
  have hip : Integrable f ((gaussianProduct (Fin n)).prod
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n))) :=
    exp_prod_integrable_of_bound hmeas (fun p ↦ (Real.exp_pos _).le)
      (fun z ↦ hi (fun i ↦ x i+Real.sqrt (l.endpoint-q)*z i)) hH
      (fun z ↦ hb (fun i ↦ x i+Real.sqrt (l.endpoint-q)*z i))
  constructor
  · rw [fieldChildLaw,integrable_map_measure (by fun_prop) (continuous_fieldChild n q l T x).measurable.aemeasurable]
    exact hip
  · rw [fieldChildLaw,integral_map (continuous_fieldChild n q l T x).measurable.aemeasurable (by fun_prop)]
    rw [integral_prod _ hip]
    have H := integral_mono hip.integral_prod_left hH (fun z ↦ hb (fun i ↦ x i+Real.sqrt (l.endpoint-q)*z i))
    rw [integral_const_mul,gaussian_exp_sum_coleHopf hψ hm n x (l.endpoint-q)] at H
    exact H

theorem fieldTreeEval_moment_bound (n : ℕ) {T : GaussianTree} {a : ℝ} (h : TreeScale a T)
    (q : ℝ) (x : Fin n → ℝ) :
    Integrable (fun w ↦ Real.exp (a*fieldTreeEval n q T x w))
      (Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) ∧
    (∫ w,Real.exp (a*fieldTreeEval n q T x w) ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) ≤
      gumbelTreeMoment a T*Real.exp (a*∑ i,fieldProfile q T (x i)) := by
  induction T generalizing a q x with
  | nil =>
    simp only [fieldTreeEval_nil,gumbelTreeMoment,fieldProfile,one_mul]
    exact ⟨integrable_const _,by simp⟩
  | cons l T ih =>
    obtain ⟨ha,ham,hT⟩ := h
    have hm : 0 < l.height := ha.trans_lt ham
    have hcb := fieldChildLaw_exp_bound n q l T x (fieldProfile_lipschitz hT l.endpoint) hm
      (fun y ↦ (ih hT l.endpoint y).1) (fun y ↦ (ih hT l.endpoint y).2)
    have hp := fieldTreeEval_law_step n q l T x
    constructor
    · exact hp.integrable_comp (by fun_prop) |>.mpr (branchLaw_exp_integrable ha ((div_lt_one hm).mpr ham)
        (integrable_exp_smaller ha ham.le hcb.1) _)
    · have heq := hp.hasLaw.integral_comp (show AEStronglyMeasurable (fun y : ℝ ↦ Real.exp (a*y))
          (branchLaw (fieldChildLaw n q l T x) l.height l.branchExcess) by fun_prop)
      simp only [Function.comp_def] at heq
      rw [heq]
      have hub := branchLaw_exp_upper hm ha ham hcb.1 l.branchExcess
      apply hub.trans
      have kr := Real.rpow_le_rpow (integral_nonneg (fun y ↦ (Real.exp_pos _).le)) hcb.2 (div_nonneg ha hm.le)
      have hh := mul_le_mul_of_nonneg_left kr (gumbelExpMoment_pos ((div_lt_one hm).mpr ham)).le
      rw [Real.mul_rpow (gumbelTreeMoment_pos hT).le (Real.exp_pos _).le,←Real.exp_mul] at hh
      have he : (l.height*(∑ i,SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T) (x i)))*(a/l.height)=
          a*(∑ i,SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T) (x i)) := by field_simp
      rw [he] at hh
      simpa only [gumbelTreeMoment,fieldProfile,mul_assoc] using hh

theorem fieldTreeEval_mean_upper (n : ℕ) {T : GaussianTree} (h : TreeScale 0 T)
    (q : ℝ) (x : Fin n → ℝ) :
    (∫ w,fieldTreeEval n q T x w ∂Measure.pi (fun _ : TreeEdges T ↦ fieldNoiseLaw n)) ≤
      (∑ i,fieldProfile q T (x i))+gumbelTreeMean T := by
  cases T with
  | nil => simp [fieldTreeEval_nil,fieldProfile,gumbelTreeMean]
  | cons l T =>
    obtain ⟨_,hm,hT⟩ := h
    have hcb := fieldChildLaw_exp_bound n q l T x (fieldProfile_lipschitz hT l.endpoint) hm
      (fun y ↦ (fieldTreeEval_moment_bound n hT l.endpoint y).1)
      (fun y ↦ (fieldTreeEval_moment_bound n hT l.endpoint y).2)
    have hp := fieldTreeEval_law_step n q l T x
    have heq := hp.hasLaw.integral_comp (show AEStronglyMeasurable (fun y : ℝ ↦ y)
      (branchLaw (fieldChildLaw n q l T x) l.height l.branchExcess) from aestronglyMeasurable_id)
    simp only [Function.comp_def] at heq
    rw [heq]
    have hu := branchLaw_mean_upper (fieldChildLaw_integrable n q l T x) hm hcb.1 l.branchExcess
    apply hu.trans
    have hpos := integral_exp_pos hcb.1
    have hh := Real.log_le_log hpos hcb.2
    rw [Real.log_mul (gumbelTreeMoment_pos hT).ne' (Real.exp_pos _).ne',Real.log_exp] at hh
    have hd := div_le_div_of_nonneg_right hh hm.le
    dsimp only [fieldProfile,gumbelTreeMean]
    have he : (Real.log (gumbelTreeMoment l.height T)+l.height*(∑ i,SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T) (x i)))/l.height=
        Real.log (gumbelTreeMoment l.height T)/l.height+(∑ i,SKValue.coleHopf l.height (l.endpoint-q) (fieldProfile l.endpoint T) (x i)) := by field_simp
    rw [he] at hd
    linarith

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_TreeWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma resizeTree_valid (n : ℕ) {q : ℝ} {T : GaussianTree} (h : ValidTreeGrid q T)
    (w : CascadeWidths (auxShape n q T)) : ValidTreeGrid q (resizeTree n q T w) := by
  induction T generalizing q with
  | nil => exact h
  | cons l T ih => exact ⟨h.1,ih h.2 w.2⟩

lemma resizeTree_scale (n : ℕ) (q : ℝ) {a : ℝ} {T : GaussianTree} (h : TreeScale a T)
    (w : CascadeWidths (auxShape n q T)) : TreeScale a (resizeTree n q T w) := by
  induction T generalizing a q with
  | nil => exact h
  | cons l T ih => exact ⟨h.1,h.2.1,ih _ h.2.2 w.2⟩

lemma auxShape_scale (n : ℕ) (q : ℝ) {a : ℝ} {T : GaussianTree} (h : TreeScale a T) :
    CascadeScale a (auxShape n q T) := by
  induction T generalizing a q with
  | nil => exact h
  | cons l T ih => exact ⟨h.1,h.2.1,ih _ h.2.2⟩

lemma resizeTree_profile (n : ℕ) (q : ℝ) (T : GaussianTree) (w : CascadeWidths (auxShape n q T)) :
    fieldProfile q (resizeTree n q T w)=fieldProfile q T := by
  induction T generalizing q with
  | nil => rfl
  | cons l T ih => simp only [resizeTree,fieldProfile,ih]

lemma resizeTree_gumbelMoment (n : ℕ) (q a : ℝ) (T : GaussianTree) (w : CascadeWidths (auxShape n q T)) :
    gumbelTreeMoment a (resizeTree n q T w)=gumbelTreeMoment a T := by
  induction T generalizing q a with
  | nil => rfl
  | cons l T ih => simp only [resizeTree,gumbelTreeMoment,ih]

lemma resizeTree_gumbelMean (n : ℕ) (q : ℝ) (T : GaussianTree) (w : CascadeWidths (auxShape n q T)) :
    gumbelTreeMean (resizeTree n q T w)=gumbelTreeMean T := by
  cases T with
  | nil => rfl
  | cons l T => simp only [resizeTree,gumbelTreeMean,resizeTree_gumbelMoment]

lemma resizeTree_scalarLaw (n : ℕ) (q : ℝ) (T : GaussianTree) (w : CascadeWidths (auxShape n q T)) :
    scalarTreeLaw (auxAmplitude n) q (resizeTree n q T w)=cascadeLaw (auxShape n q T) w := by
  induction T generalizing q with
  | nil => rfl
  | cons l T ih => simp only [resizeTree,scalarTreeLaw,auxShape,cascadeLaw,ih,auxAmplitude]

lemma auxAmplitude_sq (n : ℕ) {q : ℝ} {l : TreeLevel} (hq : 0 ≤ q) (hql : q ≤ l.endpoint) :
    (auxAmplitude n q l)^2=(n : ℝ)/2*(l.endpoint^2-q^2) := by
  have hl := hq.trans hql
  have hs : 0 ≤ l.endpoint^2-q^2 := by nlinarith
  rw [auxAmplitude,mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hs]

lemma auxShape_moment (n : ℕ) {q a : ℝ} {T : GaussianTree} (hq : 0 ≤ q)
    (hgrid : ValidTreeGrid q T) (h : TreeScale a T) :
    cascadeMoment a (auxShape n q T)=gumbelTreeMoment a T*Real.exp (a*(n : ℝ)*treeCorrection q T) := by
  induction T generalizing q a with
  | nil => simp [auxShape,cascadeMoment,gumbelTreeMoment,treeCorrection]
  | cons l T ih =>
    obtain ⟨ha,ham,hT⟩ := h
    have hm : 0 < l.height := ha.trans_lt ham
    have hs := auxAmplitude_sq n hq hgrid.1
    rw [auxShape,cascadeMoment,ih (hq.trans hgrid.1) hgrid.2 hT]
    rw [mul_pow,hs]
    have he : Real.exp (l.height^2*((n : ℝ)/2*(l.endpoint^2-q^2))/2)*
        (gumbelTreeMoment l.height T*Real.exp (l.height*(n : ℝ)*treeCorrection l.endpoint T))=
        gumbelTreeMoment l.height T*Real.exp (l.height*(n : ℝ)*treeCorrection q (l::T)) := by
      rw [mul_left_comm,←Real.exp_add]
      congr 2
      simp only [treeCorrection]
      ring
    rw [he,Real.mul_rpow (gumbelTreeMoment_pos hT).le (Real.exp_pos _).le,←Real.exp_mul]
    have he2 : l.height*(n : ℝ)*treeCorrection q (l::T)*(a/l.height)=a*(n : ℝ)*treeCorrection q (l::T) := by
      field_simp
    rw [he2]
    simp only [gumbelTreeMoment,mul_assoc]

lemma auxShape_mean (n : ℕ) {q : ℝ} {T : GaussianTree} (hq : 0 ≤ q)
    (hgrid : ValidTreeGrid q T) (h : TreeScale 0 T) :
    cascadeMean (auxShape n q T)=gumbelTreeMean T+(n : ℝ)*treeCorrection q T := by
  cases T with
  | nil => simp [auxShape,cascadeMean,gumbelTreeMean,treeCorrection]
  | cons l T =>
    obtain ⟨_,hm,hT⟩ := h
    have hs := auxAmplitude_sq n hq hgrid.1
    rw [auxShape,cascadeMean,auxShape_moment n (hq.trans hgrid.1) hgrid.2 hT]
    rw [Real.log_mul (Real.exp_pos _).ne' (mul_pos (gumbelTreeMoment_pos hT) (Real.exp_pos _)).ne',
      Real.log_exp,Real.log_mul (gumbelTreeMoment_pos hT).ne' (Real.exp_pos _).ne',Real.log_exp]
    rw [mul_pow,hs]
    simp only [gumbelTreeMean,treeCorrection]
    field_simp
    ring

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_CascadePassage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

theorem finite_step_guerra_upper {n : ℕ} (hn : 0 < n) (T : GaussianTree)
    (hgrid : ValidTreeGrid 0 T) (hscale : TreeScale 0 T) :
    expectedMaximum n ≤ (n : ℝ)*(fieldProfile 0 T 0-treeCorrection 0 T) := by
  have hm := cascadeMean_mem_closure (auxShape_scale n 0 hscale)
  have hh : closure (range (fun w : CascadeWidths (auxShape n 0 T) ↦
      ∫ y,y ∂cascadeLaw (auxShape n 0 T) w)) ⊆
      {y : ℝ | expectedMaximum n+y ≤ (n : ℝ)*fieldProfile 0 T 0+gumbelTreeMean T} := by
    apply closure_minimal
    · rintro y ⟨w,rfl⟩
      have hu := randomized_tree_guerra_upper hn (resizeTree n 0 T w) (resizeTree_valid n hgrid w)
      change expectedMaximum n+(∫ y,y ∂scalarTreeLaw (auxAmplitude n) 0 (resizeTree n 0 T w))≤_ at hu
      rw [resizeTree_scalarLaw] at hu
      have hf := fieldTreeEval_mean_upper n (resizeTree_scale n 0 hscale w) 0 (fun _ ↦ 0)
      rw [resizeTree_profile,resizeTree_gumbelMean] at hf
      simpa only [Set.mem_ofPred_eq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hu.trans hf
    · exact isClosed_le (continuous_const.add continuous_id) continuous_const
  have hf := hh hm
  change expectedMaximum n+cascadeMean (auxShape n 0 T) ≤ (n : ℝ)*fieldProfile 0 T 0+gumbelTreeMean T at hf
  rw [auxShape_mean n (by norm_num) hgrid hscale] at hf
  nlinarith

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma profileTree_valid {q : ℝ} {l : SKValue.HeatProfile} (h : q+SKValue.profileTime l=1) :
    ValidTreeGrid q (profileTree q l) := by
  induction l generalizing q with
  | nil => simpa only [profileTree,ValidTreeGrid,SKValue.profileTime,add_zero] using h
  | cons p l ih =>
    exact ⟨le_add_of_nonneg_right p.1.coe_nonneg,ih (by simpa only [SKValue.profileTime,add_assoc] using h)⟩

lemma profileTree_scale {a q : ℝ} {l : SKValue.HeatProfile} (ha : 0 ≤ a)
    (hl : l.Pairwise (fun p r ↦ p.2 < r.2)) (hb : ∀ p∈l,a<(p.2 : ℝ)) :
    TreeScale a (profileTree q l) := by
  induction l generalizing a q with
  | nil => exact ha
  | cons p l ih =>
    obtain ⟨hpl,hl⟩ := List.pairwise_cons.mp hl
    exact ⟨ha,hb p (List.mem_cons_self ..),ih p.2.coe_nonneg hl (fun r hr ↦ hpl r hr)⟩

lemma coleHopf_mono_lipschitz {ψ χ : ℝ → ℝ} (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    {m : ℝ} (hm : 0 < m) (h : ℝ) (hb : ∀ x,ψ x≤χ x) (x : ℝ) :
    SKValue.coleHopf m h ψ x≤SKValue.coleHopf m h χ x := by
  simp only [SKValue.coleHopf,ite_eq_right hm.ne',SKValue.heat]
  apply div_le_div_of_nonneg_right _ hm.le
  apply Real.log_le_log (SKValue.lipschitz_exp_integral_pos hψ hm.le x (Real.sqrt h))
  apply integral_mono (SKValue.lipschitz_exp_integrable hψ hm.le _ _) (SKValue.lipschitz_exp_integrable hχ hm.le _ _)
  intro z
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (hb _) hm.le

lemma profileTree_le_smooth {ψ : ℝ → ℝ} (hψ : SKValue.SmoothTerminal ψ) (hb : ∀ x,|x|≤ψ x)
    {a q : ℝ} {l : SKValue.HeatProfile} (h : TreeScale a (profileTree q l)) :
    ∀ x,fieldProfile q (profileTree q l) x≤SKValue.profileValue ψ l 0 x := by
  induction l generalizing a q with
  | nil => exact hb
  | cons p l ih =>
    obtain ⟨ha,ham,hT⟩ := h
    have hm : 0<(p.2 : ℝ) := ha.trans_lt ham
    have hχ := (hψ.profile_evolution l).slices 0 ⟨le_rfl,SKValue.profileTime_nonneg l⟩
    intro x
    simp only [profileTree,fieldProfile,SKValue.profileValue,SKValue.patchTime_left _ _ p.1.coe_nonneg,sub_zero,add_sub_cancel_left]
    exact coleHopf_mono_lipschitz (fieldProfile_lipschitz hT _) hχ.lipschitz hm _ (ih hT) x

lemma patchTime_integral {a b : ℝ} (ha : 0≤a) (hb : 0≤b) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 a) (hg : IntervalIntegrable g volume 0 b) :
    (∫ s in (0 : ℝ)..(a+b),SKValue.patchTime a f g s)=(∫ s in (0 : ℝ)..a,f s)+(∫ s in (0 : ℝ)..b,g s) := by
  have hi := SKValue.patchTime_intervalIntegrable ha hb hf hg
  have h1 := hi.mono_set (show uIcc (0 : ℝ) a⊆uIcc (0 : ℝ) (a+b) by
    rw [uIcc_of_le ha,uIcc_of_le (add_nonneg ha hb)]; exact Icc_subset_Icc le_rfl (le_add_of_nonneg_right hb))
  have h2 := hi.mono_set (show uIcc a (a+b)⊆uIcc (0 : ℝ) (a+b) by
    rw [uIcc_of_le (le_add_of_nonneg_right hb),uIcc_of_le (add_nonneg ha hb)]; exact Icc_subset_Icc ha le_rfl)
  rw [←intervalIntegral.integral_add_adjacent_intervals h1 h2,SKValue.patchTime_integral_left ⟨ha,le_rfl⟩,
    SKValue.patchTime_integral_right (le_add_of_nonneg_right hb),add_sub_cancel_left]

lemma profile_weighted_integrable (q : ℝ) (l : SKValue.HeatProfile) :
    IntervalIntegrable (fun s ↦ (q+s)*SKValue.profileCoeff l s) volume 0 (SKValue.profileTime l) :=
  (SKValue.profileCoeff_integrable l).continuousOn_mul (continuous_const.add continuous_id).continuousOn

lemma profileTree_correction (q : ℝ) (l : SKValue.HeatProfile) :
    treeCorrection q (profileTree q l)=(1/2 : ℝ)*(∫ s in (0 : ℝ)..SKValue.profileTime l,(q+s)*SKValue.profileCoeff l s) := by
  induction l generalizing q with
  | nil => simp [profileTree,treeCorrection,SKValue.profileTime]
  | cons p l ih =>
    have he : (fun s ↦ (q+s)*SKValue.profileCoeff (p::l) s)=
        SKValue.patchTime (p.1 : ℝ) (fun s ↦ (q+s)*(p.2 : ℝ))
          (fun s ↦ (q+(p.1 : ℝ)+s)*SKValue.profileCoeff l s) := by
      funext s
      change (q+s)*(if s≤(p.1 : ℝ) then (p.2 : ℝ) else SKValue.profileCoeff l (s-p.1)) =
        if s≤(p.1 : ℝ) then (q+s)*(p.2 : ℝ) else
          (q+(p.1 : ℝ)+(s-p.1))*SKValue.profileCoeff l (s-p.1)
      split_ifs
      · rfl
      · congr 1; ring
    rw [he,SKValue.profileTime,patchTime_integral p.1.coe_nonneg (SKValue.profileTime_nonneg l)
      ((by fun_prop : Continuous (fun s : ℝ ↦ (q+s)*(p.2 : ℝ))).intervalIntegrable ..) (profile_weighted_integrable _ l)]
    have he2 : (∫ s in (0 : ℝ)..(p.1 : ℝ),(q+s)*(p.2 : ℝ))=
        (p.2 : ℝ)*((q+(p.1 : ℝ))^2-q^2)/2 := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_add (f := fun _ : ℝ ↦ q) (g := fun s : ℝ ↦ s)
        intervalIntegrable_const (continuous_id.intervalIntegrable ..)]
      simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,integral_id]
      ring
    rw [he2,profileTree,treeCorrection,ih]
    ring

end SKValueG

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_WeakGuerra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma profile_penalty_mono (ε : ℝ≥0) (k : ℕ) {l : SKValue.HeatProfile}
    (hT : SKValue.profileTime l=1) :
    (∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t) ≤
      ∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff (SKValue.liftProfile ε k l) t := by
  have h1 := profile_weighted_integrable 0 l
  have h2 := profile_weighted_integrable 0 (SKValue.liftProfile ε k l)
  simp only [zero_add,SKValue.liftProfile_time,hT] at h1 h2
  apply intervalIntegral.integral_mono_on (by norm_num) h1 h2
  intro t ht
  exact mul_le_mul_of_nonneg_left (SKValue.liftProfile_coeff_lower ε k l t) ht.1

lemma weak_profile_guerra_upper_oai (W : SKValue.BrownianSpace) {n : ℕ} (hn : 0<n)
    {ψ : ℝ → ℝ} (hψ : SKValue.SmoothTerminal ψ) (hb : ∀ x,|x|≤ψ x)
    {l : SKValue.HeatProfile} (hl : l.Pairwise (fun p r ↦ p.2 ≤ r.2)) (hT : SKValue.profileTime l=1) :
    expectedMaximum n ≤ (n : ℝ)*(SKValue.profileValue ψ l 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t)) := by
  have he : ∀ ε : ℝ,0<ε → expectedMaximum n ≤ (n : ℝ)*(SKValue.profileValue ψ l 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t)+(3/2 : ℝ)*ε*(1+l.length)) := by
    intro ε hε
    let e : ℝ≥0 := ⟨ε,hε.le⟩
    have hepos : 0<e := hε
    have hs := profileTree_scale (q := 0) (by norm_num : (0 : ℝ)≤0)
      (SKValue.liftProfile_strict hepos 1 hl) (SKValue.liftProfile_positive hepos (by norm_num : 0<1) l)
    have hg := profileTree_valid (q := 0) (l := SKValue.liftProfile e 1 l)
      (by rw [zero_add,SKValue.liftProfile_time,hT])
    have hu := finite_step_guerra_upper hn _ hg hs
    have hv := profileTree_le_smooth hψ hb hs 0
    have hvb := abs_le.mp (hψ.liftProfile_bound W hl hT hepos 1 0)
    have hc := profile_penalty_mono e 1 hT
    rw [profileTree_correction] at hu
    simp only [SKValue.liftProfile_time,hT,zero_add] at hu
    have hnn : (0 : ℝ)≤n := by positivity
    have hvb' : SKValue.profileValue ψ (SKValue.liftProfile e 1 l) 0 0-SKValue.profileValue ψ l 0 0 ≤
        (3/2 : ℝ)*ε*(1+l.length) := by
      have h := hvb.2
      have hcoe : (e : ℝ)=ε := rfl
      rw [Nat.cast_one,hcoe] at h
      exact h
    apply hu.trans
    apply mul_le_mul_of_nonneg_left _ hnn
    linarith
  have hh : Tendsto (fun j : ℕ ↦ (n : ℝ)*(SKValue.profileValue ψ l 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t)+
        (3/2 : ℝ)*(1/(j+1 : ℝ))*(1+l.length))) atTop
      (𝓝 ((n : ℝ)*(SKValue.profileValue ψ l 0 0-
        (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t)))) := by
    have hr : Tendsto (fun j : ℕ ↦ (3/2 : ℝ)*(1/(j+1 : ℝ))*(1+l.length)) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (3/2 : ℝ)).mul_const (1+(l.length : ℝ))
    simpa only [add_zero] using (hr.const_add (SKValue.profileValue ψ l 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t))).const_mul (n : ℝ)
  exact ge_of_tendsto hh (Eventually.of_forall (fun (j : ℕ) ↦ he (1/(j+1 : ℝ)) (one_div_pos.mpr (by exact_mod_cast Nat.succ_pos j))))

end SKValueG

end

end OAI
end

theorem solution : type_of% @OAI.SKValueG.weak_profile_guerra_upper_oai := @OAI.SKValueG.weak_profile_guerra_upper_oai
