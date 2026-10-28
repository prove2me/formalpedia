-- Prove2me | solution 1 for OAI.SKValue.split_profile_coercivity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:08:02.556302+00:00
-- url     : https://prove2.me/submissions/b59a1992-6dd1-4806-9986-a1fdfeec1eed

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000

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

lemma patchTime_end {E : Type*} {a b : ℝ} (hb : 0≤b) {f g : ℝ → E} (hfg : f a=g 0) :
    patchTime a f g (a+b)=g b := by
  rcases hb.eq_or_lt with rfl | hb
  · simpa only [add_zero,patchTime_left f g le_rfl] using hfg
  · rw [patchTime_right f g (lt_add_of_pos_right a hb)]
    congr 1
    ring

lemma profileValue_terminal (ψ : ℝ → ℝ) (l : HeatProfile) :
    profileValue ψ l (profileTime l)=ψ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change patchTime _ _ _ ((p.1 : ℝ)+profileTime l)=ψ
    rw [patchTime_end (profileTime_nonneg l)]
    · exact ih
    · funext x
      simp only [sub_self,coleHopf_zero]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BackwardPolynomials
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace SKValue

namespace BackwardBurgers
variable (F : BackwardBurgers)

lemma k_space (t x : ℝ) : HasDerivAt (F.k t) (F.kx t x) x := by
  have hd := (F.space 2 t x).add (((F.space 0 t x).const_mul 2).mul (F.space 1 t x))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [k,kx]
  ring
lemma kx_space (t x : ℝ) : HasDerivAt (F.kx t) (F.kxx t x) x := by
  have hd := ((F.space 3 t x).add (((F.space 1 t x).pow 2).const_mul 2)).add
    (((F.space 0 t x).const_mul 2).mul (F.space 2 t x))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [kx,kxx]
  ring
lemma k_time {t : ℝ} (ht : 0<t) (x : ℝ) : HasDerivAt (F.k · x) (F.kt t x) t := by
  have hd := (F.time2 t ht x).add (((F.time0 t ht x).const_mul 2).mul (F.time1 t ht x))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [k,kt,kx,kxx]
  ring
lemma n_space (t x : ℝ) : HasDerivAt (F.n t) (F.nx t x) x := by
  have hd := (((F.space 0 t x).mul (F.space 3 t x)).sub
    ((F.space 1 t x).mul (F.space 2 t x))).add
    ((((F.space 0 t x).pow 2).const_mul 2).mul (F.space 2 t x))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [n,nx]
  ring
lemma nx_space (t x : ℝ) : HasDerivAt (F.nx t) (F.nxx t x) x := by
  have hd := ((((F.space 0 t x).mul (F.space 4 t x)).sub ((F.space 2 t x).pow 2)).add
    ((((F.space 0 t x).const_mul 4).mul (F.space 1 t x)).mul (F.space 2 t x))).add
    ((((F.space 0 t x).pow 2).const_mul 2).mul (F.space 3 t x))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [nx,nxx]
  ring
lemma n_time {t x : ℝ} (ht : 0<t) (hx : 0<x) : HasDerivAt (F.n · x) (F.nt t x) t := by
  have hd := (((F.time0 t ht x).mul (F.time3 t ht x)).sub
    ((F.time1 t ht x).mul (F.time2 t ht x))).add
    ((((F.time0 t ht x).pow 2).const_mul 2).mul (F.time2 t ht x))
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [n,nt,nx,nxx,k]
  field_simp [(F.positive t x hx).ne']
  ring

lemma k_continuous : Continuous (fun p : ℝ×ℝ ↦ F.k p.1 p.2) :=
  (F.continuous 2).add ((continuous_const.mul (F.continuous 0)).mul (F.continuous 1))
lemma n_continuous : Continuous (fun p : ℝ×ℝ ↦ F.n p.1 p.2) :=
  (((F.continuous 0).mul (F.continuous 3)).sub ((F.continuous 1).mul (F.continuous 2))).add
    ((continuous_const.mul ((F.continuous 0).pow 2)).mul (F.continuous 2))
lemma k_bound : ∃ C : ℝ,0≤C ∧ ∀ t x,|F.k t x|≤C := by
  let e : JetExpr := .add (.coord 2) (.mul (.mul (.const 2) (.coord 0)) (.coord 1))
  have hh : ∀ j,∃ C : ℝ,0≤C ∧ ∀ p : ℝ×ℝ,|F.jet j p.1 p.2|≤C := by
    intro j; obtain ⟨C,hC,h⟩ := F.bound j; exact ⟨C,hC,fun p ↦ h p.1 p.2⟩
  obtain ⟨C,hC,h⟩ := JetExpr.uniform_bound hh e
  exact ⟨C,hC,fun t x ↦ h (t,x)⟩
lemma n_bound : ∃ C : ℝ,0≤C ∧ ∀ t x,|F.n t x|≤C := by
  let e : JetExpr := .add (.add (.mul (.coord 0) (.coord 3))
    (.mul (.const (-1)) (.mul (.coord 1) (.coord 2))))
    (.mul (.mul (.const 2) (.mul (.coord 0) (.coord 0))) (.coord 2))
  have hh : ∀ j,∃ C : ℝ,0≤C ∧ ∀ p : ℝ×ℝ,|F.jet j p.1 p.2|≤C := by
    intro j; obtain ⟨C,hC,h⟩ := F.bound j; exact ⟨C,hC,fun p ↦ h p.1 p.2⟩
  obtain ⟨C,hC,h⟩ := JetExpr.uniform_bound hh e
  refine ⟨C,hC,fun t x ↦ ?_⟩
  convert! h (t,x) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  dsimp [n,e,JetExpr.eval]
  ring

end BackwardBurgers
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ParabolicComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue

lemma localMin_second_deriv_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMin f x) (hc : ContinuousAt f x) : 0≤deriv (deriv f) x := by
  by_contra hn
  have hn := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn hm.deriv_eq_zero hc
  have he : f=ᶠ[𝓝 x] fun _ ↦ f x := by
    filter_upwards [hm,hmax] with y hy hy'
    exact le_antisymm hy' hy
  have hz := he.deriv.deriv_eq
  simp only [deriv_const',deriv_const] at hz
  linarith

lemma time_min_deriv_nonpos {f : ℝ → ℝ} {T t d : ℝ} (ht : 0<t)
    (htT : t≤T) (hm : IsMinOn f (Icc (0 : ℝ) T) t) (hd : HasDerivAt f d t) : d≤0 := by
  have hdir : (0 : ℝ)-t∈posTangentConeAt (Icc (0 : ℝ) T) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc (0 : ℝ) T).segment_subset ⟨ht.le,htT⟩ ⟨le_rfl,ht.le.trans htT⟩)
  have hh := hm.localize.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt hdir
  have hh' : 0≤(0-t)*d := by simpa using hh
  nlinarith

lemma parabolic_nonneg_of_negative_zeroth {T a b : ℝ}
    (hT : 0≤T) (hab : a≤b) {u ut ux uxx β c : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ u p.1 p.2) ((Icc 0 T)×ˢ(Icc a b)))
    (hdt : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, HasDerivAt (u · x) (ut t x) t)
    (hdx : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, HasDerivAt (u t) (ux t x) x)
    (hdxx : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b,
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hinit : ∀ x∈Icc a b, 0≤u 0 x)
    (hleft : ∀ t∈Icc (0 : ℝ) T, 0≤u t a)
    (hright : ∀ t∈Icc (0 : ℝ) T, 0≤u t b)
    (hcneg : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, c t x<0)
    (hpde : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b,
      0≤ut t x-(1/2 : ℝ)*uxx t x-β t x*ux t x-c t x*u t x) :
    ∀ t∈Icc (0 : ℝ) T, ∀ x∈Icc a b, 0≤u t x := by
  obtain ⟨⟨s,y⟩,⟨hs,hy⟩,hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn
    (show (((Icc (0 : ℝ) T)×ˢ(Icc a b))).Nonempty from ⟨(0,a),⟨⟨le_rfl,hT⟩,⟨le_rfl,hab⟩⟩⟩) hc
  suffices hm : 0≤u s y by
    intro t ht x hx
    exact hm.trans (@hmin (t,x) ⟨ht,hx⟩)
  by_contra hn
  have hn : u s y<0 := lt_of_not_ge hn
  have hs0 : 0 < s := lt_of_le_of_ne hs.1 (by intro he; subst s; exact (not_lt_of_ge (hinit y hy)) hn)
  have hya : a<y := lt_of_le_of_ne hy.1 (by intro he; subst y; exact (not_lt_of_ge (hleft s hs)) hn)
  have hyb : y<b := lt_of_le_of_ne hy.2 (by intro he; subst y; exact (not_lt_of_ge (hright s hs)) hn)
  have hst : s∈Ioc (0 : ℝ) T := ⟨hs0,hs.2⟩
  have hyi : y∈Ioo a b := ⟨hya,hyb⟩
  have hmt : IsMinOn (u · y) (Icc (0 : ℝ) T) s := fun t ht ↦ @hmin (t,y) ⟨ht,hy⟩
  have hmx : IsLocalMin (u s) y :=
    (show IsMinOn (u s) (Icc a b) y from fun x hx ↦ @hmin (s,x) ⟨hs,hx⟩).isLocalMin (Icc_mem_nhds hya hyb)
  have htime := time_min_deriv_nonpos hs0 hs.2 hmt (hdt s hst y hyi)
  have hxzero := hmx.hasDerivAt_eq_zero (hdx s hst y hyi)
  have hxxpos := localMin_second_deriv_nonneg hmx (hdx s hst y hyi).continuousAt
  rw [(hdxx s hst y hyi).deriv] at hxxpos
  have hcc := mul_pos_of_neg_of_neg (hcneg s hst y hyi) hn
  have hp := hpde s hst y hyi
  rw [hxzero,mul_zero] at hp
  linarith

lemma parabolic_barrier {T a b C ε : ℝ}
    (hT : 0≤T) (hab : a≤b) (hε : 0≤ε) {u ut ux uxx β c : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ u p.1 p.2) ((Icc 0 T)×ˢ(Icc a b)))
    (hdt : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, HasDerivAt (u · x) (ut t x) t)
    (hdx : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, HasDerivAt (u t) (ux t x) x)
    (hdxx : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b,
      HasDerivAt (deriv (u t)) (uxx t x) x)
    (hinit : ∀ x∈Icc a b, 0≤u 0 x)
    (hleft : ∀ t∈Icc (0 : ℝ) T, -ε≤u t a)
    (hright : ∀ t∈Icc (0 : ℝ) T, -ε≤u t b)
    (hcbd : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b, c t x≤C)
    (hpde : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioo a b,
      0≤ut t x-(1/2 : ℝ)*uxx t x-β t x*ux t x-c t x*u t x) :
    ∀ t∈Icc (0 : ℝ) T, ∀ x∈Icc a b,
      -ε*Real.exp ((max C 0+1)*t)≤u t x := by
  let k := max C 0+1
  let e := fun t : ℝ ↦ Real.exp (-k*t)
  have hk : 0<k := by dsimp [k]; linarith [le_max_right C 0]
  have hepos : ∀ t,0<e t := fun t ↦ Real.exp_pos _
  have heder : ∀ t,HasDerivAt e (-k*e t) t := by
    intro t
    convert ((hasDerivAt_id t).const_mul (-k)).exp using 1 <;> dsimp [e]
    ring
  have hecont : Continuous e := by fun_prop
  have hbound : ∀ t∈Icc (0 : ℝ) T, 0≤e t ∧ e t≤1 := by
    intro t ht
    refine ⟨(hepos t).le,Real.exp_le_one_iff.mpr ?_⟩
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) ht.1
  have hlbound {t v : ℝ} (ht : t∈Icc (0 : ℝ) T) (hv : -ε≤v) : 0≤e t*v+ε := by
    have hh := mul_le_mul_of_nonneg_left hv (hepos t).le
    have hh' := mul_le_mul_of_nonneg_left (hbound t ht).2 hε
    nlinarith
  have hh := parabolic_nonneg_of_negative_zeroth hT hab
    (u := fun t x ↦ e t*u t x+ε)
    (ut := fun t x ↦ e t*(ut t x-k*u t x))
    (ux := fun t x ↦ e t*ux t x) (uxx := fun t x ↦ e t*uxx t x)
    (β := β) (c := fun t x ↦ c t x-k)
    (((hecont.comp continuous_fst).continuousOn.mul hc).add continuousOn_const)
    (by
      intro t ht x hx
      have hd : HasDerivAt (fun s : ℝ ↦ e s*u s x+ε)
          ((-k*e t)*u t x+e t*ut t x) t :=
        ((heder t).mul (hdt t ht x hx)).add_const ε
      convert hd using 1
      all_goals try with_reducible_and_instances rfl
      ring)
    (by
      intro t ht x hx
      exact ((hdx t ht x hx).const_mul (e t)).add_const ε)
    (by
      intro t ht x hx
      have heq : (deriv (fun y ↦ e t*u t y+ε))=fun y ↦ e t*deriv (u t) y := by
        funext y
        rw [deriv_add_const,deriv_const_mul_field]
      rw [heq]
      exact (hdxx t ht x hx).const_mul (e t))
    (by intro x hx; simpa only [e,mul_zero,Real.exp_zero,one_mul] using add_nonneg (hinit x hx) hε)
    (by intro t ht; exact hlbound ht (hleft t ht))
    (by intro t ht; exact hlbound ht (hright t ht))
    (by intro t ht x hx; have hb := hcbd t ht x hx; dsimp [k]; linarith [le_max_left C 0])
    (by
      intro t ht x hx
      have hp := mul_nonneg (hepos t).le (hpde t ht x hx)
      have hb : c t x-k≤0 := by have hb := hcbd t ht x hx; dsimp [k]; linarith [le_max_left C 0]
      have hbε := mul_nonpos_of_nonpos_of_nonneg hb hε
      nlinarith only [hp,hbε])
  intro t ht x hx
  have hn := hh t ht x hx
  have heinv : e t*Real.exp (k*t)=1 := by
    dsimp [e]
    rw [←Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  have hmul : 0≤Real.exp (k*t)*(e t*u t x+ε) := mul_nonneg (Real.exp_pos _).le hn
  have heq : Real.exp (k*t)*(e t*u t x+ε)=u t x+ε*Real.exp (k*t) := by
    calc
      _ = (e t*Real.exp (k*t))*u t x+ε*Real.exp (k*t) := by ring
      _ = _ := by rw [heinv,one_mul]
  rw [heq] at hmul
  change -ε*Real.exp (k*t)≤u t x
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_HalflineComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue

lemma halfline_parabolic_nonneg {T B C M : ℝ} (hT : 0≤T) (hB : 0≤B) (_ : 0≤M)
    {u ut ux uxx β c : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ u p.1 p.2) ((Icc 0 T)×ˢ(Ici 0)))
    (hdt : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioi (0 : ℝ), HasDerivAt (u · x) (ut t x) t)
    (hdx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (u t) (ux t x) x)
    (hdxx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (ux t) (uxx t x) x)
    (hinit : ∀ x, 0≤x → 0≤u 0 x)
    (hleft : ∀ t∈Icc (0 : ℝ) T, 0≤u t 0)
    (hbound : ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x → -M≤u t x)
    (hβ : ∀ t∈Ioc (0 : ℝ) T, ∀ x, 0<x → β t x≤B)
    (hcbd : ∀ t∈Ioc (0 : ℝ) T, ∀ x, 0<x → c t x≤C)
    (hpde : ∀ t∈Ioc (0 : ℝ) T, ∀ x, 0<x →
      0≤ut t x-(1/2 : ℝ)*uxx t x-β t x*ux t x-c t x*u t x) :
    ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x → 0≤u t x := by
  let k := max C 0+B+2
  have hk : 0≤k := by dsimp [k]; linarith [le_max_right C 0]
  have hεbound : ∀ ε : ℝ, 0<ε → ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x →
      -ε*Real.exp (k*t)*(1+x^2)≤u t x := by
    intro ε hε t ht x hx
    let A := max 1 (max x (M/ε+1))
    have hA1 : 1≤A := le_max_left _ _
    have hA0 : 0≤A := le_trans zero_le_one hA1
    have hxA : x≤A := (le_max_left _ _).trans (le_max_right _ _)
    have hMA : M≤ε*A := by
      have hA := (le_max_right x (M/ε+1)).trans (le_max_right 1 (max x (M/ε+1)))
      have hh := mul_le_mul_of_nonneg_left hA hε.le
      rw [mul_add,mul_div_cancel₀ M hε.ne'] at hh
      linarith
    have hMA2 : M≤ε*(1+A^2) := by
      have hAA : A≤A^2 := by nlinarith
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hAA)]
    let q := fun s : ℝ ↦ ε*Real.exp (k*s)
    have hqpos : ∀ s, 0≤q s := fun s ↦ mul_nonneg hε.le (Real.exp_pos _).le
    have hqε : ∀ s∈Icc (0 : ℝ) T, ε≤q s := by
      intro s hs
      have hh : 1≤Real.exp (k*s) := Real.one_le_exp_iff.mpr (mul_nonneg hk hs.1)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hε.le
    have hqder : ∀ s, HasDerivAt q (k*q s) s := by
      intro s
      have hd : HasDerivAt q (ε*(Real.exp (k*s)*k)) s :=
        by simpa only [id_eq,mul_one] using (((hasDerivAt_id s).const_mul k).exp).const_mul ε
      convert! hd using 1; dsimp [q]; ring
    have hqcont : Continuous q := by fun_prop
    have hpder : ∀ y : ℝ, HasDerivAt (fun z : ℝ ↦ 1+z^2) (2*y) y := by
      intro y
      convert! ((hasDerivAt_id y).pow 2).const_add 1 using 1; simp
    have hcmp := parabolic_barrier (C := C) (ε := 0) hT hA0 le_rfl
      (u := fun s y ↦ u s y+q s*(1+y^2))
      (ut := fun s y ↦ ut s y+k*q s*(1+y^2))
      (ux := fun s y ↦ ux s y+q s*(2*y))
      (uxx := fun s y ↦ uxx s y+2*q s) (β := β) (c := c)
      ((hc.mono (fun p hp ↦ ⟨hp.1,hp.2.1⟩)).add
        (((hqcont.comp continuous_fst).mul (continuous_const.add
          (continuous_snd.pow 2))).continuousOn))
      (by
        intro s hs y hy
        exact (hdt s hs y hy.1).add ((hqder s).mul_const (1+y^2)))
      (by
        intro s hs y hy
        exact (hdx s hs y).add ((hpder y).const_mul (q s)))
      (by
        intro s hs y hy
        have he : deriv (fun z ↦ u s z+q s*(1+z^2))=
            fun z ↦ ux s z+q s*(2*z) := by
          funext z
          exact ((hdx s hs z).add ((hpder z).const_mul (q s))).deriv
        rw [he]
        convert! (hdxx s hs y).add (((hasDerivAt_id y).const_mul 2).const_mul (q s)) using 1; simp; ring)
      (by
        intro y hy
        exact add_nonneg (hinit y hy.1) (mul_nonneg (hqpos _) (by positivity)))
      (by
        intro s hs
        simpa only [neg_zero,zero_pow (by decide : 2≠0),add_zero,mul_one] using
          add_nonneg (hleft s hs) (hqpos s))
      (by
        intro s hs
        have hb := hbound s hs A hA0
        have hq := mul_le_mul_of_nonneg_right (hqε s hs) (show 0≤1+A^2 by positivity)
        change - (0 : ℝ)≤u s A+q s*(1+A^2)
        linarith)
      (by intro s hs y hy; exact hcbd s hs y hy.1)
      (by
        intro s hs y hy
        have hp := hpde s hs y hy.1
        have hb := hβ s hs y hy.1
        have hc' := hcbd s hs y hy.1
        have hkC : B+2≤k-c s y := by dsimp [k]; linarith [le_max_left C 0]
        have hh1 := mul_nonneg (sub_nonneg.mpr hkC) (show 0≤1+y^2 by positivity)
        have hh2 := mul_nonneg (sub_nonneg.mpr hb) hy.1.le
        have hh3 := mul_nonneg hB (sq_nonneg (y-1))
        have hbr : 0≤(k-c s y)*(1+y^2)-1-2*β s y*y := by nlinarith [sq_nonneg y]
        have hbq := mul_nonneg (hqpos s) hbr
        nlinarith only [hp,hbq]) t ht x ⟨hx,hxA⟩
    simp only [neg_zero,zero_mul] at hcmp
    dsimp [q] at hcmp
    linarith
  intro t ht x hx
  by_contra hn
  have hu : u t x<0 := lt_of_not_ge hn
  let D := Real.exp (k*t)*(1+x^2)
  have hD : 0<D := mul_pos (Real.exp_pos _) (by positivity)
  have he : 0<(-u t x)/(2*D) := div_pos (neg_pos.mpr hu) (mul_pos (by norm_num) hD)
  have hh := hεbound ((-u t x)/(2*D)) he t ht x hx
  have heq : -((-u t x)/(2*D))*Real.exp (k*t)*(1+x^2)=u t x/2 := by
    dsimp [D]
    field_simp
  rw [heq] at hh
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BackwardComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue.BackwardBurgers
variable (F : SKValue.BackwardBurgers)

lemma preserve_w (hinit : ∀ x,0≤x → F.jet 2 0 x≤0) {t x : ℝ}
    (ht : 0≤t) (hx : 0≤x) : F.jet 2 t x≤0 := by
  obtain ⟨B,hB,hb⟩ := F.bound 0
  obtain ⟨C,hC,hc⟩ := F.bound 1
  obtain ⟨M,hM,hm⟩ := F.bound 2
  have hh := halfline_parabolic_nonneg (T := t) (B := B) (C := 3*C) (M := M) ht hB hM
    (u := fun s y ↦ -F.jet 2 s y)
    (ut := fun s y ↦ -((1/2:ℝ)*F.jet 4 s y+3*F.jet 1 s y*F.jet 2 s y+F.jet 0 s y*F.jet 3 s y))
    (ux := fun s y ↦ -F.jet 3 s y) (uxx := fun s y ↦ -F.jet 4 s y)
    (β := F.jet 0) (c := fun s y ↦ 3*F.jet 1 s y)
    (F.continuous 2).neg.continuousOn
    (by intro s hs y hy; exact (F.time2 s hs.1 y).neg)
    (by intro s hs y; exact (F.space 2 s y).neg)
    (by intro s hs y; exact (F.space 3 s y).neg)
    (by intro y hy; exact neg_nonneg.mpr (hinit y hy))
    (by intro s hs; simp only [F.zero2,neg_zero,le_refl])
    (by intro s hs y hy; have hh := (le_abs_self _).trans (hm s y); linarith)
    (by intro s hs y hy; exact (le_abs_self _).trans (hb s y))
    (by intro s hs y hy; have hh := (le_abs_self _).trans (hc s y); linarith)
    (by intro s hs y hy; ring_nf; exact le_rfl) t ⟨ht,le_rfl⟩ x hx
  linarith

lemma preserve_k (hinit : ∀ x,0≤x → F.k 0 x≤0) {t x : ℝ}
    (ht : 0≤t) (hx : 0≤x) : F.k t x≤0 := by
  obtain ⟨B,hB,hb⟩ := F.bound 0
  obtain ⟨C,hC,hc⟩ := F.bound 1
  obtain ⟨M,hM,hm⟩ := F.k_bound
  have hh := halfline_parabolic_nonneg (T := t) (B := B) (C := C) (M := M) ht hB hM
    (u := fun s y ↦ -F.k s y) (ut := fun s y ↦ -F.kt s y)
    (ux := fun s y ↦ -F.kx s y) (uxx := fun s y ↦ -F.kxx s y)
    (β := F.jet 0) (c := F.jet 1)
    F.k_continuous.neg.continuousOn
    (by intro s hs y hy; exact (F.k_time hs.1 y).neg)
    (by intro s hs y; exact (F.k_space s y).neg)
    (by intro s hs y; exact (F.kx_space s y).neg)
    (by intro y hy; exact neg_nonneg.mpr (hinit y hy))
    (by intro s hs; simp only [k_zero,neg_zero,le_refl])
    (by intro s hs y hy; have hh := (le_abs_self _).trans (hm s y); linarith)
    (by intro s hs y hy; exact (le_abs_self _).trans (hb s y))
    (by intro s hs y hy; exact (le_abs_self _).trans (hc s y))
    (by intro s hs y hy; dsimp only [kt]; ring_nf; exact le_rfl) t ⟨ht,le_rfl⟩ x hx
  linarith

lemma preserve_n (hw : ∀ x,0≤x → F.jet 2 0 x≤0)
    (hk : ∀ x,0≤x → F.k 0 x≤0) (hn : ∀ x,0≤x → 0≤F.n 0 x)
    {t x : ℝ} (ht : 0≤t) (hx : 0≤x) : 0≤F.n t x := by
  obtain ⟨B,hB,hb⟩ := F.bound 0
  obtain ⟨M,hM,hm⟩ := F.n_bound
  apply halfline_parabolic_nonneg (T := t) (B := B) (C := 0) (M := M) ht hB hM
    (u := F.n) (ut := F.nt) (ux := F.nx) (uxx := F.nxx)
    (β := fun s y ↦ F.jet 0 s y-F.jet 1 s y/F.jet 0 s y)
    (c := fun s y ↦ F.k s y/F.jet 0 s y)
    F.n_continuous.continuousOn
    (by intro s hs y hy; exact F.n_time hs.1 hy)
    (by intro s hs y; exact F.n_space s y)
    (by intro s hs y; exact F.nx_space s y)
    hn
    (by intro s hs; simp only [n_zero,le_refl])
    (by intro s hs y hy; exact (neg_le_abs _).trans (hm s y) |> neg_le_neg |>.trans_eq (neg_neg _))
    (by
      intro s hs y hy
      have hd := div_nonneg (F.slope_nonneg s y) (F.positive s y hy).le
      have hh := (le_abs_self _).trans (hb s y)
      linarith)
    (by
      intro s hs y hy
      exact div_nonpos_of_nonpos_of_nonneg (F.preserve_k hk hs.1.le hy.le) (F.positive s y hy).le)
    (by
      intro s hs y hy
      have hf := mul_nonneg (F.positive s y hy).le
        (mul_nonneg_of_nonpos_of_nonpos (F.preserve_w hw hs.1.le hy.le) (F.preserve_k hk hs.1.le hy.le))
      dsimp only [nt]
      nlinarith only [hf]) t ⟨ht,le_rfl⟩ x hx

end SKValue.BackwardBurgers

end

section

open Set Filter
open scoped Topology
namespace SKValue

lemma halfline_parabolic_nonneg_linear {T B C M : ℝ} (hT : 0≤T) (hB : 0≤B) (hM : 0≤M)
    {u ut ux uxx β c : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ u p.1 p.2) ((Icc 0 T)×ˢ(Ici 0)))
    (hdt : ∀ t∈Ioc (0 : ℝ) T, ∀ x∈Ioi (0 : ℝ), HasDerivAt (u · x) (ut t x) t)
    (hdx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (u t) (ux t x) x)
    (hdxx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (ux t) (uxx t x) x)
    (hinit : ∀ x, 0≤x → 0≤u 0 x)
    (hleft : ∀ t∈Icc (0 : ℝ) T, 0≤u t 0)
    (hbound : ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x → -M*(1+x)≤u t x)
    (hβ : ∀ t∈Ioc (0 : ℝ) T, ∀ x, 0<x → β t x≤B)
    (hcbd : ∀ t∈Ioc (0 : ℝ) T, ∀ x, 0<x → c t x≤C)
    (hpde : ∀ t∈Ioc (0 : ℝ) T, ∀ x, 0<x →
      0≤ut t x-(1/2 : ℝ)*uxx t x-β t x*ux t x-c t x*u t x) :
    ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x → 0≤u t x := by
  let k := max C 0+B+2
  have hk : 0≤k := by dsimp [k]; linarith [le_max_right C 0]
  have hεbound : ∀ ε : ℝ, 0<ε → ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤x →
      -ε*Real.exp (k*t)*(1+x^2)≤u t x := by
    intro ε hε t ht x hx
    let A := max 1 (max x (2*M/ε+1))
    have hA1 : 1≤A := le_max_left _ _
    have hA0 : 0≤A := le_trans zero_le_one hA1
    have hxA : x≤A := (le_max_left _ _).trans (le_max_right _ _)
    have hMA : 2*M≤ε*A := by
      have hA := (le_max_right x (2*M/ε+1)).trans (le_max_right 1 (max x (2*M/ε+1)))
      have hh := mul_le_mul_of_nonneg_left hA hε.le
      rw [mul_add,mul_div_cancel₀ (2*M) hε.ne'] at hh
      linarith
    have hMA2 : M*(1+A)≤ε*(1+A^2) := by
      have hh := mul_le_mul_of_nonneg_right hMA hA0
      have ha := mul_nonneg hM (sub_nonneg.mpr hA1)
      nlinarith
    let q := fun s : ℝ ↦ ε*Real.exp (k*s)
    have hqpos : ∀ s, 0≤q s := fun s ↦ mul_nonneg hε.le (Real.exp_pos _).le
    have hqε : ∀ s∈Icc (0 : ℝ) T, ε≤q s := by
      intro s hs
      have hh : 1≤Real.exp (k*s) := Real.one_le_exp_iff.mpr (mul_nonneg hk hs.1)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hε.le
    have hqder : ∀ s, HasDerivAt q (k*q s) s := by
      intro s
      have hd : HasDerivAt q (ε*(Real.exp (k*s)*k)) s :=
        by simpa only [id_eq,mul_one] using (((hasDerivAt_id s).const_mul k).exp).const_mul ε
      convert! hd using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [q]
      ring
    have hqcont : Continuous q := by fun_prop
    have hpder : ∀ y : ℝ, HasDerivAt (fun z : ℝ ↦ 1+z^2) (2*y) y := by
      intro y
      convert! ((hasDerivAt_id y).pow 2).const_add 1 using 1
      all_goals try with_reducible_and_instances rfl
      simp
    have hcmp := parabolic_barrier (C := C) (ε := 0) hT hA0 le_rfl
      (u := fun s y ↦ u s y+q s*(1+y^2))
      (ut := fun s y ↦ ut s y+k*q s*(1+y^2))
      (ux := fun s y ↦ ux s y+q s*(2*y))
      (uxx := fun s y ↦ uxx s y+2*q s) (β := β) (c := c)
      ((hc.mono (fun p hp ↦ ⟨hp.1,hp.2.1⟩)).add
        (((hqcont.comp continuous_fst).mul (continuous_const.add
          (continuous_snd.pow 2))).continuousOn))
      (by
        intro s hs y hy
        exact (hdt s hs y hy.1).add ((hqder s).mul_const (1+y^2)))
      (by
        intro s hs y hy
        exact (hdx s hs y).add ((hpder y).const_mul (q s)))
      (by
        intro s hs y hy
        have he : deriv (fun z ↦ u s z+q s*(1+z^2))=
            fun z ↦ ux s z+q s*(2*z) := by
          funext z
          exact ((hdx s hs z).add ((hpder z).const_mul (q s))).deriv
        rw [he]
        convert! (hdxx s hs y).add (((hasDerivAt_id y).const_mul 2).const_mul (q s)) using 1
        all_goals try with_reducible_and_instances rfl
        simp
        ring)
      (by
        intro y hy
        exact add_nonneg (hinit y hy.1) (mul_nonneg (hqpos _) (by positivity)))
      (by
        intro s hs
        simpa only [neg_zero,zero_pow (by decide : 2≠0),add_zero,mul_one] using
          add_nonneg (hleft s hs) (hqpos s))
      (by
        intro s hs
        have hb := hbound s hs A hA0
        have hq := mul_le_mul_of_nonneg_right (hqε s hs) (show 0≤1+A^2 by positivity)
        change - (0 : ℝ)≤u s A+q s*(1+A^2)
        linarith)
      (by intro s hs y hy; exact hcbd s hs y hy.1)
      (by
        intro s hs y hy
        have hp := hpde s hs y hy.1
        have hb := hβ s hs y hy.1
        have hc' := hcbd s hs y hy.1
        have hkC : B+2≤k-c s y := by dsimp [k]; linarith [le_max_left C 0]
        have hh1 := mul_nonneg (sub_nonneg.mpr hkC) (show 0≤1+y^2 by positivity)
        have hh2 := mul_nonneg (sub_nonneg.mpr hb) hy.1.le
        have hh3 := mul_nonneg hB (sq_nonneg (y-1))
        have hbr : 0≤(k-c s y)*(1+y^2)-1-2*β s y*y := by nlinarith [sq_nonneg y]
        have hbq := mul_nonneg (hqpos s) hbr
        nlinarith only [hp,hbq]) t ht x ⟨hx,hxA⟩
    simp only [neg_zero,zero_mul] at hcmp
    dsimp [q] at hcmp
    linarith
  intro t ht x hx
  by_contra hn
  have hu : u t x<0 := lt_of_not_ge hn
  let D := Real.exp (k*t)*(1+x^2)
  have hD : 0<D := mul_pos (Real.exp_pos _) (by positivity)
  have he : 0<(-u t x)/(2*D) := div_pos (neg_pos.mpr hu) (mul_pos (by norm_num) hD)
  have hh := hεbound ((-u t x)/(2*D)) he t ht x hx
  have heq : -((-u t x)/(2*D))*Real.exp (k*t)*(1+x^2)=u t x/2 := by
    dsimp [D]
    field_simp
  rw [heq] at hh
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_LineComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue

lemma line_parabolic_nonneg {T B C M : ℝ} (hT : 0≤T) (hB : 0≤B) (hM : 0≤M)
    {u ut ux uxx β c : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ×ℝ ↦ u p.1 p.2) ((Icc 0 T)×ˢ(univ)))
    (hdt : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (u · x) (ut t x) t)
    (hdx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (u t) (ux t x) x)
    (hdxx : ∀ t∈Ioc (0 : ℝ) T, ∀ x, HasDerivAt (ux t) (uxx t x) x)
    (hinit : ∀ x, 0≤u 0 x)
    (hbound : ∀ t∈Icc (0 : ℝ) T, ∀ x, -M≤u t x)
    (hβ : ∀ t∈Ioc (0 : ℝ) T, ∀ x, β t x*x≤B*(1+x^2))
    (hcbd : ∀ t∈Ioc (0 : ℝ) T, ∀ x, c t x≤C)
    (hpde : ∀ t∈Ioc (0 : ℝ) T, ∀ x,
      0≤ut t x-(1/2 : ℝ)*uxx t x-β t x*ux t x-c t x*u t x) :
    ∀ t∈Icc (0 : ℝ) T, ∀ x, 0≤u t x := by
  let k := max C 0+2*B+2
  have hk : 0≤k := by dsimp [k]; linarith [le_max_right C 0]
  have hεbound : ∀ ε : ℝ, 0<ε → ∀ t∈Icc (0 : ℝ) T, ∀ x,
      -ε*Real.exp (k*t)*(1+x^2)≤u t x := by
    intro ε hε t ht x
    let A := max 1 (max |x| (M/ε+1))
    have hA1 : 1≤A := le_max_left _ _
    have hxA : |x|≤A := (le_max_left _ _).trans (le_max_right _ _)
    have hMA : M≤ε*A := by
      have hA := (le_max_right |x| (M/ε+1)).trans (le_max_right 1 (max |x| (M/ε+1)))
      have hh := mul_le_mul_of_nonneg_left hA hε.le
      rw [mul_add,mul_div_cancel₀ M hε.ne'] at hh
      linarith
    have hA0 : 0≤A := (mul_nonneg_iff_of_pos_left hε).mp (hM.trans hMA)
    have hMA2 : M≤ε*(1+A^2) := by
      have hAA : A≤A^2 := by nlinarith
      nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hAA)]
    let q := fun s : ℝ ↦ ε*Real.exp (k*s)
    have hqpos : ∀ s, 0≤q s := fun s ↦ mul_nonneg hε.le (Real.exp_pos _).le
    have hqε : ∀ s∈Icc (0 : ℝ) T, ε≤q s := by
      intro s hs
      have hh : 1≤Real.exp (k*s) := Real.one_le_exp_iff.mpr (mul_nonneg hk hs.1)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh hε.le
    have hqder : ∀ s, HasDerivAt q (k*q s) s := by
      intro s
      have hd : HasDerivAt q (ε*(Real.exp (k*s)*k)) s :=
        by simpa only [id_eq,mul_one] using (((hasDerivAt_id s).const_mul k).exp).const_mul ε
      convert! hd using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [q]
      ring
    have hqcont : Continuous q := by fun_prop
    have hpder : ∀ y : ℝ, HasDerivAt (fun z : ℝ ↦ 1+z^2) (2*y) y := by
      intro y
      convert! ((hasDerivAt_id y).pow 2).const_add 1 using 1
      all_goals try with_reducible_and_instances rfl
      simp
    have hcmp := parabolic_barrier (C := C) (ε := 0) hT (show -A≤A by linarith) le_rfl
      (u := fun s y ↦ u s y+q s*(1+y^2))
      (ut := fun s y ↦ ut s y+k*q s*(1+y^2))
      (ux := fun s y ↦ ux s y+q s*(2*y))
      (uxx := fun s y ↦ uxx s y+2*q s) (β := β) (c := c)
      ((hc.mono (fun p hp ↦ ⟨hp.1,mem_univ _⟩)).add
        (((hqcont.comp continuous_fst).mul (continuous_const.add
          (continuous_snd.pow 2))).continuousOn))
      (by
        intro s hs y hy
        exact (hdt s hs y).add ((hqder s).mul_const (1+y^2)))
      (by
        intro s hs y hy
        exact (hdx s hs y).add ((hpder y).const_mul (q s)))
      (by
        intro s hs y hy
        have he : deriv (fun z ↦ u s z+q s*(1+z^2))=
            fun z ↦ ux s z+q s*(2*z) := by
          funext z
          exact ((hdx s hs z).add ((hpder z).const_mul (q s))).deriv
        rw [he]
        convert! (hdxx s hs y).add (((hasDerivAt_id y).const_mul 2).const_mul (q s)) using 1
        all_goals try with_reducible_and_instances rfl
        simp
        ring)
      (by
        intro y hy
        exact add_nonneg (hinit y) (mul_nonneg (hqpos _) (by positivity)))
      (by
        intro s hs
        have hb := hbound s hs (-A)
        have hq := mul_le_mul_of_nonneg_right (hqε s hs) (show 0≤1+A^2 by positivity)
        change -(0 : ℝ)≤u s (-A)+q s*(1+(-A)^2)
        rw [neg_sq]
        linarith)
      (by
        intro s hs
        have hb := hbound s hs A
        have hq := mul_le_mul_of_nonneg_right (hqε s hs) (show 0≤1+A^2 by positivity)
        change -(0 : ℝ)≤u s A+q s*(1+A^2)
        linarith)
      (by intro s hs y hy; exact hcbd s hs y)
      (by
        intro s hs y hy
        have hp := hpde s hs y
        have hb := hβ s hs y
        have hc' := hcbd s hs y
        have hkC : 2*B+2≤k-c s y := by dsimp [k]; linarith [le_max_left C 0]
        have hh1 := mul_nonneg (sub_nonneg.mpr hkC) (show 0≤1+y^2 by positivity)
        have hbr : 0≤(k-c s y)*(1+y^2)-1-2*β s y*y := by nlinarith [sq_nonneg y]
        have hbq := mul_nonneg (hqpos s) hbr
        nlinarith only [hp,hbq]) t ht x ((abs_le.mp hxA))
    simp only [neg_zero,zero_mul] at hcmp
    dsimp [q] at hcmp
    linarith
  intro t ht x
  by_contra hn
  have hu : u t x<0 := lt_of_not_ge hn
  let D := Real.exp (k*t)*(1+x^2)
  have hD : 0<D := mul_pos (Real.exp_pos _) (by positivity)
  have he : 0<(-u t x)/(2*D) := div_pos (neg_pos.mpr hu) (mul_pos (by norm_num) hD)
  have hh := hεbound ((-u t x)/(2*D)) he t ht x
  have heq : -((-u t x)/(2*D))*Real.exp (k*t)*(1+x^2)=u t x/2 := by
    dsimp [D]
    field_simp
  rw [heq] at hh
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ForwardComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue

namespace ForwardBurgers
variable {T : ℝ} (F : ForwardBurgers T)

lemma preserve_slope {a : ℝ} (ha : 0<a) (hT : 0≤T)
    (hinit : ∀ x,1/a≤F.jet 1 0 x) {t : ℝ} (ht : t∈Icc (0:ℝ) T) (x : ℝ) :
    1/(a+t)≤F.jet 1 t x := by
  obtain ⟨C,hC,hc⟩ := F.bound 0
  obtain ⟨L,hL,hl⟩ := F.growth
  have hap (s : ℝ) (hs : 0≤ s) : 0<a+s := by linarith
  have hi (s : ℝ) (hs : 0≤ s) : 0≤1/(a+s) ∧ 1/(a+s)≤1/a :=
    ⟨one_div_nonneg.mpr (hap s hs).le,one_div_le_one_div_of_le ha (by linarith)⟩
  have hd (s : ℝ) (hs : 0≤ s) : HasDerivAt (fun z : ℝ ↦ 1/(a+z)) (-(1/(a+s))^2) s := by
    have hh := ((hasDerivAt_id s).const_add a).inv (hap s hs).ne'
    convert! hh using 1
    · funext z; simp only [one_div, Pi.inv_apply, id_eq]
    · simp only [one_div, inv_pow, id_eq]; ring
  have hcont : ContinuousOn (fun p : ℝ×ℝ ↦ 1/(a+p.1)) ((Icc (0:ℝ) T)×ˢuniv) :=
    continuousOn_const.div (continuous_const.add continuous_fst).continuousOn
      (fun p hp ↦ (hap p.1 hp.1.1).ne')
  have hh := line_parabolic_nonneg (T := T) (B := 2*L) (C := C) (M := C+1/a)
    hT (by positivity) (add_nonneg hC (one_div_nonneg.mpr ha.le))
    (u := fun s y ↦ F.jet 1 s y-1/(a+s))
    (ut := fun s y ↦ (1/2:ℝ)*F.jet 3 s y-(F.jet 1 s y)^2-F.jet 0 s y*F.jet 2 s y+(1/(a+s))^2)
    (ux := F.jet 2) (uxx := F.jet 3)
    (β := fun s y ↦ -F.jet 0 s y) (c := fun s y ↦ -(F.jet 1 s y+1/(a+s)))
    ((F.continuous 1).continuousOn.sub hcont)
    (by intro s hs y; convert! (F.time1 s hs y).sub (hd s hs.1.le) using 1; ring)
    (by intro s hs y; simpa using (F.space 1 s y).sub_const (1/(a+s)))
    (by intro s hs y; exact F.space 2 s y)
    (by intro y; simpa only [add_zero] using sub_nonneg.mpr (hinit y))
    (by
      intro s hs y
      have h1 := (abs_le.mp (hc s hs y)).1
      have h2 := (hi s hs.1).2
      linarith)
    (by
      intro s hs y
      have h1 : -(F.jet 0 s y*y)≤L*(1+|y|)*|y| := calc
        _ ≤ |F.jet 0 s y*y| := neg_le_abs _
        _ = |F.jet 0 s y| *|y| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right (hl s ⟨hs.1.le,hs.2⟩ y) (abs_nonneg y)
      have h2 := mul_nonneg hL (sq_nonneg (|y|-1))
      have he : (-F.jet 0 s y)*y= -(F.jet 0 s y*y) := by ring
      rw [he]
      nlinarith [sq_nonneg y,sq_abs y])
    (by
      intro s hs y
      have h1 := (abs_le.mp (hc s ⟨hs.1.le,hs.2⟩ y)).1
      have h2 := (hi s hs.1.le).1
      linarith)
    (by intro s hs y; ring_nf; exact le_rfl) t ht x
  linarith

lemma score_nonneg {a : ℝ} (ha : 0<a) (hT : 0≤T)
    (hinit : ∀ x,1/a≤F.jet 1 0 x) {t : ℝ} (ht : t∈Icc (0:ℝ) T)
    {x : ℝ} (hx : 0≤x) : 0≤F.jet 0 t x := by
  have hm : Monotone (F.jet 0 t) := monotone_of_deriv_nonneg (fun y ↦ (F.space 0 t y).differentiableAt)
    (fun y ↦ by
      rw [(F.space 0 t y).deriv]
      exact (one_div_nonneg.mpr (by linarith [ht.1] : 0≤a+t)).trans (F.preserve_slope ha hT hinit ht y))
  simpa only [F.zero0] using hm hx

lemma preserve_concavity {a : ℝ} (ha : 0<a) (hT : 0≤T)
    (hinit : ∀ x,1/a≤F.jet 1 0 x)
    (hbinit : ∀ x,0≤x → F.jet 2 0 x≤0) {t : ℝ} (ht : t∈Icc (0:ℝ) T)
    {x : ℝ} (hx : 0≤x) : F.jet 2 t x≤0 := by
  obtain ⟨M,hM,hm⟩ := F.bound 1
  have hh := halfline_parabolic_nonneg (T := T) (B := 0) (C := 0) (M := M) hT le_rfl hM
    (u := fun s y ↦ -F.jet 2 s y)
    (ut := fun s y ↦ -((1/2:ℝ)*F.jet 4 s y-3*F.jet 1 s y*F.jet 2 s y-F.jet 0 s y*F.jet 3 s y))
    (ux := fun s y ↦ -F.jet 3 s y) (uxx := fun s y ↦ -F.jet 4 s y)
    (β := fun s y ↦ -F.jet 0 s y) (c := fun s y ↦ -3*F.jet 1 s y)
    (F.continuous 2).neg.continuousOn
    (by intro s hs y hy; exact (F.time2 s hs y).neg)
    (by intro s hs y; exact (F.space 2 s y).neg)
    (by intro s hs y; exact (F.space 3 s y).neg)
    (by intro y hy; exact neg_nonneg.mpr (hbinit y hy))
    (by intro s hs; simp only [F.zero2,neg_zero,le_refl])
    (by intro s hs y hy; have hh := (le_abs_self _).trans (hm s hs y); linarith)
    (by intro s hs y hy; exact neg_nonpos.mpr (F.score_nonneg ha hT hinit ⟨hs.1.le,hs.2⟩ hy.le))
    (by
      intro s hs y hy
      have hp := F.preserve_slope ha hT hinit ⟨hs.1.le,hs.2⟩ y
      have hpos := one_div_nonneg.mpr (show 0≤a+s by linarith [hs.1])
      nlinarith)
    (by intro s hs y hy; ring_nf; exact le_rfl) t ht x hx
  linarith

end ForwardBurgers
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_LogCoshTerminal
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

lemma logCoshTerminal_smooth (M : ℝ) : ContDiff ℝ ∞ (logCoshTerminal M) := by
  apply ContDiff.div_const
  apply ContDiff.log
  · exact contDiff_const.mul (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id))
  · intro x
    exact (mul_pos (by norm_num) (Real.cosh_pos (M*x))).ne'

lemma logCoshTerminal_hasDerivAt {M : ℝ} (hM : M≠0) (x : ℝ) :
    HasDerivAt (logCoshTerminal M) (Real.tanh (M*x)) x := by
  have hc := (Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd := ((hc.const_mul 2).log (mul_pos (by norm_num : (0:ℝ)<2) (Real.cosh_pos (M*x))).ne').div_const M
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  rw [Real.tanh_eq_sinh_div_cosh]
  simp only [Function.comp_apply, mul_one]
  field_simp

lemma tanh_scaled_hasDerivAt (M x : ℝ) :
    HasDerivAt (fun x ↦ Real.tanh (M*x)) (M*(1-(Real.tanh (M*x))^2)) x := by
  have hs := (Real.hasDerivAt_sinh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hc := (Real.hasDerivAt_cosh (M*x)).comp x ((hasDerivAt_id x).const_mul M)
  have hd := hs.div hc (Real.cosh_pos (M*x)).ne'
  simp_rw [Real.tanh_eq_sinh_div_cosh]
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Function.comp_apply, mul_one]
  field_simp [(Real.cosh_pos (M*x)).ne']

namespace JetExpr

lemma iteratedDeriv_fieldJet {R : ℕ → ℝ → ℝ} {σ : ℕ → JetExpr}
    (hd : ∀ j x, HasDerivAt (R j) (eval (fun i ↦ R i x) (σ j)) x) (e : JetExpr) (n : ℕ) :
    iteratedDeriv n (fun x ↦ eval (fun j ↦ R j x) e)=
      fun x ↦ eval (fun j ↦ R j x) (fieldJet σ e n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    exact (hasDerivAt_eval (fun j ↦ hd j x) _).deriv
end JetExpr

lemma logCoshTerminal_jets {M : ℝ} (hM : M≠0) :
    BoundedSmooth (deriv (logCoshTerminal M)) := by
  refine ⟨(contDiff_infty_iff_deriv.mp (logCoshTerminal_smooth M)).2,?_⟩
  intro n
  let σ : ℕ → JetExpr := fun _ ↦ JetExpr.mul (JetExpr.const M)
    (JetExpr.add (JetExpr.const 1) (JetExpr.mul (JetExpr.const (-1)) (JetExpr.mul (JetExpr.coord 0) (JetExpr.coord 0))))
  let R : ℕ → ℝ → ℝ := fun _ x ↦ Real.tanh (M*x)
  have hd : ∀ j x, HasDerivAt (R j) (JetExpr.eval (fun i ↦ R i x) (σ j)) x := by
    intro j x
    convert! tanh_scaled_hasDerivAt M x using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [σ,JetExpr.eval,R]
    ring
  have he : deriv (logCoshTerminal M)=fun x ↦ JetExpr.eval (fun j ↦ R j x) (JetExpr.coord 0) := by
    funext x
    exact (logCoshTerminal_hasDerivAt hM x).deriv
  rw [he,JetExpr.iteratedDeriv_fieldJet hd]
  exact JetExpr.uniform_bound (fun _ ↦ ⟨1,by norm_num,fun x ↦ (Real.abs_tanh_lt_one (M*x)).le⟩) _

lemma logCoshTerminal_smoothTerminal {M : ℝ} (hM : 0<M) : SmoothTerminal (logCoshTerminal M) := by
  have hs := logCoshTerminal_smooth M
  refine ⟨?_,hs,logCoshTerminal_jets hM.ne'⟩
  apply lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (ne_of_gt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0)))
  intro x
  have he := (logCoshTerminal_hasDerivAt hM.ne' x).deriv
  rw [he]
  exact_mod_cast (Real.abs_tanh_lt_one (M*x)).le

lemma logCoshTerminal_even (M x : ℝ) : logCoshTerminal M (-x)=logCoshTerminal M x := by
  simp only [logCoshTerminal,mul_neg,Real.cosh_neg]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_CoupledComparison
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology
namespace SKValue
namespace BackwardBurgers
variable {T : ℝ} (B : BackwardBurgers) (F : ForwardBurgers T) (b : ℝ)
lemma ratioJ_space (t x : ℝ) : HasDerivAt (B.ratioJ F b t) (B.ratioJx F b t x) x := by
  have hh := ((B.space 0 (b-t) x).mul (F.space 1 t x)).sub
    ((F.space 0 t x).mul (B.space 1 (b-t) x))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [ratioJ,ratioJx]
  ring
lemma ratioJx_space (t x : ℝ) : HasDerivAt (B.ratioJx F b t) (B.ratioJxx F b t x) x := by
  have hh := ((B.space 0 (b-t) x).mul (F.space 2 t x)).sub
    ((F.space 0 t x).mul (B.space 2 (b-t) x))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [ratioJx,ratioJxx]
  ring
lemma ratioJ_time {t x : ℝ} (ht : t∈Ioc (0:ℝ) T) (hb : T<b) (hx : 0<x) :
    HasDerivAt (B.ratioJ F b · x) (B.ratioJt F b t x) t := by
  have hbt : 0<b-t := by linarith [ht.2]
  have hd : HasDerivAt (fun s : ℝ ↦ b-s) (-1) t := (hasDerivAt_id t).const_sub b
  have h0 := (B.time0 (b-t) hbt x).comp t hd
  have h1 := (B.time1 (b-t) hbt x).comp t hd
  have hh := (h0.mul (F.time1 t ht x)).sub ((F.time0 t ht x).mul h1)
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [ratioJt,ratioJxx,ratioJx,ratioJ,n]
  field_simp [(B.positive (b-t) x hx).ne']
  ring
lemma ratioJ_continuous : Continuous (fun p : ℝ×ℝ ↦ B.ratioJ F b p.1 p.2) := by
  have hb (n : ℕ) : Continuous (fun p : ℝ×ℝ ↦ B.jet n (b-p.1) p.2) :=
    (B.continuous n).comp ((continuous_const.sub continuous_fst).prodMk continuous_snd)
  exact ((hb 0).mul (F.continuous 1)).sub ((F.continuous 0).mul (hb 1))

lemma ratioJ_nonneg {b a : ℝ} (ha : 0<a) (hT : 0≤T) (hb : T<b)
    (hinit : ∀ x,0≤x → 0≤B.ratioJ F b 0 x)
    (hslope : ∀ x,1/a≤F.jet 1 0 x)
    (hsconc : ∀ x,0≤x → F.jet 2 0 x≤0)
    (hw : ∀ t∈Icc (0:ℝ) T,∀ x,0≤x → B.jet 2 (b-t) x≤0)
    (hn : ∀ t∈Icc (0:ℝ) T,∀ x,0≤x → 0≤B.n (b-t) x) :
    ∀ t∈Icc (0:ℝ) T,∀ x,0≤x → 0≤B.ratioJ F b t x := by
  obtain ⟨R,hR,hr⟩ := B.bound 0
  obtain ⟨V,hV,hv⟩ := B.bound 1
  obtain ⟨A,hA,ha'⟩ := F.bound 0
  obtain ⟨S,hS,hs⟩ := F.growth
  apply halfline_parabolic_nonneg_linear (B := 0) (C := 0) (M := R*A+S*V) hT le_rfl (by positivity)
    (ut := B.ratioJt F b) (ux := B.ratioJx F b) (uxx := B.ratioJxx F b)
    (β := fun t x ↦ -(B.jet 1 (b-t) x/B.jet 0 (b-t) x))
    (c := fun t x ↦ -(B.jet 1 (b-t) x+F.jet 1 t x))
    (B.ratioJ_continuous F b).continuousOn
    (fun t ht x hx ↦ B.ratioJ_time F b ht hb hx)
    (fun t _ x ↦ B.ratioJ_space F b t x)
    (fun t _ x ↦ B.ratioJx_space F b t x) hinit
    (by intro t ht; simp [ratioJ,B.zero0,F.zero0])
    (by
      intro t ht x hx
      have h1 : |B.jet 0 (b-t) x*F.jet 1 t x|≤R*A := by
        rw [abs_mul]; exact mul_le_mul (hr _ _) (ha' t ht x) (abs_nonneg _) hR
      have h2 : |F.jet 0 t x*B.jet 1 (b-t) x|≤S*(1+x)*V := by
        rw [abs_mul]
        exact mul_le_mul (by simpa only [abs_of_nonneg hx] using hs t ht x) (hv _ _) (abs_nonneg _) (by positivity)
      have h3 := (abs_le.mp h1).1
      have h4 := (abs_le.mp h2).2
      dsimp [ratioJ]
      nlinarith [mul_nonneg (mul_nonneg hR hA) hx])
    (by intro t ht x hx; exact neg_nonpos.mpr (div_nonneg (B.slope_nonneg _ _) (B.positive _ _ hx).le))
    (by
      intro t ht x hx
      have h1 := F.preserve_slope ha hT hslope ⟨ht.1.le,ht.2⟩ x
      have h2 : 0<1/(a+t) := one_div_pos.mpr (by linarith [ht.1])
      linarith [B.slope_nonneg (b-t) x])
    (by
      intro t ht x hx
      have htc : t∈Icc (0:ℝ) T := ⟨ht.1.le,ht.2⟩
      have hrp := (B.positive (b-t) x hx).le
      have hsp := F.score_nonneg ha hT hslope htc hx.le
      have hnp := hn t htc x hx.le
      have hwp := hw t htc x hx.le
      have hscp := F.preserve_concavity ha hT hslope hsconc htc hx.le
      have hsrc1 := mul_nonneg (div_nonneg hsp hrp) hnp
      have hsrc2 := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hrp hsp) (add_nonpos hwp hscp)
      dsimp [ratioJt]
      linarith)

end BackwardBurgers
end SKValue

end

section

open Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue

lemma spatialJet_scale (a c : ℝ) (ψ : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    spatialJet (a*c) ψ n x=a*spatialJet c ψ n x := by dsimp [spatialJet]; ring

lemma spatialK_scale (a c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) :
    spatialK (a*c) ψ x=a*spatialK c ψ x-
      2*a*(1-a)*spatialJet c ψ 0 x*spatialJet c ψ 1 x := by
  simp only [spatialK,spatialJet_scale]
  ring
lemma spatialN_scale (a c : ℝ) (ψ : ℝ → ℝ) (x : ℝ) :
    spatialN (a*c) ψ x=a^2*spatialN c ψ x-
      2*a^2*(1-a)*(spatialJet c ψ 0 x)^2*spatialJet c ψ 2 x := by
  simp only [spatialN,spatialJet_scale]
  ring

lemma BackwardShape.scale {c a : ℝ} {ψ : ℝ → ℝ} (hs : BackwardShape c ψ)
    (hc : 0 < c) (ha : 0≤a) (ha1 : a≤1) : BackwardShape (a*c) ψ := by
  have hr (x : ℝ) (hx : 0≤x) : 0≤ spatialJet c ψ 0 x := by
    have hm := (strictMono_of_deriv_pos hs.convex).monotone hx
    rw [deriv_even_zero hs.even] at hm
    exact mul_nonneg hc.le hm
  have hv (x : ℝ) : 0≤ spatialJet c ψ 1 x := by
    simpa only [spatialJet,iteratedDeriv_one] using (mul_pos hc (hs.convex x)).le
  refine ⟨hs.even,hs.convex,?_,?_,?_⟩
  · intro x hx
    rw [spatialJet_scale]
    exact mul_nonpos_of_nonneg_of_nonpos ha (hs.w x hx)
  · intro x hx
    rw [spatialK_scale]
    have hn := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) ha)
      (sub_nonneg.mpr ha1)) (hr x hx)) (hv x)
    exact sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos ha (hs.k x hx)).trans hn)
  · intro x hx
    rw [spatialN_scale]
    have hn := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) (sq_nonneg a))
        (sub_nonneg.mpr ha1)) (sq_nonneg (spatialJet c ψ 0 x))) (hs.w x hx)
    exact sub_nonneg.mpr (hn.trans (mul_nonneg (sq_nonneg a) (hs.n x hx)))

lemma BackwardShape.lower {c d : ℝ} {ψ : ℝ → ℝ} (hs : BackwardShape c ψ)
    (hc : 0 < c) (hd : 0≤d) (hdc : d ≤ c) : BackwardShape d ψ := by
  have hh := hs.scale hc (div_nonneg hd hc.le) ((div_le_one hc).mpr hdc)
  rwa [div_mul_cancel₀ _ hc.ne'] at hh

lemma BackwardShape.evolve {c : ℝ} {ψ : ℝ → ℝ} (hs : BackwardShape c ψ)
    (hψ : SmoothTerminal ψ) (hc : 0 < c) {t : ℝ} (ht : 0≤t) :
    BackwardShape c (coleHopf c t ψ) := by
  let F := hψ.backwardBurgers hs.even hs.convex hc
  have h0 : coleHopf c 0 ψ=ψ := by funext x; exact coleHopf_zero c ψ x
  have hw : ∀ x,0≤x → F.jet 2 0 x≤0 := by
    simpa only [F,SmoothTerminal.backwardBurgers,scaledHeatJet,h0,spatialJet] using hs.w
  have hk : ∀ x,0≤x → F.k 0 x≤0 := by
    simpa only [F,BackwardBurgers.k,SmoothTerminal.backwardBurgers,scaledHeatJet,h0,
      spatialK,spatialJet] using hs.k
  have hn : ∀ x,0≤x → 0≤F.n 0 x := by
    simpa only [F,BackwardBurgers.n,SmoothTerminal.backwardBurgers,scaledHeatJet,h0,
      spatialN,spatialJet] using hs.n
  exact ⟨coleHopf_even hs.even c t,hψ.coleHopf_curvature_pos hs.convex hc t,
    fun x hx ↦ F.preserve_w hw ht hx,fun x hx ↦ F.preserve_k hk ht hx,
    fun x hx ↦ F.preserve_n hw hk hn ht hx⟩

lemma logCoshTerminal_gradient_jet (M : ℝ) (hM : M≠0) (n : ℕ) :
    iteratedDeriv n (deriv (logCoshTerminal M)) =
    fun x ↦ JetExpr.eval (fun _ ↦ Real.tanh (M*x)) (JetExpr.fieldJet
      (fun _ ↦ .mul (.const M) (.add (.const 1) (.mul (.const (-1)) (.mul (.coord 0) (.coord 0)))))
      (.coord 0) n) := by
  have hder : deriv (logCoshTerminal M)=fun x ↦ Real.tanh (M*x) :=
    funext (fun x ↦ (logCoshTerminal_hasDerivAt hM x).deriv)
  rw [hder]
  apply JetExpr.iteratedDeriv_fieldJet (R := fun _ x ↦ Real.tanh (M*x)) (e := .coord 0)
  intro j x
  convert! tanh_scaled_hasDerivAt M x using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [JetExpr.eval]
  ring

lemma logCoshTerminal_backwardShape {M c : ℝ} (hM : 0<M) (hc : 0 < c) (hcM : c≤M) :
    BackwardShape c (logCoshTerminal M) := by
  have hq (x : ℝ) : 0<1-(Real.tanh (M*x))^2 := by
    have hh := Real.abs_tanh_lt_one (M*x)
    have hh2 := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ)≤1)).mpr hh
    rw [sq_abs] at hh2
    nlinarith
  have htanh (x : ℝ) (hx : 0≤x) : 0≤Real.tanh (M*x) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg hM.le hx)) (Real.cosh_pos _).le
  have he1 (x : ℝ) : spatialJet M (logCoshTerminal M) 1 x=M^2*(1-(Real.tanh (M*x))^2) := by
    rw [spatialJet,logCoshTerminal_gradient_jet M hM.ne' 1]
    dsimp [JetExpr.fieldJet,JetExpr.D,JetExpr.eval]
    ring
  have he2 (x : ℝ) : spatialJet M (logCoshTerminal M) 2 x=
      -2*M^3*Real.tanh (M*x)*(1-(Real.tanh (M*x))^2) := by
    rw [spatialJet,logCoshTerminal_gradient_jet M hM.ne' 2]
    dsimp [JetExpr.fieldJet,JetExpr.D,JetExpr.eval]
    ring
  have hk (x : ℝ) : spatialK M (logCoshTerminal M) x=0 := by
    dsimp only [spatialK,spatialJet]
    simp only [logCoshTerminal_gradient_jet M hM.ne']
    dsimp [JetExpr.fieldJet,JetExpr.D,JetExpr.eval]
    ring
  have hn (x : ℝ) : spatialN M (logCoshTerminal M) x=0 := by
    dsimp only [spatialN,spatialJet]
    simp only [logCoshTerminal_gradient_jet M hM.ne']
    dsimp [JetExpr.fieldJet,JetExpr.D,JetExpr.eval]
    ring
  have hs : BackwardShape M (logCoshTerminal M) := by
    refine ⟨logCoshTerminal_even M,?_,?_,fun x hx ↦ (hk x).le,fun x hx ↦ (hn x).ge⟩
    · intro x
      have hj := he1 x
      simp only [spatialJet,iteratedDeriv_one] at hj
      have hp := mul_pos (sq_pos_of_pos hM) (hq x)
      rw [←hj] at hp
      exact pos_of_mul_pos_right hp hM.le
    · intro x hx
      rw [he2]
      have hp := mul_nonneg (mul_nonneg (pow_nonneg hM.le 3) (htanh x hx)) (hq x).le
      nlinarith
  exact hs.lower hM hc.le hcM

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_GaussianFactor
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue

lemma shiftedGaussian_hasLaw {h : ℝ} (hh : 0≤h) (x : ℝ) :
    HasLaw (fun z : ℝ ↦ x+Real.sqrt h*z) (gaussianReal x h.toNNReal) standardGaussian := by
  have hl : HasLaw (fun z : ℝ ↦ z) (gaussianReal 0 1) standardGaussian :=
    ⟨measurable_id.aemeasurable,by simp [standardGaussian]⟩
  have he := gaussianReal_const_add (gaussianReal_const_mul hl (Real.sqrt h)) x
  convert! he using 1; simp only [mul_zero,zero_add,mul_one]
  congr 1
  ext
  simp only [NNReal.coe_mk,Real.sq_sqrt hh,Real.coe_toNNReal _ hh]

lemma heat_eq_gaussian {f : ℝ → ℝ} (hf : Measurable f) {h : ℝ} (hh : 0≤h) (x : ℝ) :
    heat h f x=∫ y,f y ∂gaussianReal x h.toNNReal :=
  (shiftedGaussian_hasLaw hh x).integral_comp hf.aestronglyMeasurable

lemma gaussianPDF_square {a h : ℝ} (ha : 0<a) (hh : 0<h) (x y : ℝ) :
    gaussianPDFReal x h.toNNReal y*gaussianPDFReal 0 a.toNNReal y=
      gaussianPDFReal 0 (a+h).toNNReal x*
        gaussianPDFReal (a/(a+h)*x) (a*h/(a+h)).toNNReal y := by
  have hs : a+h≠0 := (add_pos ha hh).ne'
  have hv : a*h/(a+h)≠0 := ne_of_gt (div_pos (mul_pos ha hh) (add_pos ha hh))
  have hroot : Real.sqrt (2*Real.pi*h)*Real.sqrt (2*Real.pi*a)=
      Real.sqrt (2*Real.pi*(a+h))*Real.sqrt (2*Real.pi*(a*h/(a+h))) := by
    rw [←Real.sqrt_mul (by positivity),←Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hexp : -(y-x)^2/(2*h)-y^2/(2*a)=
      -x^2/(2*(a+h))-(y-a/(a+h)*x)^2/(2*(a*h/(a+h))) := by
    field_simp
    ring
  simp only [gaussianPDFReal,Real.coe_toNNReal _ ha.le,Real.coe_toNNReal _ hh.le,
    Real.coe_toNNReal _ (add_pos ha hh).le,Real.coe_toNNReal _ (div_pos (mul_pos ha hh) (add_pos ha hh)).le,sub_zero]
  calc
    _ = (Real.sqrt (2*Real.pi*h)*Real.sqrt (2*Real.pi*a))⁻¹*
        Real.exp (-(y-x)^2/(2*h)-y^2/(2*a)) := by
      simp only [sub_eq_add_neg,neg_div,Real.exp_add,mul_inv_rev]
      ring
    _ = (Real.sqrt (2*Real.pi*(a+h))*Real.sqrt (2*Real.pi*(a*h/(a+h))))⁻¹*
        Real.exp (-x^2/(2*(a+h))-(y-a/(a+h)*x)^2/(2*(a*h/(a+h)))) := by rw [hroot,hexp]
    _ = _ := by simp only [sub_eq_add_neg,neg_div,Real.exp_add,mul_inv_rev]; ring

lemma heat_gaussianFactor {a h : ℝ} (ha : 0<a) (hh : 0≤h)
    {f : ℝ → ℝ} (hf : Measurable f) (x : ℝ) :
    heat h (fun y ↦ gaussianPDFReal 0 a.toNNReal y*f y) x=
      gaussianPDFReal 0 (a+h).toNNReal x*
        heat (a*h/(a+h)) f (a/(a+h)*x) := by
  rcases hh.eq_or_lt with rfl | hh
  · simp [heat,ha.ne']
  have hah : 0<a+h := add_pos ha hh
  have hv : 0<a*h/(a+h) := div_pos (mul_pos ha hh) hah
  rw [heat_eq_gaussian (f := fun y ↦ gaussianPDFReal 0 a.toNNReal y*f y)
    ((measurable_gaussianPDFReal _ _).mul hf) hh.le]
  rw [integral_gaussianReal_eq_integral_smul (ne_of_gt (Real.toNNReal_pos.mpr hh))]
  rw [heat_eq_gaussian hf hv.le,integral_gaussianReal_eq_integral_smul (ne_of_gt (Real.toNNReal_pos.mpr hv))]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_eq_mul]
  rw [←mul_assoc,gaussianPDF_square ha hh x y,mul_assoc]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ForwardDensity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue

namespace ForwardDensityData
variable (D : ForwardDensityData)
lemma weight_pos (x : ℝ) : 0<D.weight x :=
  mul_pos (gaussianPDFReal_pos _ _ _ (Real.toNNReal_pos.mpr D.variance_pos).ne') (Real.exp_pos _)
lemma weight_measurable : Measurable D.weight :=
  (measurable_gaussianPDFReal _ _).mul ((measurable_const.mul D.smooth.smooth.continuous.measurable).exp)
lemma jet_initial (n : ℕ) (x : ℝ) :
    D.jet n x=forwardJet D.variance D.size D.potential n 0 x := by
  have he : coleHopf D.size 0 D.potential=D.potential := funext (coleHopf_zero _ _)
  have hv : D.variance^2/D.variance=D.variance := by field_simp
  simp [forwardJet,heatDen,heatScale,heatTime,D.variance_pos.ne',hv,scaledHeatJet,he,jet]

lemma jet_space (n : ℕ) (x : ℝ) : HasDerivAt (D.jet n) (D.jet (n+1) x) x := by
  have he (k : ℕ) : D.jet k=forwardJet D.variance D.size D.potential k 0 := funext (D.jet_initial k)
  rw [he n,he (n+1)]
  exact forwardJet_space D.smooth D.size_pos.le n 0 x
lemma jet_continuous (n : ℕ) : Continuous (D.jet n) :=
  continuous_iff_continuousAt.mpr (fun x ↦ (D.jet_space n x).continuousAt)

lemma evolve_weight (t : ℝ) (ht : 0≤t) (x : ℝ) :
    (D.evolve t ht).weight x=heat t D.weight x := by
  have he (v y : ℝ) : Real.exp (D.size*coleHopf D.size v D.potential y)=
      heat v (fun z ↦ Real.exp (D.size*D.potential z)) y := by
    simp only [coleHopf,ite_eq_right D.size_pos.ne']
    rw [mul_div_cancel₀ _ D.size_pos.ne']
    exact Real.exp_log (lipschitz_exp_integral_pos D.smooth.lipschitz D.size_pos.le y (Real.sqrt v))
  unfold weight
  rw [heat_gaussianFactor D.variance_pos ht
    (D.smooth.smooth.continuous.measurable.const_mul D.size).exp]
  simp only [evolve,he,heatScale,heatTime,heatDen_of_nonneg _ ht]
  congr 2
  field_simp [(add_pos_of_pos_of_nonneg D.variance_pos ht).ne']
  ring

lemma evolve_jet (t : ℝ) (ht : 0≤t) (n : ℕ) (x : ℝ) :
    (D.evolve t ht).jet n x=forwardJet D.variance D.size D.potential n t x := by
  let f := coleHopf D.size (heatTime D.variance t) D.potential
  let lam := heatScale D.variance t
  have hf := D.smooth.evolve D.size_pos.le (heatTime D.variance t)
  have hfd := hf.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hder : deriv (fun y ↦ f (lam*y))=fun y ↦ lam*deriv f (lam*y) := by
    funext y
    convert! ((hfd (lam*y)).hasDerivAt.comp y ((hasDerivAt_id y).const_mul lam)).deriv using 1
    all_goals try with_reducible_and_instances rfl
    simp
    ring
  have hjet : iteratedDeriv n (deriv (fun y ↦ f (lam*y))) x=
      lam^(n+1)*iteratedDeriv n (deriv f) (lam*x) := by
    rw [hder,iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_comp_const_mul (hf.jets.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))]
    ring
  change (if n=0 then x/(D.variance+t) else if n=1 then 1/(D.variance+t) else 0)-
    D.size*iteratedDeriv n (deriv (fun y ↦ f (lam*y))) x=_
  rw [hjet]
  simp only [forwardJet,heatDen_of_nonneg _ ht,scaledHeatJet]
  dsimp [f,lam]
  ring

lemma evolve_slope_concavity
    (h1 : ∀ x,1/D.variance≤D.jet 1 x)
    (h2 : ∀ x,0≤x → D.jet 2 x≤0) {t : ℝ} (ht : 0≤t) :
    (∀ x,1/(D.variance+t)≤(D.evolve t ht).jet 1 x) ∧
    (∀ x,0≤x → (D.evolve t ht).jet 2 x≤0) := by
  let F := D.smooth.forwardBurgers D.even D.variance_pos D.size_pos t
  have hi1 : ∀ x,1/D.variance≤F.jet 1 0 x := by
    simpa only [F,SmoothTerminal.forwardBurgers,←D.jet_initial] using h1
  have hi2 : ∀ x,0≤x → F.jet 2 0 x≤0 := by
    simpa only [F,SmoothTerminal.forwardBurgers,←D.jet_initial] using h2
  constructor
  · intro x
    rw [D.evolve_jet]
    exact F.preserve_slope D.variance_pos ht hi1 ⟨ht,le_rfl⟩ x
  · intro x hx
    rw [D.evolve_jet]
    exact F.preserve_concavity D.variance_pos ht hi1 hi2 ⟨ht,le_rfl⟩ hx

end ForwardDensityData
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_DensityJump
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace SKValue
namespace ForwardDensityData
lemma gaussian_weight (a : ℝ) (ha : 0<a) (x : ℝ) :
    (gaussian a ha).weight x=gaussianPDFReal 0 a.toNNReal x := by
  simp [weight,gaussian]
lemma gaussian_jet (a : ℝ) (ha : 0<a) (n : ℕ) (x : ℝ) :
    (gaussian a ha).jet n x=if n=0 then x/a else if n=1 then 1/a else 0 := by
  simp [jet,gaussian]

variable (D : ForwardDensityData) {φ : ℝ → ℝ}

lemma jump_weight (hφ : SmoothTerminal φ) (heven : ∀ x,φ (-x)=φ x)
    (δ : ℝ) (hδ : 0≤δ) (x : ℝ) :
    (D.jump hφ heven δ hδ).weight x=D.weight x*Real.exp (-δ*φ x) := by
  have hp : D.size+δ≠0 := (add_pos_of_pos_of_nonneg D.size_pos hδ).ne'
  have he : (D.size+δ)*(D.size/(D.size+δ)*D.potential x+(-δ/(D.size+δ))*φ x)=
      D.size*D.potential x+(-δ*φ x) := by field_simp [hp]
  simp only [weight,jump,he,Real.exp_add,mul_assoc,neg_mul]

lemma jump_jet (hφ : SmoothTerminal φ) (heven : ∀ x,φ (-x)=φ x)
    (δ : ℝ) (hδ : 0≤δ) (n : ℕ) (x : ℝ) :
    (D.jump hφ heven δ hδ).jet n x=D.jet n x+δ*iteratedDeriv n (deriv φ) x := by
  have hp : D.size+δ≠0 := (add_pos_of_pos_of_nonneg D.size_pos hδ).ne'
  have hd := D.smooth.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hf := hφ.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have he : deriv (fun y ↦ D.size/(D.size+δ)*D.potential y+(-δ/(D.size+δ))*φ y)=
      fun y ↦ D.size/(D.size+δ)*deriv D.potential y+(-δ/(D.size+δ))*deriv φ y := by
    funext y
    exact (((hd y).hasDerivAt.const_mul _).add ((hf y).hasDerivAt.const_mul _)).deriv
  simp only [jet,jump,he]
  rw [iteratedDeriv_fun_add
    ((contDiff_const.mul D.smooth.jets.smooth).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
    ((contDiff_const.mul hφ.jets.smooth).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
    iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
  field_simp
  ring

lemma jump_slope_concavity (hφ : SmoothTerminal φ) (heven : ∀ x,φ (-x)=φ x)
    (δ : ℝ) (hδ : 0≤δ)
    (hslope : ∀ x,1/D.variance≤D.jet 1 x)
    (hconc : ∀ x,0≤x → D.jet 2 x≤0)
    (hφslope : ∀ x,0 ≤ iteratedDeriv 1 (deriv φ) x)
    (hφconc : ∀ x,0≤x → iteratedDeriv 2 (deriv φ) x≤0) :
    (∀ x,1/D.variance≤(D.jump hφ heven δ hδ).jet 1 x) ∧
    (∀ x,0≤x → (D.jump hφ heven δ hδ).jet 2 x≤0) := by
  constructor
  · intro x
    rw [D.jump_jet]
    exact (hslope x).trans (le_add_of_nonneg_right (mul_nonneg hδ (hφslope x)))
  · intro x hx
    rw [D.jump_jet]
    exact add_nonpos (hconc x hx) (mul_nonpos_of_nonneg_of_nonpos hδ (hφconc x hx))
end ForwardDensityData
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue
namespace ExpGrowth
lemma const (c:ℝ) : ExpGrowth (fun _ : ℝ ↦ c) :=
  of_bound (abs_nonneg c) (fun _ ↦ le_rfl)
lemma add {f g:ℝ → ℝ} (hf:ExpGrowth f) (hg:ExpGrowth g) : ExpGrowth (fun x ↦ f x+g x) := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  obtain ⟨b,D,hb,hD,hg⟩ := hg
  refine ⟨a+b,C+D,add_nonneg ha hb,add_nonneg hC hD,?_⟩
  intro x
  apply (abs_add_le _ _).trans ((add_le_add (hf x) (hg x)).trans _)
  rw [add_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])) hC)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])) hD)
lemma neg {f:ℝ → ℝ} (hf:ExpGrowth f) : ExpGrowth (fun x ↦ -f x) := by
  simpa only [ExpGrowth,abs_neg] using hf
lemma sub {f g:ℝ → ℝ} (hf:ExpGrowth f) (hg:ExpGrowth g) : ExpGrowth (fun x ↦ f x-g x) :=
  hf.add hg.neg
lemma mul {f g:ℝ → ℝ} (hf:ExpGrowth f) (hg:ExpGrowth g) : ExpGrowth (fun x ↦ f x*g x) := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  obtain ⟨b,D,hb,hD,hg⟩ := hg
  refine ⟨a+b,C*D,add_nonneg ha hb,mul_nonneg hC hD,?_⟩
  intro x
  rw [abs_mul,add_mul,Real.exp_add]
  calc
    _ ≤ (C*Real.exp (a*|x|))*(D*Real.exp (b*|x|)) :=
      mul_le_mul (hf x) (hg x) (abs_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by ring
lemma pow {f:ℝ → ℝ} (hf:ExpGrowth f) (n:ℕ) : ExpGrowth (fun x ↦ f x^n) := by
  induction n with
  | zero => simpa using const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf
lemma gaussian_integrable {f:ℝ → ℝ} (hf:ExpGrowth f) (hm:Measurable f)
    {a:ℝ} (ha:0≤a) (x:ℝ) : Integrable f (gaussianReal x a.toNNReal) := by
  have hmp := (shiftedGaussian_hasLaw ha x).measurePreserving (by fun_prop)
  exact (hmp.integrable_comp hm.aestronglyMeasurable).mp (hf.shift_integrable hm x (Real.sqrt a))
lemma pdf_integrable {f:ℝ → ℝ} (hf:ExpGrowth f) (hm:Measurable f)
    {a:ℝ} (ha:0<a) (x:ℝ) : Integrable (fun y ↦ gaussianPDFReal x a.toNNReal y*f y) := by
  have hi := hf.gaussian_integrable hm ha.le x
  rw [gaussianReal_of_var_ne_zero _ (Real.toNNReal_pos.mpr ha).ne'] at hi
  have he := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
    (ae_of_all _ (fun _ ↦ gaussianPDF_lt_top))).mp hi
  simpa only [toReal_gaussianPDF,smul_eq_mul] using he
end ExpGrowth
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_Coercivity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SKValue.Certificate

theorem rational_identity (R K v B j z L : ℝ) :
    let b:=B+2*v
    z^2-12*R*v*b^2+6*v^4=
      (z+Q R K v b)^2+(z+b*v-2*R*b)*T R v j+
      (337/10000)*(R*j*(b-7*v)^2)+
      (183/2500)*(R*B*(b-(7/3)*v)^2)+
      (411/10000)*(K*v*(b-(9/2)*v)^2)+
      (11461/5000)*(v*B*(K+(1/4)*R-(1/7)*v)^2)+
      (647/10000)*(v*b-(14/5)*v^2-(13/4)*K*v+(4/3)*R*v)^2+
      W₂ R K v b j z L+L*((4663/5000)*v^2+(87/2500)*b*v)+remainder R K v B j := by
  dsimp only [Q,T,W₂,F₂,remainder]
  ring

theorem pointwise_coercivity {R K v B j z L : ℝ}
    (hR : 0≤R) (hK : 0≤K) (hv : 0≤v) (hB : 0≤B) (hj : 0≤j) (hL : 0≤L)
    (hS : 0≤z+(B+2*v)*v-2*R*(B+2*v)) :
    (1661507/1521000000)*v^4+W₂ R K v (B+2*v) j z L≤
      z^2-12*R*v*(B+2*v)^2+6*v^4 := by
  have he := rational_identity R K v B j z L
  dsimp only at he
  have hrem : (1661507/1521000000)*v^4 ≤ remainder R K v B j := by
    unfold remainder
    have hrest : 0≤
      (223/160000)*R^2*v^2+(4007/240000)*R^2*v*B+(1097/120000)*R^2*B^2+
      (83/80000)*R*K*v^2+(3343/24000)*R*K*v*B+(16259/23400000)*R*v^3+
      (30179/5460000)*R*v^2*B+(26/625)*R*v^2*j+(107/15000)*R*v*B^2+
      (3/2500)*R*v*B*j+(121/32500)*R*B^3+(11/10000)*R*B^2*j+
      (579/20000)*K^2*v^2+(207/2500)*K^2*v*B+(911/975000)*K*v^3+
      (349/420000)*K*v^2*B+(5011/5000)*K*v^2*j+(133/130000)*K*v*B^2+
      (87/2500)*K*v*B*j+
      (633799/621075000)*v^3*B+(10657/1690000)*v^2*B^2 := by positivity
    linarith
  have hT : 0≤T R v j := by unfold T; positivity
  have hST := mul_nonneg hS hT
  have h0 : 0≤(337/10000 : ℝ)*(R*j*(B+2*v-7*v)^2) := by positivity
  have h1 : 0≤(183/2500 : ℝ)*(R*B*(B+2*v-(7/3)*v)^2) := by positivity
  have h2 : 0≤(411/10000 : ℝ)*(K*v*(B+2*v-(9/2)*v)^2) := by positivity
  have h3 : 0≤(11461/5000 : ℝ)*(v*B*(K+(1/4)*R-(1/7)*v)^2) := by positivity
  have h4 : 0≤(647/10000 : ℝ)*(v*(B+2*v)-(14/5)*v^2-(13/4)*K*v+(4/3)*R*v)^2 := by positivity
  have hLC : 0≤L*((4663/5000)*v^2+(87/2500)*(B+2*v)*v) := by positivity
  have hs := sq_nonneg (z+Q R K v (B+2*v))
  linarith only [he,hrem,hST,h0,h1,h2,h3,h4,hLC,hs]
end SKValue.Certificate

end

section
namespace SKValue.Certificate
lemma growth_F {R K v b j:ℝ → ℝ} (hR:ExpGrowth R) (hK:ExpGrowth K)
    (hv:ExpGrowth v) (hb:ExpGrowth b) (hj:ExpGrowth j) :
    ExpGrowth (fun x ↦ F₂ (R x) (K x) (v x) (b x) (j x)) := by
  have h := (((((((ExpGrowth.const (4663/5000:ℝ)).mul (hv.pow 2)).mul hj).add ((ExpGrowth.const (6853/10000:ℝ)).mul (hv.pow 3))).sub (((ExpGrowth.const (1051/400:ℝ)).mul hK).mul (hv.pow 2))).sub (((ExpGrowth.const (1073/500:ℝ)).mul hR).mul (hv.pow 2))).sub (((hb.pow 2).mul ((((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (19/16:ℝ))).sub ((ExpGrowth.const (1/13:ℝ)).mul hv))).add (hb.mul ((((((((ExpGrowth.const (-2/1:ℝ)).mul hK).mul (ExpGrowth.const (19/16:ℝ))).mul hv).sub ((hR.mul (ExpGrowth.const (2331/10000:ℝ))).mul hv)).sub ((((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (73/48:ℝ))).mul hv)).sub ((ExpGrowth.const (53/12:ℝ)).mul (hv.pow 2))).sub (((ExpGrowth.const (87/2500:ℝ)).mul hj).mul hv)))))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  dsimp [F₂]
  ring
lemma growth_W {R K v b j z L:ℝ → ℝ} (hR:ExpGrowth R) (hK:ExpGrowth K)
    (hv:ExpGrowth v) (hb:ExpGrowth b) (hj:ExpGrowth j) (hz:ExpGrowth z) (hL:ExpGrowth L) :
    ExpGrowth (fun x ↦ W₂ (R x) (K x) (v x) (b x) (j x) (z x) (L x)) := by
  have hF:=growth_F hR hK hv hb hj
  have h := (((((((((ExpGrowth.const (2/1:ℝ)).mul hR).mul hv).mul ((((ExpGrowth.const (-1073/500:ℝ)).mul (hv.pow 2)).sub ((ExpGrowth.const (19/8:ℝ)).mul (hb.pow 2))).add (hb.mul (((ExpGrowth.const (2331/10000:ℝ)).mul hv).add ((ExpGrowth.const (73/24:ℝ)).mul hv))))).add (((((ExpGrowth.const (2/1:ℝ)).mul hv).mul hK).add (hR.mul hj)).mul (((ExpGrowth.const (-1051/400:ℝ)).mul (hv.pow 2)).add (((ExpGrowth.const (19/8:ℝ)).mul hb).mul hv)))).add (((hR.neg).mul hb).mul ((((((((ExpGrowth.const (4663/2500:ℝ)).mul hv).mul hj).add ((ExpGrowth.const (20559/10000:ℝ)).mul (hv.pow 2))).sub (((ExpGrowth.const (1051/200:ℝ)).mul hK).mul hv)).sub (((ExpGrowth.const (1073/250:ℝ)).mul hR).mul hv)).add ((ExpGrowth.const (1/13:ℝ)).mul (hb.pow 2))).add (hb.mul (((((((ExpGrowth.const (2/1:ℝ)).mul hK).mul (ExpGrowth.const (19/16:ℝ))).add (hR.mul (ExpGrowth.const (2331/10000:ℝ)))).add (((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (73/48:ℝ)))).add ((ExpGrowth.const (53/6:ℝ)).mul hv)).add ((ExpGrowth.const (87/2500:ℝ)).mul hj)))))).add (((hz.neg).sub (hb.mul hv)).mul ((((((((ExpGrowth.const (-2/1:ℝ)).mul hb).mul ((((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (19/16:ℝ))).sub ((ExpGrowth.const (1/13:ℝ)).mul hv))).add ((((ExpGrowth.const (2/1:ℝ)).mul hK).mul (ExpGrowth.const (19/16:ℝ))).mul hv)).add ((hR.mul (ExpGrowth.const (2331/10000:ℝ))).mul hv)).add ((((ExpGrowth.const (2/1:ℝ)).mul hR).mul (ExpGrowth.const (73/48:ℝ))).mul hv)).add ((ExpGrowth.const (53/12:ℝ)).mul (hv.pow 2))).add (((ExpGrowth.const (87/2500:ℝ)).mul hj).mul hv)))).add (((((hj.neg).mul hv).add (hK.mul hb)).sub hL).mul (((ExpGrowth.const (4663/5000:ℝ)).mul (hv.pow 2)).add (((ExpGrowth.const (87/2500:ℝ)).mul hb).mul hv)))).add (((hv.add hR).sub hK).mul hF))
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  dsimp [W₂]
  ring
end SKValue.Certificate

end

section
open MeasureTheory Set Filter
open scoped Topology
namespace SKValue.Certificate

lemma flux_derivative {r v w z s a d f:ℝ → ℝ} {x:ℝ}
    (hr:HasDerivAt r (v x) x) (hv:HasDerivAt v (w x) x)
    (hw:HasDerivAt w (z x) x) (hs:HasDerivAt s (a x) x)
    (ha:HasDerivAt a (d x) x) (hf:HasDerivAt f ((r x-s x)*f x) x)
    (hn:r x≠0) :
    HasDerivAt (fun y ↦ r y*F₂ (r y^2) (r y*s y) (v y) (-w y/r y)
      (a y-s y/r y*v y)*f y)
      (W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
        (z x) (-r x*d x)*f x) x := by
  have hR := hr.pow 2
  have hK := hr.mul hs
  have hb := hw.neg.div hr hn
  have hj := ha.sub ((hs.div hr hn).mul hv)
  have hF := (((((((hasDerivAt_const x (4663/5000:ℝ)).mul (hv.pow 2)).mul hj).add ((hasDerivAt_const x (6853/10000:ℝ)).mul (hv.pow 3))).sub (((hasDerivAt_const x (1051/400:ℝ)).mul hK).mul (hv.pow 2))).sub (((hasDerivAt_const x (1073/500:ℝ)).mul hR).mul (hv.pow 2))).sub (((hb.pow 2).mul ((((hasDerivAt_const x (2/1:ℝ)).mul hR).mul (hasDerivAt_const x (19/16:ℝ))).sub ((hasDerivAt_const x (1/13:ℝ)).mul hv))).add (hb.mul ((((((((hasDerivAt_const x (-2/1:ℝ)).mul hK).mul (hasDerivAt_const x (19/16:ℝ))).mul hv).sub ((hR.mul (hasDerivAt_const x (2331/10000:ℝ))).mul hv)).sub ((((hasDerivAt_const x (2/1:ℝ)).mul hR).mul (hasDerivAt_const x (73/48:ℝ))).mul hv)).sub ((hasDerivAt_const x (53/12:ℝ)).mul (hv.pow 2))).sub (((hasDerivAt_const x (87/2500:ℝ)).mul hj).mul hv)))))
  have hflux := (hr.mul hF).mul hf
  convert! hflux using 1
  · funext y
    dsimp [F₂]
    ring
  · dsimp [W₂,F₂]
    field_simp
    ring
end SKValue.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_DensityDerivative
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue
lemma gaussianPDFReal_derivative {a:ℝ} (ha:0<a) (x:ℝ) :
    HasDerivAt (gaussianPDFReal 0 a.toNNReal)
      (-(x/a)*gaussianPDFReal 0 a.toNNReal x) x := by
  have hd := (((((hasDerivAt_id x).pow 2).neg).div_const (2*a)).exp).const_mul
    (Real.sqrt (2*Real.pi*a))⁻¹
  convert! hd using 1
  · funext y
    simp only [gaussianPDFReal,Real.coe_toNNReal _ ha.le,sub_zero,
      Pi.neg_apply,Pi.pow_apply,id_eq]
  · simp only [gaussianPDFReal,Real.coe_toNNReal _ ha.le,sub_zero,
      Pi.neg_apply,Pi.pow_apply,id_eq]
    field_simp
    ring

namespace ForwardDensityData
variable (D:ForwardDensityData)
lemma weight_derivative (x:ℝ) : HasDerivAt D.weight (-D.jet 0 x*D.weight x) x := by
  have hψ := D.smooth.smooth.differentiable (by simp)
  have hd := (gaussianPDFReal_derivative D.variance_pos x).mul
    ((((hψ x).hasDerivAt).const_mul D.size).exp)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [jet,ite_true,iteratedDeriv_zero,weight]
  ring
lemma weight_exp_integrable {f:ℝ → ℝ} (hf:ExpGrowth f) (hm:Measurable f) :
    Integrable (fun x ↦ D.weight x*f x) := by
  have he := (ExpGrowth.exp_lipschitz D.smooth.lipschitz D.size_pos.le).mul hf
  have hm' : Measurable (fun x ↦ Real.exp (D.size*D.potential x)*f x) :=
    ((measurable_const.mul D.smooth.smooth.continuous.measurable).exp).mul hm
  simpa only [weight,mul_assoc] using he.pdf_integrable hm' D.variance_pos 0
lemma density_derivative {A:ℝ → ℝ} {c:ℝ} (hA:SmoothTerminal A) (x:ℝ) :
    HasDerivAt (fun y ↦ Real.exp (c*A y)*D.weight y)
      ((c*deriv A x-D.jet 0 x)*(Real.exp (c*A x)*D.weight x)) x := by
  have hd := ((((hA.smooth.differentiable (by simp)) x).hasDerivAt.const_mul c).exp).mul
    (D.weight_derivative x)
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  ring
end ForwardDensityData
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_ZeroFlux
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology
namespace SKValue

lemma integral_flux_zero {f g:ℝ → ℝ} (hc:ContinuousAt f 0)
    (hd:∀ x:ℝ,x≠0 → HasDerivAt f (g x) x) (hf:Integrable f) (hg:Integrable g) :
    (∫ x,g x)=0 := by
  have ht:Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a:=0)
      (fun x hx ↦ hd x (ne_of_gt hx)) hg.integrableOn hf.integrableOn
  have hb:Tendsto f atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a:=(-1:ℝ))
      (fun x hx ↦ hd x (by change x≤(-1:ℝ) at hx;linarith)) hg.integrableOn hf.integrableOn
  rw [←setIntegral_univ,←Iic_union_Ioi (a:=(0:ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hg.integrableOn hg.integrableOn,
    integral_Iic_of_hasDerivAt_of_tendsto hc.continuousWithinAt
      (fun x hx ↦ hd x (ne_of_lt hx)) hg.integrableOn hb,
    integral_Ioi_of_hasDerivAt_of_tendsto hc.continuousWithinAt
      (fun x hx ↦ hd x (ne_of_gt hx)) hg.integrableOn ht]
  ring

lemma ExpGrowth.zero_mul_continuousAt {F r f:ℝ → ℝ} (hF:ExpGrowth F)
    (hr:ContinuousAt r 0) (hr0:r 0=0) (hf:ContinuousAt f 0) :
    ContinuousAt (fun x ↦ r x*F x*f x) 0 := by
  obtain ⟨a,C,ha,hC,hb⟩ := hF
  have hh:Tendsto (fun x ↦ |r x| *(C*Real.exp (a*|x|))*|f x|) (𝓝 0) (𝓝 0) := by
    have he : Continuous (fun x:ℝ ↦ C*Real.exp (a*|x|)) := by fun_prop
    have hc : ContinuousAt (fun x:ℝ ↦ |r x| *(C*Real.exp (a*|x|))*|f x|) 0 :=
      (hr.abs.mul he.continuousAt).mul hf.abs
    simpa only [hr0,abs_zero,zero_mul] using hc.tendsto

  have hz:Tendsto (fun x ↦ r x*F x*f x) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall (fun x ↦ ?_)) hh
    rw [Real.norm_eq_abs,abs_mul,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)) (abs_nonneg _)
  simpa only [ContinuousAt,hr0,zero_mul] using hz
end SKValue

end

section

open MeasureTheory Set Filter
open scoped Topology
namespace SKValue

lemma ExpGrowth.div_odd_monotone {g r:ℝ → ℝ} {g' r':ℝ}
    (hg:ExpGrowth g) (hg0:g 0=0) (hr0:r 0=0)
    (hdg:HasDerivAt g g' 0) (hdr:HasDerivAt r r' 0) (hr':0 < r')
    (hodd:∀ x,r (-x)= -r x) (hmono:Monotone r) (hpos:∀ x,0<x → 0 < r x) :
    ExpGrowth (fun x ↦ g x/r x) := by
  have ht:Tendsto (fun x ↦ g x/r x) (𝓝[≠] 0) (𝓝 (g'/r')) := by
    have hgsl:=hdg.tendsto_slope_zero
    have hrsl:=hdr.tendsto_slope_zero
    simp only [zero_add,hg0,hr0,sub_zero,smul_eq_mul] at hgsl hrsl
    apply (hgsl.div hrsl hr'.ne').congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0:x≠0 := by simpa using hx
    change (x⁻¹*g x)/(x⁻¹*r x)=g x/r x
    field_simp
  obtain ⟨K,hK⟩ := ht.abs.isBoundedUnder_le
  have hn:∀ᶠ x in 𝓝 (0:ℝ),x≠0 → |g x/r x|≤K := by
    exact eventually_nhdsWithin_iff.mp hK
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp hn
  let δ:=ε/2
  have hδ:0<δ := by dsimp [δ];linarith
  have hrδ:0 < r δ := hpos δ hδ
  obtain ⟨a,C,ha,hC,hb⟩ := hg
  refine ⟨a,max (max K 0) (C/r δ),ha,le_trans (le_max_right K 0) (le_max_left _ _),?_⟩
  intro x
  by_cases hx:|x|<δ
  · have hnear:|g x/r x|≤ max K 0 := by
      by_cases hx0:x=0
      · subst x;simp [hg0]
      · exact (he (by simpa only [Real.dist_eq,sub_zero] using hx.trans (by dsimp [δ];linarith)) hx0).trans (le_max_left _ _)
    exact hnear.trans ((le_max_left _ _).trans (le_mul_of_one_le_right
      (le_trans (le_max_right K 0) (le_max_left _ _)) (Real.one_le_exp (mul_nonneg ha (abs_nonneg x)))))
  · have haway:r δ≤|r x| := by
      rw [not_lt] at hx
      by_cases hs:0≤x
      · rw [abs_of_nonneg hs] at hx
        exact (hmono hx).trans (le_abs_self _)
      · have hxs:x<0 := lt_of_not_ge hs
        rw [abs_of_neg hxs] at hx
        have hm:=hmono hx
        rw [hodd] at hm
        exact hm.trans (neg_le_abs _)
    have hbound:|g x/r x|≤(C/r δ)*Real.exp (a*|x|) := by
      rw [abs_div]
      calc
        _ ≤ (C*Real.exp (a*|x|))/(r δ) :=
          div_le_div₀ (mul_nonneg hC (Real.exp_pos _).le) (hb x) hrδ haway
        _ = _ := by ring
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
end SKValue

end

section

open MeasureTheory Set Filter
open scoped Topology
namespace SKValue.Certificate
lemma integral_W_zero {r v w z s a d f:ℝ → ℝ}
    (hr:∀ x,HasDerivAt r (v x) x) (hv:∀ x,HasDerivAt v (w x) x)
    (hw:∀ x,HasDerivAt w (z x) x) (hs:∀ x,HasDerivAt s (a x) x)
    (ha:∀ x,HasDerivAt a (d x) x) (hf:∀ x,HasDerivAt f ((r x-s x)*f x) x)
    (hz:Measurable z) (hd:Measurable d) (hr0:r 0=0) (hrn:∀ x,x≠0 → r x≠0)
    (hgr:ExpGrowth r) (hgv:ExpGrowth v) (hgz:ExpGrowth z) (hgs:ExpGrowth s)
    (_:ExpGrowth a) (hgd:ExpGrowth d) (hgb:ExpGrowth (fun x ↦ -w x/r x))
    (hgj:ExpGrowth (fun x ↦ a x-s x/r x*v x))
    (hint:∀ F:ℝ → ℝ,ExpGrowth F → Measurable F → Integrable (fun x ↦ F x*f x)) :
    (∫ x,W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
      (z x) (-r x*d x)*f x)=0 := by
  have hmr:Measurable r := (continuous_iff_continuousAt.mpr (fun x ↦ (hr x).continuousAt)).measurable
  have hmv:Measurable v := (continuous_iff_continuousAt.mpr (fun x ↦ (hv x).continuousAt)).measurable
  have hmw:Measurable w := (continuous_iff_continuousAt.mpr (fun x ↦ (hw x).continuousAt)).measurable
  have hms:Measurable s := (continuous_iff_continuousAt.mpr (fun x ↦ (hs x).continuousAt)).measurable
  have hma:Measurable a := (continuous_iff_continuousAt.mpr (fun x ↦ (ha x).continuousAt)).measurable
  have hF:=growth_F (hgr.pow 2) (hgr.mul hgs) hgv hgb hgj
  have hW:=growth_W (hgr.pow 2) (hgr.mul hgs) hgv hgb hgj hgz (hgr.neg.mul hgd)
  have hmF:Measurable (fun x ↦ F₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)) := by
    unfold F₂;fun_prop
  have hmW:Measurable (fun x ↦ W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
      (z x) (-r x*d x)) := by unfold W₂ F₂;fun_prop
  exact integral_flux_zero (hF.zero_mul_continuousAt (hr 0).continuousAt hr0 (hf 0).continuousAt)
    (fun x hx ↦ flux_derivative (hr x) (hv x) (hw x) (hs x) (ha x) (hf x) (hrn x hx))
    (hint _ (hgr.mul hF) (hmr.mul hmF)) (hint _ hW hmW)

lemma ForwardDensityData.integrable_density_factor (D:ForwardDensityData)
    {A F:ℝ → ℝ} (hA:SmoothTerminal A) {c:ℝ} (hc:0 ≤ c)
    (hF:ExpGrowth F) (hm:Measurable F) :
    Integrable (fun x ↦ F x*(Real.exp (c*A x)*D.weight x)) := by
  have hi:=D.weight_exp_integrable (hF.mul (ExpGrowth.exp_lipschitz hA.lipschitz hc))
    (hm.mul ((measurable_const.mul hA.smooth.continuous.measurable).exp))
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x;ring
end SKValue.Certificate

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_JetParity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace SKValue
lemma derivative_parity {f g:ℝ → ℝ} {e:ℝ}
    (hd:∀ x,HasDerivAt f (g x) x) (he:∀ x,f (-x)=e*f x) (x:ℝ) :
    g (-x)= -e*g x := by
  have h1:HasDerivAt (fun y ↦ f (-y)) (-g (-x)) x := by
    convert! (hd (-x)).comp x (hasDerivAt_neg x) using 1; ring
  have h2:HasDerivAt (fun y ↦ e*f y) (e*g x) x := (hd x).const_mul e
  have hh:(fun y ↦ f (-y))=(fun y ↦ e*f y) := funext he
  rw [hh] at h1
  have hh' := h1.unique h2
  linarith

lemma SmoothTerminal.spatialJet_space {A:ℝ → ℝ} (hA:SmoothTerminal A)
    (c:ℝ) (n:ℕ) (x:ℝ) :
    HasDerivAt (spatialJet c A n) (spatialJet c A (n+1) x) x := by
  have hd := (hA.jets.smooth.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) x).hasDerivAt
  rw [←iteratedDeriv_succ] at hd
  exact hd.const_mul c

lemma SmoothTerminal.spatialJet_growth {A:ℝ → ℝ} (hA:SmoothTerminal A)
    (c:ℝ) (n:ℕ) : ExpGrowth (spatialJet c A n) := by
  obtain ⟨C,hC,hb⟩ := hA.jets.bound n
  exact ExpGrowth.of_bound (mul_nonneg (abs_nonneg c) hC) (fun x ↦ by
    rw [spatialJet,abs_mul];exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg c))

lemma SmoothTerminal.spatialJet_parity {A:ℝ → ℝ} (hA:SmoothTerminal A)
    (heven:∀ x,A (-x)=A x) (c:ℝ) :
    (∀ x,spatialJet c A 0 (-x)= -spatialJet c A 0 x) ∧
    (∀ x,spatialJet c A 1 (-x)= spatialJet c A 1 x) ∧
    (∀ x,spatialJet c A 2 (-x)= -spatialJet c A 2 x) ∧
    (∀ x,spatialJet c A 3 (-x)= spatialJet c A 3 x) := by
  have h0:∀ x,spatialJet c A 0 (-x)= -spatialJet c A 0 x := by
    intro x
    have hd:∀ y,HasDerivAt A (deriv A y) y := fun y ↦
      ((hA.smooth.differentiable (by simp)) y).hasDerivAt
    have hp := derivative_parity hd (e:=1) (by simpa using heven) x
    simpa only [spatialJet,iteratedDeriv_zero,neg_one_mul,mul_neg] using congrArg (fun v ↦ c*v) hp
  have h1:∀ x,spatialJet c A 1 (-x)=spatialJet c A 1 x := by
    intro x
    simpa using derivative_parity (hA.spatialJet_space c 0) (e:= -1) (by simpa using h0) x
  have h2:∀ x,spatialJet c A 2 (-x)= -spatialJet c A 2 x := by
    intro x
    simpa using derivative_parity (hA.spatialJet_space c 1) (e:=1) (by simpa using h1) x
  have h3:∀ x,spatialJet c A 3 (-x)=spatialJet c A 3 x := by
    intro x
    simpa using derivative_parity (hA.spatialJet_space c 2) (e:= -1) (by simpa using h2) x
  exact ⟨h0,h1,h2,h3⟩

namespace ForwardDensityData
lemma jet_parity (D:ForwardDensityData) :
    (∀ x,D.jet 0 (-x)= -D.jet 0 x) ∧ (∀ x,D.jet 1 (-x)=D.jet 1 x) ∧
    (∀ x,D.jet 2 (-x)= -D.jet 2 x) := by
  obtain ⟨h0,h1,h2,h3⟩:=D.smooth.spatialJet_parity D.even D.size
  constructor
  · intro x
    change -x/D.variance-spatialJet D.size D.potential 0 (-x)=
      -(x/D.variance-spatialJet D.size D.potential 0 x)
    rw [h0];ring
  constructor
  · intro x
    change 1/D.variance-spatialJet D.size D.potential 1 (-x)=
      1/D.variance-spatialJet D.size D.potential 1 x
    rw [h1]
  · intro x
    simpa only [jet,show (2:ℕ)≠0 from by norm_num,show (2:ℕ)≠1 from by norm_num,
      ite_false,zero_sub,spatialJet] using congrArg Neg.neg (h2 x)
lemma jet_growth (D:ForwardDensityData) (n:ℕ) : ExpGrowth (D.jet n) := by
  have he:ExpGrowth (fun x:ℝ ↦ x/D.variance) := by
    have hx:ExpGrowth (fun x:ℝ ↦ x) := ⟨1,1,by norm_num,by norm_num,fun x ↦ by
      simp only [one_mul];exact (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)).trans (Real.add_one_le_exp |x|)⟩
    simpa only [div_eq_mul_inv] using hx.mul (ExpGrowth.const D.variance⁻¹)
  by_cases h0:n=0
  · subst n;exact he.sub (D.smooth.spatialJet_growth D.size 0)
  by_cases h1:n=1
  · subst n
    exact (ExpGrowth.const (1/D.variance)).sub (D.smooth.spatialJet_growth D.size 1)
  · change ExpGrowth (fun x ↦ (if n=0 then x/D.variance else if n=1 then 1/D.variance else 0)-
      D.size*iteratedDeriv n (deriv D.potential) x)
    simpa only [h0,h1,ite_false,zero_sub,spatialJet] using
      (D.smooth.spatialJet_growth D.size n).neg
end ForwardDensityData
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_IntegratedCoercivity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Set Filter
open scoped Topology
namespace SKValue.Certificate

lemma integrated_coercivity {r v w z s a d f:ℝ → ℝ}
    (hr:Measurable r) (hv:Measurable v) (hw:Measurable w) (hz:Measurable z)
    (hs:Measurable s) (ha:Measurable a) (hd:Measurable d)
    (hgv:ExpGrowth v) (hgw:ExpGrowth w) (hgz:ExpGrowth z)
    (hgr:ExpGrowth r) (hgs:ExpGrowth s) (hgd:ExpGrowth d)
    (hgb:ExpGrowth (fun x ↦ -w x/r x))
    (hgj:ExpGrowth (fun x ↦ a x-s x/r x*v x))
    (hint:∀ F:ℝ → ℝ,ExpGrowth F → Measurable F → Integrable (fun x ↦ F x*f x))
    (hf:∀ x,0≤f x) (hrn:∀ x,x≠0 → r x≠0)
    (hKv:∀ x,x≠0 → 0 ≤ r x*s x ∧ 0≤v x ∧ 0≤ -w x/r x-2*v x ∧
      0≤a x-s x/r x*v x ∧ 0≤ -r x*d x ∧
      0≤z x+(-w x/r x)*v x-2*(r x^2)*(-w x/r x))
    (hzero:(∫ x,W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
      (z x) (-r x*d x)*f x)=0) :
    (1/1000:ℝ)*(∫ x,v x^4*f x)≤∫ x,(z x^2-12*v x*w x^2+6*v x^4)*f x := by
  let W:=fun x ↦ W₂ (r x^2) (r x*s x) (v x) (-w x/r x) (a x-s x/r x*v x)
      (z x) (-r x*d x)
  have hWg:ExpGrowth W := growth_W (hgr.pow 2) (hgr.mul hgs) hgv hgb hgj hgz (hgr.neg.mul hgd)
  have hWm:Measurable W := by dsimp [W,W₂,F₂];fun_prop
  have hWi:=hint _ hWg hWm
  have hvi:=hint _ (hgv.pow 4) (hv.pow_const 4)
  have hMi:=hint _ (((hgz.pow 2).sub (((ExpGrowth.const 12).mul hgv).mul (hgw.pow 2))).add
      ((ExpGrowth.const 6).mul (hgv.pow 4))) (by fun_prop)
  have hP:∀ᵐ x:ℝ,((1661507/1521000000:ℝ)*v x^4+W x)*f x≤
      (z x^2-12*v x*w x^2+6*v x^4)*f x := by
    filter_upwards [show ∀ᵐ x:ℝ,x≠0 from by rw [ae_iff]; simp] with x hx
    obtain ⟨hK,hv0,hB,hj,hL,hS⟩:=hKv x hx
    have hp:=pointwise_coercivity (sq_nonneg (r x)) hK hv0 hB hj hL (by
      simpa only [sub_add_cancel] using hS)
    simp only [sub_add_cancel] at hp
    have he:(r x^2)*v x*(-w x/r x)^2=v x*w x^2 := by
      field_simp [hrn x hx]
    have hp':(1661507/1521000000:ℝ)*v x^4+W x≤z x^2-12*v x*w x^2+6*v x^4 := by
      dsimp [W]
      nlinarith only [hp,he]
    exact mul_le_mul_of_nonneg_right hp' (hf x)
  have hsum:Integrable (fun x ↦ ((1661507/1521000000:ℝ)*v x^4+W x)*f x) := by
    convert! (hvi.const_mul (1661507/1521000000:ℝ)).add hWi using 1
    all_goals try with_reducible_and_instances rfl
    funext x; simp only [Pi.add_apply]; ring
  have hi:=integral_mono_ae hsum hMi hP
  have he:(∫ x,((1661507/1521000000:ℝ)*v x^4+W x)*f x)=
      (1661507/1521000000:ℝ)*(∫ x,v x^4*f x) := by
    simp_rw [add_mul,mul_assoc]
    rw [integral_add (hvi.const_mul _) hWi,integral_const_mul,hzero,add_zero]
  rw [he] at hi
  have hvnon:0≤∫ x,v x^4*f x := integral_nonneg (fun x ↦ mul_nonneg (by positivity) (hf x))
  nlinarith
end SKValue.Certificate

end

section

open Set Filter MeasureTheory
open scoped Topology
namespace SKValue
lemma BackwardShape.certificate_signs {A:ℝ → ℝ} {c:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0 < c) (D:ForwardDensityData)
    (hsl:∀ x,0≤D.jet 1 x) (hsc:∀ x,0≤x → D.jet 2 x≤0)
    (hJ:∀ x,0≤x → 0≤ spatialJet c A 0 x*D.jet 1 x-D.jet 0 x*spatialJet c A 1 x) :
    ∀ x,x≠0 →
    0≤ spatialJet c A 0 x*D.jet 0 x ∧ 0≤ spatialJet c A 1 x ∧
    0≤ -spatialJet c A 2 x/spatialJet c A 0 x-2*spatialJet c A 1 x ∧
    0≤D.jet 1 x-D.jet 0 x/spatialJet c A 0 x*spatialJet c A 1 x ∧
    0≤ -spatialJet c A 0 x*D.jet 2 x ∧
    0≤ spatialJet c A 3 x+(-spatialJet c A 2 x/spatialJet c A 0 x)*spatialJet c A 1 x-
      2*(spatialJet c A 0 x^2)*(-spatialJet c A 2 x/spatialJet c A 0 x) := by
  obtain ⟨hr,hv,hw,hz⟩:=hA.spatialJet_parity hB.even c
  obtain ⟨hs,ha,hd⟩:=D.jet_parity
  have hr0:spatialJet c A 0 0=0 := by have hh:=hr 0;simp only [neg_zero] at hh;linarith
  have hs0:D.jet 0 0=0 := by have he:=hs 0;simp only [neg_zero] at he;linarith
  have hvpos (x:ℝ):0 < spatialJet c A 1 x := by
    simpa only [spatialJet,iteratedDeriv_one] using mul_pos hc (hB.convex x)
  have hrpos (x:ℝ) (hx:0<x):0 < spatialJet c A 0 x := by
    have hm:=strictMono_of_deriv_pos (fun y ↦ by rw [(hA.spatialJet_space c 0 y).deriv];exact hvpos y)
    simpa only [hr0] using hm hx
  have hspos (x:ℝ) (hx:0≤x):0≤D.jet 0 x := by
    have hm:=monotone_of_deriv_nonneg (fun y ↦ (D.jet_space 0 y).differentiableAt)
      (fun y ↦ by rw [(D.jet_space 0 y).deriv];exact hsl y)
    simpa only [hs0] using hm hx
  have hpositive (x:ℝ) (hx:0<x) :
      0≤ spatialJet c A 0 x*D.jet 0 x ∧ 0≤ spatialJet c A 1 x ∧
      0≤ -spatialJet c A 2 x/spatialJet c A 0 x-2*spatialJet c A 1 x ∧
      0≤D.jet 1 x-D.jet 0 x/spatialJet c A 0 x*spatialJet c A 1 x ∧
      0≤ -spatialJet c A 0 x*D.jet 2 x ∧
      0≤ spatialJet c A 3 x+(-spatialJet c A 2 x/spatialJet c A 0 x)*spatialJet c A 1 x-
        2*(spatialJet c A 0 x^2)*(-spatialJet c A 2 x/spatialJet c A 0 x) := by
    have hrp:=hrpos x hx
    refine ⟨mul_nonneg hrp.le (hspos x hx.le),(hvpos x).le,?_,?_,?_,?_⟩
    · have hk:=hB.k x hx.le
      dsimp only [spatialK] at hk
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hrp).mpr
      nlinarith
    · have hj:=hJ x hx.le
      apply (mul_nonneg_iff_of_pos_right hrp).mp
      field_simp
      nlinarith
    · exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hrp.le) (hsc x hx.le)
    · have hn:=hB.n x hx.le
      dsimp only [spatialN] at hn
      apply (mul_nonneg_iff_of_pos_right hrp).mp
      field_simp
      nlinarith
  intro x hx
  rcases lt_or_gt_of_ne hx with hn | hp
  · have hh:=hpositive (-x) (neg_pos.mpr hn)
    simpa only [hr,hv,hw,hz,hs,ha,hd,neg_mul_neg,neg_neg,div_neg,neg_div,neg_sq,neg_mul,mul_neg] using hh
  · exact hpositive x hp

lemma BackwardShape.integrated_certificate {A:ℝ → ℝ} {c:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0 < c) (D:ForwardDensityData)
    (hsl:∀ x,0≤D.jet 1 x) (hsc:∀ x,0≤x → D.jet 2 x≤0)
    (hJ:∀ x,0≤x → 0≤ spatialJet c A 0 x*D.jet 1 x-D.jet 0 x*spatialJet c A 1 x) :
    (1/1000:ℝ)*(∫ x,(spatialJet c A 1 x)^4*(Real.exp (c*A x)*D.weight x))≤
      ∫ x,((spatialJet c A 3 x)^2-12*spatialJet c A 1 x*(spatialJet c A 2 x)^2+
        6*(spatialJet c A 1 x)^4)*(Real.exp (c*A x)*D.weight x) := by
  let r:=spatialJet c A 0
  let v:=spatialJet c A 1
  let w:=spatialJet c A 2
  let z:=spatialJet c A 3
  let s:=D.jet 0
  let a:=D.jet 1
  let d:=D.jet 2
  let f:=fun x ↦ Real.exp (c*A x)*D.weight x
  obtain ⟨hr,hev,hw,hez⟩:=hA.spatialJet_parity hB.even c
  obtain ⟨hs,hea,hdd⟩:=D.jet_parity
  have hr0:r 0=0 := by have hh:=hr 0;change r (-0)= -r 0 at hh;simp only [neg_zero] at hh;linarith
  have hw0:w 0=0 := by have hh:=hw 0;change w (-0)= -w 0 at hh;simp only [neg_zero] at hh;linarith
  have hs0:s 0=0 := by have hh:=hs 0;change s (-0)= -s 0 at hh;simp only [neg_zero] at hh;linarith
  have hvpos (x:ℝ):0<v x := by
    simpa only [v,spatialJet,iteratedDeriv_one] using mul_pos hc (hB.convex x)
  have hrmono:StrictMono r := strictMono_of_deriv_pos (fun y ↦ by
    rw [(hA.spatialJet_space c 0 y).deriv];exact hvpos y)
  have hrpos:∀ x,0<x → 0 < r x := fun x hx ↦ by simpa only [hr0] using hrmono hx
  have hrn:∀ x,x≠0 → r x≠0 := fun x hx he ↦ hx (hrmono.injective (he.trans hr0.symm))
  have hg (n:ℕ):ExpGrowth (spatialJet c A n) := hA.spatialJet_growth c n
  have hgb:ExpGrowth (fun x ↦ -w x/r x) :=
    (hg 2).neg.div_odd_monotone (by change -w 0=0;rw [hw0];ring) hr0 ((hA.spatialJet_space c 2 0).neg)
      (hA.spatialJet_space c 0 0) (hvpos 0) hr hrmono.monotone hrpos
  have hgsr:ExpGrowth (fun x ↦ s x/r x) :=
    (D.jet_growth 0).div_odd_monotone hs0 hr0 (D.jet_space 0 0)
      (hA.spatialJet_space c 0 0) (hvpos 0) hr hrmono.monotone hrpos
  have hgj:ExpGrowth (fun x ↦ a x-s x/r x*v x) := (D.jet_growth 1).sub (hgsr.mul (hg 1))
  have hm (n:ℕ):Measurable (spatialJet c A n) :=
    (continuous_iff_continuousAt.mpr (fun x ↦ (hA.spatialJet_space c n x).continuousAt)).measurable
  have hmd (n:ℕ):Measurable (D.jet n) := (D.jet_continuous n).measurable
  have hint:∀ F:ℝ → ℝ,ExpGrowth F → Measurable F → Integrable (fun x ↦ F x*f x) :=
    fun F hF hmF ↦ Certificate.ForwardDensityData.integrable_density_factor D hA hc.le hF hmF
  have hzero:=Certificate.integral_W_zero (hA.spatialJet_space c 0) (hA.spatialJet_space c 1)
    (hA.spatialJet_space c 2) (D.jet_space 0) (D.jet_space 1)
    (D.density_derivative hA) (hm 3) (hmd 2) hr0 hrn (hg 0) (hg 1) (hg 3)
    (D.jet_growth 0) (D.jet_growth 1) (D.jet_growth 2) hgb hgj hint
  exact Certificate.integrated_coercivity (hm 0) (hm 1) (hm 2) (hm 3) (hmd 0) (hmd 1) (hmd 2)
    (hg 1) (hg 2) (hg 3) (hg 0) (D.jet_growth 0) (D.jet_growth 2) hgb hgj hint
    (fun x ↦ mul_nonneg (Real.exp_pos _).le (D.weight_pos x).le) hrn
    (hB.certificate_signs hA hc D hsl hsc hJ) hzero
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_CoupledDensity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology
namespace SKValue

lemma BackwardShape.gaussian_forwardShape {A:ℝ → ℝ} {c:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) {a:ℝ} (ha:0<a) :
    ForwardShape c A (ForwardDensityData.gaussian a ha) := by
  refine ⟨?_,?_,?_⟩
  · intro x;rw [ForwardDensityData.gaussian_jet];simp [ForwardDensityData.gaussian]
  · intro x hx;rw [ForwardDensityData.gaussian_jet];norm_num
  · intro x hx
    simp only [ForwardDensityData.gaussian_jet,ite_true,Nat.one_ne_zero,ite_false]
    have h0:spatialJet c A 0 0=0 := by simp [spatialJet,deriv_even_zero hB.even]
    let p:=fun y ↦ spatialJet c A 0 y-y*spatialJet c A 1 y
    have hd (y:ℝ):HasDerivAt p (-y*spatialJet c A 2 y) y := by
      convert! (hA.spatialJet_space c 0 y).sub ((hasDerivAt_id y).mul (hA.spatialJet_space c 1 y)) using 1; dsimp [p]; ring
    have hm:MonotoneOn p (Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y hy ↦ (hd y).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hd y).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ by
        rw [(hd y).deriv]
        exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (interior_subset hy)) (hB.w y (interior_subset hy)))
    have hh:=hm (show (0:ℝ)∈Ici 0 from by simp) hx hx
    have hp:p 0=0 := by simp [p,h0]
    rw [hp] at hh
    have hh':0≤p x/a := div_nonneg hh ha.le
    convert! hh' using 1; dsimp [p]; ring

lemma ForwardShape.evolve_coupled_interior {A:ℝ → ℝ} {c h t:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0 < c) (ht:0≤t) (hth:t<h) {D:ForwardDensityData}
    (hF:ForwardShape c (coleHopf c h A) D) (x:ℝ) (hx:0≤x) :
    0≤ scaledHeatJet c A 0 (h-t) x*forwardJet D.variance D.size D.potential 1 t x-
      forwardJet D.variance D.size D.potential 0 t x*scaledHeatJet c A 1 (h-t) x := by
  let B:=hA.backwardBurgers hB.even hB.convex hc
  let F:=D.smooth.forwardBurgers D.even D.variance_pos D.size_pos t
  have hinit:∀ y,0≤y → 0≤B.ratioJ F h 0 y := by
    intro y hy
    simpa only [BackwardBurgers.ratioJ,B,F,SmoothTerminal.forwardBurgers,
      SmoothTerminal.backwardBurgers,scaledHeatJet,sub_zero,←D.jet_initial,spatialJet]
      using hF.coupled y hy
  have hslope:∀ x,1/D.variance≤F.jet 1 0 x := by
    simpa only [F,SmoothTerminal.forwardBurgers,←D.jet_initial] using hF.slope
  have hsconc:∀ x,0≤x → F.jet 2 0 x≤0 := by
    simpa only [F,SmoothTerminal.forwardBurgers,←D.jet_initial] using hF.concave
  have hw:∀ u∈Icc (0:ℝ) t,∀ y,0≤y → B.jet 2 (h-u) y≤0 := by
    intro u hu y hy
    exact (hB.evolve hA hc (by linarith [hu.2])).w y hy
  have hn:∀ u∈Icc (0:ℝ) t,∀ y,0≤y → 0≤B.n (h-u) y := by
    intro u hu y hy
    exact (hB.evolve hA hc (by linarith [hu.2])).n y hy
  exact B.ratioJ_nonneg F D.variance_pos ht hth hinit hslope hsconc hw hn t ⟨ht,le_rfl⟩ x hx

lemma coupled_pair_continuous {A:ℝ → ℝ} {c h:ℝ} (hA:SmoothTerminal A)
    (hc:0 ≤ c) (D:ForwardDensityData) (x:ℝ) :
    Continuous (fun t:ℝ ↦ scaledHeatJet c A 0 (h-t) x*forwardJet D.variance D.size D.potential 1 t x-
      forwardJet D.variance D.size D.potential 0 t x*scaledHeatJet c A 1 (h-t) x) := by
  have hmap:Continuous (fun t:ℝ ↦ (h-t,x)) := (continuous_const.sub continuous_id).prodMk continuous_const
  have hmap':Continuous (fun t:ℝ ↦ (t,x)) := continuous_id.prodMk continuous_const
  have hb (n:ℕ):Continuous (fun t:ℝ ↦ scaledHeatJet c A n (h-t) x) := by
    have hf:=scaledHeatJet_continuous hA hc n
    have hh:=Continuous.comp hf hmap
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  have hf (n:ℕ):Continuous (fun t:ℝ ↦ forwardJet D.variance D.size D.potential n t x) := by
    have hf:=forwardJet_continuous D.smooth D.variance_pos D.size_pos.le n
    have hh:=Continuous.comp hf hmap'
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
  exact ((hb 0).mul (hf 1)).sub ((hf 0).mul (hb 1))

lemma ForwardShape.evolve {A:ℝ → ℝ} {c h:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0 < c) (hh:0≤h) {D:ForwardDensityData}
    (hF:ForwardShape c (coleHopf c h A) D) :
    ForwardShape c A (D.evolve h hh) := by
  obtain ⟨hsl,hsc⟩:=D.evolve_slope_concavity hF.slope hF.concave hh
  refine ⟨hsl,hsc,?_⟩
  intro x hx
  let R:=fun t ↦ scaledHeatJet c A 0 (h-t) x*forwardJet D.variance D.size D.potential 1 t x-
    forwardJet D.variance D.size D.potential 0 t x*scaledHeatJet c A 1 (h-t) x
  have hhR:0≤R h := by
    by_cases hh0:h=0
    · subst h
      simpa only [R,scaledHeatJet,sub_zero,←D.jet_initial,spatialJet] using hF.coupled x hx
    · have hhp:0<h := lt_of_le_of_ne hh (Ne.symm hh0)
      have hcR:Continuous R := coupled_pair_continuous hA hc.le D x
      have htend:Tendsto R (𝓝[<] h) (𝓝 (R h)) := hcR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      apply ge_of_tendsto htend
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hhp)] with t ht ht0
      exact hF.evolve_coupled_interior hA hB hc ht0.le ht x hx
  have he:coleHopf c 0 A=A := funext (coleHopf_zero c A)
  simpa only [R,scaledHeatJet,sub_self,he,←D.evolve_jet h hh,spatialJet] using hhR

lemma ForwardShape.jump {A:ℝ → ℝ} {c d:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape c A) (hc:0 < c) (hcd:c≤d) {D:ForwardDensityData}
    (hF:ForwardShape c A D) :
    ForwardShape d A (D.jump hA hB.even (d-c) (sub_nonneg.mpr hcd)) := by
  obtain ⟨hsl,hsc⟩:=D.jump_slope_concavity hA hB.even (d-c) (sub_nonneg.mpr hcd)
    hF.slope hF.concave (by simpa only [iteratedDeriv_one] using fun x ↦ (hB.convex x).le)
    (by
      intro x hx
      have hw:=hB.w x hx
      dsimp only [spatialJet] at hw
      nlinarith)
  refine ⟨hsl,hsc,?_⟩
  intro x hx
  simp only [D.jump_jet,spatialJet]
  have hj:=hF.coupled x hx
  dsimp only [spatialJet] at hj
  have hh:=mul_nonneg (div_nonneg (hc.le.trans hcd) hc.le) hj
  convert! hh using 1; field_simp; ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatDuality
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue
lemma ForwardDensityData.heat_pair_integrable (D:ForwardDensityData)
    {F:ℝ → ℝ} (hF:ExpGrowth F) (hm:Measurable F) (lam:ℝ) :
    Integrable (fun p:ℝ×ℝ ↦ D.weight p.2*F (p.2+lam*p.1)) (standardGaussian.prod volume) := by
  obtain ⟨a,C,ha,hC,hb⟩ := hF
  have he:ExpGrowth (fun x:ℝ ↦ C*Real.exp (a*|x|)) := by
    refine ⟨a,C,ha,hC,?_⟩
    intro x;rw [abs_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)]
  have hi:= (gaussian_exp_abs_integrable (a*|lam|)).mul_prod
    (D.weight_exp_integrable he (by fun_prop))
  apply hi.mono' ((D.weight_measurable.comp measurable_snd).mul (hm.comp (by fun_prop))).aestronglyMeasurable
  filter_upwards [] with p
  change ‖D.weight p.2*F (p.2+lam*p.1)‖≤_
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (D.weight_pos p.2)]
  have hh:=mul_le_mul_of_nonneg_left (expGrowth_shift_bound ha hC hb p.2 lam p.1) (D.weight_pos p.2).le
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma ForwardDensityData.heat_duality (D:ForwardDensityData)
    {F:ℝ → ℝ} (hF:ExpGrowth F) (hm:Measurable F) (h:ℝ) :
    (∫ x,D.weight x*heat h F x)=(∫ x,heat h D.weight x*F x) := by
  let lam:=Real.sqrt h
  have hi:=D.heat_pair_integrable hF hm lam
  have hmp:MeasurePreserving (fun p:ℝ×ℝ ↦ (p.1,p.2-lam*p.1))
      (standardGaussian.prod volume) (standardGaussian.prod volume) := by
    apply (MeasurePreserving.id standardGaussian).skew_product
      (g:=fun z x:ℝ ↦ x-lam*z) (by fun_prop)
    exact ae_of_all _ (fun z ↦ map_sub_right_eq_self volume (lam*z))
  have hi':Integrable (fun p:ℝ×ℝ ↦ D.weight (p.2-lam*p.1)*F p.2) (standardGaussian.prod volume) := by
    convert! hmp.integrable_comp_of_integrable hi using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp only [Function.comp_apply,sub_add_cancel]
  calc
    _ = ∫ x,∫ z,D.weight x*F (x+lam*z) ∂standardGaussian := by
      simp only [heat,lam,integral_const_mul]
    _ = ∫ z,(∫ x,D.weight x*F (x+lam*z)) ∂standardGaussian := (integral_integral_swap hi).symm
    _ = ∫ z,(∫ x,D.weight (x-lam*z)*F x) ∂standardGaussian := by
      apply integral_congr_ae
      filter_upwards [] with z
      have he:=integral_add_right_eq_self (μ:=volume) (fun x ↦ D.weight (x-lam*z)*F x) (lam*z)
      simpa only [add_sub_cancel_right] using he
    _ = ∫ x,∫ z,D.weight (x-lam*z)*F x ∂standardGaussian := integral_integral_swap hi'
    _ = ∫ x,heat h D.weight x*F x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_mul_const]
      congr 1
      change (∫ z,D.weight (x-lam*z) ∂standardGaussian)=∫ z,D.weight (x+lam*z) ∂standardGaussian
      rw [←gaussian_integral_neg (fun z ↦ D.weight (x+lam*z))]
      simp_rw [mul_neg,←sub_eq_add_neg]
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators ContDiff
namespace SKValue
lemma weightedJet_bounded {ψ f : ℝ → ℝ} (hψ : BoundedSmooth (deriv ψ))
    (hf : BoundedSmooth f) (c : ℝ) (n : ℕ) : BoundedSmooth (weightedJet c ψ f n) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.deriv.add (ih.mul (hψ.const_mul c))
lemma weighted_iteratedDeriv {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)*f x)=
      fun x ↦ Real.exp (c*ψ x)*weightedJet c ψ f n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := hψ.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
    have hj := (weightedJet_bounded hψ.jets hf c n).smooth.differentiable
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
    convert! ((((hd x).hasDerivAt.const_mul c).exp).mul (hj x).hasDerivAt).deriv using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [weightedJet]
    ring
lemma weighted_growth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ExpGrowth (iteratedDeriv n (fun x ↦ Real.exp (c*ψ x)*f x)) := by
  rw [weighted_iteratedDeriv hψ hf c n]
  obtain ⟨C,hC,hb⟩ := (weightedJet_bounded hψ.jets hf c n).bound_zero
  exact (ExpGrowth.exp_lipschitz hψ.lipschitz hc).mul_bounded hC hb

lemma responseJet_continuous {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Continuous (fun p : ℝ×ℝ ↦ responseJet c ψ f n p.1 p.2) := by
  exact (heat_jet_continuous ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth)
    (weighted_growth hψ hf hc) n).div
    (heat_continuous (Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous))
      (ExpGrowth.exp_lipschitz hψ.lipschitz hc))
    (fun p ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc p.2 (Real.sqrt p.1)).ne')
lemma responseJet_smooth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (responseJet c ψ f n t) := by
  exact (smooth_iteratedDeriv
    (heat_contDiff ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth) (weighted_growth hψ hf hc) t) n).div
    (heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
      (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) t)
    (fun x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne')
lemma responseJet_space {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (t x : ℝ) :
    HasDerivAt (responseJet c ψ f n t)
      (responseJet c ψ f (n+1) t x-responseJet c ψ f n t x*baseJet c ψ 1 t x) x := by
  have hnum := heat_contDiff ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth) (weighted_growth hψ hf hc) t
  have hden := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) t
  have hp := (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hd := (((hnum.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) x).hasDerivAt).div
    ((hden.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne') x).hasDerivAt hp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [responseJet,baseJet,normalizedJet]
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  field_simp
lemma responseJet_time {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c t : ℝ} (hc : 0 ≤ c) (ht : 0<t) (n : ℕ) (x : ℝ) :
    HasDerivAt (responseJet c ψ f n · x)
      ((1/2:ℝ)*(responseJet c ψ f (n+2) t x-responseJet c ψ f n t x*baseJet c ψ 2 t x)) t := by
  have hp := (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hd := (heat_jet_time ((contDiff_const.mul hψ.smooth).exp.mul hf.smooth)
    (weighted_growth hψ hf hc) n x ht).div
      (heat_jet_time ((contDiff_const.mul hψ.smooth).exp)
        (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc) 0 x ht) hp
  convert! hd using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [responseJet,baseJet,normalizedJet]
  simp only [iteratedDeriv_zero,zero_add]
  field_simp
lemma responseJet_bound {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ∃ C:ℝ,0≤C ∧ ∀ t x,|responseJet c ψ f n t x|≤C := by
  obtain ⟨C,hC,hb⟩ := (weightedJet_bounded hψ.jets hf c n).bound_zero
  refine ⟨C,hC,?_⟩
  intro t x
  have hs : ContDiff ℝ ∞ (fun y ↦ Real.exp (c*ψ y)*f y) := (contDiff_const.mul hψ.smooth).exp.mul hf.smooth
  have hp : 0<heat t (fun y ↦ Real.exp (c*ψ y)) x := lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)
  rw [responseJet,heat_iteratedDeriv hs (weighted_growth hψ hf hc),abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  apply heat_relative_bound ((Real.continuous_exp.comp (continuous_const.mul hψ.smooth.continuous)).measurable)
    (smooth_iteratedDeriv hs n).continuous.measurable (ExpGrowth.exp_lipschitz hψ.lipschitz hc)
    (weighted_growth hψ hf hc n)
  intro y
  rw [weighted_iteratedDeriv hψ hf c n,abs_mul,abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm,Function.comp_apply,Pi.mul_apply] using mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos (c*ψ y)).le
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TestHeat
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma linear_derivative_tower_bounded {ι : Type*} (S : ℕ → ι → ℝ → ℝ)
    (b : ι → ℝ → ℝ) (hs : ∀ j a,ContDiff ℝ ∞ (S j a))
    (hbs : ∀ a,ContDiff ℝ ∞ (b a))
    (hd : ∀ j a,deriv (S j a)=fun x ↦ S (j+1) a x-S j a x*b a x)
    (hb : ∀ j,∃ C:ℝ,0≤C ∧ ∀ a x,|S j a x|≤C)
    (hbb : ∀ n,∃ C:ℝ,0≤C ∧ ∀ a x,|iteratedDeriv n (b a) x|≤C) :
    ∀ n j:ℕ,∃ C:ℝ,0≤C ∧ ∀ a x,|iteratedDeriv n (S j a) x|≤C := by
  classical
  choose B hB hbB using hbb
  intro n
  induction n using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => intro j;simpa only [iteratedDeriv_zero] using hb j
    | succ n =>
      have hlo : ∀ k j:ℕ,∃ C:ℝ,0≤C ∧
          (k≤n → ∀ a x,|iteratedDeriv k (S j a) x|≤C) := by
        intro k j
        by_cases hk:k≤n
        · obtain ⟨C,hC,hbC⟩ := ih k (Nat.lt_succ_of_le hk) j
          exact ⟨C,hC,fun _ ↦ hbC⟩
        · exact ⟨0,le_rfl,fun h ↦ (hk h).elim⟩
      choose C hC hbound using hlo
      intro j
      refine ⟨C n (j+1)+∑ k∈Finset.range (n+1),(n.choose k:ℝ)*C k j*B (n-k),?_,?_⟩
      · exact add_nonneg (hC _ _) (Finset.sum_nonneg (fun k _ ↦
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC _ _)) (hB _)))
      · intro a x
        rw [iteratedDeriv_succ',hd,
          iteratedDeriv_fun_sub
            ((hs (j+1) a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            (((hs j a).mul (hbs a)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
          iteratedDeriv_fun_mul
            ((hs j a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
            ((hbs a).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt]
        apply (abs_sub _ _).trans
        apply add_le_add (hbound n (j+1) le_rfl a x)
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk':k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg (n.choose k))]
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hbound k j hk' a x) (Nat.cast_nonneg _))
          (hbB (n-k) a x) (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC _ _))

lemma responseJet_uniform_jets {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) :
    ∀ n j:ℕ,∃ C:ℝ,0≤C ∧ ∀ t x,|iteratedDeriv n (responseJet c ψ f j t) x|≤C := by
  have hs := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
  have hp (t x:ℝ) : heat t (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
    (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  have hb := exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc
  apply linear_derivative_tower_bounded (responseJet c ψ f) (baseJet c ψ 1)
    (responseJet_smooth hψ hf hc)
    (normalizedJet_smooth hs hp 1)
    (fun j t ↦ funext (fun x ↦ (responseJet_space hψ hf hc j t x).deriv))
    (responseJet_bound hψ hf hc)
  intro n
  exact normalizedJet_uniform_bounded hs hp hb n 1

lemma responseJet_boundedSmooth {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n:ℕ) (t:ℝ) :
    BoundedSmooth (responseJet c ψ f n t) := by
  refine ⟨responseJet_smooth hψ hf hc n t,?_⟩
  intro k
  obtain ⟨C,hC,hb⟩ := responseJet_uniform_jets hψ hf hc k n
  exact ⟨C,hC,hb t⟩

lemma baseJet_space {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    {c : ℝ} (hc : 0 ≤ c) (n:ℕ) (t x:ℝ) :
    HasDerivAt (baseJet c ψ n t)
      (baseJet c ψ (n+1) t x-baseJet c ψ n t x*baseJet c ψ 1 t x) x := by
  have hs := heat_contDiff ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
  have hp (t x:ℝ) : heat t (fun y ↦ Real.exp (c*ψ y)) x≠0 :=
    (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne'
  exact ((normalizedJet_smooth hs hp n t).differentiable
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne' x).hasDerivAt.congr_deriv
      (congrFun (normalizedJet_deriv hs hp n t) x)

lemma responseJet_second {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c : ℝ} (hc : 0 ≤ c) (n:ℕ) (t x:ℝ) :
    deriv (deriv (responseJet c ψ f n t)) x=
      responseJet c ψ f (n+2) t x-2*responseJet c ψ f (n+1) t x*baseJet c ψ 1 t x-
        responseJet c ψ f n t x*baseJet c ψ 2 t x+
          2*responseJet c ψ f n t x*(baseJet c ψ 1 t x)^2 := by
  have hd : deriv (responseJet c ψ f n t)=fun y ↦ responseJet c ψ f (n+1) t y-
      responseJet c ψ f n t y*baseJet c ψ 1 t y :=
    funext (fun y ↦ (responseJet_space hψ hf hc n t y).deriv)
  rw [hd]
  convert! ((responseJet_space hψ hf hc (n+1) t x).sub
    ((responseJet_space hψ hf hc n t x).mul (baseJet_space hψ hc 1 t x))).deriv using 1
  all_goals try with_reducible_and_instances rfl
  simp only [show n+1+1=n+2 by omega]
  ring

lemma responseJet_heat_drift {ψ f : ℝ → ℝ} (hψ : SmoothTerminal ψ)
    (hf : BoundedSmooth f) {c t : ℝ} (hc : 0 ≤ c) (ht : 0<t) (n:ℕ) (x:ℝ) :
    HasDerivAt (responseJet c ψ f n · x)
      ((1/2:ℝ)*deriv (deriv (responseJet c ψ f n t)) x+
        baseJet c ψ 1 t x*deriv (responseJet c ψ f n t) x) t := by
  convert! responseJet_time hψ hf hc ht n x using 1
  all_goals try with_reducible_and_instances rfl
  rw [responseJet_second hψ hf hc,(responseJet_space hψ hf hc n t x).deriv]
  ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ResponseJets
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma baseJet_continuous {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c:ℝ} (hc:0 ≤ c) (j:ℕ) :
    Continuous (fun p:ℝ×ℝ ↦ baseJet c ψ j p.1 p.2) :=
  heat_normalizedJet_continuous ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
    (fun t x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne') j
lemma baseJet_time {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c t:ℝ} (hc:0 ≤ c) (ht:0<t) (j:ℕ) (x:ℝ) :
    HasDerivAt (baseJet c ψ j · x)
      ((1/2:ℝ)*(baseJet c ψ (j+2) t x-baseJet c ψ j t x*baseJet c ψ 2 t x)) t :=
  heat_normalizedJet_time ((contDiff_const.mul hψ.smooth).exp)
    (exp_iteratedDeriv_growth hψ.lipschitz hψ.smooth hψ.jets hc)
    (fun t x ↦ (lipschitz_exp_integral_pos hψ.lipschitz hc x (Real.sqrt t)).ne') j x ht
lemma combinedJet_continuous {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (j:ℕ) : Continuous (fun p:ℝ×ℝ ↦ combinedJet c ψ f j p.1 p.2) := by
  unfold combinedJet
  split_ifs
  · exact baseJet_continuous hψ hc _
  · exact responseJet_continuous hψ hf hc _
lemma combinedJet_bound {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (j:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ t x,|combinedJet c ψ f j t x|≤C := by
  unfold combinedJet
  split_ifs
  · exact exp_heat_normalizedJet_bound hψ.lipschitz hψ.smooth hψ.jets hc _
  · exact responseJet_bound hψ hf hc _
lemma combinedJet_space {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (j:ℕ) (t x:ℝ) :
    HasDerivAt (combinedJet c ψ f j t)
      (combinedJet c ψ f (j+2) t x-combinedJet c ψ f j t x*combinedJet c ψ f 2 t x) x := by
  change HasDerivAt (fun y ↦ combinedJet c ψ f j t y)
    (combinedJet c ψ f (j+2) t x-combinedJet c ψ f j t x*combinedJet c ψ f 2 t x) x
  have he:(j+2)/2=j/2+1 := by omega
  have hm:(j+2)%2=j%2 := by omega
  by_cases h:j%2=0
  · simpa only [combinedJet,he,hm,h,show (2:ℕ)%2=0 from rfl,show (2:ℕ)/2=1 from rfl,ite_true] using
      baseJet_space hψ hc (j/2) t x
  · simpa only [combinedJet,he,hm,h,show (2:ℕ)%2=0 from rfl,show (2:ℕ)/2=1 from rfl,ite_true,ite_false] using
      responseJet_space hψ hf hc (j/2) t x
lemma combinedJet_time {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c t:ℝ} (hc:0 ≤ c) (ht:0<t) (j:ℕ) (x:ℝ) :
    HasDerivAt (combinedJet c ψ f j · x)
      ((1/2:ℝ)*(combinedJet c ψ f (j+4) t x-combinedJet c ψ f j t x*combinedJet c ψ f 4 t x)) t := by
  have he:(j+4)/2=j/2+2 := by omega
  have hm:(j+4)%2=j%2 := by omega
  simp only [combinedJet,he,hm,show (4:ℕ)%2=0 from rfl,show (4:ℕ)/2=2 from rfl,ite_true]
  split_ifs
  · exact baseJet_time hψ hc ht (j/2) x
  · exact responseJet_time hψ hf hc ht (j/2) x
namespace JetExpr
lemma eval_responseσx (R:ℕ → ℝ) (j:ℕ) : eval R (responseσx j)=R (j+2)-R j*R 2 := by
  simp only [responseσx,eval];ring
lemma eval_responseσt (R:ℕ → ℝ) (j:ℕ) : eval R (responseσt j)=(1/2:ℝ)*(R (j+4)-R j*R 4) := by
  simp only [responseσt,eval];ring
end JetExpr
lemma responseJet_zero_expr {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) (t:ℝ) :
    iteratedDeriv n (responseJet c ψ f 0 t)=
      fun x ↦ JetExpr.eval (fun j ↦ combinedJet c ψ f j t x) (JetExpr.responseExpr n) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero,JetExpr.responseExpr,JetExpr.eval];rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    apply HasDerivAt.deriv
    apply JetExpr.hasDerivAt_eval
    intro j
    simpa only [JetExpr.eval_responseσx] using combinedJet_space hψ hf hc j t x
lemma responseJet_joint_jets {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) :
    Continuous (fun p:ℝ×ℝ ↦ iteratedDeriv n (responseJet c ψ f 0 p.1) p.2) := by
  simp_rw [responseJet_zero_expr hψ hf hc]
  exact JetExpr.continuous_eval (combinedJet_continuous hψ hf hc) _
lemma responseJet_time_jets {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) :
    ∃ d:ℝ → ℝ → ℝ,Continuous (fun p:ℝ×ℝ ↦ d p.1 p.2) ∧
      (∃ C:ℝ,0≤C ∧ ∀ t x,|d t x|≤C) ∧
      ∀ t x,0<t → HasDerivAt (fun s ↦ iteratedDeriv n (responseJet c ψ f 0 s) x) (d t x) t := by
  let E := JetExpr.D JetExpr.responseσt (JetExpr.responseExpr n)
  let d := fun t x ↦ JetExpr.eval (fun j ↦ combinedJet c ψ f j t x) E
  refine ⟨d,JetExpr.continuous_eval (combinedJet_continuous hψ hf hc) E,?_,?_⟩
  · have hb (j:ℕ) : ∃ C:ℝ,0≤C ∧ ∀ p:ℝ×ℝ,|combinedJet c ψ f j p.1 p.2|≤C := by
      obtain ⟨C,hC,hb⟩ := combinedJet_bound hψ hf hc j
      exact ⟨C,hC,fun p ↦ hb p.1 p.2⟩
    obtain ⟨C,hC,hb⟩ := JetExpr.uniform_bound hb E
    exact ⟨C,hC,fun t x ↦ hb (t,x)⟩
  · intro t x ht
    simp_rw [responseJet_zero_expr hψ hf hc]
    apply JetExpr.hasDerivAt_eval
    intro j
    simpa only [JetExpr.eval_responseσt] using combinedJet_time hψ hf hc ht j x
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_TestEvolution
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma responseJet_zero (c:ℝ) (ψ f:ℝ → ℝ) (x:ℝ) : responseJet c ψ f 0 0 x=f x := by
  simp only [responseJet,iteratedDeriv_zero,heat_zero]
  exact mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

lemma baseJet_one_eq {ψ:ℝ → ℝ} (hψ:SmoothTerminal ψ) {c:ℝ} (hc:0 ≤ c) (t x:ℝ) :
    baseJet c ψ 1 t x=c*deriv (coleHopf c t ψ) x := by
  rcases hc.eq_or_lt with rfl | hc
  · have he : heat t (fun _ : ℝ ↦ (1:ℝ))=fun _ ↦ (1:ℝ) := by
      funext y
      simp [heat]
    simp only [baseJet,normalizedJet,zero_mul,Real.exp_zero,iteratedDeriv_one,he]
    simp
  · rw [coleHopf_deriv_eq_normalizedJet hψ.lipschitz hψ.smooth hψ.jets hc t]
    dsimp only [baseJet]
    rw [mul_inv_cancel_left₀ hc.ne']

lemma responseJet_time_lipschitz {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (n:ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (s t x : ℝ), (0 ≤ s) → (0 ≤ t) →
      |iteratedDeriv n (responseJet c ψ f 0 s) x-iteratedDeriv n (responseJet c ψ f 0 t) x|≤C*|s-t| := by
  obtain ⟨d,hdc,⟨C,hC,hb⟩,hd⟩ := responseJet_time_jets hψ hf hc n
  refine ⟨C,hC,?_⟩
  intro s t x hs ht
  exact nonneg_time_lipschitz hC
    ((responseJet_joint_jets hψ hf hc n).comp (continuous_id.prodMk continuous_const))
    (hdc.comp (continuous_id.prodMk continuous_const))
    (fun r hr ↦ hd r x hr) (fun r _ ↦ hb r x) hs ht

lemma responseJet_backward_pde {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (T:ℝ) {s t:ℝ} (ht:t∈Icc (0:ℝ) T) (hs:s∈Icc (0:ℝ) T) (x:ℝ) :
    responseJet c ψ f 0 (T-s) x-responseJet c ψ f 0 (T-t) x=
      -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (responseJet c ψ f 0 (T-r))) x+
        c*(deriv (coleHopf c (T-r) ψ) x*deriv (responseJet c ψ f 0 (T-r)) x)) := by
  let V := fun r ↦ responseJet c ψ f 0 (T-r)
  let A := fun r ↦ coleHopf c (T-r) ψ
  let g := fun r ↦ (1/2:ℝ)*deriv (deriv (V r)) x+c*(deriv (A r) x*deriv (V r) x)
  have hm : Continuous (fun r : ℝ ↦ (T-r,x)) :=
    (continuous_const.sub continuous_id).prodMk continuous_const
  have hcj (n:ℕ) : Continuous (fun r ↦ iteratedDeriv n (V r) x) := by
    have hh := (responseJet_joint_jets hψ hf hc n).comp hm
    change Continuous (fun r ↦ iteratedDeriv n (responseJet c ψ f 0 (T-r)) x)
    exact hh
  have hgc:Continuous g := by
    have h1:Continuous (fun r ↦ deriv (V r) x) := by simpa only [iteratedDeriv_one] using hcj 1
    have h2:Continuous (fun r ↦ deriv (deriv (V r)) x) := by
      simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hcj 2
    exact (continuous_const.mul h2).add (continuous_const.mul ((hψ.backward_gradient_continuous hc T x).mul h1))
  have hd (r:ℝ) (hr:r∈Ioo (0:ℝ) T) : HasDerivAt (fun r ↦ V r x) (-g r) r := by
    have hh := (responseJet_heat_drift hψ hf hc (sub_pos.mpr hr.2) 0 x).comp r
      ((hasDerivAt_const r T).sub (hasDerivAt_id r))
    rw [baseJet_one_eq hψ hc] at hh
    convert! hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [V,A,g]
    ring
  have he := integral_from_deriv_on_strip (by simpa only [iteratedDeriv_zero] using (hcj 0).continuousOn)
    hgc.neg.continuousOn hd hs ht
  change _=∫ r in t..s,-(g r) at he
  rw [intervalIntegral.integral_neg] at he
  exact he

lemma SmoothTerminal.linear_constant {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f)
    {c:ℝ} (hc:0 ≤ c) (T:ℝ) :
    LinearEvolution T (fun _ ↦ c) (fun t ↦ coleHopf c (T-t) ψ) (fun t ↦ responseJet c ψ f 0 (T-t)) := by
  refine ⟨fun t _ ↦ responseJet_boundedSmooth hψ hf hc 0 _,?_,?_,?_,?_⟩
  · intro n x
    have hm : Continuous (fun r : ℝ ↦ (T-r,x)) :=
      (continuous_const.sub continuous_id).prodMk continuous_const
    exact ((responseJet_joint_jets hψ hf hc n).comp hm).continuousOn
  · intro n
    obtain ⟨C,hC,hb⟩ := responseJet_uniform_jets hψ hf hc n 0
    exact ⟨C,hC,fun t _ x ↦ hb (T-t) x⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := responseJet_time_lipschitz hψ hf hc n
    refine ⟨C,hC,?_⟩
    intro s hs t ht x
    have hh := hb (T-s) (T-t) x (sub_nonneg.mpr hs.2) (sub_nonneg.mpr ht.2)
    simpa only [sub_sub_sub_cancel_left,abs_sub_comm] using hh
  · intro t ht s hs x
    exact responseJet_backward_pde hψ hf hc T ht hs x
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_TestPatch
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma patchTime_testjet {a t x:ℝ} (V W:ℝ → ℝ → ℝ) (n:ℕ) :
    iteratedDeriv n (patchTime a V W t) x=
      patchTime a (fun t ↦ iteratedDeriv n (V t) x) (fun t ↦ iteratedDeriv n (W t) x) t := by
  by_cases ht:t≤a <;> simp [patchTime,ht]

lemma LinearEvolution.rhs_integrable {T:ℝ} (hT:0≤T) {γ:ℝ → ℝ} {A V:ℝ → ℝ → ℝ}
    (h:LinearEvolution T γ A V) (hA:SmoothEvolution T γ A)
    (hg:IntervalIntegrable γ volume 0 T) (x:ℝ) :
    IntervalIntegrable (fun r ↦ -((1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))) volume 0 T := by
  have h1:ContinuousOn (fun r ↦ deriv (V r) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_one] using h.continuous_jet 1 x
  have h2:ContinuousOn (fun r ↦ deriv (deriv (V r)) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using h.continuous_jet 2 x
  have ha:ContinuousOn (fun r ↦ deriv (A r) x) (uIcc (0:ℝ) T) := by
    simpa only [uIcc_of_le hT,iteratedDeriv_zero] using hA.continuous_jet 0 x
  exact ((h2.intervalIntegrable.const_mul _).add (hg.mul_continuousOn (ha.mul h1))).neg

lemma LinearEvolution.patch_pde {a b:ℝ} (ha:0≤a) (hb:0≤b)
    {γ η:ℝ → ℝ} {A B V W:ℝ → ℝ → ℝ}
    (hV:LinearEvolution a γ A V) (hW:LinearEvolution b η B W)
    (hA:SmoothEvolution a γ A) (hB:SmoothEvolution b η B)
    (hγ:IntervalIntegrable γ volume 0 a) (hη:IntervalIntegrable η volume 0 b)
    (hjoin:V a=W 0) {s t:ℝ} (hs:s∈Icc (0:ℝ) (a+b)) (ht:t∈Icc (0:ℝ) (a+b)) (x:ℝ) :
    patchTime a V W s x-patchTime a V W t x=
      -(∫ r in t..s,(1/2:ℝ)*deriv (deriv (patchTime a V W r)) x+
        patchTime a γ η r*(deriv (patchTime a A B r) x*deriv (patchTime a V W r) x)) := by
  let p := fun r ↦ -((1/2:ℝ)*deriv (deriv (V r)) x+γ r*(deriv (A r) x*deriv (V r) x))
  let q := fun r ↦ -((1/2:ℝ)*deriv (deriv (W r)) x+η r*(deriv (B r) x*deriv (W r) x))
  have hp := hV.rhs_integrable ha hA hγ x
  have hq := hW.rhs_integrable hb hB hη x
  have hv:∀ t∈Icc (0:ℝ) a,V t x-V 0 x=∫ r in (0:ℝ)..t,p r := by
    intro t ht
    simpa only [p,intervalIntegral.integral_neg] using hV.pde 0 ⟨le_rfl,ha⟩ t ht x
  have hw:∀ t∈Icc (0:ℝ) b,W t x-W 0 x=∫ r in (0:ℝ)..t,q r := by
    intro t ht
    simpa only [q,intervalIntegral.integral_neg] using hW.pde 0 ⟨le_rfl,hb⟩ t ht x
  have he := primitive_to_integral (add_nonneg ha hb) (patchTime_intervalIntegrable ha hb hp hq)
    (patchTime_primitive ha hb hp hq hv hw (congrFun hjoin x)) hs ht
  rw [←patchTime_apply V W,←patchTime_apply V W] at he
  rw [he,←intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro r _
  by_cases hr:r≤a <;> simp [patchTime,hr]

lemma LinearEvolution.patch {a b:ℝ} (ha:0≤a) (hb:0≤b)
    {γ η:ℝ → ℝ} {A B V W:ℝ → ℝ → ℝ}
    (hV:LinearEvolution a γ A V) (hW:LinearEvolution b η B W)
    (hA:SmoothEvolution a γ A) (hB:SmoothEvolution b η B)
    (hγ:IntervalIntegrable γ volume 0 a) (hη:IntervalIntegrable η volume 0 b)
    (hjoin:V a=W 0) :
    LinearEvolution (a+b) (patchTime a γ η) (patchTime a A B) (patchTime a V W) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t ht
    by_cases hta:t≤a
    · rw [patchTime_left V W hta];exact hV.slices t ⟨ht.1,hta⟩
    · rw [patchTime_right V W (lt_of_not_ge hta)];exact hW.slices (t-a) ⟨by linarith,by linarith [ht.2]⟩
  · intro n x
    simp_rw [patchTime_testjet]
    apply patchTime_continuous (hV.continuous_jet n x) (hW.continuous_jet n x)
    rw [hjoin]
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.bound n
    obtain ⟨D,hD,hw⟩ := hW.bound n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro t ht x
    rw [patchTime_testjet]
    exact patchTime_bound hC hD (fun t ht ↦ hv t ht x) (fun t ht ↦ hw t ht x) t ht
  · intro n
    obtain ⟨C,hC,hv⟩ := hV.temporal n
    obtain ⟨D,hD,hw⟩ := hW.temporal n
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    intro s hs t ht x
    rw [patchTime_testjet,patchTime_testjet]
    apply patchTime_lipschitz ha hb hC hD (fun s hs t ht ↦ hv s hs t ht x)
      (fun s hs t ht ↦ hw s hs t ht x) _ s hs t ht
    rw [hjoin]
  · intro t ht s hs x
    exact hV.patch_pde ha hb hW hA hB hγ hη hjoin hs ht x

lemma SmoothTerminal.linear_profile {ψ f:ℝ → ℝ} (hψ:SmoothTerminal ψ) (hf:BoundedSmooth f) (l:HeatProfile) :
    LinearEvolution (profileTime l) (profileCoeff l) (profileValue ψ l) (profileResponse ψ f l) := by
  induction l with
  | nil =>
    change LinearEvolution 0 (fun _ ↦ 0) (fun _ ↦ ψ) (fun _ ↦ f)
    refine ⟨fun t _ ↦ hf,fun _ _ ↦ continuousOn_const,?_,?_,?_⟩
    · intro n
      obtain ⟨C,hC,hb⟩ := hf.bound n
      exact ⟨C,hC,fun _ _ ↦ hb⟩
    · intro n
      exact ⟨0,le_rfl,by intros;simp⟩
    · intro t ht s hs x
      have ht0:t=0 := le_antisymm ht.2 ht.1
      have hs0:s=0 := le_antisymm hs.2 hs.1
      subst t;subst s;simp
  | cons p l ih =>
    have hA := hψ.profile_evolution l
    have hψ' := hA.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hf' := ih.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    apply (hψ'.linear_constant hf' p.2.coe_nonneg (p.1:ℝ)).patch p.1.coe_nonneg (profileTime_nonneg l)
      ih (hψ'.constant_evolution p.2.coe_nonneg (p.1:ℝ)) hA intervalIntegrable_const (profileCoeff_integrable l)
    funext x
    simp only [sub_self,responseJet_zero]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_DensityPairing
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SKValue
lemma exp_coleHopf {A:ℝ → ℝ} (hA:SmoothTerminal A) {c:ℝ} (hc:0 < c) (t x:ℝ) :
    Real.exp (c*coleHopf c t A x)=heat t (fun y ↦ Real.exp (c*A y)) x := by
  simp only [coleHopf,ite_eq_right hc.ne']
  rw [mul_div_cancel₀ _ hc.ne']
  exact Real.exp_log (lipschitz_exp_integral_pos hA.lipschitz hc.le x (Real.sqrt t))

lemma ForwardDensityData.response_pairing (D:ForwardDensityData) {A f:ℝ → ℝ}
    (hA:SmoothTerminal A) (hf:BoundedSmooth f) {c t:ℝ} (hc:0 < c) (ht:0≤t) :
    (∫ x,(Real.exp (c*coleHopf c t A x)*D.weight x)*responseJet c A f 0 t x)=
      ∫ x,(Real.exp (c*A x)*(D.evolve t ht).weight x)*f x := by
  have he (x:ℝ):(Real.exp (c*coleHopf c t A x)*D.weight x)*responseJet c A f 0 t x=
      D.weight x*heat t (fun y ↦ Real.exp (c*A y)*f y) x := by
    rw [exp_coleHopf hA hc]
    simp only [responseJet,iteratedDeriv_zero]
    have hn:heat t (fun y ↦ Real.exp (c*A y)) x≠0 :=
      (lipschitz_exp_integral_pos hA.lipschitz hc.le x (Real.sqrt t)).ne'
    field_simp [hn]
  simp_rw [he]
  have hh:=D.heat_duality (show ExpGrowth (fun x ↦ Real.exp (c*A x)*f x) from by
      simpa only [iteratedDeriv_zero] using weighted_growth hA hf hc.le 0)
    (hA.smooth.continuous.measurable.const_mul c |>.exp |>.mul hf.smooth.continuous.measurable) t
  rw [hh]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [D.evolve_weight]
  ring

lemma ForwardDensityData.jump_density (D:ForwardDensityData) {A:ℝ → ℝ}
    (hA:SmoothTerminal A) (heven:∀ x,A (-x)=A x) {c d:ℝ} (hcd:c≤d) (x:ℝ) :
    Real.exp (d*A x)*(D.jump hA heven (d-c) (sub_nonneg.mpr hcd)).weight x=
      Real.exp (c*A x)*D.weight x := by
  rw [D.jump_weight]
  have he:d*A x+(-(d-c)*A x)=c*A x := by ring
  calc
    _ = (Real.exp (d*A x)*Real.exp (-(d-c)*A x))*D.weight x := by ring
    _ = _ := by rw [←Real.exp_add,he]

lemma gaussian_heat_zero {f:ℝ → ℝ} (hf:Measurable f) {t:ℝ} (ht:0<t) :
    heat t f 0=∫ x,gaussianPDFReal 0 t.toNNReal x*f x := by
  have hm:MeasurePreserving (fun z:ℝ ↦ 0+Real.sqrt t*z) standardGaussian (gaussianReal 0 t.toNNReal) :=
    (shiftedGaussian_hasLaw ht.le 0).measurePreserving (by fun_prop)
  have he:=(shiftedGaussian_hasLaw ht.le 0).integral_comp hf.aestronglyMeasurable
  simp only [Function.comp_def] at he
  change (∫ z,f (0+Real.sqrt t*z) ∂standardGaussian)=_
  rw [he,gaussianReal_of_var_ne_zero _ (Real.toNNReal_pos.mpr ht).ne',
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ _)
      (Eventually.of_forall (fun x ↦ by simp [gaussianPDF]))]
  simp only [toReal_gaussianPDF,smul_eq_mul]

lemma first_response_density {A f:ℝ → ℝ} (hA:SmoothTerminal A) (hf:BoundedSmooth f)
    {c t:ℝ} (hc:0 < c) (ht:0<t) :
    responseJet c A f 0 t 0=
      Real.exp (-(c*coleHopf c t A 0))*(∫ x,(Real.exp (c*A x)*(ForwardDensityData.gaussian t ht).weight x)*f x) := by
  simp only [responseJet,iteratedDeriv_zero]
  have hm:Measurable (fun y ↦ Real.exp (c*A y)*f y) :=
    ((hA.smooth.continuous.measurable.const_mul c).exp.mul hf.smooth.continuous.measurable)
  rw [gaussian_heat_zero hm ht,←exp_coleHopf hA hc,Real.exp_neg]
  rw [div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ForwardDensityData.gaussian_weight]
  ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GeneralProfileShape
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
lemma BackwardShape.profile {A:ℝ → ℝ} {M c : ℝ} (hA:SmoothTerminal A) (hB:BackwardShape M A)
    (hM : 0<M) (hc : 0 < c) (hcM : c≤M)
    {l : HeatProfile} (hl : l.Pairwise (fun p q ↦ p.2≤q.2))
    (hlow : ∀ p∈l,c≤(p.2:ℝ)) (hupp : ∀ p∈l,(p.2:ℝ)≤M) (t : ℝ) :
    BackwardShape c (profileValue A l t) := by
  induction l generalizing c t with
  | nil => exact hB.lower hM hc.le hcM
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp hl
    have hcp : c≤(p.2:ℝ) := hlow p (by simp)
    have hp0 : 0<(p.2:ℝ) := hc.trans_le hcp
    have hpM : (p.2:ℝ)≤M := hupp p (by simp)
    have hlo : ∀ q∈l,c≤(q.2:ℝ) := fun q hq ↦ hlow q (by simp [hq])
    have hup : ∀ q∈l,(q.2:ℝ)≤M := fun q hq ↦ hupp q (by simp [hq])
    change BackwardShape c (patchTime (p.1:ℝ) _ _ t)
    by_cases ht : t≤(p.1:ℝ)
    · rw [patchTime_left _ _ ht]
      have hs := ih hp0 hpM hl (fun q hq ↦ by exact_mod_cast hp q hq) hup 0
      have hψ := hA.profile_evolution l
      have hsm := hψ.slices 0 ⟨le_rfl,profileTime_nonneg l⟩
      exact (hs.evolve hsm hp0 (sub_nonneg.mpr ht)).lower hp0 hc.le hcp
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih hc hcM hl hlo hup _

end SKValue

end

section

open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SKValue
lemma profileValue_zero_cons (A:ℝ → ℝ) (p:ℝ≥0 × ℝ≥0) (l:HeatProfile) :
    profileValue A (p::l) 0=coleHopf p.2 p.1 (profileValue A l 0) := by
  simp only [profileValue,patchTime_left _ _ p.1.coe_nonneg,sub_zero]
lemma profileResponse_zero_cons (A f:ℝ → ℝ) (p:ℝ≥0 × ℝ≥0) (l:HeatProfile) :
    profileResponse A f (p::l) 0=responseJet p.2 (profileValue A l 0) (profileResponse A f l 0) 0 p.1 := by
  simp only [profileResponse,patchTime_left _ _ p.1.coe_nonneg,sub_zero]

lemma ForwardShape.profile {A:ℝ → ℝ} {C d:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape C A) (hd:0<d) (hdC:d≤C) {l:HeatProfile}
    (hl:l.Pairwise (fun p q ↦ p.2≤q.2)) (hlo:∀ p∈l,d≤(p.2:ℝ))
    (hup:∀ p∈l,(p.2:ℝ)≤C) {D:ForwardDensityData}
    (hF:ForwardShape d (profileValue A l 0) D) :
    ∃ E:ForwardDensityData,ForwardShape C A E ∧ ∀ f:ℝ → ℝ,BoundedSmooth f →
      (∫ x,(Real.exp (d*profileValue A l 0 x)*D.weight x)*profileResponse A f l 0 x)=
        ∫ x,(Real.exp (C*A x)*E.weight x)*f x := by
  induction l generalizing d D with
  | nil =>
    let E:=D.jump hA hB.even (C-d) (sub_nonneg.mpr hdC)
    refine ⟨E,hF.jump hA (hB.lower (hd.trans_le hdC) hd.le hdC) hd hdC,?_⟩
    intro f hf
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ForwardDensityData.jump_density _ _ _ hdC]
    rfl
  | cons p l ih =>
    have hdp:d≤(p.2:ℝ) := hlo p (by simp)
    have hp:0<(p.2:ℝ) := hd.trans_le hdp
    have hpC:(p.2:ℝ)≤C := hup p (by simp)
    obtain ⟨hpl,hll⟩:=List.pairwise_cons.mp hl
    have hpl':∀ q∈l,(p.2:ℝ)≤(q.2:ℝ) := fun q hq ↦ by exact_mod_cast hpl q hq
    have hup':∀ q∈l,(q.2:ℝ)≤C := fun q hq ↦ hup q (by simp [hq])
    let B:=profileValue A l 0
    have hBs:SmoothTerminal B := (hA.profile_evolution l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    have hBb:BackwardShape p.2 B := hB.profile hA (hd.trans_le hdC) hp hpC hll hpl' hup' 0
    let V:=profileValue A (p::l) 0
    have hVs:SmoothTerminal V := (hA.profile_evolution (p::l)).slices 0 ⟨le_rfl,profileTime_nonneg _⟩
    have hVb:BackwardShape d V := hB.profile hA (hd.trans_le hdC) hd hdC hl hlo hup 0
    let D':=D.jump hVs hVb.even ((p.2:ℝ)-d) (sub_nonneg.mpr hdp)
    have hF':ForwardShape p.2 V D' := hF.jump hVs hVb hd hdp
    have hstart:ForwardShape p.2 (coleHopf p.2 p.1 B) D' := by
      simpa only [V,profileValue_zero_cons] using hF'
    have hend:ForwardShape p.2 B (D'.evolve p.1 p.1.coe_nonneg) :=
      hstart.evolve hBs hBb hp p.1.coe_nonneg
    obtain ⟨E,hE,hpair⟩:=ih hp hpC hll hpl' hup' hend
    refine ⟨E,hE,?_⟩
    intro f hf
    have htest:BoundedSmooth (profileResponse A f l 0) :=
      (hA.linear_profile hf l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩
    calc
      _ = ∫ x,(Real.exp ((p.2:ℝ)*V x)*D'.weight x)*profileResponse A f (p::l) 0 x := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [ForwardDensityData.jump_density _ _ _ hdp]
      _ = ∫ x,(Real.exp ((p.2:ℝ)*B x)*(D'.evolve p.1 p.1.coe_nonneg).weight x)*profileResponse A f l 0 x := by
        rw [profileResponse_zero_cons]
        change (∫ x,(Real.exp ((p.2:ℝ)*profileValue A (p::l) 0 x)*D'.weight x)*_) = _
        rw [profileValue_zero_cons]
        exact D'.response_pairing hBs htest hp p.1.coe_nonneg
      _ = _ := hpair f hf

lemma BackwardShape.profile_density {A:ℝ → ℝ} {C:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape C A) {p:ℝ≥0 × ℝ≥0} {l:HeatProfile}
    (hp:0<(p.2:ℝ)) (ht:0<(p.1:ℝ))
    (hl:(p::l).Pairwise (fun p q ↦ p.2≤q.2)) (hup:∀ q∈p::l,(q.2:ℝ)≤C) :
    ∃ E:ForwardDensityData,ForwardShape C A E ∧ ∀ f:ℝ → ℝ,BoundedSmooth f →
      profileResponse A f (p::l) 0 0=Real.exp (-((p.2:ℝ)*profileValue A (p::l) 0 0))*
        (∫ x,(Real.exp (C*A x)*E.weight x)*f x) := by
  obtain ⟨hpl,hll⟩:=List.pairwise_cons.mp hl
  have hpC:(p.2:ℝ)≤C := hup p (by simp)
  have hpl':∀ q∈l,(p.2:ℝ)≤(q.2:ℝ) := fun q hq ↦ by exact_mod_cast hpl q hq
  have hup':∀ q∈l,(q.2:ℝ)≤C := fun q hq ↦ hup q (by simp [hq])
  have hBs:SmoothTerminal (profileValue A l 0) := (hA.profile_evolution l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩
  have hBb:BackwardShape p.2 (profileValue A l 0) := hB.profile hA (hp.trans_le hpC) hp hpC hll hpl' hup' 0
  have hF:=hBb.gaussian_forwardShape hBs ht
  obtain ⟨E,hE,hpair⟩:=hF.profile hA hB hp hpC hll hpl' hup'
  refine ⟨E,hE,?_⟩
  intro f hf
  rw [profileResponse_zero_cons,profileValue_zero_cons]
  have htest:BoundedSmooth (profileResponse A f l 0) := (hA.linear_profile hf l).slices 0 ⟨le_rfl,profileTime_nonneg l⟩
  rw [first_response_density hBs htest hp ht,hpair f hf]
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_GridProfile
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

lemma gridProfile_time (d : ℝ≥0) (f : ℕ → ℝ≥0) (j n : ℕ) :
    profileTime (gridProfile d f j n)=(n : ℝ)*d := by
  induction n generalizing j with
  | zero => simp only [gridProfile,profileTime,Nat.cast_zero,zero_mul]
  | succ n ih => simp only [gridProfile,profileTime,ih,Nat.cast_add,Nat.cast_one]; ring

lemma gridProfile_mem {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ} {p : ℝ≥0 × ℝ≥0}
    (hp : p∈gridProfile d f j n) : ∃ i, j ≤ i ∧ i<j+n ∧ p=(d,f i) := by
  induction n generalizing j with
  | zero => simp only [gridProfile,List.not_mem_nil] at hp
  | succ n ih =>
    simp only [gridProfile,List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact ⟨j,le_rfl,by omega,rfl⟩
    · obtain ⟨i,hi,hij,rfl⟩ := ih hp
      exact ⟨i,by omega,by omega,rfl⟩

lemma gridProfile_pairwise {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ}
    (hm : ∀ i k, j ≤ i → i<k → k<j+n → f i ≤ f k) :
    (gridProfile d f j n).Pairwise (fun p q ↦ p.2 ≤ q.2) := by
  induction n generalizing j with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [gridProfile,List.pairwise_cons]
    constructor
    · intro q hq
      obtain ⟨i,hi,hij,rfl⟩ := gridProfile_mem hq
      exact hm j i le_rfl (by omega) (by omega)
    · exact ih (fun i k hi hik hk ↦ hm i k (by omega) hik (by omega))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_HeatKernelBound
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

lemma BoundedSmooth.iteratedDeriv {f : ℝ → ℝ} (hf : BoundedSmooth f) (n : ℕ) :
    BoundedSmooth (iteratedDeriv n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Coercivity_FiniteCoercivity
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma BoundedSmooth.pow {f:ℝ → ℝ} (hf:BoundedSmooth f) (n:ℕ) :
    BoundedSmooth (fun x ↦ f x^n) := by
  induction n with
  | zero => simpa only [pow_zero] using BoundedSmooth.const (1:ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul hf
lemma BoundedSmooth.sub {f g:ℝ → ℝ} (hf:BoundedSmooth f) (hg:BoundedSmooth g) :
    BoundedSmooth (fun x ↦ f x-g x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))
lemma SmoothTerminal.spatialJet_boundedSmooth {A:ℝ → ℝ} (hA:SmoothTerminal A)
    (c:ℝ) (n:ℕ) : BoundedSmooth (spatialJet c A n) :=
  (hA.jets.iteratedDeriv n).const_mul c

lemma BackwardShape.profile_coercivity {A:ℝ → ℝ} {C:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape C A) {p:ℝ≥0 × ℝ≥0} {l:HeatProfile}
    (hp:0<(p.2:ℝ)) (ht:0<(p.1:ℝ))
    (hl:(p::l).Pairwise (fun p q ↦ p.2≤q.2)) (hup:∀ q∈p::l,(q.2:ℝ)≤C) :
    (1/1000:ℝ)*profileResponse A (fun x ↦ (spatialJet C A 1 x)^4) (p::l) 0 0≤
      profileResponse A (fun x ↦ (spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) (p::l) 0 0 := by
  obtain ⟨E,hE,hpair⟩:=hB.profile_density hA hp ht hl hup
  have hC:0<C := hp.trans_le (hup p (by simp))
  have hv:=hA.spatialJet_boundedSmooth C 1
  have hw:=hA.spatialJet_boundedSmooth C 2
  have hz:=hA.spatialJet_boundedSmooth C 3
  have htest:BoundedSmooth (fun x ↦ (spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) :=
    ((hz.pow 2).sub ((hv.const_mul 12).mul (hw.pow 2))).add ((hv.pow 4).const_mul 6)
  rw [hpair _ (hv.pow 4),hpair _ htest]
  have hcert:=hB.integrated_certificate hA hC E
    (fun x ↦ (one_div_pos.mpr E.variance_pos).le.trans (hE.slope x)) hE.concave hE.coupled
  have hcert':(1/1000:ℝ)*(∫ x,(Real.exp (C*A x)*E.weight x)*(spatialJet C A 1 x)^4)≤
      ∫ x,(Real.exp (C*A x)*E.weight x)*((spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) := by
    simpa only [mul_comm] using hcert
  have hh:=mul_le_mul_of_nonneg_left hcert'
    (Real.exp_pos (-((p.2:ℝ)*profileValue A (p::l) 0 0))).le
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_ProfileSplit
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma profileTime_append (l r:HeatProfile) : profileTime (l++r)=profileTime l+profileTime r := by
  induction l with
  | nil => simp [profileTime]
  | cons p l ih => simp only [List.cons_append,profileTime,ih,add_assoc]
lemma profileValue_append_zero (A:ℝ → ℝ) (l r:HeatProfile) :
    profileValue A (l++r) 0=profileValue (profileValue A r 0) l 0 := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,profileValue_zero_cons,ih]
lemma profileValue_append_before (A:ℝ → ℝ) (l r:HeatProfile) {t:ℝ}
    (ht:t∈Icc (0:ℝ) (profileTime l)) :
    profileValue A (l++r) t=profileValue (profileValue A r 0) l t := by
  induction l generalizing t with
  | nil => have ht0:t=0 := le_antisymm ht.2 ht.1; subst t; rfl
  | cons p l ih =>
    change patchTime (p.1:ℝ) _ _ t=patchTime (p.1:ℝ) _ _ t
    by_cases hp:t≤(p.1:ℝ)
    · rw [patchTime_left _ _ hp,patchTime_left _ _ hp]
      congr 1
      exact profileValue_append_zero A l r
    · rw [patchTime_right _ _ (lt_of_not_ge hp),patchTime_right _ _ (lt_of_not_ge hp)]
      apply ih
      constructor
      · exact (sub_pos.mpr (lt_of_not_ge hp)).le
      · have htu:t≤(p.1:ℝ)+profileTime l := ht.2
        linarith
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma splitLength_mul (a b:ℝ) (hab:a≤b) (n:ℕ) :
    ((n+1:ℕ):ℝ)*(splitLength a b hab n)=b-a := by
  change ((n+1:ℕ):ℝ)*((b-a)/(n+1:ℝ))=b-a
  rw [Nat.cast_add,Nat.cast_one]
  field_simp
lemma OrderParameter.splitSegment_time (γ:OrderParameter) (a b:ℝ) (hab:a≤b) (n:ℕ) :
    profileTime (γ.splitSegment a b hab n)=b-a := by
  rw [OrderParameter.splitSegment,gridProfile_time,splitLength_mul]
lemma split_sample_mem {a b:ℝ} (ha:0≤a) (hab:a<b) (hb:b≤1) {n i:ℕ} (hi:i<n+1) :
    a+(i:ℝ)*(splitLength a b hab.le n)∈Ico (0:ℝ) 1 := by
  have hd:0<(splitLength a b hab.le n:ℝ) := div_pos (sub_pos.mpr hab) (by positivity)
  have hi':(i:ℝ)<(n+1:ℕ) := by exact_mod_cast hi
  have ht:=mul_lt_mul_of_pos_right hi' hd
  rw [splitLength_mul] at ht
  exact ⟨add_nonneg ha (mul_nonneg (Nat.cast_nonneg _) hd.le),by linarith⟩
lemma OrderParameter.splitSegment_mono (γ:OrderParameter) {a b:ℝ}
    (ha:0≤a) (hab:a<b) (hb:b≤1) (n:ℕ) :
    (γ.splitSegment a b hab.le n).Pairwise (fun p q ↦ p.2≤q.2) := by
  apply gridProfile_pairwise
  intro i k _ hik hk
  apply add_le_add _ le_rfl
  apply Real.toNNReal_mono
  exact γ.monotone (split_sample_mem ha hab hb (by omega))
    (split_sample_mem ha hab hb (by omega))
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hik.le) (splitLength a b hab.le n).coe_nonneg))
lemma OrderParameter.splitGrid_time (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    profileTime (γ.splitGrid t n)=1 := by
  rw [OrderParameter.splitGrid,profileTime_append,γ.splitSegment_time,γ.splitSegment_time]
  ring
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_SplitConvergence
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue
lemma profileHeight_nonneg (l:HeatProfile) : 0 ≤ profileHeight l := by
  cases l with
  | nil => exact le_rfl
  | cons p l => exact p.2.coe_nonneg.trans (le_max_left _ _)
lemma profileHeight_mem {l:HeatProfile} {p:ℝ≥0 × ℝ≥0} (hp:p∈l) : (p.2:ℝ) ≤ profileHeight l := by
  induction l with
  | nil => simp at hp
  | cons q l ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact le_max_left _ _
    · exact (ih hp).trans (le_max_right _ _)
lemma splitSmoothParameter_pos (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    0 < splitSmoothParameter γ t n := add_pos_of_pos_of_nonneg (by positivity) (profileHeight_nonneg _)
lemma splitSmooth_evolution (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    SmoothEvolution 1 (profileCoeff (γ.splitGrid t n)) (splitSmooth γ t n) := by
  unfold splitSmooth
  convert (logCoshTerminal_smoothTerminal (splitSmoothParameter_pos γ t n)).profile_evolution (γ.splitGrid t n) using 1
  all_goals try with_reducible_and_instances rfl
  exact (γ.splitGrid_time t n).symm
end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_SplitShape
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma splitTerminal_eq (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    splitTerminal γ t n=splitSmooth γ t n t := by
  unfold splitSmooth OrderParameter.splitGrid
  rw [profileValue_append_before _ _ _ ⟨t.property.1.le,by rw [γ.splitSegment_time,sub_zero]⟩]
  have he:profileTime (γ.splitSegment 0 t t.property.1.le n)=(t:ℝ) := by rw [γ.splitSegment_time,sub_zero]
  exact (by simpa only [he,splitTerminal] using
    (profileValue_terminal (splitTerminal γ t n) (γ.splitSegment 0 t t.property.1.le n)).symm)
lemma splitTerminal_smooth (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    SmoothTerminal (splitTerminal γ t n) := by
  rw [splitTerminal_eq]
  exact (splitSmooth_evolution γ t n).slices t ⟨t.property.1.le,t.property.2.le⟩
lemma OrderParameter.splitSegment_coeff (γ:OrderParameter) {a b:ℝ}
    (ha:0 ≤ a) (hab:a<b) (hb:b ≤ 1) (n:ℕ) {p:ℝ≥0 × ℝ≥0}
    (hp:p∈γ.splitSegment a b hab.le n) :
    ∃ r∈Ico (0:ℝ) 1,a ≤ r ∧ r<b ∧ (p.2:ℝ)=γ.coeff r+(gridDelta n:ℝ) := by
  obtain ⟨i,_,hi,rfl⟩:=gridProfile_mem hp
  have hr:=split_sample_mem ha hab hb (show i<n+1 by omega)
  have hd:0<(splitLength a b hab.le n:ℝ) := div_pos (sub_pos.mpr hab) (by positivity)
  have hi':(i:ℝ)<(n+1:ℕ) := by exact_mod_cast (show i<n+1 by omega)
  have hit:=mul_lt_mul_of_pos_right hi' hd
  rw [splitLength_mul] at hit
  refine ⟨_,hr,le_add_of_nonneg_right (by positivity),by linarith,?_⟩
  simp only [NNReal.coe_add,Real.coe_toNNReal _ (γ.nonneg _ hr)]
lemma splitCut_le_parameter (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    γ.coeff t+(gridDelta n:ℝ) ≤ splitSmoothParameter γ t n := by
  let p:ℝ≥0 × ℝ≥0 := (splitLength t 1 t.property.2.le n,(γ.coeff t).toNNReal+gridDelta n)
  have hp:p∈γ.splitGrid t n := by
    apply List.mem_append_right
    change p∈gridProfile _ _ 0 (n+1)
    simp only [gridProfile,List.mem_cons,zero_add,zero_mul,Nat.cast_zero,add_zero]
    exact Or.inl rfl
  have hh:=profileHeight_mem hp
  have he:(p.2:ℝ)=γ.coeff t+(gridDelta n:ℝ) := by
    simp only [p,NNReal.coe_add,Real.coe_toNNReal _ (γ.nonneg _ ⟨t.property.1.le,t.property.2⟩)]
  rw [he] at hh
  exact hh.trans (le_add_of_nonneg_left (by positivity : (0:ℝ) ≤ n+1))
lemma splitTerminal_shape (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    BackwardShape (γ.coeff t+(gridDelta n:ℝ)) (splitTerminal γ t n) := by
  have hM:=splitSmoothParameter_pos γ t n
  have hC:0<γ.coeff t+(gridDelta n:ℝ) := add_pos_of_nonneg_of_pos
    (γ.nonneg _ ⟨t.property.1.le,t.property.2⟩) (by change 0<1/(n+1:ℝ);positivity)
  apply (logCoshTerminal_backwardShape hM hM le_rfl).profile
    (logCoshTerminal_smoothTerminal hM) hM hC (splitCut_le_parameter γ t n)
    (γ.splitSegment_mono t.property.1.le t.property.2 le_rfl n)
  · intro p hp
    obtain ⟨r,hr,htr,_,he⟩:=γ.splitSegment_coeff t.property.1.le t.property.2 le_rfl n hp
    rw [he]
    exact add_le_add (γ.monotone ⟨t.property.1.le,t.property.2⟩ hr htr) le_rfl
  · intro p hp
    exact (profileHeight_mem (List.mem_append_right _ hp)).trans
      (le_add_of_nonneg_left (by positivity : (0:ℝ) ≤ n+1))
lemma split_profile_coercivity_oai (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    let A:=splitTerminal γ t n
    let C:=γ.coeff t+(gridDelta n:ℝ)
    let l:=γ.splitSegment 0 t t.property.1.le n
    (1/1000:ℝ)*profileResponse A (fun x ↦ (spatialJet C A 1 x)^4) l 0 0 ≤
      profileResponse A (fun x ↦ (spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) l 0 0 := by
  dsimp only
  have hleft:∀ p∈γ.splitSegment 0 t t.property.1.le n,(p.2:ℝ) ≤ γ.coeff t+(gridDelta n:ℝ) := by
    intro p hp
    obtain ⟨r,hr,_,hrt,he⟩:=γ.splitSegment_coeff le_rfl t.property.1 t.property.2.le n hp
    rw [he]
    exact add_le_add (γ.monotone hr ⟨t.property.1.le,t.property.2⟩ hrt.le) le_rfl
  simp only [OrderParameter.splitSegment,gridProfile,Nat.cast_zero,zero_mul,zero_add]
  apply (splitTerminal_shape γ t n).profile_coercivity (splitTerminal_smooth γ t n)
    (p:=(splitLength 0 t t.property.1.le n,(γ.coeff 0).toNNReal+gridDelta n))
  · change 0<((γ.coeff 0).toNNReal:ℝ)+(gridDelta n:ℝ)
    exact add_pos_of_nonneg_of_pos (by positivity) (by change 0<1/(n+1:ℝ);positivity)
  · change 0<((t:ℝ)-0)/(n+1:ℝ)
    exact div_pos (by simpa only [sub_zero] using t.property.1) (by positivity)
  · simpa only [OrderParameter.splitSegment,gridProfile,Nat.cast_zero,zero_mul,zero_add] using
      γ.splitSegment_mono le_rfl t.property.1 t.property.2.le n
  · simpa only [OrderParameter.splitSegment,gridProfile,Nat.cast_zero,zero_mul,zero_add] using hleft
end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.split_profile_coercivity_oai := @OAI.SKValue.split_profile_coercivity_oai
