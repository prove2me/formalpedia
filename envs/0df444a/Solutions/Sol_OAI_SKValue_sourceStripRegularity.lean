-- Prove2me | solution 1 for OAI.SKValue.sourceStripRegularity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:06:33.275275+00:00
-- url     : https://prove2.me/submissions/77822cd9-8c30-4e5a-9070-5f910cd00e67

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000
import Theorems.Thm_OAI_SKValue_phi_evolution
import Theorems.Thm_OAI_SKValue_smoothApprox_tendsto

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

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolveStrips
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

lemma SmoothEvolution.jet_joint {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (n : ℕ) :
    ∃ L : ℝ, 0≤L ∧ ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ x y,
      |iteratedDeriv n (deriv (V s)) y-iteratedDeriv n (deriv (V t)) x|≤L*(|s-t|+|y-x|) := by
  obtain ⟨A,hA,ha⟩ := h.temporal n
  obtain ⟨B,hB,hb⟩ := h.bound (n+1)
  refine ⟨A+B,add_nonneg hA hB,?_⟩
  intro s hs t ht x y
  have hd := (h.slices t ht).jets.smooth.differentiable_iteratedDeriv n
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)
  have hl : LipschitzWith ⟨B,hB⟩ (iteratedDeriv n (deriv (V t))) := by
    apply lipschitzWith_of_nnnorm_deriv_le hd
    intro z
    have hz := hb t ht z
    rw [iteratedDeriv_succ] at hz
    exact_mod_cast hz
  have hx := hl.dist_le_mul y x
  simp only [Real.dist_eq] at hx
  change |iteratedDeriv n (deriv (V t)) y-iteratedDeriv n (deriv (V t)) x|≤B*|y-x| at hx
  have hh := abs_sub_le (iteratedDeriv n (deriv (V s)) y)
    (iteratedDeriv n (deriv (V t)) y) (iteratedDeriv n (deriv (V t)) x)
  have ht := ha s hs t ht y
  nlinarith [mul_nonneg hA (abs_nonneg (y-x)),mul_nonneg hB (abs_nonneg (s-t))]

lemma bounded_product_difference {a b c d A B Lf Lg ρ : ℝ}
    (ha : |a|≤A) (hd : |d|≤B) (hf : |a-c|≤Lf*ρ) (hg : |b-d|≤Lg*ρ)
    (hA : 0≤A) (hB : 0≤B) : |a*b-c*d|≤(A*Lg+B*Lf)*ρ := by
  have hid : a*b-c*d=a*(b-d)+d*(a-c) := by ring
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul]
  have h1 := mul_le_mul ha hg (abs_nonneg _) hA
  have h2 := mul_le_mul hd hf (abs_nonneg _) hB
  nlinarith

lemma SmoothEvolution.deriv_bound {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) (x : ℝ) :
    |deriv (V t) x|≤1 := by
  simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz (h.slices t ht).lipschitz (x₀ := x)

lemma SmoothEvolution.toValueStrip {T : ℝ} (hT : 0≤T) {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hγ : ∀ t∈Icc (0 : ℝ) T, 0≤γ t)
    (hγmono : MonotoneOn γ (Icc (0 : ℝ) T)) :
    ∃ K L, ValueStrip T γ V K L := by
  obtain ⟨B1,hB1,hb1⟩ := h.bound 1
  obtain ⟨B2,hB2,hb2⟩ := h.bound 2
  obtain ⟨L0,hL0,hl0⟩ := h.jet_joint 0
  obtain ⟨L1,hL1,hl1⟩ := h.jet_joint 1
  let K := B1+B2+1
  let L := L0+L1
  have hK : 0≤K := by dsimp [K]; positivity
  have hL : 0≤L := by dsimp [L]; positivity
  have hgint : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hγmono
  have hc1 (x : ℝ) : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_one] using h.continuous_jet 1 x
  have hc0 (x : ℝ) : ContinuousOn (fun t ↦ deriv (V t) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_zero] using h.continuous_jet 0 x
  refine ⟨K,L,hK,hL,hγ,hγmono,?_,fun t ht x ↦ h.deriv_bound ht x,?_,?_,?_,?_,?_,?_,?_,h.value_pde⟩
  · intro t ht
    exact (h.slices t ht).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  · intro t ht x
    have hb := hb1 t ht x
    simp only [iteratedDeriv_one] at hb
    dsimp [K]
    linarith
  · intro t ht x
    have hb := hb2 t ht x
    rw [←iteratedDeriv_succ'] at hb
    dsimp [K]
    linarith
  · intro t ht x
    have hb := h.deriv_bound ht x
    have hs : (deriv (V t) x)^2≤1 := (sq_le_one_iff_abs_le_one _).mpr hb
    rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/2),abs_of_nonneg (sq_nonneg _)]
    dsimp [K]
    nlinarith
  · intro t ht s hs x y
    have hb := hl1 s hs t ht x y
    simp only [iteratedDeriv_one] at hb
    dsimp [L]
    nlinarith [mul_nonneg hL0 (add_nonneg (abs_nonneg (s-t)) (abs_nonneg (y-x)))]
  · intro t ht s hs x y
    have hf := hl0 s hs t ht x y
    simp only [iteratedDeriv_zero] at hf
    have hb := bounded_product_difference (h.deriv_bound hs y) (h.deriv_bound ht x) hf hf (by norm_num) (by norm_num)
    have hid : (1/2 : ℝ)*(deriv (V s) y)^2-(1/2 : ℝ)*(deriv (V t) x)^2 =
      (1/2 : ℝ)*(deriv (V s) y*deriv (V s) y-deriv (V t) x*deriv (V t) x) := by ring
    rw [hid,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤1/2)]
    dsimp [L]
    nlinarith [mul_nonneg hL1 (add_nonneg (abs_nonneg (s-t)) (abs_nonneg (y-x)))]
  · intro x
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hc1 x
  · intro x
    apply hgint.mul_continuousOn
    rw [uIcc_of_le hT]
    convert! continuousOn_const.mul ((hc0 x).pow 2) using 1
    all_goals try with_reducible_and_instances rfl

lemma SmoothEvolution.toGradientStrip {T : ℝ} (hT : 0≤T) {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (hγ : ∀ t∈Icc (0 : ℝ) T, 0≤γ t)
    (hγmono : MonotoneOn γ (Icc (0 : ℝ) T)) (h0 : deriv (V 0) 0=0) :
    ∃ K L, GradientStrip T γ (fun t ↦ deriv (V t)) K L := by
  obtain ⟨B1,hB1,hb1⟩ := h.bound 1
  obtain ⟨B2,hB2,hb2⟩ := h.bound 2
  obtain ⟨B3,hB3,hb3⟩ := h.bound 3
  obtain ⟨L0,hL0,hl0⟩ := h.jet_joint 0
  obtain ⟨L1,hL1,hl1⟩ := h.jet_joint 1
  obtain ⟨L2,hL2,hl2⟩ := h.jet_joint 2
  let K := B1+B2+B3
  let L := L2+L1+B1*L0
  have hK : 0≤K := by dsimp [K]; positivity
  have hL : 0≤L := by dsimp [L]; positivity
  have hgint : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hγmono
  have hc0 (x : ℝ) : ContinuousOn (fun t ↦ deriv (V t) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_zero] using h.continuous_jet 0 x
  have hc1 (x : ℝ) : ContinuousOn (fun t ↦ deriv (deriv (V t)) x) (Icc (0 : ℝ) T) := by
    simpa only [iteratedDeriv_one] using h.continuous_jet 1 x
  have hc2 (x : ℝ) : ContinuousOn (fun t ↦ deriv (deriv (deriv (V t))) x) (Icc (0 : ℝ) T) := by
    simpa only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero]
      using h.continuous_jet 2 x
  have hb1' : ∀ t∈Icc (0 : ℝ) T, ∀ x, |deriv (deriv (V t)) x|≤B1 := by
    simpa only [iteratedDeriv_one] using hb1
  refine ⟨K,L,hK,hL,hγ,hγmono,?_,fun t ht x ↦ h.deriv_bound ht x,?_,?_,?_,?_,?_,?_,?_,h.gradient_pde,h0⟩
  · intro t ht
    exact (h.slices t ht).jets.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  · intro t ht x
    have hb := hb2 t ht x
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hb
    dsimp [K]
    linarith
  · intro t ht x
    have hb := hb3 t ht x
    dsimp [K]
    linarith
  · intro t ht x
    rw [abs_mul]
    have hb := mul_le_mul (h.deriv_bound ht x) (hb1' t ht x) (abs_nonneg _) (by norm_num)
    dsimp [K]
    linarith
  · intro t ht s hs x y
    have hb := hl2 s hs t ht x y
    simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hb
    dsimp [L]
    nlinarith [mul_nonneg (add_nonneg hL1 (mul_nonneg hB1 hL0))
      (add_nonneg (abs_nonneg (s-t)) (abs_nonneg (y-x)))]
  · intro t ht s hs x y
    have hf := hl0 s hs t ht x y
    have hg := hl1 s hs t ht x y
    simp only [iteratedDeriv_zero] at hf
    simp only [iteratedDeriv_one] at hg
    have hb := bounded_product_difference (h.deriv_bound hs y) (hb1' t ht x) hf hg (by norm_num) hB1
    dsimp [L]
    nlinarith [mul_nonneg hL2 (add_nonneg (abs_nonneg (s-t)) (abs_nonneg (y-x)))]
  · intro x
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hc2 x
  · intro x
    apply hgint.mul_continuousOn
    rw [uIcc_of_le hT]
    convert! (hc0 x).mul (hc1 x) using 1
    all_goals try with_reducible_and_instances rfl

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

lemma logCoshTerminal_even (M x : ℝ) : logCoshTerminal M (-x)=logCoshTerminal M x := by
  simp only [logCoshTerminal,mul_neg,Real.cosh_neg]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_EvenEvolution
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

lemma profileValue_even {ψ : ℝ → ℝ} (hψ : ∀ x, ψ (-x)=ψ x)
    (l : HeatProfile) (t x : ℝ) : profileValue ψ l t (-x)=profileValue ψ l t x := by
  induction l generalizing t x with
  | nil => exact hψ x
  | cons p l ih =>
    change (patchTime (E := ℝ → ℝ) _ _ _ t) (-x)=(patchTime (E := ℝ → ℝ) _ _ _ t) x
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht]
      exact coleHopf_even (fun y ↦ ih 0 y) _ _ _
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _ _

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_GridConvergence
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

lemma smoothApprox_even (γ : OrderParameter) (n : ℕ) (t x : ℝ) :
    smoothApprox γ n t (-x)=smoothApprox γ n t x :=
  profileValue_even (logCoshTerminal_even (n+1 : ℝ)) (γ.grid n) t x

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_Regularity
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

lemma phi_even (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Ico (0 : ℝ) 1) (x : ℝ) : phi W γ t (-x)=phi W γ t x := by
  have hl := (smoothApprox_tendsto W γ).tendsto_at (⟨t,ht⟩,-x)
  have hr := (smoothApprox_tendsto W γ).tendsto_at (⟨t,ht⟩,x)
  exact tendsto_nhds_unique hl (hr.congr (fun n ↦ (smoothApprox_even γ n t x).symm))

lemma phi_gradient_zero (W : BrownianSpace) (γ : OrderParameter) : gradient W γ 0 0=0 :=
  deriv_even_zero (phi_even W γ (by norm_num))

theorem sourceStripRegularity_oai (W : BrownianSpace) (γ : OrderParameter) : SourceStripRegularity W γ := by
  intro T hT
  have h := phi_evolution W γ hT
  have hγ : ∀ t∈Icc (0 : ℝ) T, 0 ≤ γ.coeff t :=
    fun t ht ↦ γ.nonneg _ ⟨ht.1,ht.2.trans_lt hT.2⟩
  have hmono : MonotoneOn γ.coeff (Icc (0 : ℝ) T) :=
    γ.monotone.mono (fun _ ht ↦ ⟨ht.1,ht.2.trans_lt hT.2⟩)
  obtain ⟨Kv,Lv,hV⟩ := h.toValueStrip hT.1 hγ hmono
  obtain ⟨K,L,hG⟩ := h.toGradientStrip hT.1 hγ hmono (phi_gradient_zero W γ)
  obtain ⟨D,hD,hb⟩ := h.bound 1
  obtain ⟨Lu,hLu,hu⟩ := h.jet_joint 0
  obtain ⟨La,hLa,ha⟩ := h.jet_joint 1
  refine ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,?_,?_,?_⟩
  · intro t ht x
    change |deriv (deriv (phi W γ t)) x| ≤ D
    simpa only [iteratedDeriv_one] using hb t ht x
  · intro s hs t ht x y
    simpa only [iteratedDeriv_zero,gradient] using hu s hs t ht y x
  · intro s hs t ht x y
    change |deriv (deriv (phi W γ s)) x-deriv (deriv (phi W γ t)) y| ≤ _
    simpa only [iteratedDeriv_one] using ha s hs t ht y x

end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.sourceStripRegularity_oai := @OAI.SKValue.sourceStripRegularity_oai
