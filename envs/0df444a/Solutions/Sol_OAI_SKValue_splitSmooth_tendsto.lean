-- Prove2me | solution 1 for OAI.SKValue.splitSmooth_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T08:07:18.411965+00:00
-- url     : https://prove2.me/submissions/e97fb063-db3a-411d-b518-80927466c61c

import Mathlib
import Definitions.Def_SKValue
import Definitions.Def_OAIQ4Sk000

section
-- module Solutions.OAIQ4_Sk.Compat
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_Cutoff
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators

namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma OrderParameter.cutoff_measurable (γ : OrderParameter) : Measurable γ.cutoff := by
  apply measurable_of_restrict_of_restrict_compl (s := Ico (0 : ℝ) 1) measurableSet_Ico
  · have hm : Monotone (fun t : Ico (0 : ℝ) 1 ↦ γ.coeff t) :=
      fun x y hxy ↦ γ.monotone x.property y.property hxy
    change Measurable (fun t : Ico (0 : ℝ) 1 ↦ γ.cutoff t)
    convert hm.measurable using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    exact Set.indicator_of_mem t.property γ.coeff
  · have he : ((Ico (0 : ℝ) 1)ᶜ).domRestrict γ.cutoff = fun _ ↦ (0 : ℝ) := by
      funext t
      exact Set.indicator_of_notMem t.property γ.coeff
    rw [he]
    exact measurable_const

lemma OrderParameter.cutoff_integrable (γ : OrderParameter) : Integrable γ.cutoff := by
  apply (integrable_indicator_iff measurableSet_Ico).mpr
  have hi : IntegrableOn γ.coeff (Icc (0 : ℝ) 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioc (by finiteness)).mpr γ.integrable
  exact hi.mono_set Ico_subset_Icc_self

lemma limitedControl_eq {W : BrownianSpace} (α : ℝ≥0 → W.Ω → ℝ) {s : ℝ}
    (hs : s≤1) (ω : W.Ω) : limitedControl α s ω=α (Real.toNNReal s) ω := by
  have hs' : Real.toNNReal s≤(1 : ℝ≥0) := Real.toNNReal_le_iff_le_coe.mpr hs
  simp only [limitedControl, min_eq_left hs']

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlIntegral
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma controlIntegral_eq (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (α : ℝ≥0 → W.Ω → ℝ) (n : ℕ) (ω : W.Ω) :
    controlIntegral γ t α n ω =
      ∫ s in (0 : ℝ)..(1-t), γ.coeff (t+s)*(α (Real.toNNReal s) ω)^n := by
  unfold controlIntegral
  apply intervalIntegral.integral_congr_Ioo_of_le (sub_nonneg.mpr ht.2)
  intro s hs
  have hts : t+s∈Ico (0 : ℝ) 1 := ⟨by linarith [hs.1,ht.1],by linarith [hs.2]⟩
  change γ.cutoff (t+s) * (limitedControl α s ω)^n = γ.coeff (t+s) * (α (Real.toNNReal s) ω)^n
  unfold OrderParameter.cutoff
  rw [Set.indicator_of_mem hts, limitedControl_eq α (by linarith [hs.2,ht.1]) ω]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_AdmissibleZero
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma controlPayoff_eq (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) (α : ℝ≥0 → W.Ω → ℝ) :
    controlPayoff W γ t x α = ∫ ω,
      |x+(W.B 1 ω-W.B t.toNNReal ω)+controlIntegral γ t α 1 ω|-
        (1/2 : ℝ)*controlIntegral γ t α 2 ω ∂W.μ := by
  simp only [controlPayoff, controlIntegral_eq W γ ht, pow_one]
  congr 1
  funext ω
  congr 2
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlPayoffConvex
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma brownian_increment_memLp (W : BrownianSpace) (t : ℝ) :
    MemLp (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω) 2 W.μ :=
  (W.brownian.hasLaw_sub 1 t.toNNReal).hasGaussianLaw.memLp (by norm_num)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_Controls
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

lemma progressive_clamped_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} (hα : IsProgressive f α) (t : ℝ≥0) :
    @Measurable (ℝ×Ω) ℝ (borel ℝ |>.prod (f t)) inferInstance
      (fun p ↦ α (min (Real.toNNReal p.1) t) p.2) := by
  have hj := hα t
  let : MeasurableSpace Ω := f t
  have hc : Measurable (fun p : ℝ×Ω ↦
      (⟨min (Real.toNNReal p.1) t, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Iic t)) :=
    ((measurable_real_toNNReal.comp measurable_fst).min measurable_const).subtype_mk
  exact hj.comp (hc.prodMk measurable_snd)

lemma controlAccum_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ}
    (hα : IsProgressive f α) (hγ : Measurable γ) (n : ℕ) {t : ℝ} (ht : 0≤t) :
    Measurable[f (Real.toNNReal t)] (controlAccum γ α n t) := by
  let : MeasurableSpace Ω := f (Real.toNNReal t)
  have hm : Measurable (fun p : ℝ×Ω ↦ γ p.1*(α (min (Real.toNNReal p.1) (Real.toNNReal t)) p.2)^n) :=
    (hγ.comp measurable_fst).mul ((progressive_clamped_measurable (m := m) hα _).pow_const n)
  have heq : controlAccum γ α n t = fun ω ↦
      ∫ s in (0 : ℝ)..t, γ s*(α (min (Real.toNNReal s) (Real.toNNReal t)) ω)^n := by
    funext ω
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht] at hs
    dsimp only
    rw [min_eq_left (Real.toNNReal_mono hs.2)]
  rw [heq]
  unfold intervalIntegral
  exact hm.stronglyMeasurable.integral_prod_left.measurable.sub
    hm.stronglyMeasurable.integral_prod_left.measurable

lemma controlAccum_bound {Ω : Type*} {γ : ℝ → ℝ} {α : ℝ≥0 → Ω → ℝ}
    {T t G : ℝ} (ht : 0≤t) (htT : t≤T)
    (hα : ∀ s ω, |α s ω|≤1) (hγ : ∀ s∈Icc (0 : ℝ) T, |γ s|≤G)
    (n : ℕ) (ω : Ω) : |controlAccum γ α n t ω|≤t*G := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (f := fun s ↦ γ s*(α (Real.toNNReal s) ω)^n) (C := G) (fun s hs ↦ by
      rw [uIoc_of_le ht] at hs
      rw [Real.norm_eq_abs,abs_mul,abs_pow]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hα _ _)) (abs_nonneg _)).trans
        (by simpa only [mul_one] using hγ s ⟨hs.1.le,hs.2.trans htT⟩))
  simpa only [controlAccum,Real.norm_eq_abs,sub_zero,abs_of_nonneg ht,mul_comm G t] using hh

lemma controlAccum_integrable {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T t G : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hγb : ∀ s∈Icc (0 : ℝ) T, |γ s|≤G) (n : ℕ) (ht : 0≤t) (htT : t≤T) :
    Integrable (controlAccum γ α n t) μ := by
  apply Integrable.of_bound
    ((controlAccum_measurable hα hγ n ht).mono (f.le _) le_rfl).aestronglyMeasurable (t*G)
  exact Eventually.of_forall (fun ω ↦ by
    simpa only [Real.norm_eq_abs] using controlAccum_bound ht htT hαb hγb n ω)

lemma controlAccum_integrand_intervalIntegrable {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) (n : ℕ) (ω : Ω) :
    IntervalIntegrable (fun s ↦ γ s*(α (Real.toNNReal s) ω)^n) volume 0 T := by
  have hm : Measurable (fun s ↦ γ s*(α (min (Real.toNNReal s) (Real.toNNReal T)) ω)^n) := by
    let : MeasurableSpace Ω := f (Real.toNNReal T)
    exact hγ.mul (((progressive_clamped_measurable (m := m) hα _).comp
      (measurable_id.prodMk measurable_const)).pow_const n)
  have hint : IntervalIntegrable (fun s ↦ γ s*(α (min (Real.toNNReal s) (Real.toNNReal T)) ω)^n) volume 0 T := by
    apply hi.norm.mono_fun'
    · exact hm.aestronglyMeasurable
    · exact Eventually.of_forall (fun s ↦ by
        dsimp only
        rw [Real.norm_eq_abs,abs_mul,abs_pow,Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hαb _ _))
          (abs_nonneg _)).trans_eq (mul_one _))
  apply hint.congr
  intro s hs
  rw [uIoc_of_le hT] at hs
  dsimp only
  rw [min_eq_left (Real.toNNReal_mono hs.2)]

end SKValue

namespace SKValue

lemma controlState_past_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, StronglyMeasurable (B t))
    {γ : ℝ → ℝ} {α : ℝ≥0 → Ω → ℝ}
    (hα : IsProgressive (Filtration.natural B hBm) α) (hγ : Measurable γ) (x : ℝ)
    {t : ℝ} (ht : 0≤t) :
    StronglyMeasurable[Filtration.natural B hBm (Real.toNNReal t)] (controlState B γ α x t) :=
  (stronglyMeasurable_const.add (Filtration.stronglyAdapted_natural hBm _)).add
    (controlAccum_measurable hα hγ 1 ht).stronglyMeasurable

lemma controlState_memLp_two {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B μ) (hBm : ∀ t, StronglyMeasurable (B t))
    {γ : ℝ → ℝ} {α : ℝ≥0 → Ω → ℝ} {T t G : ℝ}
    (hα : IsProgressive (Filtration.natural B hBm) α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hγb : ∀ s∈Icc (0 : ℝ) T, |γ s|≤G)
    (x : ℝ) (ht : 0≤t) (htT : t≤T) : MemLp (controlState B γ α x t) 2 μ := by
  have hi : MemLp (controlAccum γ α 1 t) 2 μ := MemLp.of_bound
    ((controlAccum_measurable hα hγ 1 ht).mono (Filtration.le _ _) le_rfl).aestronglyMeasurable
    (t*G) (Eventually.of_forall (fun ω ↦ by
      simpa only [Real.norm_eq_abs] using controlAccum_bound ht htT hαb hγb 1 ω))
  exact ((memLp_const x).add (hB.hasLaw_eval _).hasGaussianLaw.memLp_two).add hi

lemma controlState_initial {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (γ : ℝ → ℝ) (α : ℝ≥0 → Ω → ℝ) (x : ℝ) :
    ∀ᵐ ω ∂μ, controlState B γ α x 0 ω=x := by
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
  simp only [controlState,controlAccum,Real.toNNReal_zero,hω,add_zero,
    intervalIntegral.integral_same]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ShiftedPairing
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace SKValue

lemma integral_sq_le_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, f ω ∂μ)^2 ≤ ∫ ω, (f ω)^2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  exact sub_nonneg.mp h

lemma integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ) ≤ Real.sqrt (∫ ω, (f ω)^2 ∂μ) := by
  have hab : MemLp (fun ω ↦ |f ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have h := integral_sq_le_integral_sq hab
  simp only [sq_abs] at h
  exact (Real.le_sqrt (integral_nonneg (fun _ ↦ abs_nonneg _))
    (integral_nonneg (fun _ ↦ sq_nonneg _))).mpr h

end SKValue

open MeasureTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_InitialMax
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

lemma intervalIntegrable_substrip {f : ℝ → ℝ} {T a b : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T) (ha : a ∈ Icc (0 : ℝ) T)
    (hb : b ∈ Icc (0 : ℝ) T) : IntervalIntegrable f volume a b := by
  apply hf.mono_set
  rw [uIcc_of_le hT]
  exact uIcc_subset_Icc ha hb

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_MemLpLinearCombination
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace SKValue
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} {g : ι → Ω → ℝ}

lemma memLp_linearCombination (hg : ∀ i, MemLp (g i) 2 μ) (b : ι → ℝ) :
    MemLp (fun ω ↦ ∑ i, b i*g i ω) 2 μ := by
  exact memLp_finsetSum Finset.univ (fun i _ ↦ (hg i).const_mul (b i))

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_GroundState_PredictableNormalizer
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SKValue

lemma independent_of_coordinate_not_in {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace β]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    (S : Finset ι) {j : ι} (hj : j ∉ S) {F : (ι → ℝ) → β}
    (hF : Measurable F)
    (hdep : ∀ x y, (∀ i ∈ S, x i=y i) → F x=F y) :
    IndepFun F (fun x ↦ x j) (Measure.pi μ) := by
  let fill : (S → ℝ) → ι → ℝ := fun x i ↦ if hi : i ∈ S then x ⟨i,hi⟩ else 0
  have hfill : Measurable fill := by
    apply Measurable.of_eval
    intro i
    by_cases hi : i ∈ S
    · simpa only [fill, dite_eq_left hi] using (measurable_pi_apply (⟨i,hi⟩ : S))
    · simp only [fill, dite_eq_right hi]
      exact measurable_const
  have hid : ∀ x : ι → ℝ, F (fill (fun i : S ↦ x i)) = F x := by
    intro x
    apply hdep
    intro i hi
    simp [fill,hi]
  have hST : Disjoint S {j} := by simpa using hj
  have hind : iIndepFun (fun i (x : ι → ℝ) ↦ x i) (Measure.pi μ) :=
    iIndepFun_pi (fun i ↦ (measurable_id : Measurable (id : ℝ → ℝ)).aemeasurable)
  have H := (hind.indepFun_finset S {j} hST (fun i ↦ measurable_pi_apply i)).comp
    (hF.comp hfill) (measurable_pi_apply (⟨j,by simp⟩ : ({j} : Finset ι)))
  simpa only [Function.comp_def, hid] using H

lemma measurable_coordinate (N j : ℕ) : Measurable (coordinate N j) :=
  measurable_pi_apply _

lemma coordinate_eq_apply {N j : ℕ} (hj : j < N+1) (z : Fin (N+1) → ℝ) :
    coordinate N j z = z ⟨j,hj⟩ := by
  simp [coordinate, Nat.mod_eq_of_lt hj]

lemma euler_depends_on_past (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (j : ℕ) (z z' : Fin (N+1) → ℝ)
    (h : ∀ i < j, coordinate N i z=coordinate N i z') :
    euler T N γ u z j=euler T N γ u z' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hp := ih (fun i hi ↦ h i (by omega))
    simp only [euler, hp,h j (by omega)]

lemma measurable_euler (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hU : ∀ k < N, Measurable (u (meshTime T N k))) :
    ∀ j ≤ N, Measurable (fun z ↦ euler T N γ u z j) := by
  intro j hj
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hjN : j < N := by omega
    have hy := ih (by omega)
    have hz := measurable_coordinate N j
    have hu := (hU j hjN).comp hy
    simp only [euler]
    fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma gaussian_mean {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, Z ω ∂μ = 0 := by
  rw [hZ.integral_eq, integral_id_gaussianReal]

lemma gaussian_memLp {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp Z p μ := by
  have H : MemLp (id : ℝ → ℝ) p (μ.map Z) := by
    rw [hZ.map_eq]
    exact memLp_id_gaussianReal' p hp
  simpa using (memLp_map_measure_iff H.aestronglyMeasurable hZ.aemeasurable).1 H

lemma gaussian_second_moment {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    ∫ ω, (Z ω)^2 ∂μ = 1 := by
  have hvar := hZ.variance_eq
  rw [variance_eq_integral hZ.aemeasurable, gaussian_mean hZ] at hvar
  simpa using hvar

lemma coordinate_hasLaw (N j : ℕ) :
    HasLaw (coordinate N j) (gaussianReal 0 1) (gaussianProduct (Fin (N+1))) :=
  (measurePreserving_eval (fun _ : Fin (N+1) ↦ standardGaussian)
    ⟨j % (N+1), Nat.mod_lt _ (Nat.succ_pos _)⟩).hasLaw

lemma DependsBefore.independent {N j : ℕ} {β : Type*} [MeasurableSpace β] (hj : j<N+1)
    {F : (Fin (N+1) → ℝ) → β} (hF : DependsBefore j F) (hm : Measurable F) :
    IndepFun F (coordinate N j) (gaussianProduct (Fin (N+1))) := by
  have H := independent_of_coordinate_not_in (μ := fun _ : Fin (N+1) ↦ standardGaussian)
    (Finset.univ.filter (fun i : Fin (N+1) ↦ (i : ℕ)<j))
    (j := ⟨j,hj⟩) (by simp) hm (fun z z' heq ↦ hF z z' (by simpa using heq))
  have heq : coordinate N j = fun z : Fin (N+1) → ℝ ↦ z ⟨j,hj⟩ :=
    funext (coordinate_eq_apply hj)
  rw [heq]
  exact H

lemma DependsBefore.mono {N i j : ℕ} {β : Type*} {F : (Fin (N+1) → ℝ) → β}
    (hF : DependsBefore i F) (hij : i≤j) : DependsBefore j F :=
  fun z z' h ↦ hF z z' (fun k hk ↦ h k (hk.trans_le hij))

lemma DependsBefore.mul {N j : ℕ} {F G : (Fin (N+1) → ℝ) → ℝ}
    (hF : DependsBefore j F) (hG : DependsBefore j G) :
    DependsBefore j (fun z ↦ F z * G z) := by
  intro z z' h
  dsimp only
  rw [hF z z' h, hG z z' h]

lemma eulerCoefficient_dependsBefore (T : ℝ) {N j : ℕ} (hj : j≤N)
    (γ : ℝ → ℝ) (u a : ℝ → ℝ → ℝ) :
    DependsBefore j (fun z ↦ a (meshTime T N j) (euler T N γ u z j)) := by
  intro z z' h
  apply congrArg (a (meshTime T N j))
  apply euler_depends_on_past
  intro i hi
  have hiN : i<N+1 := by omega
  rw [coordinate_eq_apply hiN, coordinate_eq_apply hiN]
  exact h ⟨i,hiN⟩ hi

end SKValue

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_GaussianSquareVariance
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma gaussian_square_memLp_two {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    MemLp (fun ω ↦ (Z ω)^2) 2 μ := by
  have h := (gaussian_memLp hZ 4 (by norm_num)).norm_rpow_div 2
  norm_num [Real.norm_eq_abs, Real.rpow_two, sq_abs] at h
  have he : (4 : ℝ≥0∞)/2=2 := by
    change ((4 : ℝ≥0) : ℝ≥0∞)/((2 : ℝ≥0) : ℝ≥0∞)=((2 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.coe_div] <;> norm_num
  rwa [he] at h

lemma gaussian_centered_square_memLp_two [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    MemLp (fun ω ↦ (Z ω)^2-1) 2 μ :=
  (gaussian_square_memLp_two hZ).sub (memLp_const 1)

lemma gaussian_centered_square_mean [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    (∫ ω, (Z ω)^2-1 ∂μ)=0 := by
  rw [integral_sub (gaussian_memLp hZ 2 (by norm_num)).integrable_sq (integrable_const 1),
    gaussian_second_moment hZ]
  simp

lemma gaussianSquareVariance_nonneg : 0≤gaussianSquareVariance :=
  integral_nonneg fun _ ↦ sq_nonneg _

lemma gaussian_centered_square_variance {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    (∫ ω, ((Z ω)^2-1)^2 ∂μ)=gaussianSquareVariance := by
  exact hZ.integral_comp (f := fun z : ℝ ↦ (z^2-1)^2) (by fun_prop)

lemma predictableCenteredSquare_memLp {N j : ℕ}
    {H : (Fin (N+1) → ℝ) → ℝ} {K : ℝ}
    (hm : Measurable H) (hbound : ∀ z, |H z|≤K) :
    MemLp (fun z ↦ H z*((coordinate N j z)^2-1)) 2 (gaussianProduct (Fin (N+1))) := by
  have hQ := (gaussian_centered_square_memLp_two (coordinate_hasLaw N j))
  have hH : MemLp H ∞ (gaussianProduct (Fin (N+1))) :=
    MemLp.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hbound))
  exact hQ.mul' hH

lemma predictableCenteredSquare_variance {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} {K : ℝ}
    (hK : 0≤K) (hm : Measurable H) (hp : DependsBefore j H) (hbound : ∀ z, |H z|≤K) :
    (∫ z, (H z*((coordinate N j z)^2-1))^2 ∂gaussianProduct (Fin (N+1))) ≤
      K^2*gaussianSquareVariance := by
  have hind := (hp.independent hj hm).comp (measurable_id.pow_const 2)
    ((measurable_id.pow_const 2 |>.sub (measurable_const (a := (1 : ℝ)))).pow_const 2)
  have hi := hind.integral_mul_eq_mul_integral (hm.pow_const 2).aestronglyMeasurable
    (((measurable_coordinate N j).pow_const 2 |>.sub (measurable_const (a := (1 : ℝ)))).pow_const 2).aestronglyMeasurable
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] at hi
  simp_rw [mul_pow]
  rw [hi, gaussian_centered_square_variance (coordinate_hasLaw N j)]
  have hH : MemLp H 2 (gaussianProduct (Fin (N+1))) := MemLp.of_bound hm.aestronglyMeasurable K
    (Filter.Eventually.of_forall (by simpa only [Real.norm_eq_abs] using hbound))
  have hb : (∫ z, (H z)^2 ∂gaussianProduct (Fin (N+1))) ≤ K^2 := by
    have hi' := integral_mono hH.integrable_sq (integrable_const (K^2))
      (fun z ↦ by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 (hbound z))
    simpa using hi'
  exact mul_le_mul_of_nonneg_right hb gaussianSquareVariance_nonneg

lemma centeredSquare_dependsBefore {N j : ℕ} (hj : j<N+1)
    {H : (Fin (N+1) → ℝ) → ℝ} (hp : DependsBefore j H) :
    DependsBefore (j+1) (fun z ↦ H z*((coordinate N j z)^2-1)) := by
  intro z z' h
  dsimp only
  rw [hp.mono (Nat.le_succ j) z z' h]
  have hz : coordinate N j z=coordinate N j z' := by
    rw [coordinate_eq_apply hj, coordinate_eq_apply hj]
    exact h ⟨j,hj⟩ (Nat.lt_succ_self j)
  rw [hz]

lemma predictableCenteredSquares_orthogonal {N i j : ℕ} (hij : i<j) (hj : j<N+1)
    {H K : (Fin (N+1) → ℝ) → ℝ}
    (hHm : Measurable H) (hKm : Measurable K)
    (hHp : DependsBefore i H) (hKp : DependsBefore j K) :
    (∫ z, (H z*((coordinate N i z)^2-1))*(K z*((coordinate N j z)^2-1))
      ∂gaussianProduct (Fin (N+1)))=0 := by
  have hprev := (centeredSquare_dependsBefore (hij.trans hj) hHp).mono (by omega : i+1≤j)
  have hpm : Measurable (fun z ↦ H z*((coordinate N i z)^2-1)) :=
    hHm.mul (((measurable_coordinate N i).pow_const 2).sub (measurable_const (a := (1 : ℝ))))
  have hind := ((hprev.mul hKp).independent hj (hpm.mul hKm)).comp measurable_id
    ((measurable_id.pow_const 2).sub (measurable_const (a := (1 : ℝ))))
  have ht := hind.integral_mul_eq_mul_integral (hpm.mul hKm).aestronglyMeasurable
    (((measurable_coordinate N j).pow_const 2).sub (measurable_const (a := (1 : ℝ)))).aestronglyMeasurable
  simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_def, id_eq] at ht
  simp_rw [mul_assoc] at ht ⊢
  rw [ht, gaussian_centered_square_mean (coordinate_hasLaw N j), mul_zero]

lemma orthogonal_sum_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Ω → ℝ} (hR : ∀ i, MemLp (R i) 2 μ)
    (horth : ∀ i j, i≠j → (∫ ω, R i ω*R j ω ∂μ)=0) :
    (∫ ω, (∑ i, R i ω)^2 ∂μ)=∑ i, ∫ ω, (R i ω)^2 ∂μ := by
  have hsum : MemLp (fun ω ↦ ∑ i, R i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hR i)
  have hi j : (∫ ω, (∑ i, R i ω)*R j ω ∂μ) = ∫ ω, (R j ω)^2 ∂μ := by
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum Finset.univ (fun i _ ↦
      show Integrable (fun ω ↦ R i ω*R j ω) μ from (hR i).integrable_mul (hR j))]
    rw [Finset.sum_eq_single j]
    · simp [pow_two]
    · intro i _ hij
      exact horth i j hij
    · simp
  simp_rw [pow_two, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (fun i _ ↦
    show Integrable (fun ω ↦ R i ω*(∑ j, R j ω)) μ from (hR i).integrable_mul hsum)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (fun ω ↦ R i ω*(∑ j, R j ω))=(fun ω ↦ (∑ j, R j ω)*R i ω)
    from funext (fun _ ↦ mul_comm _ _), hi]
  simp [pow_two]

lemma predictableCenteredSquare_sum_bound {N : ℕ} {δ K : ℝ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ} (hK : 0≤K)
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hb : ∀ i z, |H i z|≤K) :
    (∫ z, ((δ/2)*(∑ i : Fin N, H i z*((coordinate N i z)^2-1)))^2
      ∂gaussianProduct (Fin (N+1))) ≤ (δ/2)^2*(N : ℝ)*K^2*gaussianSquareVariance := by
  have hmem (i : Fin N) := predictableCenteredSquare_memLp (j := (i : ℕ)) (hm i) (hb i)
  have hort : ∀ i j : Fin N, i≠j →
      (∫ z, (H i z*((coordinate N i z)^2-1))*(H j z*((coordinate N j z)^2-1))
        ∂gaussianProduct (Fin (N+1)))=0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact predictableCenteredSquares_orthogonal (by exact_mod_cast h) (by omega)
        (hm i) (hm j) (hp i) (hp j)
    · rw [show (fun z ↦ (H i z*((coordinate N i z)^2-1))*(H j z*((coordinate N j z)^2-1))) =
          (fun z ↦ (H j z*((coordinate N j z)^2-1))*(H i z*((coordinate N i z)^2-1)))
          from funext (fun _ ↦ mul_comm _ _)]
      exact predictableCenteredSquares_orthogonal (by exact_mod_cast h) (by omega)
        (hm j) (hm i) (hp j) (hp i)
  simp_rw [mul_pow]
  rw [integral_const_mul, orthogonal_sum_square hmem hort]
  calc
    _ ≤ (δ/2)^2*(∑ _i : Fin N, K^2*gaussianSquareVariance) := by
      gcongr with i
      exact predictableCenteredSquare_variance (by omega) hK (hm i) (hp i) (hb i)
    _ = _ := by simp; ring

lemma cubicEnvelope_nonneg {G K C : ℝ} (hG : 0≤G) (hK : 0≤K) (hC : 0≤C) (z : ℝ) :
    0 ≤ cubicEnvelope G K C z := by unfold cubicEnvelope; positivity

lemma measurable_cubicEnvelope (G K C : ℝ) : Measurable (cubicEnvelope G K C) := by
  unfold cubicEnvelope
  fun_prop

lemma abs_add_cube_memLp {Z : Ω → ℝ} (hz6 : MemLp (fun ω ↦ |Z ω|) 6 μ)
    {G : ℝ} (hG : 0≤G) [IsProbabilityMeasure μ] :
    MemLp (fun ω ↦ (|Z ω|+G)^3) 2 μ := by
  have hbase : MemLp (fun ω ↦ |Z ω|+G) 6 μ := hz6.add (memLp_const G)
  have hpow := hbase.norm_rpow_div 3
  have he : (6 : ℝ≥0∞)/3=2 := by
    change ((6 : ℝ≥0) : ℝ≥0∞)/((3 : ℝ≥0) : ℝ≥0∞)=((2 : ℝ≥0) : ℝ≥0∞)
    rw [← ENNReal.coe_div] <;> norm_num
  have hh : ∀ ω, ‖|Z ω|+G‖=|Z ω|+G := fun ω ↦ Real.norm_of_nonneg (by positivity)
  simpa only [hh, ENNReal.toReal_ofNat, Real.rpow_ofNat, he] using hpow

lemma cubicEnvelope_memLp_two [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) {G : ℝ} (hG : 0≤G) (K C : ℝ) :
    MemLp (fun ω ↦ cubicEnvelope G K C (Z ω)) 2 μ := by
  have hz6 : MemLp (fun ω ↦ |Z ω|) 6 μ := by
    simpa only [Real.norm_eq_abs] using (gaussian_memLp hZ 6 (by norm_num)).norm
  have hp := abs_add_cube_memLp hz6 hG
  have hz2 : MemLp (fun ω ↦ |Z ω|) 2 μ := hz6.mono_exponent (by norm_num)
  have hlin : MemLp (fun ω ↦ 1+|Z ω|+G) 2 μ := ((memLp_const (1 : ℝ)).add hz2).add (memLp_const G)
  have hlast : MemLp (fun ω ↦ |Z ω|+G/2) 2 μ := hz2.add (memLp_const (G/2))
  change MemLp (fun ω ↦ K*(|Z ω|+G)^3+C*(1+|Z ω|+G)+K*G*(|Z ω|+G/2)) 2 μ
  exact ((hp.const_mul K).add (hlin.const_mul C)).add (hlast.const_mul (K*G))

lemma cubicEnvelope_moment_eq {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) μ) (G K C : ℝ) :
    (∫ ω, (cubicEnvelope G K C (Z ω))^2 ∂μ)=cubicEnvelopeMoment G K C :=
  hZ.integral_comp (f := fun z ↦ (cubicEnvelope G K C z)^2)
    ((measurable_cubicEnvelope G K C).pow_const 2).aestronglyMeasurable

lemma finite_sum_square_le {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i)^2≤(Fintype.card ι : ℝ)*(∑ i, (f i)^2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι ↦ (1 : ℝ)) f
  simpa using h

lemma finite_envelope_L2_bound [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {P : ι → Ω → ℝ} {R : Ω → ℝ} {α β M : ℝ}
    (hα : 0≤α) (hβ : 0≤β) (hPm : ∀ i, MemLp (P i) 2 μ)
    (hPpos : ∀ i ω, 0≤P i ω) (hPval : ∀ i, (∫ ω, (P i ω)^2 ∂μ)≤M)
    (hRm : AEStronglyMeasurable R μ)
    (hR : ∀ ω, |R ω|≤α*(∑ i, P i ω)+β) :
    (∫ ω, (R ω)^2 ∂μ) ≤ 2*α^2*(Fintype.card ι : ℝ)^2*M+2*β^2 := by
  have hsum : MemLp (fun ω ↦ ∑ i, P i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hPm i)
  have henv : MemLp (fun ω ↦ α*(∑ i, P i ω)+β) 2 μ := (hsum.const_mul α).add (memLp_const β)
  have hsumpos (ω : Ω) : 0≤∑ i, P i ω := Finset.sum_nonneg (fun i _ ↦ hPpos i ω)
  have henvpos (ω : Ω) : 0≤α*(∑ i, P i ω)+β := add_nonneg (mul_nonneg hα (hsumpos ω)) hβ
  have hRmem : MemLp R 2 μ := henv.mono hRm (Filter.Eventually.of_forall (fun ω ↦ by
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (henvpos ω)]
    exact hR ω))
  have hbound : ∀ ω, (R ω)^2 ≤ 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)+2*β^2 := by
    intro ω
    have he : 0≤α*(∑ i, P i ω)+β := henvpos ω
    have hsq := (sq_le_sq₀ (abs_nonneg _) he).2 (hR ω)
    rw [sq_abs] at hsq
    have hfin := finite_sum_square_le (fun i ↦ P i ω)
    have hmul := mul_le_mul_of_nonneg_left hfin (show 0≤2*α^2 by positivity)
    nlinarith [sq_nonneg (α*(∑ i, P i ω)-β)]
  have hfirst : Integrable (fun ω ↦ 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)) μ :=
    (integrable_finsetSum Finset.univ (fun i _ ↦ (hPm i).integrable_sq)).const_mul _
  have heint : Integrable (fun ω ↦ 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)+2*β^2) μ :=
    hfirst.add (integrable_const _)
  calc
    _ ≤ ∫ ω, 2*α^2*(Fintype.card ι : ℝ)*(∑ i, (P i ω)^2)+2*β^2 ∂μ :=
      integral_mono hRmem.integrable_sq heint hbound
    _ = 2*α^2*(Fintype.card ι : ℝ)*(∑ i, ∫ ω, (P i ω)^2 ∂μ)+2*β^2 := by
      rw [integral_add hfirst (integrable_const _)]
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ ↦ (hPm i).integrable_sq)]
      simp
    _ ≤ 2*α^2*(Fintype.card ι : ℝ)*(∑ _i : ι, M)+2*β^2 := by gcongr with i; exact hPval i
    _ = _ := by simp; ring

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_SumStepsSub
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma sum_steps_sub {N : ℕ} (U : ℕ → ℝ) :
    (∑ i : Fin N, (U (i+1)-U i))=U N-U 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ U (j+1)-U j)]
  exact Finset.sum_range_sub U N

lemma sum_local_residual {N : ℕ} (U : ℕ → ℝ) (V W : Fin N → ℝ) :
    (∑ i : Fin N, (U (i+1)-U i-V i-W i)) = U N-U 0-(∑ i, V i)-(∑ i, W i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_steps_sub]

lemma sum_local_residual_bound {N : ℕ} {U : ℕ → ℝ} {V W P : Fin N → ℝ}
    {Γ : ℕ → ℝ} {α β : ℝ}
    (hlocal : ∀ i : Fin N, |U (i+1)-U i-V i-W i|≤α*P i+β*(Γ (i+1)-Γ i)) :
    |U N-U 0-(∑ i, V i)-(∑ i, W i)|≤α*(∑ i, P i)+β*(Γ N-Γ 0) := by
  rw [← sum_local_residual]
  calc
    _ ≤ ∑ i : Fin N, |U (i+1)-U i-V i-W i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, (α*P i+β*(Γ (i+1)-Γ i)) := Finset.sum_le_sum (fun i _ ↦ hlocal i)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_steps_sub]

lemma finite_envelope_memLp [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {P : ι → Ω → ℝ} {R : Ω → ℝ} {α β : ℝ}
    (hα : 0≤α) (hβ : 0≤β) (hPm : ∀ i, MemLp (P i) 2 μ)
    (hPpos : ∀ i ω, 0≤P i ω) (hRm : AEStronglyMeasurable R μ)
    (hR : ∀ ω, |R ω|≤α*(∑ i, P i ω)+β) : MemLp R 2 μ := by
  have hsum : MemLp (fun ω ↦ ∑ i, P i ω) 2 μ := memLp_finsetSum _ (fun i _ ↦ hPm i)
  have henv := (hsum.const_mul α).add (memLp_const β)
  apply henv.mono hRm
  filter_upwards [] with ω
  have hs : 0≤∑ i, P i ω := Finset.sum_nonneg (fun i _ ↦ hPpos i ω)
  have he : 0≤α*(∑ i, P i ω)+β := add_nonneg (mul_nonneg hα hs) hβ
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg he] using hR ω

lemma integral_square_add_le {R Q : Ω → ℝ} (hR : MemLp R 2 μ) (hQ : MemLp Q 2 μ) :
    (∫ ω, (R ω+Q ω)^2 ∂μ)≤2*(∫ ω, (R ω)^2 ∂μ)+2*(∫ ω, (Q ω)^2 ∂μ) := by
  calc
    _ ≤ ∫ ω, 2*(R ω)^2+2*(Q ω)^2 ∂μ := by
      apply integral_mono (hR.add hQ).integrable_sq
        ((hR.integrable_sq.const_mul 2).add (hQ.integrable_sq.const_mul 2))
      intro ω
      change (R ω+Q ω)^2≤2*(R ω)^2+2*(Q ω)^2
      nlinarith [sq_nonneg (R ω-Q ω)]
    _ = _ := by
      rw [integral_add (hR.integrable_sq.const_mul 2) (hQ.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]

lemma discrete_gradient_residual_L2 {N : ℕ} {δ G K C : ℝ} {Γ : ℕ → ℝ}
    {U : ℕ → (Fin (N+1) → ℝ) → ℝ}
    {A H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hδ : 0≤δ) (hG : 0≤G) (hK : 0≤K) (hC : 0≤C)
    (hΓ : Γ 0≤Γ N)
    (hUm : ∀ j ≤ N, Measurable (U j))
    (hAm : ∀ i, Measurable (A i))
    (hHm : ∀ i, Measurable (H i)) (hHp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hHb : ∀ i z, |H i z|≤K)
    (hloc : ∀ (i : Fin N) z,
      |U (i+1) z-U i z-Real.sqrt δ*A i z*coordinate N i z-
        (δ/2)*H i z*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope G K C (coordinate N i z)+δ*K*(Γ (i+1)-Γ i)) :
    (∫ z, (U N z-U 0 z-∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)^2
      ∂gaussianProduct (Fin (N+1))) ≤
      2*((δ/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(δ*Real.sqrt δ)^2*(N : ℝ)^2*cubicEnvelopeMoment G K C+
      4*(δ*K*(Γ N-Γ 0))^2 := by
  let P (i : Fin N) (z : Fin (N+1) → ℝ) := cubicEnvelope G K C (coordinate N i z)
  let Q (z : Fin (N+1) → ℝ) :=
    (δ/2)*(∑ i : Fin N, H i z*((coordinate N i z)^2-1))
  let R (z : Fin (N+1) → ℝ) :=
    U N z-U 0 z-(∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)-Q z
  have hPm (i : Fin N) : MemLp (P i) 2 (gaussianProduct (Fin (N+1))) :=
    cubicEnvelope_memLp_two (coordinate_hasLaw N i) hG K C
  have hPpos (i : Fin N) z : 0≤P i z := cubicEnvelope_nonneg hG hK hC _
  have hPval (i : Fin N) : (∫ z, (P i z)^2 ∂gaussianProduct (Fin (N+1))) ≤ cubicEnvelopeMoment G K C :=
    le_of_eq (cubicEnvelope_moment_eq (coordinate_hasLaw N i) G K C)
  have hQm : MemLp Q 2 (gaussianProduct (Fin (N+1))) :=
    (memLp_finsetSum Finset.univ (fun (i : Fin N) _ ↦
      predictableCenteredSquare_memLp (j := (i:ℕ)) (hHm i) (hHb i))).const_mul (δ/2)
  have hRm : Measurable R := by
    dsimp only [R, Q]
    exact ((hUm N le_rfl).sub (hUm 0 (Nat.zero_le _))).sub (Finset.measurable_fun_sum _ (fun i _ ↦
      ((hAm i).const_mul _).mul (measurable_coordinate N i))) |>.sub
        ((Finset.measurable_fun_sum _ (fun i _ ↦
          (hHm i).mul (((measurable_coordinate N i).pow_const 2).sub measurable_const))).const_mul _)
  have hRbound (z : Fin (N+1) → ℝ) :
      |R z|≤(δ*Real.sqrt δ)*(∑ i, P i z)+δ*K*(Γ N-Γ 0) := by
    have hb := sum_local_residual_bound (U := fun j ↦ U j z)
      (V := fun i ↦ Real.sqrt δ*A i z*coordinate N i z)
      (W := fun i ↦ (δ/2)*H i z*((coordinate N i z)^2-1))
      (P := fun i ↦ P i z) (Γ := Γ) (fun i ↦ hloc i z)
    simpa only [R, Q, P, mul_assoc, Finset.mul_sum] using hb
  have hβ : 0≤δ*K*(Γ N-Γ 0) := mul_nonneg (mul_nonneg hδ hK) (sub_nonneg.mpr hΓ)
  have hRmem := finite_envelope_memLp (by positivity : 0≤δ*Real.sqrt δ) hβ hPm hPpos
    hRm.aestronglyMeasurable hRbound
  have hRb := finite_envelope_L2_bound (by positivity : 0≤δ*Real.sqrt δ) hβ hPm hPpos hPval
    hRm.aestronglyMeasurable hRbound
  have hQb := predictableCenteredSquare_sum_bound (δ := δ) hK hHm hHp hHb
  have heq (z : Fin (N+1) → ℝ) : (U N z-U 0 z-∑ i : Fin N, Real.sqrt δ*A i z*coordinate N i z)=
      R z+Q z := by dsimp only [R]; ring
  simp_rw [heq]
  have hb := integral_square_add_le hRmem hQm
  simp only [Fintype.card_fin] at hRb
  dsimp only [Q] at hb
  nlinarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ThirdOrderRemainderBound
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue

lemma third_order_remainder_bound {f : ℝ → ℝ} {K : ℝ}
    (hf : ContDiff ℝ 3 f) (hK : 0≤K)
    (hbound : ∀ x, |iteratedDeriv 3 f x|≤K) (x d : ℝ) :
    |f (x+d)-f x-deriv f x*d-(1/2 : ℝ)*deriv (deriv f) x*d^2| ≤ K*|d|^3 := by
  by_cases hd : d=0
  · simp [hd]
  have hne : x ≠ x+d := by
    intro hx
    apply hd
    linarith
  have hu := uniqueDiffOn_uIcc hne
  have hmem : x ∈ uIcc x (x+d) := left_mem_uIcc
  have h1 : iteratedDerivWithin 1 f (uIcc x (x+d)) x = deriv f x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      iteratedDeriv_one]
  have h2 : iteratedDerivWithin 2 f (uIcc x (x+d)) x = deriv (deriv f) x := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num)).contDiffAt hmem,
      iteratedDeriv_succ, iteratedDeriv_one]
  have ht : taylorWithinEval f 2 (uIcc x (x+d)) x (x+d) =
      f x+deriv f x*d+(1/2 : ℝ)*deriv (deriv f) x*d^2 := by
    rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
    rw [h1, h2]
    norm_num
    ring
  obtain ⟨y,_,hy⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 2) hne hf.contDiffOn
  rw [ht] at hy
  have heq : f (x+d)-f x-deriv f x*d-(1/2 : ℝ)*deriv (deriv f) x*d^2 =
      iteratedDeriv 3 f y*d^3/6 := by
    norm_num at hy
    linarith
  rw [heq, abs_div, abs_mul, abs_pow]
  norm_num
  have hh : |iteratedDeriv 3 f y| *|d|^3 ≤ K*|d|^3 :=
    mul_le_mul_of_nonneg_right (hbound y) (by positivity)
  have hp : 0≤K*|d|^3 := by positivity
  linarith

lemma gradient_generator_quadrature {γ : ℝ → ℝ} {b p : ℝ → ℝ → ℝ}
    {t δ x y G K L : ℝ} (hδ : 0 ≤ δ) (hG : 0 ≤ G) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0 ≤ γ t) (hγG : γ t ≤ G)
    (hp : ∀ s ∈ Icc t (t+δ), |p s y| ≤ K)
    (hbLip : ∀ s ∈ Icc t (t+δ), |b s y-b t x| ≤ L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), |p s y-p t x| ≤ L*(|s-t|+|y-x|))
    (hbint : IntervalIntegrable (fun s ↦ b s y) volume t (t+δ))
    (hpint : IntervalIntegrable (fun s ↦ γ s*p s y) volume t (t+δ)) :
    |(∫ s in t..(t+δ), (1/2 : ℝ)*b s y+γ s*p s y) -
        δ*((1/2 : ℝ)*b t x+γ t*p t x)| ≤
      δ*((1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t)) := by
  have het : t ∈ Icc t (t+δ) := ⟨le_rfl, by linarith⟩
  have heT : t+δ ∈ Icc t (t+δ) := ⟨by linarith, le_rfl⟩
  have hgap : 0 ≤ γ (t+δ)-γ t := sub_nonneg.mpr (hγ het heT (by linarith))
  have hpw : ∀ s ∈ Icc t (t+δ),
      |((1/2 : ℝ)*b s y+γ s*p s y)-((1/2 : ℝ)*b t x+γ t*p t x)| ≤
      (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t) := by
    intro s hs
    have hst := hγ het hs hs.1
    have hsT := hγ hs heT hs.2
    have hr : |s-t| ≤ δ := by rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]; linarith [hs.2]
    have hb' : |b s y-b t x| ≤ L*(δ+|y-x|) := (hbLip s hs).trans (by gcongr)
    have hp' : |p s y-p t x| ≤ L*(δ+|y-x|) := (hpLip s hs).trans (by gcongr)
    calc
      _ = |((1/2 : ℝ)*(b s y-b t x)+γ t*(p s y-p t x))+(γ s-γ t)*p s y| := by
        congr 1; ring
      _ ≤ |(1/2 : ℝ)*(b s y-b t x)|+|γ t*(p s y-p t x)|+|(γ s-γ t)*p s y| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = (1/2 : ℝ)*|b s y-b t x|+γ t*|p s y-p t x|+(γ s-γ t)*|p s y| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hγ0,
          abs_of_nonneg (sub_nonneg.mpr hst)]
        norm_num
      _ ≤ (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t) := by
        calc
          _ ≤ (1/2 : ℝ)*(L*(δ+|y-x|))+G*(L*(δ+|y-x|))+(γ (t+δ)-γ t)*K := by
            apply add_le_add
            · gcongr
            · calc
                _ ≤ (γ s-γ t)*K :=
                  mul_le_mul_of_nonneg_left (hp s hs) (sub_nonneg.mpr hst)
                _ ≤ _ := mul_le_mul_of_nonneg_right (sub_le_sub_right hsT _) hK
          _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := t) (b := t+δ)
    (f := fun s ↦ ((1/2 : ℝ)*b s y+γ s*p s y)-((1/2 : ℝ)*b t x+γ t*p t x))
    (C := (1/2+G)*L*(δ+|y-x|)+K*(γ (t+δ)-γ t)) (fun s hs ↦ by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le (by linarith : t≤t+δ)] at hs
      exact hpw s ⟨hs.1.le, hs.2⟩)
  rw [intervalIntegral.integral_sub ((hbint.const_mul _).add hpint) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, Real.norm_eq_abs,
    show t+δ-t=δ by ring, abs_of_nonneg hδ] at hi
  simpa only [mul_comm δ] using hi

lemma euler_cubic_remainder {δ G K C D c v a b vsp vend z : ℝ}
    (hδ : 0≤δ) (hδ1 : δ≤1) (hG : 0≤G) (hK : 0≤K) (hC : 0≤C)
    (hc : |c|≤G) (hv : |v|≤1) (hb : |b|≤K)
    (hsp : |vsp-v-a*(Real.sqrt δ*z+δ*c*v)-
      (1/2 : ℝ)*b*(Real.sqrt δ*z+δ*c*v)^2| ≤ K*|Real.sqrt δ*z+δ*c*v|^3)
    (htm : |vend-vsp+δ*((1/2 : ℝ)*b+c*v*a)| ≤
      δ*(C*(δ+|Real.sqrt δ*z+δ*c*v|)+K*D)) :
    |vend-v-a*Real.sqrt δ*z-(1/2 : ℝ)*δ*b*(z^2-1)| ≤
      δ*Real.sqrt δ*(K*(|z|+G)^3+C*(1+|z|+G)+K*G*(|z|+G/2))+δ*K*D := by
  let η := Real.sqrt δ
  let d := η*z+δ*c*v
  have hη : 0≤η := Real.sqrt_nonneg _
  have hηsq : η^2=δ := Real.sq_sqrt hδ
  have hη1 : η≤1 := (Real.sqrt_le_one).2 hδ1
  have hδη : δ≤η := by nlinarith
  have hcv : |c*v|≤G := by
    rw [abs_mul]
    calc |c| *|v| ≤ G*1 := mul_le_mul hc hv (abs_nonneg _) hG
         _ = G := mul_one _
  have hdcv : |δ*c*v|≤δ*G := by
    rw [mul_assoc δ, abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left hcv hδ
  have hd : |d|≤η*(|z|+G) := by
    calc
      |d| ≤ |η*z|+|δ*c*v| := abs_add_le _ _
      _ ≤ η*|z|+δ*G := by rw [abs_mul, abs_of_nonneg hη]; gcongr
      _ ≤ η*(|z|+G) := by nlinarith
  have hcube : K*|d|^3 ≤ δ*η*(K*(|z|+G)^3) := by
    calc
      _ ≤ K*(η*(|z|+G))^3 := by gcongr
      _ = _ := by rw [← hηsq]; ring
  have htbound : δ*(C*(δ+|d|)+K*D) ≤ δ*η*(C*(1+|z|+G))+δ*K*D := by
    have hh : δ+|d| ≤ η*(1+|z|+G) := by nlinarith
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hδ hC)
    nlinarith
  have hcross : |(1/2 : ℝ)*b*(d^2-δ*z^2)| ≤ δ*η*(K*G*(|z|+G/2)) := by
    have heq : d^2-δ*z^2 = (δ*c*v)*(2*η*z+δ*c*v) := by
      dsimp only [d]
      rw [← hηsq]
      ring
    have hsum : |2*η*z+δ*c*v| ≤ η*(2*|z|+G) := by
      calc
        _ ≤ |2*η*z|+|δ*c*v| := abs_add_le _ _
        _ ≤ 2*η*|z|+δ*G := by
          rw [abs_mul (2*η), abs_of_nonneg (by positivity : 0≤2*η)]
          gcongr
        _ ≤ η*(2*|z|+G) := by nlinarith
    rw [heq, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ)≤1/2)]
    calc
      _ ≤ (1/2 : ℝ)*K*((δ*G)*(η*(2*|z|+G))) := by gcongr
      _ = _ := by ring
  have heq : vend-v-a*η*z-(1/2 : ℝ)*δ*b*(z^2-1) =
      (vsp-v-a*d-(1/2 : ℝ)*b*d^2)+(vend-vsp+δ*((1/2 : ℝ)*b+c*v*a))+
        (1/2 : ℝ)*b*(d^2-δ*z^2) := by dsimp only [d]; ring
  change |vend-v-a*η*z-(1/2 : ℝ)*δ*b*(z^2-1)| ≤ _
  rw [heq]
  calc
    _ ≤ |vsp-v-a*d-(1/2 : ℝ)*b*d^2|+|vend-vsp+δ*((1/2 : ℝ)*b+c*v*a)|+
        |(1/2 : ℝ)*b*(d^2-δ*z^2)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ K*|d|^3+δ*(C*(δ+|d|)+K*D)+δ*η*(K*G*(|z|+G/2)) := by gcongr
    _ ≤ δ*η*(K*(|z|+G)^3+C*(1+|z|+G)+K*G*(|z|+G/2))+δ*K*D := by linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientStrip
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma mesh_mem_strip_ito {δ T : ℝ} {N j : ℕ} (hδ : 0≤δ)
    (horizon : (N : ℝ)*δ=T) (hj : j≤N) : (j : ℝ)*δ∈Icc (0 : ℝ) T := by
  constructor
  · positivity
  · rw [← horizon]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hδ

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_GradientErrorConstant
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma gaussian_mesh_bound_linear {δ T n K V M J : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hmesh : n*δ=T) :
    2*((δ/2)^2*n*K^2*V)+4*(δ*Real.sqrt δ)^2*n^2*M+4*(δ*K*J)^2 ≤
      δ*(T/2*K^2*V+4*T^2*M+4*K^2*J^2) := by
  have hfirst : 2*((δ/2)^2*n*K^2*V)=δ*(T/2*K^2*V) := by rw [← hmesh]; ring
  have hsecond : 4*(δ*Real.sqrt δ)^2*n^2*M=δ*(4*T^2*M) := by
    rw [mul_pow, Real.sq_sqrt hδ, ← hmesh]
    ring
  have hd2 : δ^2≤δ := by nlinarith
  have hthird := mul_le_mul_of_nonneg_right hd2 (show 0≤4*K^2*J^2 by positivity)
  rw [hfirst, hsecond]
  nlinarith

end SKValue

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_MeshRaw
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma mesh_time_mem {T : ℝ} (hT : 0≤T) {N j : ℕ} (hN : 0<N) (hj : j≤N) :
    meshTime T N j∈Icc (0 : ℝ) T := by
  apply mesh_mem_strip_ito (δ := stepSize T N) (div_nonneg hT (Nat.cast_nonneg N)) _ hj
  have hNr : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold stepSize
  field_simp

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_AestronglyMeasurableInitialMax
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma mesh_time_mem_total {T : ℝ} (hT : 0≤T) {N j : ℕ} (hj : j≤N) :
    meshTime T N j∈Icc (0 : ℝ) T := by
  by_cases hN : N=0
  · subst N
    simp only [meshTime, stepSize, Nat.cast_zero, div_zero, mul_zero]
    exact ⟨le_rfl,hT⟩
  · exact mesh_time_mem hT (Nat.pos_of_ne_zero hN) hj

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_BrownianCoordinates
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

lemma brownian_grid_variance (δ : ℝ≥0) (j : ℕ) :
    nndist (↑(((j+1 : ℕ) : ℝ≥0)*δ) : ℝ) (↑((j : ℝ≥0)*δ) : ℝ) = δ := by
  apply NNReal.coe_injective
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  rw [Real.dist_eq]
  have heq : ((j : ℝ)+1)*(δ : ℝ)-(j : ℝ)*δ=δ := by ring
  rw [heq]
  exact abs_of_nonneg δ.property

lemma brownian_coordinate_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {δ : ℝ≥0} (hδ : 0 < δ)
    (n : ℕ) (j : Fin n) :
    HasLaw (fun ω ↦ brownianCoordinates B δ n ω j) standardGaussian μ := by
  have h := gaussianReal_div_const (hB.hasLaw_sub (((j : ℕ)+1 : ℕ)*δ) ((j : ℕ)*δ))
    (Real.sqrt δ)
  erw [brownian_grid_variance δ (j : ℕ)] at h
  have hs : (⟨(Real.sqrt δ)^2, sq_nonneg _⟩ : ℝ≥0) = δ := by
    apply NNReal.coe_injective
    exact Real.sq_sqrt δ.property
  have heq : NNReal.mk ((Real.sqrt (δ : ℝ))^2) (sq_nonneg _) = δ := hs
  rw [heq, div_self (ne_of_gt hδ)] at h
  simpa only [brownianCoordinates, standardGaussian, zero_div, Pi.sub_apply] using h

lemma brownian_coordinates_independent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (δ : ℝ≥0) (n : ℕ) :
    iIndepFun (fun j (ω : Ω) ↦ brownianCoordinates B δ n ω j) μ := by
  have hmono : Monotone (fun j : Fin (n+1) ↦ (j : ℕ)*δ) := by
    intro i j hij
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have h := (hB.hasIndepIncrements n (fun j : Fin (n+1) ↦ (j : ℕ)*δ) hmono).comp
    (fun (_ : Fin n) (x : ℝ) ↦ x / Real.sqrt δ) (fun _ ↦ measurable_id.div_const _)
  simpa only [brownianCoordinates, Fin.val_succ, Fin.val_castSucc, Function.comp_def] using h

lemma brownian_coordinates_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {δ : ℝ≥0} (hδ : 0 < δ)
    (n : ℕ) :
    HasLaw (brownianCoordinates B δ n) (gaussianProduct (Fin n)) μ := by
  exact iIndepFun.hasLaw_pi (fun j ↦ brownian_coordinate_hasLaw hB hδ n j)
    (brownian_coordinates_independent hB δ n)

lemma brownian_coordinate_exact {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {δ : ℝ≥0}
    (hδ : 0 < δ) (n : ℕ) (ω : Ω) (j : Fin n) :
    Real.sqrt δ * brownianCoordinates B δ n ω j =
      B (((j : ℕ)+1 : ℕ)*δ) ω-B ((j : ℕ)*δ) ω := by
  have hs : Real.sqrt (δ : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hδ)
  simp only [brownianCoordinates]
  field_simp

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_CoupledCoordinates
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma coupledCoordinates_hasLaw {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) : HasLaw (coupledCoordinates T N B) (gaussianProduct (Fin (N+1))) μ := by
  apply brownian_coordinates_hasLaw hB
  exact Real.toNNReal_pos.mpr (div_pos hT (Nat.cast_pos.mpr hN))

lemma coupled_euler_zero {Ω : Type*} (T : ℝ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (N : ℕ) (ω : Ω) : coupledEuler T γ u B N 0 ω=0 := by
  simp only [coupledEuler, euler, ite_self]

lemma coupled_coordinate_exact {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ} (hT : 0<T)
    {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j<N+1) (ω : Ω) :
    Real.sqrt (T/N)*coordinate N j (coupledCoordinates T N B ω)=
      B (Real.toNNReal (((j+1 : ℕ) : ℝ)*(T/N))) ω-B (Real.toNNReal ((j : ℝ)*(T/N))) ω := by
  have hδ : 0<T/(N : ℝ) := div_pos hT (Nat.cast_pos.mpr hN)
  rw [coordinate_eq_apply hj]
  simp only [Real.toNNReal_mul (Nat.cast_nonneg (j+1)), Real.toNNReal_mul (Nat.cast_nonneg j),
    Real.toNNReal_natCast]
  simpa only [coupledCoordinates, Real.coe_toNNReal _ hδ.le, Fin.val_mk] using
    brownian_coordinate_exact B (Real.toNNReal_pos.mpr hδ) (N+1) ω ⟨j,hj⟩

lemma coupled_euler_step {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) {T : ℝ} (hT : 0<T)
    (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) {N : ℕ} (hN : 0<N) {j : ℕ} (hj : j<N) (ω : Ω) :
    coupledEuler T γ u B N (j+1) ω = coupledEuler T γ u B N j ω +
      B (Real.toNNReal (((j+1 : ℕ) : ℝ)*(T/N))) ω-B (Real.toNNReal ((j : ℝ)*(T/N))) ω+
      (T/N)*γ ((j : ℝ)*(T/N))*u ((j : ℝ)*(T/N)) (coupledEuler T γ u B N j ω) := by
  simp only [coupledEuler, ite_eq_right (Nat.ne_of_gt hN), euler, stepSize, meshTime]
  rw [coupled_coordinate_exact B hT hN (by omega) ω]
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_RawIncrement
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma rawIncrement_memLp {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H)
    (hH : MemLp H 2 (gaussianProduct (Fin (N+1)))) :
    MemLp (rawIncrement H j) 2 (gaussianProduct (Fin (N+1))) := by
  apply (memLp_two_iff_integrable_sq
    (hm.aestronglyMeasurable.mul (measurable_coordinate N j).aestronglyMeasurable)).2
  have hind := (hp.independent hj hm).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hi := hind.integrable_mul hH.integrable_sq
      (gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).integrable_sq
  change Integrable (fun z ↦ (H z)^2 * (coordinate N j z)^2) _ at hi
  simpa only [rawIncrement, Pi.mul_apply, mul_pow] using hi

lemma rawIncrement_mean {N j : ℕ} {H : (Fin (N+1) → ℝ) → ℝ}
    (hj : j<N+1) (hm : Measurable H) (hp : DependsBefore j H) :
    (∫ z, rawIncrement H j z ∂gaussianProduct (Fin (N+1))) = 0 := by
  have hi := (hp.independent hj hm).integral_mul_eq_mul_integral
    hm.aestronglyMeasurable (measurable_coordinate N j).aestronglyMeasurable
  change (∫ z, H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) = _ at hi
  change (∫ z, H z * coordinate N j z ∂gaussianProduct (Fin (N+1))) = 0
  rw [hi, gaussian_mean (coordinate_hasLaw N j), mul_zero]

lemma finiteRaw_memLp {N : ℕ} {δ : ℝ} {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ i, Measurable (H i)) (hp : ∀ i : Fin N, DependsBefore (i : ℕ) (H i))
    (hH : ∀ i, MemLp (H i) 2 (gaussianProduct (Fin (N+1)))) :
    MemLp (finiteRawMartingale δ H) 2 (gaussianProduct (Fin (N+1))) := by
  have hc := memLp_linearCombination
    (fun i : Fin N ↦ rawIncrement_memLp (by omega) (hm i) (hp i) (hH i)) (fun _ ↦ Real.sqrt δ)
  change MemLp (fun z ↦ ∑ i : Fin N, Real.sqrt δ * H i z * coordinate N i z) 2 _
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [rawIncrement]
  ring

end SKValue
end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_ValueEulerOneStep
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma value_euler_one_step {V : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {t δ x z G K L : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hG : 0≤G) (hK : 0≤K) (hL : 0≤L)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0≤γ t) (hγG : γ t≤G)
    (hu : |deriv (V t) x|≤1) (hsmooth : ContDiff ℝ 3 (V t))
    (ha : |deriv (deriv (V t)) x|≤K)
    (hthird : ∀ y, |iteratedDeriv 3 (V t) y|≤K)
    (hp : ∀ s ∈ Icc t (t+δ), ∀ y, |(1/2 : ℝ)*(deriv (V s) y)^2|≤K)
    (haLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |deriv (deriv (V s)) y-deriv (deriv (V t)) x|≤L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |(1/2 : ℝ)*(deriv (V s) y)^2-(1/2 : ℝ)*(deriv (V t) x)^2|≤L*(|s-t|+|y-x|))
    (haint : ∀ y, IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ))
    (hpint : ∀ y, IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) y)^2)) volume t (t+δ))
    (hPDE : ∀ y, V (t+δ) y-V t y =
      -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) y+γ s*((1/2 : ℝ)*(deriv (V s) y)^2))) :
    let d := Real.sqrt δ*z+δ*γ t*deriv (V t) x
    |V (t+δ) (x+d)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)-
      (1/2 : ℝ)*δ*γ t*(deriv (V t) x)^2| ≤
    δ*Real.sqrt δ*(K*(|z|+G)^3+(1/2+G)*L*(1+|z|+G)+K*G*(|z|+G/2))+
      δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*γ t*deriv (V t) x
  have htm := gradient_generator_quadrature
    (b := fun s y ↦ deriv (deriv (V s)) y)
    (p := fun s y ↦ (1/2 : ℝ)*(deriv (V s) y)^2) (y := x+d)
    hδ hG hK hL hγ hγ0 hγG
    (fun s hs ↦ hp s hs _) (fun s hs ↦ haLip s hs _) (fun s hs ↦ hpLip s hs _)
    (haint _) (hpint _)
  have ht : |(V (t+δ) (x+d)-V t x+deriv (V t) x-
        (1/2 : ℝ)*δ*γ t*(deriv (V t) x)^2)-
      (V t (x+d)-V t x+deriv (V t) x)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*deriv (V t) x*deriv (V t) x)| ≤
      δ*(((1/2 : ℝ)+G)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq : (V (t+δ) (x+d)-V t x+deriv (V t) x-
        (1/2 : ℝ)*δ*γ t*(deriv (V t) x)^2)-
      (V t (x+d)-V t x+deriv (V t) x)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*deriv (V t) x*deriv (V t) x) =
      (V (t+δ) (x+d)-V t (x+d))+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) := by ring
    rw [heq,hPDE]
    rw [show -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
        γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))+
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) =
        -((∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
        γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))-
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2))) by ring,
      abs_neg]
    simpa only [add_sub_cancel_left] using htm
  have hs : |(V t (x+d)-V t x+deriv (V t) x)-deriv (V t) x-
      deriv (V t) x*d-(1/2 : ℝ)*deriv (deriv (V t)) x*d^2| ≤ K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound hsmooth hK hthird x d
  have hh := euler_cubic_remainder hδ hδ1 hG hK (by positivity : 0≤(1/2+G)*L)
    (by rwa [abs_of_nonneg hγ0]) hu ha hs ht
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  dsimp only [d]
  ring

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_ValueStrip
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma valueMeshCompensated_step (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (j : ℕ) (z : Fin (N+1) → ℝ) :
    valueMeshCompensated T N γ V (j+1) z-valueMeshCompensated T N γ V j z =
    V (meshTime T N (j+1)) (euler T N γ (fun t ↦ deriv (V t)) z (j+1))-
    V (meshTime T N j) (euler T N γ (fun t ↦ deriv (V t)) z j)-
    (stepSize T N/2)*γ (meshTime T N j)*
      (deriv (V (meshTime T N j)) (euler T N γ (fun t ↦ deriv (V t)) z j))^2 := by
  simp only [valueMeshCompensated, valueMeshEnergy, Finset.sum_range_succ]
  ring

lemma valueMeshCompensated_zero (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (V : ℝ → ℝ → ℝ)
    (z : Fin (N+1) → ℝ) : valueMeshCompensated T N γ V 0 z=V 0 0 := by
  simp [valueMeshCompensated, valueMeshEnergy, meshTime, euler]

lemma valueMeshError_bound {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    valueMeshError T N γ V ≤
      2*((stepSize T N/2)^2*(N : ℝ)*K^2*gaussianSquareVariance)+
      4*(stepSize T N*Real.sqrt (stepSize T N))^2*(N : ℝ)^2*
        cubicEnvelopeMoment (γ T) K ((1/2+γ T)*L)+
      4*(stepSize T N*K*(γ T-γ 0))^2 := by
  let u := fun t ↦ deriv (V t)
  let δ := stepSize T N
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0≤δ := by dsimp [δ, stepSize]; positivity
  have hδ1 : δ≤1 := by
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    dsimp [δ, stepSize]
    exact (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hmesh : (N : ℝ)*δ=T := by dsimp [δ, stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ hmesh hj
  have ht0 : (0 : ℝ)∈Icc (0 : ℝ) T := ⟨le_rfl,hT.le⟩
  have htT : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hG : 0≤γ T := h.gamma_nonneg T htT
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+δ := by
    dsimp [meshTime, δ]; push_cast; ring
  have hlast : meshTime T N N=T := hmesh
  have hzero : meshTime T N 0=0 := by simp only [meshTime, Nat.cast_zero, zero_mul]
  have huc (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : Continuous (u t) :=
    (h.smooth t ht).continuous_deriv (by norm_num)
  have hY (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ euler T N γ u z j) :=
    measurable_euler T N γ u (fun k hk ↦ (huc _ (htime k hk.le)).measurable) j hj
  have hAm (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) :=
    (huc _ (htime j hj)).measurable.comp (hY j hj)
  have hUm (j : ℕ) (hj : j≤N) : Measurable (valueMeshCompensated T N γ V j) := by
    apply Measurable.sub ((h.smooth _ (htime j hj)).continuous.measurable.comp (hY j hj))
    apply Finset.measurable_fun_sum
    intro i hi
    exact ((hAm i (le_trans (Finset.mem_range.mp hi).le hj)).pow_const 2).const_mul _
  have hHm (i : Fin N) : Measurable (fun z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i)) := by
    have hc := (h.smooth _ (htime i i.isLt.le)).continuous_iteratedDeriv 2 (by norm_num)
    have hc' : Continuous (deriv (u (meshTime T N i))) := by
      simpa only [u, show 2=1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hc
    exact hc'.measurable.comp (hY i i.isLt.le)
  have hloc (i : Fin N) (z : Fin (N+1) → ℝ) :
      |valueMeshCompensated T N γ V (i+1) z-valueMeshCompensated T N γ V i z-
        Real.sqrt δ*u (meshTime T N i) (euler T N γ u z i)*coordinate N i z-
        (δ/2)*deriv (u (meshTime T N i)) (euler T N γ u z i)*((coordinate N i z)^2-1)| ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (coordinate N i z)+
        δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [← hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hbint (x : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (V s)) x) volume t (t+δ) := by
      apply (h.second_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hpint (x : ℝ) : IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) x)^2)) volume t (t+δ) := by
      apply (h.product_integrable x).mono_set
      rw [uIcc_of_le hT.le]
      exact uIcc_subset_Icc ht ht'
    have hh := value_euler_one_step (x := euler T N γ u z i) (z := coordinate N i z)
      hδ hδ1 hG h.K_nonneg h.L_nonneg (h.gamma_mono.mono hsub) (h.gamma_nonneg t ht)
      (h.gamma_mono ht htT ht.2) (h.bounded t ht _) (h.smooth t ht)
      (h.second_bound t ht _) (h.third_bound t ht)
      (fun s hs ↦ h.product_bound s (hsub hs))
      (fun s hs y ↦ h.second_lipschitz t ht s (hsub hs) _ y)
      (fun s hs y ↦ h.product_lipschitz t ht s (hsub hs) _ y)
      hbint hpint (h.pde t ht (t+δ) ht')
    dsimp only at hh
    rw [valueMeshCompensated_step]
    convert hh using 1 <;> simp only [hsucc, euler, cubicEnvelope, t, δ, u]
    all_goals congr 1
    all_goals ring_nf
  have hb := discrete_gradient_residual_L2 (δ := δ) hδ hG h.K_nonneg
    (mul_nonneg (by positivity) h.L_nonneg : 0≤(1/2+γ T)*L)
    (Γ := fun j ↦ γ (meshTime T N j))
    (U := valueMeshCompensated T N γ V)
    (A := fun i z ↦ u (meshTime T N i) (euler T N γ u z i))
    (H := fun i z ↦ deriv (u (meshTime T N i)) (euler T N γ u z i))
    (by simpa only [hlast, hzero] using h.gamma_mono ht0 htT hT.le)
    hUm (fun i ↦ hAm i i.isLt.le) hHm
    (fun i ↦ eulerCoefficient_dependsBefore T i.isLt.le γ u (fun t ↦ deriv (u t)))
    (fun i z ↦ h.second_bound _ (htime i i.isLt.le) _) hloc
  simpa only [valueMeshError, valueMeshCompensated_zero, hlast, hzero, u, δ] using hb

lemma valueMeshError_bound_linear {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    valueMeshError T N γ V ≤ stepSize T N*gradientErrorConstant T K L γ := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hδ : 0≤ stepSize T N := div_nonneg hT.le hNr.le
  have hδ1 : stepSize T N≤1 := (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hm : (N:ℝ)*stepSize T N=T := by unfold stepSize; field_simp
  exact (valueMeshError_bound hT hT1 h hN).trans (gaussian_mesh_bound_linear hδ hδ1 hm)

lemma valueMeshError_tendsto_zero {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) :
    Tendsto (fun N ↦ valueMeshError T N γ V) atTop (𝓝 0) := by
  have hbound : ∀ᶠ N in atTop,
      valueMeshError T N γ V ≤ stepSize T N*gradientErrorConstant T K L γ := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact valueMeshError_bound_linear hT hT1 h hN
  have hlim : Tendsto (fun N ↦ stepSize T N*gradientErrorConstant T K L γ) atTop (𝓝 0) := by
    simpa only [stepSize, zero_mul] using
      (tendsto_const_div_atTop_nhds_zero_nat T).mul_const (gradientErrorConstant T K L γ)
  exact squeeze_zero' (Eventually.of_forall (fun N ↦ integral_nonneg (fun _ ↦ sq_nonneg _))) hbound hlim

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_EulerMemLp
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators

lemma euler_memLp (T : ℝ) (N : ℕ) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (huM : ∀ j<N, Measurable (u (meshTime T N j)))
    (huB : ∀ j<N, ∀ x, |u (meshTime T N j) x|≤1) :
    ∀ j≤N, MemLp (fun z ↦ euler T N γ u z j) 2 (gaussianProduct (Fin (N+1))) := by
  intro j
  induction j with
  | zero => intro _; exact memLp_const (0 : ℝ)
  | succ j ih =>
    intro hj
    have hlt : j<N := by omega
    have hU : MemLp (fun z ↦ u (meshTime T N j) (euler T N γ u z j)) 2
        (gaussianProduct (Fin (N+1))) :=
      MemLp.of_bound ((huM j hlt).comp (measurable_euler T N γ u huM j hlt.le)).aestronglyMeasurable 1
        (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using huB j hlt _))
    exact ((ih hlt.le).add ((gaussian_memLp (coordinate_hasLaw N j) 2 (by norm_num)).const_mul _)).add
      (hU.const_mul (stepSize T N*γ (meshTime T N j)))

lemma ValueStrip.value_lipschitz {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : ValueStrip T γ V K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    LipschitzWith 1 (V t) := by
  apply lipschitzWith_of_nnnorm_deriv_le ((h.smooth t ht).differentiable (by norm_num))
  intro x
  exact_mod_cast (show ‖deriv (V t) x‖≤(1 : ℝ) by simpa only [Real.norm_eq_abs] using h.bounded t ht x)

lemma ValueStrip.value_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ} (h : ValueStrip T γ V K L)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) T) {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    MemLp (fun ω ↦ V t (Y ω)) 2 μ := by
  have hl : LipschitzWith 1 (fun x ↦ V t x - V t 0) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_sub_right] using (h.value_lipschitz ht).dist_le_mul x y
  have hh := hl.comp_memLp (by simp) hY
  convert hh.add (memLp_const (V t 0)) using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  simp

lemma value_mesh_expectation_error {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    |(∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N) ∂gaussianProduct (Fin (N+1)))-V 0 0-
      (∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))| ≤
      Real.sqrt (valueMeshError T N γ V) := by
  let u := fun t ↦ deriv (V t)
  let Y := euler T N γ u
  let μ := gaussianProduct (Fin (N+1))
  let A (i : Fin N) (z : Fin (N+1) → ℝ) := u (meshTime T N i) (Y z i)
  let M (z : Fin (N+1) → ℝ) := ∑ i : Fin N, Real.sqrt (stepSize T N)*A i z*coordinate N i z
  let R (z : Fin (N+1) → ℝ) := valueMeshCompensated T N γ V N z-V 0 0-M z
  have htime (j : ℕ) (hj : j≤N) := mesh_time_mem hT.le hN hj
  have huc (j : ℕ) (hj : j≤N) : Continuous (u (meshTime T N j)) :=
    (h.smooth _ (htime j hj)).continuous_deriv (by norm_num)
  have hY (j : ℕ) (hj : j≤N) : Measurable (fun z ↦ Y z j) :=
    measurable_euler T N γ u (fun i hi ↦ (huc i hi.le).measurable) j hj
  have hAm (i : Fin N) : Measurable (A i) := (huc i i.isLt.le).measurable.comp (hY i i.isLt.le)
  have hAb (i : Fin N) z : |A i z|≤1 := h.bounded _ (htime i i.isLt.le) _
  have hAp (i : Fin N) : DependsBefore i (A i) := eulerCoefficient_dependsBefore T i.isLt.le γ u u
  have hAM (i : Fin N) : MemLp (A i) 2 μ :=
    MemLp.of_bound (hAm i).aestronglyMeasurable 1
      (Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hAb i z))
  have hMm : MemLp M 2 μ := finiteRaw_memLp hAm hAp hAM
  have hMv : (∫ z, M z ∂μ)=0 := by
    have hMi (i : Fin N) : Integrable (fun z ↦ Real.sqrt (stepSize T N)*A i z*coordinate N i z) μ :=
      ((rawIncrement_memLp (by omega : (i : ℕ)<N+1) (hAm i) (hAp i) (hAM i)).const_mul
        (Real.sqrt (stepSize T N))).integrable (by norm_num) |>.congr (by
          filter_upwards [] with z; simp only [rawIncrement]; ring)
    rw [show (∫ z, M z ∂μ)=∑ i : Fin N, ∫ z, Real.sqrt (stepSize T N)*A i z*coordinate N i z ∂μ from
      integral_finsetSum _ (fun i _ ↦ hMi i)]
    have he (i : Fin N) : (∫ z, Real.sqrt (stepSize T N)*A i z*coordinate N i z ∂μ)=0 := by
      simp only [mul_assoc]
      rw [integral_const_mul]
      change Real.sqrt (stepSize T N)*(∫ z, rawIncrement (A i) i z ∂μ)=0
      rw [rawIncrement_mean (by omega) (hAm i) (hAp i),mul_zero]
    simp only [he, Finset.sum_const_zero]
  have hEm : MemLp (valueMeshEnergy T N γ V N) 2 μ := by
    apply memLp_finsetSum
    intro j hj
    have hjN : j<N := Finset.mem_range.mp hj
    apply MemLp.const_mul
    apply MemLp.of_bound (((huc j hjN.le).measurable.comp (hY j hjN.le)).pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_pow, sq_le_one_iff_abs_le_one]
    simpa only [abs_abs, u, Function.comp_apply] using h.bounded _ (htime j hjN.le) (Y z j)
  have hYM : MemLp (fun z ↦ Y z N) 2 μ :=
    euler_memLp T N γ u (fun i hi ↦ (huc i hi.le).measurable)
      (fun i hi x ↦ h.bounded _ (htime i hi.le) x) N le_rfl
  have hVM := h.value_memLp (t := T) ⟨hT.le,le_rfl⟩ hYM
  have hlast : meshTime T N N=T := by
    dsimp only [meshTime, stepSize]
    have hn : (N : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
    field_simp
  have hRM : MemLp R 2 μ := by
    dsimp only [R,valueMeshCompensated]
    rw [hlast]
    exact ((hVM.sub hEm).sub (memLp_const (V 0 0))).sub hMm
  have hRint : (∫ z, R z ∂μ)=
      (∫ z, V T (Y z N) ∂μ)-V 0 0-(∫ z, valueMeshEnergy T N γ V N z ∂μ) := by
    dsimp only [R,valueMeshCompensated]
    rw [hlast]
    have hi₁ := integral_sub (((hVM.sub hEm).sub (memLp_const (V 0 0))).integrable (by norm_num)) (hMm.integrable (by norm_num))
    have hi₂ := integral_sub ((hVM.sub hEm).integrable (by norm_num)) (integrable_const (V 0 0))
    simp only [Pi.sub_apply] at hi₁ hi₂
    change (∫ z, V T (Y z N)-valueMeshEnergy T N γ V N z-V 0 0-M z ∂μ)=_
    rw [hi₁, hi₂]
    rw [integral_sub (hVM.integrable (by norm_num)) (hEm.integrable (by norm_num)),hMv,integral_const]
    simp only [probReal_univ, smul_eq_mul, sub_zero]
    ring
  rw [←hRint]
  exact abs_integral_le_integral_abs.trans (integral_abs_le_sqrt_integral_sq hRM)

lemma value_mesh_expectation_error_tendsto {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) :
    Tendsto (fun N ↦ (∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N)
      ∂gaussianProduct (Fin (N+1)))-V 0 0-
      (∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun N ↦ Real.sqrt (valueMeshError T N γ V))
  · filter_upwards [eventually_gt_atTop 0] with N hN
    simpa only [Real.norm_eq_abs] using value_mesh_expectation_error hT h hN
  · simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp (valueMeshError_tendsto_zero hT hT1 h)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_LipschitzCompMemLpFinite
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

lemma lipschitz_comp_memLp_finite {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {q : ℝ → ℝ} {C : ℝ≥0} (hq : LipschitzWith C q)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ) : MemLp (fun ω ↦ q (Y ω)) 2 μ := by
  have hl : LipschitzWith C (fun x ↦ q x-q 0) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [dist_sub_right] using hq.dist_le_mul x y
  have hh := hl.comp_memLp (by simp) hY
  convert hh.add (memLp_const (q 0)) using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  simp

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Equations_BrownianIncrementIndepPast
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue

lemma brownian_increment_indep_past
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F) :
    IndepFun (fun ω ↦ B t ω-B s ω) F μ := by
  have h := (hB.indepFun_shift s).comp (measurable_pi_apply (t-s)) measurable_id
  simp only [Function.comp_def, id_eq, add_tsub_cancel_of_le hst] at h
  change Indep (MeasurableSpace.comap (fun ω ↦ B t ω-B s ω) inferInstance)
    (MeasurableSpace.comap (fun ω (r : Iic s) ↦ B r ω) inferInstance) μ at h
  change Indep (MeasurableSpace.comap (fun ω ↦ B t ω-B s ω) inferInstance)
    (MeasurableSpace.comap F inferInstance) μ
  apply indep_of_indep_of_le_right h
  rw [←Filtration.natural_eq_comap B hBm s]
  exact hF.measurable.comap_le

lemma brownian_increment_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    (∫ ω, B t ω-B s ω ∂μ)=0 := by
  change (∫ ω, (B t-B s) ω ∂μ)=0
  rw [(hB.hasLaw_sub t s).integral_eq, integral_id_gaussianReal]

lemma brownian_increment_second_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {s t : ℝ≥0} (hst : s≤t) :
    (∫ ω, (B t ω-B s ω)^2 ∂μ)=(t : ℝ)-s := by
  have hv := (hB.hasLaw_sub t s).variance_eq
  rw [variance_id_gaussianReal] at hv
  rw [variance_eq_integral (hB.hasLaw_sub t s).aemeasurable] at hv
  simp only [Pi.sub_apply, brownian_increment_integral hB s t, sub_zero] at hv
  have ht' : (s : ℝ)≤t := by exact_mod_cast hst
  exact hv.trans (show (nndist (t:ℝ) (s:ℝ) : ℝ)=(t:ℝ)-s from by
    change |(t:ℝ)-(s:ℝ)|=(t:ℝ)-s
    exact abs_of_nonneg (sub_nonneg.mpr ht'))

lemma brownian_predictable_increment_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F)
    (hFi : Integrable F μ) : Integrable (fun ω ↦ F ω*(B t ω-B s ω)) μ := by
  exact (brownian_increment_indep_past hB hBm hst hF).symm.integrable_mul hFi
    ((hB.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable (by norm_num))

lemma brownian_predictable_increment_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F) :
    (∫ ω, F ω*(B t ω-B s ω) ∂μ)=0 := by
  have hFm := hF.mono (Filtration.le _ s)
  have h := (brownian_increment_indep_past hB hBm hst hF).symm.integral_mul_eq_mul_integral
    hFm.aestronglyMeasurable ((hBm t).sub (hBm s)).aestronglyMeasurable
  simpa only [Pi.mul_apply, brownian_increment_integral hB s t, mul_zero] using h

lemma brownian_predictable_quadratic_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F)
    (hFi : Integrable F μ) :
    Integrable (fun ω ↦ F ω*((B t ω-B s ω)^2-((t : ℝ)-s))) μ := by
  have h := (brownian_increment_indep_past hB hBm hst hF).comp
    (φ := fun x : ℝ ↦ x^2-((t : ℝ)-s))
    ((measurable_id.pow_const 2).sub measurable_const) measurable_id
  have hi : Integrable (fun ω ↦ (B t ω-B s ω)^2-((t : ℝ)-s)) μ :=
    ((hB.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable_sq).sub (integrable_const _)
  exact h.symm.integrable_mul hFi hi

lemma brownian_predictable_quadratic_mean
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t)) {s t : ℝ≥0} (hst : s≤t)
    {F : Ω → ℝ} (hF : StronglyMeasurable[Filtration.natural B hBm s] F) :
    (∫ ω, F ω*((B t ω-B s ω)^2-((t : ℝ)-s)) ∂μ)=0 := by
  have hFm := hF.mono (Filtration.le _ s)
  have hi : Integrable (fun ω ↦ (B t ω-B s ω)^2) μ :=
    (hB.hasLaw_sub t s).hasGaussianLaw.memLp_two.integrable_sq
  have h0 : (∫ ω, (B t ω-B s ω)^2-((t : ℝ)-s) ∂μ)=0 := by
    rw [integral_sub hi (integrable_const _), brownian_increment_second_moment hB hst]
    simp
  have h := (brownian_increment_indep_past hB hBm hst hF).comp
    (φ := fun x : ℝ ↦ x^2-((t : ℝ)-s))
    ((measurable_id.pow_const 2).sub measurable_const) measurable_id
  have hQm : AEStronglyMeasurable (fun ω ↦ (B t ω-B s ω)^2-((t : ℝ)-s)) μ :=
    (((hBm t).sub (hBm s)).pow 2 |>.sub stronglyMeasurable_const).aestronglyMeasurable
  have heq := h.symm.integral_mul_eq_mul_integral hFm.aestronglyMeasurable hQm
  simpa only [Function.comp_def, id_eq, Pi.mul_apply, h0, mul_zero] using heq

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
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlStability
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

lemma controlAccum_L1_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) (n : ℕ) (ω : Ω) :
    |controlAccum γ α n T ω|≤∫ s in (0 : ℝ)..T, |γ s| := by
  have hint := controlAccum_integrand_intervalIntegrable hα hαb hγ hi hT n ω
  apply (intervalIntegral.abs_integral_le_integral_abs hT).trans
  apply intervalIntegral.integral_mono_on hT hint.abs hi.abs
  intro s hs
  rw [abs_mul,abs_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hαb _ _)) (abs_nonneg _)).trans_eq (mul_one _)

lemma controlAccum_memLp_of_interval {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Filtration ℝ≥0 m}
    {α : ℝ≥0 → Ω → ℝ} {γ : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (controlAccum γ α n T) p μ := by
  apply MemLp.of_bound ((controlAccum_measurable hα hγ n hT).mono (f.le _) le_rfl).aestronglyMeasurable
    (∫ s in (0 : ℝ)..T, |γ s|)
  exact Eventually.of_forall (fun ω ↦ (Real.norm_eq_abs _).trans_le (controlAccum_L1_bound hα hαb hγ hi hT n ω))

lemma controlAccum_sub {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ η : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T)
    (hT : 0≤T) (n : ℕ) (ω : Ω) :
    controlAccum γ α n T ω-controlAccum η α n T ω=controlAccum (fun s ↦ γ s-η s) α n T ω := by
  have h1 := controlAccum_integrand_intervalIntegrable hα hαb hγ hiγ hT n ω
  have h2 := controlAccum_integrand_intervalIntegrable hα hαb hη hiη hT n ω
  simp only [controlAccum,sub_mul,intervalIntegral.integral_sub h1 h2]

lemma controlAccum_difference_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {α : ℝ≥0 → Ω → ℝ} {γ η : ℝ → ℝ} {T : ℝ}
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T)
    (hT : 0≤T) (n : ℕ) (ω : Ω) :
    |controlAccum γ α n T ω-controlAccum η α n T ω|≤∫ s in (0 : ℝ)..T, |γ s-η s| := by
  rw [controlAccum_sub hα hαb hγ hη hiγ hiη hT]
  exact controlAccum_L1_bound hα hαb (hγ.sub hη) (hiγ.sub hiη) hT n ω

lemma elapsedPayoff_integrable {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Filtration ℝ≥0 m}
    {α : ℝ≥0 → Ω → ℝ} {ψ γ : ℝ → ℝ} {T x : ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ)
    (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) :
    Integrable (fun ω ↦ ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω) μ := by
  have h1 := controlAccum_memLp_of_interval (μ := μ) hα hαb hγ hi hT 1 2
  have h2 := controlAccum_memLp_of_interval (μ := μ) hα hαb hγ hi hT 2 2
  have hs := lipschitz_comp_memLp_finite hψ (((memLp_const x).add hZ).add h1)
  exact (hs.integrable (by norm_num)).sub ((h2.integrable (by norm_num)).const_mul _)

lemma elapsedPayoff_difference_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Filtration ℝ≥0 m}
    {α : ℝ≥0 → Ω → ℝ} {ψ χ γ η : ℝ → ℝ} {T x ε : ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    (hε : ∀ y, |ψ y-χ y|≤ε) (hα : IsProgressive f α) (hαb : ∀ s ω, |α s ω|≤1)
    (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T) (hT : 0≤T) :
    |elapsedPayoff μ Z ψ γ T x α-elapsedPayoff μ Z χ η T x α|≤
      ε+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s-η s|) := by
  let D := ∫ s in (0 : ℝ)..T, |γ s-η s|
  have hp := elapsedPayoff_integrable hZ hψ hα hαb hγ hiγ hT (x := x)
  have hq := elapsedPayoff_integrable hZ hχ hα hαb hη hiη hT (x := x)
  unfold elapsedPayoff
  rw [←integral_sub hp hq]
  apply (abs_integral_le_integral_abs).trans
  have hb : ∀ ω,
      |(ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω)-
        (χ (x+Z ω+controlAccum η α 1 T ω)-(1/2 : ℝ)*controlAccum η α 2 T ω)|≤ε+(3/2 : ℝ)*D := by
    intro ω
    have h1 := controlAccum_difference_bound hα hαb hγ hη hiγ hiη hT 1 ω
    have h2 := controlAccum_difference_bound hα hαb hγ hη hiγ hiη hT 2 ω
    have hl := hχ.dist_le_mul (x+Z ω+controlAccum γ α 1 T ω) (x+Z ω+controlAccum η α 1 T ω)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul,add_sub_add_left_eq_sub] at hl
    have htri := abs_sub_le (ψ (x+Z ω+controlAccum γ α 1 T ω))
      (χ (x+Z ω+controlAccum γ α 1 T ω)) (χ (x+Z ω+controlAccum η α 1 T ω))
    have he := hε (x+Z ω+controlAccum γ α 1 T ω)
    have hcost : |(1/2 : ℝ)*controlAccum γ α 2 T ω-(1/2 : ℝ)*controlAccum η α 2 T ω|≤(1/2 : ℝ)*D := by
      rw [←mul_sub,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have htri2 := norm_sub_le (ψ (x+Z ω+controlAccum γ α 1 T ω)-χ (x+Z ω+controlAccum η α 1 T ω))
      ((1/2 : ℝ)*controlAccum γ α 2 T ω-(1/2 : ℝ)*controlAccum η α 2 T ω)
    simp only [Real.norm_eq_abs] at htri2
    have heq : (ψ (x+Z ω+controlAccum γ α 1 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω)-
        (χ (x+Z ω+controlAccum η α 1 T ω)-(1/2 : ℝ)*controlAccum η α 2 T ω)=
        (ψ (x+Z ω+controlAccum γ α 1 T ω)-χ (x+Z ω+controlAccum η α 1 T ω))-
        ((1/2 : ℝ)*controlAccum γ α 2 T ω-(1/2 : ℝ)*controlAccum η α 2 T ω) := by ring
    rw [heq]
    dsimp only [D] at *
    linarith
  exact (integral_mono (hp.sub hq).abs (integrable_const _) hb).trans_eq (by simp [D])

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_Verification
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators NNReal ENNReal
namespace SKValue

lemma value_bounded_drift_one_step {V : ℝ → ℝ → ℝ} {γ : ℝ → ℝ}
    {t δ x z r G K L : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hG : 0≤G) (hK : 0≤K) (hL : 0≤L) (hr : |r|≤G)
    (hγ : MonotoneOn γ (Icc t (t+δ))) (hγ0 : 0≤γ t) (hγG : γ t≤G)
    (hsmooth : ContDiff ℝ 3 (V t))
    (ha : |deriv (deriv (V t)) x|≤K)
    (hthird : ∀ y, |iteratedDeriv 3 (V t) y|≤K)
    (hp : ∀ s ∈ Icc t (t+δ), ∀ y, |(1/2 : ℝ)*(deriv (V s) y)^2|≤K)
    (haLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |deriv (deriv (V s)) y-deriv (deriv (V t)) x|≤L*(|s-t|+|y-x|))
    (hpLip : ∀ s ∈ Icc t (t+δ), ∀ y,
      |(1/2 : ℝ)*(deriv (V s) y)^2-(1/2 : ℝ)*(deriv (V t) x)^2|≤L*(|s-t|+|y-x|))
    (haint : ∀ y, IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ))
    (hpint : ∀ y, IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) y)^2)) volume t (t+δ))
    (hPDE : ∀ y, V (t+δ) y-V t y =
      -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) y+γ s*((1/2 : ℝ)*(deriv (V s) y)^2))) :
    let d := Real.sqrt δ*z+δ*r
    |V (t+δ) (x+d)-V t x-deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1)-
      δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2)| ≤
      δ*Real.sqrt δ*cubicEnvelope G K ((1/2+G)*L) z+
        δ*K*(γ (t+δ)-γ t) := by
  dsimp only
  let d := Real.sqrt δ*z+δ*r
  have htm := gradient_generator_quadrature
    (b := fun s y ↦ deriv (deriv (V s)) y)
    (p := fun s y ↦ (1/2 : ℝ)*(deriv (V s) y)^2) (y := x+d)
    hδ hG hK hL hγ hγ0 hγG
    (fun s hs ↦ hp s hs _) (fun s hs ↦ haLip s hs _) (fun s hs ↦ hpLip s hs _)
    (haint _) (hpint _)
  have ht : |(V (t+δ) (x+d)-V t x+1-
        δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2))-
      (V t (x+d)-V t x+1)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+r*1*deriv (V t) x)| ≤
      δ*(((1/2 : ℝ)+G)*L*(δ+|d|)+K*(γ (t+δ)-γ t)) := by
    have heq : (V (t+δ) (x+d)-V t x+1-
        δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2))-
      (V t (x+d)-V t x+1)+
      δ*((1/2 : ℝ)*deriv (deriv (V t)) x+r*1*deriv (V t) x) =
        (V (t+δ) (x+d)-V t (x+d))+
          δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) := by ring
    rw [heq, hPDE]
    convert htm using 1
    · rw [show -(∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
          γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))+
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2)) =
        -((∫ s in t..(t+δ), (1/2 : ℝ)*deriv (deriv (V s)) (x+d)+
          γ s*((1/2 : ℝ)*(deriv (V s) (x+d))^2))-
        δ*((1/2 : ℝ)*deriv (deriv (V t)) x+γ t*((1/2 : ℝ)*(deriv (V t) x)^2))) by ring,
        abs_neg]
    · simp only [add_sub_cancel_left]
  have hs : |(V t (x+d)-V t x+1)-1-
      deriv (V t) x*d-(1/2 : ℝ)*deriv (deriv (V t)) x*d^2| ≤ K*|d|^3 := by
    simpa only [add_sub_cancel_right] using third_order_remainder_bound hsmooth hK hthird x d
  have hh := euler_cubic_remainder (v := 1) (c := r)
    hδ hδ1 hG hK (by positivity : 0≤(1/2+G)*L)
    hr (by norm_num) ha (by simpa only [mul_one] using hs)
    (by simpa only [mul_one] using ht)
  convert hh using 1 <;> dsimp only [cubicEnvelope, d]
  all_goals congr 1
  all_goals ring

lemma control_completion_square {γ α : ℝ → ℝ} {a b p : ℝ}
    (hab : a≤b) (hγ : ∀ s∈Icc a b, 0≤γ s)
    (hi : IntervalIntegrable γ volume a b)
    (hi₁ : IntervalIntegrable (fun s ↦ γ s*α s) volume a b)
    (hi₂ : IntervalIntegrable (fun s ↦ γ s*(α s)^2) volume a b) :
    p*(∫ s in a..b, γ s*α s)-(1/2 : ℝ)*(∫ s in a..b, γ s*(α s)^2) ≤
      ((1/2 : ℝ)*p^2)*(∫ s in a..b, γ s) := by
  have hpw : ∀ s∈Icc a b,
      p*(γ s*α s)-(1/2 : ℝ)*(γ s*(α s)^2) ≤ ((1/2 : ℝ)*p^2)*γ s := by
    intro s hs
    nlinarith [mul_nonneg (hγ s hs) (sq_nonneg (α s-p))]
  have hh := intervalIntegral.integral_mono_on hab
    ((hi₁.const_mul p).sub (hi₂.const_mul (1/2))) (hi.const_mul ((1/2 : ℝ)*p^2)) hpw
  simpa only [intervalIntegral.integral_sub (hi₁.const_mul p) (hi₂.const_mul (1/2)),
    intervalIntegral.integral_const_mul] using hh

lemma ValueStrip.control_one_step {T K L t δ x z : ℝ} {γ α : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} (h : ValueStrip T γ V K L)
    (ht : 0≤t) (hδ : 0<δ) (hδ1 : δ≤1) (htδ : t+δ≤T)
    (hα : ∀ s∈Icc t (t+δ), |α s|≤1)
    (hi : IntervalIntegrable γ volume t (t+δ))
    (hi₁ : IntervalIntegrable (fun s ↦ γ s*α s) volume t (t+δ))
    (hi₂ : IntervalIntegrable (fun s ↦ γ s*(α s)^2) volume t (t+δ)) :
    V (t+δ) (x+Real.sqrt δ*z+(∫ s in t..(t+δ), γ s*α s))-
      (1/2 : ℝ)*(∫ s in t..(t+δ), γ s*(α s)^2)-V t x-
      deriv (V t) x*Real.sqrt δ*z-
      (1/2 : ℝ)*δ*deriv (deriv (V t)) x*(z^2-1) ≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) z+
        2*δ*K*(γ (t+δ)-γ t) := by
  have htT : t≤T := (le_add_of_nonneg_right hδ.le).trans htδ
  have hT : 0≤T := ht.trans htT
  have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht htδ
  have htm : t∈Icc (0 : ℝ) T := ⟨ht,htT⟩
  have hem : t+δ∈Icc (0 : ℝ) T := ⟨by linarith,htδ⟩
  have hTm : T∈Icc (0 : ℝ) T := ⟨hT,le_rfl⟩
  have hG := h.gamma_nonneg T hTm
  have hγm := h.gamma_mono.mono hsub
  have hγn : ∀ s∈Icc t (t+δ), 0≤γ s := fun s hs ↦ h.gamma_nonneg s (hsub hs)
  have hγb : ∀ s∈Icc t (t+δ), γ s≤γ T :=
    fun s hs ↦ h.gamma_mono (hsub hs) hTm (hs.2.trans htδ)
  let D := ∫ s in t..(t+δ), γ s*α s
  let r := D/δ
  have hD : |D|≤δ*(γ T) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := t+δ) (f := fun s ↦ γ s*α s) (C := γ T) (fun s hs ↦ by
        rw [uIoc_of_le (by linarith : t≤t+δ)] at hs
        have hs' : s∈Icc t (t+δ) := ⟨hs.1.le,hs.2⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hγn s hs')]
        exact (mul_le_mul_of_nonneg_left (hα s hs') (hγn s hs')).trans
          (by simpa only [mul_one] using hγb s hs'))
    simpa only [Real.norm_eq_abs, show t+δ-t=δ by ring,
      abs_of_nonneg hδ.le, mul_comm (γ T) δ] using hh
  have hr : |r|≤γ T := by
    dsimp only [r]
    rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
    simpa only [mul_comm] using hD
  have hdr : δ*r=D := by dsimp [r]; field_simp
  have hbint (y : ℝ) : IntervalIntegrable (fun s ↦ deriv (deriv (V s)) y) volume t (t+δ) :=
    (h.second_integrable y).mono_set (by
      rw [uIcc_of_le (by linarith : t≤t+δ),uIcc_of_le hT]
      exact hsub)
  have hpint (y : ℝ) : IntervalIntegrable (fun s ↦ γ s*((1/2 : ℝ)*(deriv (V s) y)^2)) volume t (t+δ) :=
    (h.product_integrable y).mono_set (by
      rw [uIcc_of_le (by linarith : t≤t+δ),uIcc_of_le hT]
      exact hsub)
  have hh := value_bounded_drift_one_step (V := V) (γ := γ) (x := x) (z := z)
    hδ.le hδ1 hG h.K_nonneg h.L_nonneg hr hγm (h.gamma_nonneg t htm)
    (h.gamma_mono htm hTm htT) (h.smooth t htm) (h.second_bound t htm x)
    (h.third_bound t htm) (fun s hs ↦ h.product_bound s (hsub hs))
    (fun s hs y ↦ h.second_lipschitz t htm s (hsub hs) x y)
    (fun s hs y ↦ h.product_lipschitz t htm s (hsub hs) x y)
    hbint hpint (fun y ↦ h.pde t htm (t+δ) hem y)
  dsimp only at hh
  rw [hdr, ←add_assoc] at hh
  have hcomp := control_completion_square (p := deriv (V t) x)
    (by linarith : t≤t+δ) hγn hi hi₁ hi₂
  have hγint : (∫ s in t..(t+δ), γ s)≤δ*γ (t+δ) := by
    have hc := intervalIntegral.integral_mono_on (by linarith : t≤t+δ) hi
      (intervalIntegrable_const (c := γ (t+δ)))
      (fun s hs ↦ h.gamma_mono (hsub hs) hem hs.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, show t+δ-t=δ by ring] using hc
  have hp0 : 0≤(1/2 : ℝ)*(deriv (V t) x)^2 := by positivity
  have hpK : (1/2 : ℝ)*(deriv (V t) x)^2≤K :=
    (le_abs_self _).trans (h.product_bound t htm x)
  have hgap : 0≤γ (t+δ)-γ t := sub_nonneg.mpr (h.gamma_mono htm hem (by linarith))
  have hdiff : (1/2 : ℝ)*(deriv (V t) x)^2*(∫ s in t..(t+δ), γ s)-
      δ*((1/2 : ℝ)*γ t*(deriv (V t) x)^2) ≤ δ*K*(γ (t+δ)-γ t) := by
    calc
      _ ≤ (1/2 : ℝ)*(deriv (V t) x)^2*(δ*γ (t+δ))-
          δ*((1/2 : ℝ)*γ t*(deriv (V t) x)^2) := by gcongr
      _ = δ*((1/2 : ℝ)*(deriv (V t) x)^2)*(γ (t+δ)-γ t) := by ring
      _ ≤ _ := by gcongr
  have hhu := (le_abs_self _).trans hh
  have hcomp' : deriv (V t) x*D-(1/2 : ℝ)*(∫ s in t..(t+δ), γ s*(α s)^2)-
      δ*((1/2 : ℝ)*γ t*(deriv (V t) x)^2) ≤ δ*K*(γ (t+δ)-γ t) := by
    dsimp only [D]
    linarith
  have heq : δ*(deriv (V t) x*r-(1/2 : ℝ)*γ t*(deriv (V t) x)^2) =
      deriv (V t) x*D-δ*((1/2 : ℝ)*γ t*(deriv (V t) x)^2) := by rw [mul_sub, mul_left_comm δ, hdr]
  rw [heq] at hhu
  dsimp only [D] at hhu hcomp'
  linarith

end SKValue

namespace SKValue

lemma ValueStrip.control_mesh_bound {T K L x : ℝ} {N : ℕ} {γ α W X : ℝ → ℝ}
    {V : ℝ → ℝ → ℝ} {Z : Fin N → ℝ}
    (hT : 0<T) (hT1 : T≤1) (hN : 0<N) (h : ValueStrip T γ V K L)
    (hα : ∀ s∈Icc (0 : ℝ) T, |α s|≤1)
    (hi₁ : IntervalIntegrable (fun s ↦ γ s*α s) volume 0 T)
    (hi₂ : IntervalIntegrable (fun s ↦ γ s*(α s)^2) volume 0 T)
    (hX : ∀ t∈Icc (0 : ℝ) T, X t=x+W t+∫ s in (0 : ℝ)..t, γ s*α s)
    (hZ : ∀ i : Fin N, Real.sqrt (stepSize T N)*Z i=
      W (meshTime T N (i+1))-W (meshTime T N i)) :
    V T (X T)-V 0 (X 0)-(1/2 : ℝ)*(∫ s in (0 : ℝ)..T, γ s*(α s)^2)-
      (∑ i : Fin N, deriv (V (meshTime T N i)) (X (meshTime T N i))*
        (W (meshTime T N (i+1))-W (meshTime T N i)))-
      (1/2 : ℝ)*(∑ i : Fin N, deriv (deriv (V (meshTime T N i))) (X (meshTime T N i))*
        ((W (meshTime T N (i+1))-W (meshTime T N i))^2-stepSize T N)) ≤
    stepSize T N*Real.sqrt (stepSize T N)*
      (∑ i : Fin N, cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i))+
      2*stepSize T N*K*(γ T-γ 0) := by
  let δ := stepSize T N
  have hNr : 0<(N : ℝ) := by exact_mod_cast hN
  have hδ : 0<δ := div_pos hT hNr
  have hδ1 : δ≤1 := by
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    exact (div_le_iff₀ hNr).2 (by simpa only [one_mul] using hT1.trans hN1)
  have hmesh : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
  have htime (j : ℕ) (hj : j≤N) : meshTime T N j∈Icc (0 : ℝ) T :=
    mesh_mem_strip_ito hδ.le hmesh hj
  have hsucc (j : ℕ) : meshTime T N (j+1)=meshTime T N j+δ := by
    dsimp [meshTime,δ]; push_cast; ring
  have hlast : meshTime T N N=T := hmesh
  have hzero : meshTime T N 0=0 := by simp only [meshTime,Nat.cast_zero,zero_mul]
  let C := fun t ↦ (1/2 : ℝ)*(∫ s in (0 : ℝ)..t, γ s*(α s)^2)
  let P := fun j ↦ V (meshTime T N j) (X (meshTime T N j))-C (meshTime T N j)
  let D := fun i : Fin N ↦ W (meshTime T N (i+1))-W (meshTime T N i)
  let R := fun i : Fin N ↦ P (i+1)-P i-
    deriv (V (meshTime T N i)) (X (meshTime T N i))*D i-
    (1/2 : ℝ)*deriv (deriv (V (meshTime T N i))) (X (meshTime T N i))*(D i^2-δ)
  have hiγ : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hT.le]
    exact h.gamma_mono
  have hlocal (i : Fin N) : R i≤
      δ*Real.sqrt δ*cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i)+
      2*δ*K*(γ (meshTime T N (i+1))-γ (meshTime T N i)) := by
    let t := meshTime T N i
    have ht : t∈Icc (0 : ℝ) T := htime i i.isLt.le
    have ht' : t+δ∈Icc (0 : ℝ) T := by rw [←hsucc]; exact htime (i+1) (by omega)
    have hsub : Icc t (t+δ)⊆Icc (0 : ℝ) T := Icc_subset_Icc ht.1 ht'.2
    have hh := h.control_one_step (x := X t) (z := Z i) ht.1 hδ hδ1 ht'.2
      (fun s hs ↦ hα s (hsub hs)) (intervalIntegrable_substrip hT.le hiγ ht ht')
      (intervalIntegrable_substrip hT.le hi₁ ht ht')
      (intervalIntegrable_substrip hT.le hi₂ ht ht')
    have hD : Real.sqrt δ*Z i=D i := hZ i
    have hXinc : X (t+δ)=X t+D i+(∫ s in t..(t+δ), γ s*α s) := by
      have hi0 := intervalIntegrable_substrip hT.le hi₁ ⟨le_rfl,hT.le⟩ ht
      have hinc := intervalIntegral.integral_add_adjacent_intervals hi0
        (intervalIntegrable_substrip hT.le hi₁ ht ht')
      rw [hX (t+δ) ht',hX t ht]
      dsimp only [D,t]
      rw [hsucc]
      linarith
    have hCinc : C (t+δ)-C t=(1/2 : ℝ)*(∫ s in t..(t+δ), γ s*(α s)^2) := by
      have hi0 := intervalIntegrable_substrip hT.le hi₂ ⟨le_rfl,hT.le⟩ ht
      have hinc := intervalIntegral.integral_add_adjacent_intervals hi0
        (intervalIntegrable_substrip hT.le hi₂ ht ht')
      dsimp only [C]
      linarith
    have hQ : D i^2=δ*(Z i)^2 := by rw [←hD,mul_pow,Real.sq_sqrt hδ.le]
    have hReq : R i=V (t+δ) (X t+Real.sqrt δ*Z i+
        (∫ s in t..(t+δ), γ s*α s))-
        (1/2 : ℝ)*(∫ s in t..(t+δ), γ s*(α s)^2)-V t (X t)-
        deriv (V t) (X t)*Real.sqrt δ*Z i-
        (1/2 : ℝ)*δ*deriv (deriv (V t)) (X t)*((Z i)^2-1) := by
      rw [hD,←hXinc]
      dsimp only [R,P]
      rw [hsucc]
      rw [show V (t+δ) (X (t+δ))-C (t+δ)-(V t (X t)-C t) =
        V (t+δ) (X (t+δ))-V t (X t)-(C (t+δ)-C t) by ring,hCinc,hQ,←hD]
      ring
    rw [hReq]
    simpa only [t,←hsucc] using hh
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) ↦ hlocal i)
  dsimp only [R] at hsum
  rw [sum_local_residual] at hsum
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  rw [sum_steps_sub (fun j ↦ γ (meshTime T N j)),hlast,hzero] at hsum
  dsimp only [P,C,D] at hsum
  rw [hlast,hzero,intervalIntegral.integral_same,mul_zero,sub_zero] at hsum
  simp_rw [mul_assoc] at hsum
  rw [←Finset.mul_sum] at hsum
  dsimp only [δ] at hsum
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Gaussian_ShiftedBrownianCoordinates
attribute [-instance] _root_.OAI.SKValueG.expOneNoAtoms _root_.OAI.SKValueG.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators

lemma shiftedBrownianCoordinates_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (a : ℝ≥0)
    {T : ℝ} {N : ℕ} (hT : 0<T) (hN : 0<N) (i : Fin N) :
    HasLaw (shiftedBrownianCoordinates B a T N i) standardGaussian μ := by
  apply brownian_coordinate_hasLaw (hB.shift a)
  exact Real.toNNReal_pos.mpr (div_pos hT (by exact_mod_cast hN))

lemma meshTime_toNNReal {T : ℝ} {N : ℕ} (hT : 0≤T) (j : ℕ) :
    Real.toNNReal (meshTime T N j)=(j : ℝ≥0)*Real.toNNReal (stepSize T N) := by
  have hδ : 0≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  apply NNReal.coe_injective
  unfold meshTime
  rw [Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg j) hδ),
    NNReal.coe_mul,NNReal.coe_natCast,Real.coe_toNNReal _ hδ]

lemma shiftedBrownianCoordinates_exact
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {W : ℝ → Ω → ℝ} {a : ℝ≥0}
    {T : ℝ} {N : ℕ} (hT : 0<T) (hN : 0<N)
    (hW : ∀ s∈Icc (0 : ℝ) T, ∀ t∈Icc (0 : ℝ) T, ∀ ω,
      W t ω-W s ω=B (a+t.toNNReal) ω-B (a+s.toNNReal) ω)
    (i : Fin N) (ω : Ω) :
    Real.sqrt (stepSize T N)*shiftedBrownianCoordinates B a T N i ω=
      W (meshTime T N (i+1)) ω-W (meshTime T N i) ω := by
  have hδ : 0≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
  have hδ' : 0<Real.toNNReal (stepSize T N) :=
    Real.toNNReal_pos.mpr (div_pos hT (by exact_mod_cast hN))
  rw [hW _ (mesh_time_mem_total hT.le i.isLt.le) _ (mesh_time_mem_total hT.le i.isLt) ω]
  rw [meshTime_toNNReal hT.le,meshTime_toNNReal hT.le]
  have hh := brownian_coordinate_exact (fun r ω ↦ B (a+r) ω-B a ω) hδ' N ω i
  simp only [Real.coe_toNNReal _ hδ] at hh
  change Real.sqrt (stepSize T N)*brownianCoordinates _ _ _ _ _=_
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlVerification
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

lemma ValueStrip.continuous_second {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : ValueStrip T γ V K L) {t : ℝ} (ht : t∈Icc (0 : ℝ) T) :
    Continuous (deriv (deriv (V t))) := by
  have hc := (h.smooth t ht).continuous_iteratedDeriv 2 (by norm_num)
  simpa only [show 2=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using hc

theorem ValueStrip.progressive_control_upper
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) (hγM : Measurable γ)
    {α : ℝ≥0 → Ω → ℝ} (hα : IsProgressive (Filtration.natural B hBm) α)
    (hαb : ∀ s ω, |α s ω|≤1) (x : ℝ) :
    (∫ ω, V T (controlState B γ α x T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω ∂μ)≤V 0 x := by
  let X := controlState B γ α x
  let W := fun t : ℝ ↦ B (Real.toNNReal t)
  let F := fun ω ↦ V T (X T ω)-V 0 (X 0 ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω
  have hγb (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |γ t|≤γ T := by
    rw [abs_of_nonneg (h.gamma_nonneg t ht)]
    exact h.gamma_mono ht ⟨hT.le,le_rfl⟩ ht.2
  have hiγ : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hT.le]
    exact h.gamma_mono
  have hXm (t : ℝ) (ht : t∈Icc (0 : ℝ) T) :
      StronglyMeasurable[Filtration.natural B hBm (Real.toNNReal t)] (X t) :=
    controlState_past_measurable hBm hα hγM x ht.1
  have hXlp (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : MemLp (X t) 2 μ :=
    controlState_memLp_two hB hBm hα hαb hγM hγb x ht.1 ht.2
  have hVi (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : Integrable (fun ω ↦ V t (X t ω)) μ :=
    (h.value_memLp ht (hXlp t ht)).integrable (by norm_num)
  have hAi : Integrable (controlAccum γ α 2 T) μ :=
    controlAccum_integrable hα hαb hγM hγb 2 hT.le le_rfl
  have hV0 := hVi 0 ⟨le_rfl,hT.le⟩
  have hVT := hVi T ⟨hT.le,le_rfl⟩
  have hFi : Integrable F μ := (hVT.sub hV0).sub (hAi.const_mul _)
  have hW (s : ℝ) (_ : s∈Icc (0 : ℝ) T) (t : ℝ) (_ : t∈Icc (0 : ℝ) T) (ω : Ω) :
      W t ω-W s ω=B (0+t.toNNReal) ω-B (0+s.toNNReal) ω := by simp only [W,zero_add]
  have hbound (N : ℕ) (hN : 0<N) : (∫ ω, F ω ∂μ)≤
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
      2*stepSize T N*K*(γ T-γ 0) := by
    let δ := stepSize T N
    let τ := fun j : ℕ ↦ (meshTime T N j).toNNReal
    let D := fun i : Fin N ↦ fun ω ↦ W (meshTime T N (i+1)) ω-W (meshTime T N i) ω
    let H := fun i : Fin N ↦ fun ω ↦ deriv (V (meshTime T N i)) (X (meshTime T N i) ω)
    let A := fun i : Fin N ↦ fun ω ↦ deriv (deriv (V (meshTime T N i))) (X (meshTime T N i) ω)
    let P := fun i : Fin N ↦ fun ω ↦ H i ω*D i ω
    let Q := fun i : Fin N ↦ fun ω ↦ A i ω*(D i ω^2-δ)
    let Z := shiftedBrownianCoordinates B 0 T N
    let E := fun i : Fin N ↦ fun ω ↦ cubicEnvelope (γ T) K ((1/2+γ T)*L) (Z i ω)
    have hδ : 0≤δ := div_nonneg hT.le (Nat.cast_nonneg N)
    have htime (j : ℕ) (hj : j≤N) := mesh_time_mem_total hT.le hj
    have hτ (i : Fin N) : τ i≤τ (i+1) := by
      apply Real.toNNReal_mono
      dsimp [meshTime]
      push_cast
      nlinarith
    have hτdiff (i : Fin N) : (τ (i+1) : ℝ)-(τ i : ℝ)=δ := by
      dsimp only [τ]
      rw [Real.coe_toNNReal _ (htime (i+1) i.isLt).1,Real.coe_toNNReal _ (htime i i.isLt.le).1]
      dsimp [meshTime,δ]
      push_cast
      ring
    have hHm (i : Fin N) : StronglyMeasurable[Filtration.natural B hBm (τ i)] (H i) :=
      ((h.smooth _ (htime i i.isLt.le)).continuous_deriv (by norm_num)).comp_stronglyMeasurable
        (hXm _ (htime i i.isLt.le))
    have hAm (i : Fin N) : StronglyMeasurable[Filtration.natural B hBm (τ i)] (A i) :=
      (h.continuous_second (htime i i.isLt.le)).comp_stronglyMeasurable (hXm _ (htime i i.isLt.le))
    have hHi (i : Fin N) : Integrable (H i) μ := by
      apply Integrable.of_bound ((hHm i).mono (Filtration.le _ _)).aestronglyMeasurable 1
      exact Eventually.of_forall (fun ω ↦ by
        simpa only [Real.norm_eq_abs] using h.bounded _ (htime i i.isLt.le) (X _ ω))
    have hAii (i : Fin N) : Integrable (A i) μ := by
      apply Integrable.of_bound ((hAm i).mono (Filtration.le _ _)).aestronglyMeasurable K
      exact Eventually.of_forall (fun ω ↦ by
        simpa only [Real.norm_eq_abs] using h.second_bound _ (htime i i.isLt.le) (X _ ω))
    have hPi (i : Fin N) : Integrable (P i) μ :=
      brownian_predictable_increment_integrable hB hBm (hτ i) (hHm i) (hHi i)
    have hQi (i : Fin N) : Integrable (Q i) μ := by
      simpa only [Q,D,W,hτdiff] using
        brownian_predictable_quadratic_integrable hB hBm (hτ i) (hAm i) (hAii i)
    have hP0 (i : Fin N) : (∫ ω, P i ω ∂μ)=0 :=
      brownian_predictable_increment_mean hB hBm (hτ i) (hHm i)
    have hQ0 (i : Fin N) : (∫ ω, Q i ω ∂μ)=0 := by
      simpa only [Q,D,W,hτdiff] using brownian_predictable_quadratic_mean hB hBm (hτ i) (hAm i)
    have hZlaw (i : Fin N) : HasLaw (Z i) standardGaussian μ :=
      shiftedBrownianCoordinates_hasLaw hB 0 hT hN i
    have hEi (i : Fin N) : Integrable (E i) μ :=
      (cubicEnvelope_memLp_two (hZlaw i) (h.gamma_nonneg T ⟨hT.le,le_rfl⟩)
        K ((1/2+γ T)*L)).integrable (by norm_num)
    have hEmean (i : Fin N) : (∫ ω, E i ω ∂μ)=cubicEnvelopeMean (γ T) K ((1/2+γ T)*L) :=
      (hZlaw i).integral_comp (measurable_cubicEnvelope _ _ _).aestronglyMeasurable
    let R := fun ω ↦ F ω-(∑ i : Fin N, P i ω)-(1/2 : ℝ)*(∑ i : Fin N, Q i ω)
    let J := fun ω ↦ δ*Real.sqrt δ*(∑ i : Fin N, E i ω)+2*δ*K*(γ T-γ 0)
    have hPs : Integrable (fun ω ↦ ∑ i : Fin N, P i ω) μ := integrable_finsetSum _ (fun i _ ↦ hPi i)
    have hQs : Integrable (fun ω ↦ ∑ i : Fin N, Q i ω) μ := integrable_finsetSum _ (fun i _ ↦ hQi i)
    have hEs : Integrable (fun ω ↦ ∑ i : Fin N, E i ω) μ := integrable_finsetSum _ (fun i _ ↦ hEi i)
    have hRi : Integrable R μ := (hFi.sub hPs).sub (hQs.const_mul _)
    have hJi : Integrable J μ := (hEs.const_mul _).add (integrable_const _)
    have hRJ (ω : Ω) : R ω≤J ω := by
      have h1 := controlAccum_integrand_intervalIntegrable hα hαb hγM hiγ hT.le 1 ω
      simp only [pow_one] at h1
      have hh := h.control_mesh_bound (x := x) (X := fun t ↦ X t ω) (W := fun t ↦ W t ω)
        (Z := fun i ↦ Z i ω) hT hT1 hN (fun s _ ↦ hαb _ ω) h1
        (controlAccum_integrand_intervalIntegrable hα hαb hγM hiγ hT.le 2 ω)
        (fun t _ ↦ by simp only [X,controlState,controlAccum,W,pow_one])
        (fun i ↦ shiftedBrownianCoordinates_exact hT hN hW i ω)
      exact hh
    have hRmean : (∫ ω, R ω ∂μ)=(∫ ω, F ω ∂μ) := by
      dsimp only [R]
      rw [integral_sub (f := fun ω ↦ F ω-∑ i : Fin N, P i ω)
        (g := fun ω ↦ (1/2 : ℝ)*(∑ i : Fin N, Q i ω))
        (hFi.sub hPs) (hQs.const_mul (1/2)),integral_sub hFi hPs,integral_const_mul,
        integral_finsetSum _ (fun i _ ↦ hPi i),integral_finsetSum _ (fun i _ ↦ hQi i)]
      simp only [hP0,hQ0,Finset.sum_const_zero,mul_zero,sub_zero]
    have hJmean : (∫ ω, J ω ∂μ)=
        T*Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+2*δ*K*(γ T-γ 0) := by
      dsimp only [J]
      rw [integral_add (hEs.const_mul _) (integrable_const _),integral_const_mul,
        integral_finsetSum _ (fun i _ ↦ hEi i)]
      simp only [hEmean,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        integral_const,probReal_univ,smul_eq_mul,one_mul]
      have hN0 : (N : ℝ)≠0 := by exact_mod_cast hN.ne'
      have hm : (N : ℝ)*δ=T := by dsimp [δ,stepSize]; field_simp
      linear_combination (Real.sqrt δ*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L))*hm
    rw [←hRmean,←hJmean]
    exact integral_mono hRi hJi hRJ
  have hs : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat T
  have hlim : Tendsto (fun N ↦
      T*Real.sqrt (stepSize T N)*cubicEnvelopeMean (γ T) K ((1/2+γ T)*L)+
      2*stepSize T N*K*(γ T-γ 0)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_zero,mul_zero,zero_mul,add_zero] using
      ((((Real.continuous_sqrt.tendsto 0).comp hs).const_mul T).mul_const
        (cubicEnvelopeMean (γ T) K ((1/2+γ T)*L))).add
        (((hs.const_mul 2).mul_const K).mul_const (γ T-γ 0))
  have hFle : (∫ ω, F ω ∂μ)≤0 := ge_of_tendsto hlim
    ((eventually_gt_atTop 0).mono (fun N hN ↦ hbound N hN))
  have h0 : (∫ ω, V 0 (X 0 ω) ∂μ)=V 0 x := by
    rw [integral_congr_ae ((controlState_initial hB γ α x).mono (fun ω hω ↦ congrArg (V 0) hω))]
    simp
  dsimp only [F] at hFle
  rw [integral_sub (f := fun ω ↦ V T (X T ω)-V 0 (X 0 ω))
    (g := fun ω ↦ (1/2 : ℝ)*controlAccum γ α 2 T ω)
    (hVT.sub hV0) (hAi.const_mul (1/2)),integral_sub hVT hV0,h0] at hFle
  rw [integral_sub hVT (hAi.const_mul (1/2))]
  linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Processes_Feedback
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

lemma progressive_interval {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {a b : ℝ} {H : Ω → ℝ} (_ : 0 ≤ a)
    (hH : Measurable[f (Real.toNNReal a)] H) :
    IsProgressive f (fun t ω ↦ if a < (t : ℝ) ∧ (t : ℝ)  ≤  b then H ω else 0) := by
  intro t
  by_cases hat : Real.toNNReal a  ≤  t
  · let : MeasurableSpace Ω := f t
    have hHm : Measurable H := hH.mono (f.mono hat) le_rfl
    exact (hHm.comp measurable_snd).ite
      ((measurableSet_lt measurable_const (measurable_coe_nnreal_real.comp
        (measurable_subtype_coe.comp measurable_fst))).inter
        (measurableSet_le (measurable_coe_nnreal_real.comp
          (measurable_subtype_coe.comp measurable_fst)) measurable_const)) measurable_const
  · have he : (fun p : Iic t × Ω ↦ if a < (p.1 : ℝ≥0) ∧ ((p.1 : ℝ≥0) : ℝ)  ≤  b then H p.2 else 0) =
        fun _ ↦ (0 : ℝ) := by
      funext p
      apply ite_eq_right
      intro hp
      exact hat ((Real.toNNReal_le_iff_le_coe).2 (hp.1.le.trans (by exact_mod_cast p.1.2)))
    rw [he]
    exact measurable_const

lemma meshControl_progressive {Ω : Type*} [m : MeasurableSpace Ω]
    {f : Filtration ℝ≥0 m} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} {H : Fin N → Ω → ℝ}
    (hH : ∀ j : Fin N, Measurable[f (Real.toNNReal (meshTime T N j))] (H j)) :
    IsProgressive f (meshControl T N H) := by
  apply IsProgressive.finsetSum
  intro j _
  exact progressive_interval (mesh_time_mem_total hT j.isLt.le).1 (hH j)

lemma mesh_intervals_disjoint {T : ℝ} (hT : 0 ≤ T) {N : ℕ} {i j : Fin N} {t : ℝ}
    (hi : meshTime T N i < t ∧ t  ≤  meshTime T N (i+1))
    (hj : meshTime T N j < t ∧ t  ≤  meshTime T N (j+1)) : i=j := by
  have hδ : 0  ≤  stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have hlt : ∀ a b : ℕ, a+1 ≤ b → meshTime T N (a+1) ≤ meshTime T N b := by
    intro a b hab
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hδ
  apply Fin.ext
  by_contra he
  rcases lt_or_gt_of_ne he with hij | hji
  · have hh := hlt i j hij
    linarith [hi.2,hj.1]
  · have hh := hlt j i hji
    linarith [hi.1,hj.2]

lemma meshControl_eq {Ω : Type*} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (H : Fin N → Ω → ℝ)
    {j : Fin N} {t : ℝ≥0} (ht : meshTime T N j < t ∧ (t : ℝ)  ≤  meshTime T N (j+1)) (ω : Ω) :
    meshControl T N H t ω=H j ω := by
  unfold meshControl
  rw [Finset.sum_eq_single j]
  · simp only [ite_eq_left ht]
  · intro i _ hij
    exact ite_eq_right (fun hi ↦ hij (mesh_intervals_disjoint hT hi ht))
  · simp

lemma meshControl_bound {Ω : Type*} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (H : Fin N → Ω → ℝ)
    (hH : ∀ j ω, |H j ω| ≤ 1) (t : ℝ≥0) (ω : Ω) : |meshControl T N H t ω| ≤ 1 := by
  by_cases he : ∃ j : Fin N, meshTime T N j < t ∧ (t : ℝ)  ≤  meshTime T N (j+1)
  · obtain ⟨j,hj⟩ := he
    rw [meshControl_eq hT H hj]
    exact hH j ω
  · have hh : meshControl T N H t ω=0 := by
      unfold meshControl
      apply Finset.sum_eq_zero
      intro j _
      exact ite_eq_right (fun hj ↦ he ⟨j,hj⟩)
    rw [hh]
    norm_num

lemma meshControl_momentIntegral {Ω : Type*} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : 0<N)
    (H : Fin N → Ω → ℝ) {γ : ℝ → ℝ} (hγ : IntervalIntegrable γ volume 0 T)
    (k : ℕ) (ω : Ω) :
    controlAccum γ (meshControl T N H) k T ω =
      ∑ j : Fin N, (∫ s in meshTime T N j..meshTime T N (j+1), γ s)*(H j ω)^k := by
  have hδ : 0 ≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have htime (j : ℕ) (hj : j ≤ N) := mesh_time_mem_total hT hj
  have horder (j : ℕ) : meshTime T N j ≤ meshTime T N (j+1) := by
    dsimp [meshTime]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hδ
  have hlast : meshTime T N N=T := by
    dsimp [meshTime,stepSize]
    field_simp
  have he (j : Fin N) :
      (fun s ↦ γ s*(meshControl T N H (Real.toNNReal s) ω)^k) =ᵐ[
        volume.restrict (uIoc (meshTime T N j) (meshTime T N (j+1)))]
      (fun s ↦ γ s*(H j ω)^k) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le (horder j)] at hs
    have hs0 : 0 ≤ s := (htime j j.isLt.le).1.trans hs.1.le
    rw [meshControl_eq hT H (by simpa only [Real.coe_toNNReal _ hs0,Set.mem_Ioc] using hs)]
  have hi (j : ℕ) (hj : j<N) : IntervalIntegrable
      (fun s ↦ γ s*(meshControl T N H (Real.toNNReal s) ω)^k) volume
      (meshTime T N j) (meshTime T N (j+1)) := by
    apply ((intervalIntegrable_substrip hT hγ (htime j hj.le)
      (htime (j+1) hj)).mul_const ((H ⟨j,hj⟩ ω)^k)).congr_ae
    exact (he ⟨j,hj⟩).symm
  have hs := intervalIntegral.sum_integral_adjacent_intervals hi
  rw [hlast,show meshTime T N 0=0 by simp [meshTime]] at hs
  rw [controlAccum,←hs,←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_congr_ae_restrict (he j),intervalIntegral.integral_mul_const]

lemma monotone_interval_quadrature {γ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hγ : MonotoneOn γ (Icc a b)) :
    |(∫ s in a..b, γ s)-(b-a)*γ a| ≤ (b-a)*(γ b-γ a) := by
  have hi : IntervalIntegrable γ volume a b := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hγ
  have hdiff : (∫ s in a..b, γ s)-(b-a)*γ a =∫ s in a..b, γ s-γ a := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,smul_eq_mul]
  rw [hdiff]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun s ↦ γ s-γ a) (C := γ b-γ a) (fun s hs ↦ by
      rw [uIoc_of_le hab] at hs
      have hs' : s∈Icc a b := ⟨hs.1.le,hs.2⟩
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hγ ⟨le_rfl,hab⟩ hs' hs.1.le))]
      exact sub_le_sub_right (hγ hs' ⟨hab,le_rfl⟩ hs.2) _)
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab),mul_comm] using hh

lemma meshControl_quadrature {Ω : Type*} {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : 0<N)
    (H : Fin N → Ω → ℝ) (hH : ∀ j ω, |H j ω| ≤ 1)
    {γ : ℝ → ℝ} (hγ : MonotoneOn γ (Icc (0 : ℝ) T)) (k : ℕ) (ω : Ω) :
    |controlAccum γ (meshControl T N H) k T ω-
      ∑ j : Fin N, stepSize T N*γ (meshTime T N j)*(H j ω)^k| ≤
      stepSize T N*(γ T-γ 0) := by
  have hi : IntervalIntegrable γ volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hγ
  rw [meshControl_momentIntegral hT hN H hi, ←Finset.sum_sub_distrib]
  have hδ : 0 ≤ stepSize T N := div_nonneg hT (Nat.cast_nonneg N)
  have htime (j : ℕ) (hj : j ≤ N) := mesh_time_mem_total hT hj
  have hgap (j : ℕ) : meshTime T N (j+1)-meshTime T N j=stepSize T N := by
    dsimp [meshTime]
    push_cast
    ring
  have horder (j : ℕ) : meshTime T N j ≤ meshTime T N (j+1) := by
    linarith [hgap j]
  have hloc (j : Fin N) :
      |(∫ s in meshTime T N j..meshTime T N (j+1), γ s)*(H j ω)^k-
        stepSize T N*γ (meshTime T N j)*(H j ω)^k| ≤
      stepSize T N*(γ (meshTime T N (j+1))-γ (meshTime T N j)) := by
    rw [←sub_mul,abs_mul]
    have hh := monotone_interval_quadrature (horder j)
      (hγ.mono (Icc_subset_Icc (htime j j.isLt.le).1 (htime (j+1) j.isLt).2))
    rw [hgap] at hh
    have hp : |(H j ω)^k| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hH j ω)
    exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans (by simpa only [mul_one] using hh)
  calc
    _ ≤ ∑ j : Fin N, |(∫ s in meshTime T N j..meshTime T N (j+1), γ s)*(H j ω)^k-
        stepSize T N*γ (meshTime T N j)*(H j ω)^k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, stepSize T N*(γ (meshTime T N (j+1))-γ (meshTime T N j)) :=
      Finset.sum_le_sum (fun j _ ↦ hloc j)
    _ = _ := by
      rw [←Finset.mul_sum, sum_steps_sub (fun j ↦ γ (meshTime T N j))]
      have hlast : meshTime T N N=T := by
        dsimp [meshTime,stepSize]
        field_simp
      change stepSize T N*(γ (meshTime T N N)-γ (meshTime T N 0)) = _
      rw [hlast]
      simp only [meshTime,Nat.cast_zero,zero_mul]

lemma coupled_euler_past_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, StronglyMeasurable (B t))
    {T : ℝ} (hT : 0<T) {N : ℕ} (hN : 0<N) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ)
    (hu : ∀ j<N, Measurable (u (meshTime T N j))) :
    ∀ j ≤ N, StronglyMeasurable[Filtration.natural B hBm (Real.toNNReal (meshTime T N j))]
      (coupledEuler T γ u B N j) := by
  let f := Filtration.natural B hBm
  intro j
  induction j with
  | zero =>
    intro _
    convert (stronglyMeasurable_const : StronglyMeasurable[f (Real.toNNReal (meshTime T N 0))] (fun _ : Ω ↦ (0 : ℝ))) using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    exact coupled_euler_zero T γ u B N ω
  | succ j ih =>
    intro hjN
    have hj : j<N := hjN
    have hδ : 0 ≤ stepSize T N := div_nonneg hT.le (Nat.cast_nonneg N)
    have ht : Real.toNNReal (meshTime T N j) ≤ Real.toNNReal (meshTime T N (j+1)) := by
      apply Real.toNNReal_mono
      apply mul_le_mul_of_nonneg_right _ hδ
      exact_mod_cast Nat.le_succ j
    have hY := (ih hj.le).mono (f.mono ht)
    have hB0 := (Filtration.stronglyAdapted_natural hBm (Real.toNNReal (meshTime T N j))).mono (f.mono ht)
    have hB1 := Filtration.stronglyAdapted_natural hBm (Real.toNNReal (meshTime T N (j+1)))
    have hU := ((hu j hj).comp hY.measurable).stronglyMeasurable.const_mul
      (stepSize T N*γ (meshTime T N j))
    convert ((hY.add hB1).sub hB0).add hU using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    rw [coupled_euler_step B hT γ u hN hj ω]
    rfl

lemma coupled_euler_drift_sum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {T : ℝ} (hT : 0<T) {N : ℕ} (hN : 0<N) (γ : ℝ → ℝ) (u : ℝ → ℝ → ℝ) (ω : Ω) :
    coupledEuler T γ u B N N ω = B (Real.toNNReal T) ω-B 0 ω+
      ∑ j : Fin N, stepSize T N*γ (meshTime T N j)*u (meshTime T N j) (coupledEuler T γ u B N j ω) := by
  have he (j : Fin N) :
      coupledEuler T γ u B N (j+1) ω-coupledEuler T γ u B N j ω =
        (B (Real.toNNReal (meshTime T N (j+1))) ω-B (Real.toNNReal (meshTime T N j)) ω)+
          stepSize T N*γ (meshTime T N j)*u (meshTime T N j) (coupledEuler T γ u B N j ω) := by
    rw [coupled_euler_step B hT γ u hN j.isLt ω]
    dsimp [meshTime,stepSize]
    ring
  have hh := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin N))=Finset.univ) (fun j _ ↦ he j)
  rw [sum_steps_sub (fun j ↦ coupledEuler T γ u B N j ω),Finset.sum_add_distrib,
    sum_steps_sub (fun j ↦ B (Real.toNNReal (meshTime T N j)) ω),coupled_euler_zero] at hh
  have hlast : meshTime T N N=T := by dsimp [meshTime,stepSize]; field_simp
  simpa only [sub_zero,hlast,show meshTime T N 0=0 by simp [meshTime],Real.toNNReal_zero] using hh

lemma ValueStrip.feedback_progressive {Ω : Type*} [m : MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) :
    IsProgressive (Filtration.natural B hBm) (feedbackControl B γ V T N) := by
  apply meshControl_progressive hT.le
  intro j
  have hu (i : ℕ) (hi : i ≤ N) : Continuous (deriv (V (meshTime T N i))) :=
    (h.smooth _ (mesh_time_mem_total hT.le hi)).continuous_deriv (by norm_num)
  exact (hu j j.isLt.le).measurable.comp
    (coupled_euler_past_measurable hBm hT hN γ (fun t ↦ deriv (V t))
      (fun i hi ↦ (hu i hi.le).measurable) j j.isLt.le).measurable

lemma ValueStrip.feedback_bound {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T) (h : ValueStrip T γ V K L) (N : ℕ) (s : ℝ≥0) (ω : Ω) :
    |feedbackControl B γ V T N s ω| ≤ 1 :=
  meshControl_bound hT _ (fun j _ ↦ h.bounded _ (mesh_time_mem_total hT j.isLt.le) _) s ω

lemma ValueStrip.feedback_state_error {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N)
    (ω : Ω) (hB0 : B 0 ω=0) :
    |controlState B γ (feedbackControl B γ V T N) 0 T ω-
      coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω| ≤ stepSize T N*(γ T-γ 0) := by
  have hh := meshControl_quadrature hT.le hN
    (fun (j : Fin N) ω ↦ deriv (V (meshTime T N j))
      (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))
    (fun j ω ↦ h.bounded _ (mesh_time_mem_total hT.le j.isLt.le) _)
    h.gamma_mono 1 ω
  rw [controlState,coupled_euler_drift_sum B hT hN,hB0]
  simpa only [pow_one,zero_add,sub_zero,add_sub_add_left_eq_sub,feedbackControl] using hh

lemma ValueStrip.feedback_energy_error {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) {N : ℕ} (hN : 0<N) (ω : Ω) :
    |(1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω-
      valueMeshEnergy T N γ V N (coupledCoordinates T N B ω)| ≤
        (1/2 : ℝ)*stepSize T N*(γ T-γ 0) := by
  have hh := meshControl_quadrature hT.le hN
    (fun (j : Fin N) ω ↦ deriv (V (meshTime T N j))
      (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))
    (fun j ω ↦ h.bounded _ (mesh_time_mem_total hT.le j.isLt.le) _)
    h.gamma_mono 2 ω
  have he : valueMeshEnergy T N γ V N (coupledCoordinates T N B ω) = (1/2 : ℝ)*
      ∑ j : Fin N, stepSize T N*γ (meshTime T N j)*
        (deriv (V (meshTime T N j)) (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))^2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ stepSize T N*γ (meshTime T N j)*
      (deriv (V (meshTime T N j)) (coupledEuler T γ (fun t ↦ deriv (V t)) B N j ω))^2)]
    dsimp only [valueMeshEnergy,coupledEuler]
    simp only [ite_eq_right hN.ne',Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,←mul_sub,abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))]
  exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans_eq (by ring)

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_ControlValue
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

lemma coupledCoordinates_measurable {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, StronglyMeasurable (B t)) (T : ℝ) (N : ℕ) :
    Measurable (coupledCoordinates T N B) := by
  apply Measurable.of_eval
  intro j
  exact ((hBm _).measurable.sub (hBm _).measurable).div_const _

lemma ValueStrip.mesh_energy_memLp {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T) (h : ValueStrip T γ V K L) (N : ℕ) :
    MemLp (valueMeshEnergy T N γ V N) 2 (gaussianProduct (Fin (N+1))) := by
  have hu (j : ℕ) (hj : j ≤ N) : Measurable (deriv (V (meshTime T N j))) :=
    ((h.smooth _ (mesh_time_mem_total hT hj)).continuous_deriv (by norm_num)).measurable
  apply memLp_finsetSum
  intro j hj
  have hjN : j<N := Finset.mem_range.mp hj
  apply MemLp.const_mul
  apply MemLp.of_bound
    (((hu j hjN.le).comp (measurable_euler T N γ (fun t ↦ deriv (V t))
      (fun i hi ↦ hu i hi.le) j hjN.le)).pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),sq_le_one_iff_abs_le_one]
  exact h.bounded _ (mesh_time_mem_total hT hjN.le) _

lemma ValueStrip.feedback_payoff_approximation
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (h : ValueStrip T γ V K L) (hγM : Measurable γ)
    {N : ℕ} (hN : 0<N) :
    |(∫ ω, V T (controlState B γ (feedbackControl B γ V T N) 0 T ω)-
      (1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω ∂μ)-
      ((∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N) ∂gaussianProduct (Fin (N+1)))-
        ∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)))| ≤
      (3/2 : ℝ)*stepSize T N*(γ T-γ 0) := by
  let α := feedbackControl B γ V T N
  let Z := coupledCoordinates T N B
  let F := fun ω ↦ V T (controlState B γ α 0 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω
  let G := fun ω ↦ V T (coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω)-
    valueMeshEnergy T N γ V N (Z ω)
  have ht : T∈Icc (0 : ℝ) T := ⟨hT.le,le_rfl⟩
  have hα := h.feedback_progressive hBm hT hN
  have hαb := h.feedback_bound B hT.le N
  have hγb (t : ℝ) (ht : t∈Icc (0 : ℝ) T) : |γ t| ≤ γ T := by
    rw [abs_of_nonneg (h.gamma_nonneg t ht)]
    exact h.gamma_mono ht ⟨hT.le,le_rfl⟩ ht.2
  have hXi := controlState_memLp_two hB hBm hα hαb hγM hγb 0 hT.le le_rfl
  have hVi := (h.value_memLp ht hXi).integrable (by norm_num)
  have hAi := controlAccum_integrable (μ := μ) hα hαb hγM hγb 2 hT.le le_rfl
  have hFi : Integrable F μ := hVi.sub (hAi.const_mul (1/2))
  have huc (j : ℕ) (hj : j ≤ N) : Measurable (deriv (V (meshTime T N j))) :=
    ((h.smooth _ (mesh_time_mem_total hT.le hj)).continuous_deriv (by norm_num)).measurable
  have hY := euler_memLp T N γ (fun t ↦ deriv (V t)) (fun j hj ↦ huc j hj.le)
    (fun j hj x ↦ h.bounded _ (mesh_time_mem_total hT.le hj.le) x) N le_rfl
  have hV := h.value_memLp ht hY
  have hE := h.mesh_energy_memLp hT.le N
  have hZlaw := coupledCoordinates_hasLaw hB hT hN
  have hZmp := hZlaw.measurePreserving (coupledCoordinates_measurable hBm T N)
  have hGi : Integrable G μ := by
    have hh := ((hV.sub hE).comp_measurePreserving hZmp).integrable (by norm_num)
    simpa only [G,Z,Function.comp_def,Pi.sub_apply,coupledEuler,ite_eq_right hN.ne'] using hh
  have hGint : (∫ ω, G ω ∂μ)=
      (∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N) ∂gaussianProduct (Fin (N+1)))-
        ∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1)) := by
    have hh := hZlaw.integral_comp (hV.sub hE).aestronglyMeasurable
    simp only [Function.comp_def,Pi.sub_apply] at hh
    rw [integral_sub (hV.integrable (by norm_num)) (hE.integrable (by norm_num))] at hh
    simpa only [G,Z,Function.comp_def,Pi.sub_apply,coupledEuler,ite_eq_right hN.ne'] using hh
  have hbound : ∀ᵐ ω ∂μ, |F ω-G ω| ≤ (3/2 : ℝ)*stepSize T N*(γ T-γ 0) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    have hS := h.feedback_state_error B hT hN ω hω
    have hE := h.feedback_energy_error B hT hN ω
    have hVl := (h.value_lipschitz ht).dist_le_mul
      (controlState B γ α 0 T ω) (coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω)
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hVl
    have hh := abs_sub_le (F ω-G ω)
      (V T (controlState B γ α 0 T ω)-V T (coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω)) 0
    have hid : (F ω-G ω)-
      (V T (controlState B γ α 0 T ω)-V T (coupledEuler T γ (fun t ↦ deriv (V t)) B N N ω)) =
        -((1/2 : ℝ)*controlAccum γ α 2 T ω-valueMeshEnergy T N γ V N (Z ω)) := by
      dsimp [F,G]
      ring
    rw [hid,abs_neg,sub_zero,sub_zero] at hh
    linarith
  rw [←hGint,←integral_sub hFi hGi]
  have hh := abs_integral_le_integral_abs (μ := μ) (f := fun ω ↦ F ω-G ω)
  have hj := integral_mono_ae (hFi.sub hGi).abs
    (integrable_const ((3/2 : ℝ)*stepSize T N*(γ T-γ 0))) hbound
  have hc : (∫ _ : Ω, (3/2 : ℝ)*stepSize T N*(γ T-γ 0) ∂μ)=
      (3/2 : ℝ)*stepSize T N*(γ T-γ 0) := by simp
  exact hh.trans (hj.trans_eq hc)

lemma ValueStrip.feedback_payoff_tendsto
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) (hγM : Measurable γ) :
    Tendsto (fun N ↦ ∫ ω, V T (controlState B γ (feedbackControl B γ V T N) 0 T ω)-
      (1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω ∂μ)
      atTop (𝓝 (V 0 0)) := by
  let p := fun N ↦ ∫ ω, V T (controlState B γ (feedbackControl B γ V T N) 0 T ω)-
      (1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω ∂μ
  let q := fun N ↦ (∫ z, V T (euler T N γ (fun t ↦ deriv (V t)) z N)
      ∂gaussianProduct (Fin (N+1)))-
      ∫ z, valueMeshEnergy T N γ V N z ∂gaussianProduct (Fin (N+1))
  have hs : Tendsto (fun N : ℕ ↦ stepSize T N) atTop (𝓝 0) := by
    simpa only [stepSize,mul_zero,div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) :
        Tendsto (fun N : ℕ ↦ T*(N : ℝ)⁻¹) atTop (𝓝 (T*0)))
  have hpq : Tendsto (fun N ↦ p N-q N) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun N ↦ (3/2 : ℝ)*stepSize T N*(γ T-γ 0))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      simpa only [Real.norm_eq_abs,p,q] using h.feedback_payoff_approximation hB hBm hT hγM hN
    · simpa using (hs.const_mul (3/2 : ℝ)).mul_const (γ T-γ 0)
  have hq : Tendsto q atTop (𝓝 (V 0 0)) := by
    have hh := (value_mesh_expectation_error_tendsto hT hT1 h).add_const (V 0 0)
    convert hh using 1
    · ext N
      dsimp only [q]
      ring
    · simp
  have hh := hpq.add hq
  simpa only [sub_add_cancel,zero_add,p] using hh

theorem ValueStrip.progressive_control_value
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ)
    (hBm : ∀ t, StronglyMeasurable (B t))
    {T K L : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (hT : 0<T) (hT1 : T≤1) (h : ValueStrip T γ V K L) (hγM : Measurable γ) :
    sSup {r | ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B hBm) α ∧ (∀ s ω, |α s ω|≤1) ∧
      r = ∫ ω, V T (controlState B γ α 0 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω ∂μ}
      = V 0 0 := by
  let S := {r | ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B hBm) α ∧ (∀ s ω, |α s ω|≤1) ∧
      r = ∫ ω, V T (controlState B γ α 0 T ω)-(1/2 : ℝ)*controlAccum γ α 2 T ω ∂μ}
  have hb : ∀ r∈S, r≤V 0 0 := by
    rintro r ⟨α,hα,hαb,rfl⟩
    exact h.progressive_control_upper hB hBm hT hT1 hγM hα hαb 0
  have hp (N : ℕ) (hN : 0<N) :
      (∫ ω, V T (controlState B γ (feedbackControl B γ V T N) 0 T ω)-
        (1/2 : ℝ)*controlAccum γ (feedbackControl B γ V T N) 2 T ω ∂μ)∈S :=
    ⟨_,h.feedback_progressive hBm hT hN,h.feedback_bound B hT.le N,rfl⟩
  apply le_antisymm
  · exact csSup_le ⟨_,hp 1 (by norm_num)⟩ hb
  · apply le_of_tendsto (h.feedback_payoff_tendsto hB hBm hT hT1 hγM)
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact le_csSup ⟨V 0 0,hb⟩ (hp N hN)

end SKValue

end

end OAI
end

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
-- module Solutions.OAIQ4_Sk.SKValue_Evolution_EvolutionShift
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

lemma deriv_const_add_eq (f : ℝ → ℝ) (x : ℝ) :
    deriv (fun y ↦ f (x+y))=fun y ↦ deriv f (x+y) :=
  funext (deriv_comp_const_add f x)

lemma BoundedSmooth.translate {f : ℝ → ℝ} (hf : BoundedSmooth f) (x : ℝ) :
    BoundedSmooth (fun y ↦ f (x+y)) := by
  refine ⟨hf.smooth.comp (contDiff_const.add contDiff_id),?_⟩
  intro n
  obtain ⟨C,hC,hb⟩ := hf.bound n
  refine ⟨C,hC,?_⟩
  simpa only [iteratedDeriv_comp_const_add] using fun y ↦ hb (x+y)

lemma SmoothTerminal.translate {f : ℝ → ℝ} (hf : SmoothTerminal f) (x : ℝ) :
    SmoothTerminal (fun y ↦ f (x+y)) := by
  refine ⟨?_,hf.smooth.comp (contDiff_const.add contDiff_id),?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [Real.dist_eq,add_sub_add_left_eq_sub,NNReal.coe_one,one_mul] using hf.lipschitz.dist_le_mul (x+y) (x+z)
  · rw [deriv_const_add_eq]
    exact hf.jets.translate x

lemma SmoothEvolution.space_translate {T : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (x : ℝ) :
    SmoothEvolution T γ (fun t y ↦ V t (x+y)) := by
  refine ⟨fun t ht ↦ (h.slices t ht).translate x,fun y ↦ h.continuous_value (x+y),?_,?_,?_,?_,?_⟩
  · intro n y
    simpa only [deriv_const_add_eq,iteratedDeriv_comp_const_add] using h.continuous_jet n (x+y)
  · intro n
    obtain ⟨C,hC,hb⟩ := h.bound n
    exact ⟨C,hC,by simpa only [deriv_const_add_eq,iteratedDeriv_comp_const_add] using fun t ht y ↦ hb t ht (x+y)⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := h.temporal n
    exact ⟨C,hC,by simpa only [deriv_const_add_eq,iteratedDeriv_comp_const_add] using fun s hs t ht y ↦ hb s hs t ht (x+y)⟩
  · intro t ht s hs y
    simpa only [deriv_const_add_eq] using h.value_pde t ht s hs (x+y)
  · intro t ht s hs y
    simpa only [deriv_const_add_eq] using h.gradient_pde t ht s hs (x+y)

lemma SmoothEvolution.time_shift {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (ha : 0≤a) (hab : a≤b) (hb : b≤T) :
    SmoothEvolution (b-a) (fun t ↦ γ (a+t)) (fun t ↦ V (a+t)) := by
  have hmem (t : ℝ) (ht : t∈Icc (0 : ℝ) (b-a)) : a+t∈Icc (0 : ℝ) T := by
    apply (ordConnected_Icc : OrdConnected (Icc (0 : ℝ) T)).out
      ⟨ha,hab.trans hb⟩ ⟨ha.trans hab,hb⟩
    constructor <;> linarith [ht.1,ht.2]
  refine ⟨fun t ht ↦ h.slices _ (hmem t ht),?_,?_,?_,?_,?_,?_⟩
  · intro x
    exact (h.continuous_value x).comp (continuous_const.add continuous_id).continuousOn hmem
  · intro n x
    exact (h.continuous_jet n x).comp (continuous_const.add continuous_id).continuousOn hmem
  · intro n
    obtain ⟨C,hC,hb⟩ := h.bound n
    exact ⟨C,hC,fun t ht ↦ hb _ (hmem t ht)⟩
  · intro n
    obtain ⟨C,hC,hb⟩ := h.temporal n
    refine ⟨C,hC,?_⟩
    intro s hs t ht x
    simpa only [add_sub_add_left_eq_sub] using hb _ (hmem s hs) _ (hmem t ht) x
  · intro t ht s hs x
    rw [intervalIntegral.integral_comp_add_left
      (fun r ↦ (1/2 : ℝ)*deriv (deriv (V r)) x+γ r*((1/2 : ℝ)*(deriv (V r) x)^2)) a]
    exact h.value_pde _ (hmem t ht) _ (hmem s hs) x
  · intro t ht s hs x
    rw [intervalIntegral.integral_comp_add_left
      (fun r ↦ (1/2 : ℝ)*deriv (deriv (deriv (V r))) x+γ r*(deriv (V r) x*deriv (deriv (V r)) x)) a]
    exact h.gradient_pde _ (hmem t ht) _ (hmem s hs) x

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

lemma profileCoeff_nonneg (l : HeatProfile) (t : ℝ) : 0≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact le_rfl
  | cons p l ih =>
    change 0≤patchTime _ _ _ t
    by_cases ht : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ ht]
      exact p.2.coe_nonneg
    · rw [patchTime_right _ _ (lt_of_not_ge ht)]
      exact ih _

lemma profileCoeff_integrable (l : HeatProfile) :
    IntervalIntegrable (profileCoeff l) volume 0 (profileTime l) := by
  induction l with
  | nil => exact intervalIntegrable_const
  | cons p l ih =>
    exact patchTime_intervalIntegrable p.1.coe_nonneg (profileTime_nonneg l) intervalIntegrable_const ih

lemma profileCoeff_measurable (l : HeatProfile) : Measurable (profileCoeff l) := by
  induction l with
  | nil => exact measurable_const
  | cons p l ih =>
    unfold profileCoeff patchTime
    exact Measurable.ite measurableSet_Iic measurable_const (ih.comp (measurable_id.sub measurable_const))

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

lemma profileCoeff_lower {l : HeatProfile} {c : ℝ}
    (hc : ∀ p∈l, c≤(p.2 : ℝ)) {t : ℝ} (ht : t∈Ioc (0 : ℝ) (profileTime l)) :
    c≤profileCoeff l t := by
  induction l generalizing t with
  | nil => exact (not_lt_of_ge ht.2 ht.1).elim
  | cons p l ih =>
    change c≤patchTime (p.1 : ℝ) _ _ t
    by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hta]
      exact hc p (by simp)
    · rw [patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih (fun q hq ↦ hc q (by simp [hq]))
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩

lemma profileCoeff_mono {l : HeatProfile} (hl : l.Pairwise (fun p q ↦ p.2≤q.2)) :
    MonotoneOn (profileCoeff l) (Icc (0 : ℝ) (profileTime l)) := by
  induction l with
  | nil => intro s hs t ht hst; exact le_rfl
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp hl
    intro s hs t ht hst
    change patchTime (p.1 : ℝ) _ _ s≤patchTime (p.1 : ℝ) _ _ t
    by_cases hsa : s≤(p.1 : ℝ) <;> by_cases hta : t≤(p.1 : ℝ)
    · rw [patchTime_left _ _ hsa,patchTime_left _ _ hta]
    · rw [patchTime_left _ _ hsa,patchTime_right _ _ (lt_of_not_ge hta)]
      apply profileCoeff_lower (fun q hq ↦ by exact_mod_cast hp q hq)
      exact ⟨sub_pos.mpr (lt_of_not_ge hta),by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
    · exact (hsa (hst.trans hta)).elim
    · rw [patchTime_right _ _ (lt_of_not_ge hsa),patchTime_right _ _ (lt_of_not_ge hta)]
      apply ih hl
      · exact ⟨by linarith,by have hsu : s≤(p.1 : ℝ)+profileTime l := hs.2; linarith⟩
      · exact ⟨by linarith,by have htu : t≤(p.1 : ℝ)+profileTime l := ht.2; linarith⟩
      · linarith

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_FiniteStepControl
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

lemma SmoothEvolution.progressive_control_from
    {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBm : ∀ s, StronglyMeasurable (B s))
    {T a b : ℝ} {γ : ℝ → ℝ} {V : ℝ → ℝ → ℝ}
    (h : SmoothEvolution T γ V) (ha : 0≤a) (hab : a<b) (hb : b≤T) (hd : b-a≤1)
    (hγ : ∀ t∈Icc (0 : ℝ) T, 0≤γ t) (hm : MonotoneOn γ (Icc (0 : ℝ) T))
    (hM : Measurable γ) (x : ℝ) :
    sSup {r | ∃ α : ℝ≥0 → Ω → ℝ,
      IsProgressive (Filtration.natural B hBm) α ∧ (∀ s ω, |α s ω|≤1) ∧
      r=∫ ω, V b (x+controlState B (fun s ↦ γ (a+s)) α 0 (b-a) ω)-
        (1/2 : ℝ)*controlAccum (fun s ↦ γ (a+s)) α 2 (b-a) ω ∂μ} = V a x := by
  have hmem (s : ℝ) (hs : s∈Icc (0 : ℝ) (b-a)) : a+s∈Icc (0 : ℝ) T := by
    constructor <;> linarith [hs.1,hs.2]
  obtain ⟨K,L,hstrip⟩ := ((h.time_shift ha hab.le hb).space_translate x).toValueStrip
    (sub_nonneg.mpr hab.le) (fun s hs ↦ hγ _ (hmem s hs))
    (fun s hs t ht hst ↦ hm (hmem s hs) (hmem t ht) (add_le_add le_rfl hst))
  have he := hstrip.progressive_control_value hB hBm (sub_pos.mpr hab) hd
    (hM.comp (measurable_const.add measurable_id))
  simpa only [add_sub_cancel,add_zero] using he

theorem SmoothTerminal.profile_control_from (W : BrownianSpace)
    {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {l : HeatProfile}
    (hl : l.Pairwise (fun p q ↦ p.2≤q.2)) (hT : profileTime l=1)
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) (x : ℝ) :
    sSup {r | ∃ α : ℝ≥0 → W.Ω → ℝ, Admissible W t α ∧
      r=∫ ω, ψ (x+W.B 1 ω-W.B t.toNNReal ω+
        ∫ s in (0 : ℝ)..(1-t), profileCoeff l (t+s)*α s.toNNReal ω)-
        (1/2 : ℝ)*(∫ s in (0 : ℝ)..(1-t), profileCoeff l (t+s)*(α s.toNNReal ω)^2) ∂W.μ} =
      profileValue ψ l t x := by
  let B := fun s ω ↦ W.B (t.toNNReal+s) ω-W.B t.toNNReal ω
  have hm : ∀ s, StronglyMeasurable (B s) := fun s ↦ (W.measurable _).sub (W.measurable _)
  have he := (hψ.profile_evolution l).progressive_control_from
    (W.brownian.toIsPreBrownianReal.shift t.toNNReal) hm ht.1 ht.2 (by rw [hT])
    (by linarith [ht.1]) (fun s _ ↦ profileCoeff_nonneg l s) (profileCoeff_mono hl)
    (profileCoeff_measurable l) x
  have hend : t.toNNReal+(1-t).toNNReal=1 := by
    apply NNReal.eq
    simp only [NNReal.coe_add,Real.coe_toNNReal _ ht.1,Real.coe_toNNReal _ (sub_nonneg.mpr ht.2.le),NNReal.coe_one]
    ring
  have hv : profileValue ψ l 1=ψ := hT ▸ profileValue_terminal ψ l
  change sSup {r | ∃ α, Admissible W t α ∧ r=_}= _
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext r
  simp only [Admissible,shiftedFiltration,and_assoc,hv,controlState,controlAccum,pow_one,zero_add,
    sub_eq_add_neg,add_assoc]
  simp only [←sub_eq_add_neg,hend]

end SKValue

end

end OAI
end

section
-- module Solutions.OAIQ4_Sk.SKValue_Control_SupStability
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

lemma elapsed_values_nonempty {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω)
    (f : Filtration ℝ≥0 m) (Z : Ω → ℝ) (ψ γ : ℝ → ℝ) (T x : ℝ) :
    {r | ∃ α, IsProgressive f α ∧ (∀ s ω, |α s ω|≤1) ∧ r=elapsedPayoff μ Z ψ γ T x α}.Nonempty := by
  exact ⟨_,fun _ _ ↦ 0,fun _ ↦ measurable_const,by norm_num,rfl⟩

lemma elapsed_values_bddAbove {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f : Filtration ℝ≥0 m)
    {Z : Ω → ℝ} {ψ γ : ℝ → ℝ} {T x : ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hγ : Measurable γ)
    (hi : IntervalIntegrable γ volume 0 T) (hT : 0≤T) :
    BddAbove {r | ∃ α, IsProgressive f α ∧ (∀ s ω, |α s ω|≤1) ∧ r=elapsedPayoff μ Z ψ γ T x α} := by
  refine ⟨(∫ ω, ψ (x+Z ω) ∂μ)+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s|),?_⟩
  rintro r ⟨α,hα,hαb,rfl⟩
  have hd := elapsedPayoff_difference_bound hZ hψ hψ (fun y ↦ by simp : ∀ y, |ψ y-ψ y|≤(0 : ℝ))
    hα hαb hγ measurable_const hi intervalIntegrable_const hT (x := x) (η := fun _ ↦ 0)
  simp only [elapsedPayoff,controlAccum,zero_mul,intervalIntegral.integral_zero,mul_zero,add_zero,sub_zero,zero_add] at hd
  have hh := (le_abs_self _).trans hd
  change elapsedPayoff μ Z ψ γ T x α≤_
  change elapsedPayoff μ Z ψ γ T x α-(∫ ω, ψ (x+Z ω) ∂μ)≤_ at hh
  linarith

lemma elapsedValue_sub_le {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Filtration ℝ≥0 m}
    {Z : Ω → ℝ} {ψ χ γ η : ℝ → ℝ} {T x ε : ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    (hε : ∀ y, |ψ y-χ y|≤ε) (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T) (hT : 0≤T) :
    elapsedValue μ f Z ψ γ T x≤elapsedValue μ f Z χ η T x+
      (ε+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s-η s|)) := by
  apply csSup_le (elapsed_values_nonempty μ f Z ψ γ T x)
  rintro r ⟨α,hα,hαb,rfl⟩
  have hd := (le_abs_self _).trans (elapsedPayoff_difference_bound hZ hψ hχ hε hα hαb hγ hη hiγ hiη hT (x := x))
  have hu : elapsedPayoff μ Z χ η T x α≤elapsedValue μ f Z χ η T x :=
    le_csSup (elapsed_values_bddAbove f hZ hχ hη hiη hT) ⟨α,hα,hαb,rfl⟩
  linarith

lemma elapsedValue_difference_bound {Ω : Type*} [m : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Filtration ℝ≥0 m}
    {Z : Ω → ℝ} {ψ χ γ η : ℝ → ℝ} {T x ε : ℝ}
    (hZ : MemLp Z 2 μ) (hψ : LipschitzWith 1 ψ) (hχ : LipschitzWith 1 χ)
    (hε : ∀ y, |ψ y-χ y|≤ε) (hγ : Measurable γ) (hη : Measurable η)
    (hiγ : IntervalIntegrable γ volume 0 T) (hiη : IntervalIntegrable η volume 0 T) (hT : 0≤T) :
    |elapsedValue μ f Z ψ γ T x-elapsedValue μ f Z χ η T x|≤
      ε+(3/2 : ℝ)*(∫ s in (0 : ℝ)..T, |γ s-η s|) := by
  have h1 := elapsedValue_sub_le (f := f) hZ hψ hχ hε hγ hη hiγ hiη hT (x := x)
  have h2 := elapsedValue_sub_le (f := f) hZ hχ hψ (fun y ↦ by rw [abs_sub_comm]; exact hε y) hη hγ hiη hiγ hT (x := x)
  simp_rw [abs_sub_comm (η _) (γ _)] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

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

lemma gridProfile_sample {d : ℝ≥0} {f : ℕ → ℝ≥0} {j n : ℕ}
    (hn : 0<n) {t : ℝ} (ht : t∈Icc (0 : ℝ) ((n : ℝ)*d)) :
    ∃ i, j ≤ i ∧ i<j+n ∧
      profileCoeff (gridProfile d f j n) t=(f i : ℝ) ∧
      0 ≤ (j : ℝ)*d+t-(i : ℝ)*d ∧ (j : ℝ)*d+t-(i : ℝ)*d ≤ d := by
  induction n generalizing j t with
  | zero => omega
  | succ n ih =>
    by_cases htd : t ≤ (d : ℝ)
    · refine ⟨j,le_rfl,by omega,?_,?_,?_⟩
      · exact patchTime_left _ _ htd
      · linarith [ht.1]
      · linarith
    · have hd : (d : ℝ)<t := lt_of_not_ge htd
      have hn' : 0<n := by
        by_contra hh
        have hn0 : n=0 := by omega
        subst n
        simp only [Nat.cast_one,zero_add,one_mul] at ht
        exact htd ht.2
      have ht' : t-(d : ℝ)∈Icc (0 : ℝ) ((n : ℝ)*d) := by
        constructor
        · linarith
        · have hu := ht.2
          rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul] at hu
          linarith
      obtain ⟨i,hij,hin,hc,hlo,hhi⟩ := ih hn' ht' (j := j+1)
      refine ⟨i,by omega,by omega,?_,?_,?_⟩
      · change patchTime (d : ℝ) _ _ t=_
        rw [patchTime_right _ _ hd]
        exact hc
      · simp only [Nat.cast_add,Nat.cast_one] at hlo
        nlinarith
      · simp only [Nat.cast_add,Nat.cast_one] at hhi
        nlinarith

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

lemma log_two_cosh_bounds (z : ℝ) : |z|≤Real.log (2*Real.cosh z) ∧
    Real.log (2*Real.cosh z)≤|z|+Real.log 2 := by
  have he : 2*Real.cosh z=Real.exp z+Real.exp (-z) := by rw [Real.cosh_eq]; ring
  have h1 : Real.exp |z|≤Real.exp z+Real.exp (-z) := by
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz]
      linarith [Real.exp_pos (-z)]
    · rw [abs_of_nonpos hz]
      linarith [Real.exp_pos z]
  have h2 : Real.exp z+Real.exp (-z)≤2*Real.exp |z| := by
    have hh1 := Real.exp_le_exp.mpr (le_abs_self z)
    have hh2 := Real.exp_le_exp.mpr (neg_le_abs z)
    linarith
  constructor
  · have hh := Real.log_le_log (Real.exp_pos |z|) h1
    simpa only [←he,Real.log_exp] using hh
  · have hh := Real.log_le_log (add_pos (Real.exp_pos z) (Real.exp_pos (-z))) h2
    rw [Real.log_mul (by norm_num) (Real.exp_pos |z|).ne',Real.log_exp,←he] at hh
    linarith

lemma logCoshTerminal_uniform_error {M : ℝ} (hM : 0<M) (x : ℝ) :
    |logCoshTerminal M x - abs x| ≤ Real.log 2/M := by
  obtain ⟨hl,hu⟩ := log_two_cosh_bounds (M*x)
  rw [abs_mul,abs_of_pos hM] at hl hu
  have hl' : |x|≤logCoshTerminal M x := by
    apply (le_div_iff₀ hM).mpr
    simpa only [mul_comm] using hl
  rw [abs_of_nonneg (sub_nonneg.mpr hl')]
  apply (sub_le_iff_le_add).mpr
  change Real.log (2*Real.cosh (M*x))/M≤_+|x|
  apply (div_le_iff₀ hM).mpr
  field_simp
  nlinarith

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

lemma controlIntegral_eq_accum (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (α : ℝ≥0 → W.Ω → ℝ) (k : ℕ) (ω : W.Ω) :
    controlIntegral γ t α k ω=controlAccum (fun s ↦ γ.cutoff (t+s)) α k (1-t) ω := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (sub_nonneg.mpr ht.2)] at hs
  dsimp only
  rw [limitedControl_eq α (by linarith [hs.2,ht.1])]

lemma phi_eq_elapsedValue (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    phi W γ t x=elapsedValue W.μ (shiftedFiltration W t)
      (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω) abs (fun s ↦ γ.cutoff (t+s)) (1-t) x := by
  unfold phi elapsedValue
  congr 1
  ext r
  simp only [Admissible,and_assoc,controlPayoff_eq W γ ht,
    controlIntegral_eq_accum W γ ht,elapsedPayoff]

lemma SmoothTerminal.profile_elapsedValue (W : BrownianSpace)
    {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {l : HeatProfile}
    (hl : l.Pairwise (fun p q ↦ p.2 ≤ q.2)) (hT : profileTime l=1)
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) (x : ℝ) :
    elapsedValue W.μ (shiftedFiltration W t) (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω)
      ψ (fun s ↦ profileCoeff l (t+s)) (1-t) x=profileValue ψ l t x := by
  rw [← hψ.profile_control_from W hl hT ht x]
  unfold elapsedValue
  congr 1
  ext r
  simp only [elapsedPayoff,Admissible,controlAccum,pow_one,and_assoc,
    sub_eq_add_neg,add_assoc]

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
lemma profileCoeff_append_before (l r:HeatProfile) {t:ℝ}
    (ht:t∈Ioc (0:ℝ) (profileTime l)) : profileCoeff (l++r) t=profileCoeff l t := by
  induction l generalizing t with
  | nil => exact (not_lt_of_ge ht.2 ht.1).elim
  | cons p l ih =>
    change patchTime (p.1:ℝ) _ _ t=patchTime (p.1:ℝ) _ _ t
    by_cases hp:t≤(p.1:ℝ)
    · rw [patchTime_left _ _ hp,patchTime_left _ _ hp]
    · rw [patchTime_right _ _ (lt_of_not_ge hp),patchTime_right _ _ (lt_of_not_ge hp)]
      apply ih
      constructor
      · exact sub_pos.mpr (lt_of_not_ge hp)
      · have htu:t≤(p.1:ℝ)+profileTime l := ht.2
        linarith

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma profileCoeff_append_after (l r:HeatProfile) {s:ℝ} (hs:profileTime l < s) :
    profileCoeff (l++r) s=profileCoeff r (s-profileTime l) := by
  induction l generalizing s with
  | nil => simp only [List.nil_append,profileTime,sub_zero]
  | cons p l ih =>
    have hp:(p.1:ℝ) < s := (le_add_of_nonneg_right (profileTime_nonneg l)).trans_lt hs
    change patchTime (p.1:ℝ) _ _ s=_
    rw [patchTime_right _ _ hp]
    have he:profileTime l < s-(p.1:ℝ) := by change (p.1:ℝ)+profileTime l < s at hs;linarith
    change profileCoeff (l++r) (s-(p.1:ℝ))=profileCoeff r (s-profileTime (p::l))
    rw [ih he]
    congr 1
    change s-(p.1:ℝ)-profileTime l=s-((p.1:ℝ)+profileTime l)
    ring

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
lemma OrderParameter.splitSegment_sample (γ:OrderParameter) {a b s:ℝ}
    (ha:0≤a) (hab:a<b) (hb:b≤1) (n:ℕ) (hs:s∈Icc (0:ℝ) (b-a)) :
    ∃ r∈Ico (0:ℝ) 1, a ≤ r ∧ r<b ∧
      profileCoeff (γ.splitSegment a b hab.le n) s=γ.coeff r+(gridDelta n:ℝ) ∧
      r≤a+s ∧ a+s-r≤(splitLength a b hab.le n:ℝ) := by
  obtain ⟨i,hi,hin,hc,hlo,hhi⟩:=gridProfile_sample (d:=splitLength a b hab.le n)
    (f:=fun i ↦ (γ.coeff (a+(i:ℝ)*(splitLength a b hab.le n))).toNNReal+gridDelta n)
    (j:=0) (Nat.succ_pos n) (by simpa only [splitLength_mul] using hs)
  have hr:=split_sample_mem ha hab hb (show i<n+1 by omega)
  have hd:0<(splitLength a b hab.le n:ℝ) := div_pos (sub_pos.mpr hab) (by positivity)
  have hi':(i:ℝ)<(n+1:ℕ) := by exact_mod_cast (show i<n+1 by omega)
  have ht:=mul_lt_mul_of_pos_right hi' hd
  rw [splitLength_mul] at ht
  refine ⟨a+(i:ℝ)*(splitLength a b hab.le n),hr,le_add_of_nonneg_right (by positivity),by linarith,?_,?_,?_⟩
  · simpa only [OrderParameter.splitSegment,NNReal.coe_add,Real.coe_toNNReal _ (γ.nonneg _ hr)] using hc
  · simp only [Nat.cast_zero,zero_mul,zero_add] at hlo;linarith
  · simp only [Nat.cast_zero,zero_mul,zero_add] at hhi;linarith

lemma OrderParameter.splitGrid_time (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    profileTime (γ.splitGrid t n)=1 := by
  rw [OrderParameter.splitGrid,profileTime_append,γ.splitSegment_time,γ.splitSegment_time]
  ring
lemma OrderParameter.splitGrid_mono (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    (γ.splitGrid t n).Pairwise (fun p q ↦ p.2≤q.2) := by
  rw [OrderParameter.splitGrid,List.pairwise_append]
  refine ⟨γ.splitSegment_mono le_rfl t.property.1 t.property.2.le n,
    γ.splitSegment_mono t.property.1.le t.property.2 le_rfl n,?_⟩
  intro p hp q hq
  obtain ⟨i,_,hi,rfl⟩:=gridProfile_mem hp
  obtain ⟨j,_,hj,rfl⟩:=gridProfile_mem hq
  apply add_le_add _ le_rfl
  apply Real.toNNReal_mono
  have hir:=split_sample_mem (a:=0) le_rfl t.property.1 t.property.2.le (show i<n+1 by omega)
  have hjr:=split_sample_mem t.property.1.le t.property.2 le_rfl (show j<n+1 by omega)
  apply γ.monotone hir hjr
  have hi':(i:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show i≤n+1 by omega)
  have hle:=mul_le_mul_of_nonneg_right hi' (splitLength 0 t t.property.1.le n).coe_nonneg
  rw [splitLength_mul] at hle
  have hj0:0≤(j:ℝ)*(splitLength t 1 t.property.2.le n) := by positivity
  linarith
lemma OrderParameter.splitGrid_sample (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    ∃ r∈Ico (0:ℝ) 1,profileCoeff (γ.splitGrid t n) s=γ.coeff r+(gridDelta n:ℝ) ∧
      r ≤ s ∧ s-r ≤ (gridDelta n:ℝ) := by
  have hd:0<(n+1:ℝ) := by positivity
  by_cases hst:s≤t
  · have he:profileCoeff (γ.splitGrid t n) s=profileCoeff (γ.splitSegment 0 t t.property.1.le n) s := by
      rcases hs.1.eq_or_lt with rfl | hs0
      · change patchTime _ _ _ 0=patchTime _ _ _ 0
        rw [patchTime_left _ _ (splitLength 0 t t.property.1.le n).coe_nonneg,
          patchTime_left _ _ (splitLength 0 t t.property.1.le n).coe_nonneg]
      · exact profileCoeff_append_before _ _ ⟨hs0,by simpa only [γ.splitSegment_time,sub_zero] using hst⟩
    obtain ⟨r,hr,_,_,hc,hrs,hclose⟩:=γ.splitSegment_sample le_rfl t.property.1 t.property.2.le n
      (show s∈Icc (0:ℝ) ((t:ℝ)-0) by exact ⟨hs.1,by simpa only [sub_zero] using hst⟩)
    refine ⟨r,hr,he.trans hc,by simpa only [zero_add] using hrs,?_⟩
    have hlen:(splitLength 0 t t.property.1.le n:ℝ)≤gridDelta n :=
      div_le_div_of_nonneg_right (by simpa only [sub_zero] using t.property.2.le) hd.le
    simpa only [zero_add] using hclose.trans hlen
  · have ht:(t:ℝ) < s := lt_of_not_ge hst
    have he:profileCoeff (γ.splitGrid t n) s=profileCoeff (γ.splitSegment t 1 t.property.2.le n) (s-t) := by
      rw [OrderParameter.splitGrid,profileCoeff_append_after _ _ (by rw [γ.splitSegment_time,sub_zero];exact ht),γ.splitSegment_time,sub_zero]
    obtain ⟨r,hr,_,_,hc,hrs,hclose⟩:=γ.splitSegment_sample t.property.1.le t.property.2 le_rfl n
      (show s-(t:ℝ)∈Icc (0:ℝ) (1-t) by constructor <;> linarith [hs.2])
    refine ⟨r,hr,he.trans hc,?_,?_⟩
    · linarith
    · have hlen:(splitLength t 1 t.property.2.le n:ℝ)≤gridDelta n :=
        div_le_div_of_nonneg_right (by linarith [t.property.1]) hd.le
      linarith
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
open scoped Topology NNReal
namespace SKValue
lemma gridDelta_le_one (n:ℕ) : (gridDelta n:ℝ)≤1 := by
  change 1/(n+1:ℝ)≤1
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α:=ℝ) n]
lemma OrderParameter.splitGrid_le (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Ico (0:ℝ) 1) :
    profileCoeff (γ.splitGrid t n) s≤γ.coeff s+(gridDelta n:ℝ) := by
  obtain ⟨r,hr,he,hrs,_⟩:=γ.splitGrid_sample t n ⟨hs.1,hs.2.le⟩
  rw [he]
  exact add_le_add (γ.monotone hr hs hrs) le_rfl
lemma OrderParameter.splitGrid_tendsto (γ:OrderParameter) (t:Ioo (0:ℝ) 1)
    {s:ℝ} (hs:s∈Ico (0:ℝ) 1) (hc:ContinuousWithinAt γ.coeff (Ico (0:ℝ) 1) s) :
    Tendsto (fun n ↦ profileCoeff (γ.splitGrid t n) s) atTop (𝓝 (γ.coeff s)) := by
  choose r hr he hrs hdist using fun n ↦ γ.splitGrid_sample t n ⟨hs.1,hs.2.le⟩
  have hd:Tendsto (fun n ↦ dist (r n) s) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (hrs n))]
    exact hdist n
  have hl:=hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨(tendsto_iff_dist_tendsto_zero).mpr hd,Eventually.of_forall hr⟩)
  have hh:=hl.add tendsto_one_div_add_atTop_nhds_zero_nat
  have hh' : Tendsto (fun n ↦ γ.coeff (r n)+(gridDelta n:ℝ)) atTop (𝓝 (γ.coeff s)) := by
    change Tendsto (fun n ↦ γ.coeff (r n)+1/(n+1:ℝ)) atTop (𝓝 (γ.coeff s))
    simpa only [Function.comp_apply,add_zero] using hh
  exact hh'.congr (fun n ↦ (he n).symm)
lemma OrderParameter.splitError_tendsto (γ:OrderParameter) (t:Ioo (0:ℝ) 1) :
    Tendsto (γ.splitError t) atTop (𝓝 0) := by
  have hdom:∀ n,∀ᵐ s ∂volume,s∈uIoc (0:ℝ) 1 →
      ‖|profileCoeff (γ.splitGrid t n) s-γ.cutoff s|‖≤γ.cutoff s+1 := by
    intro n
    filter_upwards [Measure.ae_ne volume (1:ℝ)] with s hne hs
    rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hs
    have hs':s∈Ico (0:ℝ) 1 := ⟨hs.1.le,lt_of_le_of_ne hs.2 hne⟩
    have hlo:=profileCoeff_nonneg (γ.splitGrid t n) s
    have hup:=γ.splitGrid_le t n hs'
    have hg:=γ.nonneg s hs'
    rw [Real.norm_eq_abs,abs_abs,OrderParameter.cutoff,indicator_of_mem hs']
    apply abs_le.mpr
    constructor <;> linarith [gridDelta_le_one n]
  have hl:=intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a:=0) (b:=1) (μ:=volume) (l:=atTop) (f:=fun _ : ℝ ↦ (0:ℝ))
    (F:=fun n s ↦ |profileCoeff (γ.splitGrid t n) s-γ.cutoff s|) (fun s ↦ γ.cutoff s+1)
    (Eventually.of_forall (fun n ↦ ((profileCoeff_measurable _).sub γ.cutoff_measurable).abs.aestronglyMeasurable))
    (Eventually.of_forall hdom)
    (γ.cutoff_integrable.intervalIntegrable.add (intervalIntegrable_const)) (by
      filter_upwards [γ.monotone.countable_not_continuousWithinAt.ae_notMem volume,Measure.ae_ne volume (1:ℝ)] with s hc hne hs
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hs
      have hs':s∈Ico (0:ℝ) 1 := ⟨hs.1.le,lt_of_le_of_ne hs.2 hne⟩
      have hc':ContinuousWithinAt γ.coeff (Ico (0:ℝ) 1) s := by
        by_contra hh;exact hc ⟨hs',hh⟩
      have he:=((γ.splitGrid_tendsto t hs' hc').sub_const (γ.coeff s)).abs
      simpa only [OrderParameter.cutoff,indicator_of_mem hs',sub_self,abs_zero] using he)
  change Tendsto (fun n ↦ ∫ s in (0:ℝ)..1,|profileCoeff (γ.splitGrid t n) s-γ.cutoff s|) atTop (𝓝 0)
  simpa only [intervalIntegral.integral_zero] using hl
lemma OrderParameter.split_shift_error (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    (∫ r in (0:ℝ)..(1-s),|profileCoeff (γ.splitGrid t n) (s+r)-γ.cutoff (s+r)|)≤γ.splitError t n := by
  have hg:IntervalIntegrable (profileCoeff (γ.splitGrid t n)) volume 0 1 := by
    simpa only [γ.splitGrid_time] using profileCoeff_integrable (γ.splitGrid t n)
  have hi:IntervalIntegrable (fun r ↦ |profileCoeff (γ.splitGrid t n) r-γ.cutoff r|) volume 0 1 :=
    (hg.sub γ.cutoff_integrable.intervalIntegrable).abs
  have he:(∫ r in (0:ℝ)..(1-s),|profileCoeff (γ.splitGrid t n) (s+r)-γ.cutoff (s+r)|)=
      ∫ r in s..1,|profileCoeff (γ.splitGrid t n) r-γ.cutoff r| := by
    simpa only [add_zero,add_sub_cancel] using intervalIntegral.integral_comp_add_left
      (f:=fun r ↦ |profileCoeff (γ.splitGrid t n) r-γ.cutoff r|) (a:=0) (b:=1-s) s
  rw [he]
  exact intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl (Eventually.of_forall (fun _ ↦ abs_nonneg _)) hi
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ContDiff
namespace SKValue
lemma profileHeight_nonneg (l:HeatProfile) : 0 ≤ profileHeight l := by
  cases l with
  | nil => exact le_rfl
  | cons p l => exact p.2.coe_nonneg.trans (le_max_left _ _)
lemma splitSmoothParameter_pos (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    0 < splitSmoothParameter γ t n := add_pos_of_pos_of_nonneg (by positivity) (profileHeight_nonneg _)
lemma splitSmoothParameter_ge (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ) :
    n+1 ≤ splitSmoothParameter γ t n := le_add_of_nonneg_right (profileHeight_nonneg _)
lemma splitSmooth_value_bound (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) (n:ℕ)
    {s:ℝ} (hs:s∈Ico (0:ℝ) 1) (x:ℝ) :
    |splitSmooth γ t n s x-phi W γ s x| ≤ Real.log 2/(n+1:ℝ)+(3/2:ℝ)*γ.splitError t n := by
  have hZ:=brownian_increment_memLp W s
  have hψ:=logCoshTerminal_smoothTerminal (splitSmoothParameter_pos γ t n)
  have hm:Measurable (fun r:ℝ ↦ profileCoeff (γ.splitGrid t n) (s+r)) :=
    (profileCoeff_measurable _).comp (measurable_const.add measurable_id)
  have hi:IntervalIntegrable (fun r ↦ profileCoeff (γ.splitGrid t n) (s+r)) volume 0 (1-s) := by
    have hij:IntervalIntegrable (profileCoeff (γ.splitGrid t n)) volume s 1 := by
      apply (profileCoeff_integrable _).mono_set
      rw [γ.splitGrid_time,uIcc_of_le hs.2.le,uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc hs.1 le_rfl
    simpa only [sub_self] using hij.comp_add_left s
  have hic:IntervalIntegrable (fun r ↦ γ.cutoff (s+r)) volume 0 (1-s) := by
    simpa only [sub_self] using (γ.cutoff_integrable.intervalIntegrable (a:=s) (b:=1)).comp_add_left s
  have herror:∀ x,abs (logCoshTerminal (splitSmoothParameter γ t n) x-abs x) ≤ Real.log 2/(n+1:ℝ) := by
    intro x
    exact (logCoshTerminal_uniform_error (splitSmoothParameter_pos γ t n) x).trans
      (div_le_div_of_nonneg_left (Real.log_nonneg (by norm_num)) (by positivity) (splitSmoothParameter_ge γ t n))
  have he:=elapsedValue_difference_bound (f:=shiftedFiltration W s) hZ hψ.lipschitz
    (by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub a b)
    herror hm (γ.cutoff_measurable.comp (measurable_const.add measurable_id)) hi hic (sub_nonneg.mpr hs.2.le) (x:=x)
  dsimp only [Function.comp_def,Pi.add_apply,id_eq] at he
  rw [hψ.profile_elapsedValue W (γ.splitGrid_mono t n) (γ.splitGrid_time t n) hs x,
    ←phi_eq_elapsedValue W γ ⟨hs.1,hs.2.le⟩ x] at he
  change |splitSmooth γ t n s x-phi W γ s x| ≤ _ at he
  linarith [γ.split_shift_error t n ⟨hs.1,hs.2.le⟩]
lemma splitSmooth_tendsto_oai (W:BrownianSpace) (γ:OrderParameter) (t:Ioo (0:ℝ) 1) :
    TendstoUniformly (fun n (p:Ico (0:ℝ) 1×ℝ) ↦ splitSmooth γ t n p.1 p.2)
      (fun p ↦ phi W γ p.1 p.2) atTop := by
  have hl:Tendsto (fun n:ℕ ↦ Real.log 2/(n+1:ℝ)+(3/2:ℝ)*γ.splitError t n) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero,add_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.log 2)).add ((γ.splitError_tendsto t).const_mul (3/2:ℝ))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hl.eventually (gt_mem_nhds hε)] with n hn p
  rw [Real.dist_eq,abs_sub_comm]
  exact (splitSmooth_value_bound W γ t n p.1.property p.2).trans_lt hn
end SKValue

end

end OAI
end

theorem solution : type_of% @OAI.SKValue.splitSmooth_tendsto_oai := @OAI.SKValue.splitSmooth_tendsto_oai
