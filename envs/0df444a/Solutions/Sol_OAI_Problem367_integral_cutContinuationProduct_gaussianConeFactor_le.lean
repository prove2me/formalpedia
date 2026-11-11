-- Prove2me | solution 1 for OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:45:01.028617+00:00
-- url     : https://prove2.me/submissions/d0671309-d1da-4b87-8f60-b19efbe25d8a

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_ComponentSignalAttenuation_condDistrib_posteriorMean_root
import Theorems.Thm_OAI_Problem367_ComponentSignalAttenuation_condExp_attenuation_le_critical_of_condIndep
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_selectedPosterior_root_component

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem binaryFusion_abs_mul_lt_one {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : |u * v| < 1 := by
  rw [abs_mul]
  calc
    |u| * |v| ≤ |u| * 1 := mul_le_mul_of_nonneg_left hv.le (abs_nonneg u)
    _ < 1 := by simpa using hu

theorem binaryFusion_denominator_pos {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 < 1 + u * v := by
  have h := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).1
  linarith

theorem one_sub_binaryFusion_sq {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    1 - binaryFusion u v ^ 2 =
      (1 - u ^ 2) * (1 - v ^ 2) / (1 + u * v) ^ 2 := by
  have hd := ne_of_gt (binaryFusion_denominator_pos hu hv)
  unfold binaryFusion
  field_simp
  ring

theorem abs_binaryFusion_lt_one {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : |binaryFusion u v| < 1 := by
  apply (sq_lt_one_iff_abs_lt_one _).mp
  have hu' : 0 < 1 - u ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one u).mpr hu
    linarith
  have hv' : 0 < 1 - v ^ 2 := by
    have := (sq_lt_one_iff_abs_lt_one v).mpr hv
    linarith
  have hd := binaryFusion_denominator_pos hu hv
  have hpos : 0 < 1 - binaryFusion u v ^ 2 := by
    rw [one_sub_binaryFusion_sq hu hv]
    positivity
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_ArtanhFusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem tanh_add_eq_binaryFusion (a b : ℝ) :
    Real.tanh (a + b) = binaryFusion (Real.tanh a) (Real.tanh b) := by
  have ha : |Real.tanh a| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (Real.tanh_sq_lt_one a)
  have hb : |Real.tanh b| < 1 := (sq_lt_one_iff_abs_lt_one _).mp (Real.tanh_sq_lt_one b)
  apply (eq_div_iff (binaryFusion_denominator_pos ha hb).ne').2
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  simp only [Real.tanh_eq_sinh_div_cosh]
  field_simp
  have hc : Real.cosh b * Real.cosh a + Real.sinh a * Real.sinh b ≠ 0 := by
    simpa only [Real.cosh_add, mul_comm] using (Real.cosh_pos (a + b)).ne'
  exact mul_div_cancel_right₀ _ hc

theorem artanh_binaryFusion {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    Real.artanh (binaryFusion x y) = Real.artanh x + Real.artanh y := by
  apply Real.tanh_injective
  rw [Real.tanh_artanh (abs_lt.mp (abs_binaryFusion_lt_one hx hy)),
    tanh_add_eq_binaryFusion, Real.tanh_artanh (abs_lt.mp hx),
    Real.tanh_artanh (abs_lt.mp hy)]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Attenuation
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

section Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

lemma integrable_of_measurable_unit_interval {f : Ω → ℝ} (hf : Measurable f)
    (hbound : ∀ w, 0 ≤ f w ∧ f w ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (hbound w).1]
  exact (hbound w).2

lemma integral_mul_le_of_condExp_le {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f g : Ω → ℝ} {q : ℝ}
    (hf : Integrable f μ) (hg : Measurable[m] g)
    (hgBound : ∀ w, 0 ≤ g w ∧ g w ≤ 1)
    (hcond : ∀ᵐ w ∂μ, (μ[f | m]) w ≤ q) :
    (∫ w, f w * g w ∂μ) ≤ q * ∫ w, g w ∂μ := by
  have hgb : @Measurable Ω ℝ mΩ _ g := hg.mono hm le_rfl
  have hgInt := integrable_of_measurable_unit_interval (μ := μ) hgb hgBound
  have hgNorm : ∀ᵐ w ∂μ, ‖g w‖ ≤ 1 := by
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (hgBound w).1]
    exact (hgBound w).2
  have hprod := hf.mul_bdd hgb.aestronglyMeasurable hgNorm
  have hpull := condExp_mul_of_stronglyMeasurable_right hg.stronglyMeasurable hprod hf
  calc
    (∫ w, f w * g w ∂μ) = ∫ w, (μ[fun v => f v * g v | m]) w ∂μ :=
      (integral_condExp hm).symm
    _ = ∫ w, (μ[f | m]) w * g w ∂μ := integral_congr_ae hpull
    _ ≤ ∫ w, q * g w ∂μ := by
      apply integral_mono_ae
        (integrable_condExp.mul_bdd hgb.aestronglyMeasurable hgNorm)
        (hgInt.const_mul q)
      filter_upwards [hcond] with w hw
      exact mul_le_mul_of_nonneg_right hw (hgBound w).1
    _ = q * ∫ w, g w ∂μ := integral_const_mul _ _

lemma integral_prod_le_of_condExp_le {q : ℝ} (hq : 0 ≤ q)
    (A : ℕ → Ω → ℝ) (m : ℕ → MeasurableSpace Ω) (s : Finset ℕ)
    (hMeas : ∀ i ∈ s, Measurable (A i))
    (hBound : ∀ i ∈ s, ∀ w, 0 ≤ A i w ∧ A i w ≤ 1)
    (hm : ∀ i ∈ s, m i ≤ mΩ)
    (hCE : ∀ i ∈ s, ∀ᵐ w ∂μ, (μ[A i | m i]) w ≤ q)
    (hLater : ∀ i ∈ s, ∀ j ∈ s, i < j → Measurable[m i] (A j)) :
    (∫ w, ∏ i ∈ s, A i w ∂μ) ≤ q ^ s.card := by
  classical
  revert hMeas hBound hm hCE hLater
  induction s using Finset.induction_on_min with
  | empty =>
      intros
      simp
  | insert i s hmin ih =>
      intro hMeas hBound hm hCE hLater
      have his : i ∉ s := by
        intro hi
        exact (lt_irrefl i) (hmin i hi)
      have hiMem : i ∈ insert i s := Finset.mem_insert_self i s
      have hsMem : ∀ j ∈ s, j ∈ insert i s := fun j hj => Finset.mem_insert_of_mem hj
      have htail : (∫ w, ∏ j ∈ s, A j w ∂μ) ≤ q ^ s.card :=
        ih (fun j hj => hMeas j (hsMem j hj))
          (fun j hj => hBound j (hsMem j hj))
          (fun j hj => hm j (hsMem j hj))
          (fun j hj => hCE j (hsMem j hj))
          (fun j hj k hk => hLater j (hsMem j hj) k (hsMem k hk))
      have hprodMeas : Measurable[m i] (fun w => ∏ j ∈ s, A j w) := by
        apply Finset.measurable_fun_prod
        intro j hj
        exact hLater i hiMem j (hsMem j hj) (hmin j hj)
      have hprodBound : ∀ w, 0 ≤ (∏ j ∈ s, A j w) ∧ (∏ j ∈ s, A j w) ≤ 1 := by
        intro w
        exact ⟨Finset.prod_nonneg (fun j hj => (hBound j (hsMem j hj) w).1),
          Finset.prod_le_one (fun j hj => (hBound j (hsMem j hj) w).1)
            (fun j hj => (hBound j (hsMem j hj) w).2)⟩
      calc
        (∫ w, ∏ j ∈ insert i s, A j w ∂μ) =
            ∫ w, A i w * (∏ j ∈ s, A j w) ∂μ := by simp [Finset.prod_insert, his]
        _ ≤ q * ∫ w, ∏ j ∈ s, A j w ∂μ :=
          integral_mul_le_of_condExp_le (hm i hiMem)
            (integrable_of_measurable_unit_interval (hMeas i hiMem) (hBound i hiMem))
            hprodMeas hprodBound (hCE i hiMem)
        _ ≤ q * q ^ s.card := mul_le_mul_of_nonneg_left htail hq
        _ = q ^ (insert i s).card := by rw [Finset.card_insert_of_notMem his, pow_succ']

lemma integral_prod_le_exp_of_condExp_le {delta : ℝ} (hδ : delta ≤ 1)
    (A : ℕ → Ω → ℝ) (m : ℕ → MeasurableSpace Ω) (s : Finset ℕ)
    (hMeas : ∀ i ∈ s, Measurable (A i))
    (hBound : ∀ i ∈ s, ∀ w, 0 ≤ A i w ∧ A i w ≤ 1)
    (hm : ∀ i ∈ s, m i ≤ mΩ)
    (hCE : ∀ i ∈ s, ∀ᵐ w ∂μ, (μ[A i | m i]) w ≤ 1 - delta)
    (hLater : ∀ i ∈ s, ∀ j ∈ s, i < j → Measurable[m i] (A j)) :
    (∫ w, ∏ i ∈ s, A i w ∂μ) ≤ Real.exp (-delta * (s.card : ℝ)) := by
  calc
    (∫ w, ∏ i ∈ s, A i w ∂μ) ≤ (1 - delta) ^ s.card :=
      integral_prod_le_of_condExp_le (sub_nonneg.mpr hδ) A m s hMeas hBound hm hCE hLater
    _ ≤ (Real.exp (-delta)) ^ s.card := by
      apply pow_le_pow_left₀ (sub_nonneg.mpr hδ)
      have h := Real.add_one_le_exp (-delta)
      linarith
    _ = Real.exp (-delta * (s.card : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun m hm f g ν) :
    CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := he.quasiMeasurePreserving.ae_eq_comp
    ((condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).mp hfg U V hU hV)
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.trans (hωmul.trans (congrArg₂ (· * ·) hωE.symm hωH.symm))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Descent
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ) : CondIndepFun m hm f g ν := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := (condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)).mp hfg U V hU hV
  have hmeas : MeasurableSet {ω' | (ν⟦f ⁻¹' U ∩ g ⁻¹' V | m⟧) ω' =
      (ν⟦f ⁻¹' U | m⟧) ω' * (ν⟦g ⁻¹' V | m⟧) ω'} :=
    measurableSet_eq_fun (stronglyMeasurable_condExp.mono hm).measurable
      ((stronglyMeasurable_condExp.mono hm).measurable.mul
        (stronglyMeasurable_condExp.mono hm).measurable)
  have hdesc := ae_map_iff (μ := μ) he.measurable.aemeasurable hmeas
  rw [he.map_eq] at hdesc
  apply hdesc.mpr
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.symm.trans (hωmul.trans (congrArg₂ (· * ·) hωE hωH))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_DiscreteConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory

namespace Problem367

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSingletonClass A] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem condExp_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap S inferInstance] =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => ∫ ω, f ω ∂μ[|S ⁻¹' {a}] := by
  let s := S ⁻¹' {a}
  have hs : MeasurableSet s := hS (measurableSet_singleton a)
  have hs' : MeasurableSet[MeasurableSpace.comap S inferInstance] s :=
    ⟨{a}, measurableSet_singleton a, rfl⟩
  by_cases hμs : μ s = 0
  · rw [show S ⁻¹' {a} = s from rfl, Measure.restrict_eq_zero.2 hμs]
    rfl
  have havg : (∫ ω, (∫ x, f x ∂μ[|s]) ∂μ.restrict s) =
      ∫ ω, f ω ∂μ.restrict s := by
    rw [integral_const, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    rw [← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr
      ⟨hμs, measure_ne_top _ _⟩), one_mul]
  refine (condExp_restrict_ae_eq_restrict hS.comap_le hs' hf).symm.trans ?_
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hS.comap_le hf.restrict
  · intro t _ _
    exact (integrable_const _).integrableOn
  · rintro t ⟨u, hu, rfl⟩ _
    rw [Measure.restrict_restrict (hS hu)]
    by_cases ha : a ∈ u
    · have heq : S ⁻¹' u ∩ s = s := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨And.right, fun h => ⟨h ▸ ha, h⟩⟩
      rw [heq]
      exact havg
    · have heq : S ⁻¹' u ∩ s = ∅ := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        intro h hEq
        exact ha (hEq ▸ h)
      simp [heq]
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem condExp_indicator_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {t : Set Ω} (ht : MeasurableSet t) :
    μ⟦t | MeasurableSpace.comap S inferInstance⟧ =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => μ[|S ⁻¹' {a}].real t := by
  rw [← integral_indicator_one ht]
  exact condExp_comap_eq_cond_on_fiber hS a ((integrable_const (1 : ℝ)).indicator ht)

theorem indepFun_cond_fiber_of_condIndepFun [StandardBorelSpace Ω]
    {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    {S : Ω → A} {X : Ω → B} {Y : Ω → C}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hXY : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X Y μ)
    (a : A) : IndepFun X Y μ[|S ⁻¹' {a}] := by
  by_cases hμa : μ (S ⁻¹' {a}) = 0
  · rw [cond_eq_zero_of_meas_eq_zero hμa]
    simp [indepFun_iff_measure_inter_preimage_eq_mul]
  let : IsProbabilityMeasure μ[|S ⁻¹' {a}] := cond_isProbabilityMeasure hμa
  have : (ae (μ.restrict (S ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hμa)
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hcond := (condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY).mp hXY s t hs ht
  have hcond' := ae_restrict_le (s := S ⁻¹' {a}) hcond
  have hleft := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a ((hX hs).inter (hY ht))
  have hfirst := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a (hX hs)
  have hsecond := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a (hY ht)
  have heq : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
      μ[|S ⁻¹' {a}].real (X ⁻¹' s ∩ Y ⁻¹' t) =
        μ[|S ⁻¹' {a}].real (X ⁻¹' s) * μ[|S ⁻¹' {a}].real (Y ⁻¹' t) := by
    filter_upwards [hcond', hleft, hfirst, hsecond] with ω h h₁ h₂ h₃
    simpa only [h₁, h₂, h₃] using h
  obtain ⟨ω, hω⟩ := heq.exists
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
  simpa only [measureReal_def, ENNReal.toReal_mul] using hω

theorem condIndepFun_iff_indepFun_cond_fibers [StandardBorelSpace Ω] [Countable A]
    {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    {S : Ω → A} {X : Ω → B} {Y : Ω → C}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y) :
    CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X Y μ ↔
      ∀ a : A, μ (S ⁻¹' {a}) ≠ 0 → IndepFun X Y μ[|S ⁻¹' {a}] := by
  constructor
  · intro h a _
    exact indepFun_cond_fiber_of_condIndepFun hS hX hY h a
  · intro h
    apply (condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY).mpr
    intro s t hs ht
    have hOn (a : A) : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
        (μ⟦X ⁻¹' s ∩ Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω =
          (μ⟦X ⁻¹' s | MeasurableSpace.comap S inferInstance⟧) ω *
            (μ⟦Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω := by
      by_cases hμa : μ (S ⁻¹' {a}) = 0
      · rw [Measure.restrict_eq_zero.mpr hμa]
        simp
      have hprod := (h a hμa).measure_inter_preimage_eq_mul s t hs ht
      have hreal := congrArg ENNReal.toReal hprod
      simp only [ENNReal.toReal_mul] at hreal
      filter_upwards
        [condExp_indicator_comap_eq_cond_on_fiber hS a ((hX hs).inter (hY ht)),
         condExp_indicator_comap_eq_cond_on_fiber hS a (hX hs),
         condExp_indicator_comap_eq_cond_on_fiber hS a (hY ht)] with ω h₁ h₂ h₃
      rw [h₁, h₂, h₃]
      exact hreal
    have hAll : ∀ᵐ ω ∂μ, ∀ a : A, ω ∈ S ⁻¹' {a} →
        (μ⟦X ⁻¹' s ∩ Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω =
          (μ⟦X ⁻¹' s | MeasurableSpace.comap S inferInstance⟧) ω *
            (μ⟦Y ⁻¹' t | MeasurableSpace.comap S inferInstance⟧) ω := by
      apply ae_all_iff.mpr
      intro a
      exact (ae_restrict_iff' (hS (measurableSet_singleton a))).mp (hOn a)
    filter_upwards [hAll] with ω hω
    exact hω (S ω) rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FamilyConditionalPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

alias ⟨_, iCondIndepFun_of_comp_measurePreserving⟩ :=
  iCondIndepFun_iff_comp_measurePreserving

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfinitePiPair
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

variable {I A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem infinitePi_map_pair_arrays
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro s
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      s.restrict ∘ (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      (fun p : (s → A) × (s → B) => fun i => (p.1 i, p.2 i)) ∘
        Prod.map s.restrict s.restrict := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact (measurePreserving_arrowProdEquivProdArrow A B s
    (fun i : s => μ i) (fun i : s => ν i)).symm.map_eq

theorem infinitePi_map_split_pairs
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i => (μ i).prod (ν i))).map
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) =
      (Measure.infinitePi μ).prod (Measure.infinitePi ν) := by
  rw [← infinitePi_map_pair_arrays μ ν,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) ∘
        (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) = id := rfl
  rw [hcomp, Measure.map_id]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfiniteBlockIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

open MeasureTheory ProbabilityTheory

section Unconditional

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : Measure Ω} {f : ∀ i, Ω → X i}

theorem iIndepFun_disjoint_blocks {κ : Type*} (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S : κ → Set ι)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepFun (fun j ω (i : S j) => f i ω) μ := by
  have := hf.isProbabilityMeasure
  have : ∀ index, IsProbabilityMeasure (μ.map (f index)) :=
    fun i => Measure.isProbabilityMeasure_map (hm i).aemeasurable
  have hinj : Function.Injective (fun p : (j : κ) × S j => (p.2 : ι)) := by
    rintro ⟨i, u⟩ ⟨j, v⟩ huv
    change (u : ι) = (v : ι) at huv
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.1 (hS hne) u.property (huv.symm ▸ v.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext huv)
  have hgroup := hf.precomp hinj
  have hmap := hgroup.map_fun_eq_infinitePi_map (fun p => hm p.2)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  calc
    μ.map (fun ω j (i : S j) => f i ω) =
        (μ.map (fun ω (p : (j : κ) × S j) => f p.2 ω)).map
          (MeasurableEquiv.piCurry (fun j (i : S j) => X i)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.infinitePi (fun j =>
        Measure.infinitePi (fun i : S j => μ.map (f i))) := by
      rw [hmap]
      exact Measure.infinitePi_map_piCurry (fun (j : κ) (i : S j) => μ.map (f i))
    _ = Measure.infinitePi (fun j => μ.map (fun ω (i : S j) => f i ω)) := by
      congr 1
      funext j
      exact (hf.precomp (g := fun i : S j => (i : ι)) Subtype.val_injective
        |>.map_fun_eq_infinitePi_map (fun i : S j => hm (i : ι))).symm

theorem infinitePi_map_disjoint_family {κ : Type*}
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (S : κ → Set ι) (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    (Measure.infinitePi ν).map (fun labels index => (S index).domRestrict labels) =
      Measure.infinitePi (fun j => Measure.infinitePi (fun i : S j => ν i)) := by
  have h := iIndepFun_disjoint_blocks (iIndepFun_infinitePi (fun _ => measurable_id))
    (fun i => measurable_pi_apply i) S hS (μ := Measure.infinitePi ν)
  change iIndepFun (fun index labels => (S index).domRestrict labels)
    (Measure.infinitePi ν) at h
  calc
    _ = Measure.infinitePi (fun index => (Measure.infinitePi ν).map (S index).domRestrict) :=
      h.map_fun_eq_infinitePi_map (by fun_prop)
    _ = _ := by
      congr 1
      funext j
      exact Measure.infinitePi_map_restrict' ν

end Unconditional

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LatentProductIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

theorem setIntegral_prod_preimage_fst
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    {f : S × A → ℝ} (hf : Integrable f (ρ.prod μ)) (D : Set S) :
    (∫ z in Prod.fst ⁻¹' D, f z ∂ρ.prod μ) =
      ∫ s in D, ∫ a, f (s, a) ∂μ ∂ρ := by
  have hset : (Prod.fst ⁻¹' D : Set (S × A)) = D ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, ← Measure.restrict_prod_eq_prod_univ]
  apply integral_prod
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hf.restrict

theorem condExp_prod_fst
    {S A : Type*} [mS : MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    {f : S × A → ℝ} (hfm : StronglyMeasurable f) (hf : Integrable f (ρ.prod μ)) :
    (ρ.prod μ)[f | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
      fun z => ∫ a, f (z.1, a) ∂μ := by
  have hg : Integrable (fun z : S × A => ∫ a, f (z.1, a) ∂μ) (ρ.prod μ) :=
    hf.integral_prod_left.comp_fst μ
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf
    (fun _ _ _ => hg.integrableOn)
  · intro D hD _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hD
    rw [setIntegral_prod_preimage_fst ρ μ hg,
      setIntegral_prod_preimage_fst ρ μ hf]
    simp
  · have hfm' : StronglyMeasurable (Function.uncurry (fun s a => f (s, a))) := by
      simpa only [Function.uncurry_def] using hfm
    exact (hfm'.integral_prod_right.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

theorem condIndepFun_latent_product
    {S A B C D : Type*} [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace S] [StandardBorelSpace A] [StandardBorelSpace B]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap (Prod.fst : S × (A × B) → S)) measurable_fst.comap_le
      (fun z : S × (A × B) => F (z.1, z.2.1))
      (fun z : S × (A × B) => G (z.1, z.2.2)) (ρ.prod (μ.prod ν)) := by
  classical
  have hFm : Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) := by fun_prop
  have hGm : Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) := by fun_prop
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hFm hGm]
  intro U V hU hV
  let E : Set (S × (A × B)) := (fun z => F (z.1, z.2.1)) ⁻¹' U
  let H : Set (S × (A × B)) := (fun z => G (z.1, z.2.2)) ⁻¹' V
  have hE : MeasurableSet E := hU.preimage hFm
  have hH : MeasurableSet H := hV.preimage hGm
  have hcE := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hE).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hE)
  have hcH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hH).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hH)
  have hcEH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator (hE.inter hH)).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  filter_upwards [hcE, hcH, hcEH] with z hzE hzH hzEH
  change ((ρ.prod (μ.prod ν))[(E ∩ H).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzEH, hzE, hzH]
  have hprod : (fun ab : A × B => (E ∩ H).indicator (fun _ => (1 : ℝ)) (z.1, ab)) =
      fun ab => (if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0) *
        (if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0) := by
    funext ab
    by_cases hfa : F (z.1, ab.1) ∈ U <;> by_cases hgb : G (z.1, ab.2) ∈ V <;>
      simp [E, H, hfa, hgb]
  rw [hprod, integral_prod_mul
    (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)
    (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
  have hleft : (∫ ab : A × B, E.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ a, if F (z.1, a) ∈ U then (1 : ℝ) else 0 ∂μ := by
    change (∫ ab : A × B, if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_fst (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)]
    simp
  have hright : (∫ ab : A × B, H.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ b, if G (z.1, b) ∈ V then (1 : ℝ) else 0 ∂ν := by
    change (∫ ab : A × B, if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_snd (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
    simp
  rw [hleft, hright]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LatentFamilyIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem iCondIndepFun_latent_of_fiber_indep
    {ι S A : Type*} {B : ι → Type*}
    [mS : MeasurableSpace S] [MeasurableSpace A]
    [mB : ∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [StandardBorelSpace A]
    (ρ : Measure S) (μ : Measure A)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    (F : ∀ i, S × A → B i) (hF : ∀ i, Measurable (F i))
    (hind : ∀ s, iIndepFun (fun i a => F i (s, a)) μ) :
    iCondIndepFun (mS.comap (Prod.fst : S × A → S)) measurable_fst.comap_le
      F (ρ.prod μ) := by
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB F hF]
  intro I sets hsets
  let E : ι → Set (S × A) := fun i => F i ⁻¹' sets i
  have hE : ∀ i ∈ I, MeasurableSet (E i) := fun i hi => (hsets i hi).preimage (hF i)
  have hEI : MeasurableSet (⋂ i ∈ I, E i) := by
    exact I.measurableSet_biInter hE
  have hcI := condExp_prod_fst ρ μ
    (measurable_const.indicator hEI).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hEI)
  have hc : ∀ i ∈ I,
      (ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
        fun z => ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ := by
    intro i hi
    exact condExp_prod_fst ρ μ
      (measurable_const.indicator (hE i hi)).stronglyMeasurable
      ((integrable_const (1 : ℝ)).indicator (hE i hi))
  have hcall := (Filter.eventually_all_finset I).2 hc
  filter_upwards [hcI, hcall] with z hzI hz
  change ((ρ.prod μ)[(⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzI]
  simp only [Finset.prod_apply]
  have hprod : (∏ i ∈ I,
      ((ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst]) z) =
      ∏ i ∈ I, ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ :=
    Finset.prod_congr rfl hz
  rw [hprod]
  let T : ι → Set A := fun i => (fun a => F i (z.1, a)) ⁻¹' sets i
  have hT : ∀ i ∈ I, MeasurableSet (T i) := by
    intro i hi
    exact (hsets i hi).preimage ((hF i).comp (measurable_const.prodMk measurable_id))
  have hTI : MeasurableSet (⋂ i ∈ I, T i) := I.measurableSet_biInter hT
  have hleft : (fun a => (⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) (z.1, a)) =
      (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) := by
    funext a
    simp only [Set.indicator, Set.mem_iInter, E, T, Set.mem_preimage]
  rw [hleft]
  have hmass : (∫ a, (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) a ∂μ) =
      μ.real (⋂ i ∈ I, T i) := by
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) hTI)
  rw [hmass]
  have hright : ∀ i ∈ I,
      (∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ) = μ.real (T i) := by
    intro i hi
    change (∫ a, (T i).indicator (fun _ => (1 : ℝ)) a ∂μ) = _
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) (hT i hi))
  rw [Finset.prod_congr rfl hright]
  unfold Measure.real
  rw [(hind z.1).measure_inter_preimage_eq_mul I hsets, ENNReal.toReal_prod]

theorem iCondIndepFun_latent_infinitePi
    {ι S : Type*} [Countable ι] {A B : ι → Type*}
    [mS : MeasurableSpace S] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [∀ i, StandardBorelSpace (A i)]
    (ρ : Measure S) (ν : ∀ i, Measure (A i))
    [IsFiniteMeasure ρ] [∀ i, IsProbabilityMeasure (ν i)]
    (F : ∀ i, S × A i → B i) (hF : ∀ i, Measurable (F i)) :
    iCondIndepFun (mS.comap (Prod.fst : S × (∀ i, A i) → S))
      measurable_fst.comap_le
      (fun i z => F i (z.1, z.2 i)) (ρ.prod (Measure.infinitePi ν)) := by
  apply iCondIndepFun_latent_of_fiber_indep ρ (Measure.infinitePi ν)
    (fun i z => F i (z.1, z.2 i))
  · intro i
    exact (hF i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · intro s
    exact iIndepFun_infinitePi (fun i =>
      (hF i).comp (measurable_const.prodMk measurable_id))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FairSpin
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma fairSpin_neg_preimage : fairSpin ⁻¹' {IsingSpin.neg} = Set.Iic (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin]

lemma fairSpin_pos_preimage : fairSpin ⁻¹' {IsingSpin.pos} = Set.Ioi (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin, not_le]

lemma fairSpin_neg_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.neg}) = 1 / 2 := by
  rw [fairSpin_neg_preimage, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨h0, hu⟩
    · rintro ⟨h0, hu⟩
      exact ⟨hu, h0, by linarith⟩
  rw [h, Real.volume_Icc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_pos_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.pos}) = 1 / 2 := by
  rw [fairSpin_pos_preimage, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨hu, h1⟩
    · rintro ⟨hu, h1⟩
      exact ⟨hu, by linarith, h1⟩
  rw [h, Real.volume_Ioc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_mass (a : IsingSpin) : uniform01 (fairSpin ⁻¹' {a}) = 1 / 2 := by
  cases a
  · exact fairSpin_neg_mass
  · exact fairSpin_pos_mass

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LabelDecomposition
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.LabelDecomposition

theorem indepFun_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    IndepFun (fun U : ι → A => U r)
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i)
      (Measure.infinitePi μ) := by
  have hi : iIndepFun (fun i (U : ι → A) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → A => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → A)) :=
    fun i => measurable_iff_comap_le.mp (measurable_pi_apply i)
  have hd : Disjoint ({r} : Set ι) {i | i ≠ r} := by simp
  have h := indep_iSup_of_disjoint hle hi hd
  change Indep (MeasurableSpace.comap (fun U : ι → A => U r) inferInstance)
    (MeasurableSpace.comap
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i) inferInstance)
    (Measure.infinitePi μ)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

theorem map_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    (Measure.infinitePi μ).map
      (fun U : ι → A => (U r, fun i : {i : ι // i ≠ r} => U i)) =
      (μ r).prod (Measure.infinitePi (fun i : {i : ι // i ≠ r} => μ i)) := by
  rw [(indepFun_coordinate_rest μ r).map_prod_eq_prod_map_map
    (measurable_pi_apply r).aemeasurable
      ((measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1)).aemeasurable)]
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

theorem map_fairSpin_rest (d : ℕ) (r : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (fairSpin (U r), fun v : {v : TreeVertex d // v ≠ r} => U v)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : {v : TreeVertex d // v ≠ r} => uniform01)) := by
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map _ = _
  have hrest : Measurable
      (fun U : TreeVertex d → ℝ => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v)) :=
    (measurable_pi_apply r).prodMk
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1))
  calc
    _ = ((Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map
        (fun U => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v))).map
          (Prod.map fairSpin id) := by
      rw [Measure.map_map (measurable_fairSpin.prodMap measurable_id) hrest]
      rfl
    _ = _ := by
      rw [map_coordinate_rest,
        ← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]

end Problem367.LabelDecomposition

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_lower_unique {d : ℕ} {u v w : TreeVertex d}
    (hu : treeAdj u w) (hv : treeAdj v w)
    (huw : u.1.length < w.1.length) (hvw : v.1.length < w.1.length) : u = v := by
  exact (treeAdj_parent_of_length_lt hu huw).symm.trans
    (treeAdj_parent_of_length_lt hv hvw)

theorem treeAdj_parentVertex {d : ℕ} {v : TreeVertex d} (hv : v.1 ≠ []) :
    treeAdj (parentVertex v) v := by
  exact Or.inl ⟨v.1.getLast hv, (List.dropLast_append_getLast hv).symm⟩

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Cardinality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

private lemma mem_inducedEdges_8911 {d : ℕ} (D : Finset (TreeVertex d))
    (u v : TreeVertex d) :
    (u, v) ∈ inducedEdges D ↔
      (u ∈ D ∧ v ∈ D) ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  rw [inducedEdges, Finset.mem_filter]
  exact and_congr Finset.mem_product Iff.rfl

lemma inducedEdges_snd_injOn {d : ℕ} (D : Finset (TreeVertex d)) :
    Set.InjOn Prod.snd (↑(inducedEdges D) : Set (TreeVertex d × TreeVertex d)) := by
  rintro ⟨a, b⟩ hab ⟨c, e⟩ hce heq
  have hab' : (a ∈ D ∧ b ∈ D) ∧ treeAdj a b ∧ a.1.length < b.1.length := by
    exact (mem_inducedEdges_8911 D a b).mp hab
  have hce' : (c ∈ D ∧ e ∈ D) ∧ treeAdj c e ∧ c.1.length < e.1.length := by
    exact (mem_inducedEdges_8911 D c e).mp hce
  change b = e at heq
  subst e
  exact Prod.ext (treeAdj_lower_unique hab'.2.1 hce'.2.1 hab'.2.2 hce'.2.2) rfl

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcast
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

attribute [local instance] OAI.Problem367.RootedBroadcast.rootedBroadcastMeasurableSingletonSpin
lemma spinMul_comm (a b : IsingSpin) : spinMul a b = spinMul b a := by
  cases a <;> cases b <;> rfl
lemma spinMul_assoc (a b c : IsingSpin) : spinMul (spinMul a b) c = spinMul a (spinMul b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] lemma spinMul_cancel (a b : IsingSpin) : spinMul a (spinMul a b) = b := by
  rw [← spinMul_assoc, spinMul_self, pos_spinMul]

lemma biasedSpin_pos_mass {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.pos}) = ENNReal.ofReal p := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.pos} = Set.Iic p := by
    ext u
    simp [biasedSpin]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic p ∩ Set.Icc 0 1 = Set.Icc 0 p := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨hu,h0,_⟩ => ⟨h0,hu⟩, fun ⟨h0,hu⟩ => ⟨hu,h0,hu.trans hp1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

lemma biasedSpin_neg_mass {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.neg}) = ENNReal.ofReal (1-p) := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.neg} = Set.Ioi p := by
    ext u
    simp [biasedSpin, not_le]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi p ∩ Set.Icc 0 1 = Set.Ioc p 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨hu,_,h1⟩ => ⟨hu,h1⟩, fun ⟨hu,h1⟩ => ⟨hu,hp0.trans hu.le,h1⟩⟩
  rw [h, Real.volume_Ioc]

lemma ofNoise_root {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    ofNoise noise ⟨[], List.isChain_nil⟩ = noise ⟨[], List.isChain_nil⟩ := by
  rw [ofNoise]
  simp

@[simp] lemma noiseFromSpins_ofNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    noiseFromSpins (ofNoise noise) = noise := by
  funext v
  by_cases hv : v.val = []
  · rw [noiseFromSpins, ite_eq_left hv, ofNoise]
    simp [hv]
  · rw [noiseFromSpins, ite_eq_right hv, ofNoise_nonroot noise v hv]
    rw [spinMul_assoc, spinMul_self, spinMul_pos]

@[simp] lemma ofNoise_noiseFromSpins {d : ℕ} (x : TreeVertex d → IsingSpin) :
    ofNoise (noiseFromSpins x) = x := by
  funext v
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise (noiseFromSpins x) v = x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · rw [ofNoise]
        simp [hnil, noiseFromSpins]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot _ v hnil, ih _ hlt (parent v) rfl,
          noiseFromSpins, ite_eq_right hnil, spinMul_assoc, spinMul_self, spinMul_pos]
  exact h _ v rfl

lemma edgeNoise_mass {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (a : IsingSpin) :
    uniform01 ((edgeNoise theta) ⁻¹' {a}) =
      ENNReal.ofReal ((1 + (if a = IsingSpin.pos then theta else -theta)) / 2) := by
  have hp0 : 0 ≤ (1 + theta) / 2 := by linarith
  have hp1 : (1 + theta) / 2 ≤ 1 := by linarith
  cases a
  · rw [edgeNoise, biasedSpin_neg_mass hp0 hp1, ite_eq_right (by decide : IsingSpin.neg ≠ IsingSpin.pos)]
    congr 1
    ring
  · rw [edgeNoise, biasedSpin_pos_mass hp0 hp1]
    rfl

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SpinEncoding
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma spinAgreementCode_comm (a b : IsingSpin) :
    spinAgreementCode a b = spinAgreementCode b a := by
  cases a <;> cases b <;> rfl

lemma ConnectedFinset.spin_eq_on_iff_root_agreements {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (σ τ : TreeVertex d → IsingSpin) :
    (∀ v ∈ D, σ v = τ v) ↔
      σ r = τ r ∧ ∀ e ∈ inducedEdges D,
        spinAgreementCode (σ e.1) (σ e.2) =
          spinAgreementCode (τ e.1) (τ e.2) := by
  classical
  constructor
  · intro h
    refine ⟨h r hr, ?_⟩
    intro e he
    have heD := Finset.mem_product.mp (Finset.mem_filter.mp he).1
    rw [h e.1 heD.1, h e.2 heD.2]
  · rintro ⟨hroot, hedges⟩
    have step {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D)
        (hadj : treeAdj u v) (heq : σ u = τ u) : σ v = τ v := by
      have hcode : spinAgreementCode (σ u) (σ v) =
          spinAgreementCode (τ u) (τ v) := by
        rcases treeAdj_length hadj with hlen | hlen
        · apply hedges (u, v)
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj, by change u.1.length < v.1.length; omega⟩
        · have his : (v, u) ∈ inducedEdges D := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨hv, hu⟩, Or.symm hadj, by change v.1.length < u.1.length; omega⟩
          simpa only [spinAgreementCode_comm (σ v) (σ u),
            spinAgreementCode_comm (τ v) (τ u)] using hedges (v, u) his
      rw [heq] at hcode
      exact spinAgreementCode_injective_right (τ u) hcode
    intro v hv
    have hpath := hD.2 r hr v hv
    induction hpath with
    | refl => exact hroot
    | tail hpath hadj ih => exact step hadj.1 hadj.2.1 hadj.2.2 (ih hadj.1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcastLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastLawMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩

lemma eq_root_iff {d : ℕ} (v : TreeVertex d) : v = root d ↔ v.val = [] := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact h

lemma ofNoise_root_decomposition {d : ℕ} (noise : TreeVertex d → IsingSpin)
    (v : TreeVertex d) :
    ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · have hvroot : v = root d := (eq_root_iff v).mpr hnil
        subst v
        simp [root, ofNoise_root, eraseRootNoise]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise v hnil, ofNoise_nonroot (eraseRootNoise noise) v hnil,
          eraseRootNoise, ite_eq_right hnil, ih _ hlt (parent v) rfl]
        rw [← spinMul_assoc, spinMul_comm (noise v) (noise (root d)), spinMul_assoc]
  exact h _ v rfl

lemma measurable_nonrootNoise (d : ℕ) (theta : ℝ) : Measurable (@nonrootNoise d theta) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v = root d
  · simpa only [nonrootNoise, dite_eq_left hv] using
      (measurable_const : Measurable (fun _ : NonrootVertex d → ℝ => IsingSpin.pos))
  · simpa only [nonrootNoise, dite_eq_right hv, Function.comp_def] using
      (measurable_edgeNoise theta).comp (measurable_pi_apply (X := fun _ : NonrootVertex d => ℝ) ⟨v, hv⟩)

lemma measurable_rootlessFactor (d : ℕ) (theta : ℝ) : Measurable (@rootlessFactor d theta) :=
  (measurable_ofNoise d).comp (measurable_nonrootNoise d theta)

lemma factor_root_decomposition {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    (v : TreeVertex d) :
    factor theta U v = spinMul (fairSpin (U (root d)))
      (rootlessFactor theta (fun w : NonrootVertex d => U w.val) v) := by
  rw [factor, ofNoise_root_decomposition]
  have heq : eraseRootNoise (inputNoise theta U) =
      nonrootNoise theta (fun w : NonrootVertex d => U w.val) := by
    funext w
    by_cases hw : w = root d
    · subst w
      simp [eraseRootNoise, nonrootNoise]
    · have hnil : w.val ≠ [] := fun h => hw ((eq_root_iff w).mpr h)
      simp [eraseRootNoise, inputNoise, nonrootNoise, hw, hnil]
  rw [heq]
  rfl

lemma factor_edge_agreement {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    {u v : TreeVertex d} (huv : treeAdj u v) (hlt : u.val.length < v.val.length) :
    spinAgreementCode (factor theta U u) (factor theta U v) = edgeNoise theta (U v) := by
  have hp : parent v = u := treeAdj_parent_of_length_lt huv hlt
  have hnil : v.val ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlt
    omega
  change spinMul (factor theta U u) (factor theta U v) = _
  change spinMul (ofNoise (inputNoise theta U) u) (ofNoise (inputNoise theta U) v) = _
  rw [ofNoise_nonroot _ v hnil, hp]
  simp only [inputNoise, ite_eq_right hnil]
  rw [spinMul_comm (edgeNoise theta (U v)), spinMul_cancel]

lemma factor_cylinder_event {d : ℕ} (theta : ℝ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (eta : TreeVertex d → IsingSpin) :
    {U : TreeVertex d → ℝ | ∀ v ∈ D, factor theta U v = eta v} =
      {U | factor theta U r = eta r ∧ ∀ e ∈ inducedEdges D,
        edgeNoise theta (U e.2) = spinAgreementCode (eta e.1) (eta e.2)} := by
  classical
  ext U
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hD.spin_eq_on_iff_root_agreements hr]
  apply and_congr_right
  intro hroot
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  have he' := (Finset.mem_filter.mp he).2
  rw [factor_edge_agreement theta U he'.1 he'.2]

lemma edgeVertex_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (edgeVertex D) := by
  intro a b hab
  apply Subtype.ext
  apply inducedEdges_snd_injOn D a.property b.property
  exact congrArg Subtype.val hab

lemma nonroot_edge_event_mass {d : ℕ} {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))
      {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
        spinAgreementCode (eta e.val.1) (eta e.val.2)} =
      ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  classical
  let A : Set ((e : inducedEdges D) → ℝ) := Set.pi Set.univ
    (fun e => edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)})
  have hA : MeasurableSet A := MeasurableSet.univ_pi
    (fun e => (measurable_edgeNoise theta) (measurableSet_singleton _))
  have hm : Measurable (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e)) := by
    fun_prop
  calc
    _ = (Measure.map (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e))
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) A := by
      rw [Measure.map_apply hm hA]
      congr 1
      ext Y
      simp [A, Set.mem_pi]
    _ = (Measure.infinitePi (fun _ : inducedEdges D => uniform01)) A := by
      rw [Measure.map_infinitePi_infinitePi_of_inj (edgeVertex_injective D)]
    _ = ∏ e : inducedEdges D, uniform01
        (edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)}) := by
      simpa only [A, Finset.coe_univ] using
        (Measure.infinitePi_pi (fun _ : inducedEdges D => uniform01)
          (s := Finset.univ) (fun e _ => (measurable_edgeNoise theta)
            (measurableSet_singleton (spinAgreementCode (eta e.val.1) (eta e.val.2)))))
    _ = _ := by
      simp only [edgeNoise_mass h0 h1, spinAgreementCode_eq_pos_iff]
      exact Finset.prod_coe_sort (inducedEdges D) (fun e : TreeVertex d × TreeVertex d =>
        ENNReal.ofReal ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

lemma freeCylinderWeight_eq_edge_product {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  unfold freeCylinderWeight
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · norm_num [ENNReal.ofReal_div_of_pos]
  · intro e he
    split_ifs <;> linarith

lemma hasFreeIsingLaw_of_root_nonroot_joint {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (hjoint : ∀ r : TreeVertex d,
      (labelMeasure d).map (fun U => (factor theta U r, fun w : NonrootVertex d => U w.val)) =
        (uniform01.map fairSpin).prod (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) :
    HasFreeIsingLaw theta ((labelMeasure d).map (factor theta)) := by
  classical
  intro D hD eta
  obtain ⟨r, hr⟩ := hD.1
  let A : Set (NonrootVertex d → ℝ) :=
    {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
      spinAgreementCode (eta e.val.1) (eta e.val.2)}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro e
    exact ((measurable_edgeNoise theta).comp (measurable_pi_apply (edgeVertex D e)))
      (measurableSet_singleton _)
  have hS : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet (fun v _ => measurableSet_singleton (eta v))
  have hm : Measurable (fun U : TreeVertex d → ℝ =>
      (factor theta U r, fun w : NonrootVertex d => U w.val)) := by
    exact ((measurable_pi_apply r).comp (measurable_factor d theta)).prodMk
      (Measurable.of_eval (fun w => measurable_pi_apply w.val))
  rw [Measure.map_apply (measurable_factor d theta) hS]
  change (labelMeasure d) {U | ∀ v ∈ D, factor theta U v = eta v} = _
  rw [factor_cylinder_event theta D hD r hr eta]
  calc
    _ = ((labelMeasure d).map (fun U =>
        (factor theta U r, fun w : NonrootVertex d => U w.val))) ({eta r} ×ˢ A) := by
      rw [Measure.map_apply hm ((measurableSet_singleton _).prod hA)]
      congr 1
      ext U
      simp [A, Set.mem_prod, edgeVertex]
    _ = ((uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) ({eta r} ×ˢ A) := by
      rw [hjoint r]
    _ = (uniform01.map fairSpin) {eta r} *
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A :=
      Measure.prod_prod _ _
    _ = (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
      rw [Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass]
      rw [show (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A = _ from
        nonroot_edge_event_mass h0 h1 D eta]
    _ = freeCylinderWeight theta D eta := (freeCylinderWeight_eq_edge_product h0 h1 D eta).symm

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

lemma ofNoise_congr_prefix {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (v : TreeVertex d)
    (heq : ∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      (∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv heq
      by_cases hnil : v.val = []
      · calc
          ofNoise noise₁ v = noise₁ v := by rw [ofNoise]; simp [hnil]
          _ = noise₂ v := heq v (List.prefix_refl _)
          _ = ofNoise noise₂ v := by rw [ofNoise]; simp [hnil]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        apply congrArg₂ spinMul (heq v (List.prefix_refl _))
        apply ih _ hlt (parent v) rfl
        intro w hw
        exact heq w (hw.trans (List.dropLast_prefix v.val))
  exact h _ v rfl heq

lemma prefix_in_branch_or_root {d : ℕ} (c : Fin d)
    {u v : TreeVertex d} (hv : [c] <+: v.val) (huv : u.val <+: v.val) :
    u.val = [] ∨ [c] <+: u.val := by
  by_cases hu : u.val = []
  · exact Or.inl hu
  · right
    apply List.prefix_of_prefix_length_le hv huv
    have : 0 < u.val.length := List.length_pos_iff.mpr hu
    simpa only [List.length_singleton] using Nat.succ_le_of_lt this

lemma measurable_branchNoise {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (fun p : IsingSpin × (BranchVertex c → ℝ) => branchNoise theta c p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hnil : v.val = []
  · simpa only [branchNoise, ite_eq_left hnil] using
      (measurable_fst : Measurable (Prod.fst : IsingSpin × (BranchVertex c → ℝ) → IsingSpin))
  · by_cases hv : [c] <+: v.val
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_left hv, Function.comp_def] using
        (measurable_edgeNoise theta).comp
          ((measurable_pi_apply (X := fun _ : BranchVertex c => ℝ) ⟨v,hv⟩).comp measurable_snd)
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_right hv] using
        (measurable_const : Measurable (fun _ : IsingSpin × (BranchVertex c → ℝ) => IsingSpin.pos))

lemma measurable_branchFactor {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (branchFactor theta c) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_ofNoise_apply v.val).comp (measurable_branchNoise theta c)

lemma factor_branch_representation {d : ℕ} (theta : ℝ) (c : Fin d)
    (U : TreeVertex d → ℝ) :
    (fun v : BranchVertex c => factor theta U v.val) =
      branchFactor theta c (fairSpin (U (root d)), fun v : BranchVertex c => U v.val) := by
  funext v
  apply ofNoise_congr_prefix
  intro w hw
  rcases prefix_in_branch_or_root c v.property hw with hnil | hbranch
  · have heq : w = root d := (eq_root_iff w).mpr hnil
    subst w
    simp [inputNoise, branchNoise]
  · have hnil : w.val ≠ [] := by
      intro heq
      rw [heq] at hbranch
      have hl := hbranch.length_le
      simp at hl
    simp [inputNoise, branchNoise, hnil, hbranch]

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchLabels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

namespace RootedBroadcast

lemma branch_disjoint {d : ℕ} {c e : Fin d} (hce : c ≠ e) :
    Disjoint {v : TreeVertex d | [c] <+: v.val} {v | [e] <+: v.val} := by
  apply Set.disjoint_left.mpr
  intro v hc he
  have hprefix : [c] <+: [e] := List.prefix_of_prefix_length_le hc he (by simp)
  have heq : [c] = [e] := hprefix.eq_of_length (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hce (by simpa only [List.singleton_inj] using heq)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_UniformTwist
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurePreserving_fiberTwist
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (twist : B → A → A)
    (hmeas : Measurable (fun p : A × B => twist p.2 p.1))
    (hpres : ∀ b, MeasurePreserving (twist b) μ μ) :
    MeasurePreserving (fun p : A × B => (twist p.2 p.1, p.2))
      (μ.prod ν) (μ.prod ν) := by
  have hm : Measurable (fun p : A × B => (twist p.2 p.1, p.2)) :=
    hmeas.prodMk measurable_snd
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hs.preimage hm),
    Measure.prod_apply_symm hs]
  apply lintegral_congr
  intro b
  change μ ((twist b) ⁻¹' ((fun a => (a, b)) ⁻¹' s)) =
    μ ((fun a => (a, b)) ⁻¹' s)
  exact (hpres b).measure_preimage ((hs.preimage measurable_prodMk_right).nullMeasurableSet)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Twist
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance localInst_rff45b3_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem measurePreserving_fairSpin_mul (b : IsingSpin) :
    MeasurePreserving (fun a => spinMul a b)
      (uniform01.map fairSpin) (uniform01.map fairSpin) := by
  have hm : Measurable (fun a => spinMul a b) := measurable_of_finite _
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_singleton
  intro a
  have hpre : (fun x => spinMul x b) ⁻¹' {a} = {spinMul a b} := by
    ext x
    cases x <;> cases a <;> cases b <;> simp [spinMul]
  rw [Measure.map_apply hm (measurableSet_singleton a), hpre,
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _),
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass,
    fairSpin_mass]

theorem measurePreserving_fairSpin_twist
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {f : Y → IsingSpin} (hf : Measurable f) :
    MeasurePreserving (fun p : IsingSpin × Y => (spinMul p.1 (f p.2), p.2))
      ((uniform01.map fairSpin).prod ν) ((uniform01.map fairSpin).prod ν) := by
  apply measurePreserving_fiberTwist (uniform01.map fairSpin) ν
    (fun y a => spinMul a (f y))
  · exact measurable_spinMul.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  · intro y
    exact measurePreserving_fairSpin_mul (f y)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastJointLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem map_factor_rest (d : ℕ) (theta : ℝ) (v : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (factor theta U v, fun w : NonrootVertex d => U w.val)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) := by
  have hf : Measurable (fun Y : NonrootVertex d → ℝ => rootlessFactor theta Y v) :=
    (measurable_pi_apply v).comp (measurable_rootlessFactor d theta)
  have ht := measurePreserving_fairSpin_twist
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) hf
  have hj : Measurable (fun U : TreeVertex d → ℝ =>
      (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val)) :=
    (measurable_fairSpin.comp (measurable_pi_apply (root d))).prodMk
      (measurable_pi_iff.mpr (fun w => measurable_pi_apply w.val))
  calc
    _ = ((labelMeasure d).map
        (fun U => (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val))).map
          (fun p : IsingSpin × (NonrootVertex d → ℝ) =>
            (spinMul p.1 (rootlessFactor theta p.2 v), p.2)) := by
      rw [Measure.map_map ht.measurable hj]
      congr 1
      funext U
      exact Prod.ext (factor_root_decomposition theta U v) rfl
    _ = _ := by
      rw [LabelDecomposition.map_fairSpin_rest]
      exact ht.map_eq

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeIsingMeasure
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem freeIsingMeasure_hasFreeIsingLaw (d : ℕ) {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) :
    HasFreeIsingLaw theta (freeIsingMeasure d theta) :=
  RootedBroadcast.hasFreeIsingLaw_of_root_nonroot_joint h0 h1
    (RootedBroadcast.map_factor_rest d theta)

theorem HasFreeIsingLaw.eq_freeIsingMeasure {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) : mu = freeIsingMeasure d theta :=
  hmu.unique (freeIsingMeasure_hasFreeIsingLaw d h0 h1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_FreeIsingBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

theorem map_root_branch_family_of_sampler {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [MeasurableSpace S]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f) :
    (Measure.infinitePi ν).map (fun U => (f (U (root d)),
      fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
        Measure.infinitePi (fun v : BranchVertex c => ν v.val))) := by
  let F : (NonrootVertex d → A) → (∀ c : Fin d, BranchVertex c → A) :=
    fun Y c v => Y (branchEmbedding c v)
  have hF : Measurable F := by fun_prop
  have hind := (LabelDecomposition.indepFun_coordinate_rest ν (root d)).comp hf hF
  have hB : Measurable (fun U : TreeVertex d → A => f (U (root d))) :=
    hf.comp (measurable_pi_apply (root d))
  have hY : Measurable (fun U : TreeVertex d → A =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) := by fun_prop
  have hroot : (Measure.infinitePi ν).map (fun U => f (U (root d))) =
      (ν (root d)).map f := by
    change (Measure.infinitePi ν).map (f ∘ (fun U => U (root d))) = _
    rw [← Measure.map_map hf (measurable_pi_apply (root d)), Measure.infinitePi_map_eval]
  change IndepFun (fun U : TreeVertex d → A => f (U (root d)))
    (fun U => fun c : Fin d => fun v : BranchVertex c => U v.val)
    (Measure.infinitePi ν) at hind
  rw [hind.map_prod_eq_prod_map_map hB.aemeasurable hY.aemeasurable, hroot]
  congr 1
  exact infinitePi_map_disjoint_family ν
    (fun c : Fin d => {v : TreeVertex d | [c] <+: v.val})
    (fun _ _ hce => branch_disjoint hce)

theorem iCondIndepFun_root_branch_observables {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [mS : MeasurableSpace S]
    [StandardBorelSpace A] [StandardBorelSpace S]
    {B : Fin d → Type*} [∀ c, MeasurableSpace (B c)]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f)
    (F : ∀ c, S × (BranchVertex c → A) → B c) (hF : ∀ c, Measurable (F c)) :
    iCondIndepFun
      (mS.comap (fun U : TreeVertex d → A => f (U (root d))))
      (hf.comp (measurable_pi_apply (root d))).comap_le
      (fun c U => F c (f (U (root d)), fun v => U v.val))
      (Measure.infinitePi ν) := by
  let e : (TreeVertex d → A) → S × (∀ c : Fin d, BranchVertex c → A) :=
    fun U => (f (U (root d)), fun c v => U v.val)
  let ρ := ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
    Measure.infinitePi (fun v : BranchVertex c => ν v.val)))
  have he : MeasurePreserving e (Measure.infinitePi ν) ρ :=
    ⟨(hf.comp (measurable_pi_apply (root d))).prodMk (by fun_prop),
      map_root_branch_family_of_sampler ν f hf⟩
  have hbase := iCondIndepFun_latent_infinitePi ((ν (root d)).map f)
    (fun c : Fin d => Measure.infinitePi (fun v : BranchVertex c => ν v.val)) F hF
  have hpull := iCondIndepFun_comp_measurePreserving (Measure.infinitePi ν) ρ e he
    (mS.comap Prod.fst) measurable_fst.comap_le
    (fun c => show Measurable (fun z : S × (∀ c : Fin d, BranchVertex c → A) =>
      F c (z.1, z.2 c)) from by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

theorem map_noisyBroadcast {d : ℕ} {A : Type*} [MeasurableSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.infinitePi (fun v => uniform01.prod (ν v))).map
      (fun U : TreeVertex d → ℝ × A =>
        (factor theta (fun v => (U v).1), fun v => (U v).2)) =
      (freeIsingMeasure d theta).prod (Measure.infinitePi ν) := by
  calc
    _ = ((Measure.infinitePi (fun v => uniform01.prod (ν v))).map
        (fun U : TreeVertex d → ℝ × A =>
          ((fun v => (U v).1), fun v => (U v).2))).map
        (Prod.map (factor theta) id) := by
      rw [Measure.map_map ((measurable_factor d theta).prodMap measurable_id) (by fun_prop)]
      rfl
    _ = _ := by
      rw [infinitePi_map_split_pairs, ← Measure.map_prod_map _ _
        (measurable_factor d theta) measurable_id, Measure.map_id]
      rfl

local instance instMeasurableSingletonClassIsingSpin_2_rff45b3_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem iCondIndepFun_noisy_factor_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1))
      ((measurable_fairSpin.comp measurable_fst).comp
        (measurable_pi_apply (root d))).comap_le
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2))
      (Measure.infinitePi (fun v => uniform01.prod (ν v))) := by
  let F : ∀ c : Fin d, IsingSpin × (BranchVertex c → ℝ × A) →
      (BranchVertex c → IsingSpin) × (BranchVertex c → A) :=
    fun c p => (branchFactor theta c (p.1, fun v => (p.2 v).1),
      fun v => (p.2 v).2)
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact ((measurable_branchFactor theta c).comp
      (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have h := iCondIndepFun_root_branch_observables
    (fun v => uniform01.prod (ν v)) (fun p : ℝ × A => fairSpin p.1)
    (measurable_fairSpin.comp measurable_fst) F hF
  have heq : (fun (c : Fin d) (U : TreeVertex d → ℝ × A) => F c (fairSpin (U (root d)).1, fun v => U v.val)) =
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2)) := by
    funext c U
    apply Prod.ext
    · exact (factor_branch_representation theta c (fun w => (U w).1)).symm
    · rfl
  rw [heq] at h
  exact h

end RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_1_rff45b3_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem freeIsingMeasure_iCondIndepFun_noisy_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let e : (TreeVertex d → ℝ × A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    fun U => (RootedBroadcast.factor theta (fun v => (U v).1), fun v => (U v).2)
  have he : MeasurePreserving e (Measure.infinitePi (fun v => uniform01.prod (ν v)))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) :=
    ⟨((RootedBroadcast.measurable_factor d theta).comp (by fun_prop)).prodMk
      (by fun_prop), RootedBroadcast.map_noisyBroadcast theta ν⟩
  apply iCondIndepFun_of_comp_measurePreserving
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) e he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (fun c => show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
  have hroot : (fun U : TreeVertex d → ℝ × A =>
      RootedBroadcast.factor theta (fun v => (U v).1) (RootedBroadcast.root d)) =
      (fun U => fairSpin (U (RootedBroadcast.root d)).1) := by
    funext U
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e, hroot] using
    RootedBroadcast.iCondIndepFun_noisy_factor_branches theta ν

theorem HasFreeIsingLaw.iCondIndepFun_noisy_branches {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_noisy_branches theta ν

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_NoisyBranchConditionalLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance noisyBranchConditionalLawMeasurableSingletonIsingSpin_rff45b3_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.planted_spin_event_mass
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (v : TreeVertex d) (s : IsingSpin) :
    (μ.prod (Measure.infinitePi ν))
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} = 1 / 2 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hset :
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} =
        {x : TreeVertex d → IsingSpin | x v = s} ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, Measure.prod_prod, measure_univ, mul_one, hμ.marginal]
  norm_num [ENNReal.ofReal_div_of_pos]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_PlantedInformation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem367.PlantedInformation

open PlantedSymmetry

variable {ι κ : Type*}

theorem measurable_spinSign : Measurable spinSign := by
  intro s hs
  trivial

theorem observationSigma_le (v : ι → κ) (t : ℝ) :
    observationSigma v t ≤ (inferInstance : MeasurableSpace ((κ → IsingSpin) × (κ → ℝ))) := by
  apply Measurable.comap_le
  exact Measurable.of_eval (fun index =>
    (measurable_pi_apply (v index)).comp (measurable_observation t))

end Problem367.PlantedInformation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Regrouping
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem indepFun_prodMk_left_of_joint
    {Ω A B C : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXYZ : IndepFun X (fun ω => (Y ω, Z ω)) μ)
    (hYZ : IndepFun Y Z μ) :
    IndepFun (fun ω => (X ω, Y ω)) Z μ := by
  have hXY : IndepFun X Y μ := hXYZ.comp measurable_id measurable_fst
  have hmapX : IsProbabilityMeasure (μ.map X) := by first | exact Measure.isProbabilityMeasure_map (by first | exact hX.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hmapY : IsProbabilityMeasure (μ.map Y) := by first | exact Measure.isProbabilityMeasure_map (by first | exact hY.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hmapZ : IsProbabilityMeasure (μ.map Z) := by first | exact Measure.isProbabilityMeasure_map (by first | exact hZ.aemeasurable) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  apply (indepFun_iff_map_prod_eq_prod_map_map (hX.prodMk hY).aemeasurable
    hZ.aemeasurable).mpr
  calc
    _ = (μ.map (fun ω => (X ω, Y ω, Z ω))).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [Measure.map_map (by fun_prop) (hX.prodMk (hY.prodMk hZ))]
      rfl
    _ = ((μ.map X).prod ((μ.map Y).prod (μ.map Z))).map
        MeasurableEquiv.prodAssoc.symm := by
      rw [hXYZ.map_prod_eq_prod_map_map hX.aemeasurable (hY.prodMk hZ).aemeasurable,
        hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable]
    _ = ((μ.map X).prod (μ.map Y)).prod (μ.map Z) :=
      (measurePreserving_prodAssoc (μ.map X) (μ.map Y) (μ.map Z)).symm.map_eq
    _ = _ := by
      rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]

theorem condIndepFun_prodMk_left_of_joint
    {Ω S A B C : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {R : Ω → S} {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hR : Measurable R) (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXYZ : CondIndepFun (MeasurableSpace.comap R inferInstance) hR.comap_le
      X (fun ω => (Y ω, Z ω)) μ)
    (hYZ : CondIndepFun (MeasurableSpace.comap R inferInstance) hR.comap_le Y Z μ) :
    CondIndepFun (MeasurableSpace.comap R inferInstance) hR.comap_le
      (fun ω => (X ω, Y ω)) Z μ := by
  apply (condIndepFun_iff_indepFun_cond_fibers hR (hX.prodMk hY) hZ).mpr
  intro s hs
  let : IsProbabilityMeasure μ[|R ⁻¹' {s}] := cond_isProbabilityMeasure hs
  exact indepFun_prodMk_left_of_joint hX hY hZ
    (indepFun_cond_fiber_of_condIndepFun hR hX (hY.prodMk hZ) hXYZ s)
    (indepFun_cond_fiber_of_condIndepFun hR hY hZ hYZ s)

theorem condIndepFun_coordinate_others
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {B : ι → Type*} [mB : ∀ i, MeasurableSpace (B i)]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} {hm : m ≤ mΩ} {F : ∀ i, Ω → B i}
    (hF : ∀ i, @Measurable Ω (B i) mΩ (mB i) (F i)) (hI : iCondIndepFun m hm F μ) (c : ι) :
    CondIndepFun m hm (F c) (fun ω => fun i : {i : ι // i ≠ c} => F i.val ω) μ := by
  let : MeasurableSpace Ω := mΩ
  have hle : ∀ i : ι, MeasurableSpace.comap (F i) (mB i) ≤ mΩ :=
    fun i => (hF i).comap_le
  have hd : Disjoint ({c} : Set ι) {i | i ≠ c} := by simp
  have h := condIndep_iSup_of_disjoint hle hI hd
  change CondIndep m
    (MeasurableSpace.comap (F c) (mB c))
    (MeasurableSpace.comap (fun ω => fun i : {i : ι // i ≠ c} => F i.val ω)
      inferInstance) hm μ
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ShiftedFieldVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {G : Ω → ℝ} {beta : ℝ}

lemma continuous_responseAttenuation {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Continuous (responseAttenuation theta) := by
  have ht := lipschitzWith_tanh_response.continuous
  exact (continuous_const.sub (ht.pow 2)).div
    (continuous_const.sub (continuous_const.mul (ht.pow 2)))
    (fun z => ne_of_gt (attenuation_denominator_pos hθ z))

end Probability

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ShiftedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

lemma shiftedLossCoefficient_pos {theta beta : ℝ} (hθ : theta ^ 2 < 1) :
    0 < shiftedLossCoefficient theta beta := by
  apply div_pos (sub_pos.mpr hθ)
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (Real.cosh_pos _)) (by positivity)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Transitivity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

theorem exists_treeAut_to_root {d : ℕ} (u : TreeVertex d) :
    ∃ g : TreeAut d, g.toEquiv u = ⟨[], List.IsChain.nil⟩ := by
  rcases u with ⟨w, hw⟩
  induction w with
  | nil => exact ⟨TreeAut.refl d, rfl⟩
  | cons a w ih =>
    have hw' : w.IsChain (· ≠ ·) := hw.tail
    obtain ⟨g, hg⟩ := ih hw'
    refine ⟨(prefixTreeAut a).trans g, ?_⟩
    change g.toEquiv (prefixFlip a ⟨a :: w, hw⟩) = _
    have hflip : prefixFlip a ⟨a :: w, hw⟩ = ⟨w, hw'⟩ := by
      apply Subtype.ext
      simp [prefixFlip, prefixFlipWord]
    rw [hflip]
    exact hg

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_LinearSignalTilt
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem linearSignalTilt_density_nonneg {a q : ℝ}
    (ha : |a| ≤ 1) (hq : |q| ≤ 1) : 0 ≤ 1 + a * q := by
  have hab : |a * q| ≤ 1 := by
    rw [abs_mul]
    calc
      |a| * |q| ≤ 1 * |q| := mul_le_mul_of_nonneg_right ha (abs_nonneg q)
      _ ≤ 1 := by simpa using hq
  have := (abs_le.mp hab).1
  linarith

theorem integrable_boundedSignal_mul {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (hf : Integrable f mu) :
    Integrable (fun x => q x * f x) mu := by
  refine hf.norm.mono' (hq.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [hqb] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

theorem integral_linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q f : Ω → ℝ} {a : ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ x ∂mu, |q x| ≤ 1) (ha : |a| ≤ 1) (hf : Integrable f mu) :
    (∫ x, f x ∂linearSignalTilt mu q a) =
      (∫ x, f x ∂mu) + a * ∫ x, q x * f x ∂mu := by
  rw [linearSignalTilt, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun x => (ENNReal.ofReal (1 + a * q x)).toReal • f x) =ᵐ[mu]
      (fun x => f x + a * (q x * f x)) := by
    filter_upwards [hqb] with x hx
    rw [ENNReal.toReal_ofReal (linearSignalTilt_density_nonneg ha hx), smul_eq_mul]
    ring
  rw [integral_congr_ae heq,
    integral_add hf ((integrable_boundedSignal_mul hq hqb hf).const_mul a),
    integral_const_mul]

theorem map_withDensity_comp {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {mu : Measure Ω} {f : Ω → X} {w : X → ENNReal}
    (hf : Measurable f) (hw : Measurable w) :
    Measure.map f (mu.withDensity (w ∘ f)) = (Measure.map f mu).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hw hf]
  rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SideSignalLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma sideSignalLossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < sideSignalLossCoefficient theta := by
  have hθsq : theta ^ 2 < 1 := by nlinarith
  exact mul_pos (mul_pos (shiftedLossCoefficient_pos hθsq) (sub_pos.mpr hθsq))
    (sq_pos_of_pos hθ0)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_StatisticSideSignalLoss
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurable_statisticMessage (theta : ℝ) : Measurable (statisticMessage theta) := by
  unfold statisticMessage Real.artanh
  fun_prop

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ComponentSignalAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

theorem measurable_posteriorMean {d : ℕ} (μ : Measure (TreeVertex d → IsingSpin))
    (c : Fin d) (t : ℝ≥0) : Measurable (posteriorMean μ c t) :=
  stronglyMeasurable_condExp.measurable.mono
    (PlantedInformation.observationSigma_le _ _) le_rfl

theorem lossCoefficient_pos {theta : ℝ} (hθ0 : 0 < theta) (hθ1 : theta < 1) :
    0 < lossCoefficient theta :=
  lt_min (div_pos (sideSignalLossCoefficient_pos hθ0 hθ1) (by norm_num)) (by norm_num)

theorem lossCoefficient_le_half (theta : ℝ) : lossCoefficient theta ≤ 1 / 2 :=
  min_le_right _ _

end Problem367.ComponentSignalAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_LatentObservationIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_product_jointLaw
    {Ω S A B C D : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure Ω) [IsFiniteMeasure P]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : Ω → S} {X : Ω → A} {Y : Ω → B}
    (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (hjoint : Measure.map (fun ω => (Z ω, X ω, Y ω)) P = ρ.prod (μ.prod ν))
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap Z) hZ.comap_le
      (fun ω => F (Z ω, X ω)) (fun ω => G (Z ω, Y ω)) P := by
  have he : MeasurePreserving (fun ω => (Z ω, X ω, Y ω)) P (ρ.prod (μ.prod ν)) :=
    ⟨hZ.prodMk (hX.prodMk hY), hjoint⟩
  have hbase := condIndepFun_latent_product ρ μ ν F G hF hG
  have hpull := condIndepFun_comp_measurePreserving P (ρ.prod (μ.prod ν))
    (fun ω => (Z ω, X ω, Y ω)) he (mS.comap Prod.fst) measurable_fst.comap_le
    (show Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) by fun_prop)
    (show Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hpull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyRootIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_3_rff45b3_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem map_root_ownNoise_branch_family {d : ℕ} {A : Type*}
    [MeasurableSpace A] (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.infinitePi (fun v => uniform01.prod (ν v))).map
      (fun U : TreeVertex d → ℝ × A =>
        (fairSpin (U (root d)).1, (U (root d)).2,
          fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      (uniform01.map fairSpin).prod ((ν (root d)).prod
        (Measure.infinitePi (fun c : Fin d =>
          Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))) := by
  have hbase := map_root_branch_family_of_sampler
    (fun v => uniform01.prod (ν v))
    (fun p : ℝ × A => (fairSpin p.1, p.2))
    ((measurable_fairSpin.comp measurable_fst).prodMk measurable_snd)
  have hroot : (uniform01.prod (ν (root d))).map
      (fun p : ℝ × A => (fairSpin p.1, p.2)) =
      (uniform01.map fairSpin).prod (ν (root d)) := by
    change (uniform01.prod (ν (root d))).map (Prod.map fairSpin id) = _
    rw [← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]
  rw [hroot] at hbase
  calc
    _ = ((Measure.infinitePi (fun v => uniform01.prod (ν v))).map
        (fun U : TreeVertex d → ℝ × A =>
          ((fairSpin (U (root d)).1, (U (root d)).2),
            fun c : Fin d => fun v : BranchVertex c => U v.val))).map
          MeasurableEquiv.prodAssoc := by
      have hmf : Measurable (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1) :=
        (measurable_fairSpin.comp measurable_fst).comp (measurable_pi_apply (root d))
      have hm : Measurable (fun U : TreeVertex d → ℝ × A =>
          ((fairSpin (U (root d)).1, (U (root d)).2),
            fun c : Fin d => fun v : BranchVertex c => U v.val)) :=
        (hmf.prodMk (by fun_prop)).prodMk (by fun_prop)
      rw [Measure.map_map (by fun_prop) hm]
      rfl
    _ = _ := by
      rw [hbase]
      exact (measurePreserving_prodAssoc (uniform01.map fairSpin) (ν (root d))
        (Measure.infinitePi (fun c : Fin d =>
          Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))).map_eq

theorem condIndepFun_noisy_factor_root_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1))
      ((measurable_fairSpin.comp measurable_fst).comp
        (measurable_pi_apply (root d))).comap_le
      (fun U => (fairSpin (U (root d)).1, (U (root d)).2))
      (fun U => fun c : Fin d =>
        ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
          fun v : BranchVertex c => (U v.val).2))
      (Measure.infinitePi (fun v => uniform01.prod (ν v))) := by
  let G : IsingSpin × (∀ c : Fin d, BranchVertex c → ℝ × A) →
      (∀ c : Fin d, (BranchVertex c → IsingSpin) × (BranchVertex c → A)) :=
    fun p c => (branchFactor theta c (p.1, fun v => (p.2 c v).1),
      fun v => (p.2 c v).2)
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro c
    exact ((measurable_branchFactor theta c).comp
      (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have h := condIndepFun_of_product_jointLaw
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    (uniform01.map fairSpin) (ν (root d))
    (Measure.infinitePi (fun c : Fin d =>
      Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))
    ((measurable_fairSpin.comp measurable_fst).comp (measurable_pi_apply (root d)))
    (measurable_snd.comp (measurable_pi_apply (root d)))
    (show Measurable (fun U : TreeVertex d → ℝ × A =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) from by fun_prop)
    (map_root_ownNoise_branch_family ν) id G measurable_id hG
  have hfun : (fun U : TreeVertex d → ℝ × A =>
      G (fairSpin (U (root d)).1, fun c v => U v.val)) =
      (fun U => fun c : Fin d =>
        ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
          fun v : BranchVertex c => (U v.val).2)) := by
    funext U c
    apply Prod.ext
    · exact (factor_branch_representation theta c (fun w => (U w).1)).symm
    · rfl
  simpa only [Function.comp_def, id_eq, hfun] using h

end RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_2_rff45b3_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem freeIsingMeasure_condIndepFun_noisy_root_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)))
      (fun z => fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
          fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let e : (TreeVertex d → ℝ × A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    fun U => (RootedBroadcast.factor theta (fun v => (U v).1), fun v => (U v).2)
  have he : MeasurePreserving e (Measure.infinitePi (fun v => uniform01.prod (ν v)))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) :=
    ⟨((RootedBroadcast.measurable_factor d theta).comp (by fun_prop)).prodMk
      (by fun_prop), RootedBroadcast.map_noisyBroadcast theta ν⟩
  apply condIndepFun_of_comp_measurePreserving
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) e he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from by fun_prop)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun c : Fin d => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
  have hroot (U : TreeVertex d → ℝ × A) :
      RootedBroadcast.factor theta (fun v => (U v).1) (RootedBroadcast.root d) =
      fairSpin (U (RootedBroadcast.root d)).1 := by
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e, hroot] using
    RootedBroadcast.condIndepFun_noisy_factor_root_branches theta ν

theorem HasFreeIsingLaw.condIndepFun_root_branch_observables
    {d : ℕ} {theta : ℝ} {A C D : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : IsingSpin × A → C)
    (G : (∀ c : Fin d, (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) → D)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => F (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)))
      (fun z => G (fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
          fun v : RootedBroadcast.BranchVertex c => z.2 v.val)))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact (freeIsingMeasure_condIndepFun_noisy_root_branches theta ν).comp hF hG

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchTransport
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin_3_rff45b3_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.measurePreserving_planted_relabel
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (ν : Measure A) [IsProbabilityMeasure ν]
    (g : TreeAut d) :
    MeasurePreserving (Prod.map (relabel g) (relabel g))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  apply (hμ.measurePreserving_relabel g).prod
  exact ⟨measurable_relabel g,
    Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchSeparation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurable_noisyBranchArray {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) : Measurable (noisyBranchArray (A := A) c) := by
  unfold noisyBranchArray
  fun_prop

theorem measurable_noisyRootOtherArray {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) : Measurable (noisyRootOtherArray (A := A) c) := by
  unfold noisyRootOtherArray noisyBranchArray
  fun_prop

local instance instMeasurableSingletonClassIsingSpin_4 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

theorem HasFreeIsingLaw.condIndepFun_noisy_root_others_branch
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (noisyRootOtherArray c) (noisyBranchArray c)
      (μ.prod (Measure.infinitePi ν)) := by
  have hbranches : iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (noisyBranchArray (A := A)) (μ.prod (Measure.infinitePi ν)) :=
    hμ.iCondIndepFun_noisy_branches h0 h1 ν
  have hothers := (condIndepFun_coordinate_others
    (fun b => measurable_noisyBranchArray (A := A) b) hbranches c).symm
  have hroot := hμ.condIndepFun_root_branch_observables h0 h1 ν id
    (fun p => ((fun b : {b : Fin d // b ≠ c} => p b.val), p c))
    measurable_id (by fun_prop)
  exact condIndepFun_prodMk_left_of_joint
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from by fun_prop)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun b : {b : Fin d // b ≠ c} => noisyBranchArray b.val z) from
      Measurable.of_eval (fun b => measurable_noisyBranchArray b.val))
    (measurable_noisyBranchArray c) hroot hothers

theorem HasFreeIsingLaw.condIndepFun_relabel_noisy_root_others_branch
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d) (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (g.toEquiv.symm (RootedBroadcast.root d))))
      ((measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comp
        measurable_fst).comap_le
      (noisyRootOtherArray c ∘ Prod.map (relabel g) (relabel g))
      (noisyBranchArray c ∘ Prod.map (relabel g) (relabel g))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := condIndepFun_comp_measurePreserving
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (Prod.map (relabel g) (relabel g)) (hμ.measurePreserving_planted_relabel ν g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (measurable_noisyRootOtherArray c) (measurable_noisyBranchArray c)
    (hμ.condIndepFun_noisy_root_others_branch h0 h1 (fun _ => ν) c)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map, relabel] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_BranchObservationRegression
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurable_noisyRootOtherDecode {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) (w : {w : TreeVertex d // ¬ [c] <+: w.val}) :
    Measurable (fun p : NoisyRootOtherData A c => noisyRootOtherDecode c p w) := by
  unfold noisyRootOtherDecode
  split_ifs <;> dsimp <;> fun_prop

theorem noisyRootOtherDecode_array {d : ℕ} {A : Type*} (c : Fin d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A))
    (w : {w : TreeVertex d // ¬ [c] <+: w.val}) :
    noisyRootOtherDecode c (noisyRootOtherArray c z) w = (z.1 w.val, z.2 w.val) := by
  unfold noisyRootOtherDecode
  split_ifs with hw
  · have hroot : w.val = RootedBroadcast.root d := Subtype.ext hw
    simp only [noisyRootOtherArray, hroot]
  · rfl

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurable_selectedPosterior {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    Measurable (selectedPosterior rho F v r) :=
  stronglyMeasurable_condExp.measurable.mono (selectedObservationField_le hF v) le_rfl

theorem selectedObservationField_comap_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (g : TreeAut d) :
    (selectedObservationField F v).comap (Prod.map (relabel g) (relabel g)) =
      selectedObservationField F (fun i => g.toEquiv.symm (v i)) := by
  unfold selectedObservationField
  rw [MeasurableSpace.comap_comp]
  rfl

theorem selectedObservationField_eq_of_range_eq {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) {v : ι → TreeVertex d} {w : κ → TreeVertex d}
    (hvw : Set.range v = Set.range w) :
    selectedObservationField F v = selectedObservationField F w :=
  le_antisymm (selectedObservationField_le_of_range_subset F hvw.subset)
    (selectedObservationField_le_of_range_subset F hvw.symm.subset)

theorem selectedPosterior_relabel_ae {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r ∘
        Prod.map (relabel g) (relabel g) =ᵐ[mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))]
      selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r) := by
  let := hmu.isProbabilityMeasure
  let rho := mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hi : Integrable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) rho := by
    apply Integrable.of_bound
      ((hsign.comp ((measurable_pi_apply r).comp measurable_fst)).aestronglyMeasurable) 1
    apply Filter.Eventually.of_forall
    intro p
    cases hs : p.1 r <;> norm_num [spinSign, hs]
  have hCE := condExp_comp_measurePreserving rho rho
    (Prod.map (relabel g) (relabel g))
    (PlantedStationarity.measurePreserving_planted_relabel hmu nu g)
    (selectedObservationField F v) (selectedObservationField_le hF v) hi
  rw [selectedObservationField_comap_relabel] at hCE
  exact hCE.symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ComponentPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem mem_range_componentIndexVertex {d : ℕ} {c : Fin d} {v : TreeVertex d} :
    v ∈ Set.range (componentIndexVertex (c := c)) ↔ ∃ w, v.1 = c :: w := by
  constructor
  · rintro ⟨⟨n, w⟩, rfl⟩
    exact ⟨w.1, rfl⟩
  · rintro ⟨w, hw⟩
    have hchain : (c :: w).IsChain (fun a b : Fin d => a ≠ b) := by
      rw [← hw]
      exact v.2
    refine ⟨⟨w.length, ⟨w, rfl, hchain⟩⟩, ?_⟩
    exact Subtype.ext hw.symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorTilt
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367

theorem setIntegral_spin_posterior_tilt
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    {F : Ω → ℝ} (hF : StronglyMeasurable[mSmall] F) (hFi : Integrable F mu)
    (a : IsingSpin) :
    ∫ x in {x | S x = a}, F x ∂mu = (1 / 2 : ℝ) *
      ∫ x, F x * (1 + spinSign a * mu[fun y => spinSign (S y) | mSmall] x) ∂mu := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hSm : AEStronglyMeasurable (fun x => spinSign (S x)) mu :=
    (hsign.comp hS).aestronglyMeasurable
  have hSb : ∀ᵐ x ∂mu, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    cases hs : S x <;> norm_num [spinSign, hs]
  have hSi : Integrable (fun x => spinSign (S x)) mu := Integrable.of_bound hSm 1 hSb
  have hFSi : Integrable (fun x => F x * spinSign (S x)) mu := hFi.mul_bdd hSm hSb
  have hpull := condExp_mul_of_stronglyMeasurable_left hF hFSi hSi
  have hFMi : Integrable
      (fun x => F x * mu[fun y => spinSign (S y) | mSmall] x) mu :=
    integrable_condExp.congr hpull
  have hint : (∫ x, F x * spinSign (S x) ∂mu) =
      ∫ x, F x * mu[fun y => spinSign (S y) | mSmall] x ∂mu := by
    rw [← integral_condExp (m := mSmall) hm]
    exact integral_congr_ae hpull
  have hA : MeasurableSet {x | S x = a} :=
    (show MeasurableSet ({a} : Set IsingSpin) from trivial).preimage hS
  have hindicator : ({x | S x = a} : Set Ω).indicator F =
      fun x => (1 / 2 : ℝ) * (F x + spinSign a * (F x * spinSign (S x))) := by
    funext x
    cases hs : S x <;> cases a <;> simp [Set.indicator, hs, spinSign] <;> ring
  rw [← integral_indicator hA, hindicator, integral_const_mul,
    integral_add hFi (hFSi.const_mul (spinSign a)), integral_const_mul, hint]
  congr 1
  rw [← integral_const_mul, ← integral_add hFi (hFMi.const_mul (spinSign a))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

theorem integral_cond_spin_posterior_tilt
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    {F : Ω → ℝ} (hF : StronglyMeasurable[mSmall] F) (hFi : Integrable F mu)
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    ∫ x, F x ∂ProbabilityTheory.cond mu {x | S x = a} =
      ∫ x, F x * (1 + spinSign a * mu[fun y => spinSign (S y) | mSmall] x) ∂mu := by
  rw [ProbabilityTheory.cond, integral_smul_measure, hfair]
  rw [setIntegral_spin_posterior_tilt hm hS hF hFi a]
  norm_num
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_ObservationLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem map_cond_spin_observation_eq_linearSignalTilt
    {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {mY : MeasurableSpace Y}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → Y} (hX : Measurable X) {q : Y → ℝ} (hq : Measurable q)
    (hpost : mu[fun x => spinSign (S x) | mY.comap X] =ᵐ[mu] fun x => q (X x))
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    Measure.map X (ProbabilityTheory.cond mu {x | S x = a}) =
      linearSignalTilt (Measure.map X mu) q (spinSign a) := by
  have hQ : Measurable (fun x => q (X x)) := hq.comp hX
  have hSb : ∀ᵐ x ∂mu, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    cases hs : S x <;> norm_num [spinSign, hs]
  have hQb : ∀ᵐ x ∂mu, |q (X x)| ≤ 1 := by
    have hb := ae_bdd_norm_condExp_of_ae_bdd_norm (m := mY.comap X) hSb
    filter_upwards [hb, hpost] with x hx hp
    simpa only [hp, Real.norm_eq_abs] using hx
  have hQi : Integrable (fun x => q (X x)) mu :=
    Integrable.of_bound hQ.aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hQb)
  have ha : |spinSign a| ≤ 1 := by cases a <;> norm_num [spinSign]
  let : IsProbabilityMeasure (ProbabilityTheory.cond mu {x | S x = a}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (by rw [hfair]; norm_num)
  have hdi := (integrable_const (1 : ℝ)).add (hQi.const_mul (spinSign a))
  let : IsFiniteMeasure (linearSignalTilt mu (fun x => q (X x)) (spinSign a)) :=
    isFiniteMeasure_withDensity_ofReal hdi.hasFiniteIntegral
  have hmap : Measure.map X (linearSignalTilt mu (fun x => q (X x)) (spinSign a)) =
      linearSignalTilt (Measure.map X mu) q (spinSign a) := by
    unfold linearSignalTilt
    exact map_withDensity_comp (mu := mu) (f := X)
      (w := fun y => ENNReal.ofReal (1 + spinSign a * q y)) hX
      (ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_const.mul hq)))
  rw [← hmap]
  ext t ht
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  let f : Y → ℝ := t.indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator ht
  have hfint : Integrable (fun x => f (X x)) mu := by
    refine Integrable.of_bound (hfm.comp hX).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : X x ∈ t <;> simp [f, hx])
  have hfsmall : StronglyMeasurable[mY.comap X] (fun x => f (X x)) :=
    (hfm.comp (measurable_iff_comap_le.mpr le_rfl)).stronglyMeasurable
  have hint : (∫ y, f y ∂Measure.map X (ProbabilityTheory.cond mu {x | S x = a})) =
      ∫ y, f y ∂Measure.map X (linearSignalTilt mu (fun x => q (X x)) (spinSign a)) := by
    rw [integral_map hX.aemeasurable hfm.aestronglyMeasurable,
      integral_map hX.aemeasurable hfm.aestronglyMeasurable,
      integral_cond_spin_posterior_tilt hX.comap_le hS hfsmall hfint a hfair,
      integral_linearSignalTilt hQ hQb ha hfint,
      ← integral_const_mul,
      ← integral_add hfint ((integrable_boundedSignal_mul hQ hQb hfint).const_mul (spinSign a))]
    apply integral_congr_ae
    filter_upwards [hpost] with x hx
    rw [hx]
    ring
  simpa [f, integral_indicator ht, measureReal_def] using hint

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootComponentAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

local instance rootComponentAttenuationMeasurableSingletonIsingSpin_rff45b3_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance rootComponentAttenuationNonemptyIsingSpin_rff45b3_1 : Nonempty IsingSpin := ⟨.neg⟩
theorem HasFreeIsingLaw.condIndepFun_root_others_componentPosterior
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    let q := selectedPosterior P F (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c)
    noisyRootOtherArray c ⟂ᵢ[fun z => z.1 (RootedBroadcast.root d),
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst); P] q := by
  dsimp only
  let v (u : ComponentIndex c) : RootedBroadcast.BranchVertex c :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G : (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A) → (ComponentIndex c → B) :=
    fun p u => F (p.1 (v u)) (p.2 (v u))
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (RootedBroadcast.BranchVertex c → IsingSpin) ×
        (RootedBroadcast.BranchVertex c → A) => (p.1 (v u), p.2 (v u))) from by fun_prop)
  have hObs : Measurable[(inferInstance : MeasurableSpace
      ((RootedBroadcast.BranchVertex c → IsingSpin) ×
        (RootedBroadcast.BranchVertex c → A))).comap (noisyBranchArray c)]
      (fun p i => F (p.1 (componentIndexVertex (c := c) i))
        (p.2 (componentIndexVertex i))) :=
    hG.comp (comap_measurable (noisyBranchArray c))
  have hq : Measurable[(inferInstance : MeasurableSpace
      ((RootedBroadcast.BranchVertex c → IsingSpin) ×
        (RootedBroadcast.BranchVertex c → A))).comap (noisyBranchArray c)]
      (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
        F (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c)) :=
    stronglyMeasurable_condExp.measurable.mono hObs.comap_le le_rfl
  obtain ⟨Q, hQ, hqQ⟩ := hq.exists_eq_measurable_comp
  rw [hqQ]
  exact (hμ.condIndepFun_noisy_root_others_branch h0 h1 (fun _ => ν) c).comp
    measurable_id hQ

namespace ComponentSignalAttenuation

open PlantedSymmetry

local instance rootComponentAttenuationMeasurableSingletonIsingSpin_rff45b3_2 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
local instance rootComponentAttenuationNonemptyIsingSpin_rff45b3_2 : Nonempty IsingSpin := ⟨.neg⟩
theorem condExp_attenuation_le_critical_root_others
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    {B : Type*} [mB : MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (G : NoisyRootOtherData ℝ c → B) (hG : Measurable G)
    (shift : B → ℝ) (hs : Measurable shift) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let X := G ∘ noisyRootOtherArray c
    ∀ᵐ w ∂P,
      (P[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (posteriorMean μ c t v)) ^ 2 |
          mB.comap X]) w ≤
        1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  let := hμ.isProbabilityMeasure
  dsimp only
  have hchannel : Measurable (Function.uncurry
      (fun s z => (t : ℝ) * spinSign s + z)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hind := (hμ.condIndepFun_root_others_componentPosterior
    (by linarith) hθ1.le (gaussianReal 0 t) hchannel c).comp hG measurable_id
  apply condExp_attenuation_le_critical_of_condIndep (eta := spinSign) hμ hθ0 hθ1 c hcritical ht
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst)
    (hG.comp (measurable_noisyRootOtherArray c)) (measurable_posteriorMean μ c t)
    hs hind
  · exact Filter.Eventually.of_forall (fun w => by
      cases h : w.1 (RootedBroadcast.root d) <;> norm_num [spinSign, h])
  · exact Filter.Eventually.of_forall (fun w =>
      condDistrib_posteriorMean_root hμ (by linarith) hθ1.le c t _)

end ComponentSignalAttenuation

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_RelabeledComponentAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry

theorem condExp_attenuation_le_critical_relabel_root_others
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (c : Fin d) (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (g : TreeAut d)
    {B : Type*} [mB : MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (G : NoisyRootOtherData ℝ c → B) (hG : Measurable G)
    (shift : B → ℝ) (hs : Measurable shift) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let X := (G ∘ noisyRootOtherArray c) ∘ Prod.map (relabel g) (relabel g)
    let Q := selectedPosterior P (fun s z => (t : ℝ) * spinSign s + z)
      (fun i => g.toEquiv.symm (componentIndexVertex (c := c) i))
      (g.toEquiv.symm (RootedBroadcast.branchRoot c))
    ∀ᵐ w ∂P,
      (P[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
        1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  let := hμ.isProbabilityMeasure
  let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let T : ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) →
      ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    Prod.map (relabel g) (relabel g)
  let X := G ∘ noisyRootOtherArray (A := ℝ) c
  let f := fun v => responseAttenuation theta
    (shift (X v) + statisticMessage theta (posteriorMean μ c t v)) ^ 2
  have hX : Measurable X := hG.comp (measurable_noisyRootOtherArray c)
  have hθsq : theta ^ 2 ≤ 1 := by nlinarith
  have hfm : Measurable f :=
    ((continuous_responseAttenuation hθsq).measurable.comp
      ((hs.comp hX).add ((measurable_statisticMessage theta).comp
        (measurable_posteriorMean μ c t)))).pow_const 2
  have hfi : Integrable f P := by
    apply (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable
    filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hpos := responseAttenuation_pos hθsq
      (shift (X v) + statisticMessage theta (posteriorMean μ c t v))
    have hle := responseAttenuation_le_one hθsq
      (shift (X v) + statisticMessage theta (posteriorMean μ c t v))
    dsimp only [f]
    nlinarith
  have hmp : MeasurePreserving T P P :=
    PlantedStationarity.measurePreserving_planted_relabel hμ (gaussianReal 0 t) g
  have hCE := condExp_comp_measurePreserving P P T hmp (mB.comap X) hX.comap_le hfi
  have hbase := hmp.quasiMeasurePreserving.ae
    (condExp_attenuation_le_critical_root_others hμ hθ0 hθ1 c hcritical ht G hG shift hs)
  have hchannel : Measurable (Function.uncurry
      (fun s z => (t : ℝ) * spinSign s + z)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hpost := selectedPosterior_relabel_ae hμ (gaussianReal 0 t) hchannel
    (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) g
  have hfc : f ∘ T =ᵐ[P] fun v => responseAttenuation theta
      (shift ((X ∘ T) v) + statisticMessage theta
        (selectedPosterior P (fun s z => (t : ℝ) * spinSign s + z)
          (fun i => g.toEquiv.symm (componentIndexVertex (c := c) i))
          (g.toEquiv.symm (RootedBroadcast.branchRoot c)) v)) ^ 2 := by
    filter_upwards [hpost] with v hv
    exact congrArg (fun q => responseAttenuation theta
      (shift ((X ∘ T) v) + statisticMessage theta q) ^ 2) hv
  have hcongr := condExp_congr_ae (m := mB.comap (X ∘ T)) hfc
  rw [MeasurableSpace.comap_comp] at hCE
  filter_upwards [hCE, hcongr, hbase] with w hw hc hb
  exact hc.symm.trans_le (hw.trans_le hb)

end Problem367.ComponentSignalAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusionMixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem binaryFusion_density_eq_mixture {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    (1 / 2 : ENNReal) * (ENNReal.ofReal (1 + u) * ENNReal.ofReal (1 + v)) +
      (1 / 2 : ENNReal) * (ENNReal.ofReal (1 - u) * ENNReal.ofReal (1 - v)) =
        ENNReal.ofReal (1 + u * v) := by
  have hpu : 0 ≤ 1 + u := by have := (abs_lt.mp hu).1; linarith
  have hpv : 0 ≤ 1 + v := by have := (abs_lt.mp hv).1; linarith
  have hmu : 0 ≤ 1 - u := by have := (abs_lt.mp hu).2; linarith
  have hmv : 0 ≤ 1 - v := by have := (abs_lt.mp hv).2; linarith
  have hh : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rw [hh, ← ENNReal.ofReal_mul hpu, ← ENNReal.ofReal_mul hmu,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_add (by positivity : 0 ≤ (1 / 2 : ℝ) * ((1 + u) * (1 + v)))
      (by positivity : 0 ≤ (1 / 2 : ℝ) * ((1 - u) * (1 - v)))]
  congr 1
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorCertification
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem condExp_spin_eq_of_restricted_density
    {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {mY : MeasurableSpace Y}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → Y} (hX : Measurable X) {q : Y → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ y ∂Measure.map X mu, |q y| ≤ 1)
    (hdensity : Measure.map X (mu.restrict {x | S x = IsingSpin.pos}) =
      (Measure.map X mu).withDensity (fun y => ENNReal.ofReal ((1 + q y) / 2))) :
    mu[fun x => spinSign (S x) | mY.comap X] =ᵐ[mu] fun x => q (X x) := by
  let E : Set Ω := {x | S x = IsingSpin.pos}
  have hE : MeasurableSet E :=
    (show MeasurableSet ({IsingSpin.pos} : Set IsingSpin) from trivial).preimage hS
  let I : Ω → ℝ := E.indicator (fun _ => 1)
  have hI : Integrable I mu := (integrable_const (1 : ℝ)).indicator hE
  have hsrc : (fun x => ((mu.restrict E).rnDeriv mu x).toReal) =ᵐ[mu] I := by
    filter_upwards [Measure.rnDeriv_restrict_self mu hE] with x hx
    rw [hx]
    by_cases hxE : x ∈ E <;> simp [I, hxE]
  have hRN := toReal_rnDeriv_map (Measure.absolutelyContinuous_restrict (μ := mu) (s := E)) hX
  have hpost :
      (fun x => ((Measure.map X (mu.restrict E)).rnDeriv (Measure.map X mu) (X x)).toReal)
        =ᵐ[mu] mu[I | mY.comap X] :=
    hRN.trans (condExp_congr_ae hsrc)
  have htarg :
      (fun x => ((Measure.map X (mu.restrict E)).rnDeriv (Measure.map X mu) (X x)).toReal)
        =ᵐ[mu] fun x => (1 + q (X x)) / 2 := by
    have hderiv := Measure.rnDeriv_withDensity (Measure.map X mu)
      (show Measurable (fun y => ENNReal.ofReal ((1 + q y) / 2)) by fun_prop)
    rw [← hdensity] at hderiv
    filter_upwards [ae_of_ae_map hX.aemeasurable hderiv,
      ae_of_ae_map hX.aemeasurable hqb] with x hx hxb
    rw [hx, ENNReal.toReal_ofReal]
    have := (abs_le.mp hxb).1
    linarith
  have hIp : mu[I | mY.comap X] =ᵐ[mu] fun x => (1 + q (X x)) / 2 :=
    hpost.symm.trans htarg
  have hsrepr : (fun x => spinSign (S x)) = (2 : ℝ) • I - (fun _ => 1) := by
    funext x
    cases hs : S x <;> norm_num [I, E, hs, spinSign]
  rw [hsrepr]
  have hsub := condExp_sub (hI.smul (2 : ℝ)) (integrable_const (1 : ℝ)) (mY.comap X)
  have hmul := condExp_smul (μ := mu) (2 : ℝ) I (mY.comap X)
  filter_upwards [hsub, hmul, hIp] with x hxsub hxmul hxI
  rw [hxsub, Pi.sub_apply, hxmul, Pi.smul_apply, smul_eq_mul,
    condExp_const hX.comap_le, hxI]
  ring

theorem condExp_spin_eq_of_conditional_linearTilt
    {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {mY : MeasurableSpace Y}
    {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → Y} (hX : Measurable X) {q : Y → ℝ} (hq : Measurable q)
    (hqb : ∀ᵐ y ∂Measure.map X mu, |q y| ≤ 1)
    (hfair : mu {x | S x = IsingSpin.pos} = (1 / 2 : ENNReal))
    (hcond : Measure.map X (ProbabilityTheory.cond mu {x | S x = IsingSpin.pos}) =
      linearSignalTilt (Measure.map X mu) q 1) :
    mu[fun x => spinSign (S x) | mY.comap X] =ᵐ[mu] fun x => q (X x) := by
  apply condExp_spin_eq_of_restricted_density hS hX hq hqb
  have hscaled := congrArg (fun nu : Measure Y => (1 / 2 : ENNReal) • nu) hcond
  rw [ProbabilityTheory.cond, Measure.map_smul, hfair, smul_smul] at hscaled
  norm_num at hscaled
  rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤), one_smul] at hscaled
  rw [hscaled, linearSignalTilt, ← withDensity_smul (2⁻¹) (by fun_prop)]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [Pi.smul_apply, smul_eq_mul, one_mul]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp [div_eq_mul_inv, mul_comm]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorFusion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Problem367

theorem measure_eq_fair_spin_mixture
    {Ω : Type*} [MeasurableSpace Ω] {mu : Measure Ω} [IsFiniteMeasure mu]
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, mu {x | S x = a} = (1 / 2 : ENNReal)) :
    mu = (1 / 2 : ENNReal) • cond mu {x | S x = .pos} +
      (1 / 2 : ENNReal) • cond mu {x | S x = .neg} := by
  have h := sum_meas_smul_cond_fiber hS mu
  change (∑ a : IsingSpin, mu {x | S x = a} • cond mu {x | S x = a}) = mu at h
  simpa only [sum_isingSpin, hfair, add_comm] using h.symm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_ObservationFusion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

private theorem ae_observation_pair_bounds
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {q : A → ℝ} {r : B → ℝ}
    (hq : ∀ᵐ x ∂mu, |q x| < 1) (hr : ∀ᵐ y ∂nu, |r y| < 1) :
    ∀ᵐ p ∂mu.prod nu, |q p.1| < 1 ∧ |r p.2| < 1 := by
  have hq' : ∀ᵐ p ∂mu.prod nu, |q p.1| < 1 :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hq
  have hr' : ∀ᵐ p ∂mu.prod nu, |r p.2| < 1 :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae hr
  exact hq'.and hr'

theorem observationFusionJointLaw_eq_mixture
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {q : A → ℝ} {r : B → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hqb : ∀ᵐ x ∂mu, |q x| < 1) (hrb : ∀ᵐ y ∂nu, |r y| < 1) :
    (1 / 2 : ENNReal) • ((linearSignalTilt mu q 1).prod (linearSignalTilt nu r 1)) +
      (1 / 2 : ENNReal) • ((linearSignalTilt mu q (-1)).prod (linearSignalTilt nu r (-1))) =
        observationFusionJointLaw mu nu q r := by
  unfold linearSignalTilt observationFusionJointLaw
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [prod_withDensity (by fun_prop) (by fun_prop),
    prod_withDensity (by fun_prop) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_add_left (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_observation_pair_bounds hqb hrb] with p hp
  exact binaryFusion_density_eq_mixture hp.1 hp.2

theorem observationFusion_positive_product_eq_tilt
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {nu : Measure B} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {q : A → ℝ} {r : B → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hqb : ∀ᵐ x ∂mu, |q x| < 1) (hrb : ∀ᵐ y ∂nu, |r y| < 1) :
    (linearSignalTilt mu q 1).prod (linearSignalTilt nu r 1) =
      linearSignalTilt (observationFusionJointLaw mu nu q r)
        (fun p => binaryFusion (q p.1) (r p.2)) 1 := by
  unfold linearSignalTilt observationFusionJointLaw
  rw [prod_withDensity (by fun_prop) (by fun_prop),
    ← withDensity_mul _ (by fun_prop) (by unfold binaryFusion; fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_observation_pair_bounds hqb hrb] with p hp
  simp only [one_mul, Pi.mul_apply]
  have hpq : 0 ≤ 1 + q p.1 := by have := (abs_lt.mp hp.1).1; linarith
  have hden := binaryFusion_denominator_pos hp.1 hp.2
  rw [← ENNReal.ofReal_mul hpq, ← ENNReal.ofReal_mul hden.le]
  congr 1
  unfold binaryFusion
  field_simp
  ring

theorem condExp_spin_given_observation_pair_eq_binaryFusion
    {Ω A B : Type*} {mΩ : MeasurableSpace Ω} {mA : MeasurableSpace A}
    {mB : MeasurableSpace B} {rho : Measure Ω} [IsProbabilityMeasure rho]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    {q : A → ℝ} {r : B → ℝ} (hq : Measurable q) (hr : Measurable r)
    (hpostX : rho[fun x => spinSign (S x) | mA.comap X] =ᵐ[rho] fun x => q (X x))
    (hpostY : rho[fun x => spinSign (S x) | mB.comap Y] =ᵐ[rho] fun x => r (Y x))
    (hqb : ∀ᵐ x ∂rho, |q (X x)| < 1) (hrb : ∀ᵐ x ∂rho, |r (Y x)| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, IndepFun X Y (cond rho {x | S x = a})) :
    rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] =ᵐ[rho]
      fun x => binaryFusion (q (X x)) (r (Y x)) := by
  let mu := Measure.map X rho
  let nu := Measure.map Y rho
  haveI : IsProbabilityMeasure mu := Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure nu := Measure.isProbabilityMeasure_map hY.aemeasurable
  have hqm : ∀ᵐ x ∂mu, |q x| < 1 :=
    (ae_map_iff hX.aemeasurable (measurableSet_lt hq.abs measurable_const)).2 hqb
  have hrm : ∀ᵐ y ∂nu, |r y| < 1 :=
    (ae_map_iff hY.aemeasurable (measurableSet_lt hr.abs measurable_const)).2 hrb
  have hpair (a : IsingSpin) : Measure.map (fun x => (X x, Y x)) (cond rho {x | S x = a}) =
      (linearSignalTilt mu q (spinSign a)).prod (linearSignalTilt nu r (spinSign a)) := by
    let : IsProbabilityMeasure (cond rho {x | S x = a}) :=
      cond_isProbabilityMeasure (by rw [hfair]; norm_num)
    rw [(hInd a).map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
      map_cond_spin_observation_eq_linearSignalTilt hS hX hq hpostX a (hfair a),
      map_cond_spin_observation_eq_linearSignalTilt hS hY hr hpostY a (hfair a)]
  have hjoint : Measure.map (fun x => (X x, Y x)) rho =
      observationFusionJointLaw mu nu q r := by
    calc
      _ = Measure.map (fun x => (X x, Y x))
          ((1 / 2 : ENNReal) • cond rho {x | S x = .pos} +
           (1 / 2 : ENNReal) • cond rho {x | S x = .neg}) := by
        rw [← measure_eq_fair_spin_mixture hS hfair]
      _ = _ := by
        rw [Measure.map_add _ _ (hX.prodMk hY),
          Measure.map_smul,
          Measure.map_smul,
          hpair .pos, hpair .neg]
        exact observationFusionJointLaw_eq_mixture hq hr hqm hrm
  apply condExp_spin_eq_of_conditional_linearTilt hS (hX.prodMk hY)
    (show Measurable (fun p : A × B => binaryFusion (q p.1) (r p.2)) by
      unfold binaryFusion
      fun_prop)
  · rw [hjoint]
    have hb : ∀ᵐ p ∂observationFusionJointLaw mu nu q r, |q p.1| < 1 ∧ |r p.2| < 1 :=
      (withDensity_absolutelyContinuous (mu.prod nu)
        (fun p => ENNReal.ofReal (1 + q p.1 * r p.2))).ae_le
          (ae_observation_pair_bounds hqm hrm)
    filter_upwards [hb] with p hp
    exact (abs_binaryFusion_lt_one hp.1 hp.2).le
  · exact hfair .pos
  · rw [hpair .pos, hjoint]
    exact observationFusion_positive_product_eq_tilt hq hr hqm hrm

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_FusionSup
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance localInst_rff45b3_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem condExp_spin_comap_sup_eq_binaryFusion
    {Ω A B : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {S : Ω → IsingSpin} {X : Ω → A} {Y : Ω → B}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hfair : ∀ a : IsingSpin, P {ω | S ω = a} = (1 / 2 : ENNReal))
    (hInd : X ⟂ᵢ[S, hS; P] Y)
    (hL : ∀ᵐ ω ∂P, |(P[fun ω => spinSign (S ω) | mA.comap X]) ω| < 1)
    (hR : ∀ᵐ ω ∂P, |(P[fun ω => spinSign (S ω) | mB.comap Y]) ω| < 1) :
    P[fun ω => spinSign (S ω) | mA.comap X ⊔ mB.comap Y] =ᵐ[P]
      fun ω => binaryFusion (P[fun ω => spinSign (S ω) | mA.comap X] ω)
        (P[fun ω => spinSign (S ω) | mB.comap Y] ω) := by
  obtain ⟨q, hq, hqe⟩ :=
    (show Measurable[mA.comap X]
      (P[fun ω => spinSign (S ω) | mA.comap X]) from
      stronglyMeasurable_condExp.measurable).exists_eq_measurable_comp
  obtain ⟨r, hr, hre⟩ :=
    (show Measurable[mB.comap Y]
      (P[fun ω => spinSign (S ω) | mB.comap Y]) from
      stronglyMeasurable_condExp.measurable).exists_eq_measurable_comp
  have hpostX : P[fun ω => spinSign (S ω) | mA.comap X] =ᵐ[P] fun ω => q (X ω) :=
    Filter.Eventually.of_forall (congrFun hqe)
  have hpostY : P[fun ω => spinSign (S ω) | mB.comap Y] =ᵐ[P] fun ω => r (Y ω) :=
    Filter.Eventually.of_forall (congrFun hre)
  have h := condExp_spin_given_observation_pair_eq_binaryFusion hS hX hY hq hr
    hpostX hpostY (by simpa only [hqe, Function.comp_apply] using hL)
    (by simpa only [hre, Function.comp_apply] using hR) hfair
    (fun a => indepFun_cond_fiber_of_condIndepFun hS hX hY hInd a)
  simpa only [Prod.instMeasurableSpace, MeasurableSpace.comap_prodMk,
    hqe, hre, Function.comp_apply] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem condExp_tanh_bounds_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K)) :
    ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₁]) ω ∧
      (μ[f | m₁]) ω ≤ Real.tanh (X ω + K) := by
  have h₁ : m₁ ≤ m := h₁₂.trans h₂
  have hL : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω - K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.sub stronglyMeasurable_const)
  have hU : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω + K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.add stronglyMeasurable_const)
  have iL : Integrable (fun ω => Real.tanh (X ω - K)) μ := by
    apply Integrable.of_bound (hL.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω - K)).le
  have iU : Integrable (fun ω => Real.tanh (X ω + K)) μ := by
    apply Integrable.of_bound (hU.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω + K)).le
  have hlo := condExp_mono (m := m₁) iL integrable_condExp
    (hb.mono fun ω hω => hω.1)
  have hhi := condExp_mono (m := m₁) integrable_condExp iU
    (hb.mono fun ω hω => hω.2)
  rw [condExp_of_stronglyMeasurable h₁ hL iL] at hlo
  rw [condExp_of_stronglyMeasurable h₁ hU iU] at hhi
  filter_upwards [hlo, hhi, condExp_condExp_of_le (f := f) h₁₂ h₂] with ω hLω hUω hTω
  rw [hTω] at hLω hUω
  exact ⟨hLω, hUω⟩

theorem condExp_field_bound_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, (μ[f | m₂]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₂]) ω) - X ω| ≤ K) :
    ∀ᵐ ω ∂μ, (μ[f | m₁]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₁]) ω) - X ω| ≤ K := by
  have hmono : Monotone Real.tanh := by
    apply monotone_of_deriv_nonneg
    · intro x
      exact (hasDerivAt_tanh_response x).differentiableAt
    · intro x
      rw [(hasDerivAt_tanh_response x).deriv]
      exact (sub_pos.mpr (Real.tanh_sq_lt_one x)).le
  have hs : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K) := by
    filter_upwards [hb] with ω hω
    have hlo := hmono (show X ω - K ≤ Real.artanh ((μ[f | m₂]) ω) by
      linarith [(abs_le.mp hω.2).1])
    have hhi := hmono (show Real.artanh ((μ[f | m₂]) ω) ≤ X ω + K by
      linarith [(abs_le.mp hω.2).2])
    rw [Real.tanh_artanh hω.1] at hlo hhi
    exact ⟨hlo, hhi⟩
  filter_upwards [condExp_tanh_bounds_of_le (m := m) μ h₁₂ h₂ hX hs] with ω hω
  have h := posterior_field_limit_of_tanh_bounds
    (u := fun _ : ℕ => (μ[f | m₁]) ω) tendsto_const_nhds (fun _ => hω)
  exact ⟨h.1, h.2.1⟩

theorem HasFreeIsingLaw.selected_gaussian_posterior_field_bound
    {d : ℕ} {ι : Type*} {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (hr : r ∈ Set.range v) :
    ∀ᵐ p ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p) -
          PlantedSymmetry.observation t p r| ≤ (d : ℝ) * β := by
  let := hμ.isProbabilityMeasure
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hsub : selectedObservationField F v ≤
      PlantedSymmetry.observationSigma (TreeVertex d) t := by
    change selectedObservationField F v ≤ selectedObservationField F id
    apply selectedObservationField_le_of_range_subset F
    intro w hw
    exact ⟨w, rfl⟩
  have hX : StronglyMeasurable[selectedObservationField F v]
      (fun p => PlantedSymmetry.observation t p r) := by
    obtain ⟨i, rfl⟩ := hr
    exact ((measurable_pi_apply i).comp (comap_measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        fun j => F (p.1 (v j)) (p.2 (v j))))).stronglyMeasurable
  exact condExp_field_bound_of_le
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hsub
    (PlantedSymmetry.observationSigma_le (TreeVertex d) t) hX
    (hμ.gaussian_posterior_field_bound hβ t r)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideBranches
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

theorem sideColor_ne_outgoing {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) (hi : i.1 + 1 < v.1.length) :
    sideColor hd v i ≠ v.1[i.1 + 1] := by
  have h := (Classical.choose_spec (Fin.exists_ne_and_ne_of_two_lt v.1[i]
    (v.1.getD (i.1 + 1) v.1[i]) (by omega))).2
  change sideColor hd v i ≠ v.1.getD (i.1 + 1) v.1[i] at h
  rw [List.getD_eq_getElem _ _ hi] at h
  exact h

private theorem not_prefix_wrong_color {α : Type*} (w : List α) {n : ℕ}
    (hn : n < w.length) {c : α} (hc : c ≠ w[n]) :
    ¬ w.take n ++ [c] <+: w := by
  intro h
  have hlen : (w.take n).length = n := by
    simp only [List.length_take, Nat.min_eq_left hn.le]
  have hidx : n < (w.take n ++ [c]).length := by
    simp only [List.length_append, hlen, List.length_singleton]
    omega
  have he := h.getElem hidx
  have hread : (w.take n ++ [c])[n] = c := by
    simpa only [hlen, Nat.sub_self, List.getElem_cons_zero] using
      (List.getElem_append_right (as := w.take n) (bs := [c])
        (i := n) (h₂ := hidx) (by omega))
  exact hc (hread.symm.trans he)

theorem sideVertex_not_prefix {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : ¬ (sideVertex hd v i).1 <+: v.1 := by
  by_cases hi : i.1 + 1 < v.1.length
  · exact not_prefix_wrong_color v.1 hi (sideColor_ne_outgoing hd v i hi)
  · intro h
    have := h.length_le
    rw [sideVertex_length] at this
    omega

theorem cone_mono {d : ℕ} {r s : TreeVertex d} (h : r.1 <+: s.1) :
    cone s ⊆ cone r := fun _ hu => h.trans hu

theorem path_vertex_not_mem_sideCone {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) (k : ℕ) :
    ConnectedHull.takeVertex v k ∉ cone (sideVertex hd v i) := by
  intro h
  exact sideVertex_not_prefix hd v i (h.trans (List.take_prefix k v.1))

theorem sideCone_disjoint_later_forward {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) {i j : Fin v.1.length} (hij : i < j) :
    Disjoint (cone (sideVertex hd v i))
      (cone (ConnectedHull.takeVertex v (j.1 + 1))) := by
  apply Set.disjoint_left.mpr
  intro u hu hv
  have hlen : (sideVertex hd v i).1.length ≤
      (ConnectedHull.takeVertex v (j.1 + 1)).1.length := by
    rw [sideVertex_length]
    change i.1 + 2 ≤ (v.1.take (j.1 + 1)).length
    rw [List.length_take, Nat.min_eq_left (by omega : j.1 + 1 ≤ v.1.length)]
    exact Nat.succ_le_succ (Fin.lt_def.mp hij)
  have hp := List.prefix_of_prefix_length_le hu hv hlen
  exact sideVertex_not_prefix hd v i (hp.trans (List.take_prefix _ _))

theorem sideCone_subset_forward {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : cone (sideVertex hd v i) ⊆
      cone (ConnectedHull.takeVertex v (i.1 + 1)) :=
  cone_mono (List.prefix_append _ _)

theorem edge_leaving_cone {d : ℕ} {r u w : TreeVertex d}
    (hu : u ∈ cone r) (hw : w ∉ cone r) (huw : treeAdj u w) :
    u = r ∧ w = parentVertex r := by
  have hur : u = r := by
    by_contra hne
    exact hw (treeAdj_preserves_prefix hu huw hne)
  subst u
  refine ⟨rfl, ?_⟩
  rcases huw with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact False.elim (hw (by
      change r.1 <+: w.1
      rw [hc]
      exact List.prefix_append _ _))
  · apply Subtype.ext
    change w.1 = r.1.dropLast
    rw [hc]
    simp

theorem reachable_in_cone {d : ℕ} {r u : TreeVertex d} (hu : u ∈ cone r) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ∈ cone r ∧ y ∈ cone r ∧ treeAdj x y) r u := by
  have aux : ∀ n : ℕ, ∀ u : TreeVertex d, u.1.length = n → u ∈ cone r →
      Relation.ReflTransGen
        (fun x y : TreeVertex d => x ∈ cone r ∧ y ∈ cone r ∧ treeAdj x y) r u := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hlen hu
      by_cases hur : u = r
      · subst u
        exact .refl
      · have hlt : r.1.length < u.1.length := by
          have hle := hu.length_le
          have hne : r.1.length ≠ u.1.length := by
            intro heq
            exact hur (Subtype.ext (hu.eq_of_length heq).symm)
          omega
        have hnil : u.1 ≠ [] := by
          intro h
          simp [h] at hlt
        have hp : parentVertex u ∈ cone r := by
          apply List.prefix_of_prefix_length_le hu (List.dropLast_prefix u.1)
          rw [List.length_dropLast]
          omega
        have hplen : (parentVertex u).1.length < n := by
          rw [parentVertex_length]
          omega
        exact (ih _ hplen _ rfl hp).tail ⟨hp, hu, treeAdj_parentVertex hnil⟩
  exact aux _ u rfl hu

theorem parent_not_mem_cone {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    parentVertex r ∉ cone r := by
  intro h
  have hlen := h.length_le
  rw [parentVertex_length] at hlen
  have hpos := List.length_pos_iff.mpr hr
  omega

theorem mem_cone_iff_reachable_avoiding_parent {d : ℕ} (r u : TreeVertex d)
    (hr : r.1 ≠ []) : u ∈ cone r ↔
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ parentVertex r ∧ y ≠ parentVertex r ∧ treeAdj x y)
      r u := by
  constructor
  · intro hu
    apply Relation.ReflTransGen.mono (fun x y hxy => ?_) r u (reachable_in_cone hu)
    exact ⟨fun h => parent_not_mem_cone r hr (h ▸ hxy.1),
      fun h => parent_not_mem_cone r hr (h ▸ hxy.2.1), hxy.2.2⟩
  · intro h
    induction h with
    | refl => exact List.prefix_refl _
    | tail h hxy ih =>
        by_contra hy
        exact hxy.2.1 (edge_leaving_cone ih hy hxy.2.2).2

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideReroot
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367.PathSideBranches

theorem map_reachable_avoiding {d : ℕ} (g : TreeAut d)
    {p a b : TreeVertex d}
    (h : Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ p ∧ y ≠ p ∧ treeAdj x y) a b) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ g.toEquiv p ∧
        y ≠ g.toEquiv p ∧ treeAdj x y) (g.toEquiv a) (g.toEquiv b) := by
  induction h with
  | refl => exact .refl
  | tail h hxy ih =>
      exact ih.tail ⟨fun he => hxy.1 (g.toEquiv.injective he),
        fun he => hxy.2.1 (g.toEquiv.injective he), (g.map_adj _ _).mpr hxy.2.2⟩

theorem map_reachable_avoiding_iff {d : ℕ} (g : TreeAut d)
    (p a b : TreeVertex d) :
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ g.toEquiv p ∧
        y ≠ g.toEquiv p ∧ treeAdj x y) (g.toEquiv a) (g.toEquiv b) ↔
    Relation.ReflTransGen
      (fun x y : TreeVertex d => x ≠ p ∧ y ≠ p ∧ treeAdj x y) a b := by
  constructor
  · intro h
    have hm := map_reachable_avoiding g.symm h
    simpa only [TreeAut.symm, Equiv.symm_apply_apply] using hm
  · exact map_reachable_avoiding g

theorem mem_cone_iff_map_mem_root_branch {d : ℕ} (g : TreeAut d)
    (r : TreeVertex d) (hr : r.1 ≠ []) (c : Fin d)
    (hp : g.toEquiv (parentVertex r) = ConnectedHull.root d)
    (hc : g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩) (u : TreeVertex d) :
    u ∈ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  let s : TreeVertex d := ⟨[c], List.IsChain.singleton c⟩
  have hs : s.1 ≠ [] := by simp [s]
  have hparent : parentVertex s = ConnectedHull.root d := by
    apply Subtype.ext
    rfl
  have hmap := map_reachable_avoiding_iff g (parentVertex r) r u
  rw [hp, hc, ← hparent] at hmap
  rw [mem_cone_iff_reachable_avoiding_parent r u hr]
  change _ ↔ g.toEquiv u ∈ cone s
  rw [mem_cone_iff_reachable_avoiding_parent s (g.toEquiv u) hs]
  exact hmap.symm

theorem exists_reroot_cone {d : ℕ} (r : TreeVertex d) (hr : r.1 ≠ []) :
    ∃ (g : TreeAut d) (c : Fin d),
      g.toEquiv (parentVertex r) = ConnectedHull.root d ∧
      g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩ ∧
      ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1 := by
  obtain ⟨g, hg⟩ := exists_treeAut_to_root (parentVertex r)
  have hadj := (g.map_adj (parentVertex r) r).mpr (treeAdj_parentVertex hr)
  rw [hg] at hadj
  obtain ⟨c, hc⟩ : ∃ c : Fin d, (g.toEquiv r).1 = [c] := by
    rcases hadj with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨c, by simpa using hc⟩
    · have hlen := congrArg List.length hc
      simp at hlen
  have hgr : g.toEquiv r = ⟨[c], List.IsChain.singleton c⟩ := Subtype.ext hc
  exact ⟨g, c, hg, hgr, mem_cone_iff_map_mem_root_branch g r hr c hg hgr⟩

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyConeSeparation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.PathSideBranches

theorem measurable_noisyRegionArray {d : ℕ} {A : Type*} [MeasurableSpace A]
    (S : Set (TreeVertex d)) : Measurable (noisyRegionArray (A := A) S) := by
  exact (S.measurable_restrict.comp measurable_fst).prodMk
    (S.measurable_restrict.comp measurable_snd)

theorem measurable_decodeCone {d : ℕ} {A : Type*} [MeasurableSpace A]
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1) :
    Measurable (decodeCone (A := A) g r c hgeo) := by
  unfold decodeCone
  fun_prop

theorem decodeCone_relabel {d : ℕ} {A : Type*}
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    decodeCone g r c hgeo (noisyBranchArray c
      (Prod.map (relabel g) (relabel g) z)) = noisyRegionArray (cone r) z := by
  apply Prod.ext <;> funext u <;>
    simp [decodeCone, noisyBranchArray, noisyRegionArray, relabel]

theorem measurable_decodeConeComplement {d : ℕ} {A : Type*} [MeasurableSpace A]
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1) :
    Measurable (decodeConeComplement (A := A) g r c hgeo) := by
  exact (Measurable.of_eval (fun vertex : {u : TreeVertex d // u ∉ cone r} =>
    (measurable_noisyRootOtherDecode c
      ⟨g.toEquiv vertex.1, fun hmem => vertex.2 ((hgeo vertex.1).mpr hmem)⟩).fst)).prodMk
    (Measurable.of_eval (fun vertex : {u : TreeVertex d // u ∉ cone r} =>
      (measurable_noisyRootOtherDecode c
        ⟨g.toEquiv vertex.1, fun hmem => vertex.2 ((hgeo vertex.1).mpr hmem)⟩).snd))

theorem decodeConeComplement_relabel {d : ℕ} {A : Type*}
    (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    decodeConeComplement g r c hgeo (noisyRootOtherArray c
      (Prod.map (relabel g) (relabel g) z)) = noisyRegionArray (cone r)ᶜ z := by
  apply Prod.ext
  · funext u
    change (noisyRootOtherDecode c _ _).1 = _
    rw [noisyRootOtherDecode_array]
    simp [Prod.map, relabel, noisyRegionArray]
  · funext u
    change (noisyRootOtherDecode c _ _).2 = _
    rw [noisyRootOtherDecode_array]
    simp [Prod.map, relabel, noisyRegionArray]

end Problem367.PathSideBranches

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.condIndepFun_noisy_cone_complement
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (r : TreeVertex d) (hr : r.1 ≠ []) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (parentVertex r)))
      ((measurable_pi_apply (parentVertex r)).comp measurable_fst).comap_le
      (noisyRegionArray (cone r)ᶜ) (noisyRegionArray (cone r))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  have hroot : g.toEquiv.symm (RootedBroadcast.root d) = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hp]
    rfl
  have h := (hμ.condIndepFun_relabel_noisy_root_others_branch h0 h1 ν g c).comp
    (measurable_decodeConeComplement g r c hgeo) (measurable_decodeCone g r c hgeo)
  classical
  simp only [hroot, Function.comp_def, decodeConeComplement_relabel,
    decodeCone_relabel] at h
  exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_PathSideLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.PathSideBranches

theorem later_forward_subset_side_complement {d : ℕ} (hd : 3 ≤ d)
    (v : TreeVertex d) {i j : Fin v.1.length} (hij : i < j) :
    cone (ConnectedHull.takeVertex v (j.1 + 1)) ⊆ (cone (sideVertex hd v i))ᶜ :=
  fun _ hu => (Set.disjoint_right.mp (sideCone_disjoint_later_forward hd v hij)) hu

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyPathLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.PathSideBranches

theorem measurable_restrictNoisyRegion {d : ℕ} {A : Type*} [MeasurableSpace A]
    {S T : Set (TreeVertex d)} (hST : S ⊆ T) :
    Measurable (restrictNoisyRegion (A := A) hST) := by
  unfold restrictNoisyRegion
  fun_prop

theorem measurable_noisyRegionArray_of_subset {d : ℕ} {A : Type*}
    [MeasurableSpace A] {S T : Set (TreeVertex d)} (hST : S ⊆ T) :
    Measurable[noisyRegionSigma (A := A) T] (noisyRegionArray (A := A) S) := by
  exact (measurable_restrictNoisyRegion hST).comp
    (comap_measurable (noisyRegionArray (A := A) T))

theorem noisyRegionSigma_mono {d : ℕ} {A : Type*} [MeasurableSpace A]
    {S T : Set (TreeVertex d)} (hST : S ⊆ T) :
    noisyRegionSigma (A := A) S ≤ noisyRegionSigma (A := A) T :=
  (measurable_noisyRegionArray_of_subset (A := A) hST).comap_le

theorem noisyRegionSigma_le {d : ℕ} {A : Type*} [MeasurableSpace A]
    (S : Set (TreeVertex d)) :
    noisyRegionSigma (A := A) S ≤
      (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A))) :=
  (measurable_noisyRegionArray S).comap_le

end Problem367.PathSideBranches

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.condIndepFun_noisy_cone_observables
    {d : ℕ} {theta : ℝ} {A B C : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    [MeasurableSpace C] [StandardBorelSpace C] [Nonempty C]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (r : TreeVertex d) (hr : r.1 ≠ [])
    (X : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → B)
    (Q : (TreeVertex d → IsingSpin) × (TreeVertex d → A) → C)
    (hX : Measurable[noisyRegionSigma (A := A) (cone r)ᶜ] X)
    (hQ : Measurable[noisyRegionSigma (A := A) (cone r)] Q) :
    CondIndepFun
      (isingSpinMeasurable.comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (parentVertex r)))
      ((measurable_pi_apply (parentVertex r)).comp measurable_fst).comap_le X Q
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  obtain ⟨F, hF, rfl⟩ := hX.exists_eq_measurable_comp
  obtain ⟨G, hG, rfl⟩ := hQ.exists_eq_measurable_comp
  exact (hμ.condIndepFun_noisy_cone_complement h0 h1 ν r hr).comp hF hG

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConeComponentAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PathSideBranches

theorem range_relabel_componentIndexVertex_eq_cone
    {d : ℕ} (g : TreeAut d) (r : TreeVertex d) (c : Fin d)
    (hgeo : ∀ u : TreeVertex d, u ∈ cone r ↔ [c] <+: (g.toEquiv u).1) :
    Set.range (fun i => g.toEquiv.symm (componentIndexVertex (c := c) i)) =
      Set.range (Subtype.val : cone r → TreeVertex d) := by
  rw [Subtype.range_coe_subtype]
  ext u
  constructor
  · rintro ⟨i, rfl⟩
    apply (hgeo _).mpr
    simp only [Equiv.apply_symm_apply]
    change [c] <+: c :: i.2.1
    simp
  · intro hu
    have hp := (hgeo u).mp hu
    have hm : g.toEquiv u ∈ Set.range (componentIndexVertex (c := c)) := by
      apply mem_range_componentIndexVertex.mpr
      obtain ⟨w, hw⟩ := hp
      exact ⟨w, by simpa using hw.symm⟩
    obtain ⟨i, hi⟩ := hm
    refine ⟨i, ?_⟩
    change g.toEquiv.symm (componentIndexVertex i) = u
    rw [hi, Equiv.symm_apply_apply]

end Problem367.PathSideBranches

namespace Problem367.ComponentSignalAttenuation

open PlantedSymmetry PathSideBranches

theorem condExp_attenuation_le_critical_cone_complement
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hcritical : ((d - 1 : ℕ) : ℝ) * theta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (r : TreeVertex d) (hr : r.1 ≠ [])
    {B : Type*} [mB : MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    (G : (({u : TreeVertex d // u ∉ cone r} → IsingSpin) ×
      ({u : TreeVertex d // u ∉ cone r} → ℝ)) → B) (hG : Measurable G)
    (shift : B → ℝ) (hs : Measurable shift) :
    let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
    let X := G ∘ noisyRegionArray (cone r)ᶜ
    let Q := selectedPosterior P (fun s z => (t : ℝ) * spinSign s + z)
      (Subtype.val : cone r → TreeVertex d) r
    ∀ᵐ w ∂P,
      (P[fun v => responseAttenuation theta
        (shift (X v) + statisticMessage theta (Q v)) ^ 2 | mB.comap X]) w ≤
        1 - lossCoefficient theta * min (Real.sqrt (t : ℝ)) 1 := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  have hroot : g.toEquiv.symm (RootedBroadcast.branchRoot c) = r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hc]
    rfl
  have hchannelField := selectedObservationField_eq_of_range_eq
    (fun s z => (t : ℝ) * spinSign s + z)
    (range_relabel_componentIndexVertex_eq_cone g r c hgeo)
  have hX : ((G ∘ decodeConeComplement (A := ℝ) g r c hgeo) ∘ noisyRootOtherArray c) ∘
      Prod.map (relabel g) (relabel g) = G ∘ noisyRegionArray (cone r)ᶜ := by
    funext z
    exact congrArg G (decodeConeComplement_relabel g r c hgeo z)
  have h := condExp_attenuation_le_critical_relabel_root_others
    hμ hθ0 hθ1 c hcritical ht g (G ∘ decodeConeComplement g r c hgeo)
    (hG.comp (measurable_decodeConeComplement g r c hgeo)) shift hs
  dsimp only at h ⊢
  simpa only [hX, hroot, selectedPosterior, hchannelField] using h

end Problem367.ComponentSignalAttenuation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ConePosteriorRegression
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.selectedPosterior_parent_cone
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (r : TreeVertex d) (hr : r.1 ≠ []) :
    let P := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    selectedPosterior P F (Subtype.val : cone r → TreeVertex d) (parentVertex r) =ᵐ[P]
      fun z => theta * selectedPosterior P F (Subtype.val : cone r → TreeVertex d) r z := by
  obtain ⟨g, c, hp, hc, hgeo⟩ := exists_reroot_cone r hr
  have hparent : g.toEquiv.symm (RootedBroadcast.root d) = parentVertex r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hp]
    rfl
  have hchild : g.toEquiv.symm (RootedBroadcast.branchRoot c) = r := by
    apply g.toEquiv.injective
    rw [Equiv.apply_symm_apply, hc]
    rfl
  have hfield := selectedObservationField_eq_of_range_eq F
    (range_relabel_componentIndexVertex_eq_cone g r c hgeo)
  have hb := hμ.selectedPosterior_root_component h0 h1 ν hF c
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hμ ν g
  have hbp := hmp.quasiMeasurePreserving.ae_eq_comp hb
  have hpull := selectedPosterior_relabel_ae hμ ν hF
    (componentIndexVertex (c := c)) (RootedBroadcast.root d) g
  have hcpull := selectedPosterior_relabel_ae hμ ν hF
    (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) g
  filter_upwards [hbp, hpull, hcpull] with z hbz hpz hcz
  have h := hpz.symm.trans (hbz.trans (congrArg (fun q : ℝ => theta * q) hcz))
  simpa only [selectedPosterior, hfield, hparent, hchild] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SelectedPathLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

open PathSideBranches

theorem selectedObservationField_region_union {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (S T : Set (TreeVertex d)) :
    selectedObservationField F (Subtype.val : (S ∪ T : Set (TreeVertex d)) → TreeVertex d) =
      selectedObservationField F (Subtype.val : S → TreeVertex d) ⊔
        selectedObservationField F (Subtype.val : T → TreeVertex d) := by
  simp only [selectedObservationField, MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro u
    rcases u.2 with hu | hu
    · exact le_sup_of_le_left (le_iSup_of_le (⟨u.1, hu⟩ : S) le_rfl)
    · exact le_sup_of_le_right (le_iSup_of_le (⟨u.1, hu⟩ : T) le_rfl)
  · apply sup_le
    · apply iSup_le
      intro u
      exact le_iSup_of_le (⟨u.1, Or.inl u.2⟩ : ↥(S ∪ T)) le_rfl
    · apply iSup_le
      intro u
      exact le_iSup_of_le (⟨u.1, Or.inr u.2⟩ : ↥(S ∪ T)) le_rfl

theorem selectedObservationField_le_noisyRegionSigma {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (S : Set (TreeVertex d)) :
    selectedObservationField F (Subtype.val : S → TreeVertex d) ≤
      noisyRegionSigma (A := A) S := by
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → A)) :=
    noisyRegionSigma (A := A) S
  have hobs : Measurable[noisyRegionSigma (A := A) S]
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun u : S => F (z.1 u.1) (z.2 u.1)) := by
    apply Measurable.of_eval
    intro u
    exact hF.comp ((((measurable_pi_apply u).comp measurable_fst).prodMk
      ((measurable_pi_apply u).comp measurable_snd)).comp
        (comap_measurable (noisyRegionArray (A := A) S)))
  exact hobs.comap_le

theorem measurable_selectedPosterior_noisyRegion {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (S : Set (TreeVertex d)) (r : TreeVertex d) :
    Measurable[noisyRegionSigma (A := A) S]
      (selectedPosterior ρ F (Subtype.val : S → TreeVertex d) r) :=
  stronglyMeasurable_condExp.measurable.mono
    (selectedObservationField_le_noisyRegionSigma hF S) le_rfl

theorem measurable_selectedField_noisyRegion {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (S : Set (TreeVertex d)) (r : TreeVertex d) :
    Measurable[noisyRegionSigma (A := A) S]
      (fun z => Real.artanh (selectedPosterior ρ F (Subtype.val : S → TreeVertex d) r z)) := by
  have hA : Measurable Real.artanh := by
    unfold Real.artanh
    fun_prop
  exact hA.comp (measurable_selectedPosterior_noisyRegion ρ hF S r)

namespace PathSideBranches

theorem target_mem_reducedForward {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : ConnectedHull.takeVertex v (i.1 + 1) ∈ reducedForward hd v i :=
  ⟨List.prefix_refl _, path_vertex_not_mem_sideCone hd v i _⟩

theorem reducedForward_subset_complement {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : reducedForward hd v i ⊆ (cone (sideVertex hd v i))ᶜ :=
  fun _ hu => hu.2

theorem forward_eq_reduced_union_side {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d)
    (i : Fin v.1.length) : cone (ConnectedHull.takeVertex v (i.1 + 1)) =
      reducedForward hd v i ∪ cone (sideVertex hd v i) := by
  ext u
  constructor
  · intro hu
    by_cases hs : u ∈ cone (sideVertex hd v i)
    · exact Or.inr hs
    · exact Or.inl ⟨hu, hs⟩
  · rintro (hu | hu)
    · exact hu.1
    · exact sideCone_subset_forward hd v i hu

theorem forwardObservationField_eq_reduced_sup_side {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (hd : 3 ≤ d) (v : TreeVertex d) (i : Fin v.1.length) :
    selectedObservationField F
      (Subtype.val : cone (ConnectedHull.takeVertex v (i.1 + 1)) → TreeVertex d) =
      selectedObservationField F (Subtype.val : reducedForward hd v i → TreeVertex d) ⊔
        selectedObservationField F (Subtype.val : cone (sideVertex hd v i) → TreeVertex d) := by
  rw [forward_eq_reduced_union_side hd v i]
  exact selectedObservationField_region_union F _ _

theorem measurable_later_selectedPosterior {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hd : 3 ≤ d) (v : TreeVertex d) {i j : Fin v.1.length} (hij : i < j)
    (r : TreeVertex d) :
    Measurable[noisyRegionSigma (A := A) (cone (sideVertex hd v i))ᶜ]
      (selectedPosterior ρ F
        (Subtype.val : cone (ConnectedHull.takeVertex v (j.1 + 1)) → TreeVertex d) r) :=
  (measurable_selectedPosterior_noisyRegion ρ hF _ r).mono
    (noisyRegionSigma_mono (later_forward_subset_side_complement hd v hij)) le_rfl

end PathSideBranches

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConeSelectedFusion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PathSideBranches

theorem HasFreeIsingLaw.selected_gaussian_outside_cone_fusion
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hp : parentVertex r ∈ S) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    selectedPosterior P F (Subtype.val : (S ∪ cone r : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) =ᵐ[P]
      fun z => binaryFusion
        (selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z)
        (Real.tanh beta * selectedPosterior P F
          (Subtype.val : cone r → TreeVertex d) r z) := by
  let := hμ.isProbabilityMeasure
  let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let X := fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i : S => F (z.1 i.1) (z.2 i.1)
  let Y := fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
    fun i : cone r => F (z.1 i.1) (z.2 i.1)
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hX : Measurable X := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (z.1 i.1, z.2 i.1)) from by fun_prop)
  have hY : Measurable Y := by
    apply Measurable.of_eval
    intro i
    exact hF.comp (show Measurable (fun z :
      (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        (z.1 i.1, z.2 i.1)) from by fun_prop)
  have hXout : Measurable[noisyRegionSigma (A := ℝ) (cone r)ᶜ] X :=
    (comap_measurable X).mono
      ((selectedObservationField_le_noisyRegionSigma hF S).trans
        (noisyRegionSigma_mono hS)) le_rfl
  have hYin : Measurable[noisyRegionSigma (A := ℝ) (cone r)] Y :=
    (comap_measurable Y).mono
      (selectedObservationField_le_noisyRegionSigma hF (cone r)) le_rfl
  have hInd := hμ.condIndepFun_noisy_cone_observables
    (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le
    (gaussianReal 0 t) r hr X Y hXout hYin
  have hreg : selectedPosterior P F (Subtype.val : cone r → TreeVertex d)
      (parentVertex r) =ᵐ[P] fun z => Real.tanh beta *
        selectedPosterior P F (Subtype.val : cone r → TreeVertex d) r z :=
    hμ.selectedPosterior_parent_cone
    (Real.neg_one_lt_tanh beta).le (Real.tanh_lt_one beta).le
    (gaussianReal 0 t) hF r hr
  have hL : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z| < 1 := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : S → TreeVertex d) (parentVertex r) ⟨⟨_, hp⟩, rfl⟩] with z hz
    exact abs_lt.mpr hz.1
  have hQ : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : cone r → TreeVertex d) r z| < 1 := by
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hbeta t
      (Subtype.val : cone r → TreeVertex d) r ⟨⟨r, List.prefix_refl _⟩, rfl⟩] with z hz
    exact abs_lt.mpr hz.1
  have hR : ∀ᵐ z ∂P,
      |selectedPosterior P F (Subtype.val : cone r → TreeVertex d) (parentVertex r) z| < 1 := by
    filter_upwards [hreg, hQ] with z hz hq
    rw [hz, abs_mul]
    exact (mul_le_mul_of_nonneg_left hq.le (abs_nonneg (Real.tanh beta))).trans_lt
      (by simpa using Real.abs_tanh_lt_one beta)
  have h := condExp_spin_comap_sup_eq_binaryFusion
    ((measurable_pi_apply (parentVertex r)).comp measurable_fst) hX hY
    (hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) _) hInd hL hR
  dsimp only
  unfold selectedPosterior
  rw [selectedObservationField_region_union]
  filter_upwards [h, hreg] with z hz hregz
  exact hz.trans (congrArg (binaryFusion
    (selectedPosterior P F (Subtype.val : S → TreeVertex d) (parentVertex r) z)) hregz)

theorem HasFreeIsingLaw.selected_gaussian_outside_cone_field
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (t : ℝ≥0) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hp : parentVertex r ∈ S) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    (fun z => Real.artanh (selectedPosterior P F
      (Subtype.val : (S ∪ cone r : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) z)) =ᵐ[P]
      fun z => Real.artanh (selectedPosterior P F
        (Subtype.val : S → TreeVertex d) (parentVertex r) z) +
        statisticMessage (Real.tanh beta) (selectedPosterior P F
          (Subtype.val : cone r → TreeVertex d) r z) := by
  have h := hμ.selected_gaussian_outside_cone_fusion hbeta t r hr S hS hp
  have hL := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : S → TreeVertex d) (parentVertex r) ⟨⟨_, hp⟩, rfl⟩
  have hQ := hμ.selected_gaussian_posterior_field_bound hbeta t
    (Subtype.val : cone r → TreeVertex d) r ⟨⟨r, List.prefix_refl _⟩, rfl⟩
  filter_upwards [h, hL, hQ] with z hz hl hq
  rw [hz]
  exact artanh_binaryFusion (abs_lt.mpr hl.1)
    (binaryFusion_abs_mul_lt_one (Real.abs_tanh_lt_one beta) (abs_lt.mpr hq.1))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_ConeSelectedFieldAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PathSideBranches

local instance localInst_rff45b3_3 : Nonempty IsingSpin := ⟨.neg⟩
theorem HasFreeIsingLaw.condExp_selected_cone_field_attenuation_le_critical
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta)
    (hθ0 : 0 < Real.tanh beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (r : TreeVertex d) (hr : r.1 ≠ [])
    (S : Set (TreeVertex d)) (hS : S ⊆ (cone r)ᶜ) (hp : parentVertex r ∈ S) :
    let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
    let field := fun z => Real.artanh (selectedPosterior P F
      (Subtype.val : (S ∪ cone r : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) z)
    ∀ᵐ z ∂P,
      (P[fun z => responseAttenuation (Real.tanh beta) (field z) ^ 2 |
        noisyRegionSigma (A := ℝ) (cone r)ᶜ]) z ≤
        1 - ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
          min (Real.sqrt (t : ℝ)) 1 := by
  let := hμ.isProbabilityMeasure
  let P := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd
  have hout : Measurable[noisyRegionSigma (A := ℝ) (cone r)ᶜ]
      (fun z => Real.artanh (selectedPosterior P F
        (Subtype.val : S → TreeVertex d) (parentVertex r) z)) :=
    (measurable_selectedField_noisyRegion P hF S (parentVertex r)).mono
      (noisyRegionSigma_mono hS) le_rfl
  obtain ⟨shift, hs, hshift⟩ := hout.exists_eq_measurable_comp
  have hbase := ComponentSignalAttenuation.condExp_attenuation_le_critical_cone_complement
    hμ hθ0 (Real.tanh_lt_one beta) hcritical ht r hr
    (id : (({u : TreeVertex d // u ∉ cone r} → IsingSpin) ×
      ({u : TreeVertex d // u ∉ cone r} → ℝ)) → _) measurable_id shift hs
  have hfield := hμ.selected_gaussian_outside_cone_field hbeta t r hr S hS hp
  have hfactor : (fun z => responseAttenuation (Real.tanh beta)
      (Real.artanh (selectedPosterior P F
        (Subtype.val : (S ∪ cone r : Set (TreeVertex d)) → TreeVertex d) (parentVertex r) z)) ^ 2) =ᵐ[P]
      fun z => responseAttenuation (Real.tanh beta)
        (shift (noisyRegionArray (cone r)ᶜ z) + statisticMessage (Real.tanh beta)
          (selectedPosterior P F (Subtype.val : cone r → TreeVertex d) r z)) ^ 2 := by
    filter_upwards [hfield] with z hz
    have hs' := congrFun hshift z
    dsimp only [Function.comp_apply] at hs'
    rw [hz, hs']
  have hCE := condExp_congr_ae
    (m := noisyRegionSigma (A := ℝ) (cone r)ᶜ) hfactor
  filter_upwards [hbase, hCE] with z hz heq
  exact heq.trans_le hz

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SelectedPathAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.PathSideBranches

theorem measurable_forwardGaussianField {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (v : TreeVertex d) (k : ℕ) :
    Measurable (forwardGaussianField μ t v k) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  exact ha.comp (measurable_selectedPosterior _
    (((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd) _ _)

theorem measurable_later_forwardGaussianField {d : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (hd : 3 ≤ d) (v : TreeVertex d) {i j : Fin v.1.length} (hij : i < j) :
    Measurable[noisyRegionSigma (A := ℝ) (cone (sideVertex hd v i))ᶜ]
      (forwardGaussianField μ t v j) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  apply ha.comp
  exact measurable_later_selectedPosterior _
    (((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul
      (t : ℝ)).add measurable_snd) hd v hij _

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SelectedPathSegmentAttenuation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.PathSideBranches

theorem integral_forwardGaussianField_subset_attenuation_le_exp_of_condExp
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    [IsProbabilityMeasure μ] (hθ : theta ^ 2 ≤ 1)
    (hd : 3 ≤ d) (t : ℝ≥0) (v : TreeVertex d)
    (s : Finset ℕ) (hs : ∀ i ∈ s, i < v.1.length) {delta : ℝ} (hδ : delta ≤ 1)
    (hCE : ∀ i : Fin v.1.length,
      ∀ᵐ p ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
        ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[
          fun p => responseAttenuation theta (forwardGaussianField μ t v i p) ^ 2 |
          noisyRegionSigma (A := ℝ) (cone (sideVertex hd v i))ᶜ]) p ≤ 1 - delta) :
    (∫ p, ∏ k ∈ s,
      responseAttenuation theta (forwardGaussianField μ t v k p) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
        Real.exp (-delta * (s.card : ℝ)) := by
  classical
  let A : ℕ → ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) → ℝ :=
    fun k p => responseAttenuation theta (forwardGaussianField μ t v k p) ^ 2
  let m : ℕ → MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) :=
    fun k => if hk : k < v.1.length then
      noisyRegionSigma (A := ℝ) (cone (sideVertex hd v ⟨k, hk⟩))ᶜ else ⊥
  have hresp : Measurable (fun z : ℝ => responseAttenuation theta z ^ 2) :=
    (continuous_responseAttenuation hθ).measurable.pow_const 2
  have hMeas (k : ℕ) : Measurable (A k) :=
    hresp.comp (measurable_forwardGaussianField μ t v k)
  have hBound (k : ℕ) (p) : 0 ≤ A k p ∧ A k p ≤ 1 := by
    have hp := responseAttenuation_pos hθ (forwardGaussianField μ t v k p)
    have hl := responseAttenuation_le_one hθ (forwardGaussianField μ t v k p)
    exact ⟨sq_nonneg _, by dsimp [A] <;> nlinarith⟩
  have hm (k : ℕ) (hk : k ∈ s) : m k ≤
      (inferInstance : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))) := by
    have hk := hs k hk
    simpa only [m, dite_eq_left hk] using
      noisyRegionSigma_le (A := ℝ) (cone (sideVertex hd v ⟨k, hk⟩))ᶜ
  have hcond (k : ℕ) (hk : k ∈ s) :
      ∀ᵐ p ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
        ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[A k | m k]) p ≤
          1 - delta := by
    have hk := hs k hk
    simpa only [m, dite_eq_left hk, A] using hCE ⟨k, hk⟩
  have hLater (i : ℕ) (hi : i ∈ s)
      (j : ℕ) (hj : j ∈ s) (hij : i < j) :
      Measurable[m i] (A j) := by
    have hi := hs i hi
    have hj := hs j hj
    have hmi : m i = noisyRegionSigma (A := ℝ)
        (cone (sideVertex hd v ⟨i, hi⟩))ᶜ := by simp only [m, dite_eq_left hi]
    have ht : Measurable[noisyRegionSigma (A := ℝ)
        (cone (sideVertex hd v ⟨i, hi⟩))ᶜ] (A j) := by
      exact hresp.comp (measurable_later_forwardGaussianField μ t hd v
        (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) hij)
    exact hmi.symm ▸ ht
  simpa only [A] using
    integral_prod_le_exp_of_condExp_le hδ A m s
      (fun k _ => hMeas k) (fun k _ => hBound k) hm hcond hLater

theorem integral_forwardGaussianField_subset_attenuation_le_exp_critical
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t) (v : TreeVertex d)
    (s : Finset ℕ) (hs : ∀ i ∈ s, i < v.1.length) :
    (∫ p, ∏ k ∈ s,
      responseAttenuation (Real.tanh beta) (forwardGaussianField μ t v k p) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
        Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
          min (Real.sqrt (t : ℝ)) 1) * (s.card : ℝ)) := by
  let := hμ.isProbabilityMeasure
  have hθ0 : 0 < Real.tanh beta := by
    have hn := tanh_nonneg_of_beta_nonneg hbeta
    by_contra h
    have hz : Real.tanh beta = 0 := le_antisymm (not_lt.mp h) hn
    simp [hz] at hcritical
  have hθ1 := Real.tanh_lt_one beta
  have hc := ComponentSignalAttenuation.lossCoefficient_pos hθ0 hθ1
  have hc1 := ComponentSignalAttenuation.lossCoefficient_le_half (Real.tanh beta)
  have hδ : ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
      min (Real.sqrt (t : ℝ)) 1 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left
      (min_le_right (Real.sqrt (t : ℝ)) (1 : ℝ)) hc.le
    nlinarith
  apply integral_forwardGaussianField_subset_attenuation_le_exp_of_condExp
    (by nlinarith : Real.tanh beta ^ 2 ≤ 1) hd t v s hs hδ
  intro i
  have hr : (sideVertex hd v i).1 ≠ [] := by
    intro he
    have hl := sideVertex_length hd v i
    rw [he] at hl
    simp at hl
  have hp : parentVertex (sideVertex hd v i) ∈ reducedForward hd v i := by
    rw [parent_sideVertex]
    exact target_mem_reducedForward hd v i
  have h := hμ.condExp_selected_cone_field_attenuation_le_critical
    hbeta hθ0 hcritical ht (sideVertex hd v i) hr (reducedForward hd v i)
    (reducedForward_subset_complement hd v i) hp
  have hfield := forwardObservationField_eq_reduced_sup_side
    (fun s z => (t : ℝ) * spinSign s + z) hd v i
  rw [← selectedObservationField_region_union] at hfield
  simpa only [parent_sideVertex, selectedPosterior, ← hfield,
    forwardGaussianField] using h

end Problem367.PathSideBranches

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_CutChannels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367
open PathSideBranches CutContinuationChannels

theorem cutContinuationProduct_gaussianConeFactor {d k L : ℕ}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0) (theta : ℝ)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) (z) :
    cutContinuationProduct (gaussianConeFactor μ t theta z) p w =
      ∏ i ∈ Finset.Ico (k + 1) (k + 1 + L),
        responseAttenuation theta
          (forwardGaussianField μ t (appendCutContinuation p w).1 i z) ^ 2 := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel_left]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [gaussianConeFactor, forwardGaussianField, rootPathVertex,
    ConnectedHull.takeVertex, Nat.add_assoc]
  rfl

theorem integral_cutContinuationProduct_gaussianConeFactor_le_oai {d k L : ℕ}
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hbeta : 0 ≤ beta) (hd : 3 ≤ d)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1)
    {t : ℝ≥0} (ht : 0 < t)
    (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    (∫ z, cutContinuationProduct (gaussianConeFactor μ t (Real.tanh beta) z) p w
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
        Real.exp (-(ComponentSignalAttenuation.lossCoefficient (Real.tanh beta) *
          min (Real.sqrt (t : ℝ)) 1) * (L : ℝ)) := by
  have h := integral_forwardGaussianField_subset_attenuation_le_exp_critical
    hμ hbeta hd hcritical ht (appendCutContinuation p w).1
      (Finset.Ico (k + 1) (k + 1 + L)) (by
        intro i hi
        rw [(appendCutContinuation p w).2]
        exact (Finset.mem_Ico.mp hi).2)
  simpa only [cutContinuationProduct_gaussianConeFactor, Nat.card_Ico,
    Nat.add_sub_cancel_left] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteIsingGaussianTesting
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Problem367

local instance instNonemptyIsingSpin : Nonempty IsingSpin := ⟨.neg⟩

end Problem367

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le_oai := @OAI.Problem367.integral_cutContinuationProduct_gaussianConeFactor_le_oai
