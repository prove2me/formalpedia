-- Prove2me | solution 1 for OAI.Problem367.HasFreeIsingLaw.gaussian_root_information_le_component
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:56.336076+00:00
-- url     : https://prove2.me/submissions/aa0ca63b-2346-4f9c-9ec7-b4c9b3ee85ba

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_selectedPosterior_root_component

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

local instance localInst_r0e31cd_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
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

local instance instMeasurableSingletonClassIsingSpin_2_r0e31cd_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
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

local instance instMeasurableSingletonClassIsingSpin_1_r0e31cd_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
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

local instance noisyBranchConditionalLawMeasurableSingletonIsingSpin_r0e31cd_1 :
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

theorem map_linearSignalTilt {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} {q : Ω → ℝ} (hq : Measurable q) (a : ℝ) :
    Measure.map q (linearSignalTilt mu q a) = linearSignalTilt (Measure.map q mu) id a := by
  unfold linearSignalTilt
  simpa only [Function.comp_def, id_eq] using
    (map_withDensity_comp (mu := mu) (f := q)
      (w := fun y : ℝ => ENNReal.ofReal (1 + a * y)) hq (by fun_prop))

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

theorem integral_cond_spin_posterior_function
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    (g : ℝ → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun x => g (mu[fun y => spinSign (S y) | mSmall] x)) mu)
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    ∫ x, g (mu[fun y => spinSign (S y) | mSmall] x)
        ∂ProbabilityTheory.cond mu {x | S x = a} =
      ∫ x, g (mu[fun y => spinSign (S y) | mSmall] x) *
        (1 + spinSign a * mu[fun y => spinSign (S y) | mSmall] x) ∂mu := by
  exact integral_cond_spin_posterior_tilt hm hS
    (hg.comp stronglyMeasurable_condExp.measurable).stronglyMeasurable hgi a hfair

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

theorem binaryFusionLoss_denominator_pos {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 < 1 - u ^ 2 * v ^ 2 := by
  have h := (sq_lt_one_iff_abs_lt_one (u * v)).mpr
    (binaryFusion_abs_mul_lt_one hu hv)
  nlinarith

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

theorem binaryFusionLoss_nonneg {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : 0 ≤ binaryFusionLoss u v := by
  have hu' := (sq_lt_one_iff_abs_lt_one u).mpr hu
  have hv' := (sq_lt_one_iff_abs_lt_one v).mpr hv
  have hf : 0 ≤ 2 - u ^ 2 - v ^ 2 := by linarith
  have hd := binaryFusionLoss_denominator_pos hu hv
  unfold binaryFusionLoss
  positivity

theorem binaryFusion_symmetric_square {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) :
    ((u + v) ^ 2 / (1 + u * v) + (u - v) ^ 2 / (1 - u * v)) / 2 =
      u ^ 2 + v ^ 2 - binaryFusionLoss u v := by
  have hp := ne_of_gt (binaryFusion_denominator_pos hu hv)
  have hm : 1 - u * v ≠ 0 := by
    have := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).2
    linarith
  have hq := ne_of_gt (binaryFusionLoss_denominator_pos hu hv)
  unfold binaryFusionLoss
  field_simp
  ring

theorem binaryFusion_integrand_le_two {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : (u + v) ^ 2 / (1 + u * v) ≤ 2 := by
  apply (div_le_iff₀ (binaryFusion_denominator_pos hu hv)).mpr
  have hu' := (sq_lt_one_iff_abs_lt_one u).mpr hu
  have hv' := (sq_lt_one_iff_abs_lt_one v).mpr hv
  nlinarith

theorem binaryFusionLoss_le_sum_sq {u v : ℝ}
    (hu : |u| < 1) (hv : |v| < 1) : binaryFusionLoss u v ≤ u ^ 2 + v ^ 2 := by
  have hp : 0 ≤ (u + v) ^ 2 / (1 + u * v) :=
    div_nonneg (sq_nonneg _) (binaryFusion_denominator_pos hu hv).le
  have hmden : 0 < 1 - u * v := by
    have := (abs_lt.mp (binaryFusion_abs_mul_lt_one hu hv)).2
    linarith
  have hm : 0 ≤ (u - v) ^ 2 / (1 - u * v) :=
    div_nonneg (sq_nonneg _) hmden.le
  have hid := binaryFusion_symmetric_square hu hv
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Stochastic_BinaryFusionIntegral
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem ae_binaryFusion_bounds {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    ∀ᵐ p ∂mu.prod nu, |p.1| < 1 ∧ |p.2| < 1 := by
  have hu' : ∀ᵐ p ∂mu.prod nu, |p.1| < 1 :=
    measurePreserving_fst.quasiMeasurePreserving.tendsto_ae hu
  have hv' : ∀ᵐ p ∂mu.prod nu, |p.2| < 1 :=
    measurePreserving_snd.quasiMeasurePreserving.tendsto_ae hv
  exact hu'.and hv'

theorem integrable_binaryFusion_integrand {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    Integrable (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 / (1 + p.1 * p.2))
      (mu.prod nu) := by
  refine (integrable_const (2 : ℝ)).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (sq_nonneg _) (binaryFusion_denominator_pos hp.1 hp.2).le)]
  exact binaryFusion_integrand_le_two hp.1 hp.2

theorem integrable_binaryFusionLoss {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    Integrable (fun p : ℝ × ℝ => binaryFusionLoss p.1 p.2) (mu.prod nu) := by
  refine (integrable_const (2 : ℝ)).mono' ?_ ?_
  · unfold binaryFusionLoss
    apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (binaryFusionLoss_nonneg hp.1 hp.2)]
    have h := binaryFusionLoss_le_sum_sq hp.1 hp.2
    have hu' := (sq_lt_one_iff_abs_lt_one p.1).mpr hp.1
    have hv' := (sq_lt_one_iff_abs_lt_one p.2).mpr hp.2
    linarith

theorem integral_binaryFusion_symmetric_square {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1)
    (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    (∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu) =
      (∫ u : ℝ, u ^ 2 ∂mu) + (∫ v : ℝ, v ^ 2 ∂nu) -
        ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  let R : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
  have hR : MeasurePreserving R (mu.prod nu) (mu.prod nu) :=
    (MeasurePreserving.id mu).prod ⟨measurable_neg, hsym⟩
  have hi := integrable_binaryFusion_integrand hu hv
  have hin : Integrable (fun p : ℝ × ℝ =>
      (p.1 - p.2) ^ 2 / (1 - p.1 * p.2)) (mu.prod nu) := by
    have h := (hR.integrable_comp hi.aestronglyMeasurable).mpr hi
    change Integrable (fun p : ℝ × ℝ =>
      (p.1 + -p.2) ^ 2 / (1 + p.1 * -p.2)) (mu.prod nu) at h
    simpa [sub_eq_add_neg] using h
  have heq : (∫ p : ℝ × ℝ, (p.1 - p.2) ^ 2 / (1 - p.1 * p.2) ∂mu.prod nu) =
      ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu := by
    have h := hR.integral_comp'
      (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 / (1 + p.1 * p.2))
    change (∫ p : ℝ × ℝ, (p.1 + -p.2) ^ 2 / (1 + p.1 * -p.2) ∂mu.prod nu) = _ at h
    simpa [sub_eq_add_neg] using h
  have hiu : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) (mu.prod nu) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg p.1)] using
      ((sq_lt_one_iff_abs_lt_one p.1).mpr hp.1).le
  have hiv : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) (mu.prod nu) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg p.2)] using
      ((sq_lt_one_iff_abs_lt_one p.2).mpr hp.2).le
  have hl := integrable_binaryFusionLoss hu hv
  have hiuv : Integrable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) (mu.prod nu) := hiu.add hiv
  have hsum : (∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 ∂mu.prod nu) =
      (∫ p : ℝ × ℝ, p.1 ^ 2 ∂mu.prod nu) +
        ∫ p : ℝ × ℝ, p.2 ^ 2 ∂mu.prod nu := integral_add hiu hiv
  have hscalar :
      (∫ p : ℝ × ℝ,
        ((p.1 + p.2) ^ 2 / (1 + p.1 * p.2) +
          (p.1 - p.2) ^ 2 / (1 - p.1 * p.2)) / 2 ∂mu.prod nu) =
      ∫ p : ℝ × ℝ, p.1 ^ 2 + p.2 ^ 2 - binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
    apply integral_congr_ae
    filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
    exact binaryFusion_symmetric_square hp.1 hp.2
  rw [integral_div, integral_add hi hin, heq,
    integral_sub hiuv hl, hsum,
    integral_fun_fst (μ := mu) (ν := nu) (fun u : ℝ => u ^ 2),
    integral_fun_snd (μ := mu) (ν := nu) (fun v : ℝ => v ^ 2)] at hscalar
  simp only [probReal_univ, one_smul] at hscalar
  linarith

theorem integral_binaryFusionLoss_nonneg {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    0 ≤ ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  exact binaryFusionLoss_nonneg hp.1 hp.2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusionJointLaw
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem integral_binaryFusion_sq_jointLaw {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    (∫ p : ℝ × ℝ, binaryFusion p.1 p.2 ^ 2 ∂binaryFusionJointLaw mu nu) =
      ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 / (1 + p.1 * p.2) ∂mu.prod nu := by
  rw [binaryFusionJointLaw, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  have hd := binaryFusion_denominator_pos hp.1 hp.2
  rw [ENNReal.toReal_ofReal hd.le, smul_eq_mul, binaryFusion]
  field_simp

theorem binaryFusionJointLaw_secondMoment {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1)
    (hsym : Measure.map (fun v : ℝ => -v) nu = nu) :
    (∫ p : ℝ × ℝ, binaryFusion p.1 p.2 ^ 2 ∂binaryFusionJointLaw mu nu) =
      (∫ u : ℝ, u ^ 2 ∂mu) + (∫ v : ℝ, v ^ 2 ∂nu) -
        ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂mu.prod nu := by
  rw [integral_binaryFusion_sq_jointLaw hu hv]
  exact integral_binaryFusion_symmetric_square hu hv hsym

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_BinaryFusionMixture
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
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

theorem binaryFusionJointLaw_eq_conditional_mixture {mu nu : Measure ℝ}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (hu : ∀ᵐ u ∂mu, |u| < 1) (hv : ∀ᵐ v ∂nu, |v| < 1) :
    (1 / 2 : ENNReal) •
        ((linearSignalTilt mu id 1).prod (linearSignalTilt nu id 1)) +
      (1 / 2 : ENNReal) •
        ((linearSignalTilt mu id (-1)).prod (linearSignalTilt nu id (-1))) =
      binaryFusionJointLaw mu nu := by
  unfold linearSignalTilt binaryFusionJointLaw
  simp only [id_eq, one_mul, neg_one_mul, ← sub_eq_add_neg]
  rw [prod_withDensity (by fun_prop) (by fun_prop),
    prod_withDensity (by fun_prop) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_smul (1 / 2) (by fun_prop),
    ← withDensity_add_left (by fun_prop)]
  apply withDensity_congr_ae
  filter_upwards [ae_binaryFusion_bounds hu hv] with p hp
  exact binaryFusion_density_eq_mixture hp.1 hp.2

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorLaw
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

theorem map_cond_spin_posterior_eq_linearSignalTilt
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    Measure.map (mu[fun y => spinSign (S y) | mSmall])
        (ProbabilityTheory.cond mu {x | S x = a}) =
      linearSignalTilt (Measure.map (mu[fun y => spinSign (S y) | mSmall]) mu)
        id (spinSign a) := by
  let M : Ω → ℝ := mu[fun y => spinSign (S y) | mSmall]
  have hM : Measurable M := stronglyMeasurable_condExp.measurable.mono hm le_rfl
  have hSb : ∀ᵐ x ∂mu, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    cases hs : S x <;> norm_num [spinSign, hs]
  have hMb : ∀ᵐ x ∂mu, |M x| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using
      (ae_bdd_norm_condExp_of_ae_bdd_norm (m := mSmall) hSb)
  have ha : |spinSign a| ≤ 1 := by cases a <;> norm_num [spinSign]
  have hMi : Integrable M mu := integrable_condExp
  let : IsProbabilityMeasure (ProbabilityTheory.cond mu {x | S x = a}) :=
    ProbabilityTheory.cond_isProbabilityMeasure (by rw [hfair]; norm_num)
  have hdi : Integrable (fun x => 1 + spinSign a * M x) mu :=
    (integrable_const 1).add (hMi.const_mul (spinSign a))
  let : IsFiniteMeasure (linearSignalTilt mu M (spinSign a)) :=
    isFiniteMeasure_withDensity_ofReal hdi.hasFiniteIntegral
  change Measure.map M (ProbabilityTheory.cond mu {x | S x = a}) =
    linearSignalTilt (Measure.map M mu) id (spinSign a)
  rw [← map_linearSignalTilt hM]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hM.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    integral_map hM.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  have hfi : Integrable (fun x => f (M x)) mu :=
    Integrable.of_bound (f.continuous.measurable.comp hM).aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm (M x)))
  rw [integral_cond_spin_posterior_function hm hS f f.continuous.measurable hfi a hfair,
    integral_linearSignalTilt hM hMb ha hfi]
  rw [← integral_const_mul,
    ← integral_add hfi ((integrable_boundedSignal_mul hM hMb hfi).const_mul (spinSign a))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by dsimp [M] <;> ring)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorFusion
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
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

theorem map_posterior_pair_eq_binaryFusionJointLaw
    {Ω : Type*} {mLeft mRight m : MeasurableSpace Ω}
    {mu : Measure Ω} [IsProbabilityMeasure mu]
    (hLeft : mLeft ≤ m) (hRight : mRight ≤ m)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hfair : ∀ a : IsingSpin, mu {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin,
      IndepFun (mu[fun x => spinSign (S x) | mLeft])
        (mu[fun x => spinSign (S x) | mRight]) (cond mu {x | S x = a}))
    (hL : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mLeft] x| < 1)
    (hR : ∀ᵐ x ∂mu, |mu[fun y => spinSign (S y) | mRight] x| < 1) :
    Measure.map (fun x =>
        (mu[fun y => spinSign (S y) | mLeft] x,
         mu[fun y => spinSign (S y) | mRight] x)) mu =
      binaryFusionJointLaw
        (Measure.map (mu[fun y => spinSign (S y) | mLeft]) mu)
        (Measure.map (mu[fun y => spinSign (S y) | mRight]) mu) := by
  let L : Ω → ℝ := mu[fun y => spinSign (S y) | mLeft]
  let R : Ω → ℝ := mu[fun y => spinSign (S y) | mRight]
  have hLm : Measurable L := stronglyMeasurable_condExp.measurable.mono hLeft le_rfl
  have hRm : Measurable R := stronglyMeasurable_condExp.measurable.mono hRight le_rfl
  haveI : IsProbabilityMeasure (Measure.map L mu) := Measure.isProbabilityMeasure_map hLm.aemeasurable
  haveI : IsProbabilityMeasure (Measure.map R mu) := Measure.isProbabilityMeasure_map hRm.aemeasurable
  have hpair (a : IsingSpin) :
      Measure.map (fun x => (L x, R x)) (cond mu {x | S x = a}) =
        (linearSignalTilt (Measure.map L mu) id (spinSign a)).prod
          (linearSignalTilt (Measure.map R mu) id (spinSign a)) := by
    let : IsProbabilityMeasure (cond mu {x | S x = a}) :=
      cond_isProbabilityMeasure (by rw [hfair]; norm_num)
    rw [(hInd a).map_prod_eq_prod_map_map hLm.aemeasurable hRm.aemeasurable,
      map_cond_spin_posterior_eq_linearSignalTilt hLeft hS a (hfair a),
      map_cond_spin_posterior_eq_linearSignalTilt hRight hS a (hfair a)]
  have hLmap : ∀ᵐ u ∂Measure.map L mu, |u| < 1 :=
    (ae_map_iff hLm.aemeasurable (measurableSet_lt measurable_abs measurable_const)).2 hL
  have hRmap : ∀ᵐ v ∂Measure.map R mu, |v| < 1 :=
    (ae_map_iff hRm.aemeasurable (measurableSet_lt measurable_abs measurable_const)).2 hR
  change Measure.map (fun x => (L x, R x)) mu =
    binaryFusionJointLaw (Measure.map L mu) (Measure.map R mu)
  calc
    _ = Measure.map (fun x => (L x, R x))
        ((1 / 2 : ENNReal) • cond mu {x | S x = .pos} +
          (1 / 2 : ENNReal) • cond mu {x | S x = .neg}) := by
      rw [← measure_eq_fair_spin_mixture hS hfair]
    _ = _ := by
      rw [Measure.map_add _ _ (hLm.prodMk hRm),
        Measure.map_smul,
        Measure.map_smul,
        hpair .pos, hpair .neg]
      exact binaryFusionJointLaw_eq_conditional_mixture hLmap hRmap

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ObservationInformation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

section Observations

variable {Ω A B : Type*} {mΩ : MeasurableSpace Ω} {mA : MeasurableSpace A}
  {mB : MeasurableSpace B} {rho : Measure Ω} [IsProbabilityMeasure rho]
  {S : Ω → IsingSpin} (hS : Measurable S)
  {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
  {q : A → ℝ} {r : B → ℝ} (hq : Measurable q) (hr : Measurable r)
  (hpostX : rho[fun x => spinSign (S x) | mA.comap X] =ᵐ[rho] fun x => q (X x))
  (hpostY : rho[fun x => spinSign (S x) | mB.comap Y] =ᵐ[rho] fun x => r (Y x))
  (hqb : ∀ᵐ x ∂rho, |q (X x)| < 1) (hrb : ∀ᵐ x ∂rho, |r (Y x)| < 1)
  (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
  (hInd : ∀ a : IsingSpin, IndepFun X Y (cond rho {x | S x = a}))

include hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd

theorem map_observation_posterior_pair_eq_binaryFusionJointLaw :
    Measure.map (fun x => (q (X x), r (Y x))) rho =
      binaryFusionJointLaw (Measure.map (fun x => q (X x)) rho)
        (Measure.map (fun x => r (Y x)) rho) := by
  have hL : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mA.comap X] x| < 1 := by
    filter_upwards [hpostX, hqb] with x hx hb
    simpa only [hx] using hb
  have hR : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mB.comap Y] x| < 1 := by
    filter_upwards [hpostY, hrb] with x hx hb
    simpa only [hx] using hb
  have hInd' (a : IsingSpin) :
      IndepFun (rho[fun y => spinSign (S y) | mA.comap X])
        (rho[fun y => spinSign (S y) | mB.comap Y]) (cond rho {x | S x = a}) :=
    ((hInd a).comp hq hr).congr
      (cond_absolutelyContinuous.ae_le hpostX.symm)
      (cond_absolutelyContinuous.ae_le hpostY.symm)
  have hjoint := map_posterior_pair_eq_binaryFusionJointLaw
    hX.comap_le hY.comap_le hS hfair hInd' hL hR
  have hp : (fun x => (rho[fun y => spinSign (S y) | mA.comap X] x,
      rho[fun y => spinSign (S y) | mB.comap Y] x)) =ᵐ[rho]
        (fun x => (q (X x), r (Y x))) := by
    filter_upwards [hpostX, hpostY] with x hx hy
    rw [hx, hy]
  rw [Measure.map_congr hp, Measure.map_congr hpostX, Measure.map_congr hpostY] at hjoint
  exact hjoint

theorem condExp_observation_pair_secondMoment
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => r (Y x)) rho) = Measure.map (fun x => r (Y x)) rho) :
    (∫ x, (rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] x) ^ 2 ∂rho) =
      (∫ x, q (X x) ^ 2 ∂rho) + (∫ x, r (Y x) ^ 2 ∂rho) -
        ∫ p : ℝ × ℝ, binaryFusionLoss p.1 p.2 ∂
          (Measure.map (fun x => q (X x)) rho).prod (Measure.map (fun x => r (Y x)) rho) := by
  haveI : IsProbabilityMeasure (Measure.map (fun x => q (X x)) rho) := Measure.isProbabilityMeasure_map (hq.comp hX).aemeasurable
  haveI : IsProbabilityMeasure (Measure.map (fun x => r (Y x)) rho) := Measure.isProbabilityMeasure_map (hr.comp hY).aemeasurable
  have hCE := condExp_spin_given_observation_pair_eq_binaryFusion
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd
  have hiCE := integral_congr_ae (hCE.fun_comp (fun x : ℝ => x ^ 2))
  simp only [Function.comp_apply] at hiCE
  rw [hiCE]
  have hpair : Measurable (fun x => (q (X x), r (Y x))) :=
    (hq.comp hX).prodMk (hr.comp hY)
  have hmap := integral_map (μ := rho) hpair.aemeasurable
    (show AEStronglyMeasurable (fun p : ℝ × ℝ => binaryFusion p.1 p.2 ^ 2) _ by
      apply Measurable.aestronglyMeasurable; unfold binaryFusion; fun_prop)
  rw [map_observation_posterior_pair_eq_binaryFusionJointLaw
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd] at hmap
  rw [← hmap]
  have hqm : ∀ᵐ u ∂Measure.map (fun x => q (X x)) rho, |u| < 1 :=
    (ae_map_iff (hq.comp hX).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hqb
  have hrm : ∀ᵐ u ∂Measure.map (fun x => r (Y x)) rho, |u| < 1 :=
    (ae_map_iff (hr.comp hY).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hrb
  rw [binaryFusionJointLaw_secondMoment hqm hrm hsym,
    integral_map (μ := rho) (φ := fun x => q (X x)) (f := fun u : ℝ => u ^ 2)
      (hq.comp hX).aemeasurable (by fun_prop),
    integral_map (μ := rho) (φ := fun x => r (Y x)) (f := fun u : ℝ => u ^ 2)
      (hr.comp hY).aemeasurable (by fun_prop)]

theorem condExp_observation_pair_secondMoment_le_add
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (fun x => r (Y x)) rho) = Measure.map (fun x => r (Y x)) rho) :
    (∫ x, (rho[fun x => spinSign (S x) |
      (inferInstance : MeasurableSpace (A × B)).comap (fun x => (X x, Y x))] x) ^ 2 ∂rho) ≤
      (∫ x, q (X x) ^ 2 ∂rho) + (∫ x, r (Y x) ^ 2 ∂rho) := by
  haveI : IsProbabilityMeasure (Measure.map (fun x => q (X x)) rho) := Measure.isProbabilityMeasure_map (hq.comp hX).aemeasurable
  haveI : IsProbabilityMeasure (Measure.map (fun x => r (Y x)) rho) := Measure.isProbabilityMeasure_map (hr.comp hY).aemeasurable
  rw [condExp_observation_pair_secondMoment
    hS hX hY hq hr hpostX hpostY hqb hrb hfair hInd hsym]
  apply sub_le_self
  apply integral_binaryFusionLoss_nonneg
  · exact (ae_map_iff (hq.comp hX).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hqb
  · exact (ae_map_iff (hr.comp hY).aemeasurable
      (measurableSet_lt measurable_abs measurable_const)).2 hrb

end Observations

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Flip
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.map_flipConfig {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    HasFreeIsingLaw theta (mu.map flipConfig) := by
  intro D hD eta
  have hmeas : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
    simp only [Set.ofPred_forall]
    apply D.measurableSet_biInter
    intro v hv
    exact (show MeasurableSet ({eta v} : Set IsingSpin) from trivial).preimage
      (measurable_pi_apply v)
  rw [Measure.map_apply measurable_flipConfig hmeas]
  have hpre : flipConfig ⁻¹' {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} =
      {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = flipConfig eta v} := by
    ext x
    simp [flipConfig]
  rw [hpre, hmu D hD (flipConfig eta), freeCylinderWeight_flipConfig]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeLawSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.flip_invariant {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    mu.map flipConfig = mu :=
  hmu.map_flipConfig.unique hmu

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_FiniteSignalInformation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem367

theorem spinInformation_sup_le_add
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| < 1)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a}))
    (hsym : Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | m₂]) rho) :
    spinInformation rho S (m₁ ⊔ m₂) ≤
      spinInformation rho S m₁ + spinInformation rho S m₂ := by
  have hX : @Measurable Ω Ω mΩ m₁ id := measurable_id.mono hm₁ le_rfl
  have hY : @Measurable Ω Ω mΩ m₂ id := measurable_id.mono hm₂ le_rfl
  have hI : ∀ a : IsingSpin,
      @IndepFun Ω Ω Ω mΩ m₁ m₂ id id (cond rho {x | S x = a}) := by
    intro a
    simpa [IndepFun, Kernel.IndepFun, Indep] using hInd a
  have h := @condExp_observation_pair_secondMoment_le_add
    Ω Ω Ω mΩ m₁ m₂ rho _ S hS id id hX hY
    (rho[fun y => spinSign (S y) | m₁])
    (rho[fun y => spinSign (S y) | m₂])
    stronglyMeasurable_condExp.measurable stronglyMeasurable_condExp.measurable
    (by simp) (by simp) h₁ h₂ hfair hI hsym
  change spinInformation rho S
    ((m₁.prod m₂).comap (fun x : Ω => (id x, id x))) ≤ _ at h
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_id,
    MeasurableSpace.comap_id] at h
  exact h

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

theorem selectedPosterior_identDistrib_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r)
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  have hm := measurable_selectedPosterior
    (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) hF v r
  refine ⟨hm.aemeasurable, (measurable_selectedPosterior _ hF _ _).aemeasurable, ?_⟩
  have hCE := selectedPosterior_relabel_ae hmu nu hF v r g
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hmu nu g
  calc
    _ = Measure.map
        (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r ∘
          Prod.map (relabel g) (relabel g))
        (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
      rw [← Measure.map_map hm hmp.measurable, hmp.map_eq]
    _ = _ := Measure.map_congr hCE

theorem selectedPosterior_secondMoment_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    (∫ p, selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      F v r p ^ 2 ∂mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) =
    ∫ p, selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r) p ^ 2
        ∂mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)) :=
  ((selectedPosterior_identDistrib_relabel hmu nu hF v r g).comp
    (show Measurable (fun u : ℝ => u ^ 2) by fun_prop)).integral_eq

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem selectedPosterior_abs_le_one {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ∀ᵐ p ∂ρ, |selectedPosterior ρ F v r p| ≤ 1 := by
  apply ae_bdd_abs_condExp_of_ae_bdd_abs
  apply Filter.Eventually.of_forall
  intro p
  cases hs : p.1 r <;> norm_num [spinSign, hs]

theorem measurePreserving_plantedMarkFlip {d : ℕ} {A : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν) :
    MeasurePreserving (plantedMarkFlipEquiv d A)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  have hm : (Measure.infinitePi (fun _ : TreeVertex d => ν)).map Neg.neg =
      Measure.infinitePi (fun _ : TreeVertex d => ν) := by
    change (Measure.infinitePi (fun _ : TreeVertex d => ν)).map
      (fun z i => -z i) = _
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_neg)]
    simp only [hν]
  exact (show MeasurePreserving flipConfig μ μ from
    ⟨measurable_flipConfig, hμ.flip_invariant⟩).prod
    (show MeasurePreserving Neg.neg
      (Measure.infinitePi (fun _ : TreeVertex d => ν))
      (Measure.infinitePi (fun _ : TreeVertex d => ν)) from ⟨measurable_neg, hm⟩)

theorem measurable_plantedMarkFlip_selectedObservationField
    {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B]
    (F : IsingSpin → A → B)
    (hodd : ∀ s z, F s.flip (-z) = -F s z) (v : ι → TreeVertex d) :
    Measurable[selectedObservationField F v, selectedObservationField F v]
      (plantedMarkFlipEquiv d A) := by
  apply measurable_comap_iff.mpr
  have heq : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun i => F (p.1 (v i)) (p.2 (v i))) ∘ plantedMarkFlipEquiv d A =
      fun p i => -F (p.1 (v i)) (p.2 (v i)) := by
    funext p i
    exact hodd (p.1 (v i)) (p.2 (v i))
  rw [heq]
  exact (comap_measurable (fun p : (TreeVertex d → IsingSpin) ×
    (TreeVertex d → A) => fun i => F (p.1 (v i)) (p.2 (v i)))).neg

theorem selectedPosterior_flip_ae {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r ∘
      plantedMarkFlipEquiv d A =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      -selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r := by
  let := hμ.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  have hi : Integrable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) ρ := by
    have hs : Measurable spinSign := by intro s hs; trivial
    apply Integrable.of_bound
      ((hs.comp ((measurable_pi_apply r).comp measurable_fst)).aestronglyMeasurable) 1
    apply Filter.Eventually.of_forall
    intro p
    cases hs : p.1 r <;> norm_num [spinSign, hs]
  have hm := measurable_plantedMarkFlip_selectedObservationField F hodd v
  have hn := condExp_comp_measurePreserving_equiv
    (selectedObservationField_le hF v) (plantedMarkFlipEquiv d A)
    (measurePreserving_plantedMarkFlip hμ ν hν) hm hm hi
  have ho : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) ∘ plantedMarkFlipEquiv d A =
      -(fun p => spinSign (p.1 r)) := by
    funext p
    cases hs : p.1 r <;>
      simp [plantedMarkFlipEquiv, flipConfig, IsingSpin.flip, spinSign, hs]
  rw [ho] at hn
  exact hn.trans (condExp_neg _ _)

theorem selectedPosteriorLaw_neg_invariant {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))).map
      (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r)).map
        Neg.neg =
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))).map
        (selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r) := by
  exact FactorTransport.map_invariant_of_ae_equivariant
    (measurePreserving_plantedMarkFlip hμ ν hν) measurable_neg
    (measurable_selectedPosterior _ hF v r)
    (selectedPosterior_flip_ae hμ ν hν hF hodd v r)

theorem HasFreeIsingLaw.selected_gaussian_posteriorLaw_neg_invariant
    {d : ℕ} {ι : Type*} {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (t : ℝ) (variance : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d) :
    ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
      (selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
        (fun s z => t * spinSign s + z) v r)).map Neg.neg =
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)).map
        (selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
          (fun s z => t * spinSign s + z) v r) := by
  apply selectedPosteriorLaw_neg_invariant hμ (gaussianReal 0 variance)
  · simp only [gaussianReal_map_neg, neg_zero]
  · have hs : Measurable spinSign := by intro s hs; trivial
    exact ((hs.comp measurable_fst).const_mul t).add measurable_snd
  · intro s z
    cases s <;> simp [IsingSpin.flip, spinSign] <;> ring

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

local instance instMeasurableSingletonClassIsingSpin_3_r0e31cd_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
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

local instance instMeasurableSingletonClassIsingSpin_2_r0e31cd_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
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

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BranchFlipGeometry
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367
namespace RootedBroadcast

theorem prefix_flip_iff_not_prefix {d : ℕ} (c : Fin d) (v : TreeVertex d) :
    [c] <+: (prefixFlip c v).val ↔ ¬ [c] <+: v.val := by
  constructor
  · intro h
    simpa only [prefixFlip_twice] using
      not_prefix_flip_of_prefix c (prefixFlip c v) h
  · intro h
    rcases v with ⟨w, hw⟩
    cases w with
    | nil => simp [prefixFlip, prefixFlipWord]
    | cons b t =>
      have hcb : c ≠ b := by
        intro heq
        subst b
        exact h (by simp)
      simp [prefixFlip, prefixFlipWord, hcb]

end RootedBroadcast
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

theorem measurable_decodeFlippedBranch {d : ℕ} {A : Type*} [MeasurableSpace A]
    (c : Fin d) : Measurable (decodeFlippedBranch (A := A) c) :=
  (Measurable.of_eval (fun v =>
    (measurable_noisyRootOtherDecode c (RootedBroadcast.flipBranchToComplement c v)).fst)).prodMk
      (Measurable.of_eval (fun v =>
        (measurable_noisyRootOtherDecode c (RootedBroadcast.flipBranchToComplement c v)).snd))

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
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_SiteInformation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem component_or_flipped_component {d : ℕ} (c : Fin d) (v : TreeVertex d) :
    v ∈ Set.range (componentIndexVertex (c := c)) ∨
      v ∈ Set.range (fun u : ComponentIndex c => prefixFlip c (componentIndexVertex u)) := by
  by_cases h : [c] <+: v.1
  · left
    apply mem_range_componentIndexVertex.mpr
    obtain ⟨w, hw⟩ := h
    exact ⟨w, by simpa using hw.symm⟩
  · right
    have hf := (RootedBroadcast.prefix_flip_iff_not_prefix c v).mpr h
    obtain ⟨w, hw⟩ := hf
    have hmem : prefixFlip c v ∈ Set.range (componentIndexVertex (c := c)) :=
      mem_range_componentIndexVertex.mpr ⟨w, by simpa using hw.symm⟩
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, ?_⟩
    change prefixFlip c (componentIndexVertex u) = v
    rw [hu, prefixFlip_twice]

theorem selectedObservationField_eq_component_sup_flip
    {d : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (c : Fin d) :
    selectedObservationField F id =
      selectedObservationField F (fun u : ComponentIndex c => prefixFlip c (componentIndexVertex u)) ⊔
      selectedObservationField F (componentIndexVertex (c := c)) := by
  apply le_antisymm
  · simp only [selectedObservationField, MeasurableSpace.comap_process_pi, id_eq]
    apply iSup_le
    intro v
    rcases component_or_flipped_component c v with ⟨u, rfl⟩ | ⟨u, rfl⟩
    · exact le_sup_of_le_right (le_iSup_of_le u le_rfl)
    · exact le_sup_of_le_left (le_iSup_of_le u le_rfl)
  · apply sup_le
    · apply selectedObservationField_le_of_range_subset F
      intro v hv
      exact ⟨v, rfl⟩
    · apply selectedObservationField_le_of_range_subset F
      intro v hv
      exact ⟨v, rfl⟩

theorem HasFreeIsingLaw.condIndepFun_component_flip_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) => z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => fun u : ComponentIndex c => F
        (z.1 (prefixFlip c (componentIndexVertex u))) (z.2 (prefixFlip c (componentIndexVertex u))))
      (fun z => fun u : ComponentIndex c => F (z.1 (componentIndexVertex u)) (z.2 (componentIndexVertex u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let v (u : ComponentIndex c) : RootedBroadcast.BranchVertex c :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G (p : (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) :=
    fun u : ComponentIndex c => F (p.1 (v u)) (p.2 (v u))
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A) => (p.1 (v u), p.2 (v u))) by fun_prop)
  have h := (hμ.condIndepFun_noisy_root_others_branch h0 h1 (fun _ => ν) c).comp
    (hG.comp (measurable_decodeFlippedBranch c)) hG
  simpa only [Function.comp_def, G, decodeFlippedBranch, noisyRootOtherDecode_array,
    RootedBroadcast.flipBranchToComplement_val, noisyBranchArray, v] using h

theorem HasFreeIsingLaw.gaussian_root_information_le_component_oai
    {d : ℕ} {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    (∫ z, (PlantedSymmetry.posteriorMagnetization
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) t
      (RootedBroadcast.root d) z) ^ 2
      ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) ≤
      (1 + (Real.tanh beta) ^ 2) * gaussianComponentInformation μ t c := by
  let := hμ.isProbabilityMeasure
  let mΩ : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) := inferInstance
  let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
  let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
  let r := RootedBroadcast.root d
  let w := fun u : ComponentIndex c => prefixFlip c (componentIndexVertex u)
  let mL := selectedObservationField F w
  let mR := selectedObservationField F (componentIndexVertex (c := c))
  let : MeasurableSpace ((TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) := mΩ
  let S (z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ)) := z.1 r
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add measurable_snd
  have hS : Measurable S := (measurable_pi_apply r).comp measurable_fst
  have hθ0 := tanh_nonneg_of_beta_nonneg hb
  have hθ1 := Real.tanh_lt_one beta
  have hθlo : -1 ≤ Real.tanh beta := by linarith
  have hfair (s : IsingSpin) : ρ {z | S z = s} = (1 / 2 : ENNReal) :=
    hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) r s
  have hL : ∀ᵐ z ∂ρ, |ρ[fun z => spinSign (S z) | mL] z| < 1 := by
    have hr : r ∈ Set.range w := by
      refine ⟨⟨0, ⟨[], rfl, List.IsChain.singleton c⟩⟩, ?_⟩
      exact RootedBroadcast.prefixFlip_branchRoot c
    filter_upwards [hμ.selected_gaussian_posterior_field_bound hb t w r hr] with z hz
    exact abs_lt.mpr hz.1
  have hreg := hμ.selectedPosterior_root_component hθlo hθ1.le (gaussianReal 0 t) hF c
  have hR : ∀ᵐ z ∂ρ, |ρ[fun z => spinSign (S z) | mR] z| < 1 := by
    filter_upwards [hreg, selectedPosterior_abs_le_one ρ F (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c)] with z hz hz1
    change |selectedPosterior ρ F (componentIndexVertex (c := c)) r z| < 1
    change selectedPosterior ρ F (componentIndexVertex (c := c)) r z =
      Real.tanh beta * selectedPosterior ρ F (componentIndexVertex (c := c))
        (RootedBroadcast.branchRoot c) z at hz
    rw [hz, abs_mul, abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_left hz1 hθ0).trans_lt (by simpa using hθ1)
  have hCI := hμ.condIndepFun_component_flip_observations hθlo hθ1.le (gaussianReal 0 t) hF c
  have hInd (s : IsingSpin) : Indep mL mR (cond ρ {z | S z = s}) := by
    exact indepFun_cond_fiber_of_condIndepFun hS
      (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        fun u : ComponentIndex c => F (z.1 (w u)) (z.2 (w u))) from
        Measurable.of_eval (fun u => hF.comp (show Measurable
          (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
            (z.1 (w u), z.2 (w u))) by fun_prop)))
      (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        fun u : ComponentIndex c => F (z.1 (componentIndexVertex u)) (z.2 (componentIndexVertex u))) from
        Measurable.of_eval (fun u => hF.comp (show Measurable
          (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
            (z.1 (componentIndexVertex u), z.2 (componentIndexVertex u))) by fun_prop))) hCI s
  have hsym := hμ.selected_gaussian_posteriorLaw_neg_invariant t t
    (componentIndexVertex (c := c)) r
  have hsum := spinInformation_sup_le_add (selectedObservationField_le hF w)
    (selectedObservationField_le hF (componentIndexVertex (c := c))) hS hL hR hfair hInd hsym
  have hfield := selectedObservationField_eq_component_sup_flip F c
  change selectedObservationField F id = mL ⊔ mR at hfield
  rw [← hfield] at hsum
  have hleft : spinInformation ρ S mL = gaussianComponentInformation μ t c := by
    have h := selectedPosterior_secondMoment_relabel hμ (gaussianReal 0 t) hF
      (componentIndexVertex (c := c)) (RootedBroadcast.branchRoot c) (prefixTreeAut c)
    rw [RootedBroadcast.prefixTreeAut_symm_branchRoot] at h
    exact h.symm
  have hright : spinInformation ρ S mR =
      (Real.tanh beta) ^ 2 * gaussianComponentInformation μ t c := by
    have h := integral_congr_ae (hreg.fun_comp (fun x : ℝ => x ^ 2))
    simp only [Function.comp_apply, mul_pow, integral_const_mul] at h
    exact h
  rw [hleft, hright] at hsum
  change (∫ z, (PlantedSymmetry.posteriorMagnetization ρ t r z) ^ 2 ∂ρ) ≤ _ at hsum
  nlinarith [hsum]

end Problem367

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.HasFreeIsingLaw.gaussian_root_information_le_component_oai := @OAI.Problem367.HasFreeIsingLaw.gaussian_root_information_le_component_oai
