-- Prove2me | solution 1 for OAI.Rokhlin.tail_finite_correlation_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:02:57.317723+00:00
-- url     : https://prove2.me/submissions/80551dd8-cc52-4249-9bfd-b835e466fe12

import Mathlib
import Definitions.Def_Rokhlin
import Definitions.Def_OAIQ3Ro000
import Definitions.Def_OAIQ3Ro001
import Theorems.Thm_OAI_Rokhlin_ArrayObjects_compact_zero_entropy_no_witness
import Theorems.Thm_OAI_Rokhlin_finite_tail_entropy_zero

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Entropy
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators symmDiff
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

omit [IsProbabilityMeasure μ] in
lemma randomEntropy_measurePreserving {Υ : Type*} [MeasurableSpace Υ] (ν : Measure Υ)
    [IsProbabilityMeasure ν] {T : Ω → Υ} (hT : MeasurePreserving T μ ν)
    (F : Υ → A) (hF : Measurable F) : randomEntropy μ (F ∘ T) = randomEntropy ν F := by
  unfold randomEntropy
  congr 1
  funext a
  exact hT.measureReal_preimage (hF (measurableSet_singleton a)).nullMeasurableSet

end

section
open MeasureTheory Filter
variable {Ω A : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)
    [MeasurableSpace A]

lemma processTail_le (F : ℤ → Ω → A) : processTail μ F ≤ m₀ :=
  (iInf_le _ 0).trans (completedFactor_le μ _)

end

open MeasureTheory Filter
open scoped Topology

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω]
lemma timeMap_zero (T : Ω ≃ᵐ Ω) : timeMap T 0 = id := by
  simp [timeMap]
lemma timeMap_add (T : Ω ≃ᵐ Ω) (m n : ℤ) : timeMap T (m+n) = timeMap T m ∘ timeMap T n := by
  simp only [timeMap,zpow_add,Equiv.Perm.coe_mul]
lemma timeMap_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T n = (T : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
lemma timeMap_neg_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T (-(n:ℤ)) = (T.symm : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_neg,zpow_natCast,←inv_pow,Equiv.Perm.coe_pow]
  rfl
lemma timeMap_measurable (T : Ω ≃ᵐ Ω) (n : ℤ) : Measurable (timeMap T n) := by
  induction n using Int.negInduction with
  | nat n => rw [timeMap_nat]; exact T.measurable.iterate n
  | neg _ n => rw [timeMap_neg_nat]; exact T.symm.measurable.iterate n
end

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [TopologicalSpace A] [BorelSpace A]

omit [MeasurableSpace A] [BorelSpace A] in
lemma fullShift_iterate (n : ℕ) (x : ℤ → A) (q : ℤ) :
    (fullShift^[n]) x q = x (q+n) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change (fullShift^[n]) x (q+1) = _
    rw [ih]
    congr 1
    push_cast
    ring

omit [TopologicalSpace A] [BorelSpace A] in
lemma symbolicCode_measurable (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a) :
    Measurable (symbolicCode T a) := Measurable.of_eval fun q => ha.comp (timeMap_measurable T q)

omit [MeasurableSpace A] [BorelSpace A] in
lemma symbolicCode_time (T : Ω ≃ᵐ Ω) (a : Ω → A) (n : ℕ) (x : Ω) :
    symbolicCode T a (timeMap T n x) = (fullShift^[n]) (symbolicCode T a x) := by
  funext q
  rw [fullShift_iterate]
  exact congrArg a (congrFun (timeMap_add T q n).symm x)

variable [SecondCountableTopology A]
lemma symbolicShift_preserving (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (a : Ω → A) (ha : Measurable a) :
    MeasurePreserving fullShift (μ.map (symbolicCode T a)) (μ.map (symbolicCode T a)) := by
  refine ⟨fullShift.continuous.measurable,?_⟩
  rw [Measure.map_map fullShift.continuous.measurable (symbolicCode_measurable T a ha)]
  have he : fullShift ∘ symbolicCode T a = symbolicCode T a ∘ T := by
    funext x
    simpa only [Function.comp_apply,timeMap_nat,Function.iterate_one] using (symbolicCode_time T a 1 x).symm
  rw [he,←Measure.map_map (symbolicCode_measurable T a ha) T.measurable,hT.map_eq]

omit [SecondCountableTopology A] [TopologicalSpace A] [BorelSpace A] in
lemma symbolicCode_preserving (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a) :
    MeasurePreserving (symbolicCode T a) μ (μ.map (symbolicCode T a)) :=
  ⟨symbolicCode_measurable T a ha,rfl⟩

lemma symbolicShift_mixing (μ : Measure Ω) (T : Ω ≃ᵐ Ω)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (a : Ω → A) (ha : Measurable a) :
    ∀ s t : Set (ℤ → A), MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ.map (symbolicCode T a) (s ∩ (fullShift^[n]) ⁻¹' t)) atTop
        (𝓝 (μ.map (symbolicCode T a) s * μ.map (symbolicCode T a) t)) := by
  intro s t hs ht
  have hc := symbolicCode_measurable T a ha
  have h := hmix (symbolicCode T a ⁻¹' s) (symbolicCode T a ⁻¹' t) (hc hs) (hc ht)
  rw [Measure.map_apply hc hs,Measure.map_apply hc ht]
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [Measure.map_apply hc (hs.inter ((fullShift.continuous.iterate n).measurable ht))]
  congr 1
  ext x
  simp only [Set.mem_preimage,Set.mem_inter_iff]
  rw [←symbolicCode_time,timeMap_nat]

lemma symbolicCode_rectangles {I : Type*} [Fintype I]
    (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a)
    (d : I → ℕ) (s : I → Set (ℤ → A)) (hs : ∀ i, MeasurableSet (s i)) :
    μ.map (symbolicCode T a) (⋂ i, (fullShift^[d i]) ⁻¹' s i) =
      μ (⋂ i, (T^[d i]) ⁻¹' (symbolicCode T a ⁻¹' s i)) := by
  rw [Measure.map_apply (symbolicCode_measurable T a ha)
    (MeasurableSet.iInter fun i => (fullShift.continuous.iterate (d i)).measurable (hs i))]
  congr 1
  ext x
  simp only [Set.mem_preimage,Set.mem_iInter]
  simp_rw [←symbolicCode_time,timeMap_nat]

variable [Fintype A] [MeasurableSingletonClass A]
lemma symbolicCode_entropy {B : Type*} [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω) (a : Ω → A) (ha : Measurable a)
    (b : A → B) (n : ℕ) :
    randomEntropy (μ.map (symbolicCode T a)) (fun x : ℤ → A => fun i : Fin n => b ((fullShift^[i.val]) x 0)) =
      randomEntropy μ (fun x => fun i : Fin n => b (a (timeMap T i.val x))) := by
  let : IsProbabilityMeasure (μ.map (symbolicCode T a)) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) (symbolicCode_measurable T a ha).aemeasurable
  have hb : Measurable (fun x : ℤ → A => fun i : Fin n => b ((fullShift^[i.val]) x 0)) :=
    Measurable.of_eval fun i => (measurable_of_finite b).comp
      ((measurable_pi_apply 0).comp (fullShift.continuous.iterate i.val).measurable)
  have h := randomEntropy_measurePreserving μ (μ.map (symbolicCode T a))
    (symbolicCode_preserving μ T a ha) _ hb
  simpa [Function.comp_def,fullShift_iterate,symbolicCode] using h.symm
end

section
open MeasureTheory Filter TopologicalSpace
open scoped Topology BigOperators
variable {Ω : Type*} {I : Type} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

theorem finite_alphabet_no_witness (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    {A B : Type} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (a : Ω → A) (ha : Measurable a) (b : A → B)
    (v : B → ℝ) (hcenter : ∫ x, v (b (a x)) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => randomEntropy μ
        (fun x => fun i : Fin n => b (a ((T^[i.val]) x))) / n) atTop (𝓝 0))
    (i : I) (f : I → A → ℝ) (hb : ∀ j z, |f j z| ≤ 1)
    (hi : ∀ z, f i z = v (b z)) (δ : ℝ) (hδ : 0 < δ)
    (hc : ∀ r, δ ≤ ∫ x, ∏ j, f j (a ((T^[d r j]) x)) ∂μ) : False := by
  let X : ArrayObjects.StandardSpace := ⟨ℤ → A,inferInstance,inferInstance,inferInstance⟩
  let C : Ω → X := symbolicCode T a
  have hC : Measurable C := symbolicCode_measurable T a ha
  let : IsProbabilityMeasure (μ.map C) := (fun mapMeasurable => (Measure.isProbabilityMeasure_map_iff mapMeasurable).mpr inferInstance) hC.aemeasurable
  let ν : ProbabilityMeasure X := ⟨μ.map C,inferInstance⟩
  let S : X ≃ₜ X := fullShift
  let F : I → C(X,ℝ) := fun j => ⟨fun x => f j (x 0),
    (continuous_of_discreteTopology (f := f j)).comp (continuous_apply 0)⟩
  have hp : MeasurePreserving S ν ν := symbolicShift_preserving μ T hT a ha
  have hr : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set X,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => (ν : Measure X) (⋂ j : J, (S^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, (ν : Measure X) (s j))) := by
    intro J hJ s hs
    have hh := hrect J hJ (fun j => C ⁻¹' s j) (fun j => hC (hs j))
    convert hh using 1
    · funext r
      exact symbolicCode_rectangles μ T a ha _ s hs
    · congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact Measure.map_apply hC (hs j)
  have hctr : ∫ x : X, v (b (x 0)) ∂(ν : Measure X) = 0 := by
    change (∫ x : ℤ → A, v (b (x 0)) ∂μ.map C) = 0
    have hm : AEStronglyMeasurable (fun x : ℤ → A => v (b (x 0))) (μ.map C) :=
      (((measurable_of_finite v).comp ((measurable_of_finite b).comp (measurable_pi_apply 0))).aestronglyMeasurable)
    rw [integral_map hC.aemeasurable hm]
    change (∫ x, v (b (a (timeMap T 0 x))) ∂μ) = 0
    simpa only [timeMap_zero,id_eq] using hcenter
  have hent : Tendsto (fun n : ℕ => wordEntropy (η := (ν : Measure X))
      (fun m x => b ((S^[m]) x 0)) n / n) atTop (𝓝 0) := by
    convert hH using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    congr 1
    change randomEntropy (μ.map C) (fun x => fun j : Fin n => b ((S^[j.val]) x 0)) = _
    simpa only [timeMap_nat] using symbolicCode_entropy μ T a ha b n
  apply ArrayObjects.compact_zero_entropy_no_witness S d ν hp hr hk
    (symbolicShift_mixing μ T hmix a ha) (fun x => b (x 0))
    ((measurable_of_finite b).comp (measurable_pi_apply 0)) v hctr hent i F
    (fun j x => hb j (x 0)) (fun x => hi (x 0)) δ hδ
  intro r
  change δ ≤ ∫ x : X, ∏ j, f j ((S^[d r j]) x 0) ∂μ.map C
  have hm : AEStronglyMeasurable (fun x : X => ∏ j, f j ((S^[d r j]) x 0)) (μ.map C) := by
    apply Continuous.aestronglyMeasurable
    exact continuous_finsetProd Finset.univ fun j _ =>
      (continuous_of_discreteTopology (f := f j)).comp
        ((continuous_apply 0).comp (S.continuous.iterate (d r j)))
  rw [integral_map hC.aemeasurable hm]
  convert hc r using 1
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards with x
  apply Finset.prod_congr rfl
  intro j _
  change f j ((fullShift^[d r j]) (symbolicCode T a x) 0) = _
  rw [fullShift_iterate,zero_add]
  change f j (a (timeMap T (d r j) x)) = _
  rw [timeMap_nat]
end

section
open Filter
open scoped Topology
lemma exists_signed_subsequence {x : ℕ → ℝ} (hx : ¬Tendsto x atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ σ : ℝ, |σ| = 1 ∧ ∃ u : ℕ → ℕ,
      StrictMono u ∧ ∀ n, ε ≤ σ*x (u n) := by
  have hh : ¬∀ ε > (0:ℝ), ∀ᶠ n in atTop, |x n| < ε := by
    intro h
    apply hx
    exact Metric.tendsto_nhds.mpr (by simpa only [Real.dist_eq,sub_zero] using h)
  push Not at hh
  obtain ⟨ε,hε,he⟩ := hh
  have hf : ∃ᶠ n in atTop, ε ≤ x n ∨ x n ≤ -ε := by
    simpa only [not_lt,le_abs,le_neg] using he
  rcases frequently_or_distrib.mp hf with hp | hn
  · obtain ⟨u,hu,hp⟩ := extraction_of_frequently_atTop hp
    exact ⟨ε,hε,1,by norm_num,u,hu,fun n => by simpa using hp n⟩
  · obtain ⟨u,hu,hn⟩ := extraction_of_frequently_atTop hn
    exact ⟨ε,hε,-1,by norm_num,u,hu,fun n => by have := hn n; linarith⟩
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I : Type} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]

lemma prod_sign_one (i : I) (σ : ℝ) (z : I → ℝ) :
    (∏ j, (if j=i then σ else 1)*z j) = σ*∏ j, z j := by
  rw [Finset.prod_mul_distrib]
  simp

theorem finite_alphabet_correlation_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    {A B : Type} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
    [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
    (a : Ω → A) (ha : Measurable a) (b : A → B)
    (v : B → ℝ) (hcenter : ∫ x, v (b (a x)) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => randomEntropy μ
        (fun x => fun i : Fin n => b (a ((T^[i.val]) x))) / n) atTop (𝓝 0))
    (i : I) (f : I → A → ℝ) (hb : ∀ j z, |f j z| ≤ 1) (hi : ∀ z, f i z = v (b z)) :
    Tendsto (fun r => ∫ x, ∏ j, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  by_contra hn
  obtain ⟨δ,hδ,σ,hσ,u,hu,hpos⟩ := exists_signed_subsequence hn
  let F : I → A → ℝ := fun j z => (if j=i then σ else 1)*f j z
  apply finite_alphabet_no_witness μ T hT hmix hk (fun r => d (u r))
    (fun J hJ s hs => (hrect J hJ s hs).comp hu.tendsto_atTop) a ha b
    (fun z => σ*v z) ?_ hH i F ?_ ?_ δ hδ ?_
  · rw [integral_const_mul,hcenter,mul_zero]
  · intro j z
    dsimp [F]
    rw [abs_mul]
    split_ifs <;> simpa only [hσ,abs_one,one_mul] using hb j z
  · intro z
    simp [F,hi]
  · intro r
    change δ ≤ ∫ x, ∏ j, (if j=i then σ else 1)*f j (a ((T^[d (u r) j]) x)) ∂μ
    simp_rw [prod_sign_one]
    rw [integral_const_mul]
    exact hpos r
end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A B : Type} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
    [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]
    [TopologicalSpace B] [DiscreteTopology B] [BorelSpace B]

theorem tail_finite_correlation_zero_oai (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    (a : Ω → A) (ha : Measurable a) (b : Ω → B)
    (hb : Measurable[observableTail μ T a] b) (v : B → ℝ)
    (hc : ∫ x, v (b x) ∂μ = 0) (hv : ∀ z, |v z| ≤ 1)
    (i : I) (f : I → A → ℝ) (hf : ∀ j z, |f j z| ≤ 1) :
    Tendsto (fun r => ∫ x, ∏ j, if j=i then v (b ((T^[d r j]) x))
      else f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  have hbm : Measurable b := hb.mono (processTail_le μ _) le_rfl
  exact finite_alphabet_correlation_zero μ T hT hmix hk d hrect
    (fun x => (a x,b x)) (ha.prodMk hbm) Prod.snd v hc
    (finite_tail_entropy_zero μ T hT a ha b hb) i
    (fun j z => if j=i then v z.2 else f j z.1)
    (fun j z => by split_ifs; exact hv _; exact hf _ _) (fun _ => ite_eq_left rfl)
end

open MeasureTheory Filter
open scoped Topology BigOperators

end Rokhlin

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Rokhlin.tail_finite_correlation_zero_oai.{u_1} := @OAI.Rokhlin.tail_finite_correlation_zero_oai.{u_1}
