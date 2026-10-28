-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:55:13.940769+00:00
-- url     : https://prove2.me/submissions/96922e15-4fb8-49ec-bf88-1da54abb43ab

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype A] in
lemma density_nonneg {w : E → A → ℝ} (h : ∀ e a, 0 ≤ w e a) (ω : E → A) :
    0 ≤ density w ω := Finset.prod_nonneg fun e _ => h e (ω e)

lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BernoulliProduct

lemma bitWeight_sum (p : unitInterval) : ∑ b, bitWeight p b = 1 := by
  simp [bitWeight]

lemma bitWeight_nonneg (p : unitInterval) (b : Prop) : 0 ≤ bitWeight p b := by
  unfold bitWeight
  split_ifs
  · exact p.property.1
  · exact sub_nonneg.mpr p.property.2

lemma bitMeasure_real_singleton (p : unitInterval) (b : Prop) :
    (bitMeasure p).real {b} = bitWeight p b := by
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]

variable {E : Type*}

lemma law_const (p : unitInterval) :
    law (fun _ : E => p) = setBernoulli Set.univ p := by
  rw [law, setBernoulli_eq_map]
  rfl

lemma integral_bits_eq_expect [Fintype E] (q : E → unitInterval) (f : (E → Prop) → ℝ) :
    (∫ ω, f ω ∂(Measure.infinitePi fun e => bitMeasure (q e))) =
      FiniteProduct.expect (fun e => bitWeight (q e)) f := by
  rw [Measure.infinitePi_eq_pi, integral_fintype Integrable.of_finite]
  unfold FiniteProduct.expect FiniteProduct.density
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_eq_mul]
  congr 1
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun e _ => bitMeasure_real_singleton (q e) (ω e))

lemma integral_law_eq_expect [Fintype E] (q : E → unitInterval) (f : Set E → ℝ) :
    (∫ ω, f ω ∂law q) =
      FiniteProduct.expect (fun e => bitWeight (q e)) (fun ω => f {e | ω e}) := by
  rw [law, integral_map MeasurableEquiv.setOfPred.measurable.aemeasurable
    Integrable.of_finite.aestronglyMeasurable, integral_bits_eq_expect]
  rfl

lemma law_map_restrict (q : E → unitInterval) (s : Set E) :
    (law q).map (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) =
      law (fun e : s => q e) := by
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_set_iff.mpr (fun bond => measurable_set_mem bond.val)
  unfold law
  rw [Measure.map_map hmeas MeasurableEquiv.setOfPred.measurable]
  have hcomp : (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) ∘
      MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ s.domRestrict := rfl
  rw [hcomp, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_restrict']

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_TailProduct
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_eq_infinitePi (q : E → unitInterval) :
    law q = Measure.infinitePi (fun e => bitMeasure (q e)) := by
  change Measure.map id _ = _
  exact Measure.map_id

lemma independent_coordinates (q : E → unitInterval) :
    iIndep coordinateSigma (law q) := by
  rw [law_eq_infinitePi]
  exact iIndepFun_infinitePi (X := fun _ (b : Prop) => b) (fun _ => measurable_id)

lemma independent_blocks (q : E → unitInterval) (S : Set E) :
    Indep (blockSigma S) (blockSigma Sᶜ) (law q) :=
  indep_biSup_compl coordinateSigma_le (independent_coordinates q) S

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_DensityModular
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma density_modular (w : E → Prop → ℝ) (x y : E → Prop) :
    density w x * density w y = density w (x ⊓ y) * density w (x ⊔ y) := by
  unfold density
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  simp only [Pi.inf_apply, Pi.sup_apply]
  by_cases hx : x e <;> by_cases hy : y e <;> simp [hx, hy, mul_comm]

lemma expect_mul_ge (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (f g : (E → Prop) → ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hf : Monotone f) (hg : Monotone g) :
    expect w f * expect w g ≤ expect w (fun ω => f ω * g ω) := by
  have h := fkg f g (density w) (fun ω => density_nonneg hpos ω) hf0 hg0 hf hg
    (fun x y => le_of_eq (density_modular w x y))
  simpa only [expect, sum_density w hw, one_mul] using h

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProductConditioning
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma forceOn_map_law (q : E → unitInterval) (S σ : Set E) :
    (law q).map (forceOn S σ)=law (pinnedParameters q S σ) := by
  simp only [law_eq_infinitePi]
  have hm (e : E) : Measurable (fun b : Prop => if e∈S then e∈σ else b) := .of_discrete
  have h := Measure.infinitePi_map_pi (fun e => bitMeasure (q e)) hm
  change (Measure.infinitePi (fun e => bitMeasure (q e))).map
    (fun (ω : E → Prop) e => if e∈S then e∈σ else ω e)=
    Measure.infinitePi (fun e => bitMeasure (pinnedParameters q S σ e))
  rw [h]
  congr 1
  funext e
  by_cases he : e∈S
  · simp only [ite_eq_left he,Measure.map_const,measure_univ,one_smul]
    by_cases hs : e∈σ <;> simp [pinnedParameters,he,hs,bitMeasure]
  · simp [pinnedParameters,he]

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BlockExposure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E B : Type*}

lemma measurable_block_of_dependsOn {A : Type*} [MeasurableSpace A]
    {f : Set E → A} (hf : Measurable f) (S : Set E) (hdep : DependsOn f S) :
    @Measurable (Set E) A (blockSigma S) inferInstance f := by
  have hm := hf.comp (measurable_forceOn_block Sᶜ (∅ : Set E))
  rw [compl_compl] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  apply hdep
  intro e he
  simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he),
    Set.mem_empty_iff_false]
  rfl

lemma lintegral_indicator_fresh (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hdep : DependsOn (fun ω => ω ∈ A) S)
    (g : Set E → ℝ≥0∞) (hg : Measurable g) (hgdep : DependsOn g Sᶜ) :
    (∫⁻ ω, A.indicator g ω ∂law q) = law q A * ∫⁻ ω, g ω ∂law q := by
  have hAb : MeasurableSet[blockSigma S] A := by
    have hm := hA.preimage (measurable_forceOn_block Sᶜ (∅ : Set E))
    rw [compl_compl] at hm
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    apply Iff.of_eq
    apply hdep
    intro e he
    simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he)]
    rfl
  have hgb := measurable_block_of_dependsOn hg Sᶜ hgdep
  have hi := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (blockSigma_le S) (blockSigma_le Sᶜ)
    (independent_blocks q S)
    ((measurable_const : @Measurable (Set E) ℝ≥0∞ (blockSigma S) inferInstance
      (fun _ => 1)).indicator hAb) hgb
  have heq : (fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω * g ω) = A.indicator g := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  have hone := lintegral_indicator_const (μ := law q) hA (1 : ℝ≥0∞)
  simp only [one_mul] at hone
  rw [heq, hone] at hi
  exact hi

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Bounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Coupling

theorem measurable_threshold (p : unitInterval) :
    Measurable (fun t : unitInterval => t ≤ p) :=
  measurableSet_setOfPred.mp measurableSet_Iic

 
theorem map_threshold (p : unitInterval) :
    (volume : Measure unitInterval).map (fun t => t ≤ p) =
      unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Iic p) = _
    rw [unitInterval.volume_Iic, ← unitInterval.coe_toNNReal p,
      ENNReal.ofReal_coe_nnreal]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Ioi p) = _
    rw [unitInterval.volume_Ioi, ← unitInterval.coe_symm_eq,
      ← unitInterval.coe_toNNReal (unitInterval.symm p), ENNReal.ofReal_coe_nnreal]


end Coupling

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_ProductMeasure_Association
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ClusterEvents
attribute [local instance] Classical.propDecidable
open Filter Topology


theorem finiteWitness_conn (G : BondGraph V E) (x y : V) :
    FiniteWitness {ω | Conn G ω x y} := by
  intro ω h
  induction h with
  | refl => exact ⟨∅, by simp, by simp⟩
  | @tail b c hab hbc ih =>
    obtain ⟨s, hs, hconn⟩ := ih
    obtain ⟨e, he, hGe⟩ := hbc
    refine ⟨insert e s, ?_, ?_⟩
    · simpa only [Finset.coe_insert] using Set.insert_subset he hs
    · exact (conn_mono G (by simp) hconn).tail ⟨e, by simp, hGe⟩

end ClusterEvents

section ORLift
attribute [local instance] Classical.propDecidable

instance bitLaw_isProbabilityMeasure (q : unitInterval) : IsProbabilityMeasure (bitLaw q) := by
  rw [bitLaw, ← map_threshold q]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)


end ORLift

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Sprinkling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sprinkling estimates for finite and infinite graph operators. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SprinklingLaw
attribute [local instance] Classical.propDecidable

 theorem map_bool_or (p a : unitInterval) :
    (Measure.infinitePi (fun b : Bool => bitLaw (pairParameter p a b))).map
      (fun f : Bool → Prop => ∃ b, f b) = bitLaw (sprinkleParameter p a) := by
  let μ := (Measure.infinitePi (fun b : Bool => bitLaw (pairParameter p a b))).map
      (fun f : Bool → Prop => ∃ b, f b)
  have hm : Measurable (fun f : Bool → Prop => ∃ b, f b) := .of_discrete
  have : IsProbabilityMeasure μ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hf : μ.real {False} = (1-(p : ℝ)) * (1-(a : ℝ)) := by
    change ((Measure.infinitePi _).map _).real _ = _
    rw [Measure.real, Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun f : Bool → Prop => ∃ b, f b) ⁻¹' ({False} : Set Prop) =
        ((Finset.univ : Finset Bool) : Set Bool).pi (fun _ => ({False} : Set Prop)) := by
      ext f
      simp [and_comm]
    rw [he, Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    simp [pairParameter, bitLaw, ENNReal.toReal_mul]
  have ht : μ.real {True} = (p : ℝ) + (1-p)*a := by
    have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext b; simp
    rw [he, measureReal_compl (measurableSet_singleton _), probReal_univ, hf]
    ring
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {b} = (bitLaw (sprinkleParameter p a)).real {b}
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    rw [ht]
    simp [bitLaw, Measure.real, sprinkleParameter]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    rw [hf]
    simp [bitLaw, Measure.real, sprinkleParameter]
    ring

end SprinklingLaw

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ComponentSelf
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}

lemma roots_singleton (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]

end CriticalPercolation.ClusterDeletion

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma finite_subset_exhaustion {X : Type*} {U S : Set X}
    (K : Set.FiniteExhaustion U) (hS : S.Finite) (hSU : S ⊆ U) :
    ∃ n, S ⊆ K n := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x S hx hS ih =>
      obtain ⟨n, hn⟩ := ih (Set.Subset.trans (Set.subset_insert _ _) hSU)
      have hxU := hSU (Set.mem_insert x S)
      rw [← K.iUnion_eq, Set.mem_iUnion] at hxU
      obtain ⟨m, hm⟩ := hxU
      exact ⟨max m n, Set.insert_subset (K.mono (le_max_left _ _) hm)
        (Set.Subset.trans hn (K.mono (le_max_right _ _)))⟩

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteOpenWitness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma finiteWitness_exhaustion (A : Set (Set E)) (hmono : IsUpperSet A)
    (hw : HasFiniteOpenWitness A) (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    (⋃ n, {ω | K n ∩ ω ∈ A}) = A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact hmono Set.inter_subset_right hn
  · intro h
    obtain ⟨s, hs, hsω, hsA⟩ := hw ω h
    obtain ⟨n, hn⟩ := BondGraph.finite_subset_exhaustion K hs (Set.subset_univ _)
    exact Set.mem_iUnion.mpr ⟨n, hmono (Set.subset_inter hn hsω) hsA⟩

lemma finiteWitness_exhaustion_mono (A : Set (Set E)) (hmono : IsUpperSet A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Monotone (fun n => {ω | K n ∩ ω ∈ A}) := by
  intro m n h ω hω
  exact hmono (Set.inter_subset_inter_left _ (K.mono h)) hω

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_MeasurableSetRestrict
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurableSet_restrict (s : Set E) (hs : s.Finite) (A : Set (Set E)) :
    MeasurableSet {ω | s ∩ ω ∈ A} := by
  let := hs.fintype
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have he : {ω : Set E | s ∩ ω ∈ A} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        {u : Set s | Subtype.val '' u ∈ A} := by
    ext ω
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
      ext e
      simp
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hi]
  rw [he]
  exact hf (.of_discrete)

lemma measurableSet_finiteWitness [Countable E] (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A) : MeasurableSet A := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  rw [← finiteWitness_exhaustion A hmono hw K]
  exact MeasurableSet.iUnion fun n => measurableSet_restrict (K n) (K.finite n) A

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_MonotoneIndicatorUpper
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma monotone_indicator_upper (A : Set (Set E)) (hA : IsUpperSet A) :
    Monotone (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  intro ω ω' h
  change (if {e | ω e} ∈ A then (1 : ℝ) else 0) ≤
    (if {e | ω' e} ∈ A then (1 : ℝ) else 0)
  split_ifs with ha hb
  · rfl
  · exact (hb (hA h ha)).elim
  · norm_num
  · rfl

lemma real_eq_expect_indicator [Fintype E] (q : E → unitInterval) (A : Set (Set E)) :
    (law q).real A = FiniteProduct.expect (fun e => bitWeight (q e))
      (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  rw [← integral_law_eq_expect]
  exact (integral_indicator_one (.of_discrete)).symm

lemma finite_harris [Fintype E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law q).real A * (law q).real B ≤ (law q).real (A ∩ B) := by
  simp_rw [real_eq_expect_indicator]
  have he : (fun ω : E → Prop => (A ∩ B).indicator (1 : Set E → ℝ) {e | ω e}) =
      (fun ω => A.indicator (1 : Set E → ℝ) {e | ω e} *
        B.indicator (1 : Set E → ℝ) {e | ω e}) := by
    funext ω
    by_cases ha : {e | ω e} ∈ A <;> by_cases hb : {e | ω e} ∈ B <;> simp [ha, hb]
  rw [he]
  exact FiniteProduct.expect_mul_ge _ (fun e => bitWeight_sum (q e))
    (fun e b => bitWeight_nonneg (q e) b) _ _
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (monotone_indicator_upper A hA) (monotone_indicator_upper B hB)

lemma real_law_restrict_general (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (A : Set (Set E)) :
    (law q).real {ω | s ∩ ω ∈ A} =
      (law (fun e : s => q e)).real {ω | Subtype.val '' ω ∈ A} := by
  let := hs.fintype
  have hi (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
    ext e
    simp
  rw [← law_map_restrict q s]
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [Measure.real]
  rw [Measure.map_apply hf (.of_discrete)]
  simp only [Set.preimage_ofPred_eq, hi]

lemma finite_restriction_harris (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law q).real {ω | s ∩ ω ∈ A} * (law q).real {ω | s ∩ ω ∈ B} ≤
      (law q).real {ω | s ∩ ω ∈ A ∩ B} := by
  let := hs.fintype
  simp_rw [real_law_restrict_general _ s hs]
  exact finite_harris _ _ _ (fun _ _ h => hA (Set.image_mono h))
    (fun _ _ h => hB (Set.image_mono h))

lemma HasFiniteOpenWitness.inter {A B : Set (Set E)}
    (hA : HasFiniteOpenWitness A) (hB : HasFiniteOpenWitness B)
    (hAm : IsUpperSet A) (hBm : IsUpperSet B) : HasFiniteOpenWitness (A ∩ B) := by
  rintro ω ⟨hωA, hωB⟩
  obtain ⟨s, hs, hsω, hsA⟩ := hA ω hωA
  obtain ⟨t, ht, htω, htB⟩ := hB ω hωB
  exact ⟨s ∪ t, hs.union ht, Set.union_subset hsω htω,
    hAm Set.subset_union_left hsA, hBm Set.subset_union_right htB⟩

lemma tendsto_real_finiteWitness_general (q : E → unitInterval) (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law q).real {ω | K n ∩ ω ∈ A})
      atTop (𝓝 ((law q).real A)) := by
  have h := tendsto_measure_iUnion_atTop (μ := law q)
    (finiteWitness_exhaustion_mono A hmono K)
  rw [finiteWitness_exhaustion A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

theorem harris_finiteWitness [Countable E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : HasFiniteOpenWitness A) (hwB : HasFiniteOpenWitness B) :
    (law q).real A * (law q).real B ≤ (law q).real (A ∩ B) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  exact le_of_tendsto_of_tendsto
    ((tendsto_real_finiteWitness_general q A hA hwA K).mul
      (tendsto_real_finiteWitness_general q B hB hwB K))
    (tendsto_real_finiteWitness_general q (A ∩ B) (hA.inter hB)
      (hwA.inter hwB hA hB) K)
    (Eventually.of_forall fun n => finite_restriction_harris q (K n) (K.finite n) A B hA hB)

end CriticalPercolation.BernoulliProduct
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PhaseInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem criticalModel_openGraph (G : BondGraph V E) (ω : Set E) :
    (criticalModel G).openGraph ω = openSimpleGraph G ω := by
  ext x y
  simp only [CriticalPercolation.BondGraph.openGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_image, openSimpleGraph, criticalModel]
  tauto

theorem criticalModel_cluster (G : BondGraph V E) (ω : Set E) (x : V) :
    (criticalModel G).cluster ω x = cluster G ω x := by
  ext y
  simp only [CriticalPercolation.BondGraph.cluster, criticalModel_openGraph,
    Set.mem_ofPred_eq, cluster]
  exact (conn_iff_reachable G ω x y).symm

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_RelativeModular
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace Subgroup
open scoped _root_.Subgroup
variable {Γ : Type*} [Group Γ]

lemma relativeMass_self (A : Subgroup Γ) : relativeMass A A = 1 := by
  simp [relativeMass]

end Subgroup
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_GraphModular
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularRatio_self (x : V) : G.modularRatio x x = 1 := by
  rw [modularRatio_eq_relativeMass,Subgroup.relativeMass_self]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularClusterMass
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma stabilizerWeight_self (o : V) : G.stabilizerWeight o o = 1 := by
  simp [stabilizerWeight,modularRatio_self]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ModularSlabs
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma modularLogHeight_self (x : V) : G.modularLogHeight x x = 0 := by
  simp only [modularLogHeight,G.modularRatio_self,Real.log_one]

lemma modularLogHeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x v y : V) : G.modularLogHeight x y = G.modularLogHeight x v + G.modularLogHeight v y := by
  unfold modularLogHeight
  rw [← Real.log_mul (G.modularRatio_pos hc hl v x).ne' (G.modularRatio_pos hc hl y v).ne']
  congr 1
  rw [mul_comm,G.modularRatio_cocycle hc hl]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_OrbitHeightComparison
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma orbitAdjustedHeight_self (a : V → ℝ) (x : V) :
    G.orbitAdjustedHeight a x x = 0 := by simp [orbitAdjustedHeight]

lemma orbitAdjustedHeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (x v y : V) :
    G.orbitAdjustedHeight a x y = G.orbitAdjustedHeight a x v + G.orbitAdjustedHeight a v y := by
  simp only [orbitAdjustedHeight,G.modularLogHeight_change_base hc hl x v y]
  ring

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ClusterExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exactCluster_dependsOn (x : V) (S : Set V) :
    DependsOn (fun ω : Set E => G.cluster ω x = S) (G.incidentEdges S) := by
  intro ω η hω
  apply propext
  have hforward (ω η : Set E) (hωη : ∀ e ∈ G.incidentEdges S, e ∈ ω ↔ e ∈ η)
      (hS : G.cluster ω x = S) : G.cluster η x = S := by
    have hr : ClusterDeletion.roots (G.openGraph ω) {x} = S := by
      simpa only [ClusterDeletion.roots_singleton, ClusterDeletion.component, cluster] using hS
    have hr' := G.roots_eq_of_incident hr hωη
    simpa only [ClusterDeletion.roots_singleton, ClusterDeletion.component, cluster] using hr'
  exact ⟨hforward ω η (fun e he => (hω e he).to_iff),
    hforward η ω (fun e he => (hω e he).symm.to_iff)⟩

lemma measurableSet_exactCluster [Countable V] [Countable E] (x : V) (S : Set V) :
    MeasurableSet {ω | G.cluster ω x = S} := by
  have heq : {ω | G.cluster ω x = S} =
      ⋂ y : V, {ω | (G.openGraph ω).Reachable x y ↔ y ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Set.ext_iff
  rw [heq]
  exact MeasurableSet.iInter fun y => ((G.measurable_reachable x y).iff measurable_const).setOf

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProductEmbedding
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {A E : Type*}

lemma law_map_preimage (q : E → unitInterval) (i : A → E) (hi : Injective i) :
    (law q).map (fun ω : Set E => i ⁻¹' ω)=law (q∘i) := by
  have hind : iIndepFun (fun a (ω : Set E) => i a∈ω) (law q) :=
    iIndepFun.precomp hi (independent_coordinates q)
  have hh := hind.map_fun_eq_infinitePi_map (fun a => measurable_set_mem (i a))
  change (law q).map (fun ω : Set E => i ⁻¹' ω)=_ at hh
  rw [hh]
  rw [law_eq_infinitePi (q∘i)]
  apply congrArg Measure.infinitePi
  funext a
  rw [law_eq_infinitePi]
  exact Measure.infinitePi_map_eval _ (i a)

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_LayerFrontierGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem conn_last_exit_frontier (ω : Set E) (S : Set V) {x y : V}
    (hx : x ∈ S) (hy : y ∉ S) (hc : Conn G ω x y) :
    ∃ z ∈ openFrontier G ω S, Conn G (ω \ ballIncidentEdges G S) z y := by
  revert hy
  induction hc with
  | refl => exact fun hy => (hy hx).elim
  | @tail a b hxa hab ih =>
    intro hy
    obtain ⟨e,he,heq⟩ := hab
    by_cases ha : a ∈ S
    · exact ⟨b,⟨hy,a,ha,e,he,heq⟩,conn_refl G _ b⟩
    · obtain ⟨z,hz,hza⟩ := ih ha
      refine ⟨z,hz,hza.tail ⟨e,⟨he,?_⟩,heq⟩⟩
      rintro ⟨u,hu,hue⟩
      rw [heq,Sym2.mem_iff] at hue
      rcases hue with rfl | rfl
      · exact ha hu
      · exact hy hu

lemma measurable_restrictedLayerCount [Countable V] [Countable E]
    (I : Set E) (A : Set V) (x : V) : Measurable (fun ω => restrictedLayerCount G I A ω x) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact Measurable.tsum fun y => Measurable.ite
    (measurable_const.and ((measurableSet_conn G x y).mem.comp hm)).setOf
    measurable_const measurable_const

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_AvoidanceProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BernoulliProduct
variable {E ι : Type*} [Countable E]

lemma harris_finiteWitness_compl (q : E → unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : HasFiniteOpenWitness A) (hwB : HasFiniteOpenWitness B) :
    (law q).real Aᶜ*(law q).real Bᶜ ≤ (law q).real (Aᶜ ∩ Bᶜ) := by
  have hmA := measurableSet_finiteWitness A hA hwA
  have hmB := measurableSet_finiteWitness B hB hwB
  have hh := harris_finiteWitness q A B hA hB hwA hwB
  have hu := measureReal_union_add_inter (μ := law q) (s := A) hmB
    (measure_ne_top _ _) (measure_ne_top _ _)
  rw [measureReal_compl hmA,measureReal_compl hmB,←Set.compl_union,
    measureReal_compl (hmA.union hmB),probReal_univ]
  nlinarith

omit [Countable E] in
lemma finiteBadUnion_upper (F : Finset ι) (A : ι → Set (Set E))
    (hA : ∀ i ∈ F, IsUpperSet (A i)) : IsUpperSet (finiteBadUnion F A) := by
  rintro ω η hωη ⟨i,hi,hω⟩
  exact ⟨i,hi,hA i hi hωη hω⟩

omit [Countable E] in
lemma finiteBadUnion_finiteWitness (F : Finset ι) (A : ι → Set (Set E))
    (hw : ∀ i ∈ F, HasFiniteOpenWitness (A i)) : HasFiniteOpenWitness (finiteBadUnion F A) := by
  rintro ω ⟨i,hi,hω⟩
  obtain ⟨S,hS,hSω,hSA⟩ := hw i hi ω hω
  exact ⟨S,hS,hSω,i,hi,hSA⟩

theorem finite_avoidance_product (q : E → unitInterval) (F : Finset ι)
    (A : ι → Set (Set E)) (hA : ∀ i ∈ F, IsUpperSet (A i))
    (hw : ∀ i ∈ F, HasFiniteOpenWitness (A i)) :
    (∏ i ∈ F, (law q).real (A i)ᶜ) ≤ (law q).real (finiteBadUnion F A)ᶜ := by
  induction F using Finset.induction_on with
  | empty =>
    have he : finiteBadUnion (∅ : Finset ι) A=∅ := by ext ω; simp [finiteBadUnion]
    simp only [Finset.prod_empty,he,Set.compl_empty,probReal_univ,le_refl]
  | @insert i F hi ih =>
    have hAF : ∀ j ∈ F, IsUpperSet (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hwF : ∀ j ∈ F, HasFiniteOpenWitness (A j) := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hh := harris_finiteWitness_compl q (A i) (finiteBadUnion F A)
      (hA i (Finset.mem_insert_self _ _)) (finiteBadUnion_upper F A hAF)
        (hw i (Finset.mem_insert_self _ _)) (finiteBadUnion_finiteWitness F A hwF)
    have he : finiteBadUnion (insert i F) A=A i ∪ finiteBadUnion F A := by
      ext ω
      simp only [finiteBadUnion,Set.mem_ofPred_eq,Finset.mem_insert,Set.mem_union]
      aesop
    rw [Finset.prod_insert hi,he,Set.compl_union]
    exact (mul_le_mul_of_nonneg_left (ih hAF hwF) measureReal_nonneg).trans hh

theorem exponential_finite_avoidance (q : E → unitInterval) (F : Finset ι)
    (A : ι → Set (Set E)) (hA : ∀ i ∈ F, IsUpperSet (A i))
    (hw : ∀ i ∈ F, HasFiniteOpenWitness (A i)) (g : ι → ℝ)
    (hbound : ∀ i ∈ F, Real.exp (-g i) ≤ (law q).real (A i)ᶜ) :
    ENNReal.ofReal (Real.exp (-(∑ i ∈ F, g i))) ≤ law q (finiteBadUnion F A)ᶜ := by
  apply ENNReal.ofReal_le_of_le_toReal
  calc
    _ = ∏ i ∈ F, Real.exp (-g i) := by rw [←Real.exp_sum,Finset.sum_neg_distrib]
    _ ≤ ∏ i ∈ F, (law q).real (A i)ᶜ :=
      Finset.prod_le_prod (fun i _ => (Real.exp_pos (-g i)).le) hbound
    _ ≤ _ := finite_avoidance_product q F A hA hw

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_NormalizedLayerTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitAdjustedHeight_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (x y : V) :
    G.orbitAdjustedHeight a y x = -G.orbitAdjustedHeight a x y := by
  have hh := G.orbitAdjustedHeight_change_base hc hl a x y x
  rw [G.orbitAdjustedHeight_self] at hh
  linarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ConsistentLayers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

@[simp] lemma adjustedLayerIndex_self (a : V → ℝ) (R u : ℝ) (x : V) :
    G.adjustedLayerIndex a R u x x=0 := by simp [adjustedLayerIndex]

lemma adjustedLayerIndex_height_bounds (a : V → ℝ) (R u : ℝ) (hR : 0 < R) (x y : V) :
    R*((G.adjustedLayerIndex a R u x y : ℝ)-1) < G.orbitAdjustedHeight a x y ∧
      G.orbitAdjustedHeight a x y < R*((G.adjustedLayerIndex a R u x y : ℝ)+1) := by
  have h₁ := Int.floor_le (G.orbitAdjustedHeight a x y/R+u)
  have h₂ := Int.lt_floor_add_one (G.orbitAdjustedHeight a x y/R+u)
  have h₃ := Int.floor_le u
  have h₄ := Int.lt_floor_add_one u
  have he : (G.adjustedLayerIndex a R u x y : ℝ) =
      (⌊G.orbitAdjustedHeight a x y/R+u⌋ : ℝ)-(⌊u⌋ : ℝ) := by
    simp only [adjustedLayerIndex,Int.cast_sub]
  rw [he]
  constructor
  · have hh : (⌊G.orbitAdjustedHeight a x y/R+u⌋ : ℝ)-(⌊u⌋ : ℝ)-1 <
        G.orbitAdjustedHeight a x y/R := by linarith
    have hm := (lt_div_iff₀ hR).mp hh
    nlinarith
  · have hh : G.orbitAdjustedHeight a x y/R <
        (⌊G.orbitAdjustedHeight a x y/R+u⌋ : ℝ)-(⌊u⌋ : ℝ)+1 := by linarith
    have hm := (div_lt_iff₀ hR).mp hh
    nlinarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PairedSprinkling
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_whiteProjection : Measurable (whiteProjection (E := E)) :=
  Measurable.of_eval fun e => measurable_set_mem (e,true)

lemma measurable_pairedUnion : Measurable (pairedUnion (E := E)) :=
  Measurable.of_eval fun e => (Measurable.of_discrete :
    Measurable (fun f : Bool → Prop => ∃ j, f j)).comp
      (Measurable.of_eval fun j => measurable_set_mem (e,j))

lemma pairedUnion_eq (ω : Set (E × Bool)) :
    pairedUnion ω=whiteProjection ω ∪ blueProjection ω := by
  ext e
  simp [pairedUnion,whiteProjection,blueProjection,Bool.exists_bool,or_comm]

lemma paired_white_law (q b : E → unitInterval) :
    (law (pairedParameters q b)).map whiteProjection=law q := by
  change (law (pairedParameters q b)).map (fun ω => (fun e => (e,true)) ⁻¹' ω)=law q
  simpa [whiteProjection,pairedParameters,Percolation.pairParameter,
    Function.comp_def] using law_map_preimage (pairedParameters q b)
      (fun e => (e,true)) (fun _ _ h => congrArg Prod.fst h)

lemma paired_union_law (q b : E → unitInterval) :
    (law (pairedParameters q b)).map pairedUnion=
      law (fun e => Percolation.sprinkleParameter (q e) (b e)) := by
  simp only [law_eq_infinitePi]
  change (Measure.infinitePi (fun z : E × Bool => bitMeasure (pairedParameters q b z))).map
    (fun ω : E × Bool → Prop => fun e => ∃ j, ω (e,j))=
      Measure.infinitePi (fun e => bitMeasure (Percolation.sprinkleParameter (q e) (b e)))
  let c := MeasurableEquiv.curry E Bool Prop
  let f := fun g : E → Bool → Prop => fun e => ∃ j, g e j
  have hf : Measurable f := Measurable.of_eval fun e =>
    (Measurable.of_discrete : Measurable (fun g : Bool → Prop => ∃ j, g j)).comp
      (measurable_pi_apply e)
  change (Measure.infinitePi (fun z : E × Bool => bitMeasure (pairedParameters q b z))).map (f ∘ c)=_
  rw [←Measure.map_map hf c.measurable]
  rw [Measure.infinitePi_map_curry (fun e j => bitMeasure (pairedParameters q b (e,j)))]
  rw [Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  congr 1
  funext e
  exact Percolation.map_bool_or (q e) (b e)

lemma pinned_white_parameters (q b : E → unitInterval) (Q : Set E) :
    pinnedParameters (pairedParameters q b) (whiteBlock Q) ∅=
      pairedParameters (erasedWhiteParameters q Q) b := by
  funext z
  rcases z with ⟨e,j⟩
  cases j <;> by_cases he : e ∈ Q <;>
    simp [pinnedParameters,pairedParameters,Percolation.pairParameter,
      whiteBlock,erasedWhiteParameters,he]

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SprinklingPeakGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma conn_last_exit_off_internal (ω : Set E) (S : Set V) {x y : V}
    (hx : x ∈ S) (hy : y ∉ S) (hc : Conn G ω x y) :
    ∃ u ∈ S, Conn G (ω \ internalEdges G S) u y := by
  obtain ⟨z,⟨hz,u,hu,e,he,heq⟩,hzy⟩ := conn_last_exit_frontier G ω S hx hy hc
  have heI : e ∉ internalEdges G S := fun h => hz (h z (by rw [heq]; simp))
  have huz : Conn G (ω \ internalEdges G S) u z :=
    Relation.ReflTransGen.single ⟨e,⟨he,heI⟩,heq⟩
  refine ⟨u,hu,huz.trans (conn_mono G ?_ hzy)⟩
  intro b hb
  refine ⟨hb.1,fun hI => hb.2 ?_⟩
  exact ⟨(G b).out.1,hI _ (Sym2.out_fst_mem _),Sym2.out_fst_mem _⟩

lemma union_strict_peak_of_exterior_avoidance (white blue : Set E) (f : V → ℝ) (x : V)
    (hpeak : ∀ y, Conn G white x y → y ≠ x → f y < f x)
    (havoid : ∀ u ∈ cluster G white x,
      ¬∃ y, y ≠ x ∧ f x ≤ f y ∧ y ∉ cluster G white x ∧
        Conn G ((white ∪ blue) \ internalEdges G (cluster G white x)) u y) :
    ∀ y, Conn G (white ∪ blue) x y → y ≠ x → f y < f x := by
  intro y hxy hyx
  by_contra! hle
  have hyS : y ∉ cluster G white x := fun hy => (hpeak y hy hyx).not_ge hle
  obtain ⟨u,hu,huy⟩ := conn_last_exit_off_internal G (white ∪ blue) (cluster G white x)
    (mem_cluster_self G white x) hyS hxy
  exact havoid u hu ⟨y,hyx,hle,hyS,huy⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FreshWhiteExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma fresh_white_union_inter_factor (q b : E → unitInterval) (Q : Set E)
    (A B : Set (Set (E × Bool))) (hA : MeasurableSet A)
    (hdep : DependsOn (fun ω => ω ∈ A) (whiteBlock Q)) (hB : MeasurableSet B) :
    law (pairedParameters q b) (A ∩ forceOn (whiteBlock Q) ∅ ⁻¹' B)=
      law (pairedParameters q b) A *
        law (pairedParameters (erasedWhiteParameters q Q) b) B := by
  let g := fun ω => B.indicator (fun _ => (1 : ℝ≥0∞)) (forceOn (whiteBlock Q) ∅ ω)
  have hg : Measurable g := (measurable_const.indicator hB).comp (measurable_forceOn _ _)
  have hgd : DependsOn g (whiteBlock Q)ᶜ := by
    intro ω η hωη
    have hh : forceOn (whiteBlock Q) ∅ ω=forceOn (whiteBlock Q) ∅ η := by
      ext z
      change (if z ∈ whiteBlock Q then False else ω z) ↔
        (if z ∈ whiteBlock Q then False else η z)
      by_cases hz : z ∈ whiteBlock Q
      · simp only [ite_eq_left hz]
      · simpa only [ite_eq_right hz] using (hωη z hz).to_iff
    exact congrArg (B.indicator (fun _ => (1 : ℝ≥0∞))) hh
  have hi := lintegral_indicator_fresh (pairedParameters q b) (whiteBlock Q) A hA hdep g hg hgd
  have he : A.indicator g=(A ∩ forceOn (whiteBlock Q) ∅ ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases ha : ω ∈ A <;> by_cases hb : forceOn (whiteBlock Q) ∅ ω ∈ B <;>
      simp [Set.indicator,g,ha,hb]
  have hmB := hB.preimage (measurable_forceOn (whiteBlock Q) ∅)
  rw [he,lintegral_indicator_fun_one (hA.inter hmB)] at hi
  have hgint : (∫⁻ ω, g ω ∂law (pairedParameters q b))=
      law (pairedParameters (erasedWhiteParameters q Q) b) B := by
    change (∫⁻ ω, (forceOn (whiteBlock Q) ∅ ⁻¹' B).indicator
      (fun _ => (1 : ℝ≥0∞)) ω ∂law (pairedParameters q b))=_
    rw [lintegral_indicator_fun_one hmB,←Measure.map_apply (measurable_forceOn _ _) hB,
      forceOn_map_law,pinned_white_parameters]
  rwa [hgint] at hi

lemma fresh_white_union_event_factor (q b : E → unitInterval) (Q : Set E)
    (A : Set (Set (E × Bool))) (hA : MeasurableSet A)
    (hdep : DependsOn (fun ω => ω ∈ A) (whiteBlock Q))
    (B : Set (Set E)) (hB : MeasurableSet B) :
    law (pairedParameters q b)
      (A ∩ (pairedUnion ∘ forceOn (whiteBlock Q) ∅) ⁻¹' B)=
      law (pairedParameters q b) A *
        law (fun e => Percolation.sprinkleParameter (erasedWhiteParameters q Q e) (b e)) B := by
  rw [show (pairedUnion ∘ forceOn (whiteBlock Q) ∅) ⁻¹' B=
    forceOn (whiteBlock Q) ∅ ⁻¹' (pairedUnion ⁻¹' B) from rfl]
  rw [fresh_white_union_inter_factor q b Q A _ hA hdep (hB.preimage measurable_pairedUnion),
    ←Measure.map_apply measurable_pairedUnion hB,paired_union_law]

lemma erased_pairedUnion (Q : Set E) (ω : Set (E × Bool)) :
    pairedUnion (forceOn (whiteBlock Q) ∅ ω)=
      (whiteProjection ω \ Q) ∪ blueProjection ω := by
  ext e
  by_cases he : e ∈ Q <;>
    simp [pairedUnion,whiteBlock,whiteProjection,blueProjection,
      Bool.exists_bool,he,and_comm,or_comm]

end CriticalPercolation.BernoulliProduct

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_eq_percolationCluster (ω : Set E) (x : V) :
    G.cluster ω x=Percolation.cluster G.ends ω x := criticalModel_cluster G.ends ω x

lemma paired_exactWhiteCluster_dependsOn (x : V) (S : Set V) :
    DependsOn (fun ω : Set (E × Bool) => G.cluster (whiteProjection ω) x=S)
      (whiteBlock (G.incidentEdges S)) := by
  intro ω η hωη
  apply G.exactCluster_dependsOn x S
  intro e he
  exact hωη (e,true) ⟨he,rfl⟩

lemma white_edge_incident_cluster_internal (white : Set E) (x : V) (e : E)
    (he : e ∈ white) (hI : e ∈ G.incidentEdges (G.cluster white x)) :
    e ∈ Percolation.internalEdges G.ends (G.cluster white x) := by
  have hS : G.cluster white x=Percolation.cluster G.ends white x := criticalModel_cluster G.ends white x
  rw [hS] at hI ⊢
  obtain ⟨v,hv,hve⟩ := hI
  intro w hw
  by_cases h : v=w
  · simpa only [←h] using hv
  · have heq : G.ends e=s(v,w) := (Sym2.mem_and_mem_iff h).mp ⟨hve,hw⟩
    exact hv.trans (Relation.ReflTransGen.single ⟨e,he,heq⟩)

lemma erasedWhiteCluster_exterior_eq (ω : Set (E × Bool)) (x : V) :
    pairedUnion (forceOn (whiteBlock (G.incidentEdges (G.cluster (whiteProjection ω) x))) ∅ ω) \
        Percolation.internalEdges G.ends (G.cluster (whiteProjection ω) x)=
      pairedUnion ω \ Percolation.internalEdges G.ends (G.cluster (whiteProjection ω) x) := by
  rw [erased_pairedUnion,pairedUnion_eq]
  ext e
  constructor
  · rintro ⟨(⟨hew,_⟩ | heb),heI⟩
    · exact ⟨Or.inl hew,heI⟩
    · exact ⟨Or.inr heb,heI⟩
  · rintro ⟨(hew | heb),heI⟩
    · exact ⟨Or.inl ⟨hew,fun hQ => heI (G.white_edge_incident_cluster_internal _ x e hew hQ)⟩,heI⟩
    · exact ⟨Or.inr heb,heI⟩

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ExteriorEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma exteriorEscape_upper (S : Set V) (f : V → ℝ) (x u : V) :
    IsUpperSet (exteriorEscape G S f x u) := by
  rintro ω η hωη ⟨y,hy,hf,hyS,huy⟩
  exact ⟨y,hy,hf,hyS,conn_mono G (Set.sdiff_subset_sdiff_left hωη) huy⟩

lemma exteriorEscape_hasFiniteOpenWitness (S : Set V) (f : V → ℝ) (x u : V) :
    CriticalPercolation.BernoulliProduct.HasFiniteOpenWitness (exteriorEscape G S f x u) := by
  rintro ω ⟨y,hy,hf,hyS,huy⟩
  obtain ⟨F,hF,hconn⟩ := finiteWitness_conn G u y _ huy
  refine ⟨F,F.finite_toSet,fun e he => (hF he).1,y,hy,hf,hyS,conn_mono G ?_ hconn⟩
  intro e he
  exact ⟨he,(hF he).2⟩

lemma measurableSet_exteriorEscape [Countable E] (S : Set V) (f : V → ℝ) (x u : V) :
    MeasurableSet (exteriorEscape G S f x u) :=
  CriticalPercolation.BernoulliProduct.measurableSet_finiteWitness _
    (exteriorEscape_upper G S f x u) (exteriorEscape_hasFiniteOpenWitness G S f x u)

end Percolation.BenjaminiSchramm

namespace Percolation.BenjaminiSchramm
open CriticalPercolation.BernoulliProduct
variable {V E : Type*} [Countable E] (G : BondGraph V E)

theorem exteriorEscape_avoidance_product (r : E → unitInterval)
    (S : Finset V) (f : V → ℝ) (x : V) (g : V → ℝ)
    (hbound : ∀ u ∈ S, Real.exp (-g u) ≤
      (CriticalPercolation.BernoulliProduct.law r).real (exteriorEscape G (S : Set V) f x u)ᶜ) :
    ENNReal.ofReal (Real.exp (-(∑ u ∈ S, g u))) ≤
      CriticalPercolation.BernoulliProduct.law r {η | ∀ u ∈ S, η ∉ exteriorEscape G (S : Set V) f x u} := by
  have he : (finiteBadUnion S (fun u => exteriorEscape G (S : Set V) f x u))ᶜ=
      {η | ∀ u ∈ S, η ∉ exteriorEscape G (S : Set V) f x u} := by
    ext η
    simp [finiteBadUnion]
  rw [←he]
  exact exponential_finite_avoidance r S _
    (fun u _ => exteriorEscape_upper G _ f x u)
    (fun u _ => exteriorEscape_hasFiniteOpenWitness G _ f x u) g hbound

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FreshSlabConcatenation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_restrictedHit [Countable V] [Countable E]
    (I : Set E) (x : V) (A : Set V) : MeasurableSet (restrictedHit G I x A) := by
  have hm : Measurable (fun ω : Set E => ω ∩ I) :=
    measurable_set_iff.mpr fun e => (measurable_set_mem e).and measurable_const
  exact (Measurable.exists fun y => measurable_const.and
    ((measurableSet_conn G x y).mem.comp hm)).setOf

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSurgeryProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_strictHeightPeakConnection [Countable V] [Countable E]
    (f : V → ℝ) (x z : V) : MeasurableSet (strictHeightPeakConnection G f x z) := by
  exact ((measurableSet_conn G x z).mem.and (Measurable.forall fun y =>
    (measurableSet_conn G z y).mem.imp (measurable_const.imp measurable_const))).setOf

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakBandTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

variable [Countable V] [Countable E]

lemma measurable_peakUpBandTransport (a : V → ℝ) (l u : ℝ) (y x : V) :
    Measurable (fun ω => G.peakUpBandTransport a l u ω y x) := by
  exact Measurable.ite (measurable_const.and (measurable_const.and
    (measurableSet_strictHeightPeakConnection G.ends _ y x).mem)).setOf
      measurable_const measurable_const

lemma measurable_peakDownBandCount (a : V → ℝ) (l u : ℝ) (x : V) :
    Measurable (fun ω => G.peakDownBandCount a l u ω x) :=
  Measurable.tsum fun y => G.measurable_peakUpBandTransport a l u y x

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakLayerCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma integer_downward_layer_cost {V : Type*} (f : V → ℤ) (P : V → Prop) (g : ℕ → ℝ≥0∞) :
    (∑' l : ℕ, g l*(∑' y, if f y= -(l : ℤ) ∧ P y then (1 : ℝ≥0∞) else 0))=
      ∑' y, if f y ≤ 0 ∧ P y then g (-f y).toNat else 0 := by
  simp_rw [←ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro y
  by_cases hP : P y
  · by_cases hf : f y ≤ 0
    · have hd : f y= -(((-f y).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (neg_nonneg.mpr hf)]
        ring
      rw [ite_eq_left ⟨hf,hP⟩,tsum_eq_single (-f y).toNat]
      · rw [ite_eq_left (show f y= -(((-f y).toNat : ℕ) : ℤ) ∧ P y from ⟨hd,hP⟩),mul_one]
      · intro l hl
        have hne : f y ≠ -(l : ℤ) := by
          intro hh
          have hcast : (((-f y).toNat : ℕ) : ℤ)=(l : ℤ) := by omega
          exact hl (Int.ofNat_inj.mp hcast).symm
        rw [ite_eq_right (fun h => hne h.1),mul_zero]
    · rw [ite_eq_right (fun h => hf h.1)]
      apply ENNReal.tsum_eq_zero.mpr
      intro l
      have hne : f y ≠ -(l : ℤ) := by omega
      rw [ite_eq_right (fun h => hne h.1),mul_zero]
  · rw [ite_eq_right (fun h => hP h.2)]
    apply ENNReal.tsum_eq_zero.mpr
    intro l
    rw [ite_eq_right (fun h => hP h.2),mul_zero]

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma downwardLayerCost_eq_vertex_sum (a : V → ℝ) (R : ℝ) (g : ℕ → ℝ) (ω : Set E) (x : V) :
    G.downwardLayerCost a R g ω x=
      ∑' y, if G.adjustedLayerIndex a R 0 x y ≤ 0 ∧ Percolation.Conn G.ends ω x y then
        ENNReal.ofReal (g (-G.adjustedLayerIndex a R 0 x y).toNat) else 0 := by
  unfold downwardLayerCost restrictedLayerCount
  calc
    _ = ∑' l : ℕ, ENNReal.ofReal (g l)*(∑' y, if G.adjustedLayerIndex a R 0 x y= -(l : ℤ) ∧
        Percolation.Conn G.ends ω x y then (1 : ℝ≥0∞) else 0) := by
      apply tsum_congr
      intro l
      apply congrArg (fun b => ENNReal.ofReal (g l)*b)
      apply tsum_congr
      intro y
      by_cases hh : G.adjustedLayerIndex a R 0 x y= -(l : ℤ) ∧ Percolation.Conn G.ends ω x y
      · have hh' : y ∈ {z | G.adjustedLayerIndex a R 0 x z= -(l : ℤ)} ∧ Percolation.Conn G.ends ω x y := hh
        simp only [Set.inter_univ]
        rw [ite_eq_left hh',ite_eq_left hh]
      · have hh' : ¬(y ∈ {z | G.adjustedLayerIndex a R 0 x z= -(l : ℤ)} ∧ Percolation.Conn G.ends ω x y) := hh
        simp only [Set.inter_univ]
        rw [ite_eq_right hh',ite_eq_right hh]
    _ = _ := integer_downward_layer_cost _ _ _

lemma downwardLayerCost_of_exact_cluster (a : V → ℝ) (R : ℝ) (g : ℕ → ℝ)
    (ω : Set E) (x : V) (S : Finset V) (hS : Percolation.cluster G.ends ω x=(S : Set V))
    (hbelow : ∀ y ∈ S, G.adjustedLayerIndex a R 0 x y ≤ 0) :
    G.downwardLayerCost a R g ω x=
      ∑ y ∈ S, ENNReal.ofReal (g (-G.adjustedLayerIndex a R 0 x y).toNat) := by
  rw [G.downwardLayerCost_eq_vertex_sum]
  rw [tsum_eq_sum (s := S)]
  · apply Finset.sum_congr rfl
    intro y hy
    have hxy : Percolation.Conn G.ends ω x y := by
      change y ∈ Percolation.cluster G.ends ω x
      rw [hS]
      exact hy
    exact ite_eq_left ⟨hbelow y hy,hxy⟩
  · intro y hy
    apply ite_eq_right
    intro hh
    have hys : y ∈ Percolation.cluster G.ends ω x := hh.2
    rw [hS] at hys
    exact hy hys

variable [Countable V] [Countable E]

lemma measurable_downwardLayerCost (a : V → ℝ) (R : ℝ) (g : ℕ → ℝ) (x : V) :
    Measurable (fun ω => G.downwardLayerCost a R g ω x) :=
  Measurable.tsum fun _l => measurable_const.mul (measurable_restrictedLayerCount G.ends _ _ x)

theorem peakSurvivalCostMoment_eq (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (g : ℕ → ℝ) (n : ℕ) :
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => G.downwardLayerCost a R g η x) ω ∂G.law p))=
      ∑' l, ENNReal.ofReal (g l)*G.peakSurvivalLayerMoment O a R p n l := by
  have he (x : V) :
      (fun ω => {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => G.downwardLayerCost a R g η x) ω)=
      (fun ω => ∑' l, ENNReal.ofReal (g l)*
        {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
          (fun η => restrictedLayerCount G.ends Set.univ
            {y | G.adjustedLayerIndex a R 0 x y= -(l : ℤ)} η x) ω) := by
    funext ω
    by_cases hω : ω ∈ {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}
    · simp only [Set.indicator_of_mem hω,downwardLayerCost]
    · simp only [Set.indicator_of_notMem hω,mul_zero,tsum_zero]
  have hroot (x : V) :
      (∫⁻ ω, {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => G.downwardLayerCost a R g η x) ω ∂G.law p)=
      ∑' l, ENNReal.ofReal (g l)*(∫⁻ ω,
        {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
          (fun η => restrictedLayerCount G.ends Set.univ
            {y | G.adjustedLayerIndex a R 0 x y= -(l : ℤ)} η x) ω ∂G.law p) := by
    have hmA : MeasurableSet {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x} :=
      measurableSet_lt measurable_const (G.measurable_peakDownBandCount a _ _ x)
    rw [he]
    rw [lintegral_tsum (f := fun j ω => ENNReal.ofReal (g j)*
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y= -(j : ℤ)} η x) ω)
      (fun j => (measurable_const.mul
        ((measurable_restrictedLayerCount G.ends Set.univ
          {y | G.adjustedLayerIndex a R 0 x y= -(j : ℤ)} x).indicator hmA)).aemeasurable)]
    apply tsum_congr
    intro l
    exact lintegral_const_mul _ ((measurable_restrictedLayerCount G.ends Set.univ
      {y | G.adjustedLayerIndex a R 0 x y= -(l : ℤ)} x).indicator hmA)
  simp_rw [hroot,←ENNReal.tsum_mul_left]
  rw [←Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro l
  unfold peakSurvivalLayerMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSprinklingCost
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Finset
open scoped Topology BigOperators

namespace Percolation.BenjaminiSchramm

lemma geometric_continuation_cost_bound (g : ℕ → ℝ) (C q : ℝ)
    (hg : ∀ l, 0 ≤ g l) (_hC : 0 ≤ C) (hb : ∀ l, g l ≤ C)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    Summable (fun l => g l*q^(l-n)) ∧
      0 ≤ (∑' l, g l*q^(l-n)) ∧
      (∑' l, g l*q^(l-n)) ≤ (∑ l ∈ range n, g l)+C*(1-q)⁻¹ := by
  have hsgeom := summable_geometric_of_lt_one hq0 hq1
  have htail : Summable (fun k => g (k+n)*q^k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hg _) (pow_nonneg hq0 _))
      (fun k => mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hq0 _)) (hsgeom.mul_left C)
  have hs : Summable (fun l => g l*q^(l-n)) := by
    apply (summable_nat_add_iff n).mp
    simpa only [Nat.add_sub_cancel] using htail
  refine ⟨hs,tsum_nonneg (fun l => mul_nonneg (hg _) (pow_nonneg hq0 _)),?_⟩
  have hhead : (∑ l ∈ range n, g l*q^(l-n)) = ∑ l ∈ range n, g l := by
    apply sum_congr rfl
    intro l hl
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt (mem_range.mp hl)),pow_zero,mul_one]
  calc
    _ = (∑ l ∈ range n, g l*q^(l-n))+(∑' k, g (k+n)*q^k) := by
      simpa only [Nat.add_sub_cancel] using (hs.sum_add_tsum_nat_add n).symm
    _ ≤ (∑ l ∈ range n, g l)+∑' k, C*q^k := by
      rw [hhead]
      exact add_le_add le_rfl (htail.tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hq0 _))
        (hsgeom.mul_left C))
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hq0 hq1]

theorem geometric_continuation_cost_sublinear (g : ℕ → ℝ) (C q : ℝ)
    (hg : ∀ l, 0 ≤ g l) (hC : 0 ≤ C) (hb : ∀ l, g l ≤ C)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hlim : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (∑' l, g l*q^(l-n))/(n : ℝ)) atTop (𝓝 0) := by
  have hces : Tendsto (fun n : ℕ => (∑ l ∈ range n, g l)/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_comm] using hlim.cesaro
  have hconst : Tendsto (fun n : ℕ => (C*(1-q)⁻¹)/(n : ℝ)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n : ℕ =>
      ((∑ l ∈ range n, g l)+C*(1-q)⁻¹)/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [add_div,zero_add] using hces.add hconst
  apply squeeze_zero (fun n => div_nonneg
    (geometric_continuation_cost_bound g C q hg hC hb hq0 hq1 n).2.1 (Nat.cast_nonneg n))
    (fun n => div_le_div_of_nonneg_right
      (geometric_continuation_cost_bound g C q hg hC hb hq0 hq1 n).2.2 (Nat.cast_nonneg n)) hupper

lemma exponential_continuation_weight (a : ℝ) (l n : ℕ) :
    Real.exp (-a*max ((l : ℝ)-n) 0) = Real.exp (-a)^(l-n) := by
  by_cases hn : n ≤ l
  · rw [max_eq_left (sub_nonneg.mpr (Nat.cast_le.mpr hn)),←Real.exp_nat_mul,
      Nat.cast_sub hn]
    congr 1
    ring
  · have hln : l ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hn)
    rw [max_eq_right (sub_nonpos.mpr (Nat.cast_le.mpr hln)),mul_zero,Real.exp_zero,
      Nat.sub_eq_zero_of_le hln,pow_zero]

theorem exponential_continuation_cost_sublinear (g : ℕ → ℝ) (C a : ℝ)
    (hg : ∀ l, 0 ≤ g l) (hC : 0 ≤ C) (hb : ∀ l, g l ≤ C)
    (ha : 0 < a) (hlim : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∑' l, g l*Real.exp (-a*max ((l : ℝ)-n) 0))/(n : ℝ)) atTop (𝓝 0) := by
  simp_rw [exponential_continuation_weight]
  exact geometric_continuation_cost_sublinear g C (Real.exp (-a)) hg hC hb
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)) hlim

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakCostBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma exponential_continuation_cost_summable (g : ℕ → ℝ) (C a : ℝ)
    (hg : ∀ l, 0 ≤ g l) (hC : 0 ≤ C) (hb : ∀ l, g l ≤ C)
    (ha : 0 < a) (n : ℕ) :
    Summable (fun l => g l*Real.exp (-a*max ((l : ℝ)-n) 0)) := by
  simp_rw [exponential_continuation_weight]
  exact (geometric_continuation_cost_bound g C (Real.exp (-a)) hg hC hb
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)) n).1

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem peakSurvivalCostMoment_bound (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (hgb : ∀ l, g l ≤ C₀)
    (A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C) (n : ℕ)
    (hprofile : ∀ l : ℕ, G.peakSurvivalLayerMoment O a R p n l ≤
      G.peakSurvivalProbability O a R p n *
        ENNReal.ofReal (C*Real.exp (-A*max ((l : ℝ)-n) 0))) :
    (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω,
      {η | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) η x}.indicator
        (fun η => G.downwardLayerCost a R g η x) ω ∂G.law p)) ≤
      G.peakSurvivalProbability O a R p n *
        ENNReal.ofReal (C*(∑' l, g l*Real.exp (-A*max ((l : ℝ)-n) 0))) := by
  rw [G.peakSurvivalCostMoment_eq]
  let P := G.peakSurvivalProbability O a R p n
  let f : ℕ → ℝ := fun l => g l*Real.exp (-A*max ((l : ℝ)-n) 0)
  have hf : ∀ l, 0 ≤ f l := fun l => mul_nonneg (hg l) (Real.exp_nonneg _)
  have hs : Summable f := exponential_continuation_cost_summable g C₀ A hg hC₀ hgb hA n
  have he (l : ℕ) : ENNReal.ofReal (g l)*(P*ENNReal.ofReal
      (C*Real.exp (-A*max ((l : ℝ)-n) 0)))=(P*ENNReal.ofReal C)*ENNReal.ofReal (f l) := by
    rw [ENNReal.ofReal_mul hC,show f l=g l*Real.exp (-A*max ((l : ℝ)-n) 0) from rfl,
      ENNReal.ofReal_mul (hg l)]
    ring
  calc
    _ ≤ ∑' l, ENNReal.ofReal (g l)*(P*ENNReal.ofReal
        (C*Real.exp (-A*max ((l : ℝ)-n) 0))) :=
      ENNReal.tsum_le_tsum fun l => mul_le_mul' le_rfl (hprofile l)
    _ = (P*ENNReal.ofReal C)*(∑' l, ENNReal.ofReal (f l)) := by
      simp_rw [he]
      exact ENNReal.tsum_mul_left
    _ = _ := by
      rw [←ENNReal.ofReal_tsum_of_nonneg hf hs,mul_assoc,←ENNReal.ofReal_mul hC]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakOrbitComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurableSet_fullPeakDownHit (a : V → ℝ) (ell : ℝ) (x : V) :
    MeasurableSet (G.fullPeakDownHit a ell x) :=
  (measurableSet_strictHeightPeakConnection G.ends _ x x).inter
    (measurableSet_restrictedHit G.ends Set.univ x _)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSurvivalRealHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma positive_peakDownBandCount_subset_fullPeakDownHit
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (a : V → ℝ)
    (l u ell : ℝ) (hell : ell ≤ l) (x : V) :
    {ω | 0 < G.peakDownBandCount a l u ω x} ⊆ G.fullPeakDownHit a ell x := by
  intro ω hω
  change 0 < G.peakDownBandCount a l u ω x at hω
  have he : ∃ y, l < G.orbitAdjustedHeight a y x ∧ G.orbitAdjustedHeight a y x ≤ u ∧
      ω ∈ strictHeightPeakConnection G.ends (G.orbitAdjustedHeight a y) y x := by
    by_contra hn
    have hz : G.peakDownBandCount a l u ω x=0 := ENNReal.tsum_eq_zero.mpr fun y =>
      ite_eq_right (fun hy => hn ⟨y,hy⟩)
    rw [hz] at hω
    exact lt_irrefl _ hω
  obtain ⟨y,hylo,_hyhi,hxy,hpeak⟩ := he
  refine ⟨⟨Percolation.conn_refl G.ends ω x,?_⟩,y,?_,?_⟩
  · intro z hxz hzx
    have hz := hpeak z hxz hzx
    rw [G.orbitAdjustedHeight_change_base hc hl a y x z] at hz
    rw [G.orbitAdjustedHeight_self]
    linarith
  · change G.orbitAdjustedHeight a x y ≤ -ell
    rw [G.orbitAdjustedHeight_reverse hc hl a x y] at hylo
    linarith
  · simpa only [Set.inter_univ] using Percolation.conn_symm G.ends ω hxy

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSprinklingCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_exteriorAvoidance [Countable V] [Countable E]
    (S : Set V) (a : V → ℝ) (x : V) : MeasurableSet (G.exteriorAvoidance S a x) :=
  (Measurable.forall fun u => measurable_const.imp
    (measurableSet_exteriorEscape G.ends S (G.orbitAdjustedHeight a x) x u).compl.mem).setOf

lemma fullPeakDownHit_iff_cluster_property (a : V → ℝ) (ell : ℝ) (x : V) (ω : Set E) :
    ω ∈ G.fullPeakDownHit a ell x ↔ G.peakDownClusterProperty a ell x (G.cluster ω x) := by
  rw [G.cluster_eq_percolationCluster]
  constructor
  · rintro ⟨⟨_,hpeak⟩,y,hy,hxy⟩
    refine ⟨fun z hz hzx => ?_,y,?_,hy⟩
    · simpa only [G.orbitAdjustedHeight_self] using hpeak z hz hzx
    · simpa only [Percolation.cluster,Set.mem_ofPred_eq,Set.inter_univ] using hxy
  · rintro ⟨hpeak,y,hxy,hy⟩
    refine ⟨⟨Percolation.conn_refl G.ends ω x,?_⟩,y,hy,?_⟩
    · intro z hz hzx
      simpa only [G.orbitAdjustedHeight_self] using hpeak z hz hzx
    · simpa only [Percolation.cluster,Set.mem_ofPred_eq,Set.inter_univ] using hxy

lemma peak_survives_white_cell (a : V → ℝ) (ell : ℝ) (x : V) (S : Set V)
    (hprop : G.peakDownClusterProperty a ell x S) (ω : Set (E × Bool))
    (hS : G.cluster (whiteProjection ω) x=S)
    (havoid : pairedUnion (forceOn (whiteBlock (G.incidentEdges S)) ∅ ω) ∈ G.exteriorAvoidance S a x) :
    pairedUnion ω ∈ G.fullPeakDownHit a ell x := by
  have hwhite : whiteProjection ω ∈ G.fullPeakDownHit a ell x :=
    (G.fullPeakDownHit_iff_cluster_property a ell x _).mpr (hS ▸ hprop)
  have hSc : Percolation.cluster G.ends (whiteProjection ω) x=S := by
    rwa [←G.cluster_eq_percolationCluster]
  have hη : pairedUnion (forceOn (whiteBlock (G.incidentEdges S)) ∅ ω) \
      Percolation.internalEdges G.ends S=pairedUnion ω \ Percolation.internalEdges G.ends S := by
    have hh := G.erasedWhiteCluster_exterior_eq ω x
    rwa [hS] at hh
  have hpeak : ∀ y, Percolation.Conn G.ends (pairedUnion ω) x y → y ≠ x →
      G.orbitAdjustedHeight a x y < G.orbitAdjustedHeight a x x := by
    rw [pairedUnion_eq]
    apply union_strict_peak_of_exterior_avoidance G.ends (whiteProjection ω) (blueProjection ω)
      (G.orbitAdjustedHeight a x) x hwhite.1.2
    intro u hu hescape
    have huS : u ∈ S := hSc ▸ hu
    apply havoid u huS
    rcases hescape with ⟨y,hy,hheight,hyS,hconn⟩
    refine ⟨y,hy,hheight,?_,?_⟩
    · rwa [hSc] at hyS
    · rw [hη,pairedUnion_eq,←hSc]
      exact hconn
  refine ⟨⟨Percolation.conn_refl G.ends _ x,hpeak⟩,?_⟩
  obtain ⟨y,hy,hxy⟩ := hwhite.2
  refine ⟨y,hy,?_⟩
  apply Percolation.conn_mono G.ends _ hxy
  intro e he
  exact ⟨(pairedUnion_eq ω).symm ▸ Or.inl he.1,he.2⟩

variable [Countable V] [Countable E]

theorem peak_sprinkling_cell_lower (q b : unitInterval) (a : V → ℝ)
    (x : V) (S : Finset V)
    (g : V → ℝ)
    (hbound : ∀ u ∈ S, Real.exp (-g u) ≤
      (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
        (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
          (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ) :
    G.law q {η | G.cluster η x=(S : Set V)} *
      ENNReal.ofReal (Real.exp (-(∑ u ∈ S, g u))) ≤
      BernoulliProduct.law (pairedParameters (fun _ => q) (fun _ => b))
        ({ω | G.cluster (whiteProjection ω) x=(S : Set V)} ∩
          (pairedUnion ∘ forceOn (whiteBlock (G.incidentEdges (S : Set V))) ∅) ⁻¹'
            G.exteriorAvoidance (S : Set V) a x) := by
  rw [fresh_white_union_event_factor (fun _ => q) (fun _ => b)
    (G.incidentEdges (S : Set V)) {ω | G.cluster (whiteProjection ω) x=(S : Set V)}
    ((G.measurableSet_exactCluster x _).preimage measurable_whiteProjection)
    (G.paired_exactWhiteCluster_dependsOn x _) (G.exteriorAvoidance (S : Set V) a x)
    (G.measurableSet_exteriorAvoidance _ a x)]
  have hcell : BernoulliProduct.law (pairedParameters (fun _ : E => q) (fun _ => b))
      {ω | G.cluster (whiteProjection ω) x=(S : Set V)}=
      G.law q {η | G.cluster η x=(S : Set V)} := by
    change BernoulliProduct.law (pairedParameters (fun _ : E => q) (fun _ => b))
      (whiteProjection ⁻¹' {η | G.cluster η x=(S : Set V)})=_
    rw [←Measure.map_apply measurable_whiteProjection (G.measurableSet_exactCluster x _),
      paired_white_law,BernoulliProduct.law_const]
    rfl
  rw [hcell]
  exact mul_le_mul' le_rfl (exteriorEscape_avoidance_product G.ends _ S
    (G.orbitAdjustedHeight a x) x g hbound)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_SprinklingAvoidanceProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma nonpositive_height_depth (a : V → ℝ) (R : ℝ) (hR : 0 < R) (x u : V)
    (hu : G.orbitAdjustedHeight a x u ≤ 0) :
    G.adjustedLayerIndex a R 0 x u ≤ 0 ∧
      R*(((-G.adjustedLayerIndex a R 0 x u).toNat-1 : ℕ) : ℝ) ≤
        -G.orbitAdjustedHeight a x u := by
  have hf : G.adjustedLayerIndex a R 0 x u ≤ 0 := by
    simpa only [adjustedLayerIndex,add_zero,Int.floor_zero,sub_zero] using
      (Int.floor_mono (div_nonpos_of_nonpos_of_nonneg hu hR.le))
  refine ⟨hf,?_⟩
  let n := (-G.adjustedLayerIndex a R 0 x u).toNat
  change R*((n-1 : ℕ) : ℝ) ≤ -G.orbitAdjustedHeight a x u
  by_cases hn : n=0
  · simpa only [hn,Nat.zero_sub,Nat.cast_zero,mul_zero] using neg_nonneg.mpr hu
  · have hn1 : 1 ≤ n := by omega
    have hd : (n : ℤ)= -G.adjustedLayerIndex a R 0 x u := Int.toNat_of_nonneg (neg_nonneg.mpr hf)
    have hheight := (G.adjustedLayerIndex_height_bounds a R 0 hR x u).2
    have he : (G.adjustedLayerIndex a R 0 x u : ℝ)= -(n : ℝ) := by exact_mod_cast (show G.adjustedLayerIndex a R 0 x u= -(n : ℤ) by omega)
    change G.orbitAdjustedHeight a x u < R*((G.adjustedLayerIndex a R 0 x u : ℝ)+1) at hheight
    rw [he] at hheight
    change R*((n-1 : ℕ) : ℝ) ≤ -G.orbitAdjustedHeight a x u
    rw [Nat.cast_sub hn1,Nat.cast_one]
    nlinarith

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSprinklingAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma exactCluster_partition_measure (p : unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite)
    (B : Set (Set E)) (hB : MeasurableSet B) :
    G.law p B=∑' S : Finset V, G.law p ({ω | G.cluster ω x=(S : Set V)} ∩ B) := by
  have hdis : Pairwise (fun S T : Finset V => Disjoint
      ({ω | G.cluster ω x=(S : Set V)} ∩ B) ({ω | G.cluster ω x=(T : Set V)} ∩ B)) := by
    intro S T hne
    apply Set.disjoint_left.mpr
    rintro ω ⟨hS,_⟩ ⟨hT,_⟩
    exact hne (Finset.coe_injective (hS.symm.trans hT))
  calc
    _ = G.law p (⋃ S : Finset V, {ω | G.cluster ω x=(S : Set V)} ∩ B) := by
      apply measure_congr
      filter_upwards [hfin] with ω hω
      apply propext
      constructor
      · intro hBω
        exact Set.mem_iUnion.mpr ⟨hω.toFinset,hω.coe_toFinset.symm,hBω⟩
      · intro hω'
        obtain ⟨S,_hS,hBω⟩ := Set.mem_iUnion.mp hω'
        exact hBω
    _ = _ := measure_iUnion hdis fun S => (G.measurableSet_exactCluster x _).inter hB

theorem peak_sprinkling_average (q b p : unitInterval)
    (hparam : Percolation.sprinkleParameter q b=p)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (ell : ℝ) (x : V)
    (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l) (t : ℝ) (ht : 0 ≤ t)
    (hfin : ∀ᵐ ω ∂G.law q, (G.cluster ω x).Finite)
    (havoid : ∀ (S : Finset V) (u : V), u ∈ S → G.orbitAdjustedHeight a x u ≤ 0 →
      Real.exp (-g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤
        (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
          (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
            (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ)
    (B : Set (Set E)) (hB : MeasurableSet B)
    (hBpeak : B ⊆ G.fullPeakDownHit a ell x)
    (hBcost : ∀ ω ∈ B, G.downwardLayerCost a R g ω x ≤ ENNReal.ofReal t) :
    G.law q B*ENNReal.ofReal (Real.exp (-t)) ≤ G.law p (G.fullPeakDownHit a ell x) := by
  let μ := BernoulliProduct.law (pairedParameters (fun _ : E => q) (fun _ => b))
  let C (S : Finset V) : Set (Set (E × Bool)) :=
    ({ω | G.cluster (whiteProjection ω) x=(S : Set V)} ∩
      (pairedUnion ∘ forceOn (whiteBlock (G.incidentEdges (S : Set V))) ∅) ⁻¹'
        G.exteriorAvoidance (S : Set V) a x) ∩ pairedUnion ⁻¹' G.fullPeakDownHit a ell x
  have hCm (S : Finset V) : MeasurableSet (C S) :=
    (((G.measurableSet_exactCluster x _).preimage measurable_whiteProjection).inter
      ((G.measurableSet_exteriorAvoidance _ a x).preimage
        (measurable_pairedUnion.comp (measurable_forceOn _ _)))).inter
      ((G.measurableSet_fullPeakDownHit a ell x).preimage measurable_pairedUnion)
  have hCdis : Pairwise (fun S T : Finset V => Disjoint (C S) (C T)) := by
    intro S T hne
    apply Set.disjoint_left.mpr
    rintro ω ⟨⟨hS,_⟩,_⟩ ⟨⟨hT,_⟩,_⟩
    exact hne (Finset.coe_injective (hS.symm.trans hT))
  have hlocal (S : Finset V) :
      G.law q ({ω | G.cluster ω x=(S : Set V)} ∩ B)*ENNReal.ofReal (Real.exp (-t)) ≤ μ (C S) := by
    by_cases he : ({ω | G.cluster ω x=(S : Set V)} ∩ B).Nonempty
    · obtain ⟨ω,hS,hBω⟩ := he
      have hprop : G.peakDownClusterProperty a ell x (S : Set V) := by
        have hh := (G.fullPeakDownHit_iff_cluster_property a ell x ω).mp (hBpeak hBω)
        rwa [hS] at hh
      have hbelow (u : V) (hu : u ∈ S) : G.orbitAdjustedHeight a x u ≤ 0 := by
        by_cases hux : u=x
        · simp only [hux,G.orbitAdjustedHeight_self,le_refl]
        · exact (hprop.1 u hu hux).le
      have hSc : Percolation.cluster G.ends ω x=(S : Set V) := by
        rwa [←G.cluster_eq_percolationCluster]
      have hcostreal : (∑ u ∈ S, g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤ t := by
        have hh := hBcost ω hBω
        rw [G.downwardLayerCost_of_exact_cluster a R g ω x S hSc
          (fun u hu => (G.nonpositive_height_depth a R hR x u (hbelow u hu)).1)] at hh
        rw [←ENNReal.ofReal_sum_of_nonneg (fun u _ => hg _)] at hh
        exact (ENNReal.ofReal_le_ofReal_iff ht).mp hh
      have hsubset :
          ({η | G.cluster (whiteProjection η) x=(S : Set V)} ∩
            (pairedUnion ∘ forceOn (whiteBlock (G.incidentEdges (S : Set V))) ∅) ⁻¹'
              G.exteriorAvoidance (S : Set V) a x) ⊆ pairedUnion ⁻¹' G.fullPeakDownHit a ell x := by
        rintro η ⟨hη,hηavoid⟩
        exact G.peak_survives_white_cell a ell x _ hprop η hη hηavoid
      have hCeq : C S=
          {η | G.cluster (whiteProjection η) x=(S : Set V)} ∩
            (pairedUnion ∘ forceOn (whiteBlock (G.incidentEdges (S : Set V))) ∅) ⁻¹'
              G.exteriorAvoidance (S : Set V) a x := Set.inter_eq_left.mpr hsubset
      rw [hCeq]
      calc
        _ ≤ G.law q {η | G.cluster η x=(S : Set V)}*
            ENNReal.ofReal (Real.exp (-(∑ u ∈ S, g (-G.adjustedLayerIndex a R 0 x u).toNat))) := by
          apply mul_le_mul' (measure_mono Set.inter_subset_left)
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hcostreal))
        _ ≤ _ := G.peak_sprinkling_cell_lower q b a x S
          (fun u => g (-G.adjustedLayerIndex a R 0 x u).toNat)
          (fun u hu => havoid S u hu (hbelow u hu))
    · rw [Set.not_nonempty_iff_eq_empty.mp he,measure_empty,zero_mul]
      exact bot_le
  calc
    _ = ∑' S : Finset V, G.law q ({ω | G.cluster ω x=(S : Set V)} ∩ B)*
        ENNReal.ofReal (Real.exp (-t)) := by
      rw [G.exactCluster_partition_measure q x hfin B hB,←ENNReal.tsum_mul_right]
    _ ≤ ∑' S : Finset V, μ (C S) := ENNReal.tsum_le_tsum hlocal
    _ = μ (⋃ S : Finset V, C S) := (measure_iUnion hCdis hCm).symm
    _ ≤ μ (pairedUnion ⁻¹' G.fullPeakDownHit a ell x) := measure_mono
      (Set.iUnion_subset fun S _ h => h.2)
    _ = _ := by
      rw [←Measure.map_apply measurable_pairedUnion (G.measurableSet_fullPeakDownHit a ell x)]
      dsimp [μ]
      rw [paired_union_law,hparam,BernoulliProduct.law_const]
      rfl

theorem weighted_peak_sprinkling_average (O : G.OrbitRepresentatives)
    (q b p : unitInterval) (hparam : Percolation.sprinkleParameter q b=p)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (ell : ℝ)
    (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l) (t : ℝ) (ht : 0 ≤ t)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law q, (G.cluster ω x).Finite)
    (havoid : ∀ (x : V) (S : Finset V) (u : V), u ∈ S → G.orbitAdjustedHeight a x u ≤ 0 →
      Real.exp (-g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤
        (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
          (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
            (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ)
    (B : V → Set (Set E)) (hB : ∀ x, MeasurableSet (B x))
    (hBpeak : ∀ x, B x ⊆ G.fullPeakDownHit a ell x)
    (hBcost : ∀ x ω, ω ∈ B x → G.downwardLayerCost a R g ω x ≤ ENNReal.ofReal t) :
    ENNReal.ofReal (Real.exp (-t))*(∑ x ∈ O.roots, ENNReal.ofReal (a x)*G.law q (B x)) ≤
      G.fullPeakDownProbability O a p ell := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  calc
    _ = ENNReal.ofReal (a x)*(G.law q (B x)*ENNReal.ofReal (Real.exp (-t))) := by ring
    _ ≤ _ := mul_le_mul' le_rfl (G.peak_sprinkling_average q b p hparam a R hR ell x
      g hg t ht (hfin x) (havoid x) (B x) (hB x) (hBpeak x) (hBcost x))

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_WeightedCostRetention
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators Topology

namespace Percolation.BenjaminiSchramm

lemma weighted_cost_retains_half {ι Ω : Type*} [MeasurableSpace Ω]
    (I : Finset ι) (μ : ι → Measure Ω) (w : ι → ℝ≥0∞)
    (A : ι → Set Ω) (hA : ∀ i ∈ I, MeasurableSet (A i))
    (Z : ι → Ω → ℝ≥0∞) (hZ : ∀ i ∈ I, Measurable (Z i))
    (t : ℝ) (ht : 0 < t)
    (hP : (∑ i ∈ I, w i*μ i (A i)) < ⊤)
    (hcost : (∑ i ∈ I, w i*(∫⁻ ω in A i, Z i ω ∂μ i)) ≤
      (∑ i ∈ I, w i*μ i (A i))*ENNReal.ofReal (t/2)) :
    (∑ i ∈ I, w i*μ i (A i))/2 ≤
      ∑ i ∈ I, w i*μ i (A i ∩ {ω | Z i ω ≤ ENNReal.ofReal t}) := by
  let P := ∑ i ∈ I, w i*μ i (A i)
  let B := ∑ i ∈ I, w i*μ i (A i ∩ {ω | ENNReal.ofReal t < Z i ω})
  let Q := ∑ i ∈ I, w i*μ i (A i ∩ {ω | Z i ω ≤ ENNReal.ofReal t})
  have hBQ : B ≤ P ∧ Q ≤ P := by
    constructor <;> apply Finset.sum_le_sum <;> intro i hi
    all_goals exact mul_le_mul' le_rfl (measure_mono Set.inter_subset_left)
  have hB : B ≠ ⊤ := ne_top_of_le_ne_top hP.ne hBQ.1
  have hQ : Q ≠ ⊤ := ne_top_of_le_ne_top hP.ne hBQ.2
  have hsum : Q+B=P := by
    dsimp [P,Q,B]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [←mul_add]
    congr 1
    have hmeas : MeasurableSet {ω | ENNReal.ofReal t < Z i ω} := (measurable_const.lt (hZ i hi)).setOf
    have hdis : Disjoint (A i ∩ {ω | Z i ω ≤ ENNReal.ofReal t})
        (A i ∩ {ω | ENNReal.ofReal t < Z i ω}) := by
      apply Set.disjoint_left.mpr
      intro ω hω hω'
      exact (not_lt_of_ge (show Z i ω ≤ ENNReal.ofReal t from hω.2)) hω'.2
    rw [←measure_union hdis ((hA i hi).inter hmeas)]
    congr 1
    ext ω
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_ofPred_eq]
    constructor
    · exact fun h => h.elim And.left And.left
    · intro h
      rcases le_or_gt (Z i ω) (ENNReal.ofReal t) with hh | hh
      · exact Or.inl ⟨h,hh⟩
      · exact Or.inr ⟨h,hh⟩
  have hmarkov : ENNReal.ofReal t*B ≤ P*ENNReal.ofReal (t/2) := by
    apply le_trans _ hcost
    dsimp [B]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    let S := A i ∩ {ω | ENNReal.ofReal t < Z i ω}
    have hm : MeasurableSet S := (hA i hi).inter (measurable_const.lt (hZ i hi)).setOf
    have hh : ENNReal.ofReal t*μ i S ≤ ∫⁻ ω in A i, Z i ω ∂μ i := by
      calc
        _ = ∫⁻ ω, ENNReal.ofReal t*S.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ i := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact congrArg (fun b => ENNReal.ofReal t*b) (lintegral_indicator_fun_one hm).symm
        _ ≤ ∫⁻ ω, (A i).indicator (Z i) ω ∂μ i := by
          apply lintegral_mono
          intro ω
          change ENNReal.ofReal t*S.indicator (fun _ => (1 : ℝ≥0∞)) ω ≤ (A i).indicator (Z i) ω
          by_cases hω : ω ∈ S
          · rw [Set.indicator_of_mem hω (fun _ => (1 : ℝ≥0∞)),Set.indicator_of_mem hω.1 (Z i),mul_one]
            exact hω.2.le
          · rw [Set.indicator_of_notMem hω (fun _ => (1 : ℝ≥0∞)),mul_zero]
            exact bot_le
        _ = _ := lintegral_indicator (hA i hi) (Z i)
    exact (show ENNReal.ofReal t*(w i*μ i S)=(w i)*(ENNReal.ofReal t*μ i S) by ac_rfl).le.trans
      (mul_le_mul' le_rfl hh)
  have hre := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hP.ne ENNReal.ofReal_ne_top) hmarkov
  rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal ht.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ t/2)] at hre
  have hb : B.toReal ≤ P.toReal/2 := by nlinarith
  have hsumreal : Q.toReal+B.toReal=P.toReal := by
    rw [←ENNReal.toReal_add hQ hB,hsum]
  change P/2 ≤ Q
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top hP.ne (by norm_num)) hQ).mp
  rw [ENNReal.toReal_div,ENNReal.toReal_ofNat]
  linarith

lemma sublinear_cost_eventually_small (F : ℕ → ℝ)
    (hF : Tendsto (fun n : ℕ => F n/(n : ℝ)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, F n ≤ ε*n := by
  filter_upwards [hF.eventually (gt_mem_nhds hε),eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ((div_lt_iff₀ hn0).mp hn).le

lemma retained_peak_exponential_bound (P Q T : ℝ≥0∞) (c b ε n : ℝ)
    (hP : ENNReal.ofReal (c*Real.exp (-b*n)) ≤ P)
    (hhalf : P/2 ≤ Q) (htransfer : ENNReal.ofReal (Real.exp (-ε*n))*Q ≤ T) :
    ENNReal.ofReal ((c/2)*Real.exp (-(b+ε)*n)) ≤ T := by
  have he : (c/2)*Real.exp (-(b+ε)*n)=
      Real.exp (-ε*n)*((c*Real.exp (-b*n))/2) := by
    have hexp : Real.exp (-(b+ε)*n)=Real.exp (-ε*n)*Real.exp (-b*n) := by
      rw [←Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  calc
    _ = ENNReal.ofReal (Real.exp (-ε*n))*(ENNReal.ofReal (c*Real.exp (-b*n))/2) := by
      rw [he,ENNReal.ofReal_mul (Real.exp_nonneg _),ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ)<2)]
      norm_num
    _ ≤ ENNReal.ofReal (Real.exp (-ε*n))*(P/2) := mul_le_mul' le_rfl (ENNReal.div_le_div_right hP 2)
    _ ≤ ENNReal.ofReal (Real.exp (-ε*n))*Q := mul_le_mul' le_rfl hhalf
    _ ≤ T := htransfer

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PeakSprinklingSurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem peak_sprinkling_eventual_survival_bs_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (O : G.OrbitRepresentatives) (p q b : unitInterval)
    (hparam : Percolation.sprinkleParameter q b=p)
    (a : V → ℝ) (R : ℝ) (hR : 0 < R)
    (hfin : ∀ x, ∀ᵐ ω ∂G.law q, (G.cluster ω x).Finite)
    (g : ℕ → ℝ) (hg : ∀ l, 0 ≤ g l) (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hgb : ∀ l, g l ≤ C₀) (hglim : Tendsto g atTop (𝓝 0))
    (havoid : ∀ (x : V) (S : Finset V) (u : V), u ∈ S → G.orbitAdjustedHeight a x u ≤ 0 →
      Real.exp (-g (-G.adjustedLayerIndex a R 0 x u).toNat) ≤
        (BernoulliProduct.law (fun e => Percolation.sprinkleParameter
          (erasedWhiteParameters (fun _ => q) (G.incidentEdges (S : Set V)) e) b)).real
            (exteriorEscape G.ends (S : Set V) (G.orbitAdjustedHeight a x) x u)ᶜ)
    (c rate A C : ℝ) (hA : 0 < A) (hC : 0 ≤ C)
    (hsurv : ∀ n : ℕ, 0 < n → ENNReal.ofReal (c*Real.exp (-rate*n)) ≤
      G.peakSurvivalProbability O a R q n)
    (hprofile : ∀ n : ℕ, 0 < n → ∀ l : ℕ, G.peakSurvivalLayerMoment O a R q n l ≤
      G.peakSurvivalProbability O a R q n *
        ENNReal.ofReal (C*Real.exp (-A*max ((l : ℝ)-n) 0)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((c/2)*Real.exp (-(rate+ε)*n)) ≤
      G.fullPeakDownProbability O a p (R*n) := by
  let Ev (n : ℕ) (x : V) : Set (Set E) :=
    {ω | 0 < G.peakDownBandCount a (R*((n : ℝ)+1)) (R*((n : ℝ)+4)) ω x}
  let Z (x : V) (ω : Set E) := G.downwardLayerCost a R g ω x
  let F (n : ℕ) := C*(∑' l, g l*Real.exp (-A*max ((l : ℝ)-n) 0))
  have hEv (n : ℕ) (x : V) : MeasurableSet (Ev n x) :=
    measurableSet_lt measurable_const (G.measurable_peakDownBandCount a _ _ x)
  have hZ (x : V) : Measurable (Z x) := G.measurable_downwardLayerCost a R g x
  have hP (n : ℕ) : G.peakSurvivalProbability O a R q n < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact ENNReal.sum_ne_top.mpr fun x _ => ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hF : Tendsto (fun n : ℕ => F n/(n : ℝ)) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := C) (f := atTop)).mul
      (exponential_continuation_cost_sublinear g C₀ A hg hC₀ hgb hA hglim)
    simpa only [F,div_eq_mul_inv,mul_assoc,mul_zero] using hh
  filter_upwards [sublinear_cost_eventually_small F hF (ε/2) (by positivity),
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : 0 < n := by omega
  have htn : 0 < ε*(n : ℝ) := mul_pos hε (Nat.cast_pos.mpr hn0)
  have hcost : (∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω in Ev n x, Z x ω ∂G.law q)) ≤
      G.peakSurvivalProbability O a R q n*ENNReal.ofReal (F n) := by
    calc
      _ = ∑ x ∈ O.roots, ENNReal.ofReal (a x)*(∫⁻ ω, (Ev n x).indicator (Z x) ω ∂G.law q) := by
        apply Finset.sum_congr rfl
        intro x _
        exact congrArg (fun z => ENNReal.ofReal (a x)*z) (lintegral_indicator (hEv n x) (Z x)).symm
      _ ≤ _ := G.peakSurvivalCostMoment_bound O a R q g hg C₀ hC₀ hgb A C hA hC n (hprofile n hn0)
  have hcost' := hcost.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
    (show F n ≤ ε*(n : ℝ)/2 by nlinarith [hn])))
  have hhalf := weighted_cost_retains_half O.roots (fun _ : V => G.law q)
    (fun x => ENNReal.ofReal (a x)) (Ev n) (fun x _ => hEv n x) Z (fun x _ => hZ x)
    (ε*n) htn (hP n) hcost'
  let B (x : V) := Ev n x ∩ {ω | Z x ω ≤ ENNReal.ofReal (ε*n)}
  have hB (x : V) : MeasurableSet (B x) := (hEv n x).inter (measurableSet_le (hZ x) measurable_const)
  have hBpeak (x : V) : B x ⊆ G.fullPeakDownHit a (R*n) x := by
    apply Set.Subset.trans Set.inter_subset_left
    exact G.positive_peakDownBandCount_subset_fullPeakDownHit hc hl a _ _ (R*n) (by nlinarith [hR]) x
  have htransfer := G.weighted_peak_sprinkling_average O q b p hparam a R hR (R*n)
    g hg (ε*n) htn.le hfin havoid B hB hBpeak (fun _ _ h => h.2)
  apply retained_peak_exponential_bound _ _ _ c rate ε n (hsurv n hn0) hhalf
  simpa only [B,neg_mul] using htransfer

end CriticalPercolation.BondGraph

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.peak_sprinkling_eventual_survival_bs_oai.{u_1, u_2}
